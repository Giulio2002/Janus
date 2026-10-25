package main

// Cache garbage collection: a size- and age-bounded LRU over the Janus cache (docs/CLI.md
// "Cache", docs/SOUNDNESS.md "Cache eviction").
//
// Every cache below <cache>/v1 grows with use: one consumer workspace (100-300 MB) per
// package, framework and extraction; one framework build (~370 MB) per framework version; one
// JanusASL build (~1-2.5 GB) per framework, JanusASL version and framework directory; small
// result, trusted-compile and replay entries per verification; and the temporary trees of
// processes that were killed. Nothing bounded them but $JANUS_CACHE_RETENTION_DAYS. The
// collector here runs after every `janus verify`, `verify-batch` and `blockers` (at most once a
// minute per cache unless the disk is nearly full) and on `janus cache gc`; `janus cache du`
// shows the usage.
//
// Entries and their last use (the time of the newest of the listed files; janus touches them
// on every use, touchUse and touchHit):
//
//	consumer   v1/consumer/<family>/<ws>           dir, <ws>.lock (exclusive while in use)
//	framework  v1/framework/<key>                  dir, <key>.lock (shared while in use), <key>.ready
//	asl        v1/asl/<key>                        dir, <key>.lock (exclusive while built),
//	                                               <key>.use (shared while in use)
//	trusted    v1/trusted/<xx>/<key>               dir (written once, by an atomic rename)
//	result     v1/result/<xx>/<key>.json           file (written by an atomic rename)
//	replay     v1/replay/{<xx>,early/<xx>}/<key>   empty marker file
//	tmp, run   v1/tmp/<name>, v1/run/<name>        temporary trees of running (or killed)
//	                                               processes: removed when nothing in them
//	                                               changed for $JANUS_CACHE_TMP_HOURS (24)
//
// The rules, in order:
//
//  1. Nothing is collected unless the cache passes checkCacheRoot (round 8 C1): a cache another
//     user can write is not ours to delete from, and its entries are not trusted anyway.
//  2. Entries used within the grace period (10 minutes) are never collected, nor the entries
//     of the framework and JanusASL builds this process uses (gcPin; `janus cache gc` keeps
//     those of the current framework unless --all).
//  3. An entry with a lock is collected only under that lock, taken exclusively and without
//     waiting: an entry a process is using (holding its lock shared or exclusive) is skipped.
//     Under the lock the entry is first made unusable (its .ready stamp removed), then renamed
//     whole into a fresh v1/tmp/gc-* directory, and only then deleted; its lock files are
//     removed while still held (lockFileMode re-checks the inode, so a process waiting on the
//     old lock retries on a new file and then finds the entry gone). Entries without a lock
//     (trusted, result, replay) are written atomically and read with full verification, and
//     are removed with one rename or unlink: a reader sees the whole entry or none.
//  4. Consumer and framework builds unused for $JANUS_CACHE_RETENTION_DAYS (7) and JanusASL
//     builds unused for $JANUS_ASL_RETENTION_DAYS (30) are collected whatever the budget.
//  5. While the cache is larger than its budget, the remaining entries are collected in
//     order of age / weight, the oldest first (weights: asl 4, framework 2, others 1: a JanusASL
//     build costs an hour, a framework build minutes, everything else seconds). The budget is
//     $JANUS_CACHE_MAX or --max ("40G", "500M", "10%" of the filesystem, "off"), by default
//     min(40 GiB, 10% of the filesystem), or min(8 GiB, 5%) on a tmpfs (RAM). When the
//     filesystem has less than min(20 GiB, 5%) free, the budget shrinks by the shortfall.
//
// Soundness: collecting only ever deletes. Every cache is already safe against deletion of any
// entry not in use, since each read re-verifies what it reads (the result and trusted-compile
// entries by their HMAC under the hidden key and the SHA-256 of every file; the framework
// build by its ready stamp, its sources and the pins of every module; consumer workspaces are
// untrusted by design and pinned and replayed; replay markers only skip work whose inputs they
// name by hash), and a miss rebuilds the entry from the same inputs. The collector never
// writes an entry, a key or a stamp, follows no symbolic link, and only renames entries into
// its own trash directory; it cannot make a stale or foreign entry be used.

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// gcGrace is the default grace period: entries used more recently are never collected.
const gcGrace = 10 * time.Minute

// gcAutoInterval is how often the automatic collector runs per cache (unless space is low).
const gcAutoInterval = time.Minute

// cacheStatFS is statFS (a variable for the tests).
var cacheStatFS = statFS

// gcKinds are the evictable entry kinds, in display order, with their LRU weights.
var gcKinds = []string{"consumer", "framework", "asl", "trusted", "result", "replay", "tmp", "run"}

var gcWeight = map[string]float64{"asl": 4, "framework": 2}

// gcEntry is one cache entry.
type gcEntry struct {
	Kind  string    `json:"kind"`
	Path  string    `json:"path"`
	Size  int64     `json:"size"`
	Used  time.Time `json:"lastUse"`
	locks []string  // lock files, all taken exclusively (without waiting) to collect it
	side  []string  // other files of the entry (the .ready stamp), removed with it
	// marks are the files whose modification time is the last use.
	marks  []string
	pinned bool
	inUse  bool // a lock is held by another process (found by du / dry run)
}

// gcPins are the entry directories this process uses (never collected by its own GC).
var (
	gcPinMu sync.Mutex
	gcPins  = map[string]bool{}
)

func gcPin(dir string) {
	gcPinMu.Lock()
	gcPins[filepath.Clean(dir)] = true
	gcPinMu.Unlock()
}

func gcPinned(dir string) bool {
	gcPinMu.Lock()
	defer gcPinMu.Unlock()
	return gcPins[filepath.Clean(dir)]
}

// touchUse records a use of a locked entry: its directory and lock file get the current time.
// The lock file sits next to the entry, outside anything a sandbox can write.
func touchUse(paths ...string) {
	now := time.Now()
	for _, p := range paths {
		_ = os.Chtimes(p, now, now)
	}
}

// fileExists reports whether p names an existing file (os.Stat, as the marker checks always did).
func fileExists(p string) bool {
	_, err := os.Stat(p)
	return err == nil
}

// touchHit records a hit on an entry without a lock (a result, trusted-compile or replay entry).
func touchHit(p string) { touchUse(p) }

// diskUsage is the space a file takes (its allocated blocks; the size if unknown).
func diskUsage(fi fs.FileInfo) int64 {
	if st, ok := fi.Sys().(*syscall.Stat_t); ok {
		return int64(st.Blocks) * 512
	}
	return fi.Size()
}

// treeUsage sums the disk usage of the tree at p (not following symbolic links) and returns the
// newest modification time in it (clamped to now: a future time set inside a tree does not keep
// it forever beyond the clamp's reach of "now").
func treeUsage(p string) (int64, time.Time) {
	var n int64
	var newest time.Time
	now := time.Now()
	_ = filepath.WalkDir(p, func(q string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		fi, err := d.Info()
		if err != nil {
			return nil
		}
		n += diskUsage(fi)
		if t := fi.ModTime(); t.After(newest) {
			newest = t
		}
		return nil
	})
	if newest.After(now) {
		newest = now
	}
	return n, newest
}

// lastUse is the newest modification time of the existing files among marks.
func lastUse(marks []string) time.Time {
	var t time.Time
	for _, m := range marks {
		if fi, err := os.Lstat(m); err == nil && fi.ModTime().After(t) {
			t = fi.ModTime()
		}
	}
	if now := time.Now(); t.After(now) {
		t = now
	}
	return t
}

// gcScan lists the entries of the cache under root, and the bytes under v1 that belong to no
// entry (lock files, the result key, unknown directories).
type gcScan struct {
	root    string
	entries []*gcEntry
	other   int64
	orphans []string // lock and stamp files whose entry is gone (removed under their lock)
	empty   []string // empty consumer family directories
	trash   []string // v1/tmp/gc-* directories of an interrupted collection
}

func (s *gcScan) total() int64 {
	n := s.other
	for _, e := range s.entries {
		n += e.Size
	}
	return n
}

func scanCache(root string) *gcScan {
	s := &gcScan{root: root}
	v1 := filepath.Join(root, "v1")
	known := map[string]bool{}
	for _, k := range gcKinds {
		known[k] = true
	}
	tops, _ := os.ReadDir(v1)
	for _, t := range tops {
		p := filepath.Join(v1, t.Name())
		if !t.IsDir() || !known[t.Name()] {
			n, _ := treeUsage(p)
			s.other += n
			continue
		}
		if fi, err := os.Lstat(p); err == nil {
			s.other += diskUsage(fi)
		}
		switch t.Name() {
		case "consumer":
			fams, _ := os.ReadDir(p)
			for _, f := range fams {
				fd := filepath.Join(p, f.Name())
				if !f.IsDir() {
					n, _ := treeUsage(fd)
					s.other += n
					continue
				}
				if fi, err := os.Lstat(fd); err == nil {
					s.other += diskUsage(fi)
				}
				members, _ := os.ReadDir(fd)
				if len(members) == 0 {
					s.empty = append(s.empty, fd)
				}
				s.scanLocked("consumer", fd, members, nil)
			}
		case "framework":
			ents, _ := os.ReadDir(p)
			s.scanLocked("framework", p, ents, []string{".ready"})
		case "asl":
			ents, _ := os.ReadDir(p)
			s.scanLocked("asl", p, ents, nil)
		case "trusted", "result":
			shards, _ := os.ReadDir(p)
			for _, sh := range shards {
				sd := filepath.Join(p, sh.Name())
				if !sh.IsDir() || strings.HasPrefix(sh.Name(), ".") {
					// v1/result/.key and anything else at the top: never collected.
					n, _ := treeUsage(sd)
					s.other += n
					continue
				}
				if fi, err := os.Lstat(sd); err == nil {
					s.other += diskUsage(fi)
				}
				ents, _ := os.ReadDir(sd)
				for _, e := range ents {
					s.addFile(t.Name(), filepath.Join(sd, e.Name()))
				}
			}
		case "replay":
			_ = filepath.WalkDir(p, func(q string, d fs.DirEntry, err error) error {
				if err != nil || q == p {
					return nil
				}
				if d.IsDir() {
					if fi, err := d.Info(); err == nil {
						s.other += diskUsage(fi)
					}
					return nil
				}
				if filepath.Base(filepath.Dir(q)) == "locks" && filepath.Dir(filepath.Dir(q)) == p {
					// Replay target locks: removed (under the lock) once old.
					fi, err := d.Info()
					if err == nil && time.Since(fi.ModTime()) > gcGrace {
						s.orphans = append(s.orphans, q)
					}
					return nil
				}
				s.addFile("replay", q)
				return nil
			})
		case "tmp", "run":
			ents, _ := os.ReadDir(p)
			for _, e := range ents {
				q := filepath.Join(p, e.Name())
				if t.Name() == "tmp" && strings.HasPrefix(e.Name(), "gc-") && e.IsDir() {
					s.trash = append(s.trash, q)
				}
				n, newest := treeUsage(q)
				s.entries = append(s.entries, &gcEntry{Kind: t.Name(), Path: q, Size: n, Used: newest})
			}
		}
	}
	return s
}

// addFile adds a lock-less entry (a file or a directory written by an atomic rename).
func (s *gcScan) addFile(kind, p string) {
	n, _ := treeUsage(p)
	s.entries = append(s.entries, &gcEntry{Kind: kind, Path: p, Size: n, marks: []string{p}, Used: lastUse([]string{p})})
}

// scanLocked adds the directory entries of parent (with their <name>.lock, <name>.use and
// sideExt files) and records lock or stamp files whose directory is gone as orphans.
func (s *gcScan) scanLocked(kind, parent string, ents []fs.DirEntry, sideExt []string) {
	dirs := map[string]bool{}
	for _, e := range ents {
		if e.IsDir() {
			dirs[e.Name()] = true
		}
	}
	for _, e := range ents {
		p := filepath.Join(parent, e.Name())
		if e.IsDir() {
			ent := &gcEntry{Kind: kind, Path: p, locks: []string{p + ".lock"}, marks: []string{p, p + ".lock"}}
			if kind == "asl" {
				ent.locks = append(ent.locks, p+".use")
				ent.marks = append(ent.marks, p+".use")
			}
			for _, x := range sideExt {
				ent.side = append(ent.side, p+x)
				ent.marks = append(ent.marks, p+x)
			}
			n, _ := treeUsage(p)
			for _, f := range append(append([]string{}, ent.locks...), ent.side...) {
				if fi, err := os.Lstat(f); err == nil {
					n += diskUsage(fi)
				}
			}
			// Only files that exist now mark uses (evict creates missing lock files).
			var marks []string
			for _, m := range ent.marks {
				if fileExists(m) {
					marks = append(marks, m)
				}
			}
			ent.marks = marks
			ent.Size, ent.Used = n, lastUse(ent.marks)
			s.entries = append(s.entries, ent)
			continue
		}
		name := e.Name()
		if e.Type()&fs.ModeSymlink != 0 {
			// Not something janus creates: removed (the link only) like a lock-less entry.
			s.addFile(kind, p)
			continue
		}
		owner := ""
		for _, x := range append([]string{".lock", ".use"}, sideExt...) {
			if strings.HasSuffix(name, x) {
				owner = strings.TrimSuffix(name, x)
				break
			}
		}
		if owner != "" && dirs[owner] {
			continue // counted with its entry
		}
		fi, err := e.Info()
		if err != nil {
			continue
		}
		s.other += diskUsage(fi)
		if owner != "" && time.Since(fi.ModTime()) > gcGrace {
			s.orphans = append(s.orphans, p)
		} else if strings.HasPrefix(name, ".") && strings.Contains(name, ".tmp-") && time.Since(fi.ModTime()) > 24*time.Hour {
			// A stamp's temporary file left by a killed writer (writeFileAtomic).
			s.orphans = append(s.orphans, p)
		}
	}
}

// gcOptions configure one collection.
type gcOptions struct {
	Max    int64 // budget in bytes; < 0: no size budget
	DryRun bool
	Grace  time.Duration
	All    bool // do not keep the current framework's entries (CLI)
	Keep   []string
	Now    time.Time
}

// gcReport is what a collection did (or, dry, would do).
type gcReport struct {
	Root      string     `json:"root"`
	Budget    int64      `json:"budget"` // -1: none
	Before    int64      `json:"before"`
	After     int64      `json:"after"`
	Evicted   []*gcEntry `json:"evicted"`
	Skipped   int        `json:"skippedInUse"`
	DryRun    bool       `json:"dryRun"`
	FreeSpace int64      `json:"freeSpace"`
	Reason    string     `json:"reason,omitempty"`
}

func envFloat(name string, def float64) float64 {
	if v, err := strconv.ParseFloat(os.Getenv(name), 64); err == nil && v > 0 {
		return v
	}
	return def
}

// parseCacheSize parses a cache budget: "40G", "500M", "1.5GiB", "123456" (bytes), "10%" (of
// the filesystem's size), "0", or "off" (-1: no size budget).
func parseCacheSize(s string, fsSize int64) (int64, error) {
	t := strings.TrimSpace(s)
	if strings.EqualFold(t, "off") || strings.EqualFold(t, "none") {
		return -1, nil
	}
	bad := fmt.Errorf("%q is not a cache size like 40G, 500M, 10%% or off", s)
	if strings.HasSuffix(t, "%") {
		f, err := strconv.ParseFloat(strings.TrimSuffix(t, "%"), 64)
		if err != nil || f < 0 || f > 100 || fsSize <= 0 {
			return 0, bad
		}
		return int64(f / 100 * float64(fsSize)), nil
	}
	u := strings.ToUpper(t)
	u = strings.TrimSuffix(strings.TrimSuffix(u, "B"), "I")
	mult := int64(1)
	if u != "" {
		switch u[len(u)-1] {
		case 'K':
			mult = 1 << 10
		case 'M':
			mult = 1 << 20
		case 'G':
			mult = 1 << 30
		case 'T':
			mult = 1 << 40
		}
		if mult != 1 {
			u = u[:len(u)-1]
		}
	}
	f, err := strconv.ParseFloat(u, 64)
	if err != nil || f < 0 {
		return 0, bad
	}
	return int64(f * float64(mult)), nil
}

// defaultCacheBudget is min(40 GiB, 10% of the filesystem), or min(8 GiB, 5%) on a tmpfs.
func defaultCacheBudget(fsi fsInfo) int64 {
	b := 40 * gib
	if fsi.size > 0 && fsi.size/10 < b {
		b = fsi.size / 10
	}
	if fsi.ram {
		b = 8 * gib
		if fsi.size > 0 && fsi.size/20 < b {
			b = fsi.size / 20
		}
	}
	return b
}

// cacheBudget is the configured budget ($JANUS_CACHE_MAX, else the default) for the cache root.
func cacheBudget(fsi fsInfo) (int64, error) {
	if v := strings.TrimSpace(os.Getenv("JANUS_CACHE_MAX")); v != "" {
		n, err := parseCacheSize(v, fsi.size)
		if err != nil {
			return 0, fmt.Errorf("JANUS_CACHE_MAX: %v", err)
		}
		return n, nil
	}
	return defaultCacheBudget(fsi), nil
}

// minFree is the free space below which the budget shrinks: min(20 GiB, 5% of the filesystem).
func minFree(fsi fsInfo) int64 {
	m := 20 * gib
	if fsi.size > 0 && fsi.size/20 < m {
		m = fsi.size / 20
	}
	return m
}

// gcDiag is a collection failure.
func gcDiag(msg string) error {
	return &diag{Msg: msg, Stage: "cache gc", Next: "See docs/CLI.md (Cache)."}
}

// collectCache runs one collection of the cache under cacheRoot(). With block false it returns
// (nil, nil) if another collection is running.
func collectCache(o gcOptions, block bool) (*gcReport, error) {
	if err := checkCacheRoot(); err != nil {
		return nil, err
	}
	root := cacheRoot()
	if o.Now.IsZero() {
		o.Now = time.Now()
	}
	v1 := filepath.Join(root, "v1")
	if err := os.MkdirAll(v1, 0o755); err != nil {
		return nil, gcDiag("Cannot prepare the cache: " + err.Error())
	}
	lk, err := lockFileMode(filepath.Join(v1, "gc.lock"), false, block)
	if err != nil {
		if !block {
			return nil, nil
		}
		return nil, gcDiag("Cannot lock the cache for collection: " + err.Error())
	}
	defer lk.unlock()
	if !o.DryRun {
		touchUse(filepath.Join(v1, "gc.lock"))
	}
	keep := map[string]bool{}
	for _, k := range o.Keep {
		keep[filepath.Clean(k)] = true
	}
	s := scanCache(root)
	fsi := cacheStatFS(root)
	rep := &gcReport{Root: root, Budget: o.Max, Before: s.total(), DryRun: o.DryRun, FreeSpace: fsi.avail}

	// The trash of an interrupted collection (nobody else uses gc-* directories: the gc lock
	// is held), orphaned lock and stamp files, empty consumer families.
	if !o.DryRun {
		for _, t := range s.trash {
			_ = os.RemoveAll(t)
		}
		for _, p := range s.orphans {
			removeOrphan(p)
		}
		for _, f := range s.empty {
			if fi, err := os.Lstat(f); err == nil && o.Now.Sub(fi.ModTime()) > o.Grace {
				_ = os.Remove(f) // fails unless still empty
			}
		}
	}
	trashSet := map[string]bool{}
	for _, t := range s.trash {
		trashSet[t] = true
	}
	usage := rep.Before
	var trash string
	evict := func(e *gcEntry) bool {
		if trashSet[e.Path] {
			return false
		}
		ok, inUse := e.evict(o, func() (string, error) {
			if trash == "" {
				if err := os.MkdirAll(filepath.Join(v1, "tmp"), 0o755); err != nil {
					return "", err
				}
				d, err := os.MkdirTemp(filepath.Join(v1, "tmp"), "gc-")
				if err != nil {
					return "", err
				}
				trash = d
			}
			return trash, nil
		})
		if inUse {
			e.inUse = true
			rep.Skipped++
		}
		if ok {
			usage -= e.Size
			rep.Evicted = append(rep.Evicted, e)
		}
		return ok
	}
	retention := time.Duration(envFloat("JANUS_CACHE_RETENTION_DAYS", 7) * 24 * float64(time.Hour))
	aslRetention := time.Duration(envFloat("JANUS_ASL_RETENTION_DAYS", 30) * 24 * float64(time.Hour))
	tmpAge := time.Duration(envFloat("JANUS_CACHE_TMP_HOURS", 24) * float64(time.Hour))
	var lru []*gcEntry
	for _, e := range s.entries {
		age := o.Now.Sub(e.Used)
		if gcPinned(e.Path) || (!o.All && keep[e.Path]) {
			e.pinned = true
		}
		if e.pinned || age < o.Grace || trashSet[e.Path] {
			continue
		}
		switch {
		case e.Kind == "tmp" || e.Kind == "run":
			// Temporary trees: only by age (they have no lock; their process may still run).
			if age > tmpAge {
				evict(e)
			}
			continue
		case e.Kind == "asl" && age > aslRetention, (e.Kind == "consumer" || e.Kind == "framework") && age > retention:
			if evict(e) {
				continue
			}
		}
		lru = append(lru, e)
	}

	target := o.Max
	if avail := fsi.avail; fsi.size > 0 && avail >= 0 && avail < minFree(fsi) {
		short := minFree(fsi) - avail
		if t := usage - short; target < 0 || t < target {
			target = t
			rep.Reason = fmt.Sprintf("the filesystem has %s free, below %s", fmtBytes(avail), fmtBytes(minFree(fsi)))
		}
		if target < 0 {
			target = 0
		}
	}
	if target >= 0 && usage > target {
		sort.SliceStable(lru, func(i, j int) bool {
			return lru[i].priority(o.Now) > lru[j].priority(o.Now)
		})
		for _, e := range lru {
			if usage <= target {
				break
			}
			evict(e)
		}
	}
	if trash != "" {
		_ = os.RemoveAll(trash)
	}
	rep.After = usage
	if !o.DryRun {
		rep.After = scanCache(root).total()
		if f := cacheStatFS(root); f.size > 0 {
			rep.FreeSpace = f.avail
		}
	}
	return rep, nil
}

// priority orders the LRU: the larger, the earlier collected.
func (e *gcEntry) priority(now time.Time) float64 {
	w := gcWeight[e.Kind]
	if w == 0 {
		w = 1
	}
	return float64(now.Sub(e.Used)) / w
}

// evict collects e (rule 3 of the file comment). It reports whether e was collected and whether
// it was skipped because it is in use. With o.DryRun nothing is changed.
func (e *gcEntry) evict(o gcOptions, trashDir func() (string, error)) (ok, inUse bool) {
	var held []*fileLock
	defer func() {
		for _, l := range held {
			l.unlock()
		}
	}()
	for _, l := range e.locks {
		if _, err := os.Lstat(l); os.IsNotExist(err) && o.DryRun {
			continue
		}
		lk, err := lockFileMode(l, false, false)
		if err != nil {
			return false, errors.Is(err, syscall.EWOULDBLOCK)
		}
		held = append(held, lk)
	}
	// Used again since the scan (between the scan and the lock): keep it.
	if len(e.marks) > 0 && lastUse(e.marks).After(e.Used) && o.Now.Sub(lastUse(e.marks)) < o.Grace {
		return false, false
	}
	if o.DryRun {
		return true, false
	}
	for _, f := range e.side {
		_ = os.Remove(f)
	}
	fi, err := os.Lstat(e.Path)
	if err != nil {
		return false, false
	}
	if fi.IsDir() {
		d, err := trashDir()
		if err != nil {
			return false, false
		}
		dst := filepath.Join(d, strconv.FormatInt(time.Now().UnixNano(), 36)+"-"+filepath.Base(e.Path))
		if err := os.Rename(e.Path, dst); err != nil {
			// Another filesystem below the cache: delete in place (still under the lock).
			if err := os.RemoveAll(e.Path); err != nil {
				return false, false
			}
		}
	} else if err := os.Remove(e.Path); err != nil {
		return false, false
	}
	for _, l := range e.locks {
		_ = os.Remove(l) // under the lock: waiters re-check the inode (lockFileMode)
	}
	return true, false
}

// removeOrphan removes a lock or stamp file whose entry is gone, under its lock if it is one.
func removeOrphan(p string) {
	if strings.HasSuffix(p, ".lock") || strings.HasSuffix(p, ".use") {
		if lk, err := lockFileMode(p, false, false); err == nil {
			_ = os.Remove(p)
			lk.unlock()
		}
		return
	}
	// A .ready stamp (or a temporary stamp file): its directory is gone, so it can make nothing
	// ready (framework.ready also requires the sources and pins); remove it under the entry lock.
	lockPath := strings.TrimSuffix(p, ".ready") + ".lock"
	if strings.HasSuffix(p, ".ready") {
		if lk, err := lockFileMode(lockPath, false, false); err == nil {
			if _, err := os.Lstat(strings.TrimSuffix(p, ".ready")); os.IsNotExist(err) {
				_ = os.Remove(p)
				_ = os.Remove(lockPath)
			}
			lk.unlock()
		}
		return
	}
	_ = os.Remove(p)
}

// autoCollect runs the collector after a command that used the cache (unless
// JANUS_CACHE_GC=off), at most once per gcAutoInterval unless the disk is nearly full. Errors are
// reported on stderr only if the budget is misconfigured; the command's outcome is not affected.
func autoCollect(stderr io.Writer) {
	if strings.EqualFold(strings.TrimSpace(os.Getenv("JANUS_CACHE_GC")), "off") {
		return
	}
	root := cacheRoot()
	v1 := filepath.Join(root, "v1")
	if _, err := os.Lstat(v1); err != nil {
		return
	}
	fsi := cacheStatFS(root)
	low := fsi.size > 0 && fsi.avail < minFree(fsi)
	if fi, err := os.Stat(filepath.Join(v1, "gc.lock")); err == nil && !low && time.Since(fi.ModTime()) < gcAutoInterval {
		return
	}
	max, err := cacheBudget(fsi)
	if err != nil {
		fmt.Fprintf(stderr, "Warning: cache collection skipped: %v\n", err)
		return
	}
	if checkCacheRoot() != nil {
		return
	}
	_, _ = collectCache(gcOptions{Max: max, Grace: gcGrace}, false)
}

// cmdCache is `janus cache du|gc`.
func cmdCache(args []string, stdout, stderr io.Writer) error {
	if len(args) == 0 {
		return usageErr("cache takes a subcommand: du or gc")
	}
	sub := args[0]
	args, flags := takeBoolFlags(args[1:], "json", "dry-run", "all")
	pos, opts, err := parseArgs(args, "max", "grace", "janus-root")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) != 0 {
		return usageErr("cache %s takes no arguments", sub)
	}
	if err := checkCacheRoot(); err != nil {
		return err
	}
	root := cacheRoot()
	fsi := cacheStatFS(root)
	budget, err := cacheBudget(fsi)
	if err != nil {
		return usageErr("%v", err)
	}
	switch sub {
	case "du":
		if len(opts) > 0 || flags["dry-run"] || flags["all"] {
			return usageErr("cache du takes only --json")
		}
		s := scanCache(root)
		for _, e := range s.entries {
			e.inUse = e.probeInUse()
		}
		return printCacheDu(stdout, s, fsi, budget, flags["json"])
	case "gc":
		if v, ok := opts["max"]; ok {
			if budget, err = parseCacheSize(v, fsi.size); err != nil {
				return usageErr("--max: %v", err)
			}
		}
		o := gcOptions{Max: budget, DryRun: flags["dry-run"], Grace: gcGrace, All: flags["all"]}
		if v, ok := opts["grace"]; ok {
			if o.Grace, err = time.ParseDuration(v); err != nil || o.Grace < 0 {
				return usageErr("--grace %q is not a duration like 10m or 0s", v)
			}
		}
		if !o.All {
			o.Keep = currentEntries(opts["janus-root"])
		}
		rep, err := collectCache(o, true)
		if err != nil {
			return err
		}
		return printCacheGC(stdout, rep, flags["json"])
	}
	return usageErr("unknown cache subcommand %q (du or gc)", sub)
}

// currentEntries are the framework and JanusASL cache directories of the framework this janus
// would use now (embedded, or --janus-root / $JANUS_ROOT): `janus cache gc` keeps them.
func currentEntries(janusRoot string) []string {
	fw, err := loadFramework(janusRoot)
	if err != nil {
		return nil
	}
	base := filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24])
	keep := []string{base}
	if pkg, err := loadASL(fw); err == nil {
		keep = append(keep, aslCacheDir(fw, pkg, base))
		if fw.Source == "directory" {
			keep = append(keep, aslCacheDir(fw, pkg, fw.Dir))
		}
	}
	return keep
}

// probeInUse reports whether another process holds one of e's locks (without changing it).
func (e *gcEntry) probeInUse() bool {
	for _, l := range e.locks {
		if _, err := os.Lstat(l); err != nil {
			continue
		}
		lk, err := lockFileMode(l, false, false)
		if err != nil {
			return errors.Is(err, syscall.EWOULDBLOCK)
		}
		lk.unlock()
	}
	return false
}

type duKind struct {
	Kind    string    `json:"kind"`
	Entries int       `json:"entries"`
	Size    int64     `json:"size"`
	InUse   int       `json:"inUse"`
	Oldest  time.Time `json:"oldestUse"`
	Newest  time.Time `json:"newestUse"`
}

func printCacheDu(w io.Writer, s *gcScan, fsi fsInfo, budget int64, asJSON bool) error {
	byKind := map[string]*duKind{}
	for _, k := range gcKinds {
		byKind[k] = &duKind{Kind: k}
	}
	for _, e := range s.entries {
		d := byKind[e.Kind]
		d.Entries++
		d.Size += e.Size
		if e.inUse {
			d.InUse++
		}
		if d.Oldest.IsZero() || e.Used.Before(d.Oldest) {
			d.Oldest = e.Used
		}
		if e.Used.After(d.Newest) {
			d.Newest = e.Used
		}
	}
	if asJSON {
		var kinds []*duKind
		for _, k := range gcKinds {
			kinds = append(kinds, byKind[k])
		}
		b, _ := json.MarshalIndent(map[string]any{"root": s.root, "total": s.total(), "other": s.other, "budget": budget,
			"filesystemSize": fsi.size, "freeSpace": fsi.avail, "ram": fsi.ram, "kinds": kinds}, "", "  ")
		fmt.Fprintf(w, "%s\n", b)
		return nil
	}
	where := ""
	if fsi.size > 0 {
		where = fmt.Sprintf(" (filesystem %s, %s free", fmtBytes(fsi.size), fmtBytes(fsi.avail))
		if fsi.ram {
			where += ", tmpfs: RAM"
		}
		where += ")"
	}
	fmt.Fprintf(w, "Janus cache %s%s\n", displayPath(s.root), where)
	fmt.Fprintf(w, "%-10s %8s %11s %7s  %-16s  %-16s\n", "KIND", "ENTRIES", "SIZE", "IN USE", "OLDEST USE", "NEWEST USE")
	ts := func(t time.Time) string {
		if t.IsZero() {
			return "-"
		}
		return t.Local().Format("2006-01-02 15:04")
	}
	for _, k := range gcKinds {
		d := byKind[k]
		fmt.Fprintf(w, "%-10s %8d %11s %7d  %-16s  %-16s\n", k, d.Entries, fmtBytes(d.Size), d.InUse, ts(d.Oldest), ts(d.Newest))
	}
	fmt.Fprintf(w, "%-10s %8s %11s\n", "other", "", fmtBytes(s.other))
	b := "none (JANUS_CACHE_MAX=off)"
	if budget >= 0 {
		b = fmtBytes(budget)
	}
	fmt.Fprintf(w, "Total: %s; budget: %s.\n", fmtBytes(s.total()), b)
	return nil
}

func printCacheGC(w io.Writer, rep *gcReport, asJSON bool) error {
	if asJSON {
		if rep.Evicted == nil {
			rep.Evicted = []*gcEntry{}
		}
		b, _ := json.MarshalIndent(rep, "", "  ")
		fmt.Fprintf(w, "%s\n", b)
		return nil
	}
	verb := "Removed"
	if rep.DryRun {
		verb = "Would remove"
	}
	var freed int64
	for _, e := range rep.Evicted {
		freed += e.Size
		fmt.Fprintf(w, "  %-9s %10s  last used %s  %s\n", e.Kind, fmtBytes(e.Size),
			e.Used.Local().Format("2006-01-02 15:04"), displayPath(e.Path))
	}
	b := "none"
	if rep.Budget >= 0 {
		b = fmtBytes(rep.Budget)
	}
	fmt.Fprintf(w, "%s %d entries (%s); cache %s -> %s (budget %s); %d in use skipped.\n", verb, len(rep.Evicted), fmtBytes(freed),
		fmtBytes(rep.Before), fmtBytes(rep.After), b, rep.Skipped)
	if rep.Reason != "" {
		fmt.Fprintf(w, "Budget reduced: %s.\n", rep.Reason)
	}
	return nil
}
