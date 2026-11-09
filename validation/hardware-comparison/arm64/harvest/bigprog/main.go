// Command bigprog exists only to be compiled for arm64: its .text (runtime plus a spread of
// std packages) is a corpus of instruction words the Go compiler really emits.
package main

import (
	"bytes"
	"compress/flate"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"hash/crc32"
	"math"
	"math/big"
	"math/bits"
	"os"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode/utf8"
)

func main() {
	x, _ := new(big.Int).SetString(strings.Repeat("9", 80), 10)
	y := new(big.Int).Exp(x, big.NewInt(17), big.NewInt(1000000007))
	q, r := new(big.Int).QuoRem(x, y, new(big.Int))
	h := sha256.Sum256(x.Bytes())
	h5 := sha512.Sum512(h[:])
	xs := []int{5, 3, 9, 1}
	sort.Ints(xs)
	slices.Sort(xs)
	var buf bytes.Buffer
	w, _ := flate.NewWriter(&buf, 9)
	w.Write(h5[:])
	w.Close()
	j, _ := json.Marshal(map[string]any{"q": q.String(), "r": r.Text(16), "f": math.Sqrt(2)})
	re := regexp.MustCompile(`a+b*`)
	var mu sync.Mutex
	mu.Lock()
	n := bits.OnesCount64(binary.LittleEndian.Uint64(h[:])) + utf8.RuneCountInString("héllo")
	mu.Unlock()
	f, _ := strconv.ParseFloat("3.25", 64)
	fmt.Fprintln(os.Stdout, len(buf.Bytes()), string(j), re.MatchString("aab"), n, crc32.ChecksumIEEE(h[:]), f, xs)
}
