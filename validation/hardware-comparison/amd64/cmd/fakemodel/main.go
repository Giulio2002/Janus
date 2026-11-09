// Command fakemodel stands in for janus-oracle-amd64 when testing the pipeline: it answers
// every case with an `undecodable` fault (so every hardware success is a model-gap).
package main

import (
	"bufio"
	"encoding/json"
	"os"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	w := bufio.NewWriter(os.Stdout)
	enc := json.NewEncoder(w)
	for in.Scan() {
		var c L.Case
		if json.Unmarshal(in.Bytes(), &c) != nil {
			continue
		}
		enc.Encode(&L.Model{ID: c.ID, Status: "fault", Fault: "undecodable"})
	}
	w.Flush()
}
