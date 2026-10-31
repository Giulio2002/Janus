package gen

import (
	"math/rand/v2"
	"testing"
)

func TestSVESIMDGroupsDeterministicAndInGroup(t *testing.T) {
	op0 := func(w uint32) uint32 { return w >> 25 & 0xF }
	for i, g := range SVESIMDGroups {
		a := rand.New(rand.NewPCG(7, 9))
		b := rand.New(rand.NewPCG(7, 9))
		for k := 0; k < 2000; k++ {
			w, w2 := SVESIMDWord(a, i), SVESIMDWord(b, i)
			if w != w2 {
				t.Fatalf("%s: not deterministic", g.Name)
			}
			ok := false
			switch g.Name {
			case "sve":
				ok = op0(w) == 0b0010
			case "sme":
				ok = op0(w) == 0 && w>>31 == 1
			case "simdfp":
				ok = op0(w) == 0b0111 || op0(w) == 0b1111
			case "simdls":
				ok = op0(w) == 0b0110 || op0(w) == 0b1110
			}
			if !ok {
				t.Fatalf("%s: word %#08x outside its group", g.Name, w)
			}
		}
	}
}
