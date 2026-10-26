// Command cmd links the size-specialised allocation example (scripts/build-examples-rtmisc.sh).
package main

import "example.com/rtmisc/sc"

func main() { println(sc.NewPair(1, 2).A) }
