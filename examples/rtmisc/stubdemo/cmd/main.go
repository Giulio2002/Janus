// Command cmd links the live-stub examples (scripts/build-examples-rtmisc.sh).
package main

import "example.com/rtmisc/stubdemo"

func main() {
	n := stubdemo.Cons(nil, 1)
	println(stubdemo.Cons(n, 2) != nil)
	s := stubdemo.Push(nil, 7)
	d := make([]byte, 4)
	println(stubdemo.CopyBytes(d, s), len(s))
	stubdemo.Zero(d)
}
