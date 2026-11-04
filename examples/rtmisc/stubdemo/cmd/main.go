// Command cmd links the live-stub example (scripts/build-examples-rtmisc.sh).
package main

import "example.com/rtmisc/stubdemo"

func main() {
	n := stubdemo.Cons(nil, 1)
	println(stubdemo.Cons(n, 2) != nil)
}
