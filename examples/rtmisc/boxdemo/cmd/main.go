// Command cmd links the live boxing example (scripts/build/build-examples-rtmisc.sh).
package main

import "example.com/rtmisc/boxdemo"

func main() {
	n, a, b := boxdemo.BoxAfterNew("hello", 300)
	println(n != nil, a != nil, b != nil)
}
