package main

import "fmt"

var extra = func() string { return "" }

func hex(v uint32) string { return fmt.Sprintf("%#x", v) }
