// Command uint256-arm64 keeps a broad set of github.com/holiman/uint256 methods alive as
// real out-of-line function bodies, so that Janus can extract and verify them.
//
// Every method is reached only through a method expression stored in a package-level
// variable and invoked indirectly with inputs derived from os.Args. The compiler cannot
// inline an indirect call, and the linker cannot drop a function whose address escapes
// into a reachable global, so the binary contains the exact symbol
// github.com/holiman/uint256.(*Int).<Method> as compiled for this GOOS/GOARCH.
package main

import (
	"fmt"
	"os"

	"github.com/holiman/uint256"
)

type (
	binOp   = func(z, x, y *uint256.Int) *uint256.Int
	binOvf  = func(z, x, y *uint256.Int) (*uint256.Int, bool)
	ternOp  = func(z, x, y, m *uint256.Int) *uint256.Int
	unOp    = func(z, x *uint256.Int) *uint256.Int
	cmpOp   = func(z, x *uint256.Int) bool
	predOp  = func(z *uint256.Int) bool
	shiftOp = func(z, x *uint256.Int, n uint) *uint256.Int
)

var binOps = []struct {
	name string
	f    binOp
}{
	{"Add", (*uint256.Int).Add},
	{"Sub", (*uint256.Int).Sub},
	{"Mul", (*uint256.Int).Mul},
	{"And", (*uint256.Int).And},
	{"Or", (*uint256.Int).Or},
	{"Xor", (*uint256.Int).Xor},
	{"Exp", (*uint256.Int).Exp},
	{"Div", (*uint256.Int).Div},
	{"Mod", (*uint256.Int).Mod},
	{"SDiv", (*uint256.Int).SDiv},
	{"SMod", (*uint256.Int).SMod},
	{"ExtendSign", (*uint256.Int).ExtendSign},
}

var ovfOps = []struct {
	name string
	f    binOvf
}{
	{"AddOverflow", (*uint256.Int).AddOverflow},
	{"SubOverflow", (*uint256.Int).SubOverflow},
	{"MulOverflow", (*uint256.Int).MulOverflow},
}

var ternOps = []struct {
	name string
	f    ternOp
}{
	{"AddMod", (*uint256.Int).AddMod},
	{"MulMod", (*uint256.Int).MulMod},
}

var unOps = []struct {
	name string
	f    unOp
}{
	{"Not", (*uint256.Int).Not},
	{"Neg", (*uint256.Int).Neg},
	{"Byte", (*uint256.Int).Byte}, // z.Byte(n): z is both input and output
	{"Sqrt", (*uint256.Int).Sqrt},
	{"Set", (*uint256.Int).Set},
}

var cmpOps = []struct {
	name string
	f    cmpOp
}{
	{"Lt", (*uint256.Int).Lt},
	{"Gt", (*uint256.Int).Gt},
	{"Slt", (*uint256.Int).Slt},
	{"Sgt", (*uint256.Int).Sgt},
	{"Eq", (*uint256.Int).Eq},
}

var predOps = []struct {
	name string
	f    predOp
}{
	{"IsZero", (*uint256.Int).IsZero},
	{"IsUint64", (*uint256.Int).IsUint64},
}

var shiftOps = []struct {
	name string
	f    shiftOp
}{
	{"Lsh", (*uint256.Int).Lsh},
	{"Rsh", (*uint256.Int).Rsh},
	{"SRsh", (*uint256.Int).SRsh},
}

var (
	cmpFn        func(z, x *uint256.Int) int                  = (*uint256.Int).Cmp
	bitLenFn     func(z *uint256.Int) int                     = (*uint256.Int).BitLen
	setUint64Fn  func(z *uint256.Int, x uint64) *uint256.Int  = (*uint256.Int).SetUint64
	setBytes32Fn func(z *uint256.Int, in []byte) *uint256.Int = (*uint256.Int).SetBytes32
	bytes32Fn    func(z *uint256.Int) [32]byte                = (*uint256.Int).Bytes32
	cloneFn      func(z *uint256.Int) *uint256.Int            = (*uint256.Int).Clone
	clearFn      func(z *uint256.Int) *uint256.Int            = (*uint256.Int).Clear
)

func arg(i int) *uint256.Int {
	if i < len(os.Args) {
		if v, err := uint256.FromHex(os.Args[i]); err == nil {
			return v
		}
	}
	return uint256.NewInt(uint64(len(os.Args) + i))
}

func main() {
	x, y, m := arg(1), arg(2), arg(3)
	var z uint256.Int
	for _, op := range binOps {
		fmt.Println(op.name, op.f(&z, x, y).Hex())
	}
	for _, op := range ovfOps {
		r, o := op.f(&z, x, y)
		fmt.Println(op.name, r.Hex(), o)
	}
	for _, op := range ternOps {
		fmt.Println(op.name, op.f(&z, x, y, m).Hex())
	}
	for _, op := range unOps {
		z.Set(y)
		fmt.Println(op.name, op.f(&z, x).Hex())
	}
	for _, op := range cmpOps {
		fmt.Println(op.name, op.f(x, y))
	}
	for _, op := range predOps {
		fmt.Println(op.name, op.f(x))
	}
	n := uint(y.Uint64())
	for _, op := range shiftOps {
		fmt.Println(op.name, op.f(&z, x, n).Hex())
	}
	fmt.Println("Cmp", cmpFn(x, y))
	fmt.Println("BitLen", bitLenFn(x))
	fmt.Println("SetUint64", setUint64Fn(&z, uint64(len(os.Args))).Hex())
	b := bytes32Fn(x)
	fmt.Println("Bytes32", b)
	fmt.Println("SetBytes32", setBytes32Fn(&z, b[:]).Hex())
	fmt.Println("Clone", cloneFn(x).Hex())
	fmt.Println("Clear", clearFn(&z).Hex())
}
