// Command cmd is the example binary of package xcrypto (artifacts/examples-amd64-crypto).
package main

import (
	"encoding/hex"
	"fmt"
	"math/big"

	"example.com/basic/xcrypto"
)

func main() {
	key, _ := hex.DecodeString("000102030405060708090a0b0c0d0e0f")
	pt, _ := hex.DecodeString("00112233445566778899aabbccddeeff")
	x, _ := new(big.Int).SetString("123456789012345678901234567890123456789012345678901234567890", 10)
	fmt.Println(hex.EncodeToString(xcrypto.Encrypt(key, pt)), xcrypto.Count([]uint64{1, 2, 2, 3}), xcrypto.Square(x))
}
