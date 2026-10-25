//go:build amd64

// Package xcrypto holds the WP-E examples: Go code whose work is done by std assembly using the
// x86 crypto extensions (built into artifacts/examples-amd64-crypto, a binary of its own so that
// the other examples' binaries do not change). The proved functions are the std ones it reaches:
// runtime.memhash64 (AES-NI, the hash of every 8-byte map key), crypto/internal/fips140/aes's
// encryptBlockAsm (AES-NI) and math/big's addMulVVWW (ADX/BMI2).
package xcrypto

import (
	"crypto/aes"
	"math/big"
)

// Encrypt encrypts one block under key with crypto/aes (encryptBlockAsm on AES-NI CPUs).
func Encrypt(key, block []byte) []byte {
	c, err := aes.NewCipher(key)
	if err != nil {
		panic(err)
	}
	out := make([]byte, 16)
	c.Encrypt(out, block)
	return out
}

// Count counts the distinct keys (a map[uint64]: runtime.memhash64 hashes them).
func Count(keys []uint64) int {
	m := map[uint64]bool{}
	for _, k := range keys {
		m[k] = true
	}
	return len(m)
}

// Square returns x*x with math/big (its multiplication runs math/big.addMulVVWW).
func Square(x *big.Int) *big.Int { return new(big.Int).Mul(x, x) }
