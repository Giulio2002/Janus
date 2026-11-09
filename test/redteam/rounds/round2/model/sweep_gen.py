import random, sys
random.seed(int(sys.argv[2])); n=int(sys.argv[1])
# (fixed-mask, fixed-value) templates covering the classes added on arm64cov2 + atomics/sys
T=[(0x0E000000,0x0E000000),  # x111 SIMD/FP DP (op0 bits 27:25 = 111)
   (0x0E000000,0x0C000000),  # loads/stores, V=1 (bits 27:25 =110 incl bit26)
   (0x3F000000,0x08000000),  # exclusive/ordered/CAS
   (0x3F200C00,0x38200000),  # atomics
   (0xFFC00000,0xD5000000),  # system
   (0x9F000000,0x0E000000),(0x9F000000,0x0F000000),(0x9F000000,0x2E000000),(0x9F000000,0x2F000000),
   (0xFF000000,0x4E000000),(0xBF000000,0x0C000000),(0xBF000000,0x0D000000),
   (0x3F000000,0x3C000000),(0x3F000000,0x3D000000),(0x3F000000,0x2C000000),(0x3F000000,0x2D000000),(0x3F000000,0x1C000000),
   (0x7F000000,0x1E000000)]
for _ in range(n):
    m,v=random.choice(T); w=(random.getrandbits(32)&~m)|v; print(hex(w))
