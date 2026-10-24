// usage: argv[1][0] selects the test: 'a' LDADDAL, 'r' LDAPR, 'e' AESE, 'z' exit(DCZID_EL0), 'u' unaligned LDAR
.global _start
_start:
  ldr x9, [sp, #16]        // argv[1]
  ldrb w9, [x9]
  sub sp, sp, #64
  mov x0, sp
  str xzr, [x0]
  mov x1, #1
  cmp w9, #'a'
  b.eq 1f
  cmp w9, #'r'
  b.eq 2f
  cmp w9, #'e'
  b.eq 3f
  cmp w9, #'z'
  b.eq 4f
  cmp w9, #'u'
  b.eq 5f
  b 9f
1: .inst 0xf8e10002        // ldaddal x1, x2, [x0]
  b 9f
2: .inst 0xf8bfc002        // ldapr x2, [x0]
  b 9f
3: .inst 0x4e284820        // aese v0.16b, v1.16b
  b 9f
4: mrs x0, dczid_el0
  b 10f
5: add x3, x0, #4
  .inst 0xc8dffc62         // ldar x2, [x3]  (address 4 mod 8, inside one 16-byte granule)
9: mov x0, #0
10: mov x8, #93
  svc #0
