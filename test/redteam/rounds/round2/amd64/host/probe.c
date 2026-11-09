/* Host-CPU counterparts of ExecProbe.lean / DF.lean cases.
   Build: gcc -O1 -o probe probe.c && ./probe */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>

int main(void) {
  uint64_t rax, rdx, m;
  /* 1. CMPXCHG r/m32 success: RAX upper half preserved */
  m = 0x5756555400000044ull; rax = 0xDEADBEEF00000044ull;
  __asm__ volatile("movl $0x55, %%ecx; cmpxchgl %%ecx, %1" : "+a"(rax), "+m"(m) :: "rcx", "cc");
  printf("cmpxchg32 ok:   rax=%016llx mem=%016llx\n", (unsigned long long)rax, (unsigned long long)m);
  m = 0x5756555400000044ull; rax = 0xDEADBEEF00000045ull;
  __asm__ volatile("movl $0x55, %%ecx; cmpxchgl %%ecx, %1" : "+a"(rax), "+m"(m) :: "rcx", "cc");
  printf("cmpxchg32 fail: rax=%016llx mem=%016llx\n", (unsigned long long)rax, (unsigned long long)m);
  /* 2. CMPXCHG8B: success leaves RAX/RDX; failure loads zero-extended */
  m = 0x0000000200000001ull; rax = 0xAAAA000000000001ull; rdx = 0xBBBB000000000002ull;
  __asm__ volatile("xor %%ebx,%%ebx; xor %%ecx,%%ecx; cmpxchg8b %2" : "+a"(rax), "+d"(rdx), "+m"(m) :: "rbx", "rcx", "cc");
  printf("cmpxchg8b ok:   rax=%016llx rdx=%016llx mem=%016llx\n", (unsigned long long)rax, (unsigned long long)rdx, (unsigned long long)m);
  m = 0x5756555453525150ull; rax = 0xAAAA000000000001ull; rdx = 0xBBBB000000000002ull;
  __asm__ volatile("xor %%ebx,%%ebx; xor %%ecx,%%ecx; cmpxchg8b %2" : "+a"(rax), "+d"(rdx), "+m"(m) :: "rbx", "rcx", "cc");
  printf("cmpxchg8b fail: rax=%016llx rdx=%016llx\n", (unsigned long long)rax, (unsigned long long)rdx);
  /* 3. REP MOVSB with RCX=0 and unmapped RSI/RDI: no access, no fault */
  {
    uint64_t c = 0, si = 0xdead0000, di = 0xbeef0000;
    __asm__ volatile("rep movsb" : "+c"(c), "+S"(si), "+D"(di) :: "memory");
    printf("rep movsb rcx=0 unmapped: rcx=%llu rsi=%llx rdi=%llx (no fault)\n", (unsigned long long)c, (unsigned long long)si, (unsigned long long)di);
  }
  /* 4. overlapping forward REP MOVSB, dst = src + 1 */
  {
    unsigned char b[16] = {0x50,1,2,3,4,5,6,7};
    uint64_t c = 4; unsigned char *si = b, *di = b + 1;
    __asm__ volatile("rep movsb" : "+c"(c), "+S"(si), "+D"(di) :: "memory");
    printf("rep movsb overlap: %02x %02x %02x %02x %02x\n", b[0], b[1], b[2], b[3], b[4]);
  }
  /* 5. DF = 1: the same REP MOVSB bytes copy BACKWARDS (model assumes DF = 0) */
  {
    unsigned char src[8] = {1,2,3,4,5,6,7,8}, dst[8] = {0};
    uint64_t c = 4; unsigned char *si = src + 3, *di = dst + 3;
    __asm__ volatile("std; rep movsb; cld" : "+c"(c), "+S"(si), "+D"(di) :: "memory");
    printf("DF=1 rep movsb: dst=%d %d %d %d, rsi moved by %td (model: +4 forward)\n", dst[0], dst[1], dst[2], dst[3], si - (src + 3));
  }
  /* 6. BSF r64 of 0: destination unchanged on this CPU */
  {
    uint64_t d = 0x1234, s = 0;
    __asm__ volatile("bsfq %1, %0" : "+r"(d) : "r"(s) : "cc");
    printf("bsf64 0: dst=%llx\n", (unsigned long long)d);
    uint64_t d2 = 0xFFFFFFFF00001234ull; uint32_t s2 = 0;
    __asm__ volatile("bsfl %1, %k0" : "+r"(d2) : "r"(s2) : "cc");
    printf("bsf32 0: dst=%016llx (model faults: undefinedResult)\n", (unsigned long long)d2);
  }
  /* 7. F3 0F BD (LZCNT) vs BSR: on this CPU (ABM) it is LZCNT */
  {
    uint64_t d, s = 1;
    __asm__ volatile(".byte 0xf3, 0x48, 0x0f, 0xbd, 0xc1" : "=a"(d) : "c"(s) : "cc");
    printf("F3 48 0F BD C1 (x=1): %llu (LZCNT=63, BSR=0)\n", (unsigned long long)d);
  }
  /* 8. XCHG eax,eax via 87 C0 zero-extends; 90 does not */
  {
    uint64_t a = 0xFFFFFFFF00000001ull;
    __asm__ volatile(".byte 0x87, 0xc0" : "+a"(a));
    printf("87 C0: rax=%016llx\n", (unsigned long long)a);
    a = 0xFFFFFFFF00000001ull;
    __asm__ volatile(".byte 0x90" : "+a"(a));
    printf("90:    rax=%016llx\n", (unsigned long long)a);
  }
  /* 9. IMUL r/m64 one-operand, signed: -5 * 7 */
  {
    uint64_t a = (uint64_t)-5, d, c = 7;
    __asm__ volatile("imulq %2" : "+a"(a), "=d"(d) : "r"(c) : "cc");
    printf("imul1 -5*7: rax=%016llx rdx=%016llx\n", (unsigned long long)a, (unsigned long long)d);
  }
  return 0;
}
