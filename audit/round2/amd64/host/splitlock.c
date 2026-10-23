/* LOCK XADDQ on a word that straddles a 64-byte cache line (p = line + 60).
   The AtomicAdd theorem's precondition admits such p (no alignment requirement) and the model
   returns normally. On Linux with split-lock detection the CPU raises #AC:
     split_lock_detect=warn  (default)  -> kernel logs "took a split_lock trap", throttles
                                           (split_lock_mitigate=1), result is correct;
     split_lock_detect=fatal            -> SIGBUS: the call never returns.
   Build: gcc -O1 -o splitlock splitlock.c && ./splitlock ; dmesg | grep -i split | tail -2 */
#include <stdio.h>
#include <stdint.h>
#include <signal.h>
#include <stdlib.h>
static void onbus(int s) { (void)s; puts("SIGBUS: split-lock #AC was fatal"); exit(2); }
int main(void) {
  static _Alignas(64) unsigned char buf[192];
  signal(SIGBUS, onbus);
  uint64_t *p = (uint64_t *)(buf + 64 + 60);
  *p = 40; uint64_t d = 2;
  __asm__ volatile("lock xaddq %0, %1" : "+r"(d), "+m"(*p) :: "cc", "memory");
  printf("lock xadd at line+60 returned: old=%llu new=%llu (warn mode or no detection)\n",
         (unsigned long long)d, (unsigned long long)*p);
  return 0;
}
