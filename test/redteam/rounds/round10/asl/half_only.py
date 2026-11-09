import sys; sys.path.insert(0, sys.argv[1])
import sqrt_model as M
for b in range(1 << 16): M.check(b, 16)
print('half comparisons', sum(M.stats.values()), 'MISMATCHES', len(M.bad), dict(M.stats))
for r in M.bad[:10]: print(r)
