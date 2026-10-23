# Random words biased to the classes the Janus decoder accepts (op0 = 100x, 101x, x1x0, x101).
import random, sys
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
n = int(sys.argv[1])
for _ in range(n):
    w = random.getrandbits(32)
    c = random.randrange(4)
    op0 = [random.choice([8,9]), random.choice([10,11]), random.choice([4,6,12,14]), random.choice([5,13])][c]
    w = (w & ~(0xF << 25)) | (op0 << 25)
    print(hex(w))
