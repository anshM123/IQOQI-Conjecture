"""DOUBLING LEMMA: hook decomposition for M  ->  for 2M.
new hook c      (c<M):  1/2 old_c on A + 1/2 old_c on B
new hook M+c    (c<M):  1/2 old_{M-1-c} on A + 1/2 old_{M-1-c} on B + old_c on the cross block A x B."""
import sys
from fractions import Fraction as F
from hookio import load, save, check

def double(Ys):
    M = len(Ys); N = 2 * M
    new = []
    half = F(1, 2)
    for b in range(N):
        Y = [[F(0)] * N for _ in range(N)]
        c = b if b < M else M - 1 - (b - M)
        O = Ys[c]
        for i in range(M):
            for j in range(M):
                Y[i][j] += half * O[i][j]
                Y[M + i][M + j] += half * O[i][j]
        if b >= M:
            X = Ys[b - M]
            for i in range(M):
                for j in range(M):
                    Y[i][M + j] += X[i][j]
                    Y[M + j][i] += X[i][j]
        new.append(Y)
    return new

if __name__ == "__main__":
    base = '../stu3/hookdec_n{}.txt'
    for M in [int(v) for v in sys.argv[1:]]:
        Ys = load(base.format(M), M)
        ok0 = check(Ys)
        D = double(Ys)
        print(M, '->', 2 * M, 'base ok:', ok0[0], ' doubled ok:', check(D))
