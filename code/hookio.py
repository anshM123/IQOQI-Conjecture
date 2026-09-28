"""I/O and exact checking of hook decompositions as symmetric matrices Y[a] (list of N x N Fraction matrices)."""
from fractions import Fraction as F
from collections import defaultdict

def load(path, N):
    x = defaultdict(F)
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('#'): continue
            a, s, i, v = line.split(); x[(int(a), int(s), int(i))] += F(v)
    Ys = []
    for a in range(N):
        Y = [[F(0)] * N for _ in range(N)]
        for s in range(a + 1):
            for i in range(N - s):
                v = x[(a, s, i)]
                Y[i][i + s] += v
                if s: Y[i + s][i] += v
        Ys.append(Y)
    return Ys

def to_x(Ys):
    N = len(Ys); out = {}
    for a, Y in enumerate(Ys):
        for s in range(N):
            for i in range(N - s):
                v = Y[i][i + s]
                if v != 0: out[(a, s, i)] = v
    return out

def save(path, Ys, note=''):
    N = len(Ys); x = to_x(Ys)
    with open(path, 'w') as f:
        f.write(f'# hook decomposition of the {N}-box {note}: a s i value\n')
        for (a, s, i), v in sorted(x.items()):
            f.write(f'{a} {s} {i} {v}\n')

def check(Ys):
    """exact check of all conditions (symmetric-matrix form). returns (ok, message)."""
    N = len(Ys)
    for a, Y in enumerate(Ys):
        for i in range(N):
            for j in range(N):
                if Y[i][j] != Y[j][i]: return False, ('asym', a, i, j)
                if Y[i][j] < 0: return False, ('neg', a, i, j, Y[i][j])
        for s in range(N):
            c = sum(Y[i][i + s] for i in range(N - s))
            if c != (1 if s <= a else 0): return False, ('run', a, s, c)
        for r in range(N):
            if sum(Y[r]) != F(2 * a + 1, N): return False, ('row', a, r, sum(Y[r]))
    for i in range(N):
        for j in range(N):
            if sum(Y[i][j] for Y in Ys) != 1: return False, ('cell', i, j)
    return True, 'ok'
