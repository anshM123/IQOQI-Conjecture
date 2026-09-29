"""Small numerical facts quoted in main.tex (exact Fractions unless stated):
  * the plain renewal difference (alpha = 0) fails for (n,lo,hi) = (12,10,10): its negative entries are
    -677/4620 (minimum, at the central cells (5,6),(6,5)), -59/420, -9/70, -1/10 (the value -1/10 quoted in the
    research log unif/LOG.md is one of them, at cells (2,9),(9,2));
    with the case-(D) amplitude 2/7 all entries lie in [0,1];
  * exact rational enclosures of a(1), a(2), a(3) from Lemma B:
      a(1) in [15/64 - 343/46656, 15/64], a(2) in [67/729 - 1297/746496, 67/729],
      a(3) in [193/4096 - 31689/64000000, 193/4096];
    and F5, F6 follow from these fractions alone;
  * u(2) = 79/256, u(3) = 1127/5832, u(4) = 2297/16384.
"""
import os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_constructions_lib import dipole_matrix, renewal_closed
FAILS = []
def ok(name, cond):
    print(('OK   ' if cond else 'FAIL ') + name, flush=True)
    if not cond: FAILS.append(name)
Y0 = dipole_matrix(12, 10, 10, F(0))
P, N = renewal_closed(12, 10), renewal_closed(12, 9)
ok('(12,10,10): alpha = 0 matrix equals U^10_12 - U^9_12', all(Y0[i][j] == P[i][j] - N[i][j] for i in range(12) for j in range(12)))
mn = min(min(r) for r in Y0)
ok(f'(12,10,10): minimal entry of the renewal difference is {mn} = -677/4620', mn == F(-677, 4620))
ok('(12,10,10): the entry -1/10 occurs at (2,9) and (9,2)', Y0[2][9] == F(-1, 10) and Y0[9][2] == F(-1, 10))
where = [(i, j) for i in range(12) for j in range(12) if Y0[i][j] == mn]
print('   attained at cells', where)
Y1 = dipole_matrix(12, 10, 10, F(2, 7))
ok('(12,10,10): with alpha = 2/7 all entries in [0,1]', all(0 <= v <= 1 for r in Y1 for v in r))
def uF(y):
    y = F(y); return 1/(2*y) + F(1,4)/y**2 - F(1,8)/y**4 + F(1,4)/y**6
def eF(y):
    y = F(y); return (17*y**4 + 34*y**3 + 29*y**2 + 12*y + 2)/(8*y**6*(y+1)**6)
ok('u(2) = 79/256, u(3) = 1127/5832, u(4) = 2297/16384', uF(2) == F(79,256) and uF(3) == F(1127,5832) and uF(4) == F(2297,16384))
enc = {K: (4*K*K*(uF(K+1)-eF(K+1)) + 1 - 2*K, 4*K*K*uF(K+1) + 1 - 2*K) for K in (1,2,3)}
ok('a(1) in [15/64 - 343/46656, 15/64]', enc[1] == (F(15,64) - F(343,46656), F(15,64)))
ok('a(2) in [67/729 - 1297/746496, 67/729]', enc[2] == (F(67,729) - F(1297,746496), F(67,729)))
ok('a(3) in [193/4096 - 31689/64000000, 193/4096]', enc[3] == (F(193,4096) - F(31689,64000000), F(193,4096)))
for K in (1,2,3):
    print(f'   a({K}) in [{float(enc[K][0]):.7f}, {float(enc[K][1]):.7f}]')
a1l, a1h = enc[1]; a2l, a2h = enc[2]; a3l, a3h = enc[3]
ok('F5(i):  a1l - 2/21 - a3h > 0', a1l - F(2,21) - a3h > 0)
ok('F5(ii): a1h - 2/21 + a2h <= 2/7', a1h - F(2,21) + a2h <= F(2,7))
ok('F5(iii): a1h < 5/21', a1h < F(5,21))
ok('F6: a1h < 1/4 and a3h < 1/20', a1h < F(1,4) and a3h < F(1,20))
print('   F5(i) lower bound', float(a1l - F(2,21) - a3h), '; F5(ii) slack', float(F(2,7) - a1h + F(2,21) - a2h), '; F5(iii) slack', float(F(5,21) - a1h))
# decimal enclosures used in Lean (aF_one_bounds etc.) contain these
ok('Lean decimals: 0.227 < a1l, a1h < 0.2344; 0.0901 < a2l, a2h < 0.092; 0.0466 < a3l, a3h < 0.0472',
   F(227,1000) < a1l and a1h < F(2344,10000) and F(901,10000) < a2l and a2h < F(92,1000) and F(466,10000) < a3l and a3h < F(472,10000))
# cross-check of the amplitude rule (cases C/D/E and the alpha* formula of main.tex, eq. (8.2)) against the
# public package's construct.py (which uses alpha* = -A_ren/(2 omega(K+1)), rationalised to 1e-40)
sys.dont_write_bytecode = True
PUB = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..',
                                    'publish', 'IQOQI-Conjecture', 'code'))
sys.path.insert(0, PUB)
import construct as pubconstruct                     # noqa: E402
from check_constructions_lib import amplitude, case_of  # noqa: E402
maxdiff = 0.0
agree = True
for n in list(range(3, 41)) + [60, 101, 150]:
    for hi in range(1, n - 1):
        for lo in range(1, hi + 1):
            mine = amplitude(n, lo, hi)                   # Fraction (alpha* rationalised to 1e-30)
            pub = pubconstruct.amplitudes(n, lo, hi)      # {} or {hi: Fraction}
            pubv = pub.get(hi, F(0)) if pub else F(0)
            if (mine == 0) != (pubv == 0):
                agree = False
            maxdiff = max(maxdiff, abs(float(mine - pubv)))
ok(f'amplitude rule (C/D/E, alpha*) agrees with publish/code/construct.py for all 1<=lo<=hi<=n-2, n<=40 and n in {{60,101,150}} (max |diff| = {maxdiff:.1e})',
   agree and maxdiff < 1e-25)

print(); print('FAILURES:' , FAILS) if FAILS else print('ALL SMALL-VALUE CHECKS PASSED')
sys.exit(1 if FAILS else 0)
