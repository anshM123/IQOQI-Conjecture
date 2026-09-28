"""Consolidated exact certificates of condition (C) for the explicit LC construction of v_k.
Each entry: (d, k) -> (matchings per tail j = n..d-1, mixing parameters theta per pair).
Run: python certs.py  -> re-verifies every certificate with exact sympy rationals.
"""
from fractions import Fraction as F
from certify_c import certify

H = F(1, 2)
CERTS = {
    (5, 2): ([[(0, 2)], [(0, 2)]], [[H], [H]]),
    (5, 3): ([[(0, 3), (1, 2)]], [[H, H]]),
    (6, 2): ([[(0, 2)]] * 3, [[H]] * 3),
    (6, 3): ([[(0, 3), (1, 2)]] * 2, [[H, H]] * 2),
    (6, 4): ([[(0, 4), (1, 3)]], [[H, H]]),
    (7, 2): ([[(0, 2)]] * 4, [[H]] * 4),
    (7, 3): ([[(0, 3), (1, 2)], [(0, 1), (2, 3)], [(0, 2), (1, 3)]], [[H, H], [F(1), F(1)], [H, H]]),
    (7, 4): ([[(0, 3), (1, 4)], [(0, 4), (1, 3)]], [[H, F(4, 7)], [F(5, 7), F(7, 8)]]),
    (7, 5): ([[(0, 2), (1, 3), (4, 5)]], [[H, H, H]]),
    (8, 2): ([[(0, 2)], [(1, 2)], [(0, 1)], [(0, 2)], [(0, 2)]], [[F(5, 7)], [F(1)], [F(1)], [F(1)], [F(0)]]),
    (8, 3): ([[(0, 3), (1, 2)], [(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 3), (1, 2)]],
             [[F(4, 7), F(2, 3)], [F(1), F(1)], [F(1), F(1)], [F(0), F(1)]]),
}

if __name__ == "__main__":
    import sys
    allok = True
    for (d, k), (Ms, ths) in CERTS.items():
        ok, bad = certify(d, k, Ms, thetas=ths, verbose=True, polya_max=4)
        print(f"d={d} k={k}: matchings={Ms} theta={[[str(t) for t in tt] for tt in ths]} -> certified {ok}", flush=True)
        allok &= ok
    print("ALL CERTIFIED:", allok)
