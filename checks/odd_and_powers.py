#!/usr/bin/env python3
"""Exhaustive checks for OEIS A400868 (losing card, then winning card).

(a) For n = 2, 4, 8: no position lies on a cycle.
(b) For odd n <= 9: in every cycle, the card that won its previous turn (role W)
    beats the card that lost its previous turn (role L) at every turn; hence
    every card keeps its role and the winners alternate (Theorem 2 of the paper).

Every cycle passes through a position with card n on top of some pile; up to
swapping the players, it is enough to start from positions with n on top of P1.
Usage: python3 odd_and_powers.py
"""
import itertools
from collections import deque

def step(p1, p2):
    x, y = p1[0], p2[0]
    p1, p2 = p1[1:], p2[1:]
    return (p1 + (y, x), p2) if x > y else (p1, p2 + (x, y))

def cycles(n):
    found = {}
    for perm in itertools.permutations(range(1, n)):
        for k in range(n - 1):
            s = ((n,) + perm[:k], perm[k:])
            t, seen = s, set()
            while t[0] and t[1] and t not in seen:
                seen.add(t); t = step(*t)
            if t == s:
                found[min(seen)] = len(seen)
    return found

def odd_check(n, cyc):
    for s, L in cyc.items():
        t, role = s, {}
        for i in range(3 * L):
            x, y = t[0][0], t[1][0]
            if i >= L:   # every card has played at least once
                assert role[x] != role[y], "two tops with the same role"
                w = x if role[x] == "W" else y
                assert max(x, y) == w, "an L card beat a W card"
            role[min(x, y)], role[max(x, y)] = "L", "W"
            t = step(*t)

for n in (2, 4, 8):
    c = cycles(n)
    assert not c
    print(f"n={n}: no cycle (exhaustive)")
for n in (3, 5, 7, 9):
    c = cycles(n)
    odd_check(n, c)
    print(f"n={n}: {len(c)} cycles through 'n on top of P1'; W beats L at every turn")
print("OK")
