#!/usr/bin/env python3
"""Independent check of the construction for the easy direction of OEIS A400868.

Rule: the winner of a turn puts the LOSING card, then the WINNING card, at the
bottom of their pile.

For every n <= N that is not a power of 2 (default N = 200):
  1. write n = m * 2^k with m odd >= 3 and build the labelled position
     P1 = (B_k(1) B_k(2))^((m-1)/2),  P2 = B_k(2),  B_k(v)_i = v - k + popcount(i);
  2. check that the labelled game returns to its start after 2^(k+1) turns
     with no tie at any turn (so it never ends);
  3. realise the labels by the distinct cards 1..n (ties broken by position);
  4. rewind pairs from the end of the longer pile to obtain a balanced deal
     (ceil(n/2), floor(n/2)) and replay it forward to the realised position.
Usage: python3 construct_and_replay.py [N]
"""
import sys
from collections import deque

def step(p1, p2):
    x, y = p1.popleft(), p2.popleft()
    assert x != y, "tie"
    if x > y: p1.extend((y, x))
    else:     p2.extend((x, y))

def block(k, v):
    return [v - k + bin(i).count("1") for i in range(2 ** k)]

def check(n):
    k = (n & -n).bit_length() - 1
    m = n >> k
    assert m >= 3 and m % 2 == 1
    a = (m - 1) // 2
    p1 = (block(k, 1) + block(k, 2)) * a
    p2 = block(k, 2)
    assert len(p1) + len(p2) == n
    # 2. labelled loop, no ties
    q1, q2 = deque(p1), deque(p2)
    for _ in range(2 ** (k + 1)):
        assert q1 and q2
        step(q1, q2)
    assert list(q1) == p1 and list(q2) == p2, "labelled loop does not close"
    # 3. realisation by distinct cards
    occ = [(v, 0, i) for i, v in enumerate(p1)] + [(v, 1, i) for i, v in enumerate(p2)]
    rank = {o: r + 1 for r, o in enumerate(sorted(occ))}
    r1 = [rank[(v, 0, i)] for i, v in enumerate(p1)]
    r2 = [rank[(v, 1, i)] for i, v in enumerate(p2)]
    assert sorted(r1 + r2) == list(range(1, n + 1))
    # the realised game makes the same comparisons as the labelled one, hence never ends
    q1, q2, l1, l2 = deque(r1), deque(r2), deque(p1), deque(p2)
    for _ in range(2 ** (k + 1)):
        x, y, u, v = q1[0], q2[0], l1[0], l2[0]
        assert (x > y) == (u > v)
        step(q1, q2); step(l1, l2)
    # 4. rewind to a balanced deal (P1 is the longer pile here)
    s1, s2 = list(r1), list(r2)
    c = (n + 1) // 2
    d = len(s1) - c
    assert d >= 0 and 2 * d <= len(s1) - 1
    for _ in range(d):
        l, w = s1[-2], s1[-1]
        assert l < w
        s1, s2 = [w] + s1[:-2], [l] + s2
    assert len(s1) == c and len(s2) == n // 2
    deal = (list(s1), list(s2))
    q1, q2 = deque(s1), deque(s2)
    for _ in range(d):
        step(q1, q2)
    assert list(q1) == r1 and list(q2) == r2, "rewound deal does not reach the construction"
    return deal

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    count = 0
    for n in range(1, N + 1):
        if n & (n - 1):
            deal = check(n)
            count += 1
            if n <= 12:
                print(f"n={n:3d}  never-ending deal: {deal[0]} | {deal[1]}")
    print(f"OK: construction, realisation and balanced deal checked for all {count} n <= {N} that are not powers of 2.")
