"""Check a 2-colouring of the t-subsets of the points 0..n-1 against the definition of a Ramsey lower bound.

    python verify.py R553_98_points.csv 5 5

The CSV has one row per t-subset: its t points, then its colour (0 or 1). The first row is a header.
PASS means: no A points have all their t-subsets in colour 0, and no B points have all their t-subsets in colour 1
(A and B are the two numbers on the command line). That shows R(A,B;t) >= n + 1.

Standard library only. It reads nothing but the CSV and shares no code with the program that found the colourings.
"""
import csv
import sys
import time
from itertools import combinations
from math import comb

path, sizes = sys.argv[1], (int(sys.argv[2]), int(sys.argv[3]))
t0 = time.time()
rows = [r for r in csv.reader(open(path, newline="")) if r and r[0].strip().isdigit()]
t = len(rows[0]) - 1
colour = {}
for r in rows:
    pts = tuple(sorted(int(x) for x in r[:t]))
    assert len(r) == t + 1 and len(set(pts)) == t and pts[0] >= 0, f"bad row {r}"
    assert pts not in colour, f"the subset {pts} appears twice"
    assert r[t].strip() in ("0", "1"), f"bad colour in row {r}"
    colour[pts] = int(r[t])
n = max(p[-1] for p in colour) + 1
assert len(colour) == comb(n, t), f"{len(colour)} subsets given, {comb(n, t)} needed for {n} points"
assert min(sizes) > t


def one_coloured_set(c, size):
    """`size` points whose t-subsets all have colour c, or None.

    A set is grown one point at a time, always by a larger point, and a new point is accepted only if every t-subset
    that contains it has colour c. Every one-coloured set is reached this way (take its points in increasing order:
    each beginning of it is one-coloured too), so None means that there is none."""
    def grow(pts):
        if len(pts) == size:
            return pts
        for p in range(pts[-1] + 1, n):
            if all(colour[s + (p,)] == c for s in combinations(pts, t - 1)):
                found = grow(pts + (p,))
                if found:
                    return found
        return None
    for base in combinations(range(n), t):
        if colour[base] == c:
            found = grow(base)
            if found:
                return found
    return None


print(f"{path}: {n} points, {len(colour)} {t}-subsets, {sum(v == 0 for v in colour.values())} in colour 0")
bad = [(c, one_coloured_set(c, sizes[c])) for c in (0, 1)]
for c, found in bad:
    what = f"{sizes[c]} points with all {comb(sizes[c], t)} {t}-subsets in colour {c}"
    print(f"  colour {c}: " + (f"FOUND {what}: {found}" if found else f"no {what}"))
ok = not any(found for _c, found in bad)
print(("PASS" if ok else "FAIL") + f": R({sizes[0]},{sizes[1]};{t}) >= {n + 1}" * ok + f"   ({time.time() - t0:.0f} s)")
sys.exit(0 if ok else 1)
