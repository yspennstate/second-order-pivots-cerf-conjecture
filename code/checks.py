"""Checks for "A counterexample to a conjecture of Cerf on second-order pivots".

1. Exhaustive check over all increasing families on n <= 5 coordinates:
   the maxima of phi_2 and phi_{2\1} under the literal definition and under
   the occupied-coordinate reading, whether every maximizer lies in the band,
   and the agreement of the definition with the pair-witness description
   (Lemma 2.2) on occupied coordinates.
2. The clause-graph lemma (Lemma 5.1) on every array with n = 3, r = 2, M = 3,
   repeated coordinates included.
3. The exact rational inequalities used in the proof, for h = 10^7 and for
   the smallest admissible h in Remark 6.2.

Writes checks.json next to this file. Standard library only.
"""
import itertools
import json
import pathlib
import time
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent


def p1(A, w, n):
    """Positive pivots: i with w (i set to 0) not in A and w (i set to 1) in A."""
    return {i for i in range(n) if (w & ~(1 << i)) not in A and (w | (1 << i)) in A}


def p2_literal(A, w, n):
    """Formula (49.1) of Cerf with k = 2: I empty or I = {j} with w(j) = 1."""
    ans = p1(A, w, n)
    for j in range(n):
        if w >> j & 1:
            ans |= p1(A, w & ~(1 << j), n)
    return ans


def p2_pair(A, w, n):
    """Occupied second pivots through the pair witness of Lemma 2.2 (w in A)."""
    ans = {i for i in range(n) if w >> i & 1 and (w & ~(1 << i)) not in A}
    for i in range(n):
        if not w >> i & 1:
            continue
        for j in range(n):
            if i != j and w >> j & 1 and (w & ~(1 << j)) in A \
                    and (w & ~(1 << j) & ~(1 << i)) not in A:
                ans.add(i)
    return ans


def upsets(n):
    if n == 0:
        return [0, 1]
    prev = upsets(n - 1)
    shift = 1 << (n - 1)
    return [a | (b << shift) for a in prev for b in prev if a & ~b == 0]


def small_cube():
    rows = []
    for n in range(1, 6):
        occ_mask = None
        best = {}
        for mask in upsets(n):
            A = {w for w in range(1 << n) if mask >> w & 1}
            vals = {"lit2": 0, "lit21": 0, "occ2": 0, "occ21": 0}
            for w in A:
                occ = {i for i in range(n) if w >> i & 1}
                lit = p2_literal(A, w, n)
                pair = p2_pair(A, w, n)
                assert lit & occ == pair, (n, mask, w)
                first = p1(A, w, n)
                assert first <= occ
                vals["lit2"] += len(lit)
                vals["lit21"] += len(lit - first)
                vals["occ2"] += len(pair)
                vals["occ21"] += len(pair - first)
            inband = all(w in A for w in range(1 << n) if 2 * bin(w).count("1") >= n + 2) \
                and all(2 * bin(w).count("1") >= n - 4 for w in A)
            for key, v in vals.items():
                b = best.setdefault(key, [-1, 0, 0])
                if v > b[0]:
                    best[key] = [v, 1, int(not inband)]
                elif v == b[0]:
                    b[1] += 1
                    b[2] += int(not inband)
        row = {"n": n, "increasing_families": len(upsets(n))}
        for key, (v, cnt, out) in best.items():
            row[key] = {"max": v, "maximizers": cnt, "maximizers_outside_band": out}
        rows.append(row)
        print("1.", row, flush=True)
    assert [r["occ2"]["max"] for r in rows] == [1, 4, 9, 24, 62]
    assert [r["occ21"]["max"] for r in rows] == [0, 2, 6, 12, 38]
    return rows


def clause_graph():
    n, r, M = 3, 2, 3
    arrays = pairs = 0
    for tup in itertools.product(range(n), repeat=r * M):
        clauses = [tup[k * r:(k + 1) * r] for k in range(M)]
        A = {w for w in range(1 << n) if all(any(w >> i & 1 for i in c) for c in clauses)}
        for w in A:
            S, edges = set(), []
            for c in clauses:
                pos = [i for i in c if w >> i & 1]
                distinct = set(pos)
                if len(distinct) == 1:
                    S |= distinct
                if len(pos) == 2 and len(distinct) == 2:
                    edges.append(distinct)
            C = set().union(*edges) if edges else set()
            bad = [e for e in edges if e & S]
            vbad = set().union(*bad) if bad else set()
            assert S == p1(A, w, n)
            second_only = p2_literal(A, w, n) - S
            assert C - vbad <= second_only
            assert len(second_only) >= len(C) - 2 * len(bad)
            pairs += 1
        arrays += 1
    print("2. clause-graph lemma holds on all", arrays, "arrays and", pairs,
          "successful array/support pairs", flush=True)
    return {"arrays": arrays, "successful_pairs": pairs}


def margins(h):
    assert h % 10 == 0
    n, r = h * h, h // 10
    out = {
        "h": h, "n": str(n), "r": r,
        "graph_lower_r2/12-288r3/n": str(Fraction(r * r, 12) - Fraction(288 * r ** 3, n)),
        "r2/24": str(Fraction(r * r, 24)),
        "final_lower_r2/2592": str(Fraction(r * r, 2592)),
        "band_upper_10h": 10 * h,
        "Mt_upper_32r2/(3n)": str(Fraction(32 * r * r, 3 * n)),
        "E3_parameter": str(r * (Fraction(2, h) + Fraction(2, n))),
    }
    assert Fraction(r * r, 12) - Fraction(288 * r ** 3, n) >= Fraction(r * r, 24)
    assert Fraction(32 * r * r, 3 * n) < 1
    assert r * (Fraction(2, h) + Fraction(2, n)) < Fraction(1, 4)
    assert Fraction(r * r, 2592) > 10 * h
    assert 3 * h * h >= 6  # n >= 6 so that n/3 <= s - 1 in the central range
    print("3.", out, flush=True)
    return out


if __name__ == "__main__":
    t0 = time.time()
    res = {"small_cube": small_cube(), "clause_graph": clause_graph(),
           "margins": [margins(10 ** 7), margins(2592010)]}
    try:
        margins(2592000)
        res["h_2592000_fails"] = False
    except AssertionError:
        res["h_2592000_fails"] = True
    assert res["h_2592000_fails"]
    print("3. the final inequality fails at h = 2592000, as stated", flush=True)
    res["seconds"] = round(time.time() - t0, 1)
    (ROOT / "checks.json").write_text(json.dumps(res, indent=2), encoding="utf8")
    print("all checks passed in", res["seconds"], "s", flush=True)
