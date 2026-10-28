"""Checks for the report on the 4-RGDD of type 10^4 (equivalently 3 MOLS(10)).

usage:
  python3 verify_10_4.py              check every object printed in 4rgdd_10_4.tex
  python3 verify_10_4.py triple FILE  check a candidate triple of MOLS(10): FILE holds
                                      300 integers 0..9 (three 10x10 squares, row by row);
                                      the 4-RGDD of type 10^4 of Theorem 2.2 is built and
                                      checked directly from the definition

Everything is checked from first principles (pair coverage, partitions); nothing is
taken from the search program.
"""
import itertools
import re
import sys

N = 10

# Fig. 1 of A.E. Brouwer, Four MOLS of order 10 with a hole of order 2,
# J. Statist. Plann. Inference 10 (1984) 203-205.  Cell (i,j) lists the entries of
# the four squares; '-' marks the 2x2 hole (rows/columns 8,9; hole symbols 8,9).
BROUWER_FIG1 = """
5039 8225 4568 9753 6812 0390 2487 7976 3141 1604
9460 6109 8336 5678 4947 7823 1091 3584 0252 2715
6748 9571 7219 8007 0685 5954 4830 2192 1363 3426
8114 7458 9642 4329 3293 1786 6965 5801 2070 0537
2856 4794 6083 3932 1479 8661 0128 9317 7505 5240
0903 3867 5495 7180 9024 2549 8772 1238 4616 6351
4281 1910 0874 6596 2308 9135 3659 8443 5727 7062
7697 5382 2921 1845 8550 3018 9206 0769 6434 4173
1522 2633 3700 0411 5166 6277 7344 4055 - -
3375 0046 1157 2264 7731 4402 5513 6620 - -
"""

NEARMISS = [
    # Section 5.2: the near triple of Egan and Wanless, Math. Comp. 85 (2016) 799-824,
    # Section 8 (A orthogonal to B and C; B, C give 91 distinct pairs).
    dict(name="Egan-Wanless triple",
         A="""
0 8 9 7 5 6 4 2 3 1
9 1 4 6 2 7 3 8 0 5
7 4 2 5 1 3 8 6 9 0
8 6 5 3 9 2 1 0 4 7
6 2 1 8 4 0 9 5 7 3
4 9 3 2 7 5 0 1 6 8
5 3 7 1 0 8 6 9 2 4
3 5 0 9 8 4 2 7 1 6
1 7 6 0 3 9 5 4 8 2
2 0 8 4 6 1 7 3 5 9
""",
         B="""
0 7 8 9 1 2 3 4 5 6
9 0 6 1 8 3 2 5 4 7
7 2 0 4 3 9 1 8 6 5
8 5 3 0 2 1 7 6 9 4
6 9 5 3 0 7 4 2 1 8
4 1 7 6 5 0 8 9 3 2
5 4 2 8 9 6 0 3 7 1
3 6 1 7 4 8 5 0 2 9
1 8 4 2 6 5 9 7 0 3
2 3 9 5 7 4 6 1 8 0
""",
         C="""
0 7 8 9 1 2 3 4 5 6
6 4 2 8 9 5 1 3 7 0
4 9 5 3 2 7 6 0 1 8
5 1 7 6 4 3 8 9 0 2
3 2 9 0 7 1 5 6 8 4
1 0 3 7 6 8 2 5 4 9
2 8 0 1 3 4 9 7 6 5
9 5 4 2 8 6 0 1 3 7
7 3 6 5 0 9 4 8 2 1
8 6 1 4 5 0 7 2 9 3
"""),
    # Section 5.3: an orthogonal pair (A, B) found by the search and 3 pairwise
    # disjoint common transversals (partial third square; '.' = no symbol).
    dict(name="search pair (nu = 3)",
         A="""
7 2 1 4 5 8 6 9 0 3
3 4 5 0 8 6 9 7 1 2
6 5 8 3 9 2 0 1 7 4
1 3 4 7 2 9 8 0 6 5
9 1 3 8 0 7 5 2 4 6
2 0 9 6 7 3 1 4 5 8
8 9 2 5 1 0 4 6 3 7
5 8 0 1 6 4 7 3 2 9
0 7 6 2 4 5 3 8 9 1
4 6 7 9 3 1 2 5 8 0
""",
         B="""
5 6 2 4 1 7 3 8 9 0
7 5 9 1 6 2 0 4 8 3
4 7 0 2 9 1 5 3 6 8
9 8 7 3 4 5 2 0 1 6
2 1 6 8 3 9 4 7 0 5
0 2 3 7 8 4 6 1 5 9
1 4 5 0 7 8 9 6 3 2
8 3 4 5 0 6 7 9 2 1
6 0 8 9 2 3 1 5 7 4
3 9 1 6 5 0 8 2 4 7
""",
         Cpartial="""
. . . . 0 1 . . 2 .
. . . 1 . 2 . . . 0
. . 2 . . . . . 0 1
1 0 . . . . . . . 2
0 . . . . . 1 2 . .
. . 1 0 2 . . . . .
. 2 . . . . 0 1 . .
. . 0 2 . . . . 1 .
. 1 . . . . 2 0 . .
2 . . . 1 0 . . . .
"""),
]  # @NEARMISS@


def parse_square(text):
    v = [int(x) for x in text.split()]
    assert len(v) == N * N
    return [v[i * N:(i + 1) * N] for i in range(N)]


def parse_partial(text):
    v = [None if x == '.' else int(x) for x in text.split()]
    assert len(v) == N * N
    return [v[i * N:(i + 1) * N] for i in range(N)]


def is_latin(L):
    full = set(range(N))
    return all(set(L[i]) == full for i in range(N)) and \
        all({L[i][j] for i in range(N)} == full for j in range(N))


def distinct_pairs(A, B):
    return len({(A[i][j], B[i][j]) for i in range(N) for j in range(N)})


def tdesign(A, B, cells):
    """Points r_i, c_j, a_s, b_t; one block {r_i, c_j, a_A(i,j), b_B(i,j)} per cell."""
    groups = [[(g, x) for x in range(N)] for g in 'rcab']
    blocks = {(i, j): frozenset({('r', i), ('c', j), ('a', A[i][j]), ('b', B[i][j])})
              for (i, j) in cells}
    return groups, blocks


def check_gdd(groups, blocks, hole=frozenset()):
    """Every pair of points from distinct groups, not both in the hole, lies in exactly
    one block; no block meets a group twice or the hole twice."""
    group_of = {p: k for k, G in enumerate(groups) for p in G}
    count = {}
    for B in blocks:
        if len(B) != 4 or len({group_of[p] for p in B}) != 4:
            raise ValueError(f"block {sorted(B)} is not a transversal of the groups")
        if len(B & hole) > 1:
            raise ValueError(f"block {sorted(B)} meets the hole twice")
        for p, q in itertools.combinations(sorted(B), 2):
            count[(p, q)] = count.get((p, q), 0) + 1
    pts = sorted(group_of)
    for p, q in itertools.combinations(pts, 2):
        want = 0 if group_of[p] == group_of[q] or (p in hole and q in hole) else 1
        if count.get((p, q), 0) != want:
            raise ValueError(f"pair {p},{q} covered {count.get((p, q), 0)} times, expected {want}")
    return len(blocks)


def check_classes(points, blocks_by_class):
    """Each class must partition `points` (given per class)."""
    for name, (pts, cls) in blocks_by_class.items():
        cover = [p for B in cls for p in B]
        if len(cover) != len(set(cover)) or set(cover) != set(pts):
            raise ValueError(f"class {name} is not a partition of its point set")


def rgdd_from_triple(A, B, C):
    """Theorem 2.2: blocks from (A,B), parallel classes = symbol classes of C."""
    for X in (A, B, C):
        if not is_latin(X):
            raise ValueError("not a Latin square")
    cells = [(i, j) for i in range(N) for j in range(N)]
    groups, blocks = tdesign(A, B, cells)
    nb = check_gdd(groups, list(blocks.values()))
    pts = [p for G in groups for p in G]
    classes = {s: (pts, [blocks[c] for c in cells if C[c[0]][c[1]] == s]) for s in range(N)}
    check_classes(pts, classes)
    return nb


def check_triple_file(path):
    v = [int(x) for x in re.findall(r'\d+', open(path).read())]
    if len(v) != 3 * N * N:
        raise ValueError(f"expected 300 entries, got {len(v)}")
    A, B, C = (parse_square(' '.join(map(str, v[k * 100:(k + 1) * 100]))) for k in range(3))
    for X, Y, nm in ((A, B, 'AB'), (A, C, 'AC'), (B, C, 'BC')):
        if distinct_pairs(X, Y) != 100:
            raise ValueError(f"squares {nm} are not orthogonal")
    nb = rgdd_from_triple(A, B, C)
    print(f"OK: three MOLS(10); the 4-RGDD of type 10^4 has 40 points, {nb} blocks, 10 parallel classes")


def brouwer():
    rows = [r.split() for r in BROUWER_FIG1.strip().splitlines()]
    hole_rc = {8, 9}
    sq = [[[None] * N for _ in range(N)] for _ in range(4)]
    for i, r in enumerate(rows):
        for j, c in enumerate(r):
            if c == '-':
                assert i in hole_rc and j in hole_rc
                continue
            for k in range(4):
                sq[k][i][j] = int(c[k])
    cells = [(i, j) for i in range(N) for j in range(N) if sq[0][i][j] is not None]
    assert len(cells) == 96
    # TD(6,10) - TD(6,2): six groups (rows, columns, four symbol sets), hole of size 2 in each
    groups6 = [[(g, x) for x in range(N)] for g in 'rc0123']
    hole6 = frozenset((g, x) for g in 'rc0123' for x in hole_rc)
    blocks6 = [frozenset({('r', i), ('c', j)} | {(str(k), sq[k][i][j]) for k in range(4)}) for (i, j) in cells]
    group_of = {p: k for k, G in enumerate(groups6) for p in G}
    count = {}
    for B in blocks6:
        assert len({group_of[p] for p in B}) == 6 and len(B & hole6) <= 1
        for p, q in itertools.combinations(sorted(B), 2):
            count[(p, q)] = count.get((p, q), 0) + 1
    for p, q in itertools.combinations(sorted(group_of), 2):
        want = 0 if group_of[p] == group_of[q] or (p in hole6 and q in hole6) else 1
        if count.get((p, q), 0) != want:
            raise ValueError("Brouwer: ITD(6,10;2) pair condition fails")
    print("OK: Brouwer's Fig. 1 is a TD(6,10)-TD(6,2) (four incomplete MOLS(10) with a hole of size 2), 96 blocks")
    # incomplete 4-RGDD of type 10^4 with hole of type 2^4: blocks from squares 0,1;
    # classes from the symbols of square 2 (full for s<8, holey for s in {8,9})
    A, B, C = sq[0], sq[1], sq[2]
    groups, blocks = tdesign(A, B, cells)
    hole = frozenset((g, x) for g in 'rcab' for x in hole_rc)
    nb = check_gdd(groups, list(blocks.values()), hole)
    pts = [p for G in groups for p in G]
    out = [p for p in pts if p not in hole]
    classes = {s: (pts if s < 8 else out, [blocks[c] for c in cells if C[c[0]][c[1]] == s]) for s in range(N)}
    check_classes(pts, classes)
    sizes = sorted(len(v[1]) for v in classes.values())
    assert sum(sizes) == nb == 96
    print(f"OK: 4-IRGDD of type (10,2)^4: {nb} blocks = 8 parallel classes of 10 blocks"
          f" + 2 holey parallel classes of 8 blocks (class sizes {sizes})")


def count_transversals(L):
    def rec(i, cols, syms):
        if i == len(L):
            return 1
        return sum(rec(i + 1, cols | {j}, syms | {L[i][j]})
                   for j in range(len(L)) if j not in cols and L[i][j] not in syms)
    return rec(0, frozenset(), frozenset())


def common_transversals(A, B):
    """All sets of cells that are transversals of both A and B."""
    out = []

    def rec(i, cols, sa, sb, cur):
        if i == N:
            out.append(tuple(cur))
            return
        for j in range(N):
            if j not in cols and A[i][j] not in sa and B[i][j] not in sb:
                cur.append(j)
                rec(i + 1, cols | {j}, sa | {A[i][j]}, sb | {B[i][j]}, cur)
                cur.pop()
    rec(0, frozenset(), frozenset(), frozenset(), [])
    return out


def max_disjoint(ts):
    """Largest number of pairwise disjoint transversals (cell sets) in the list ts."""
    cellsets = [frozenset(enumerate(t)) for t in ts]
    best = 0

    def rec(start, chosen, used):
        nonlocal best
        best = max(best, chosen)
        for k in range(start, len(cellsets)):
            if not (cellsets[k] & used):
                rec(k + 1, chosen + 1, used | cellsets[k])
    rec(0, 0, frozenset())
    return best


def no_transversal_order10_groups():
    def cayley_z10(x, y):
        return (x + y) % 10

    def cayley_d5(x, y):          # x = r^a s^e encoded a + 5e
        a, e, b, f = x % 5, x // 5, y % 5, y // 5
        return ((a - b) % 5 if e else (a + b) % 5) + 5 * ((e + f) % 2)

    for name, op in (('Z10', cayley_z10), ('D5', cayley_d5)):
        L = [[op(x, y) for y in range(N)] for x in range(N)]
        assert is_latin(L)
        cnt = count_transversals(L)
        print(f"OK: Cayley table of {name} has {cnt} transversals (no complete mapping)")
        assert cnt == 0


def nearmiss_checks():
    for item in NEARMISS:
        A, B = parse_square(item['A']), parse_square(item['B'])
        if not (is_latin(A) and is_latin(B) and distinct_pairs(A, B) == 100):
            raise ValueError(f"{item['name']}: A, B are not orthogonal Latin squares")
        cells = [(i, j) for i in range(N) for j in range(N)]
        groups, blocks = tdesign(A, B, cells)
        check_gdd(groups, list(blocks.values()))
        msg = f"OK: {item['name']}: A, B orthogonal; 4-GDD of type 10^4 with 100 blocks"
        if 'Cpartial' in item:
            Cp = parse_partial(item['Cpartial'])
            syms = sorted({x for r in Cp for x in r if x is not None})
            pts = [p for G in groups for p in G]
            classes = {s: (pts, [blocks[c] for c in cells if Cp[c[0]][c[1]] == s]) for s in syms}
            check_classes(pts, classes)
            ct = common_transversals(A, B)
            msg += (f"; {len(syms)} pairwise disjoint parallel classes;"
                    f" the 4-GDD has exactly {len(ct)} parallel classes in all, so it is not resolvable"
                    if len(ct) < N else f"; {len(syms)} pairwise disjoint parallel classes")
        if 'C' in item:
            C = parse_square(item['C'])
            assert is_latin(C)
            pts = [p for G in groups for p in G]
            good = [s for s in range(N)
                    if len({B[i][j] for (i, j) in cells if C[i][j] == s}) == N]
            classes = {s: (pts, [blocks[c] for c in cells if C[c[0]][c[1]] == s]) for s in good}
            check_classes(pts, classes)
            ct = common_transversals(A, B)
            nu = max_disjoint(ct)
            msg += (f"; third square C: pairs(A,C)={distinct_pairs(A, C)},"
                    f" pairs(B,C)={distinct_pairs(B, C)}; symbol classes {good} of C are"
                    f" {len(good)} disjoint parallel classes; the 4-GDD has {len(ct)} parallel"
                    f" classes in all, at most {nu} pairwise disjoint, so it is not resolvable")
            assert nu < N
        print(msg)


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[1] == 'triple':
        check_triple_file(sys.argv[2])
    else:
        brouwer()
        nearmiss_checks()
        no_transversal_order10_groups()
