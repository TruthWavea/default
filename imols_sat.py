"""SAT test: do k incomplete MOLS of order n with a common h x h hole exist?

k incomplete MOLS of order n with a common hole of size h are the same as an
ITD(k+2, n; h); for k = 3 they are the same as a 4-IRGDD of type (n,h)^4
(Remark 5.3 of 4rgdd_10_4.tex).  Hole rows = hole columns = hole symbols = {0..h-1}.
Any solution found is checked independently before it is reported.

usage: python3 imols_sat.py n h k [timeout_seconds]      (needs: pip install python-sat)
e.g.   python3 imols_sat.py 10 4 3    -> UNSAT (no hole of size 4 in three MOLS(10))
"""
import sys
import threading
import time
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153


def build(n, h, k):
    H = set(range(h))
    cells = [(i, j) for i in range(n) for j in range(n) if not (i in H and j in H)]
    allowed = {(i, j): [s for s in range(n) if not ((i in H or j in H) and s in H)] for (i, j) in cells}
    pool = IDPool()
    x = {(q, i, j, s): pool.id(('x', q, i, j, s))
         for q in range(k) for (i, j) in cells for s in allowed[i, j]}
    clauses = []

    def exactly_one(lits):
        if not lits:
            clauses.append([])
        else:
            clauses.extend(CardEnc.equals(lits=lits, bound=1, vpool=pool,
                                          encoding=EncType.seqcounter).clauses)

    for q in range(k):
        for (i, j) in cells:
            exactly_one([x[q, i, j, s] for s in allowed[i, j]])
        for i in range(n):
            for s in range(n):
                if i in H and s in H:
                    continue          # a hole symbol never occurs in a hole row/column
                exactly_one([x[q, i, j, s] for j in range(n) if (q, i, j, s) in x])
                exactly_one([x[q, j, i, s] for j in range(n) if (q, j, i, s) in x])
    for p, q in combinations(range(k), 2):
        for s in range(n):
            for t in range(n):
                ys = []
                for (i, j) in cells:
                    if (p, i, j, s) not in x or (q, i, j, t) not in x:
                        continue
                    if s in H and t in H:   # pairs of hole symbols must not occur
                        clauses.append([-x[p, i, j, s], -x[q, i, j, t]])
                        continue
                    y = pool.id(('y', p, q, i, j, s, t))
                    clauses += [[-y, x[p, i, j, s]], [-y, x[q, i, j, t]],
                                [y, -x[p, i, j, s], -x[q, i, j, t]]]
                    ys.append(y)
                if not (s in H and t in H):
                    exactly_one(ys)       # every other pair occurs exactly once
    # symmetry breaking: permuting hole columns, non-hole columns, and the hole and
    # non-hole symbols of square 0 separately, row h of square 0 can be normalised
    if n >= 2 * h:
        for j in range(n):
            sym = h + j if j < h else (j - h if j < 2 * h else j)
            clauses.append([x[0, h, j, sym]])
    return cells, allowed, x, clauses, pool


def check(n, h, squares):
    H = set(range(h))
    for L in squares:
        for i in range(n):
            need = set(range(n)) - (H if i in H else set())
            row = [L[i][j] for j in range(n) if L[i][j] is not None]
            col = [L[j][i] for j in range(n) if L[j][i] is not None]
            assert sorted(row) == sorted(need) and sorted(col) == sorted(need)
            for j in range(n):
                assert (L[i][j] is None) == (i in H and j in H)
    for A, B in combinations(squares, 2):
        pairs = [(A[i][j], B[i][j]) for i in range(n) for j in range(n) if A[i][j] is not None]
        assert len(set(pairs)) == len(pairs) == n * n - h * h
        assert not any(a in H and b in H for a, b in pairs)


if __name__ == '__main__':
    n, h, k = (int(a) for a in sys.argv[1:4])
    tlimit = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    cells, allowed, x, clauses, pool = build(n, h, k)
    t0 = time.time()
    with Cadical153(bootstrap_with=clauses) as solver:
        timer = threading.Timer(tlimit, solver.interrupt)
        timer.start()
        res = solver.solve_limited(expect_interrupt=True)
        timer.cancel()
        verdict = {True: 'SAT', False: 'UNSAT', None: 'TIMEOUT'}[res]
        print(f"n={n} h={h} k={k}: {verdict} in {time.time() - t0:.1f}s "
              f"(vars={pool.top}, clauses={len(clauses)})")
        if res:
            model = {l for l in solver.get_model() if l > 0}
            squares = [[[next((s for s in allowed[i, j] if x[q, i, j, s] in model), None)
                         if (i, j) in allowed else None for j in range(n)] for i in range(n)]
                       for q in range(k)]
            check(n, h, squares)
            print("solution checked: valid incomplete MOLS")
            for L in squares:
                print('\n'.join(' '.join('.' if v is None else str(v) for v in r) for r in L) + '\n')
