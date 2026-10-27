"""Check a candidate 5-GDD of type 10^27 given by base blocks over Z_270.

Groups are the residue classes modulo 27; the design is developed by
x -> x + 2j (mod 270), 0 <= j < 135.  Base blocks are read from a text file
containing brace-delimited 5-sets such as {0, 3, 17, 101, 222}.

usage: python3 verify_10_27.py blocks.txt
"""
import itertools
import re
import sys

V, U, G = 270, 27, 10


def load(path):
    text = open(path).read()
    return [tuple(int(x) for x in m.split(',')) for m in re.findall(r'\{([0-9,\s]+)\}', text)]


def check(base):
    if len(base) != 26:
        raise ValueError(f"expected 26 base blocks, got {len(base)}")
    blocks = set()
    for B in base:
        if len(set(x % V for x in B)) != 5:
            raise ValueError(f"block {B} does not have 5 distinct points")
        for j in range(135):
            blocks.add(frozenset((x + 2 * j) % V for x in B))
    covered = set()
    for B in blocks:
        for x, y in itertools.combinations(sorted(B), 2):
            if x % U == y % U:
                raise ValueError(f"pair {x},{y} lies inside a group")
            if (x, y) in covered:
                raise ValueError(f"pair {x},{y} is covered twice")
            covered.add((x, y))
    needed = V * (V - 1) // 2 - U * G * (G - 1) // 2
    if len(covered) != needed:
        raise ValueError(f"{needed - len(covered)} cross-group pairs are not covered")
    return len(blocks), len(covered)


if __name__ == '__main__':
    nblocks, npairs = check(load(sys.argv[1]))
    print(f"OK: {nblocks} blocks, {npairs} cross-group pairs each covered exactly once")
