#!/usr/bin/env python3
"""Enumerate the first four stages of Gunter & Scott §7.4's chain I, I+, I++, I+++
under two candidate readings of the pre-ordering on M(A), and report the sizes.

Why this exists: §7.4 states the element counts 1, 2, 5, 20 for that chain but
prints a relation, `(x,u) |- (y,v)  iff  exists z in u with z <= y`, that is not
reflexive.  Two repairs are on the table:

  gunter  the relation as printed, closed under reflexivity by identifying
          (x,u) with (x,v) whenever the up-sets of u and v agree.  This is
          Gunter, *Universal Profinite Domains* (Inf. & Comp. 72, 1987), p. 23,
          "remarked to the author by Dana Scott": A+ is the pairs <X,u> with u
          UPWARD CLOSED and X a lower bound of u, ordered by <X,u> <= <Y,v> iff
          Y in u.

  smyth   base components compared in A, cover components compared in the Smyth
          (upper) pre-order:  (x,u) <= (y,v)  iff  x <= y and every z in v is
          above some z' in u.

The stage sizes discriminate them.  Run: python3 scripts/mpair-stages.py
"""

from itertools import chain, combinations


def subsets(xs):
    return chain.from_iterable(combinations(xs, k) for k in range(len(xs) + 1))


def stage(elems, leq, order):
    """One application of M to a finite poset given as (elements, leq), returned
    as a new finite poset quotiented by the pre-order's equivalence."""
    pairs = []
    for x in elems:
        for u in subsets([z for z in elems if leq(x, z)]):
            pairs.append((x, frozenset(u)))

    def up(u):
        return frozenset(y for y in elems if any(leq(z, y) for z in u))

    if order == "gunter":
        def le(m, n):
            return any(leq(z, n[0]) for z in m[1]) or (m[0] == n[0] and up(m[1]) == up(n[1]))
    elif order == "smyth":
        def le(m, n):
            return leq(m[0], n[0]) and all(any(leq(zp, z) for zp in m[1]) for z in n[1])
    else:
        raise ValueError(order)

    # quotient by the pre-order's equivalence
    reps = []
    for p in pairs:
        if not any(le(p, q) and le(q, p) for q in reps):
            reps.append(p)
    return reps, le


def run(order, steps=3):
    elems = ["*"]
    leq = lambda a, b: True
    sizes = [len(elems)]
    for _ in range(steps):
        elems, leq = stage(elems, leq, order)
        sizes.append(len(elems))
    return sizes


if __name__ == "__main__":
    print("paper's stated sizes for I, I+, I++, I+++ : [1, 2, 5, 20]")
    for order in ("gunter", "smyth"):
        print(f"{order:8s}: {run(order)}")
