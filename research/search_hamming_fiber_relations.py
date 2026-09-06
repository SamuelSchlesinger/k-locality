#!/usr/bin/env sage -python
"""Interpolate relations in the degree-32 Hamming-code marginal fiber.

The 240 affine cosets of binary [7,4,3] Hamming codes have identical visible
order-three profiles.  For one hidden bit, the expanded monomial attached to a
coset C is

    P_C(b) = product_(x in C) (1 + b_x),

where ``b_x`` ranges over the quadratic Boolean toric model.  A linear
relation among products ``P_C P_D`` is consequently a homogeneous order-three
marginal identity of visible degree 32.

This script uses finite-field evaluations to discover candidates.  A reported
kernel vector is not a proof; it must be expanded or otherwise certified in
Lean before use.
"""

from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement, permutations
from random import Random

from sage.all import GF, matrix


def hamming_cosets():
    candidates = set()
    for columns in permutations(range(1, 8)):
        fibers = [[] for _ in range(8)]
        for state in range(128):
            syndrome = 0
            for coordinate, column in enumerate(columns):
                if (state >> coordinate) & 1:
                    syndrome ^= column
            fibers[syndrome].append(state)
        candidates.update(tuple(fiber) for fiber in fibers)
    return sorted(candidates)


def quadratic_state_values(field, random):
    scopes = [
        scope
        for degree in range(3)
        for scope in combinations(range(7), degree)
    ]
    parameters = [field(random.randrange(1, field.order())) for _ in scopes]
    values = []
    for state in range(128):
        monomial = field.one()
        for parameter, scope in zip(parameters, scopes):
            if all((state >> coordinate) & 1 for coordinate in scope):
                monomial *= parameter
        values.append(field.one() + monomial)
    return values


def main():
    parser = ArgumentParser()
    parser.add_argument("--columns", type=int, default=600)
    parser.add_argument("--rows", type=int, default=620)
    parser.add_argument("--prime", type=int, default=1_000_003)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--keep-duplicate-unions",
        action="store_true",
        help="keep pair monomials representing an already-seen visible multiset",
    )
    args = parser.parse_args()
    print(f"parameters={vars(args)}", flush=True)

    field = GF(args.prime)
    random = Random(args.seed)
    cosets = hamming_cosets()
    all_pairs = list(combinations_with_replacement(range(len(cosets)), 2))
    if not args.keep_duplicate_unions:
        representatives = {}
        for left, right in all_pairs:
            visible_multiset = tuple(sorted(cosets[left] + cosets[right]))
            representatives.setdefault(visible_multiset, (left, right))
        all_pairs = list(representatives.values())
    random.shuffle(all_pairs)
    selected_pairs = all_pairs[: args.columns]
    print(
        f"cosets={len(cosets)} pair candidates={len(all_pairs)} "
        f"selected={len(selected_pairs)}",
        flush=True,
    )

    evaluations = []
    for row in range(args.rows):
        state_values = quadratic_state_values(field, random)
        coset_values = [
            field.prod(state_values[state] for state in coset) for coset in cosets
        ]
        evaluations.append(
            [coset_values[left] * coset_values[right] for left, right in selected_pairs]
        )
        if (row + 1) % 100 == 0:
            print(f"evaluated {row + 1} rows", flush=True)

    evaluation_matrix = matrix(field, evaluations)
    rank = evaluation_matrix.rank()
    print(
        f"rows={args.rows} columns={args.columns} rank={rank} "
        f"nullity={args.columns - rank}",
        flush=True,
    )
    if rank == args.columns:
        return
    kernel = evaluation_matrix.right_kernel_matrix()
    witness = kernel.row(0)
    support = [
        (selected_pairs[index], int(value))
        for index, value in enumerate(witness)
        if value
    ]
    print(f"candidate support={len(support)}")
    print(support)
    print(
        [
            (coefficient, cosets[left], cosets[right])
            for (left, right), coefficient in support
        ]
    )


if __name__ == "__main__":
    main()
