#!/usr/bin/env sage -python
"""Search homogeneous marginal identities for cubic models with one hidden bit.

For a visible monomial ``prod_i p[x_i]``, expanding

    p[x] = q[x, 0] + q[x, 1]

produces one joint monomial for each choice of hidden labels.  Two joint
monomials coincide under the order-three toric parametrization precisely when
their total order-three feature profiles agree.  This script builds the exact
profile-incidence matrix over a finite field; its right kernel is the space of
homogeneous visible identities in the requested candidate set.

The default candidate set is every degree-two monomial on the seven-bit
visible cube.  It is deliberately a search/validation tool, not part of the
Lean trust boundary.
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations
from random import Random

from sage.all import GF, matrix


def feature_scopes(n: int, maximum_degree: int):
    return [
        scope
        for degree in range(maximum_degree + 1)
        for scope in combinations(range(n), degree)
    ]


def feature_vector(state: int, scopes):
    return tuple(
        int(all((state >> coordinate) & 1 for coordinate in scope))
        for scope in scopes
    )


def expansion_signature(states, visible_features, hidden_features):
    visible_profile = tuple(
        sum(feature[index] for feature in visible_features)
        for index in range(len(visible_features[0]))
    )
    expanded = Counter()
    degree = len(states)
    for hidden_mask in range(1 << degree):
        hidden_profile = tuple(
            sum(
                hidden_features[state][index]
                for occurrence, state in enumerate(states)
                if (hidden_mask >> occurrence) & 1
            )
            for index in range(len(hidden_features[0]))
        )
        expanded[(visible_profile, hidden_profile)] += 1
    return expanded


def hamming_cosets():
    """All 240 coordinate-permuted cosets of the binary [7,4,3] code."""
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


def evaluated_kernel(monomials, hidden_features, prime: int, samples: int, seed: int):
    """Probabilistically find a relation among subset-sum polynomials."""
    field = GF(prime)
    random = Random(seed)
    evaluations = []
    for _ in range(samples):
        point = [field(random.randrange(1, prime)) for _ in hidden_features[0]]
        state_values = []
        for feature in hidden_features:
            value = field.one()
            for coordinate, exponent in enumerate(feature):
                if exponent:
                    value *= point[coordinate]
            state_values.append(field.one() + value)
        evaluations.append(
            [
                field.prod(state_values[state] for state in monomial)
                for monomial in monomials
            ]
        )
    evaluation_matrix = matrix(field, evaluations)
    kernel = evaluation_matrix.right_kernel_matrix()
    print(
        f"evaluated rows={evaluation_matrix.nrows()} "
        f"columns={evaluation_matrix.ncols()} "
        f"rank={evaluation_matrix.rank()} nullity={kernel.nrows()}"
    )
    return kernel


def main():
    parser = ArgumentParser()
    parser.add_argument("--visible-bits", type=int, default=7)
    parser.add_argument("--degree", type=int, default=2)
    parser.add_argument("--prime", type=int, default=1_000_003)
    parser.add_argument(
        "--family", choices=("all", "hamming"), default="all"
    )
    parser.add_argument("--samples", type=int, default=260)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    print(f"parameters={vars(args)}", flush=True)

    states = range(1 << args.visible_bits)
    visible_scopes = feature_scopes(args.visible_bits, 3)
    hidden_scopes = feature_scopes(args.visible_bits, 2)
    visible_feature = {
        state: feature_vector(state, visible_scopes) for state in states
    }
    hidden_feature = {
        state: feature_vector(state, hidden_scopes) for state in states
    }

    if args.family == "hamming":
        if args.visible_bits != 7:
            parser.error("the Hamming family requires seven visible bits")
        monomials = hamming_cosets()
        print(f"Hamming-code cosets={len(monomials)}")
        kernel = evaluated_kernel(
            monomials,
            [hidden_feature[state] for state in states],
            args.prime,
            args.samples,
            args.seed,
        )
        if not kernel.nrows():
            return
        candidate = kernel.row(0)
        support = [
            (monomials[index], int(value))
            for index, value in enumerate(candidate)
            if value
        ]
        print(f"candidate support={len(support)}")
        print(support)
        return

    monomials = list(combinations_with_replacement(states, args.degree))
    row_ids = {}
    column_signatures = []
    for monomial in monomials:
        signature = expansion_signature(
            monomial,
            [visible_feature[state] for state in monomial],
            hidden_feature,
        )
        column_signatures.append(signature)
        for profile in signature:
            row_ids.setdefault(profile, len(row_ids))

    entries = {}
    field = GF(args.prime)
    for column, signature in enumerate(column_signatures):
        for profile, multiplicity in signature.items():
            entries[(row_ids[profile], column)] = field(multiplicity)

    incidence = matrix(
        field, len(row_ids), len(monomials), entries, sparse=True
    )
    kernel = incidence.right_kernel_matrix()
    print(
        f"n={args.visible_bits} degree={args.degree} "
        f"rows={incidence.nrows()} columns={incidence.ncols()} "
        f"rank={incidence.rank()} nullity={kernel.nrows()}"
    )
    if kernel.nrows():
        witness = kernel.row(0)
        support = [(monomials[index], int(value)) for index, value in enumerate(witness) if value]
        print(f"first kernel vector support={len(support)}")
        print(support)


if __name__ == "__main__":
    main()
