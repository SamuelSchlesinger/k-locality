#!/usr/bin/env python3
"""Search for a constant-weight encoding of the checked quadratic trade.

If the 18 visible states used by ``oneHiddenSexticCertificate`` are encoded
as distinct subsets of an ``m``-set of size at most two, all visible cubic
monomials vanish.  This solver asks whether the remaining visible and
hidden-mixed order-three profiles can be matched using the already checked
quadratic profile matching.

The output is only discovery data.  Any successful encoding must subsequently
be checked by ``MarginalTradeCertificate.profileBalance`` in Lean.
"""

from collections import Counter, defaultdict
from itertools import combinations, permutations, product

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


POSITIVE = [
    [0, 6, 9, 19, 21, 28],
    [1, 2, 12, 20, 23, 25],
    [3, 4, 8, 17, 22, 29],
]
NEGATIVE = [
    [0, 3, 12, 21, 22, 25],
    [1, 6, 8, 19, 20, 29],
    [2, 4, 9, 17, 23, 28],
]
STATES = sorted(set(sum(POSITIVE, []) + sum(NEGATIVE, [])))


def quadratic_joint_profile(term, hidden):
    scopes = [()] + [(i,) for i in range(5)] + list(combinations(range(5), 2))
    visible = [
        sum(all((state >> coordinate) & 1 for coordinate in scope) for state in term)
        for scope in scopes
    ]
    hidden_features = [sum(hidden)] + [
        sum(hidden[index] and ((state >> coordinate) & 1) for index, state in enumerate(term))
        for coordinate in range(5)
    ]
    return tuple(visible + hidden_features)


def grouped_entries(side):
    groups = defaultdict(list)
    for term_index, term in enumerate(side):
        for hidden in product((False, True), repeat=6):
            groups[quadratic_joint_profile(term, hidden)].append((term_index, hidden))
    return groups


def target_weight(state):
    first = all((state >> coordinate) & 1 for coordinate in (0, 1, 2))
    second = all((state >> coordinate) & 1 for coordinate in (2, 3, 4))
    return (2 if first else 1) * (2 if second else 1)


def solve(width, injective=False, maximum_weight=None):
    positive_groups = grouped_entries(POSITIVE)
    negative_groups = grouped_entries(NEGATIVE)
    assert Counter(map(len, positive_groups.values())) == Counter(
        map(len, negative_groups.values())
    )
    assert positive_groups.keys() == negative_groups.keys()

    bits = {
        (state, coordinate): Bool(f"b_{state}_{coordinate}")
        for state in STATES
        for coordinate in range(width)
    }
    solver = Solver()

    if maximum_weight is not None:
        for state in STATES:
            solver.add(
                Sum(
                    [If(bits[state, coordinate], 1, 0) for coordinate in range(width)]
                )
                <= maximum_weight
            )

    # Bit complementation lets us normalize one codeword to zero.
    for coordinate in range(width):
        solver.add(bits[STATES[0], coordinate] == False)

    # It is enough to keep cells with different target weights distinct.
    # Pass ``injective=True`` to demand a literal encoding of all 18 cells.
    for left, right in combinations(STATES, 2):
        if injective or target_weight(left) != target_weight(right):
            solver.add(Or([bits[left, coordinate] != bits[right, coordinate] for coordinate in range(width)]))

    hidden_scopes = [(coordinate,) for coordinate in range(width)] + list(
        combinations(range(width), 2)
    )
    visible_scopes = hidden_scopes + list(combinations(range(width), 3))

    def feature(state, scope):
        return And([bits[state, coordinate] for coordinate in scope])

    def equal_refinement(positive_entry, negative_entry):
        positive_term, positive_hidden = positive_entry
        negative_term, negative_hidden = negative_entry
        constraints = []
        for scope in visible_scopes:
            constraints.append(
                Sum(
                    [If(feature(state, scope), 1, 0) for state in POSITIVE[positive_term]]
                )
                == Sum(
                    [If(feature(state, scope), 1, 0) for state in NEGATIVE[negative_term]]
                )
            )
        for scope in hidden_scopes:
            constraints.append(
                Sum(
                    [
                        If(And(positive_hidden[index], feature(state, scope)), 1, 0)
                        for index, state in enumerate(POSITIVE[positive_term])
                    ]
                )
                == Sum(
                    [
                        If(And(negative_hidden[index], feature(state, scope)), 1, 0)
                        for index, state in enumerate(NEGATIVE[negative_term])
                    ]
                )
            )
        return And(constraints)

    for profile in positive_groups:
        positive_entries = positive_groups[profile]
        negative_entries = negative_groups[profile]
        if len(positive_entries) == 1:
            solver.add(equal_refinement(positive_entries[0], negative_entries[0]))
        else:
            solver.add(
                Or(
                    [
                        And(
                            [
                                equal_refinement(positive_entries[index], negative_entries[target])
                                for index, target in enumerate(permutation)
                            ]
                        )
                        for permutation in permutations(range(len(negative_entries)))
                    ]
                )
            )

    result = solver.check()
    print(f"width={width}: {result}")
    if result != sat:
        return None
    model = solver.model()
    encoding = {
        state: sum(
            (1 << coordinate) * int(is_true(model.eval(bits[state, coordinate], model_completion=True)))
            for coordinate in range(width)
        )
        for state in STATES
    }
    print(encoding)
    return encoding


if __name__ == "__main__":
    for candidate_width in range(5, 9):
        if solve(candidate_width, injective=True, maximum_weight=None) is not None:
            break
