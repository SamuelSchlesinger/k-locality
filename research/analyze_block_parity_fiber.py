#!/usr/bin/env sage -python
"""Analyze a structured cubic-moment fiber and its Boolean-test transform.

Let ``A = {0,1}^q`` and ``Z = {0,1}^4``.  For every Boolean function
``s : A -> {0,1}``, form the visible subset

    C_s = {(0,a,z) : parity(z) = s(a)}.

The leading zero is a marker bit which keeps the sets away from the filler
state used by ``UniformExplicitCubicLowerBound``.  The even and odd halves of
a four-cube have the same moments through degree three, so all ``C_s`` lie in
one visible cubic-moment fiber.

For tests of the same form, the Boolean-tilt kernel is

    K(t,s) = 2^|C_t intersect C_s| = 256^(# positions where t = s).

It is the tensor power of ``[[256,1],[1,256]]`` and is diagonal in the Walsh
basis, with eigenvalue ``257^(N-j) * 255^j`` at Fourier level ``j`` where
``N = 2^q``.

The optional finite-field experiment evaluates the full order-three toric
marginal parametrization with ``ell`` hidden bits.  Its rank is discovery
data, not proof; the exact moment and kernel checks use integer arithmetic.
"""

from argparse import ArgumentParser
from itertools import combinations
from random import Random

from sage.all import GF, ZZ, matrix


def bit(state: int, coordinate: int) -> int:
    return (state >> coordinate) & 1


def parity(state: int) -> int:
    return state.bit_count() & 1


def scopes(width: int, maximum_degree: int):
    return [
        scope
        for degree in range(maximum_degree + 1)
        for scope in combinations(range(width), degree)
    ]


def block_parity_candidate(prefix_bits: int, truth_table: int):
    """Return ``C_s`` as integer-encoded visible states.

    Coordinates ``0,...,q-1`` hold ``a``; the next four hold ``z``; the final
    marker coordinate is zero on every selected state.
    """

    output = []
    for prefix in range(1 << prefix_bits):
        selected_parity = bit(truth_table, prefix)
        for suffix in range(16):
            if parity(suffix) == selected_parity:
                output.append(prefix | (suffix << prefix_bits))
    return tuple(output)


def visible_moment_profile(prefix_bits: int, candidate):
    width = prefix_bits + 5
    return tuple(
        sum(all(bit(state, coordinate) for coordinate in scope) for state in candidate)
        for scope in scopes(width, 3)
    )


def verify_visible_fiber(prefix_bits: int):
    block_count = 1 << prefix_bits
    profiles = {
        visible_moment_profile(
            prefix_bits, block_parity_candidate(prefix_bits, truth_table)
        )
        for truth_table in range(1 << block_count)
    }
    expected_size = 8 * block_count
    sizes = {
        len(block_parity_candidate(prefix_bits, truth_table))
        for truth_table in range(1 << block_count)
    }
    assert sizes == {expected_size}
    assert len(profiles) == 1
    return expected_size, next(iter(profiles))


def kernel_entry(prefix_bits: int, test: int, candidate: int) -> int:
    left = set(block_parity_candidate(prefix_bits, test))
    right = set(block_parity_candidate(prefix_bits, candidate))
    return 2 ** len(left & right)


def predicted_kernel_entry(prefix_bits: int, test: int, candidate: int) -> int:
    positions = 1 << prefix_bits
    disagreements = (test ^ candidate).bit_count()
    return 256 ** (positions - disagreements)


def walsh_sign(subset: int, point: int) -> int:
    return -1 if ((subset & point).bit_count() & 1) else 1


def verify_kernel_and_spectrum(prefix_bits: int):
    positions = 1 << prefix_bits
    function_count = 1 << positions
    kernel = matrix(
        ZZ,
        function_count,
        function_count,
        lambda test, candidate: kernel_entry(prefix_bits, test, candidate),
    )
    predicted = matrix(
        ZZ,
        function_count,
        function_count,
        lambda test, candidate: predicted_kernel_entry(
            prefix_bits, test, candidate
        ),
    )
    assert kernel == predicted

    walsh = matrix(
        ZZ,
        function_count,
        function_count,
        lambda subset, point: walsh_sign(subset, point),
    )
    diagonalized = walsh * kernel * walsh.transpose()
    assert all(
        diagonalized[row, column] == 0
        for row in range(function_count)
        for column in range(function_count)
        if row != column
    )
    eigenvalues = []
    for subset in range(function_count):
        level = subset.bit_count()
        expected = function_count * 257 ** (positions - level) * 255**level
        assert diagonalized[subset, subset] == expected
        eigenvalues.append(expected // function_count)
    return kernel.rank(), eigenvalues


def joint_marginals(field, random, visible_bits: int, hidden_bits: int):
    total_bits = visible_bits + hidden_bits
    nonempty_scopes = scopes(total_bits, 3)[1:]
    parameters = [field(random.randrange(1, field.order())) for _ in nonempty_scopes]
    joint_weights = []
    for joint in range(1 << total_bits):
        value = field.one()
        for parameter, scope in zip(parameters, nonempty_scopes):
            if all(bit(joint, coordinate) for coordinate in scope):
                value *= parameter
        joint_weights.append(value)

    visible_mask = (1 << visible_bits) - 1
    marginals = []
    for visible in range(1 << visible_bits):
        marginals.append(
            field.sum(
                joint_weights[visible | (hidden << visible_bits)]
                for hidden in range(1 << hidden_bits)
            )
        )
    assert len(marginals) == visible_mask + 1
    return marginals


def evaluated_profile_rank(
    prefix_bits: int, hidden_bits: int, samples: int, prime: int, seed: int
):
    positions = 1 << prefix_bits
    function_count = 1 << positions
    visible_bits = prefix_bits + 5
    candidates = [
        block_parity_candidate(prefix_bits, truth_table)
        for truth_table in range(function_count)
    ]
    field = GF(prime)
    random = Random(seed)
    evaluations = []
    for sample in range(samples):
        marginals = joint_marginals(field, random, visible_bits, hidden_bits)
        evaluations.append(
            [field.prod(marginals[state] for state in candidate) for candidate in candidates]
        )
        if (sample + 1) % 100 == 0:
            print(f"evaluated={sample + 1}", flush=True)
    evaluation_matrix = matrix(field, evaluations)
    return evaluation_matrix.rank(), function_count


def main():
    parser = ArgumentParser()
    parser.add_argument("--prefix-bits", type=int, default=2)
    parser.add_argument("--hidden-bits", type=int, default=1)
    parser.add_argument("--samples", type=int, default=40)
    parser.add_argument("--prime", type=int, default=1_000_003)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--skip-rank", action="store_true", help="skip randomized toric rank evaluation"
    )
    args = parser.parse_args()

    if args.prefix_bits > 3:
        parser.error("exact kernel construction is intentionally capped at q <= 3")

    candidate_size, profile = verify_visible_fiber(args.prefix_bits)
    kernel_rank, eigenvalues = verify_kernel_and_spectrum(args.prefix_bits)
    positions = 1 << args.prefix_bits
    function_count = 1 << positions
    spectrum_by_level = {
        level: 257 ** (positions - level) * 255**level
        for level in range(positions + 1)
    }
    print(
        f"q={args.prefix_bits} blocks={positions} functions={function_count} "
        f"candidate_size={candidate_size} cubic_profiles=1 kernel_rank={kernel_rank}"
    )
    print(f"kernel_spectrum_by_level={spectrum_by_level}")
    assert len(eigenvalues) == function_count

    if not args.skip_rank:
        rank, columns = evaluated_profile_rank(
            args.prefix_bits,
            args.hidden_bits,
            args.samples,
            args.prime,
            args.seed,
        )
        print(
            f"randomized_M_rank hidden_bits={args.hidden_bits} "
            f"rows={args.samples} columns={columns} rank={rank}"
        )


if __name__ == "__main__":
    main()
