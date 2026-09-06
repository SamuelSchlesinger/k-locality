#!/usr/bin/env sage -python
"""Sample cubic-margin fibers and interpolate one-hidden relations.

The integer kernel of the order-three Boolean feature matrix contains every
alternating four-face move.  Starting from unions of affine Hamming-code
cosets, these moves generate many nonnegative count vectors with the same
cubic visible profile.  For each count vector ``c`` this script evaluates

    product_x (1 + b_x)^c[x]

at random points of the quadratic toric model ``b`` and searches for linear
dependencies.  Candidates still require an exact, independently checked
profile identity before they can enter Lean.
"""

from argparse import ArgumentParser
from itertools import combinations, product
from random import Random

from sage.all import GF, matrix

from search_hamming_fiber_relations import hamming_cosets, quadratic_state_values


def four_face_moves():
    moves = []
    coordinates = range(7)
    for free in combinations(coordinates, 4):
        fixed_coordinates = [coordinate for coordinate in coordinates if coordinate not in free]
        for fixed_bits in product((0, 1), repeat=3):
            fixed_state = sum(bit << coordinate for bit, coordinate in zip(fixed_bits, fixed_coordinates))
            halves = [[], []]
            for free_bits in product((0, 1), repeat=4):
                state = fixed_state + sum(bit << coordinate for bit, coordinate in zip(free_bits, free))
                halves[sum(free_bits) % 2].append(state)
            moves.append((halves[0], halves[1]))
    return moves


def sample_fiber(random, target_count, samples, steps_per_sample):
    cosets = hamming_cosets()
    if target_count % 128 == 0:
        counts = [target_count // 128] * 128
    else:
        counts = [0] * 128
        for coset in random.sample(cosets, target_count // 16):
            for state in coset:
                counts[state] += 1
    moves = four_face_moves()
    seen = {tuple(counts)}
    output = [tuple(counts)]
    attempts = 0
    while len(output) < samples and attempts < samples * steps_per_sample * 100:
        attempts += 1
        left, right = random.choice(moves)
        if random.randrange(2):
            left, right = right, left
        if all(counts[state] for state in left):
            for state in left:
                counts[state] -= 1
            for state in right:
                counts[state] += 1
        if attempts % steps_per_sample == 0:
            candidate = tuple(counts)
            if candidate not in seen:
                seen.add(candidate)
                output.append(candidate)
    print(f"sampled={len(output)} attempts={attempts}", flush=True)
    return output


def main():
    parser = ArgumentParser()
    parser.add_argument("--degree", type=int, default=32, choices=(32, 48, 64, 128, 256))
    parser.add_argument("--samples", type=int, default=800)
    parser.add_argument("--rows", type=int, default=820)
    parser.add_argument("--steps", type=int, default=5)
    parser.add_argument("--prime", type=int, default=1_000_003)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    print(f"parameters={vars(args)}", flush=True)

    random = Random(args.seed)
    columns = sample_fiber(random, args.degree, args.samples, args.steps)
    field = GF(args.prime)
    evaluations = []
    for row in range(args.rows):
        state_values = quadratic_state_values(field, random)
        evaluations.append(
            [
                field.prod(state_values[state] ** count for state, count in enumerate(column) if count)
                for column in columns
            ]
        )
        if (row + 1) % 100 == 0:
            print(f"evaluated={row + 1}", flush=True)
    evaluation_matrix = matrix(field, evaluations)
    rank = evaluation_matrix.rank()
    print(
        f"degree={args.degree} rows={args.rows} columns={len(columns)} "
        f"rank={rank} nullity={len(columns) - rank}",
        flush=True,
    )
    if rank == len(columns):
        return
    kernel = evaluation_matrix.right_kernel_matrix()
    witness = kernel.row(0)
    support = [(index, int(value)) for index, value in enumerate(witness) if value]
    print(f"candidate support={len(support)}")
    print(support)
    for index, _ in support:
        print(index, columns[index])


if __name__ == "__main__":
    main()
