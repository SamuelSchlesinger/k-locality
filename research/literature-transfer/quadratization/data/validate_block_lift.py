#!/usr/bin/env python3
"""Exhaustively validate the balanced-block lift on small Boolean cubes.

No third-party dependencies are required.  The script checks:
1. Rosenberg's quadratic penalty is nonnegative and vanishes iff z = u*v.
2. Recursive within-block features have a unique zero-penalty assignment.
3. Every visible monomial factors into at most k block-feature factors.
"""

from itertools import combinations, product


def rosenberg(u: int, v: int, z: int) -> int:
    return u * v - 2 * u * z - 2 * v * z + 3 * z


def balanced_blocks(n: int, k: int) -> list[tuple[int, ...]]:
    q, r = divmod(n, k)
    blocks = []
    start = 0
    for j in range(k):
        size = q + (j < r)
        blocks.append(tuple(range(start, start + size)))
        start += size
    return blocks


def feature_sets(blocks: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    return [
        a
        for block in blocks
        for size in range(2, len(block) + 1)
        for a in combinations(block, size)
    ]


def canonical_lift(x: tuple[int, ...], features: list[tuple[int, ...]]) -> dict:
    return {a: int(all(x[i] for i in a)) for a in features}


def factor_value(
    x: tuple[int, ...],
    h: dict[tuple[int, ...], int],
    subset: tuple[int, ...],
    blocks: list[tuple[int, ...]],
) -> int:
    value = 1
    chosen = set(subset)
    for block in blocks:
        part = tuple(i for i in block if i in chosen)
        if len(part) == 1:
            value *= x[part[0]]
        elif len(part) >= 2:
            value *= h[part]
    return value


def graph_penalty(
    x: tuple[int, ...], h: dict[tuple[int, ...], int], features
) -> int:
    total = 0
    for a in features:
        head, tail = a[0], a[1:]
        u = x[head]
        v = x[tail[0]] if len(tail) == 1 else h[tail]
        total += rosenberg(u, v, h[a])
    return total


def main() -> None:
    for u, v, z in product((0, 1), repeat=3):
        penalty = rosenberg(u, v, z)
        assert penalty >= 0
        assert (penalty == 0) == (z == u * v)

    checked = 0
    for n in range(1, 9):
        for k in range(2, min(n, 5) + 1):
            blocks = balanced_blocks(n, k)
            features = feature_sets(blocks)
            expected = sum(2 ** len(v) - len(v) - 1 for v in blocks)
            assert len(features) == expected

            for x in product((0, 1), repeat=n):
                h = canonical_lift(x, features)
                assert graph_penalty(x, h, features) == 0
                for mask in range(1 << n):
                    subset = tuple(i for i in range(n) if mask >> i & 1)
                    direct = int(all(x[i] for i in subset))
                    assert factor_value(x, h, subset, blocks) == direct

                # Exhaustively check graph uniqueness when the hidden cube is small.
                if len(features) <= 10:
                    zero_assignments = 0
                    for bits in product((0, 1), repeat=len(features)):
                        trial = dict(zip(features, bits))
                        if graph_penalty(x, trial, features) == 0:
                            zero_assignments += 1
                            assert trial == h
                    assert zero_assignments == 1
                checked += 1

    print(f"validated {checked} visible instances; all checks passed")


if __name__ == "__main__":
    main()
