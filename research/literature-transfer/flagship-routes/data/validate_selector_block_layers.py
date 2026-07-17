#!/usr/bin/env python3
"""Validate the finite combinatorics in selector-explicit.md.

The script checks three claims for small instances of the block-layer family:

1. every pair of distinct target weight tuples has the primitive-line margin
   used in Lemma 3, and the first primitive intermediate point leaves T^m;
2. the explicit quadratic energy has exactly the claimed projected zero set
   and a unique hidden witness for every target tuple;
3. the displayed degree-2q nonnegative polynomial vanishes exactly on T.

No third-party dependencies are required.  This is a finite sanity check, not
a replacement for the symbolic proofs in the research note.
"""

from __future__ import annotations

from itertools import product
from math import gcd


def target_set(q: int) -> tuple[int, ...]:
    return tuple(range(q, 3 * q, 2))


def primitive_direction(left: tuple[int, ...], right: tuple[int, ...]):
    delta = tuple(b - a for a, b in zip(left, right, strict=True))
    scale = 0
    for value in delta:
        scale = gcd(scale, abs(value))
    assert scale >= 2
    direction = tuple(value // scale for value in delta)
    assert gcd(*(abs(value) for value in direction)) == 1
    return scale, direction


def check_line_margins(q: int, blocks: int) -> int:
    bound = 4 * q
    targets = tuple(product(target_set(q), repeat=blocks))
    checked = 0
    for index, left in enumerate(targets):
        for right in targets[index + 1 :]:
            scale, direction = primitive_direction(left, right)
            before = tuple(a - v for a, v in zip(left, direction, strict=True))
            after = tuple(b + v for b, v in zip(right, direction, strict=True))
            middle = tuple(a + v for a, v in zip(left, direction, strict=True))
            assert scale >= 2
            assert all(0 <= value <= bound for value in before)
            assert all(0 <= value <= bound for value in after)
            assert any(value % 2 for value in middle)
            assert middle not in targets
            checked += 1
    return checked


def decode_target(q: int, code: tuple[int, ...]) -> tuple[int, ...]:
    bits = q.bit_length() - 1
    assert len(code) % bits == 0
    decoded = []
    for start in range(0, len(code), bits):
        integer = sum(code[start + j] << j for j in range(bits))
        decoded.append(q + 2 * integer)
    return tuple(decoded)


def energy(weights: tuple[int, ...], targets: tuple[int, ...]) -> int:
    return sum((weight - target) ** 2 for weight, target in zip(weights, targets, strict=True))


def check_energy(q: int, blocks: int) -> tuple[int, int]:
    bits = q.bit_length() - 1
    codes = tuple(product((0, 1), repeat=bits * blocks))
    decoded = tuple(decode_target(q, code) for code in codes)
    expected = set(product(target_set(q), repeat=blocks))
    assert set(decoded) == expected
    assert len(set(decoded)) == len(decoded)

    projected_zeros: set[tuple[int, ...]] = set()
    zero_pairs = 0
    for weights in product(range(4 * q + 1), repeat=blocks):
        witnesses = [target for target in decoded if energy(weights, target) == 0]
        if witnesses:
            projected_zeros.add(weights)
            assert len(witnesses) == 1
            zero_pairs += 1
    assert projected_zeros == expected
    assert zero_pairs == q**blocks
    return len(projected_zeros), len(codes)


def check_sign_certificate(q: int) -> None:
    targets = target_set(q)
    for weight in range(4 * q + 1):
        value = 1
        for target in targets:
            value *= (weight - target) ** 2
        assert (value == 0) == (weight in targets)
        assert value >= 0


def main() -> None:
    cases = ((2, 1), (2, 2), (2, 3), (4, 1), (4, 2), (8, 1), (8, 2))
    for q, blocks in cases:
        assert q > 1 and q & (q - 1) == 0
        assert len(target_set(q)) == q
        pairs = check_line_margins(q, blocks)
        zeros, witnesses = check_energy(q, blocks)
        check_sign_certificate(q)
        print(
            f"q={q:2d}, blocks={blocks}: {pairs} target pairs checked; "
            f"{zeros} projected zeros; {witnesses} unique witness codes"
        )
    print("all selector block-layer checks passed")


if __name__ == "__main__":
    main()
