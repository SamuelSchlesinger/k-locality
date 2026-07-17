#!/usr/bin/env python3
"""Finite checks for the Eisenstein radial construction.

The script checks:

* r=2^floor(log2(n+1)) and the all-n block padding;
* the exact k=2 feature-dimension threshold;
* Eisenstein's coefficient conditions for X^r-2;
* 1 <= 2^(|x|/r) < 4 and probability ratio < e^3; and
* uniqueness of the k-digit base-L lookup encoding.

Only the Python standard library is required.  Algebraic independence and
localization lower bounds are proved in the note, not by this script.
"""

from __future__ import annotations

import argparse
import itertools
import math


def dyadic_floor(value: int) -> int:
    """Largest power of two at most value, for value>=1."""

    return 1 << (value.bit_length() - 1)


def d2(total_bits: int) -> int:
    return 1 + total_bits * (total_bits + 1) // 2


def threshold_search(m: int) -> int:
    ell = 0
    while d2(m + ell) < 2**m:
        ell += 1
    return ell


def threshold_formula(m: int) -> int:
    discriminant = 2 ** (m + 3) - 7
    s = max(0, (math.isqrt(discriminant) - 1) // 2)
    while d2(s) < 2**m:
        s += 1
    while s > 0 and d2(s - 1) >= 2**m:
        s -= 1
    return max(0, s - m)


def encoded_vector(bits: tuple[int, ...], n: int) -> tuple[int, ...]:
    encoded: list[int] = []
    for index, bit in enumerate(bits):
        encoded.extend([bit] * (2**index))
    encoded.extend([0] * (n - len(encoded)))
    return tuple(encoded)


def base_digits(value: int, base: int, width: int) -> tuple[int, ...]:
    digits: list[int] = []
    remaining = value
    for _ in range(width):
        digits.append(remaining % base)
        remaining //= base
    assert remaining == 0
    return tuple(digits)


def validate_lookup(max_n: int, max_k: int) -> None:
    for n in range(1, max_n + 1):
        for k in range(2, max_k + 1):
            base = 1
            while base**k < n + 1:
                base += 1
            seen: set[tuple[int, ...]] = set()
            for value in range(n + 1):
                digits = base_digits(value, base, k)
                assert digits not in seen
                seen.add(digits)
                assert all(0 <= digit < base for digit in digits)
                assert sum(base**j * digit for j, digit in enumerate(digits)) == value


def validate(max_n: int, exhaustive_m: int) -> None:
    print("n   m   r   q_(m,2)   max_energy      point_ratio")
    for n in range(1, max_n + 1):
        r = dyadic_floor(n + 1)
        m = r.bit_length() - 1
        assert r <= n + 1 < 2 * r

        # X^r-2: leading coefficient is odd; all other coefficients are even;
        # the constant coefficient is not divisible by four.
        leading = 1
        constant = -2
        middle = [0] * (r - 1)
        assert leading % 2 != 0
        assert constant % 2 == 0 and constant % 4 != 0
        assert all(coefficient % 2 == 0 for coefficient in middle)

        q_search = threshold_search(m)
        q_formula = threshold_formula(m)
        assert q_search == q_formula

        max_energy = 2 ** (n / r)
        assert 1.0 <= max_energy < 4.0
        point_ratio = math.exp(max_energy - 1.0)
        assert point_ratio < math.e**3

        if m <= exhaustive_m:
            for bits in itertools.product((0, 1), repeat=m):
                x = encoded_vector(bits, n)
                expected = sum(2**j * bit for j, bit in enumerate(bits))
                assert sum(x) == expected
                assert all(bit == 0 for bit in x[r - 1 :])

        print(
            f"{n:2d} {m:3d} {r:3d} {q_search:9d} "
            f"{max_energy:14.10f} {point_ratio:14.10f}"
        )

    validate_lookup(max_n=max_n, max_k=5)
    print(f"lookup encoding: checked n<={max_n} and 2<=k<=5")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=64)
    parser.add_argument(
        "--exhaustive-m",
        type=int,
        default=10,
        help="exhaust block embeddings only while m is at most this value",
    )
    args = parser.parse_args()
    if args.max_n < 1:
        parser.error("--max-n must be positive")
    validate(args.max_n, args.exhaustive_m)


if __name__ == "__main__":
    main()
