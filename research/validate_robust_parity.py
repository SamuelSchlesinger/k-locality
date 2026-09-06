#!/usr/bin/env python3
"""Exact finite checks for the manuscript's approximation section.

Standard library only; no sampling or numerical optimization. These checks
validate the declared finite cases, not the quantified manuscript theorems.
"""

from fractions import Fraction
from itertools import combinations, product
from math import comb, isqrt


def expect(values):
    return sum(values, Fraction()) / len(values)


def tv(left, right):
    return sum(abs(a - b) for a, b in zip(left, right)) / 2


def parity_bound(n, k):
    return Fraction(1, 2) - Fraction(
        sum(comb(n, j) for j in range((n - k - 1) // 2 + 1)), 2**n
    )


def check_binomial_constants():
    cases = 0
    for n in range(1, 257):
        central = Fraction(comb(n, n // 2), 2**n)
        assert central * central * (n + 1) <= 1
        for k in range(n):
            bound = parity_bound(n, k)
            assert 0 <= bound <= Fraction(k + 1, 2) * central
            cases += 1
    return cases


def check_thresholds():
    cases = 0
    for n in range(1, 4):
        points = list(product((0, 1), repeat=n))
        signs = [(-1) ** sum(x) for x in points]
        for k in range(n):
            scopes = [
                scope for degree in range(k + 1)
                for scope in combinations(range(n), degree)
            ]
            features = [
                [int(all(x[i] for i in scope)) for scope in scopes]
                for x in points
            ]
            bound = parity_bound(n, k)
            for coefficients in product((-1, 0, 1), repeat=len(scopes)):
                values = [
                    sum(c * v for c, v in zip(coefficients, row))
                    for row in features
                ]
                correlation = expect([
                    chi * int(value >= 0)
                    for chi, value in zip(signs, values)
                ])
                assert abs(correlation) <= bound
                cases += 1
    return cases


def check_clipped_transfer():
    # Exhaust every nonzero 4-by-2 table with entries in {0, 1, 4}.
    # Different positive levels exercise clipping; empty slices are included.
    # Use its actual superlevel discrepancy, with no locality assumption.
    cases = 0
    for entries in product((0, 1, 4), repeat=8):
        total = sum(entries)
        if not total:
            continue
        slices = [
            [Fraction(4 * entries[2 * x + h], total) for x in range(4)]
            for h in range(2)
        ]
        density = [sum(column) for column in zip(*slices)]
        visible = [u / 4 for u in density]
        for plus in combinations(range(4), 2):
            signs = [1 if x in plus else -1 for x in range(4)]
            discrepancy = max(
                abs(expect([
                    chi * int(value > level)
                    for chi, value in zip(signs, component)
                ]))
                for component in slices
                for level in {Fraction(), *component}
            )
            for beta in (Fraction(1, 4), Fraction(1, 2), Fraction(1)):
                target = [(1 + beta * chi) / 4 for chi in signs]
                cap = 1 + beta
                clipped = [[min(value, cap) for value in row] for row in slices]
                for row in clipped:
                    assert abs(expect([
                        chi * value for chi, value in zip(signs, row)
                    ])) <= cap * discrepancy
                assert tv(target, visible) >= (beta - 2 * cap * discrepancy) / 2
                cases += 1
    return cases


def ceil_sqrt(value):
    root = isqrt(value.numerator // value.denominator)
    return root + int(root * root < value)


def check_window_lifts():
    cases = 0
    nonempty_tails = 0
    for n in range(1, 513):
        for beta in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
            for epsilon in (beta / 4, beta / 8):
                radius = ceil_sqrt((1 + beta) * n / (4 * epsilon))
                width = (2 * radius + 1).bit_length()
                offset = n // 2 - radius
                layers = [
                    Fraction(comb(n, s), 2**n) * (1 + beta * (-1) ** s)
                    for s in range(n + 1)
                ]
                assert sum(layers) == 1
                keep = [0 <= s - offset < 2**width for s in range(n + 1)]
                discarded = sum(
                    mass for mass, included in zip(layers, keep) if not included
                )
                assert discarded <= epsilon
                nonempty_tails += int(discarded > 0)
                conditional = [
                    mass / (1 - discarded) if included else Fraction()
                    for mass, included in zip(layers, keep)
                ]
                assert tv(layers, conditional) == discarded
                for s in range(n + 1):
                    if abs(Fraction(s) - Fraction(n, 2)) <= radius:
                        assert keep[s]
                    code = s - offset
                    if keep[s]:
                        bits = [(code >> j) & 1 for j in range(width)]
                        assert sum((2**j) * b for j, b in enumerate(bits)) == code
                        assert (offset + bits[0]) % 2 == s % 2
                    if n <= 12:
                        zeros = [
                            h for h in range(2**width)
                            if (s - offset - h) ** 2 == 0
                        ]
                        assert zeros == ([code] if keep[s] else [])
                cases += 1
    assert nonempty_tails > 0
    return cases, nonempty_tails


def main():
    print("Exact finite validation; no asymptotic or Lean-proof claim.")
    print(f"Binomial bounds: {check_binomial_constants()} cases, n=1..256, k=0..n-1.")
    print(f"Polynomial thresholds: {check_thresholds()} coefficient vectors, n=1..3.")
    print(f"Clipped transfer: {check_clipped_transfer()} joint-table/balanced-sign/bias cases.")
    windows, tails = check_window_lifts()
    print(f"Window lifts: {windows} cases, n=1..512; {tails} discard positive mass.")
    print("All checks passed using exact integers and rational arithmetic.")


if __name__ == "__main__":
    main()
