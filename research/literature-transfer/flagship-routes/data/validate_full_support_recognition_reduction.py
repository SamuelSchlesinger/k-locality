#!/usr/bin/env python3
"""Exact sanity checks for the few-variable full-support reduction.

This script does not prove the theorem in circuit-consequences.md.  It checks,
with fractions and exhaustive Boolean-cube enumeration, the identities used in
the proof for representative one-hidden-bit quadratic boundary faces:

* A(x) = -min_h B(x,h) has the claimed degree;
* the exposed support is exactly argmin_h B(x,h);
* marginal weights factor as visible_weight(x) * R_{B,u}(x); and
* log(D/R_{B,u}) has degree at most two, tested without logarithms by all
  three-dimensional conditional-odds identities.

Dependencies: Python 3 standard library only.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product


Point = tuple[int, ...]


def cube(n: int) -> list[Point]:
    return list(product((0, 1), repeat=n))


def monomial(x: Point, scope: tuple[int, ...]) -> int:
    return int(all(x[i] for i in scope))


def additive_table(
    n: int, coefficients: dict[tuple[int, ...], Fraction]
) -> dict[Point, Fraction]:
    return {
        x: sum(
            (coefficient * monomial(x, scope) for scope, coefficient in coefficients.items()),
            Fraction(0),
        )
        for x in cube(n)
    }


def multiplicative_table(
    n: int, parameters: dict[tuple[int, ...], Fraction]
) -> dict[Point, Fraction]:
    result: dict[Point, Fraction] = {}
    for x in cube(n):
        value = Fraction(1)
        for scope, parameter in parameters.items():
            if monomial(x, scope):
                value *= parameter
        result[x] = value
    return result


def mobius_coefficients(values: dict[Point, Fraction]) -> dict[tuple[int, ...], Fraction]:
    n = len(next(iter(values)))
    coeffs: dict[tuple[int, ...], Fraction] = {}
    for size in range(n + 1):
        for scope in combinations(range(n), size):
            total = Fraction(0)
            for subsize in range(size + 1):
                for subset in combinations(scope, subsize):
                    x = tuple(int(i in subset) for i in range(n))
                    total += (-1) ** (size - subsize) * values[x]
            coeffs[scope] = total
    return coeffs


def degree(values: dict[Point, Fraction]) -> int:
    nonzero = [len(scope) for scope, value in mobius_coefficients(values).items() if value]
    return max(nonzero, default=0)


def conditional_odds_identity(
    values: dict[Point, Fraction], order: int
) -> bool:
    """Check that log(values) has Boolean degree < order.

    For positive rational values, a vanishing order-fold additive difference
    of the logarithm is equivalent to an exact product equality.
    """

    n = len(next(iter(values)))
    assert all(value > 0 for value in values.values())
    for varying in combinations(range(n), order):
        fixed_indices = tuple(i for i in range(n) if i not in varying)
        for fixed_bits in product((0, 1), repeat=len(fixed_indices)):
            positive = Fraction(1)
            negative = Fraction(1)
            for varying_bits in product((0, 1), repeat=order):
                x_list = [0] * n
                for i, bit in zip(fixed_indices, fixed_bits):
                    x_list[i] = bit
                for i, bit in zip(varying, varying_bits):
                    x_list[i] = bit
                value = values[tuple(x_list)]
                if sum(varying_bits) % 2 == order % 2:
                    positive *= value
                else:
                    negative *= value
            if positive != negative:
                return False
    return True


def check_case(
    name: str,
    n: int,
    b_coefficients: dict[tuple[int, ...], Fraction],
    hidden_parameters: dict[tuple[int, ...], Fraction],
) -> None:
    # B(x,h)=h*b(x) for one hidden bit.  The scopes below index visible
    # variables only; all corresponding joint monomials also contain h.
    b = additive_table(n, b_coefficients)
    hidden_weight = multiplicative_table(n, hidden_parameters)

    a = {x: max(Fraction(0), -b[x]) for x in cube(n)}
    assert degree(a) <= 2, (name, "exposing offset has degree", degree(a))

    fibers: dict[Point, tuple[int, ...]] = {}
    for x in cube(n):
        energies = (a[x], a[x] + b[x])
        assert min(energies) == 0
        assert all(value >= 0 for value in energies)
        fibers[x] = tuple(h for h, value in enumerate(energies) if value == 0)

    # A nontrivial positive visible quadratic factor, represented
    # multiplicatively so every check remains rational.
    visible_parameters: dict[tuple[int, ...], Fraction] = {
        (0,): Fraction(2),
        (1,): Fraction(3),
        (0, 1): Fraction(5, 2),
        (2, 3): Fraction(7, 3),
    }
    visible_weight = multiplicative_table(n, visible_parameters)

    r_factor: dict[Point, Fraction] = {}
    unnormalized: dict[Point, Fraction] = {}
    for x in cube(n):
        r_factor[x] = sum(
            (Fraction(1) if h == 0 else hidden_weight[x] for h in fibers[x]),
            Fraction(0),
        )
        unnormalized[x] = visible_weight[x] * r_factor[x]

    partition = sum(unnormalized.values(), Fraction(0))
    distribution = {x: value / partition for x, value in unnormalized.items()}
    assert all(value > 0 for value in distribution.values())
    assert sum(distribution.values(), Fraction(0)) == 1

    quotient = {x: distribution[x] / r_factor[x] for x in cube(n)}
    assert all(quotient[x] == visible_weight[x] / partition for x in cube(n))
    assert conditional_odds_identity(quotient, order=3)

    print(
        f"{name}: passed; degree(A)={degree(a)}, "
        f"fiber sizes={sorted(set(map(len, fibers.values())))}"
    )


def main() -> None:
    n = 4
    check_case(
        "full joint face",
        n,
        b_coefficients={},
        hidden_parameters={(): Fraction(3), (0,): Fraction(2), (2,): Fraction(5, 3)},
    )
    check_case(
        "deterministic graph face",
        n,
        b_coefficients={(): Fraction(-1), (0,): Fraction(2)},
        hidden_parameters={(): Fraction(3, 2), (1,): Fraction(4), (3,): Fraction(5, 2)},
    )
    check_case(
        "mixed boundary fibers",
        n,
        b_coefficients={(0,): Fraction(1)},
        hidden_parameters={(): Fraction(7, 2), (1,): Fraction(2), (2,): Fraction(3)},
    )
    print("all exact full-support recognition identities passed")


if __name__ == "__main__":
    main()
