#!/usr/bin/env python3
"""Check the arithmetic consequences of the audited binary-RBM bounds.

This does not re-prove the cited statistical-model theorems.  It verifies the
integer parameter-count lower bound derived from Montufar--Morton Corollary 26
and compares the transcribed U(n,n) values from Montufar--Rauh Table 2 with the
older 2^(n-1)-1 universal-approximation bound.

Dependencies: Python 3 standard library only.
"""

from math import ceil


# First column of Montufar--Rauh Table 2.  The paper states that U(n,n) is
# exact for n <= 9; later entries are published upper bounds.
STAR_COVER_UPPER = {
    2: 1,
    3: 3,
    4: 6,
    5: 12,
    6: 21,
    7: 39,
    8: 69,
    9: 127,
    10: 228,
    11: 421,
    12: 760,
    13: 1528,
    14: 3185,
}


def dimension_lower_bound(n: int) -> int:
    """Smallest m for which (n+1)(m+1)-1 can reach 2^n-1."""
    return ceil((2**n) / (n + 1)) - 1


def brute_dimension_lower_bound(n: int) -> int:
    target_dimension = 2**n - 1
    m = 0
    while (n + 1) * (m + 1) - 1 < target_dimension:
        m += 1
    return m


for n, star_upper in STAR_COVER_UPPER.items():
    lower = dimension_lower_bound(n)
    assert lower == brute_dimension_lower_bound(n)

    old_upper = 2 ** (n - 1) - 1
    assert lower <= star_upper <= old_upper

    if n >= 4:
        assert star_upper < old_upper

    print(
        f"n={n:2d}  dimension-lower={lower:4d}  "
        f"star-cover-upper={star_upper:4d}  old-upper={old_upper:4d}"
    )
