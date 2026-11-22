#!/usr/bin/env python3
"""Verify the finite pair comparison in Maximal sections of the cube.

Run with Python 3.8 or later. The default checks all 19 unordered
multiplicity types. Add --case 2 1 2 to check that type alone.
Every comparison uses exact rational arithmetic. Each successful leaf
covers its entire closed rectangle, including its boundary.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
from typing import NamedTuple


SURPLUS = Fraction(1, 4000)
ANGLE_BISECTIONS = 10
DEPTH_LIMIT = 30


class Counts(NamedTuple):
    projection: int
    strip: int
    depth: int


def angle(t):
    """Return (sine, cosine) from the tangent of the half-angle."""
    denominator = 1 + t * t
    return 2 * t / denominator, (1 - t * t) / denominator


def verify_type(q, m, ell):
    """Cover [1/(q+1), 1/q]^2 for the unordered pair (m, ell)."""
    if q not in (2, 3, 4) or not 1 <= m <= ell <= q:
        raise ValueError("Expected q in {2,3,4} and 1 <= m <= ell <= q.")

    a = Fraction(1, q + 1)
    b = Fraction(1, q)
    exponent = 2 * q - m - ell
    # R bounds (1/q) (1 + 1/q)^(exponent/2) from above.
    R = b * (1 + b) ** (exponent // 2)
    if exponent % 2:
        R *= 1 + b / 2

    @lru_cache(maxsize=None)
    def charge_upper(j, low, high):
        """Bound H_{q,j} on the closed interval [low, high]."""
        z = 1 - q * low
        curvature = a / 2 * (
            1 + (a + z) / 3 + (a * a + a * z + z * z) / (6 * (1 - a))
        )
        # When j=q the quotient is identically one, also at its limit low=b.
        ratio = 1 if j == q else (1 - q * low) / (1 - j * low)
        return curvature * ratio * (q + 1 - 1 / high) / 2

    def certify_rectangle(c0, c1, d0, d1):
        charges = charge_upper(m, c0, c1) + charge_upper(ell, d0, d1)
        angular_factor = Fraction(2, 9) + (2 - m * c0 - ell * d0) / 4
        rhs = (charges + SURPLUS) * angular_factor

        def sufficient(s):
            # Here s is a lower bound on sin^2(theta). Both sides before
            # squaring are nonnegative, and the transport constant squares to 3/5.
            return 3 * s ** 2 > 5 * (rhs * (15 + s)) ** 2

        # The complementary Gram minor bounds cos^2(theta) from above.
        cap = (1 - m * c0) * (1 - ell * d0) / (m * c0 * ell * d0)
        if sufficient(max(Fraction(0), 1 - cap)):
            return "projection"

        # s/(15+s) increases with s. All angles above the upper endpoint
        # already pass the angular test. When even s=1 fails, keep all angles.
        upper = Fraction(1)
        if sufficient(Fraction(1)):
            lower = Fraction(0)
            for _ in range(ANGLE_BISECTIONS):
                mid = (lower + upper) / 2
                sine, _ = angle(mid)
                if sufficient(sine ** 2):
                    upper = mid
                else:
                    lower = mid

        # For t <= upper, sine is at most u, cosine at least rho, and L
        # at least L0. The monotonicity of t*(1-eta*sin(theta))^2 for
        # eta <= 1/2 bounds all possible small angles by the single upper endpoint.
        u, rho = angle(upper)
        g0 = min(c0, d0)
        L0 = (c0 + d0) / 2 + g0 * rho - c1 * d1 * u ** 2
        if L0 <= 0:
            return None
        eta = L0 * g0 / (2 * R)
        if not 0 <= eta <= Fraction(1, 2):
            raise ArithmeticError("Strip monotonicity bound violated.")
        left = 2 * R * upper * (1 + c1 * d1 * u ** 2 / 4) * (1 - eta * u) ** 2
        if left < L0 ** 2:
            return "strip"
        return None

    stack = [(a, b, a, b, 0)]
    projection = strip = max_depth = 0
    while stack:
        c0, c1, d0, d1, depth = stack.pop()
        max_depth = max(max_depth, depth)
        reason = certify_rectangle(c0, c1, d0, d1)
        if reason == "projection":
            projection += 1
        elif reason == "strip":
            strip += 1
        elif depth >= DEPTH_LIMIT:
            raise ArithmeticError(
                f"Unresolved rectangle for {(q, m, ell)}: {(c0, c1, d0, d1)}"
            )
        elif c1 - c0 >= d1 - d0:
            mid = (c0 + c1) / 2
            stack.append((c0, mid, d0, d1, depth + 1))
            stack.append((mid, c1, d0, d1, depth + 1))
        else:
            mid = (d0 + d1) / 2
            stack.append((c0, c1, d0, mid, depth + 1))
            stack.append((c0, c1, mid, d1, depth + 1))
    return Counts(projection, strip, max_depth)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", nargs=3, type=int, metavar=("Q", "M", "ELL"),
                        help="check a single unordered multiplicity type")
    args = parser.parse_args()
    cases = [(q, m, ell) for q in (2, 3, 4) for m in range(1, q + 1)
             for ell in range(m, q + 1)]
    if args.case is not None:
        case = tuple(args.case)
        if case not in cases:
            parser.error("Expected q in {2,3,4} and 1 <= m <= ell <= q.")
        cases = [case]

    print(" q   m  ell   projection   strip   max depth", flush=True)
    total = Counts(0, 0, 0)
    for q, m, ell in cases:
        row = verify_type(q, m, ell)
        print(f"{q:2}  {m:2}  {ell:3}   {row.projection:10}   {row.strip:5}"
              f"   {row.depth:9}", flush=True)
        total = Counts(total.projection + row.projection,
                       total.strip + row.strip, max(total.depth, row.depth))
    types = "type" if len(cases) == 1 else "types"
    leaves = total.projection + total.strip
    noun = "leaf" if leaves == 1 else "leaves"
    print(f"Verified {len(cases)} {types} in {leaves} {noun}"
          f" ({total.projection} projection, {total.strip} strip),"
          f" maximum depth {total.depth}.")


if __name__ == "__main__":
    main()
