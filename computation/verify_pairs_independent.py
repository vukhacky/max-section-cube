#!/usr/bin/env python3
"""Independent three-variable check of the finite pair comparison.

Run with Python 3.8 or later. For each multiplicity type the program
subdivides the full closed box of two squared row lengths and one half-angle.
A leaf is counted as excluded if its parameters violate a necessary
geometric condition, or as certified if the angular inequality holds.
"""
from fractions import Fraction
from functools import lru_cache


def interval(index, low, high):
    """The indexed dyadic subinterval of [low, high], including both ends."""
    level, offset = index
    width = (high - low) / (2 ** level)
    return low + offset * width, low + (offset + 1) * width


def verify(q, m, ell):
    a, b = Fraction(1, q + 1), Fraction(1, q)
    exponent = 2 * q - m - ell
    R = (1 + b) ** (exponent // 2) / q
    if exponent % 2:
        R *= 1 + b / 2
    if R ** 2 < (1 + b) ** exponent / q ** 2:
        raise ArithmeticError("The rational density bound is too small.")

    @lru_cache(maxsize=None)
    def charge(j, lo, hi):
        # At lo the curvature coefficient and the quotient are largest.
        # The last factor increases, so it is evaluated at hi.
        z = 1 - q * lo
        numerator = (1 - a) * (6 + 2 * (a + z)) + a * a + a * z + z * z
        curvature = a * numerator / (12 * (1 - a))
        quotient = 1 if j == q else (1 - q * lo) / (1 - j * lo)
        return curvature * quotient * (q + 1 - 1 / hi) / 2

    unit = (Fraction(0), Fraction(1))
    stack = [((0, 0), (0, 0), (0, 0))]
    excluded = certified = deepest = 0
    while stack:
        indices = stack.pop()
        levels = tuple(level for level, _ in indices)
        depth = sum(levels)
        deepest = max(deepest, depth)
        c0, c1 = interval(indices[0], a, b)
        d0, d1 = interval(indices[1], a, b)
        t0, t1 = interval(indices[2], *unit)

        # As t = tan(theta/2) increases on [0,1], sine increases and
        # cosine decreases. The projection minor gives a second angle bound.
        sine_lo = 2 * t0 / (1 + t0 ** 2)
        sine_hi = 2 * t1 / (1 + t1 ** 2)
        cos_lo = (1 - t1 ** 2) / (1 + t1 ** 2)
        cap = (1 - m * c0) * (1 - ell * d0) / (m * c0 * ell * d0)
        if cos_lo ** 2 > cap:
            excluded += 1
            continue

        # Bound the necessary strip inequality from opposite sides.
        # L and the strip width are bounded below. Using the upper R
        # makes the following strict rejection test weaker.
        g_lo = min(c0, d0)
        L_lo = max(0, (c0 + d0) / 2 + g_lo * cos_lo - c1 * d1 * sine_hi ** 2)
        width_lo = L_lo * g_lo * sine_lo / (2 * R)
        if not 0 <= width_lo <= Fraction(1, 2):
            raise ArithmeticError("Strip width outside its proved range.")
        angle_upper = t1 + c1 * d1 * sine_hi ** 3 / 8
        if 2 * R * angle_upper * (1 - width_lo) ** 2 < L_lo ** 2:
            excluded += 1
            continue

        # Square only nonnegative quantities. Since s/(15+s) increases,
        # its value at this lower bound for sin^2(theta) suffices.
        s = max(sine_lo ** 2, 1 - cap)
        needed = charge(m, c0, c1) + charge(ell, d0, d1) + Fraction(1, 4000)
        factor = Fraction(2, 9) + (2 - m * c0 - ell * d0) / 4
        if 3 * s ** 2 > 5 * ((15 + s) * factor * needed) ** 2:
            certified += 1
            continue

        if depth >= 35:
            raise ArithmeticError(f"Unresolved box for {(q, m, ell)}: {indices}")
        # Bisect the widest normalized coordinate, weighting angles by four.
        effective = (levels[0], levels[1], levels[2] - 2)
        axis = effective.index(min(effective))
        level, offset = indices[axis]
        for child in (2 * offset, 2 * offset + 1):
            stack.append(indices[:axis] + ((level + 1, child),) + indices[axis + 1:])
    return excluded, certified, deepest


def main():
    print(" q   m  ell   excluded   certified   max depth", flush=True)
    total = 0
    max_depth = 0
    for q in (2, 3, 4):
        for m in range(1, q + 1):
            for ell in range(m, q + 1):
                excluded, certified, depth = verify(q, m, ell)
                print(f"{q:2}  {m:2}  {ell:3}   {excluded:8}   {certified:9}"
                      f"   {depth:9}", flush=True)
                total += excluded + certified
                max_depth = max(max_depth, depth)
    print(f"Verified 19 types in {total} boxes, maximum depth {max_depth}.")


if __name__ == "__main__":
    main()
