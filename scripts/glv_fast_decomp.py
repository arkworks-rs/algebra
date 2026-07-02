#!/usr/bin/env python3
"""Generate the `GLVFastDecomp` constants for a curve from its
`SCALAR_DECOMP_COEFFS`.

`fast_scalar_decomposition` computes the rounding
`round(k * |n_ij| / r)` as `round(k * g / 2^M)` with `M = 64 * (N + 2)` and a
precomputed `g = round(2^M * |n_ij| / r)`, so the division by `r` becomes a
shift. This script prints, for each curve, the `g1`/`g2` limbs and the `a12`,
`a22`, `negate_k2` fields of `GLVFastDecomp`.

Edit `CURVES` below (the entries mirror `SCALAR_DECOMP_COEFFS`, in the order
n11, n12, n21, n22, as `(sign, magnitude)` with `sign` being +1 or -1) and run:

    python3 scripts/glv_fast_decomp.py

References
---------
- GLV endomorphism method (split `k = k1 + lambda*k2` into ~half-width `k1, k2`) from
  [Faster Point Multiplication on Elliptic Curves with Efficient Endomorphisms](https://iacr.org/archive/crypto2001/21390189.pdf)
- Turning `round(k * |n_ij| / r)` into the division-free `round(k * g / 2^M)` with
  a precomputed `g = round(2^M * |n_ij| / r)` is a Barrett-style precomputed
  reciprocal.
- [gnark-crypto](https://hackmd.io/@drouyang/glv) uses the same precomputed
   reciprocal rounding (precompute `2^m * v / d`, then shift instead of divide at runtime
"""

CURVES = {
    "Pallas": dict(
        # scalar field modulus r
        r=28948022309329048855892746252171976963363056481941647379679742748393362948097,
        lam=26005156700822196841419187675678338661165322343552424574062261873906994770353,
        limbs=4,
        # (sign, magnitude) for n11, n12, n21, n22
        n=[
            (-1, 98231058071100081932162823354453065728),
            (+1, 98231058071186745657228807397848383489),
            (-1, 196462116142286827589391630752301449217),
            (-1, 98231058071100081932162823354453065728),
        ],
    ),
    "Vesta": dict(
        r=28948022309329048855892746252171976963363056481941560715954676764349967630337,
        lam=20444556541222657078399132219657928148671392403212669005631716460534733845831,
        limbs=4,
        n=[
            (-1, 98231058071100081932162823354453065729),
            (+1, 98231058071186745657228807397848383488),
            (-1, 196462116142286827589391630752301449217),
            (-1, 98231058071100081932162823354453065729),
        ],
    ),
}


def limbs_le(x, n):
    assert x >> (64 * n) == 0, "value does not fit in the requested number of limbs"
    # out is 64-bit limbs of x in little-endian
    out = [(x >> (64 * i)) & 0xFFFFFFFFFFFFFFFF for i in range(n)]
    return out


for name, c in CURVES.items():
    r, lam, N = c["r"], c["lam"], c["limbs"]
    (s11, a11), (s12, a12), (s21, a21), (s22, a22) = c["n"]
    n11, n12, n21, n22 = s11 * a11, s12 * a12, s21 * a21, s22 * a22

    # The short vectors must lie in the GLV lattice and the matrix determinant
    # must be the scalar field modulus.
    assert (n11 + n12 * lam) % r == 0, f"{name}: row 1 not in GLV lattice"
    assert (n21 + n22 * lam) % r == 0, f"{name}: row 2 not in GLV lattice"
    assert abs(n11 * n22 - n12 * n21) == r, f"{name}: determinant != r"

    # 2 spare limbs to handle error from division
    M = 64 * (N + 2)
    # rounding trick: add 1/2 to numerator since python's integer division is equivalent to float
    g1 = (2**M * a22 + r // 2) // r  # round(2^M * |n22| / r)
    g2 = (2**M * a12 + r // 2) // r  # round(2^M * |n12| / r)

    # +1 because g1, g2 are 1 limb wider than scalar
    fmt = lambda g: ",\n            ".join(f"0x{w:016x}" for w in limbs_le(g, N + 1))
    print(f"// {name}")
    print("    const FAST_DECOMP: Option<GLVFastDecomp<Self::ScalarField>> = Some(GLVFastDecomp {")
    print(f"        g1: &[\n            {fmt(g1)},\n        ],")
    print(f"        g2: &[\n            {fmt(g2)},\n        ],")
    print(f'        a12: MontFp!("{a12}"),')
    print(f'        a22: MontFp!("{a22}"),')
    print(f"        negate_k2: {str(s12 * s22 == -1).lower()},")
    print("    });\n")
