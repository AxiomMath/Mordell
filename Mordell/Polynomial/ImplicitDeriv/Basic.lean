module
public import Mathlib
public import Mordell.Attr

/-!
# The numerators of the derivatives of an implicit branch

For `p ∈ R[X, Y]` the polynomials `q_l = q_l(p) ∈ R[X, Y]`, `l ≥ 1`, are defined by `q₁ = p_Y` and
`q_{l+1} = (q_l)_Y p_X² - (q_l)_X p_X p_Y + (2l - 1) q_l (p_{XX} p_Y - p_{XY} p_X)`.
If `ξ(ς)` is a power series with `p(ξ, ς) = 0` and `p_X(ξ(0), 0) ≠ 0`, then
`q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} (d/dς)^l ξ = 0`, so `q_l` is, up to sign, the numerator of the
`l`-th derivative of the implicit function `X = ξ(Y)` defined by `p = 0`.

## Main definitions

* `Faltings.MvPolynomial.implicitDerivNumerator p l`: the polynomial `q_l(p)`.

## Implementation notes

The polynomial ring `R[X, Y]` is `MvPolynomial (Fin 2) R` with `X = X 0` and `Y = X 1`, and the
partial derivatives are `MvPolynomial.pderiv 0` and `MvPolynomial.pderiv 1`. The recursion only
uses ring operations, so it is stated over any commutative ring `R`; the source's field `K` is a
special case. The sequence is indexed by `ℕ` with `q_l` at index `l` for `l ≥ 1`; the value at
`0` is the junk value `0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

/-- Bombieri's polynomials `q_l(p)`, `l ≥ 1`, attached to `p ∈ R[X, Y]`: `q₁ = p_Y` and
`q_{l+1} = (q_l)_Y p_X² - (q_l)_X p_X p_Y + (2l - 1) q_l (p_{XX} p_Y - p_{XY} p_X)`.
The value at `l = 0` is `0`. -/
@[expose, faltings "def_bvs_q_polynomials"]
public noncomputable def implicitDerivNumerator {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 2) R) : ℕ → MvPolynomial (Fin 2) R
  | 0 => 0
  | 1 => pderiv 1 p
  | n + 2 =>
    let q := implicitDerivNumerator p (n + 1)
    pderiv 1 q * pderiv 0 p ^ 2 - pderiv 0 q * pderiv 0 p * pderiv 1 p +
      ((2 * n + 1 : ℕ) : MvPolynomial (Fin 2) R) * q *
        (pderiv 0 (pderiv 0 p) * pderiv 1 p - pderiv 1 (pderiv 0 p) * pderiv 0 p)

end Faltings.MvPolynomial
