module
public import Mathlib
public import Mordell.Attr

/-!
# The length of a polynomial

The length `𝓛(u)` of a polynomial `u` is the sum of the absolute values of its coefficients,
`𝓛(u) = ∑ₘ |u_m|`. It is the `ℓ¹`-norm of the coefficient vector. It is subadditive and
submultiplicative, and it bounds `|u(x)|` whenever every coordinate of `x` has absolute value at
most `1`.

## Main definitions

* `Faltings.MvPolynomial.length`: the sum of the norms of the coefficients of a multivariate
  polynomial.

## Implementation notes

Bombieri uses the length for polynomials with complex coefficients in the two variables `X, Y`.
Here it is defined for a multivariate polynomial in any family of variables `σ`, with
coefficients in any commutative semiring that carries a norm. The source's object is the
case `MvPolynomial (Fin 2) ℂ`, where `‖·‖` is the complex absolute value.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings.MvPolynomial

/-- The length `𝓛(u)` of a polynomial `u`: the sum `∑ₘ ‖u_m‖` of the norms of its
coefficients, i.e. the `ℓ¹`-norm of its coefficient vector. -/
@[expose, faltings "def_bvs_length"]
public noncomputable def length {σ R : Type*} [CommSemiring R] [Norm R]
    (u : _root_.MvPolynomial σ R) : ℝ :=
  ∑ m ∈ u.support, ‖u.coeff m‖

end Faltings.MvPolynomial
