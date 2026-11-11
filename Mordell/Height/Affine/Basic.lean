module
public import Mathlib
public import Mordell.Attr

/-!
# The affine height of a coefficient vector

Let `K` be a number field. For a polynomial, a finite family of polynomials, or a vector `f`
with coefficients in `K`, and a place `v` of `K`, let `|f|_v` be the maximum of `|c|_v` over
the coefficients `c` of `f`, for Bombieri's normalised absolute values
`|x|_v = ‖x‖_v ^ (n_v / [K : ℚ])`. The *affine height* of `f` is
`h_aff(f) = ∑_v log max(1, |f|_v)`, the sum over all places `v` of `K`. Unlike the projective
height `Finsupp.logHeight`, it is not invariant under scaling, and it is `0` for `f = 0`.

## Main definitions

* `Faltings.affineLogHeight`: the affine logarithmic height of a finitely supported
  coefficient vector `f : α →₀ K`.

## Implementation notes

A coefficient vector is a finitely supported function `f : α →₀ K`: a polynomial
`MvPolynomial σ K` is `(σ →₀ ℕ) →₀ K`, a family of polynomials is a finitely supported function
on pairs (index, monomial), and a vector `ι → K` with `ι` finite is
`Finsupp.equivFunOnFinite.symm`. The maximum `|f|_v` is taken over the support of `f`, as in
`Finsupp.mulHeight`; it is `0` when `f = 0`.

The places of `K` are Mathlib's `NumberField.InfinitePlace K` and `NumberField.FinitePlace K`,
whose absolute values are `‖σ x‖` (for an embedding `σ : K → ℂ`) and `N(𝔭)^{-v_𝔭(x)}`. Bombieri's
normalised absolute value is the `n_v / [K : ℚ]`-th power of these, where `n_v` is
`InfinitePlace.mult` at an infinite place. For a finite place it is `1 / [K : ℚ]`, because
`|N_{K_𝔭/ℚ_p}(x)|_p = N(𝔭)^{-v_𝔭(x)}`. Since `log max(1, t ^ a) = a * log⁺ t` for `t ≥ 0` and
`a ≥ 0`, the sum over places becomes
`(∑_{v | ∞} n_v log⁺ ‖f‖_v + ∑ᶠ_{v ∤ ∞} log⁺ ‖f‖_v) / [K : ℚ]`. This is the same shape as
`NumberField.logHeight₁_eq`, divided by the degree. So `h_aff` is the absolute height, which does
not depend on the number field containing the coefficients.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 2, 7 and 8
-/

namespace Faltings

open NumberField Real in
/-- The affine logarithmic height `h_aff(f) = ∑_v log max(1, |f|_v)` of a finitely supported
coefficient vector `f` over a number field `K`. Here `|f|_v` is the maximum of Bombieri's
normalised `|c|_v` over the coefficients `c` of `f`, and the sum runs over all places of `K`.
Written with Mathlib's places, it is
`(∑_{v | ∞} n_v log⁺ max_c ‖c‖_v + ∑ᶠ_{v ∤ ∞} log⁺ max_c ‖c‖_v) / [K : ℚ]`. -/
@[expose, faltings "def_bvs_affine_height"]
public noncomputable def affineLogHeight {K : Type*} [Field K] [NumberField K] {α : Type*}
    (f : α →₀ K) : ℝ :=
  ((∑ v : InfinitePlace K, v.mult * log⁺ (⨆ c : f.support, v (f c))) +
      ∑ᶠ v : FinitePlace K, log⁺ (⨆ c : f.support, v (f c))) / Module.finrank ℚ K

end Faltings
