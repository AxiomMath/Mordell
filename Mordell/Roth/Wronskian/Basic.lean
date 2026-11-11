module
public import Mathlib
public import Mordell.Attr

/-!
# Generalized Wronskian determinants

Let `K` be a field of characteristic `0`, `f₀, …, fₛ ∈ K[ς₁, …, ςₗ]` and `I₀, …, Iₛ ∈ ℕˡ`.
For a multi-index `I = (i₁, …, iₗ)` the divided derivative is
`∂_I = (1 / (i₁! ⋯ iₗ!)) ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₗ}/∂ςₗ^{iₗ}`, and the generalized Wronskian is
the determinant `Wr_{I₀,…,Iₛ}(f₀, …, fₛ) = det (∂_{I_μ} f_j)_{μ, j = 0, …, s}`.
For `l = 1` and `I_ν = ν` this is the classical Wronskian `Wr(f₀, …, fₛ) = det (∂_ν f_j)`.

## Main definitions

* `Faltings.generalizedWronskian I f`: the determinant `det (∂_{I μ} (f j))_{μ, j}` in
  `MvPolynomial (Fin l) K`.

## Implementation notes

The divided derivative `∂_I` is written out as the scalar `(∏ₖ (I k)!)⁻¹` times the product in
`Module.End K (MvPolynomial (Fin l) K)` of the iterated partial derivatives
`(MvPolynomial.pderiv k) ^ (I k)` over `k = 0, …, l - 1`, in this order (`List.ofFn`); partial
derivatives commute, so the order does not matter. Multi-indices are
functions `Fin l → ℕ`. The one-variable Wronskian is the case `l = 1`, `I = fun ν _ => ν`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9, pp. 634–635.
-/

open MvPolynomial

namespace Faltings

/-- The generalized Wronskian `Wr_{I₀,…,Iₛ}(f₀, …, fₛ) = det (∂_{I_μ} f_j)_{μ, j}` of polynomials
`f₀, …, fₛ ∈ K[ς₁, …, ςₗ]` with respect to multi-indices `I₀, …, Iₛ ∈ ℕˡ`, where
`∂_I = (∏ₖ (I k)!)⁻¹ ∏ₖ ∂^{I k}/∂ςₖ^{I k}` is the divided derivative. -/
@[faltings "def_bvr_wronskian_det", expose]
public noncomputable def generalizedWronskian {K : Type*} [Field K] [CharZero K] {l s : ℕ}
    (I : Fin (s + 1) → Fin l → ℕ) (f : Fin (s + 1) → MvPolynomial (Fin l) K) :
    MvPolynomial (Fin l) K :=
  Matrix.det <| Matrix.of fun μ j =>
    (∏ k, ((I μ k).factorial : K))⁻¹ •
      (List.ofFn fun k : Fin l =>
        (pderiv k).toLinearMap ^ I μ k).prod (f j)

end Faltings
