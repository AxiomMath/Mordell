module
public import Mathlib
public import Mordell.Attr

/-!
# The Wronskian `W` of Roth's lemma

Let `P` be a polynomial over a field `K` in the variables `ς₁, …, ς_m` with `m ≥ 2`, and let
`I'₀, …, I'_s ∈ ℕ^{m-1}` be multi-indices in the first `m - 1` variables. The Wronskian
`W_{I'}(P)` is the `(s+1) × (s+1)` determinant `det (∂_{I'_μ} ∂_ν P)_{μ,ν = 0, …, s}`, where
`∂_{I'_μ}` is the divided derivative in `ς₁, …, ς_{m-1}` and `∂_ν` the divided derivative of
order `ν` in `ς_m`. Equivalently, the `(μ, ν)` entry is the divided derivative `∂_{(I'_μ, ν)} P`
for the multi-index `(I'_μ, ν) ∈ ℕ^m`, where for `I = (i₁, …, i_m)`
`∂_I = (i₁! ⋯ i_m!)⁻¹ ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{i_m}/∂ς_m^{i_m}`.

## Main definitions

* `Faltings.rothWronskian`: the determinant `det (∂_{(I'_μ, ν)} P)_{μ,ν}`.

## Implementation notes

The `m` variables are `Fin (n + 2)` (so `m = n + 2 ≥ 2`), the last one, `Fin.last (n + 1)`,
being `ς_m`; a multi-index `I' : Fin (n + 1) → ℕ` in the first `m - 1` variables is extended to
`(I', ν)` by `Fin.snoc`. The divided derivative is written as the scalar `(∏ₖ iₖ!)⁻¹` times the
ordered composite of the iterated partial derivatives `MvPolynomial.pderiv`, as in its
definition; these partial derivatives commute (`MvPolynomial.pderiv_comm`), so the order is
immaterial. The base field `K` is any field of characteristic zero (the source takes `K = ℚ̄`):
in positive characteristic `(∏ₖ iₖ!)⁻¹ ∏ₖ ∂^{iₖ}` is not the divided (Hasse) derivative, since
the factorials may vanish while the divided derivative does not (over `𝔽₂`, `∂_2 ς² = 1`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 635
-/

namespace Faltings

open MvPolynomial in
/-- The Wronskian `W_{I'}(P) = det (∂_{I'_μ} ∂_ν P)_{μ,ν=0,…,s}` of Roth's lemma, for a polynomial
`P` in the `m = n + 2` variables `Fin (n + 2)` and multi-indices `I' μ` in the first `m - 1`
variables; `∂_ν` is the divided derivative of order `ν` in the last variable, and the entry is the
divided derivative `∂_{(I'_μ, ν)} P = (∏ₖ iₖ!)⁻¹ • ∏ₖ (∂/∂ςₖ)^{iₖ} P` for `(iₖ) = (I'_μ, ν)`. -/
@[faltings "def_bvr_wronskian_w", expose]
public noncomputable def rothWronskian {K : Type*} [Field K] [CharZero K] {n s : ℕ}
    (I' : Fin (s + 1) → Fin (n + 1) → ℕ) (P : MvPolynomial (Fin (n + 2)) K) :
    MvPolynomial (Fin (n + 2)) K :=
  Matrix.det <| Matrix.of fun μ ν : Fin (s + 1) =>
    let I : Fin (n + 2) → ℕ := Fin.snoc (I' μ) (ν : ℕ)
    (∏ k, ((I k).factorial : K))⁻¹ •
      (List.ofFn fun k => (pderiv k).toLinearMap ^ I k).prod P

end Faltings
