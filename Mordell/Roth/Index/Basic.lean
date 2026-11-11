module
public import Mathlib
public import Mordell.Attr

/-!
# The index of a multivariate polynomial at a point

Fix positive integers `r₁, …, rₘ` and a point `ς⁰ ∈ Kᵐ`. For a multi-index `I = (i₁, …, iₘ)`
let `∂_I = (1 / i₁! ⋯ iₘ!) ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₘ}/∂ςₘ^{iₘ}` be the divided derivative, and let
`w(I) = i₁/r₁ + ⋯ + iₘ/rₘ` be the weight of `I`. The *index* of a polynomial
`Q ∈ K[ς₁, …, ςₘ]` with respect to `(r₁, …, rₘ)` at `ς⁰` is the least weight `w(I)` of a
multi-index with `∂_I Q (ς⁰) ≠ 0`. It is `+∞` when `Q = 0`, because then no such `I` exists.

## Main definitions

* `Faltings.MvPolynomial.index r ς₀ Q`: the index of `Q` with respect to the weights `r` at
  `ς₀`, valued in `ℝ≥0∞`.

## Implementation notes

The source works over `\overline{ℚ}`. Here the base is any field `K` of characteristic zero,
which is what the factorials `1 / i_μ!` in `∂_I` need. Multi-indices are `Fin m →₀ ℕ`, the
exponents of `MvPolynomial (Fin m) K`. The divided derivative is the composite of the iterated
partial derivatives `MvPolynomial.pderiv μ`, taken in order `μ = 0, …, m - 1` (they commute),
and then scaled by `(∏ μ, i_μ!)⁻¹`.

The index is the infimum in `ℝ≥0∞` of the weights `w(I)` with `∂_I Q (ς⁰) ≠ 0`. Only finitely
many `I` have `∂_I Q ≠ 0`, so for `Q ≠ 0` the infimum is a minimum and is a nonnegative
rational. For `Q = 0` it is the infimum of the empty set, `⊤ = +∞`, which is the source's
convention `ind(0) = +∞`.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 634][bombieri1990]
-/

namespace Faltings.MvPolynomial

open scoped ENNReal in
/-- The *index* of a polynomial `Q ∈ K[ς₁, …, ςₘ]` with respect to positive weights
`r = (r₁, …, rₘ)` at `ς₀ ∈ Kᵐ`. It is the least weight `w(I) = ∑ μ, i_μ / r_μ` of a multi-index
`I` whose divided derivative
`∂_I Q = (∏ μ, i_μ!)⁻¹ • ∂^{i₁}_{ς₁} ⋯ ∂^{iₘ}_{ςₘ} Q` does not vanish at `ς₀`. When `Q = 0` it is
`⊤ = +∞`. -/
@[expose, faltings "def_bvr_index"]
public noncomputable def index {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+)
    (ς₀ : Fin m → K) (Q : MvPolynomial (Fin m) K) : ℝ≥0∞ :=
  ⨅ (I : Fin m →₀ ℕ)
    (_ : MvPolynomial.eval ς₀
        ((∏ μ, ((I μ).factorial : K))⁻¹ •
          (List.ofFn fun μ : Fin m =>
            ((MvPolynomial.pderiv μ : Derivation K (MvPolynomial (Fin m) K)
              (MvPolynomial (Fin m) K)) : MvPolynomial (Fin m) K →ₗ[K] MvPolynomial (Fin m) K)
              ^ I μ).prod Q) ≠ 0),
    ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞))

end Faltings.MvPolynomial
