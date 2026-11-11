module
public import Mordell.Roth.Index.Basic
public import Mordell.Polynomial.Taylor

/-!
# Range of the index

Let `r = (r₁, …, rₘ)` be positive integers, `ς⁰ ∈ Kᵐ`, and let `Q ≠ 0` be a polynomial of
degree at most `r_μ` in `ς_μ` for every `μ`. Then the index of `Q` with respect to `r` at `ς⁰`
satisfies `0 ≤ ind(Q) ≤ m`. Indeed some divided derivative `∂_I Q (ς⁰)` is non-zero, and it
vanishes unless `i_μ ≤ r_μ` for all `μ`, so such an `I` has weight `∑ μ, i_μ / r_μ ≤ m`.

## Main results

* `Faltings.MvPolynomial.index_le_of_degreeOf_le`: `index r ς₀ Q ≤ m`.

## Implementation notes

The index `Faltings.MvPolynomial.index` takes values in `ℝ≥0∞`, so the lower bound `0 ≤ ind(Q)`
holds for every `Q` and is `zero_le`; only the upper bound is stated.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 634][bombieri1990]
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

section

variable {K : Type*} [Field K] {m : ℕ}

/-- Translation of the variables by `x` is injective: `Q ≠ 0` implies `Q(x + τ) ≠ 0`. -/
private lemma aeval_C_add_X_ne_zero (x : Fin m → K) {Q : MvPolynomial (Fin m) K} (hQ : Q ≠ 0) :
    aeval (fun ν => C (x ν) + X ν) Q ≠ 0 := by
  intro h
  have hcomp : (aeval (fun ν => C (-x ν) + X ν)).comp
      (aeval (fun ν => C (x ν) + X ν) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) =
      AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro ν
    simp only [AlgHom.comp_apply, map_add, aeval_C, aeval_X, AlgHom.id_apply,
      algebraMap_eq, ← add_assoc, ← C_add, add_neg_cancel, C_0, zero_add]
  have := congrArg (fun f => f Q) hcomp
  simp only [AlgHom.comp_apply, h, map_zero, AlgHom.id_apply] at this
  exact hQ this.symm

/-- A non-vanishing iterated partial derivative `∂^I Q` forces `I μ ≤ degreeOf μ Q`. -/
private lemma le_degreeOf_of_pderiv_prod_ne_zero {I : Fin m →₀ ℕ} {Q : MvPolynomial (Fin m) K}
    (hD : (List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) :
      List (Module.End K (MvPolynomial (Fin m) K))).prod Q ≠ 0) (μ : Fin m) :
    I μ ≤ Q.degreeOf μ := by
  obtain ⟨J, hJ⟩ := ne_zero_iff.mp hD
  have h := coeff_ofFn_prod id Function.injective_id I Q J
  simp only [id] at h
  rw [h] at hJ
  have := monomial_le_degreeOf μ (mem_support_iff.mpr (left_ne_zero_of_mul hJ))
  simp only [Finsupp.univ_sum_single, Finsupp.add_apply] at this
  omega

end

open scoped ENNReal in
/-- If `Q ≠ 0` has degree at most `r μ` in each variable `ς_μ`, then the index of `Q` with
respect to `r` at any point `ς₀` is at most `m`. -/
@[faltings "lem_bvr_index_range"]
public theorem index_le_of_degreeOf_le {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (r : Fin m → ℕ+) (ς₀ : Fin m → K) {Q : MvPolynomial (Fin m) K} (hQ : Q ≠ 0)
    (hdeg : ∀ μ, Q.degreeOf μ ≤ r μ) :
    index r ς₀ Q ≤ m := by
  obtain ⟨I, hI⟩ := ne_zero_iff.mp (aeval_C_add_X_ne_zero ς₀ hQ)
  rw [coeff_aeval_C_add_X] at hI
  have hle μ : I μ ≤ (r μ : ℕ) :=
    (le_degreeOf_of_pderiv_prod_ne_zero (fun h => by simp [h] at hI) μ).trans (hdeg μ)
  refine (iInf₂_le I (by rwa [smul_eval])).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun μ _ => ENNReal.div_le_of_le_mul ?_).trans (by simp)
  rw [one_mul]
  exact_mod_cast hle μ

end Faltings.MvPolynomial
