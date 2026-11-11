module
public import Mordell.Roth.Index.Basic

/-!
# The index of a divided derivative

Fix positive weights `r = (r₁, …, rₘ)` and a point `ς⁰ ∈ Kᵐ`, and let `ind` be the index
`Faltings.MvPolynomial.index r ς⁰`. Taking the divided derivative
`∂_I = (i₁! ⋯ iₘ!)⁻¹ ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₘ}/∂ςₘ^{iₘ}` lowers the index by at most the weight
of `I`:
`ind(∂_I Q) ≥ ind(Q) - i₁/r₁ - ⋯ - iₘ/rₘ`.

## Main results

* `Faltings.MvPolynomial.index_le_index_hasseDeriv_add`:
  `ind(Q) ≤ ind(∂_I Q) + ∑ μ, i_μ / r_μ`.

## Implementation notes

The index takes values in `ℝ≥0∞`, where subtraction is truncated. The inequality is stated
additively, `ind(Q) ≤ ind(∂_I Q) + w(I)`. Since the weight `w(I)` is finite, this is equivalent
to the source's `ind(Q) - w(I) ≤ ind(∂_I Q)` by `ENNReal.sub_le_iff_le_add`, and it also covers
`Q = 0` and `∂_I Q = 0` (index `⊤`) without case distinction. The divided derivative is written
out exactly as in `Faltings.MvPolynomial.index`.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 634, property (i), with the 1991
  errata][bombieri1990]
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

section

variable {K : Type*} [Field K] {m : ℕ}

/-- The partial derivative `∂/∂ς_μ`, as a `K`-linear endomorphism of `K[ς₁, …, ςₘ]`. -/
private noncomputable abbrev pderivₗ (μ : Fin m) : Module.End K (MvPolynomial (Fin m) K) :=
  (pderiv μ : Derivation K (MvPolynomial (Fin m) K) (MvPolynomial (Fin m) K))

/-- The iterated partial derivative `∂^I = ∏ μ, (∂/∂ς_μ) ^ (I μ)`, as written in the index. -/
private noncomputable abbrev iterPDeriv (I : Fin m →₀ ℕ) : Module.End K (MvPolynomial (Fin m) K) :=
  (List.ofFn fun μ : Fin m => (pderivₗ μ : Module.End K _) ^ I μ).prod

/-- Partial derivatives commute. -/
private lemma commute_pderivₗ (μ ν : Fin m) :
    Commute (pderivₗ (K := K) μ) (pderivₗ ν) := by
  refine LinearMap.ext fun p => MvPolynomial.ext _ _ fun n => ?_
  simp only [Module.End.mul_apply, Derivation.coeFn_coe, coeff_pderiv, Finsupp.add_apply]
  by_cases h : μ = ν
  · subst h; rfl
  · simp [h, Ne.symm h, add_right_comm n]
    ring

/-- `∂^J ∘ ∂^I = ∂^{J + I}`: since the partial derivatives commute, the factors can be
regrouped in the commutative monoid they generate. -/
private lemma iterPDeriv_mul (I J : Fin m →₀ ℕ) :
    iterPDeriv (K := K) J * iterPDeriv I = iterPDeriv (J + I) := by
  have : IsMulCommutative (Submonoid.closure (Set.range (pderivₗ (K := K) (m := m)))) :=
    Submonoid.isMulCommutative_closure _ <| by
      rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ -
      exact commute_pderivₗ (K := K) μ ν
  let := IsMulCommutative.instCommMonoid
    (M := Submonoid.closure (Set.range (pderivₗ (K := K) (m := m))))
  let a : Fin m → Submonoid.closure (Set.range (pderivₗ (K := K) (m := m))) := fun μ =>
    ⟨pderivₗ μ, Submonoid.subset_closure ⟨μ, rfl⟩⟩
  have key (I : Fin m →₀ ℕ) : iterPDeriv I = ((∏ μ, a μ ^ I μ : _) : Module.End K _) := by
    rw [← List.prod_ofFn, Submonoid.coe_list_prod, List.map_ofFn]
    rfl
  rw [key, key, key, ← Submonoid.coe_mul, ← Finset.prod_mul_distrib]
  simp only [Finsupp.add_apply, pow_add]

/-- Scaled iterated derivatives compose: `a ∂^J (b ∂^I Q) = (a b) ∂^{J + I} Q`. -/
private lemma smul_iterPDeriv_smul_iterPDeriv (a b : K) (I J : Fin m →₀ ℕ)
    (Q : MvPolynomial (Fin m) K) :
    a • iterPDeriv J (b • iterPDeriv I Q) = (a * b) • iterPDeriv (J + I) Q := by
  rw [LinearMap.map_smul, smul_smul, ← Module.End.mul_apply, iterPDeriv_mul]

/-- The factorial scaling `(i₁! ⋯ iₘ!)⁻¹` of the divided derivative is nonzero. -/
private lemma inv_prod_factorial_ne_zero [CharZero K] (I : Fin m →₀ ℕ) :
    (∏ μ, ((I μ).factorial : K))⁻¹ ≠ 0 :=
  inv_ne_zero <| Finset.prod_ne_zero_iff.mpr fun _ _ => mod_cast Nat.factorial_ne_zero _

end

open scoped ENNReal in
/-- Taking the divided derivative `∂_I` lowers the index by at most the weight of `I`:
`ind(Q) ≤ ind(∂_I Q) + ∑ μ, i_μ / r_μ`, i.e. `ind(∂_I Q) ≥ ind(Q) - i₁/r₁ - ⋯ - iₘ/rₘ`. -/
@[faltings "lem_bvr_index_properties"]
public theorem index_le_index_hasseDeriv_add {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (r : Fin m → ℕ+) (ς₀ : Fin m → K) (Q : MvPolynomial (Fin m) K) (I : Fin m →₀ ℕ) :
    index r ς₀ Q ≤
      index r ς₀
          ((∏ μ, ((I μ).factorial : K))⁻¹ •
            (List.ofFn fun μ : Fin m =>
              ((MvPolynomial.pderiv μ : Derivation K (MvPolynomial (Fin m) K)
                (MvPolynomial (Fin m) K)) : MvPolynomial (Fin m) K →ₗ[K] MvPolynomial (Fin m) K)
                ^ I μ).prod Q) +
        ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) := by
  rw [← tsub_le_iff_right, index, index]
  refine le_iInf₂ fun J hJ => tsub_le_iff_right.mpr <| (iInf₂_le (J + I) ?_).trans_eq ?_
  · rw [smul_iterPDeriv_smul_iterPDeriv, smul_eval] at hJ
    rw [smul_eval]
    exact mul_ne_zero (inv_prod_factorial_ne_zero _) (right_ne_zero_of_mul hJ)
  · simp only [Finsupp.add_apply, Nat.cast_add, ENNReal.add_div, Finset.sum_add_distrib]

end Faltings.MvPolynomial
