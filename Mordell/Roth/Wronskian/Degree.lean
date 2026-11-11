module
public import Mordell.Roth.Wronskian.Basic

/-!
# Degree of a generalized Wronskian

Let `K` be a field of characteristic `0` and `f₀, …, fₛ ∈ K[ς₁, …, ςₗ]`. If every `f_j` has
degree at most `r` in the variable `ς_μ`, then so does every divided derivative `∂_I f_j`, and
each term of the expansion of the `(s + 1) × (s + 1)` determinant
`Wr_{I₀,…,Iₛ}(f₀, …, fₛ) = det (∂_{I_ν} f_j)` is a product of `s + 1` such entries; hence the
generalized Wronskian has degree at most `(s + 1) r` in `ς_μ`.

## Main results

* `Faltings.degreeOf_generalizedWronskian_le`:
  `degreeOf μ (generalizedWronskian I f) ≤ (s + 1) * r` whenever `degreeOf μ (f j) ≤ r` for all
  `j`.

## Implementation notes

A partial derivative does not raise the degree in any variable; the endomorphisms of
`K[ς₁, …, ςₗ]` with this property form a submonoid, so neither does a divided derivative. A
determinant whose entries have degree at most `r` in `ς_μ` has degree at most `n r`, since each
term of its Leibniz expansion is a signed product of `n` entries.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9, p. 635.
-/

open MvPolynomial

namespace Faltings

section Helpers

variable {K : Type*} [Field K] {l : ℕ}

/-- A partial derivative does not raise the degree in any variable. -/
private lemma degreeOf_pderiv_le (μ k : Fin l) (p : MvPolynomial (Fin l) K) :
    degreeOf μ (pderiv k p) ≤ degreeOf μ p := by
  rw [degreeOf_le_iff]
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  calc m μ ≤ (m + Finsupp.single k 1 : Fin l →₀ ℕ) μ := by simp
    _ ≤ degreeOf μ p := monomial_le_degreeOf μ (mem_support_iff.2 (left_ne_zero_of_mul hm))

/-- The endomorphisms of `K[ς]` that do not raise the degree in `ς_μ`. -/
private def degreeOfNonincreasing (μ : Fin l) :
    Submonoid (Module.End K (MvPolynomial (Fin l) K)) where
  carrier := {E | ∀ p, degreeOf μ (E p) ≤ degreeOf μ p}
  one_mem' _ := le_rfl
  mul_mem' hE hF p := (hE _).trans (hF p)

/-- A divided derivative does not raise the degree in any variable. -/
private lemma degreeOf_dividedDeriv_le (μ : Fin l) (I : Fin l → ℕ) (p : MvPolynomial (Fin l) K) :
    degreeOf μ ((∏ k, ((I k).factorial : K))⁻¹ •
      (List.ofFn fun k : Fin l => (pderiv k).toLinearMap ^ I k).prod p) ≤ degreeOf μ p := by
  rw [smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans <|
    (degreeOfNonincreasing μ).list_prod_mem (l := List.ofFn _) (fun E hE => ?_) p
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hE
  exact pow_mem (show _ ∈ degreeOfNonincreasing μ from degreeOf_pderiv_le μ k) _

/-- A determinant whose entries have degree at most `r` in `ς_μ` has degree at most `n r`. -/
private lemma degreeOf_det_le {n : Type*} [Fintype n] [DecidableEq n] (μ : Fin l)
    (M : Matrix n n (MvPolynomial (Fin l) K)) {r : ℕ} (hM : ∀ i j, degreeOf μ (M i j) ≤ r) :
    degreeOf μ M.det ≤ Fintype.card n * r := by
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ _ => (degreeOf_mul_le _ _ _).trans ?_)
  rw [← map_intCast (C : K →+* MvPolynomial (Fin l) K), degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hM (σ i) i

end Helpers

/-- If each of `f₀, …, fₛ ∈ K[ς₁, …, ςₗ]` has degree at most `r` in the variable `ς_μ`, then the
generalized Wronskian `Wr_{I₀,…,Iₛ}(f₀, …, fₛ)` has degree at most `(s + 1) r` in `ς_μ`. -/
@[faltings "lem_bvr_wronskian_degree"]
public theorem degreeOf_generalizedWronskian_le {K : Type*} [Field K] [CharZero K] {l s : ℕ}
    (I : Fin (s + 1) → Fin l → ℕ) (f : Fin (s + 1) → MvPolynomial (Fin l) K) (μ : Fin l)
    {r : ℕ} (hf : ∀ j, degreeOf μ (f j) ≤ r) :
    degreeOf μ (generalizedWronskian I f) ≤ (s + 1) * r := by
  rw [generalizedWronskian]
  exact (degreeOf_det_le μ (Matrix.of _) fun ν j =>
    (degreeOf_dividedDeriv_le μ (I ν) (f j)).trans (hf j)).trans_eq (by simp)

end Faltings
