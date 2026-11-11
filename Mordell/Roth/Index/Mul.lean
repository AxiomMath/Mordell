module
public import Mordell.Roth.Index.Basic
public import Mordell.Polynomial.Taylor

/-!
# The index of a product

The index `Faltings.MvPolynomial.index r ς₀` with respect to fixed weights `r` and a fixed
point `ς₀` is additive on products: `ind(Q₁ Q₂) = ind(Q₁) + ind(Q₂)`. The identity holds in
`ℝ≥0∞`, including when a factor is `0` (both sides are then `⊤`).

## Main results

* `Faltings.MvPolynomial.index_mul`: `index r ς₀ (Q₁ * Q₂) = index r ς₀ Q₁ + index r ς₀ Q₂`.
* `Faltings.MvPolynomial.index_prod`: the index of a finite product is the sum of the indices.
* `Faltings.MvPolynomial.index_zero`, `Faltings.MvPolynomial.index_one`: `index 0 = ⊤` and
  `index 1 = 0`.
* `Faltings.MvPolynomial.index_le_index_intCast_mul`: multiplying by an integer constant does
  not lower the index.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 634][bombieri1990]
-/

namespace Faltings.MvPolynomial

open scoped ENNReal

/-- The index read off the coefficients of the translate `Q(ς₀ + τ)`. -/
private lemma index_eq_iInf_coeff {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (r : Fin m → ℕ+) (ς₀ : Fin m → K) (Q : MvPolynomial (Fin m) K) :
    index r ς₀ Q = ⨅ (I : Fin m →₀ ℕ)
      (_ : (MvPolynomial.aeval
        (fun μ => MvPolynomial.C (ς₀ μ) + MvPolynomial.X μ) Q).coeff I ≠ 0),
      ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) := by
  unfold index
  congr! 3 with I
  rw [coeff_aeval_C_add_X, MvPolynomial.smul_eval]

/-- With `L = ∏ μ, r μ` and integer weights `w μ = L / r μ`, the weight `∑ μ, I μ / r μ`
is `weight w I / L`. -/
private lemma sum_div_eq_weight_div {m : ℕ} (r : Fin m → ℕ+) (I : Fin m →₀ ℕ) :
    ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) =
      ((Finsupp.weight (fun μ => (∏ ν, (r ν : ℕ)) / r μ) I : ℕ) : ℝ≥0∞) /
        ((∏ ν, (r ν : ℕ) : ℕ) : ℝ≥0∞) := by
  set L : ℕ := ∏ ν, (r ν : ℕ)
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ν _ => (r ν).ne_zero
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Nat.cast_sum,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hdvd : (r μ : ℕ) ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_univ μ)
  have hw : ((r μ : ℕ) : ℝ≥0∞) * ((L / r μ : ℕ) : ℝ≥0∞) = (L : ℝ≥0∞) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hw0 : L / r μ ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hdvd) (r μ).pos).ne'
  rw [← hw, smul_eq_mul, Nat.cast_mul, ← div_eq_mul_inv,
    ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hw0) (ENNReal.natCast_ne_top _)]

/-- The index is `weightedOrder w (Q(ς₀ + τ)) / L`. -/
private lemma index_eq_weightedOrder {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (r : Fin m → ℕ+) (ς₀ : Fin m → K) (Q : MvPolynomial (Fin m) K) :
    index r ς₀ Q = ((MvPowerSeries.weightedOrder (fun μ => (∏ ν, (r ν : ℕ)) / r μ)
      ((MvPolynomial.aeval (fun μ => MvPolynomial.C (ς₀ μ) + MvPolynomial.X μ) Q :
        MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) : ℕ∞) : ℝ≥0∞) /
      ((∏ ν, (r ν : ℕ) : ℕ) : ℝ≥0∞) := by
  set w : Fin m → ℕ := fun μ => (∏ ν, (r ν : ℕ)) / r μ
  set P := MvPolynomial.aeval (fun μ => MvPolynomial.C (ς₀ μ) + MvPolynomial.X μ) Q
  rw [index_eq_iInf_coeff]
  refine le_antisymm ?_ (le_iInf₂ fun I hI => ?_)
  · by_cases htop : MvPowerSeries.weightedOrder w (P : MvPowerSeries (Fin m) K) = ⊤
    · rw [htop, ENat.toENNReal_top, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)]
      exact le_top
    · obtain ⟨d, hd, hdw⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder w
        (f := (P : MvPowerSeries (Fin m) K)) (ENat.natCast_toNat htop)
      rw [MvPolynomial.coeff_coe] at hd
      refine (iInf₂_le d hd).trans_eq ?_
      rw [sum_div_eq_weight_div, ← hdw]
      rfl
  · rw [sum_div_eq_weight_div]
    exact ENNReal.div_le_div_right (ENat.toENNReal_le.mpr
      (MvPowerSeries.weightedOrder_le w (f := (P : MvPowerSeries (Fin m) K))
        (by rwa [MvPolynomial.coeff_coe]))) _

/-- The index is additive on products: for fixed weights `r` and point `ς₀`,
`index r ς₀ (Q₁ * Q₂) = index r ς₀ Q₁ + index r ς₀ Q₂`. -/
@[faltings "lem_bvr_index_product"]
public theorem index_mul {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+)
    (ς₀ : Fin m → K) (Q₁ Q₂ : MvPolynomial (Fin m) K) :
    index r ς₀ (Q₁ * Q₂) = index r ς₀ Q₁ + index r ς₀ Q₂ := by
  rw [index_eq_weightedOrder, index_eq_weightedOrder, index_eq_weightedOrder, map_mul,
    MvPolynomial.coe_mul, MvPowerSeries.weightedOrder_mul, ENat.toENNReal_add, ENNReal.add_div]

section

variable {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+) (ς₀ : Fin m → K)

/-- The zero polynomial has index `⊤`. -/
public lemma index_zero : index r ς₀ (0 : MvPolynomial (Fin m) K) = ⊤ := by
  simp [index]

/-- The constant polynomial `1` has index `0`. -/
public lemma index_one : index r ς₀ (1 : MvPolynomial (Fin m) K) = 0 := by
  refine le_antisymm ((iInf₂_le (0 : Fin m →₀ ℕ) ?_).trans_eq (by simp)) bot_le
  simp

/-- The index of a finite product is the sum of the indices of the factors. -/
public lemma index_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin m) K) :
    index r ς₀ (∏ i ∈ s, f i) = ∑ i ∈ s, index r ς₀ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [index_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, index_mul, ih]

/-- Multiplying by an integer constant does not lower the index. -/
public lemma index_le_index_intCast_mul (n : ℤ) (Q : MvPolynomial (Fin m) K) :
    index r ς₀ Q ≤ index r ς₀ ((n : MvPolynomial (Fin m) K) * Q) := by
  rw [index_mul]
  exact le_add_self

end

end Faltings.MvPolynomial
