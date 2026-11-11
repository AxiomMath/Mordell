module
public import Mordell.Algebra.CentralBinom
public import Mordell.Analysis.MahlerMeasure.LowerBound
public import Mordell.Analysis.MahlerMeasure.Mul
public import Mordell.Analysis.MahlerMeasure.UpperBound

/-!
# Gelfond's inequality

Let `f_1, …, f_k ∈ ℂ[t_1, …, t_n]` be nonzero, `f = f_1 ⋯ f_k`, and let
`d = ∑_μ deg_{t_μ} f` be the sum of the partial degrees of `f`. Gelfond's inequality bounds the
product of the `ℓ^∞`-norms of the factors by that of the product:
`2^{-d} ∏_j ℓ^∞(f_j) ≤ ℓ^∞(f)`. The proof compares both sides with the Mahler measure, which is
multiplicative, and bounds the central binomial coefficients that appear by powers of `2`.

## Main results

* `Faltings.MvPolynomial.inv_two_pow_mul_prod_supNorm_le_supNorm_prod`: for nonzero
  `f_j ∈ ℂ[t_σ]`, `j ∈ s`, `2^{-d} ∏_{j ∈ s} ℓ^∞(f_j) ≤ ℓ^∞(∏_{j ∈ s} f_j)`, where
  `d = ∑_μ deg_{t_μ} (∏_{j ∈ s} f_j)`.

## Implementation notes

The factors are indexed by a `Finset` of an arbitrary type and the variables by an arbitrary
finite type `σ`; the source's case is `s = {1, …, k}` and `σ = Fin n`. The partial degree
`deg_{t_μ}` is `MvPolynomial.degreeOf μ`, and `ℓ^∞` is `Faltings.MvPolynomial.supNorm`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022], Lemma 1.3.6.
-/

namespace Faltings

namespace MvPolynomial

/-- Supermultiplicativity of the central binomial coefficients over a finite family. -/
private theorem prod_choose_div_two_le {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    ∏ j ∈ s, (d j).choose (d j / 2) ≤ (∑ j ∈ s, d j).choose ((∑ j ∈ s, d j) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Nat.mul_le_mul_left _ ih).trans (choose_div_two_mul_choose_div_two_le _ _)

/-- With no variables, `ℓ^∞(g)` is the absolute value of the constant term. -/
private theorem supNorm_eq_norm_constantCoeff {σ : Type*} [IsEmpty σ]
    (g : _root_.MvPolynomial σ ℂ) :
    supNorm g = ‖_root_.MvPolynomial.constantCoeff g‖ := by
  refine le_antisymm ((supNorm_le_iff (norm_nonneg _)).2 fun I => ?_) ?_
  · rw [Subsingleton.elim I 0, _root_.MvPolynomial.constantCoeff_eq]
  · rw [_root_.MvPolynomial.constantCoeff_eq]
    exact norm_coeff_le_supNorm g 0

/-- The central binomial factors of a family of partial degrees, together with the
`(D + 1)^{1/2}` factor of their sum `D`, are bounded by `2^D`. -/
private theorem prod_choose_div_two_mul_sqrt_le_two_pow {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) :
    (∏ j ∈ s, ((d j).choose (d j / 2) : ℝ)) * √((∑ j ∈ s, d j : ℕ) + 1 : ℝ) ≤
      2 ^ ∑ j ∈ s, d j :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast prod_choose_div_two_le s d)
    (Real.sqrt_nonneg _)).trans (choose_div_two_mul_sqrt_succ_le_two_pow _)

/-- Gelfond's inequality in the form `∏_j ℓ^∞(f_j) ≤ 2^{∑_μ D_μ} ℓ^∞(∏_j f_j)`, for at least
one variable. -/
private theorem prod_supNorm_le_two_pow_mul_supNorm {σ ι : Type*} [Fintype σ] [Nonempty σ]
    (s : Finset ι) (f : ι → _root_.MvPolynomial σ ℂ) (hf : ∀ j ∈ s, f j ≠ 0) :
    ∏ j ∈ s, supNorm (f j) ≤
      (2 : ℝ) ^ (∑ μ : σ, (∏ j ∈ s, f j).degreeOf μ) * supNorm (∏ j ∈ s, f j) := by
  have hD (μ : σ) := _root_.MvPolynomial.degreeOf_prod_eq (n := μ) s f hf
  set F := ∏ j ∈ s, f j
  set c : σ → ι → ℝ := fun μ j => ((f j).degreeOf μ).choose ((f j).degreeOf μ / 2)
  calc ∏ j ∈ s, supNorm (f j)
      ≤ ∏ j ∈ s, ((∏ μ, c μ j) * mahlerMeasure (f j)) :=
        Finset.prod_le_prod₀ (fun j _ => supNorm_nonneg _) fun j hj =>
          supNorm_le_prod_choose_degreeOf_div_two_mul_mahlerMeasure (hf j hj)
    _ = (∏ μ, ∏ j ∈ s, c μ j) * mahlerMeasure F := by
        rw [Finset.prod_mul_distrib, Finset.prod_comm, mahlerMeasure_prod s f hf]
    _ ≤ (∏ μ, ∏ j ∈ s, c μ j) * ((∏ μ, √((F.degreeOf μ : ℝ) + 1)) * supNorm F) := by
        gcongr
        exact mahlerMeasure_le_prod_sqrt_degreeOf_add_one_mul_supNorm
          (Finset.prod_ne_zero_iff.2 hf)
    _ = (∏ μ, ((∏ j ∈ s, c μ j) * √((F.degreeOf μ : ℝ) + 1))) * supNorm F := by
        rw [Finset.prod_mul_distrib, mul_assoc]
    _ ≤ (∏ μ, (2 : ℝ) ^ F.degreeOf μ) * supNorm F := by
        gcongr with μ
        · exact supNorm_nonneg _
        · simpa only [hD] using prod_choose_div_two_mul_sqrt_le_two_pow s fun j => (f j).degreeOf μ
    _ = 2 ^ (∑ μ, F.degreeOf μ) * supNorm F := by rw [Finset.prod_pow_eq_pow_sum]

/-- **Gelfond's inequality.** For nonzero complex polynomials `f_j`, `j ∈ s`, in finitely many
variables, with `d = ∑_μ deg_{t_μ} (∏_{j ∈ s} f_j)`,
`2^{-d} ∏_{j ∈ s} ℓ^∞(f_j) ≤ ℓ^∞(∏_{j ∈ s} f_j)`, where `ℓ^∞` is
`Faltings.MvPolynomial.supNorm`. -/
@[faltings "lem_ht_gelfond_archimedean"]
public theorem inv_two_pow_mul_prod_supNorm_le_supNorm_prod {σ ι : Type*} [Fintype σ]
    (s : Finset ι) (f : ι → _root_.MvPolynomial σ ℂ) (hf : ∀ j ∈ s, f j ≠ 0) :
    (2⁻¹ : ℝ) ^ (∑ μ : σ, (∏ j ∈ s, f j).degreeOf μ) * ∏ j ∈ s, supNorm (f j) ≤
      supNorm (∏ j ∈ s, f j) := by
  rcases isEmpty_or_nonempty σ with _ | _
  · simp [supNorm_eq_norm_constantCoeff, map_prod]
  rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
  exact prod_supNorm_le_two_pow_mul_supNorm s f hf

end MvPolynomial

end Faltings
