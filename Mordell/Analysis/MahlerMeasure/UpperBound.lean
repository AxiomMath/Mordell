module
public import Mordell.Analysis.MahlerMeasure.Basic
public import Mordell.Polynomial.CoeffNorm

/-!
# An upper bound for the Mahler measure in several variables

For a nonzero polynomial `f ∈ ℂ[t_i : i ∈ σ]` in finitely many variables with partial degrees
`d_i = deg_{t_i} f`, the Mahler measure is bounded by the `ℓ^∞`-norm:
`M(f) ≤ ∏_i (d_i + 1)^{1/2} ℓ^∞(f)`. By Jensen's inequality and Parseval, `M(f)` is at most the
`ℓ²`-norm of the coefficients, and `f` has at most `∏_i (d_i + 1)` monomials.

## Main results

* `Faltings.MvPolynomial.mahlerMeasure_le_prod_sqrt_degreeOf_add_one_mul_supNorm`:
  `M(f) ≤ (∏ i, √(deg_{t_i} f + 1)) * ℓ^∞(f)`.

## Implementation notes

The variables are indexed by an arbitrary finite type `σ` rather than by `{1, …, n}`, and the
partial degree in `t_i` is `MvPolynomial.degreeOf i f`. This is the several-variable analogue of
`Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`.

## References

* [Z. Gao, *Heights*][gao2022], Lemma 1.3.10(c) and Lemma 1.3.11.
* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006], 1.6.6.
-/

namespace Faltings

open Real MeasureTheory Faltings.MahlerMeasure

private lemma ν_univ : ν Set.univ = 1 := by simp [ν]

private lemma restrict_cube {σ : Type*} [Fintype σ] :
    volume.restrict (Set.univ.pi fun _ : σ ↦ Set.Icc (0 : ℝ) 1) = Measure.pi fun _ : σ ↦ ν := by
  rw [volume_pi, Measure.restrict_pi_pi]

/-- Orthonormality on the circle: `∫_0^1 e(t)^a conj(e(t))^b dt = δ_{ab}`. -/
private lemma integral_e_pow_mul_conj_pow (a b : ℕ) :
    ∫ t, e t ^ a * (starRingEnd ℂ) (e t) ^ b ∂ν = if a = b then 1 else 0 := by
  set c : ℂ := (((a : ℤ) - b : ℤ) : ℂ) * (2 * π * Complex.I) with hc
  have hpt : ∀ t : ℝ, e t ^ a * (starRingEnd ℂ) (e t) ^ b = Complex.exp (c * t) := by
    intro t
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [hc, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast; ring
  simp_rw [hpt]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hab
  · subst hab; simp [hc]
  · have hc0 : c ≠ 0 := by
      simp [hc, pi_ne_zero, sub_eq_zero, hab]
    rw [integral_exp_mul_complex hc0]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [hc, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- Parseval on the torus. -/
private lemma integral_norm_sq {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) :
    ∫ θ, ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ^ 2 ∂(Measure.pi fun _ : σ ↦ ν) =
      ∑ I ∈ f.support, ‖f.coeff I‖ ^ 2 := by
  classical
  haveI : IsProbabilityMeasure ν := ⟨ν_univ⟩
  set P : (σ →₀ ℕ) → (σ →₀ ℕ) → (σ → ℝ) → ℂ := fun I J θ ↦
    ∏ i, (e (θ i) ^ I i * (starRingEnd ℂ) (e (θ i)) ^ J i) with hP
  have hnorm : ∀ t : ℝ, ‖e t‖ = 1 := fun t ↦ by simp [e, Complex.norm_exp]
  have hPint : ∀ I J, Integrable (P I J) (Measure.pi fun _ : σ ↦ ν) := by
    intro I J
    refine Integrable.mono' (integrable_const 1) (Continuous.aestronglyMeasurable ?_)
      (.of_forall fun θ ↦ ?_)
    · exact continuous_finset_prod _ fun i _ ↦ by fun_prop
    · simp [hP, norm_prod, hnorm]
  have hPI : ∀ I J, ∫ θ, P I J θ ∂(Measure.pi fun _ : σ ↦ ν) = if I = J then 1 else 0 := by
    intro I J
    rw [hP, integral_fintype_prod_eq_prod (fun i t ↦ e t ^ I i * (starRingEnd ℂ) (e t) ^ J i)]
    simp_rw [integral_e_pow_mul_conj_pow]
    rw [Finset.prod_boole]
    congr 1
    simp [Finsupp.ext_iff]
  have hexp : ∀ θ : σ → ℝ, ((‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ^ 2 : ℝ) : ℂ) =
      ∑ I ∈ f.support, ∑ J ∈ f.support,
        f.coeff I * (starRingEnd ℂ) (f.coeff J) * P I J θ := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', MvPolynomial.eval_eq', map_sum,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun I _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_
    simp only [hP, map_mul, map_prod, map_pow, Finset.prod_mul_distrib]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hexp]
  rw [integral_finset_sum _ fun I _ ↦ integrable_finset_sum _ fun J _ ↦
    (hPint I J).const_mul _]
  push_cast
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [integral_finset_sum _ fun J _ ↦ (hPint I J).const_mul _]
  simp_rw [integral_const_mul, hPI, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hI, Complex.mul_conj']

/-- Counting monomials. -/
private lemma card_support_le {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) :
    (f.support.card : ℝ) ≤ ∏ i, ((f.degreeOf i : ℝ) + 1) := by
  classical
  have h : f.support.card ≤ (Fintype.piFinset fun i ↦ Finset.range (f.degreeOf i + 1)).card :=
    Finset.card_le_card_of_injOn (fun I : σ →₀ ℕ ↦ (I : σ → ℕ))
      (fun I hI ↦ Fintype.mem_piFinset.2 fun i ↦
        Finset.mem_range.2 (Nat.lt_succ_of_le (MvPolynomial.monomial_le_degreeOf i hI)))
      (DFunLike.coe_injective.injOn)
  rw [Fintype.card_piFinset] at h
  simp only [Finset.card_range] at h
  exact_mod_cast h

/-- On the torus, `‖f(z)‖` is bounded by the sum of the norms of the coefficients of `f`. -/
private lemma norm_eval_e_le {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) (θ : σ → ℝ) :
    ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ≤ ∑ m ∈ f.support, ‖f.coeff m‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [norm_mul, norm_prod]
  simp [e, Complex.norm_exp]

/-- Jensen's inequality for the concave `log`, in the form `log x ≤ x - 1`: on a probability
space, `∫ log ‖F‖ ≤ ½ log ∫ ‖F‖²` for `F` nonzero almost everywhere. -/
private lemma integral_log_norm_le_half_log_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {F : α → ℂ} (h0 : ∀ᵐ x ∂μ, F x ≠ 0)
    (hlog : Integrable (fun x ↦ log ‖F x‖) μ) (hsq : Integrable (fun x ↦ ‖F x‖ ^ 2) μ) :
    ∫ x, log ‖F x‖ ∂μ ≤ log (∫ x, ‖F x‖ ^ 2 ∂μ) / 2 := by
  set A := ∫ x, ‖F x‖ ^ 2 ∂μ
  have hA : 0 < A := by
    refine (integral_pos_iff_support_of_nonneg (fun x ↦ by positivity) hsq).2 ?_
    rw [pos_iff_ne_zero, Ne, Measure.measure_support_eq_zero_iff μ]
    intro h
    obtain ⟨x, hx, hx'⟩ := (h0.and h).exists
    simp_all
  have hpt : ∀ᵐ x ∂μ, 2 * log ‖F x‖ - log A ≤ ‖F x‖ ^ 2 / A - 1 := by
    filter_upwards [h0] with x hx
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < ‖F x‖ ^ 2 / A)
    rwa [Real.log_div (by positivity) hA.ne', Real.log_pow] at this
  have : ∫ x, (2 * log ‖F x‖ - log A) ∂μ ≤ ∫ x, (‖F x‖ ^ 2 / A - 1) ∂μ :=
    integral_mono_ae ((hlog.const_mul 2).sub (integrable_const _))
      ((hsq.div_const A).sub (integrable_const _)) hpt
  rw [integral_sub (hlog.const_mul 2) (integrable_const _),
    integral_sub (hsq.div_const A) (integrable_const _), integral_const_mul, integral_div,
    div_self hA.ne'] at this
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
  linarith

/-- Jensen and Parseval: the Mahler measure is at most the `ℓ²`-norm, `M(f) ≤ ℓ²(f)`. -/
private lemma mahlerMeasure_le_l2Norm {σ : Type*} [Fintype σ] {f : MvPolynomial σ ℂ}
    (hf : f ≠ 0) : Faltings.MvPolynomial.mahlerMeasure f ≤ Faltings.l2Norm f := by
  haveI : IsProbabilityMeasure ν := ⟨ν_univ⟩
  have hlog := Faltings.integrableOn_log_norm_eval_exp_mvPolynomial hf
  rw [IntegrableOn, show volume.restrict (Set.Icc (0 : σ → ℝ) 1) = Measure.pi fun _ ↦ ν by
    rw [← Set.pi_univ_Icc]; exact restrict_cube] at hlog
  have hsq : Integrable (fun θ ↦ ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ^ 2)
      (Measure.pi fun _ : σ ↦ ν) :=
    .mono' (integrable_const ((∑ m ∈ f.support, ‖f.coeff m‖) ^ 2))
      ((measurable_eval_exp_mvPolynomial f).norm.pow_const 2).aestronglyMeasurable
      (.of_forall fun θ ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_e_le f θ) 2)
  have hJ := integral_log_norm_le_half_log_integral_sq
    (by rw [← restrict_cube]; exact ae_restrict_of_ae (ae_eval_exp_ne_zero_mvPolynomial hf))
    hlog hsq
  rw [integral_norm_sq, ← Faltings.sq_l2Norm, Real.log_pow] at hJ
  have hl : 0 < Faltings.l2Norm f := Real.sqrt_pos.2 <| Finset.sum_pos
    (fun I hI ↦ by have := MvPolynomial.mem_support_iff.1 hI; positivity)
    (MvPolynomial.support_nonempty.2 hf)
  rw [Faltings.MvPolynomial.mahlerMeasure_of_ne_zero hf, restrict_cube, ← Real.exp_log hl]
  exact Real.exp_le_exp.2 (by push_cast at hJ; linarith)

/-- Counting monomials: `ℓ²(f) ≤ ∏_i (d_i + 1)^{1/2} ℓ^∞(f)`. -/
private lemma l2Norm_le_prod_sqrt_mul_supNorm {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) :
    Faltings.l2Norm f ≤
      (∏ i, √((f.degreeOf i : ℝ) + 1)) * Faltings.MvPolynomial.supNorm f := by
  have hs := Faltings.MvPolynomial.supNorm_nonneg f
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, ← Finset.prod_pow,
    Finset.prod_congr rfl fun i _ ↦ Real.sq_sqrt (by positivity)]
  calc ∑ I ∈ f.support, ‖f.coeff I‖ ^ 2
      ≤ ∑ _I ∈ f.support, Faltings.MvPolynomial.supNorm f ^ 2 :=
        Finset.sum_le_sum fun I _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (Faltings.MvPolynomial.norm_coeff_le_supNorm f I) 2
    _ = f.support.card * Faltings.MvPolynomial.supNorm f ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr; exact card_support_le f

namespace MvPolynomial

/-- The Mahler measure of a nonzero polynomial `f` in several variables over `ℂ` is at most
`∏ i, √(deg_{t_i} f + 1)` times its `ℓ^∞`-norm. -/
@[faltings "lem_ht_mahler_upper_bound"]
public theorem mahlerMeasure_le_prod_sqrt_degreeOf_add_one_mul_supNorm {σ : Type*} [Fintype σ]
    {f : _root_.MvPolynomial σ ℂ} (hf : f ≠ 0) :
    mahlerMeasure f ≤ (∏ i, √((f.degreeOf i : ℝ) + 1)) * supNorm f :=
  (mahlerMeasure_le_l2Norm hf).trans (l2Norm_le_prod_sqrt_mul_supNorm f)

end MvPolynomial

end Faltings
