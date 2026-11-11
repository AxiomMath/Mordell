module
public import Mordell.Analysis.MahlerMeasure.Basic
public import Mordell.Polynomial.CoeffNorm

/-!
# A lower bound for the Mahler measure in terms of the coefficients

For a nonzero polynomial `f ∈ ℂ[t_i : i ∈ σ]` with partial degrees `d_i = deg_{t_i} f`,
the largest coefficient is controlled by the Mahler measure:
`ℓ^∞(f) ≤ ∏_i binom(d_i, ⌊d_i/2⌋) · M(f)`, equivalently
`∏_i binom(d_i, ⌊d_i/2⌋)⁻¹ · ℓ^∞(f) ≤ M(f)`.

The proof is by induction on the number of variables. Writing `f = ∑_j f_j t_0^j`, Fubini's
theorem expresses `log M(f)` as the integral over the remaining variables `θ'` of the logarithmic
Mahler measure of the one-variable slice `f(·, e^{2πiθ'})`. The one-variable coefficient bound
`Polynomial.norm_coeff_le_choose_mul_mahlerMeasure` then gives
`log M(f_j) ≤ log binom(d_0, ⌊d_0/2⌋) + log M(f)` for every `f_j ≠ 0`, and the induction
hypothesis applied to the `f_j` concludes, as `ℓ^∞(f) = max_j ℓ^∞(f_j)`.

## Main results

* `Faltings.MvPolynomial.supNorm_le_prod_choose_degreeOf_div_two_mul_mahlerMeasure`: the bound
  above; the several-variable analogue of
  `Polynomial.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure`.

## Implementation notes

The variables are indexed by a finite type `σ` rather than `{1, …, n}`. The bound is stated
multiplicatively, `ℓ^∞(f) ≤ (∏ binomials) · M(f)`, which is equivalent to the source's form
because the central binomial coefficients are positive.

The induction runs over `Fin n`, with the product of the uniform measures on `[0,1]`. Since
`Real.log 0 = 0`, comparing `log ‖f_j‖` with the slice Mahler measures needs that a nonzero
polynomial vanishes only on a null subset of the torus, which is
`Faltings.ae_eval_exp_ne_zero_mvPolynomial`.

## References

* [Z. Gao, *Heights*][gao2022], Lemma 1.3.10.
* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006], 1.6.7.
-/

namespace Faltings

namespace MvPolynomial

open Real MeasureTheory Faltings.MahlerMeasure

/-- `ν` is a probability measure. -/
local instance : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩

/-- The integral of `log ‖q(e x)‖` over `[0,1]` is the logarithmic Mahler measure of `q`. -/
private lemma integral_log_norm_eval_e (q : Polynomial ℂ) :
    ∫ x, log ‖q.eval (e x)‖ ∂ν = q.logMahlerMeasure := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    Polynomial.logMahlerMeasure_def, circleAverage_def, smul_eq_mul]
  simp_rw [e_eq_circleMap]
  rw [intervalIntegral.integral_comp_mul_left (fun x ↦ log ‖q.eval (circleMap 0 1 x)‖)
    (by positivity)]
  simp

/-- The splitting `θ ↦ (θ 0, θ ∘ succ)` of `[0,1]^(n+1)` as `[0,1] × [0,1]^n`. -/
private lemma measurePreserving_piFinSuccAbove_ν (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
      (Measure.pi fun _ ↦ ν) (ν.prod (Measure.pi fun _ : Fin n ↦ ν)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ν) 0

/-- `log ‖f‖` is integrable on `[0,1]^n`: `integrableOn_log_norm_eval_exp_mvPolynomial` for the
measure `ν^n`. -/
private lemma integrable_log_norm_eval_e {n : ℕ} {f : _root_.MvPolynomial (Fin n) ℂ}
    (hf : f ≠ 0) :
    Integrable (fun θ : Fin n → ℝ ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖)
      (Measure.pi fun _ ↦ ν) := by
  have hmeas : volume.restrict (Set.Icc (0 : Fin n → ℝ) 1) = Measure.pi fun _ ↦ ν := by
    rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]; rfl
  rw [← hmeas]
  exact integrableOn_log_norm_eval_exp_mvPolynomial hf

/-- Fubini in the first variable: `∫ log ‖f(e θ)‖` is the integral over the remaining variables
`y` of the logarithmic Mahler measure of the slice `f(·, e y)`, which is integrable. -/
private lemma slice_integral {n : ℕ} {f : _root_.MvPolynomial (Fin (n + 1)) ℂ} (hf : f ≠ 0) :
    Integrable (fun y : Fin n → ℝ ↦ ((MvPolynomial.finSuccEquiv ℂ n f).map
        (MvPolynomial.eval fun j ↦ e (y j))).logMahlerMeasure) (Measure.pi fun _ ↦ ν) ∧
    ∫ θ, log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ∂(Measure.pi fun _ ↦ ν) =
      ∫ y : Fin n → ℝ, ((MvPolynomial.finSuccEquiv ℂ n f).map
        (MvPolynomial.eval fun j ↦ e (y j))).logMahlerMeasure ∂(Measure.pi fun _ ↦ ν) := by
  set g := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove_ν n
  set p := MvPolynomial.finSuccEquiv ℂ n f
  set F : ℝ × (Fin n → ℝ) → ℝ :=
    fun z ↦ log ‖(p.map (MvPolynomial.eval fun j ↦ e (z.2 j))).eval (e z.1)‖
  have hfun : (fun θ : Fin (n + 1) → ℝ ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖) = F ∘ g :=
    funext fun θ ↦ by simp only [Function.comp_apply, F, eval_e_eq_eval_slice f θ]; rfl
  have hF : Integrable F (ν.prod (Measure.pi fun _ : Fin n ↦ ν)) := by
    have hint := integrable_log_norm_eval_e hf
    rwa [hfun, hmp.integrable_comp_emb g.measurableEmbedding] at hint
  have hinner : ∀ y : Fin n → ℝ, ∫ x, F (x, y) ∂ν =
      (p.map (MvPolynomial.eval fun j ↦ e (y j))).logMahlerMeasure :=
    fun y ↦ integral_log_norm_eval_e (p.map (MvPolynomial.eval fun j ↦ e (y j)))
  refine ⟨by simpa only [hinner] using hF.integral_prod_right, ?_⟩
  rw [hfun, Function.comp_def, hmp.integral_comp g.measurableEmbedding, integral_prod_symm _ hF]
  simp only [hinner]

/-- A nonzero coefficient `f_j` of `f` as a polynomial in the first variable satisfies
`log M(f_j) ≤ log binom(d_0, ⌊d_0/2⌋) + log M(f)`. -/
private lemma integral_log_coeff_le {n : ℕ} {f : _root_.MvPolynomial (Fin (n + 1)) ℂ}
    (hf : f ≠ 0) {j : ℕ} (hj : (MvPolynomial.finSuccEquiv ℂ n f).coeff j ≠ 0) :
    ∫ y, log ‖MvPolynomial.eval (fun i ↦ e (y i))
        ((MvPolynomial.finSuccEquiv ℂ n f).coeff j)‖ ∂(Measure.pi fun _ : Fin n ↦ ν) ≤
      log ((f.degreeOf 0).choose (f.degreeOf 0 / 2) : ℝ) +
        ∫ θ, log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ∂(Measure.pi fun _ ↦ ν) := by
  set p := MvPolynomial.finSuccEquiv ℂ n f
  set B : ℝ := ((f.degreeOf 0).choose (f.degreeOf 0 / 2) : ℝ)
  have hB : 0 < B := by
    simp only [B]; exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
  obtain ⟨hI, heq⟩ := slice_integral hf
  have hc : ∫ _y : Fin n → ℝ, log B ∂(Measure.pi fun _ ↦ ν) = log B := by simp
  rw [heq, ← hc, ← integral_add (integrable_const _) hI]
  refine integral_mono_ae (integrable_log_norm_eval_e hj) ((integrable_const _).add hI) ?_
  have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin n ↦ ν),
      MvPolynomial.eval (fun i ↦ e (y i)) (p.coeff j) ≠ 0 := by
    rw [← Measure.restrict_pi_pi, ← volume_pi]
    exact ae_restrict_of_ae (ae_eval_exp_ne_zero_mvPolynomial hj)
  filter_upwards [hae] with y hy
  set q := p.map (MvPolynomial.eval fun j ↦ e (y j))
  have hqj : q.coeff j = MvPolynomial.eval (fun i ↦ e (y i)) (p.coeff j) :=
    Polynomial.coeff_map _ _
  have hq : q ≠ 0 := fun h ↦ hy (by rw [← hqj, h, Polynomial.coeff_zero])
  have hM : 0 < q.mahlerMeasure := Polynomial.mahlerMeasure_pos_of_ne_zero hq
  have hdeg : q.natDegree ≤ f.degreeOf 0 :=
    Polynomial.natDegree_map_le.trans (MvPolynomial.natDegree_finSuccEquiv f).le
  have hle : ‖q.coeff j‖ ≤ B * q.mahlerMeasure := by
    refine (Polynomial.norm_coeff_le_choose_mul_mahlerMeasure j q).trans ?_
    gcongr
    simp only [B]
    exact_mod_cast (Nat.choose_le_choose j hdeg).trans (Nat.choose_le_middle _ _)
  change _ ≤ log B + q.logMahlerMeasure
  rw [← hqj, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure, ← log_mul hB.ne' hM.ne']
  exact log_le_log (norm_pos_iff.2 (hqj ▸ hy)) hle

private lemma choose_half_mono {a b : ℕ} (h : a ≤ b) : a.choose (a / 2) ≤ b.choose (b / 2) :=
  (Nat.choose_le_choose _ h).trans (Nat.choose_le_middle _ _)

/-- The statement for `Fin n`, with the product of the uniform measures on `[0,1]`. -/
private lemma supNorm_le_fin (n : ℕ) : ∀ f : _root_.MvPolynomial (Fin n) ℂ, f ≠ 0 →
    supNorm f ≤ (∏ i, ((f.degreeOf i).choose (f.degreeOf i / 2) : ℝ)) *
      exp (∫ θ, log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖ ∂(Measure.pi fun _ ↦ ν)) := by
  induction n with
  | zero =>
    intro f hf
    have hC := MvPolynomial.eq_C_of_isEmpty f
    have hc : ∀ θ : Fin 0 → ℝ, MvPolynomial.eval (fun i ↦ e (θ i)) f = f.coeff 0 := by
      intro θ; conv_lhs => rw [hC]
      simp
    have h0 : f.coeff 0 ≠ 0 := by
      intro h; apply hf; rw [hC, h, map_zero]
    simp_rw [hc]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, integral_const, probReal_univ,
      one_smul]
    rw [exp_log (norm_pos_iff.2 h0), supNorm_le_iff (norm_nonneg _)]
    intro I
    rw [hC, MvPolynomial.coeff_C]
    split_ifs <;> simp
  | succ n ih =>
    intro f hf
    set p := MvPolynomial.finSuccEquiv ℂ n f with hp_def
    rw [supNorm_le_iff (by positivity)]
    intro I
    rw [← Finsupp.cons_tail I, ← MvPolynomial.finSuccEquiv_coeff_coeff, ← hp_def]
    by_cases hj : p.coeff (I 0) = 0
    · rw [hj, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, norm_zero]; positivity
    refine (norm_coeff_le_supNorm _ _).trans ((ih _ hj).trans ?_)
    have hB : 0 < ((f.degreeOf 0).choose (f.degreeOf 0 / 2) : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
    rw [Fin.prod_univ_succ, mul_assoc, mul_left_comm]
    refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ ?_) ?_
      (exp_pos _).le (by positivity)
    · exact_mod_cast choose_half_mono (MvPolynomial.degreeOf_coeff_finSuccEquiv f i _)
    · refine (exp_le_exp.2 (integral_log_coeff_le hf hj)).trans_eq ?_
      rw [exp_add, exp_log hB]

/-- For a nonzero polynomial `f` over `ℂ` in finitely many (at least one) variables, with partial
degrees `d_i = f.degreeOf i`, the sup norm of the coefficients is at most
`∏_i binom(d_i, ⌊d_i/2⌋)` times the Mahler measure of `f`. -/
@[faltings "lem_ht_mahler_lower_bound"]
public theorem supNorm_le_prod_choose_degreeOf_div_two_mul_mahlerMeasure {σ : Type*}
    [Fintype σ] [Nonempty σ] {f : _root_.MvPolynomial σ ℂ} (hf : f ≠ 0) :
    supNorm f ≤
      (∏ i, ((f.degreeOf i).choose (f.degreeOf i / 2) : ℝ)) * mahlerMeasure f := by
  set k := Fintype.equivFin σ
  set f' := MvPolynomial.rename k f
  have hf' : f' ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.rename_injective _ k.injective)).2 hf
  have hsup : supNorm f ≤ supNorm f' := by
    rw [supNorm_le_iff (supNorm_nonneg _)]
    intro I
    rw [← MvPolynomial.coeff_rename_mapDomain k k.injective]
    exact norm_coeff_le_supNorm _ _
  have hprod : (∏ j, ((f'.degreeOf j).choose (f'.degreeOf j / 2) : ℝ)) =
      ∏ i, ((f.degreeOf i).choose (f.degreeOf i / 2) : ℝ) := by
    rw [← k.prod_comp]
    simp only [f', MvPolynomial.degreeOf_rename_of_injective k.injective]
  set G := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) ↦ ℝ) k
  have hG : MeasurePreserving G (Measure.pi fun _ : σ ↦ ν) (Measure.pi fun _ ↦ ν) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) ↦ ν) k
  have hint : ∫ θ, log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f'‖ ∂(Measure.pi fun _ ↦ ν) =
      ∫ θ in Set.univ.pi (fun _ : σ ↦ Set.Icc (0 : ℝ) 1),
        log ‖MvPolynomial.eval (fun i ↦ Complex.exp (2 * π * Complex.I * (θ i : ℂ))) f‖ := by
    rw [volume_pi, Measure.restrict_pi_pi,
      ← hG.integral_comp' (fun θ' ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ' i)) f'‖)]
    congr 1; funext θ
    simp only [f', MvPolynomial.eval_rename]
    congr 4; funext i
    simp [G, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [mahlerMeasure_of_ne_zero hf, ← hint, ← hprod]
  exact hsup.trans (supNorm_le_fin _ f' hf')

end MvPolynomial

end Faltings
