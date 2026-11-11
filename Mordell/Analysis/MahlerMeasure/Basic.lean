module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mordell.Attr
public import Mathlib

/-!
# The Mahler measure of a polynomial in several variables

For a nonzero polynomial `f ∈ ℂ[t_i : i ∈ σ]` in finitely many variables, the Mahler measure is
`M(f) = exp ∫_{[0,1]^σ} log |f(e^{2πiθ})| dθ`, the integral being taken over the unit cube with
respect to Lebesgue measure; for `f = 0` it is `0`, which is the value `exp(-∞)` of the same
formula.

## Main definitions

* `Faltings.MvPolynomial.mahlerMeasure f`: the Mahler measure `M(f)` of `f : MvPolynomial σ ℂ`.

## Main results

* `Faltings.MvPolynomial.mahlerMeasure_of_ne_zero`: the defining formula for `f ≠ 0`.
* `Faltings.MvPolynomial.mahlerMeasure_nonneg`: `M(f) ≥ 0`.
* `Faltings.MvPolynomial.mahlerMeasure_pos_of_ne_zero`: `M(f) > 0` for `f ≠ 0`.

## Implementation notes

The variables are indexed by an arbitrary finite type `σ` rather than by `{1, …, n}`.

The source takes the integral in `[-∞, ∞)`. Here it is the Bochner integral of the real function
`θ ↦ Real.log ‖f(e^{2πiθ})‖`, with `Real.log 0 = 0`. For `f ≠ 0` this function is integrable on
the cube and its zero set there is null, so the two integrals agree; the case `f = 0`, where the
source's integral is `-∞`, is set to `0` separately, exactly as for `Polynomial.mahlerMeasure`.
With this convention, for one variable the definition agrees with `Polynomial.mahlerMeasure`.

## References

* [Z. Gao, *Heights*][gao2022], Def. 1.3.8.
* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006], 1.6.1.
-/

namespace Faltings

namespace MvPolynomial

open Real in
/-- The Mahler measure `M(f) = exp ∫_{[0,1]^σ} log |f(e^{2πiθ_1}, …)| dθ` of a polynomial `f` in
finitely many variables over `ℂ`, with `M(0) = 0`. -/
@[expose, faltings "def_ht_mahler_measure"]
public noncomputable def mahlerMeasure {σ : Type*} [Fintype σ] (f : _root_.MvPolynomial σ ℂ) : ℝ :=
  if f ≠ 0 then
    Real.exp (∫ θ in Set.univ.pi (fun _ : σ ↦ Set.Icc (0 : ℝ) 1),
      Real.log ‖_root_.MvPolynomial.eval
        (fun i ↦ Complex.exp (2 * π * Complex.I * (θ i : ℂ))) f‖)
  else 0

variable {σ : Type*} [Fintype σ]

/-- The Mahler measure of the zero polynomial is `0`. -/
@[simp]
public theorem mahlerMeasure_zero : mahlerMeasure (0 : _root_.MvPolynomial σ ℂ) = 0 := by
  simp [mahlerMeasure]

open Real in
/-- For `f ≠ 0`, `M(f)` is the exponential of the integral of `log ‖f(e^{2πiθ})‖` over the unit
cube. -/
public theorem mahlerMeasure_of_ne_zero {f : _root_.MvPolynomial σ ℂ} (hf : f ≠ 0) :
    mahlerMeasure f = Real.exp (∫ θ in Set.univ.pi (fun _ : σ ↦ Set.Icc (0 : ℝ) 1),
      Real.log ‖_root_.MvPolynomial.eval
        (fun i ↦ Complex.exp (2 * π * Complex.I * (θ i : ℂ))) f‖) := by
  simp [mahlerMeasure, hf]

/-- The Mahler measure is nonnegative. -/
public theorem mahlerMeasure_nonneg (f : _root_.MvPolynomial σ ℂ) : 0 ≤ mahlerMeasure f := by
  unfold mahlerMeasure
  split_ifs
  exacts [(Real.exp_pos _).le, le_rfl]

/-- The Mahler measure of a nonzero polynomial is positive. -/
public theorem mahlerMeasure_pos_of_ne_zero {f : _root_.MvPolynomial σ ℂ} (hf : f ≠ 0) :
    0 < mahlerMeasure f :=
  (mahlerMeasure_of_ne_zero hf).symm ▸ Real.exp_pos _

end MvPolynomial

end Faltings

/-!
# Integrability of `log ‖f‖` on the torus

Let `f` be a nonzero polynomial over `ℂ` in finitely many variables `t_i`, `i ∈ σ`. Then
`θ ↦ log ‖f(e^{2πiθ_i})_i‖` is integrable on the unit cube `[0,1]^σ`. This is what makes the
multivariable Mahler measure `M(f) = exp ∫_{[0,1]^σ} log ‖f(e^{2πiθ})‖ dθ` a positive real number.
Along the way, `f(e^{2πiθ_i})_i` is nonzero for almost every `θ ∈ ℝ^σ`.

## Main results

* `Faltings.ae_eval_exp_ne_zero_mvPolynomial`: for `f ≠ 0`, the function
  `θ ↦ MvPolynomial.eval (fun i ↦ exp (2πiθ_i)) f` vanishes only on a null subset of `σ → ℝ`;
  `Faltings.ae_eval_exp_ne_zero` is the one-variable case.
* `Faltings.integrableOn_log_norm_eval_exp_mvPolynomial`: for `f ≠ 0`, the function
  `θ ↦ log ‖MvPolynomial.eval (fun i ↦ exp (2πiθ_i)) f‖` is integrable on `Set.Icc 0 1`.

## Implementation notes

The variables are indexed by an arbitrary finite type `σ` rather than `Fin n`, and the cube
`[0,1]^σ` is the order interval `Set.Icc 0 1` in `σ → ℝ`. The one-variable case is Mathlib's
`Polynomial.intervalIntegrable_mahlerMeasure`, there parametrised by `circleMap 0 1` on `[0, 2π]`.
The point `e t = e^{2πit}` and the uniform measure `ν` on `[0,1]` are
`Faltings.MahlerMeasure.e` and `Faltings.MahlerMeasure.ν`, shared with the files that bound the
Mahler measure.

Both results are proved for `Fin n` by induction on `n`, writing `f` as a polynomial in the first
variable with leading coefficient `f_d`, and transferred to `σ` along `Fintype.equivFin σ`.
Almost-everywhere nonvanishing follows on each slice from the finiteness of the roots of a nonzero
one-variable polynomial. For integrability, Jensen's inequality in one variable
(`Polynomial.leadingCoeff_le_mahlerMeasure`) bounds the slice integrals below by `log ‖f_d‖`, which
is integrable by induction and is the slice's leading coefficient for almost every slice; since
`log ‖f‖` is bounded above on the torus by the sum of the norms of the coefficients, Tonelli's
theorem applied to the nonnegative function `C - log ‖f‖` concludes.

## References

* [Gao 2022, Lemma 1.3.11], [Bombieri–Gubler, *Heights in Diophantine Geometry*, 1.6.5]
-/

open Real MeasureTheory

namespace Faltings

namespace MahlerMeasure

/-- The point `e^{2πit}` of the unit circle. -/
public noncomputable abbrev e (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

/-- The uniform probability measure on `[0,1]`. -/
public noncomputable abbrev ν : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- `e t` is `circleMap 0 1` at the angle `2πt`. -/
public lemma e_eq_circleMap (t : ℝ) : e t = circleMap 0 1 (2 * π * t) := by
  simp only [e, circleMap, zero_add]
  push_cast; ring_nf

/-- Evaluating `f` on the torus is evaluating, at `e (θ 0)`, the one-variable slice of `f` along
the first variable at the remaining coordinates. -/
public lemma eval_e_eq_eval_slice {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℂ)
    (θ : Fin (n + 1) → ℝ) :
    MvPolynomial.eval (fun i ↦ e (θ i)) f =
      ((MvPolynomial.finSuccEquiv ℂ n f).map
        (MvPolynomial.eval fun j ↦ e (Fin.removeNth 0 θ j))).eval (e (θ 0)) := by
  rw [← MvPolynomial.eval_eq_eval_mv_eval']
  congr 2; funext i
  cases i using Fin.cases <;> simp [Fin.removeNth]

end MahlerMeasure

open MahlerMeasure

private lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e_eq_circleMap]; simp

/-- Each fibre of `e` is countable: it is a coset of `ℤ` in `ℝ`. -/
private lemma countable_preimage_e (r : ℂ) : (e ⁻¹' {r}).Countable := by
  rcases (e ⁻¹' {r}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · simp [h]
  refine (Set.countable_range (fun n : ℤ ↦ x₀ + n)).mono fun x (hx : e x = r) ↦ ?_
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (hx.trans hx₀.symm)
  have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [pi_ne_zero]
  exact ⟨n, by exact_mod_cast (mul_left_cancel₀ h2 (by linear_combination hn) :
    (x : ℂ) = x₀ + n).symm⟩

/-- A nonzero complex polynomial `q` in one variable vanishes only on a null set of the circle:
`q(e^{2πix}) ≠ 0` for almost every `x ∈ ℝ`. -/
public theorem ae_eval_exp_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∀ᵐ x : ℝ, q.eval (Complex.exp (2 * π * Complex.I * x)) ≠ 0 := by
  have hc : {x : ℝ | q.eval (e x) = 0}.Countable :=
    ((Polynomial.finite_setOfPred_isRoot hq).countable.biUnion
      fun r _ ↦ countable_preimage_e r).mono fun x hx ↦ Set.mem_biUnion (x := e x) hx rfl
  exact ae_iff.2 (by simpa using hc.measure_zero volume)

/-- One-variable case: for `q ≠ 0`, `x ↦ log ‖q(e x)‖` is integrable on `[0,1]` and its integral
is at least `log ‖lead q‖`. -/
private lemma integrable_and_log_leadingCoeff_le {q : Polynomial ℂ} (hq : q ≠ 0) :
    Integrable (fun x ↦ log ‖q.eval (e x)‖) (volume.restrict (Set.Icc 0 1)) ∧
      log ‖q.leadingCoeff‖ ≤ ∫ x, log ‖q.eval (e x)‖ ∂(volume.restrict (Set.Icc 0 1)) := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hI : IntervalIntegrable (fun x ↦ log ‖q.eval (e x)‖) volume 0 1 := by
    have := (Polynomial.intervalIntegrable_mahlerMeasure (p := q)).comp_mul_left (c := 2 * π)
      enorm_ne_top enorm_ne_top
    simp only [zero_div, div_self hpos.ne'] at this
    simpa [e_eq_circleMap] using this
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hI, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have h1 : ∫ x in (0:ℝ)..1, log ‖q.eval (e x)‖ = q.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_def, circleAverage_def, smul_eq_mul]
    simp_rw [e_eq_circleMap]
    rw [intervalIntegral.integral_comp_mul_left (fun x ↦ log ‖q.eval (circleMap 0 1 x)‖)
      hpos.ne']
    simp [smul_eq_mul]
  rw [h1, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  exact log_le_log (norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hq))
    (Polynomial.leadingCoeff_le_mahlerMeasure q)

/-- On the torus, `‖f(z)‖` is bounded by the sum of the norms of the coefficients of `f`. -/
private lemma norm_eval_le_sum_norm_coeff {σ : Type*} (f : MvPolynomial σ ℂ)
    {z : σ → ℂ} (hz : ∀ i, ‖z i‖ = 1) :
    ‖MvPolynomial.eval z f‖ ≤ ∑ m ∈ f.support, ‖f.coeff m‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [norm_mul, norm_prod]; simp [hz]

/-- Evaluation of a polynomial on the torus, `θ ↦ f(e^{2πiθ_i})_i`, is measurable. -/
public theorem measurable_eval_exp_mvPolynomial {σ : Type*} [Countable σ]
    (f : MvPolynomial σ ℂ) :
    Measurable fun θ : σ → ℝ ↦
      MvPolynomial.eval (fun i ↦ Complex.exp (2 * π * Complex.I * θ i)) f :=
  ((MvPolynomial.continuous_eval f).comp
    (continuous_pi fun i ↦ (by fun_prop : Continuous e).comp (continuous_apply i))).measurable

/-- A slice of `p` at a point where its leading coefficient does not vanish is nonzero, with the
value of the leading coefficient as its own leading coefficient. -/
private lemma leadingCoeff_map_eval_and_ne_zero {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    {z : Fin n → ℂ} (hz : MvPolynomial.eval z p.leadingCoeff ≠ 0) :
    (p.map (MvPolynomial.eval z)).leadingCoeff = MvPolynomial.eval z p.leadingCoeff ∧
      p.map (MvPolynomial.eval z) ≠ 0 := by
  have h := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hz
  exact ⟨h, fun h0 ↦ hz (by rw [← h, h0, Polynomial.leadingCoeff_zero])⟩

/-- A nonzero polynomial in `n` variables vanishes only on a null subset of the torus. -/
private lemma ae_ne_zero_fin (n : ℕ) : ∀ f : MvPolynomial (Fin n) ℂ, f ≠ 0 →
    ∀ᵐ θ ∂(Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ)),
      MvPolynomial.eval (fun i ↦ e (θ i)) f ≠ 0 := by
  induction n with
  | zero =>
    intro f hf
    refine .of_forall fun θ ↦ ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ n ih =>
    intro f hf
    set g := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    have hmp : MeasurePreserving g (Measure.pi fun _ ↦ (volume : Measure ℝ))
        ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)) 0
    set p := MvPolynomial.finSuccEquiv ℂ n f
    have hp : p ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ n).injective).2 hf
    have hae := ih _ (Polynomial.leadingCoeff_ne_zero.2 hp)
    set Φ : ℝ × (Fin n → ℝ) → ℂ := fun z ↦
      (p.map (MvPolynomial.eval fun j ↦ e (z.2 j))).eval (e z.1)
    have hΦ : (fun θ ↦ MvPolynomial.eval (fun i ↦ e (θ i)) f) = Φ ∘ g :=
      funext (eval_e_eq_eval_slice f)
    have hΦm : Measurable Φ := by
      simpa [hΦ, Function.comp_assoc] using
        (measurable_eval_exp_mvPolynomial f).comp g.symm.measurable
    have hZ : ∀ᵐ z ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))),
        Φ z ≠ 0 := by
      have hms : MeasurableSet {z | Φ z ≠ 0} := hΦm (measurableSet_singleton 0).compl
      rw [Measure.ae_prod_iff_ae_ae hms, Measure.ae_ae_comm hms]
      filter_upwards [hae] with y hy
      exact ae_eval_exp_ne_zero (leadingCoeff_map_eval_and_ne_zero hy).2
    filter_upwards [hmp.quasiMeasurePreserving.ae hZ] with θ hθ
    exact (congrFun hΦ θ).trans_ne hθ

/-- Evaluation on the torus in the variables `σ` is evaluation of the renamed polynomial on the
torus in the variables `Fin (card σ)`, after the coordinate change `piCongrLeft`. -/
private lemma eval_e_rename_equivFin {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ)
    (θ : σ → ℝ) :
    MvPolynomial.eval (fun i ↦ e (θ i)) f =
      MvPolynomial.eval
        (fun i ↦ e (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (Fintype.equivFin σ) θ i))
        (MvPolynomial.rename (Fintype.equivFin σ) f) := by
  simp only [MvPolynomial.eval_rename]
  congr 2; funext i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

private lemma measurePreserving_piCongrLeft_equivFin {σ : Type*} [Fintype σ] (μ : Measure ℝ)
    [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (Fintype.equivFin σ))
      (Measure.pi fun _ : σ ↦ μ) (Measure.pi fun _ ↦ μ) :=
  measurePreserving_piCongrLeft (fun _ ↦ μ) _

/-- A nonzero complex polynomial `f` in the variables indexed by a finite type `σ` vanishes only
on a null subset of the torus: `f(e^{2πiθ_i})_i ≠ 0` for almost every `θ ∈ ℝ^σ`. -/
public theorem ae_eval_exp_ne_zero_mvPolynomial {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ ℂ} (hf : f ≠ 0) :
    ∀ᵐ θ : σ → ℝ, MvPolynomial.eval (fun i ↦ Complex.exp (2 * π * Complex.I * θ i)) f ≠ 0 := by
  have h := ae_ne_zero_fin _ _
    ((map_ne_zero_iff _ (MvPolynomial.rename_injective _ (Fintype.equivFin σ).injective)).2 hf)
  rw [volume_pi]
  filter_upwards [(measurePreserving_piCongrLeft_equivFin volume).quasiMeasurePreserving.ae h]
    with θ hθ
  exact (eval_e_rename_equivFin f θ).trans_ne hθ

/-- Tonelli's theorem for a function bounded above: on a product of finite measures, a measurable
`F ≤ C` is integrable as soon as almost every slice `F(·, y)` is integrable with integral at least
`L y`, for an integrable `L`. -/
private lemma integrable_prod_of_le_of_le_integral {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : α × β → ℝ} (hFm : Measurable F) {C : ℝ} (hle : ∀ z, F z ≤ C) {L : β → ℝ}
    (hL : Integrable L ν)
    (h : ∀ᵐ y ∂ν, Integrable (fun x ↦ F (x, y)) μ ∧ L y ≤ ∫ x, F (x, y) ∂μ) :
    Integrable F (μ.prod ν) := by
  have hGm : Measurable fun z ↦ C - F z := measurable_const.sub hFm
  have hnn : ∀ z, ‖C - F z‖ = C - F z := fun z ↦ norm_of_nonneg (sub_nonneg.2 (hle z))
  have hG : Integrable (fun z ↦ C - F z) (μ.prod ν) := by
    rw [integrable_prod_iff' hGm.aestronglyMeasurable]
    refine ⟨h.mono fun y hy ↦ (integrable_const C).sub hy.1, ?_⟩
    refine ((integrable_const (μ.real Set.univ * C)).sub hL).mono'
      (hGm.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable ?_
    filter_upwards [h] with y ⟨hint, hJ⟩
    simp_rw [hnn]
    rw [norm_of_nonneg (integral_nonneg fun x ↦ sub_nonneg.2 (hle _)),
      integral_sub (integrable_const C) hint, integral_const, smul_eq_mul]
    simp only [Pi.sub_apply]
    linarith
  exact ((integrable_const C).sub hG).congr (.of_forall fun z ↦ by simp)

private lemma pi_ν_eq_restrict (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι ↦ ν) =
      (Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).restrict
        (Set.univ.pi fun _ ↦ Set.Icc 0 1) :=
  (Measure.restrict_pi_pi _ _).symm

/-- The statement for `Fin n`, with the measure `ν^n`. -/
private lemma integrable_log_norm_fin (n : ℕ) : ∀ f : MvPolynomial (Fin n) ℂ, f ≠ 0 →
    Integrable (fun θ : Fin n → ℝ ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖)
      (Measure.pi fun _ ↦ ν) := by
  induction n with
  | zero =>
    intro f _
    rw [MvPolynomial.eq_C_of_isEmpty f]
    simp
  | succ n ih =>
    intro f hf
    set g := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    have hmp : MeasurePreserving g (Measure.pi fun _ ↦ ν)
        (ν.prod (Measure.pi fun _ : Fin n ↦ ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ν) 0
    set p := MvPolynomial.finSuccEquiv ℂ n f
    have hp : p ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ n).injective).2 hf
    have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp
    have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin n ↦ ν),
        MvPolynomial.eval (fun j ↦ e (y j)) p.leadingCoeff ≠ 0 := by
      rw [pi_ν_eq_restrict]; exact ae_restrict_of_ae (ae_ne_zero_fin _ _ hlead)
    set Φ : ℝ × (Fin n → ℝ) → ℂ := fun z ↦
      (p.map (MvPolynomial.eval fun j ↦ e (z.2 j))).eval (e z.1)
    have hΦ : (fun θ ↦ MvPolynomial.eval (fun i ↦ e (θ i)) f) = Φ ∘ g :=
      funext (eval_e_eq_eval_slice f)
    have hΦg : ∀ z, Φ z = MvPolynomial.eval (fun i ↦ e (g.symm z i)) f := fun z ↦ by
      simpa using (congrFun hΦ (g.symm z)).symm
    have hΦm : Measurable Φ := by
      simpa [hΦ, Function.comp_assoc] using
        (measurable_eval_exp_mvPolynomial f).comp g.symm.measurable
    rw [show (fun θ ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ i)) f‖) = (fun z ↦ log ‖Φ z‖) ∘ g
      from funext fun θ ↦ congrArg (log ‖·‖) (congrFun hΦ θ),
      hmp.integrable_comp_emb g.measurableEmbedding]
    refine integrable_prod_of_le_of_le_integral (measurable_log.comp hΦm.norm)
      (C := ∑ m ∈ f.support, ‖f.coeff m‖) (fun z ↦ (log_le_self (norm_nonneg _)).trans
        (by rw [hΦg]; exact norm_eval_le_sum_norm_coeff f fun i ↦ norm_e _)) (ih _ hlead) ?_
    filter_upwards [hae] with y hy
    obtain ⟨hl, hqy⟩ := leadingCoeff_map_eval_and_ne_zero hy
    simpa [Φ, hl] using integrable_and_log_leadingCoeff_le hqy

/-- For a nonzero complex polynomial `f` in the variables indexed by a finite type `σ`, the
function `θ ↦ log ‖f(e^{2πiθ_i})_i‖` is integrable on the unit cube `[0,1]^σ`. -/
@[faltings "lem_ht_mahler_integrable"]
public theorem integrableOn_log_norm_eval_exp_mvPolynomial {σ : Type*} [Fintype σ]
    {f : MvPolynomial σ ℂ} (hf : f ≠ 0) :
    IntegrableOn
      (fun θ : σ → ℝ ↦
        log ‖MvPolynomial.eval (fun i ↦ Complex.exp (2 * π * Complex.I * θ i)) f‖)
      (Set.Icc 0 1) volume := by
  have hmeas : volume.restrict (Set.Icc (0 : σ → ℝ) 1) = Measure.pi fun _ : σ ↦ ν := by
    rw [pi_ν_eq_restrict, ← Set.pi_univ_Icc, volume_pi]; rfl
  have hfun : (fun θ : σ → ℝ ↦
      log ‖MvPolynomial.eval (fun i ↦ Complex.exp (2 * π * Complex.I * θ i)) f‖) =
      (fun θ' ↦ log ‖MvPolynomial.eval (fun i ↦ e (θ' i))
        (MvPolynomial.rename (Fintype.equivFin σ) f)‖) ∘
        MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (Fintype.equivFin σ) :=
    funext fun θ ↦ by simp only [Function.comp_apply, ← eval_e_rename_equivFin]
  rw [IntegrableOn, hmeas, hfun, (measurePreserving_piCongrLeft_equivFin ν).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  exact integrable_log_norm_fin _ _
    ((map_ne_zero_iff _ (MvPolynomial.rename_injective _ (Fintype.equivFin σ).injective)).2 hf)

end Faltings
