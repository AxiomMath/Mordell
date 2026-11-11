module
public import Mathlib
public import Mordell.Attr
public import Mordell.Polynomial.Taylor
public import Mordell.Height.Finsupp

/-!
# Roth's lemma in one variable

Let `P ≠ 0` be a polynomial of degree at most `r` with algebraic coefficients, let `ς⁰` be
algebraic, and let `i*` be such that the divided derivatives `∂ᵢ P` vanish at `ς⁰` for `i < i*`
while `∂_{i*} P (ς⁰) ≠ 0`. Then `i* h(ς⁰) ≤ h(P) + r`, where `h` is the absolute logarithmic
Weil height of the algebraic number `ς⁰` and of the point of projective space whose homogeneous
coordinates are the nonzero coefficients of `P`.

## Main results

* `Faltings.mul_logHeight₁_le_logHeight_add_of_hasseDeriv`: Roth's lemma in one variable.

## Implementation notes

All coefficients of `P` and the point `ς⁰` lie in one number field `K`, and the statement is
made over an arbitrary such `K`. The divided derivative `∂ᵢ = (1/i!) dⁱ/dςⁱ` is
`Polynomial.hasseDeriv i`. Mathlib's heights over `K` are relative to `K`: they count the places
of `K` with their local degrees. So the absolute height of `ς⁰` is
`Height.logHeight₁ ς⁰ / [K : ℚ]`, and the absolute height `h(P)` of a nonzero polynomial is
`Finsupp.logHeight P.toFinsupp.coeff / [K : ℚ]`. The finsupp height is the height of the
coefficients indexed by the support of `P`, as in the source. Both quotients do not depend on
the choice of `K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9, p. 634
-/

namespace Faltings

open Polynomial Height NumberField

section Helpers

variable {K : Type*} [Field K]

/-- The Gauss norm with parameter `1` is the supremum of the absolute values of the
coefficients. -/
private lemma gaussNorm_one_eq_iSup (v : AbsoluteValue K ℝ) (p : K[X]) :
    p.gaussNorm v 1 = ⨆ n : ℕ, v (p.coeff n) := by
  have hle : ∀ n, v (p.coeff n) ≤ p.gaussNorm v 1 := fun n => by
    simpa using p.le_gaussNorm v zero_le_one n
  obtain ⟨i, hi⟩ := p.exists_eq_gaussNorm v 1
  refine le_antisymm ?_ (ciSup_le hle)
  rw [hi, one_pow, mul_one]
  exact le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ i

/-- For a nonzero polynomial, the supremum over the support of the absolute values of the
coefficients is the Gauss norm with parameter `1`. -/
private lemma iSup_support_eq_gaussNorm (v : AbsoluteValue K ℝ) {p : K[X]} (hp : p ≠ 0) :
    ⨆ j : p.support, v (p.coeff j) = p.gaussNorm v 1 := by
  have : Nonempty p.support := ⟨⟨p.natDegree, natDegree_mem_support_of_nonzero hp⟩⟩
  refine le_antisymm (ciSup_le fun j => by simpa using p.le_gaussNorm v zero_le_one j) ?_
  obtain ⟨i, hi⟩ := p.exists_eq_gaussNorm v 1
  rw [hi, one_pow, mul_one]
  by_cases h : p.coeff i = 0
  · rw [h, map_zero]
    exact Real.iSup_nonneg fun _ => v.nonneg _
  · exact le_ciSup (f := fun j : p.support => v (p.coeff j)) (Set.finite_range _).bddAbove
      ⟨i, mem_support_iff.2 h⟩

/-- At a nonarchimedean absolute value, the Gauss norm of `(X - x)^i` is `max(|x|, 1)^i`. -/
private lemma gaussNorm_X_sub_C_pow {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (x : K)
    (i : ℕ) : ((X - C x) ^ i).gaussNorm v 1 = max (v x) 1 ^ i := by
  have h1 : (X - C x).gaussNorm v 1 = max (v x) 1 := by
    refine le_antisymm ?_ (max_le ?_ ?_)
    · have hX : (X : K[X]).gaussNorm v 1 = 1 := by
        rw [← monomial_one_one_eq_X, gaussNorm_monomial, map_one, one_pow, mul_one]
      have hC : (-C x).gaussNorm v 1 = v x := by rw [← C_neg, gaussNorm_C, map_neg_eq_map]
      have := isNonarchimedean_gaussNorm v hv zero_le_one X (-C x)
      rw [hX, hC, ← sub_eq_add_neg] at this
      rwa [max_comm]
    · have := (X - C x).le_gaussNorm v zero_le_one 0
      rwa [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg_eq_map, pow_zero,
        mul_one] at this
    · have := (X - C x).le_gaussNorm v zero_le_one 1
      rwa [coeff_sub, coeff_X_one, coeff_C_of_ne_zero one_ne_zero, sub_zero, map_one, one_pow,
        mul_one] at this
  induction i with
  | zero => rw [pow_zero, pow_zero, ← C_1, gaussNorm_C, map_one]
  | succ n ih => rw [pow_succ, gaussNorm_mul hv one_pos, ih, h1, pow_succ]

/-- If the divided derivatives of `P` of order `< i` vanish at `x`, then `(X - x)^i` divides
`P`: the Taylor expansion of `P` at `x` has no terms of degree `< i`. -/
private lemma X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero {P : K[X]} {x : K} {i : ℕ}
    (hzero : ∀ j < i, (hasseDeriv j P).eval x = 0) : (X - C x) ^ i ∣ P := by
  have h := map_dvd (taylorAlgHom (-x)) <|
    X_pow_dvd_iff.2 fun j hj => (taylor_coeff (r := x) (f := P) (n := j)).trans (hzero j hj)
  rw [map_pow, taylorAlgHom_apply, taylorAlgHom_apply, taylor_X, taylor_taylor] at h
  simpa [sub_eq_add_neg] using h

/-- The supremum of a pair `![a, b]` under an absolute value. -/
private lemma iSup_vecCons (v : AbsoluteValue K ℝ) (a b : K) :
    ⨆ j : Fin 2, v (![a, b] j) = max (v a) (v b) := by
  refine le_antisymm (ciSup_le (Fin.forall_fin_two.2 ⟨le_max_left _ _, le_max_right _ _⟩))
    (max_le ?_ ?_)
  · exact le_ciSup (f := fun j : Fin 2 => v (![a, b] j)) (Set.finite_range _).bddAbove 0
  · exact le_ciSup (f := fun j : Fin 2 => v (![a, b] j)) (Set.finite_range _).bddAbove 1

/-- At an infinite place, `max(|x|, 1)^i |Q| ≤ 2^{deg Q} √(deg P + 1) |P|` for
`P = (X - x)^i Q`, where `|·|` is the sup norm of the coefficients. -/
private lemma arch_bound (w : InfinitePlace K) (x : K) (i : ℕ) (Q : K[X]) :
    max (w x) 1 ^ i * Q.gaussNorm w.1 1 ≤
      2 ^ Q.natDegree * √(((X - C x) ^ i * Q).natDegree + 1) *
        ((X - C x) ^ i * Q).gaussNorm w.1 1 := by
  set φ := w.embedding
  have hG (p : K[X]) : p.gaussNorm w.1 1 = (p.map φ).supNorm := by
    rw [gaussNorm_one_eq_iSup, supNorm_eq_iSup]
    congr 1
    ext n
    rw [coeff_map, InfinitePlace.norm_embedding_eq]
    rfl
  have hx : max (w x) 1 ^ i = ((X - C (φ x)) ^ i).mahlerMeasure := by
    induction i with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, mahlerMeasure_mul, ← ih, mahlerMeasure_X_sub_C,
        InfinitePlace.norm_embedding_eq, max_comm]
  have hmap : ((X - C x) ^ i * Q).map φ = (X - C (φ x)) ^ i * Q.map φ := by
    simp [Polynomial.map_mul, Polynomial.map_pow]
  have hQ : (Q.map φ).supNorm ≤ 2 ^ Q.natDegree * (Q.map φ).mahlerMeasure := by
    refine (supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure _).trans ?_
    rw [natDegree_map]
    gcongr
    · exact mahlerMeasure_nonneg _
    · exact_mod_cast Nat.choose_le_two_pow _ _
  calc max (w x) 1 ^ i * Q.gaussNorm w.1 1
      = ((X - C (φ x)) ^ i).mahlerMeasure * (Q.map φ).supNorm := by rw [hx, hG]
    _ ≤ ((X - C (φ x)) ^ i).mahlerMeasure * (2 ^ Q.natDegree * (Q.map φ).mahlerMeasure) := by
        gcongr
        exact mahlerMeasure_nonneg _
    _ = 2 ^ Q.natDegree * (((X - C x) ^ i * Q).map φ).mahlerMeasure := by
        rw [hmap, mahlerMeasure_mul]; ring
    _ ≤ 2 ^ Q.natDegree * (√((((X - C x) ^ i * Q).map φ).natDegree + 1) *
          (((X - C x) ^ i * Q).map φ).supNorm) := by
        gcongr
        exact mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _
    _ = _ := by rw [natDegree_map, ← hG]; ring

variable [NumberField K]

/-- The height of the coefficients of a nonzero polynomial, place by place. -/
private lemma mulHeight_coeff_eq {p : K[X]} (hp : p ≠ 0) :
    Finsupp.mulHeight p.toFinsupp.coeff =
      (∏ w : InfinitePlace K, p.gaussNorm w.1 1 ^ w.mult) *
        ∏ᶠ v : FinitePlace K, p.gaussNorm v.1 1 := by
  have hne : (fun j : p.support => p.coeff j) ≠ 0 := fun h =>
    (mem_support_iff.1 (natDegree_mem_support_of_nonzero hp))
      (congrFun h ⟨_, natDegree_mem_support_of_nonzero hp⟩)
  change mulHeight (fun j : p.support => p.coeff j) = _
  rw [NumberField.mulHeight_eq hne]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [← iSup_support_eq_gaussNorm w.1 hp]; rfl
  · exact finprod_congr fun v => by rw [← iSup_support_eq_gaussNorm v.1 hp]; rfl

/-- `4^r (r+2) ≤ 7^(r+1)`. -/
private lemma four_pow_mul_le (r : ℕ) : 4 ^ r * (r + 2) ≤ 7 ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (4 ^ n * n), Nat.zero_le (4 ^ n)]

/-- `2^(r-1) √(r+1) ≤ e^r` for `r ≥ 1`. -/
private lemma const_le_exp (r : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ (r - 1) * √(r + 1) ≤ Real.exp r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero,
    mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  have h7 : (7 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [Real.exp_one_gt_d9]
  calc (2 : ℝ) ^ (s * 2) * ((s + 1 : ℕ) + 1) = 4 ^ s * (s + 2) := by
        rw [mul_comm s, pow_mul]; push_cast; ring
    _ ≤ 7 ^ (s + 1) := by exact_mod_cast four_pow_mul_le s
    _ ≤ (Real.exp 1 ^ 2) ^ (s + 1) := by gcongr
    _ = Real.exp (2 * (s + 1 : ℕ)) := by
        rw [← pow_mul, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- The multiplicative form of the one-variable Gelfond inequality for `P = (X - x)^i Q`:
`H(x)^i H(Q) ≤ c^{[K:ℚ]} H(P)`, where `c` bounds the archimedean constants. -/
private lemma mulHeight₁_pow_mul_le {x : K} {i : ℕ} {Q : K[X]} (hQ : Q ≠ 0) {c : ℝ}
    (hc : 2 ^ Q.natDegree * √(((X - C x) ^ i * Q).natDegree + 1) ≤ c) :
    mulHeight₁ x ^ i * Finsupp.mulHeight Q.toFinsupp.coeff ≤
      c ^ Module.finrank ℚ K * Finsupp.mulHeight ((X - C x) ^ i * Q).toFinsupp.coeff := by
  have hP : (X - C x) ^ i * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero x)) hQ
  have h1 : ![x ^ i, (1 : K)] ≠ 0 := fun h => one_ne_zero (congrFun h 1)
  have hq : (fun j : Q.support => Q.coeff j) ≠ 0 := fun h =>
    (mem_support_iff.1 (natDegree_mem_support_of_nonzero hQ))
      (congrFun h ⟨_, natDegree_mem_support_of_nonzero hQ⟩)
  have hz : (fun a : Fin 2 × Q.support => ![x ^ i, (1 : K)] a.1 * Q.coeff a.2) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hq
    exact mul_ne_zero one_ne_zero hj (congrFun h (1, j))
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  change _ * mulHeight (fun j : Q.support => Q.coeff j) ≤ _
  rw [← mulHeight₁_pow, mulHeight₁_eq_mulHeight, ← mulHeight_fun_mul_eq h1 hq,
    NumberField.mulHeight_eq hz, mulHeight_coeff_eq hP]
  have hpl (v : AbsoluteValue K ℝ) :
      ⨆ a : Fin 2 × Q.support, v (![x ^ i, (1 : K)] a.1 * Q.coeff a.2) =
        max (v x) 1 ^ i * Q.gaussNorm v 1 := by
    rw [Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v ![x ^ i, (1 : K)]
      (fun j : Q.support => Q.coeff j), iSup_vecCons, iSup_support_eq_gaussNorm v hQ, map_pow,
      map_one]
    rcases le_total (v x) 1 with h | h
    · rw [max_eq_right (pow_le_one₀ (v.nonneg x) h), max_eq_right h, one_pow]
    · rw [max_eq_left (one_le_pow₀ h), max_eq_left h]
  have hfin : (∏ᶠ v : FinitePlace K,
      ⨆ a : Fin 2 × Q.support, v (![x ^ i, (1 : K)] a.1 * Q.coeff a.2)) =
        ∏ᶠ v : FinitePlace K, ((X - C x) ^ i * Q).gaussNorm v.1 1 := by
    refine finprod_congr fun v => ?_
    have hv : IsNonarchimedean v.1 := fun a b => FinitePlace.add_le v a b
    refine (hpl v.1).trans ?_
    rw [gaussNorm_mul hv one_pos, gaussNorm_X_sub_C_pow hv]
  rw [hfin, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (finprod_nonneg fun v => gaussNorm_nonneg _ _ zero_le_one)
  have hd : ∑ w : InfinitePlace K, w.mult = Module.finrank ℚ K := by
    rw [← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  rw [← hd, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (Real.iSup_nonneg fun _ => w.1.nonneg _) _)
    fun w _ => ?_
  refine ((congrArg (· ^ w.mult) (hpl w.1)).trans_le ?_)
  rw [← mul_pow]
  refine pow_le_pow_left₀ (mul_nonneg (pow_nonneg (le_max_of_le_right zero_le_one) _)
    (gaussNorm_nonneg _ _ zero_le_one)) ?_ _
  refine (arch_bound w x i Q).trans ?_
  exact mul_le_mul_of_nonneg_right hc (gaussNorm_nonneg _ _ zero_le_one)

/-- **Roth's lemma in one variable**, multiplicatively: `H(x)^i ≤ e^{r [K:ℚ]} H(P)` in heights
relative to `K`. -/
private lemma mulHeight₁_pow_le_exp_pow_mul {P : K[X]} (hP : P ≠ 0) {r : ℕ}
    (hdeg : P.natDegree ≤ r) {x : K} {i : ℕ} (hzero : ∀ j < i, (hasseDeriv j P).eval x = 0) :
    mulHeight₁ x ^ i ≤ Real.exp r ^ Module.finrank ℚ K * Finsupp.mulHeight P.toFinsupp.coeff := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (Real.one_le_exp (by positivity)))
      (one_le_finsuppMulHeight _)
  obtain ⟨Q, rfl⟩ := X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero hzero
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
  have hdegP : ((X - C x) ^ i * Q).natDegree = i + Q.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero x)) hQ, natDegree_pow, natDegree_X_sub_C,
      mul_one]
  have hc : 2 ^ Q.natDegree * √(((X - C x) ^ i * Q).natDegree + 1) ≤ Real.exp r :=
    (mul_le_mul (pow_le_pow_right₀ one_le_two (by omega))
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hdeg 1)) (by positivity)
      (by positivity)).trans (const_le_exp r (by omega))
  exact (le_mul_of_one_le_right (by positivity) (one_le_finsuppMulHeight _)).trans
    (mulHeight₁_pow_mul_le hQ hc)

end Helpers

/-- **Roth's lemma in one variable.** Let `P ≠ 0` be a polynomial of degree at most `r` over a
number field `K`, and `x ∈ K`. If the divided derivatives `hasseDeriv j P` vanish at `x` for
`j < i` and `hasseDeriv i P` does not, then `i · h(x) ≤ h(P) + r`. Here `h` is the absolute
logarithmic Weil height, i.e. Mathlib's height relative to `K` divided by `[K : ℚ]`. -/
@[faltings "lem_bvr_roth_one_variable"]
public theorem mul_logHeight₁_le_logHeight_add_of_hasseDeriv
    {K : Type*} [Field K] [NumberField K] {P : K[X]} (hP : P ≠ 0) {r : ℕ}
    (hdeg : P.natDegree ≤ r) {x : K} {i : ℕ}
    (hzero : ∀ j < i, (hasseDeriv j P).eval x = 0) (_hne : (hasseDeriv i P).eval x ≠ 0) :
    i * (Height.logHeight₁ x / Module.finrank ℚ K) ≤
      Finsupp.logHeight P.toFinsupp.coeff / Module.finrank ℚ K + r := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have h := Real.log_le_log (pow_pos (mulHeight₁_pos x) i)
    (mulHeight₁_pow_le_exp_pow_mul hP hdeg hzero)
  rw [Real.log_mul (by positivity) (zero_lt_one.trans_le (one_le_finsuppMulHeight _)).ne',
    Real.log_pow, Real.log_pow, Real.log_exp, ← logHeight₁_eq_log_mulHeight₁,
    ← mulHeight_finsupp_eq, ← Finsupp.logHeight] at h
  rw [mul_div_assoc', div_add' _ _ _ hd.ne', div_le_div_iff_of_pos_right hd]
  linarith

end Faltings


/-!
# Roth's lemma in one variable, `ε`-form

Let `P ≠ 0` be a polynomial of degree at most `r` with algebraic coefficients, let `ς⁰` be
algebraic, and let `i*` be the order of vanishing of `P` at `ς⁰` measured by the divided
derivatives: `∂ᵢ P (ς⁰) = 0` for `i < i*` and `∂_{i*} P (ς⁰) ≠ 0`. If `ε > 0` and the height of
`ς⁰` is large compared with that of `P`, in the sense that `r h(ς⁰) ≥ ε⁻¹ (h(P) + r)` for the
absolute logarithmic Weil heights, then `i* / r ≤ ε`.

## Main results

* `Faltings.le_mul_of_hasseDeriv_eval_ne_zero`: the `ε`-form of Roth's lemma in one variable.

## Implementation notes

All coefficients of `P` and the point `ς⁰` lie in one number field `K`, and the statement is
made over an arbitrary such `K`. The divided derivative `∂ᵢ = (1/i!) dⁱ/dςⁱ` is
`Polynomial.hasseDeriv i`. Mathlib's heights over `K` are relative to `K`, so the absolute
height of `ς⁰` is `Height.logHeight₁ ς⁰ / [K : ℚ]` and the absolute height of a nonzero
polynomial `P` is `Finsupp.logHeight P.toFinsupp.coeff / [K : ℚ]`, the height of its
coefficients indexed by the support of `P`. Both quotients do not depend on the choice of `K`.
The conclusion `i* / r ≤ ε` is stated as `i* ≤ ε r`; the two agree for `r > 0`, and for
`r = 0` the latter is the stronger (and still true) statement.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9
-/

open Polynomial

namespace Faltings

/-- **Roth's lemma in one variable, `ε`-form.** Let `P ≠ 0` be a polynomial of degree at most `r`
over a number field `K`, and `ξ ∈ K`. Suppose the divided derivatives `hasseDeriv j P` vanish at
`ξ` for `j < i` and `hasseDeriv i P` does not. If `ε > 0` and `ε⁻¹ (h(P) + r) ≤ r h(ξ)`, where
`h` is the absolute logarithmic Weil height (Mathlib's height relative to `K` divided by
`[K : ℚ]`), then `i ≤ ε r`. -/
@[faltings "lem_bvr_roth_one_variable_epsilon"]
public theorem le_mul_of_hasseDeriv_eval_ne_zero {K : Type*} [Field K] [NumberField K]
    {P : K[X]} (hP : P ≠ 0) {r : ℕ} (hdeg : P.natDegree ≤ r) {ξ : K} {i : ℕ}
    (hzero : ∀ j < i, (hasseDeriv j P).eval ξ = 0) (hne : (hasseDeriv i P).eval ξ ≠ 0)
    {ε : ℝ} (hε : 0 < ε)
    (hheight : ε⁻¹ * (Finsupp.logHeight P.toFinsupp.coeff / Module.finrank ℚ K + r) ≤
      r * (Height.logHeight₁ ξ / Module.finrank ℚ K)) :
    (i : ℝ) ≤ ε * r := by
  have hd : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  have hmain := mul_logHeight₁_le_logHeight_add_of_hasseDeriv hP hdeg hzero hne
  have hp0 := div_nonneg (zero_le_finsuppLogHeight P.toFinsupp.coeff) hd
  have hx0 := div_nonneg (Height.zero_le_logHeight₁ ξ) hd
  set hx := Height.logHeight₁ ξ / Module.finrank ℚ K
  set hp := Finsupp.logHeight P.toFinsupp.coeff / Module.finrank ℚ K
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : i = 0 := by
      by_contra h
      exact hne (by rw [hasseDeriv_eq_zero_of_lt_natDegree P i (by omega)]; simp)
    simp [this]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [inv_mul_le_iff₀ hε] at hheight
  have hxpos : 0 < hx := by
    refine hx0.lt_of_ne fun h => ?_
    rw [← h, mul_zero, mul_zero] at hheight
    linarith
  exact le_of_mul_le_mul_right (by nlinarith) hxpos

end Faltings
