module
public import Mordell.Height.Affine.Basic
public import Mordell.Height.Affine.LocalSize.Eval
public import Mordell.NumberField.LocalWeight

/-!
# The height of a value of a polynomial

Let `K` be a number field, `f ∈ K[X_t : t ∈ σ]` a polynomial in finitely many variables with
`deg_{X_t} f ≤ e_t` for every `t`, and `a ∈ K^σ`. Then
`h(f(a)) ≤ h_aff(f) + log #f + ∑_t e_t h(a_t)`,
where `h` is the absolute logarithmic height of an element of `K`, `h_aff` is the affine height
`Faltings.affineLogHeight` of the coefficient vector of `f`, and `#f` is the number
`Faltings.MvPolynomial.monomialCount f` of monomials of `f`. Place by place,
`|f(a)|_v ≤ #f ^ κ_v · |f|_v · ∏_t max(1, |a_t|_v) ^ {e_t}`, and summing `log⁺` over the places
gives the bound.

## Main results

* `Faltings.NumberField.logHeight₁_eval_le`: the height of `f(a)` is at most
  `h_aff(f) + log #f + ∑_t e_t h(a_t)`.

## Implementation notes

The absolute height of `x ∈ K` is written `Height.logHeight₁ x / [K : ℚ]`: Mathlib's
`Height.logHeight₁` on a number field is `∑_{v | ∞} n_v log⁺ ‖x‖_v + ∑ᶠ_{v ∤ ∞} log⁺ ‖x‖_v`
(`NumberField.logHeight₁_eq`), and dividing by `[K : ℚ]` gives Bombieri's normalisation, the one
used by `Faltings.affineLogHeight`. A polynomial `f : MvPolynomial σ K` enters
`Faltings.affineLogHeight` through its coefficient vector
`AddMonoidAlgebra.coeff f : (σ →₀ ℕ) →₀ K`. For `f = 0` both sides make sense, with `log 0 = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8
-/

namespace Faltings.NumberField

open _root_.NumberField Module Real

section Helpers

variable {K : Type*} [Field K] [NumberField K]

private lemma finrank_pos' : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos

private lemma posLog_normalizedAbs_inl (w : InfinitePlace K) (x : K) :
    log⁺ (normalizedAbs (.inl w) x) = (w.mult : ℝ) / finrank ℚ K * log⁺ (w x) := by
  rw [normalizedAbs_inl]
  exact posLog_rpow (by linarith [apply_nonneg w x]) (by have := finrank_pos' (K := K); positivity)

private lemma posLog_normalizedAbs_inr (w : FinitePlace K) (x : K) :
    log⁺ (normalizedAbs (.inr w) x) = 1 / finrank ℚ K * log⁺ (w x) := by
  rw [normalizedAbs_inr]
  exact posLog_rpow (by linarith [apply_nonneg w x]) (by have := finrank_pos' (K := K); positivity)

/-- The absolute height as a sum of `log⁺` of normalised absolute values, the finite places
being restricted to a finite set outside of which `|y|_v ≤ 1`. -/
private lemma logHeight₁_div_eq (y : K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, v y ≤ 1) :
    Height.logHeight₁ y / finrank ℚ K =
      ∑ w, log⁺ (normalizedAbs (.inl w) y) + ∑ v ∈ S, log⁺ (normalizedAbs (.inr v) y) := by
  rw [NumberField.logHeight₁_eq, finsum_eq_sum_of_support_subset (s := S)]
  · simp only [posLog_normalizedAbs_inl, posLog_normalizedAbs_inr, add_div, Finset.sum_div]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
  · intro v hv
    by_contra h
    exact hv ((posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (apply_nonneg _ _)]; exact hS v h))

/-- The affine height bounds the sum of `log⁺` of the normalised sizes. -/
private lemma sum_le_affineLogHeight {α : Type*} (c : α →₀ K) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, ∀ m, v (c m) ≤ 1) :
    ∑ w, log⁺ (⨆ m : c.support, normalizedAbs (.inl w) (c m)) +
        ∑ v ∈ S, log⁺ (⨆ m : c.support, normalizedAbs (.inr v) (c m)) ≤
      Faltings.affineLogHeight c := by
  have hd := finrank_pos' (K := K)
  have key : ∀ (g : c.support → ℝ) (r : ℝ), (∀ m, 0 ≤ g m) → 0 ≤ r →
      log⁺ (⨆ m, g m ^ r) ≤ r * log⁺ (⨆ m, g m) := by
    intro g r hg hr
    have h0 : 0 ≤ ⨆ m, g m := Real.iSup_nonneg hg
    rw [← posLog_rpow (by linarith) hr]
    refine posLog_le_posLog (by linarith [Real.iSup_nonneg fun m => Real.rpow_nonneg (hg m) r])
      (Real.iSup_le (fun m => Real.rpow_le_rpow (hg m)
        (le_ciSup (Set.finite_range _).bddAbove m) hr) (Real.rpow_nonneg h0 r))
  simp only [normalizedAbs_inl, normalizedAbs_inr]
  unfold Faltings.affineLogHeight
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · rw [add_div, Finset.sum_div, Finset.sum_div]
    refine add_le_add (Finset.sum_le_sum fun w _ => ?_) (Finset.sum_le_sum fun v _ => ?_)
    · refine (key _ _ (fun _ => apply_nonneg _ _) (by positivity)).trans (le_of_eq ?_)
      ring
    · refine (key _ _ (fun _ => apply_nonneg _ _) (by positivity)).trans (le_of_eq ?_)
      ring
  · intro v hv
    by_contra h
    refine hv ((posLog_eq_zero_iff _).2 ?_)
    rw [abs_of_nonneg (Real.iSup_nonneg fun _ => apply_nonneg _ _)]
    exact Real.iSup_le (fun m => hS v h m) zero_le_one

/-- The place-by-place bound,
`log⁺ |f(a)|_v ≤ κ_v log #f + log max(1, |f|_v) + ∑_t e_t log⁺ |a_t|_v`. -/
private lemma posLog_normalizedAbs_eval_le {σ : Type*} [Fintype σ]
    (v : InfinitePlace K ⊕ FinitePlace K) (f : _root_.MvPolynomial σ K) (e : σ → ℕ)
    (hf : ∀ t, f.degreeOf t ≤ e t) (a : σ → K) :
    log⁺ (normalizedAbs v (_root_.MvPolynomial.eval a f)) ≤
      localWeight K v * log (Faltings.MvPolynomial.monomialCount f) +
        log⁺ (⨆ m : f.support, normalizedAbs v (f.coeff m)) +
        ∑ t, (e t : ℝ) * log⁺ (normalizedAbs v (a t)) := by
  have h := normalizedAbs_eval_le v f e hf a
  simp only at h
  change normalizedAbs v _ ≤ _ * (⨆ m : f.support, normalizedAbs v _) *
    ∏ t, max 1 (normalizedAbs v (a t)) ^ e t at h
  have hκ : 0 ≤ localWeight K v := by cases v <;> simp only [localWeight] <;> positivity
  have hN : (0 : ℝ) ≤ (Faltings.MvPolynomial.monomialCount f : ℝ) := Nat.cast_nonneg _
  refine (posLog_le_posLog
      (by linarith [normalizedAbs_nonneg v (_root_.MvPolynomial.eval a f)]) h).trans
    ((posLog_mul).trans (add_le_add ((posLog_mul).trans (add_le_add_left ?_ _)) ?_))
  · rw [posLog_rpow (by linarith) hκ]
    rcases Nat.eq_zero_or_pos (Faltings.MvPolynomial.monomialCount f) with h0 | h0
    · simp [h0]
    · rw [posLog_eq_log (by rw [abs_of_nonneg hN]; exact_mod_cast h0)]
  · refine (posLog_prod _ _).trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
    rw [posLog_pow, posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact le_max_left _ _),
      posLog_eq_log_max_one (normalizedAbs_nonneg _ _)]

/-- Finitely many elements of `K` all have `|x|_v ≤ 1` outside a finite set of finite places. -/
private lemma exists_finset_forall_le_one (T : Finset K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ x ∈ T, v x ≤ 1 := by
  classical
  have hfin : ∀ x : K, {v : FinitePlace K | 1 < v x}.Finite := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [not_lt.2 zero_le_one]
    · exact (@Set.toFinite _ _ (FinitePlace.hasFiniteMulSupport hx)).subset
        fun v hv => ne_of_gt hv
  refine ⟨T.biUnion fun x => (hfin x).toFinset, fun v hv x hx => not_lt.1 fun h => hv ?_⟩
  exact Finset.mem_biUnion.2 ⟨x, hx, (hfin x).mem_toFinset.2 h⟩

/-- The local weights summed over the infinite places and any finite set of finite places. -/
private lemma sum_localWeight_eq_one (S : Finset (FinitePlace K)) :
    ∑ w, localWeight K (.inl w) + ∑ v ∈ S, localWeight K (.inr v) = 1 := by
  have h := finsum_localWeight K
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.map .inl) _
    (by rintro (w | v) h <;> simp_all [localWeight])] at h
  simpa [localWeight] using h

/-- At a finite place where every coefficient of `f` and every `a t` has absolute value `≤ 1`,
so does `f(a)`. -/
private lemma finitePlace_eval_le_one {σ : Type*} [Finite σ] (v : FinitePlace K)
    (f : _root_.MvPolynomial σ K) (e : σ → ℕ) (hf : ∀ t, f.degreeOf t ≤ e t) (a : σ → K)
    (hc : ∀ m, v (f.coeff m) ≤ 1) (ha : ∀ t, v (a t) ≤ 1) :
    v (_root_.MvPolynomial.eval a f) ≤ 1 := by
  have := Fintype.ofFinite σ
  have hr : (0 : ℝ) < 1 / finrank ℚ K := by have := finrank_pos' (K := K); positivity
  have h := normalizedAbs_eval_le (.inr v) f e hf a
  simp only at h
  change normalizedAbs (.inr v) _ ≤ _ * (⨆ m : f.support, normalizedAbs (.inr v) _) *
    ∏ t, max 1 (normalizedAbs (.inr v) (a t)) ^ e t at h
  have h1 : ∀ t, max 1 (normalizedAbs (.inr v) (a t)) = 1 := fun t =>
    max_eq_left (Real.rpow_le_one (apply_nonneg _ _) (ha t) hr.le)
  simp only [h1, one_pow, Finset.prod_const_one, mul_one,
    localWeight, Real.rpow_zero, one_mul] at h
  refine not_lt.1 fun hlt => (Real.one_lt_rpow hlt hr).not_ge (h.trans ?_)
  exact Real.iSup_le (fun m => Real.rpow_le_one (apply_nonneg _ _) (hc m) hr.le) zero_le_one

end Helpers

/-- For a polynomial `f` over a number field `K` in finitely many variables `X_t` with
`deg_{X_t} f ≤ e t`, and `a : σ → K`, the absolute height of `f(a)` satisfies
`h(f(a)) ≤ h_aff(f) + log #f + ∑_t e_t h(a_t)`, where `h(x) = Height.logHeight₁ x / [K : ℚ]`,
`h_aff = Faltings.affineLogHeight` and `#f = Faltings.MvPolynomial.monomialCount f`. -/
@[faltings "lem_bvs_height_of_polynomial_value"]
public theorem logHeight₁_eval_le {K : Type*} [Field K] [NumberField K] {σ : Type*} [Fintype σ]
    (f : _root_.MvPolynomial σ K) (e : σ → ℕ) (hf : ∀ t, f.degreeOf t ≤ e t) (a : σ → K) :
    Height.logHeight₁ (_root_.MvPolynomial.eval a f) / finrank ℚ K ≤
      affineLogHeight (AddMonoidAlgebra.coeff f) +
        log (Faltings.MvPolynomial.monomialCount f) +
        ∑ t, (e t : ℝ) * (Height.logHeight₁ (a t) / finrank ℚ K) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_forall_le_one (f.support.image f.coeff ∪ Finset.univ.image a)
  have hcoeff : ∀ v ∉ S, ∀ m, v (f.coeff m) ≤ 1 := fun v hv m => by
    by_cases hm : m ∈ f.support
    · exact hS v hv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))
    · simp [_root_.MvPolynomial.notMem_support_iff.1 hm]
  have ha : ∀ v ∉ S, ∀ t, v (a t) ≤ 1 := fun v hv t =>
    hS v hv _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
  have hP := fun v => posLog_normalizedAbs_eval_le (K := K) v f e hf a
  rw [logHeight₁_div_eq _ S fun v hv =>
    finitePlace_eval_le_one v f e hf a (hcoeff v hv) (ha v hv)]
  calc ∑ w, log⁺ (normalizedAbs (.inl w) (_root_.MvPolynomial.eval a f)) +
        ∑ v ∈ S, log⁺ (normalizedAbs (.inr v) (_root_.MvPolynomial.eval a f))
      ≤ ∑ w, (localWeight K (.inl w) * log (Faltings.MvPolynomial.monomialCount f) +
            log⁺ (⨆ m : f.support, normalizedAbs (.inl w) (f.coeff m)) +
            ∑ t, (e t : ℝ) * log⁺ (normalizedAbs (.inl w) (a t))) +
        ∑ v ∈ S, (localWeight K (.inr v) * log (Faltings.MvPolynomial.monomialCount f) +
            log⁺ (⨆ m : f.support, normalizedAbs (.inr v) (f.coeff m)) +
            ∑ t, (e t : ℝ) * log⁺ (normalizedAbs (.inr v) (a t))) :=
        add_le_add (Finset.sum_le_sum fun w _ => hP _) (Finset.sum_le_sum fun v _ => hP _)
    _ = (∑ w, localWeight K (.inl w) + ∑ v ∈ S, localWeight K (.inr v)) *
          log (Faltings.MvPolynomial.monomialCount f) +
        (∑ w, log⁺ (⨆ m : f.support, normalizedAbs (.inl w) (f.coeff m)) +
          ∑ v ∈ S, log⁺ (⨆ m : f.support, normalizedAbs (.inr v) (f.coeff m))) +
        ∑ t, (e t : ℝ) * (∑ w, log⁺ (normalizedAbs (.inl w) (a t)) +
          ∑ v ∈ S, log⁺ (normalizedAbs (.inr v) (a t))) := by
        simp only [Finset.sum_add_distrib, add_mul, Finset.sum_mul, Finset.mul_sum, mul_add]
        rw [Finset.sum_comm (s := S),
          Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace K)))]
        ring
    _ ≤ Faltings.affineLogHeight (AddMonoidAlgebra.coeff f) +
          log (Faltings.MvPolynomial.monomialCount f) +
        ∑ t, (e t : ℝ) * (Height.logHeight₁ (a t) / finrank ℚ K) := by
        rw [sum_localWeight_eq_one, one_mul, add_comm (log _)]
        simp only [← logHeight₁_div_eq _ S (fun v hv => ha v hv _)]
        gcongr
        exact sum_le_affineLogHeight (AddMonoidAlgebra.coeff f) S hcoeff

end Faltings.NumberField
