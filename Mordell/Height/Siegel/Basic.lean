module
public import Mordell.Height.IntegralVector
public import Mordell.Height.Siegel.Normalise

/-!
# Siegel's lemma over a number field

Let `K` be a number field. There is a constant `c ≥ 0`, depending only on `K`, with the following
property. Let `(L_i)_{i ∈ κ}` be linear forms in `N` variables with coefficients in `K`, spanning a
subspace of dimension `r < N` of the space of linear forms, and let `H ≥ 0` bound the absolute
logarithmic heights `h(L_i)` of the nonzero `L_i`. Then the system `L_i(x) = 0` has a nonzero
solution `x ∈ K^N` with
`h(x) ≤ r / (N - r) · (H + log N) + c · N / (N - r)`.
The proof normalises `r` independent forms to integral ones of controlled house, applies the
house-bounded Siegel lemma over the ring of integers
(`NumberField.house.exists_ne_zero_int_vec_house_le`), and bounds the height of the integral
solution by the logarithm of its largest house.

## Main results

* `Faltings.exists_ne_zero_dotProduct_eq_zero_logHeight_le`: Siegel's lemma in projective-height
  form over a number field.

## Implementation notes

A linear form in the variables indexed by the finite type `ι` is its coefficient vector
`L i : ι → K`, and `L_i(x)` is `L i ⬝ᵥ x`; the rank `r` is
`Module.finrank K (Submodule.span K (Set.range L))`. The absolute height of a vector `a : ι → K`
is `Height.logHeight a / [K : ℚ]`, the normalisation in which the local weights sum to one. The
family of forms is indexed by an arbitrary type `κ`: only the span matters. The constant `c` is
chosen before `ι` and `κ`, so it is uniform in `N` and in the number of forms.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8
-/

namespace Faltings

universe u v w x

open NumberField Matrix

/-- The house-bounded Siegel lemma over `𝓞 K`, with a constant `c ≥ 1` quantified before the
data. -/
private lemma exists_const_house_siegel (K : Type x) [Field K] [NumberField K] :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {α : Type w} {β : Type u} [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)),
      a ≠ 0 → 0 < Fintype.card α → Fintype.card α < Fintype.card β → ∀ {A : ℝ},
      (∀ k l, house (algebraMap (𝓞 K) K (a k l)) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤
        c * (c * Fintype.card β * A) ^ ((Fintype.card α : ℝ) /
          (Fintype.card β - Fintype.card α)) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, ∀ {α : Type w} {β : Type u} [Fintype α] [Fintype β]
      (a : Matrix α β (𝓞 K)), a ≠ 0 → 0 < Fintype.card α → Fintype.card α < Fintype.card β →
      ∀ {A : ℝ}, (∀ k l, house (algebraMap (𝓞 K) K (a k l)) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤
        c₀ * (c₀ * Fintype.card β * A) ^ ((Fintype.card α : ℝ) /
          (Fintype.card β - Fintype.card α)) :=
    ⟨_, fun a ha h0 hpq A habs => house.exists_ne_zero_int_vec_house_le K a ha h0 hpq rfl habs rfl⟩
  refine ⟨max 1 |c₀|, le_max_left _ _, fun {α β} _ _ a ha h0 hpq A habs => ?_⟩
  obtain ⟨ξ, hξ, haξ, hξb⟩ := hc₀ a ha h0 hpq habs
  obtain ⟨k, l, -⟩ : ∃ k l, a k l ≠ 0 := by by_contra! h; exact ha (Matrix.ext h)
  have hA : 0 ≤ A := (house_nonneg _).trans (habs k l)
  set e : ℝ := (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α)
  refine ⟨ξ, hξ, haξ, fun l ↦ (hξb l).trans ?_⟩
  calc c₀ * (c₀ * Fintype.card β * A) ^ e ≤ |c₀| * |c₀ * Fintype.card β * A| ^ e := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (Real.abs_rpow_le_abs_rpow _ _) (abs_nonneg _)
    _ ≤ max 1 |c₀| * (max 1 |c₀| * Fintype.card β * A) ^ e := by
        have he : 0 ≤ e := div_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hpq.le))
        rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg hA]
        gcongr <;> exact le_max_right _ _

/-- A vector orthogonal to a set of vectors is orthogonal to their span. -/
private lemma dotProduct_eq_zero_of_mem_span {K ι : Type*} [Field K] [Fintype ι]
    {s : Set (ι → K)} {x : ι → K} (h : ∀ v ∈ s, v ⬝ᵥ x = 0) {w : ι → K}
    (hw : w ∈ Submodule.span K s) : w ⬝ᵥ x = 0 :=
  Submodule.span_le (p := LinearMap.ker ((dotProductBilin K K).flip x)).mpr
    (fun v hv ↦ by simpa using h v hv) hw

/-- If the forms `L i` span the zero space, a standard basis vector is a nonzero solution in
`𝓞 K` of the system `L_i(x) = 0` whose coordinates have house at most `1`. -/
private lemma exists_integral_solution_of_finrank_eq_zero {K ι κ : Type*} [Field K]
    [NumberField K] [Fintype ι] [Nonempty ι] (L : κ → ι → K)
    (h0 : Module.finrank K (Submodule.span K (Set.range L)) = 0) :
    ∃ ξ : ι → 𝓞 K, ξ ≠ 0 ∧ (∀ i, L i ⬝ᵥ (fun l ↦ (ξ l : K)) = 0) ∧
      ∀ l, house (ξ l : K) ≤ 1 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hLz (i : κ) : L i = 0 := by
    simpa [Submodule.finrank_eq_zero.mp h0] using
      Submodule.subset_span (R := K) (Set.mem_range_self (f := L) i)
  refine ⟨Pi.single i₀ 1, fun h ↦ by simpa using congrFun h i₀, fun i ↦ by simp [hLz i],
    fun l ↦ ?_⟩
  obtain rfl | hl := eq_or_ne l i₀
  · simpa using (house_intCast (K := K) 1).le
  · simp [hl, show house (0 : K) = 0 by simpa using house_intCast (K := K) 0]

/-- **Siegel's lemma with an integral solution**: the system `L_i(x) = 0` of rank `r < N` with
forms of absolute height at most `H` has a nonzero solution in `𝓞 K` whose coordinates have house
at most `c (c N e^H) ^ (r / (N - r))`, for a constant `c ≥ 1` depending only on `K`. -/
private lemma exists_const_integral_solution (K : Type x) [Field K] [NumberField K] :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {ι : Type u} [Fintype ι] {κ : Type v} (L : κ → ι → K) (H : ℝ),
      Module.finrank K (Submodule.span K (Set.range L)) < Fintype.card ι →
      (∀ i, L i ≠ 0 → Height.logHeight (L i) / Module.finrank ℚ K ≤ H) →
      ∃ ξ : ι → 𝓞 K, ξ ≠ 0 ∧ (∀ i, L i ⬝ᵥ (fun l ↦ (ξ l : K)) = 0) ∧ ∀ l, house (ξ l : K) ≤
        c * (c * Fintype.card ι * Real.exp H) ^
          ((Module.finrank K (Submodule.span K (Set.range L)) : ℝ) /
            (Fintype.card ι - Module.finrank K (Submodule.span K (Set.range L)))) := by
  classical
  obtain ⟨C, hC1, hnorm⟩ := exists_isIntegral_smul_house_le.{u} K
  obtain ⟨c₀, hc₀, hsieg⟩ := exists_const_house_siegel.{u, max u x, x} K
  refine ⟨c₀ * C, one_le_mul_of_one_le_of_one_le hc₀ hC1, fun {ι} _ {κ} L H hr hL => ?_⟩
  set r := Module.finrank K (Submodule.span K (Set.range L))
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨ξ, hξ0, hξL, hξ1⟩ := exists_integral_solution_of_finrank_eq_zero L h0
    refine ⟨ξ, hξ0, hξL, fun l ↦ ?_⟩
    rw [h0, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    exact (hξ1 l).trans (one_le_mul_of_one_le_of_one_le hc₀ hC1)
  · obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent K (Set.range L)
    have : Fintype b := hbli.setFinite.fintype
    have hcardb : Fintype.card b = r := by
      rw [← Set.toFinset_card, ← finrank_span_set_eq_card hbli, hbspan]
    have hb0 (v : b) : (v : ι → K) ≠ 0 := hbli.ne_zero v
    choose lam hlam0 hlam using fun v : b ↦ hnorm (v : ι → K) (hb0 v)
    let a : Matrix b ι (𝓞 K) := fun v j ↦ ⟨lam v * (v : ι → K) j, (hlam v j).1⟩
    have ha : a ≠ 0 := by
      obtain ⟨v⟩ : Nonempty b := Fintype.card_pos_iff.mp (hcardb ▸ hpos)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp (hb0 v)
      exact fun h ↦ mul_ne_zero (hlam0 v) hj congr(($h v j : K))
    have habs (v : b) (j : ι) : house (algebraMap (𝓞 K) K (a v j)) ≤ C * Real.exp H := by
      obtain ⟨i, hi⟩ := hbL v.2
      refine (hlam v j).2.trans (by gcongr; exact hi ▸ hL i (hi ▸ hb0 v))
    obtain ⟨ξ, hξ0, haξ, hξb⟩ := hsieg a ha (hcardb ▸ hpos) (hcardb ▸ hr) habs
    have hsol (v : ι → K) (hv : v ∈ b) : v ⬝ᵥ (fun l ↦ (ξ l : K)) = 0 := by
      have h : lam ⟨v, hv⟩ * (v ⬝ᵥ fun l ↦ (ξ l : K)) = 0 := by
        have h := congr(algebraMap (𝓞 K) K ($haξ ⟨v, hv⟩))
        simp only [mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h
        rw [dotProduct, Finset.mul_sum, ← h]
        exact Finset.sum_congr rfl fun j _ ↦ (mul_assoc _ _ _).symm
      exact (mul_eq_zero.mp h).resolve_left (hlam0 _)
    refine ⟨ξ, hξ0, fun i ↦ dotProduct_eq_zero_of_mem_span hsol
      (hbspan ▸ Submodule.subset_span ⟨i, rfl⟩), fun l ↦ (hξb l).trans ?_⟩
    rw [hcardb]
    set e : ℝ := r / (Fintype.card ι - r)
    have he : 0 ≤ e := div_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hr.le))
    calc c₀ * (c₀ * Fintype.card ι * (C * Real.exp H)) ^ e
        ≤ c₀ * C * (c₀ * C * Fintype.card ι * Real.exp H) ^ e := by
          rw [show c₀ * C * Fintype.card ι * Real.exp H = c₀ * Fintype.card ι * (C * Real.exp H)
            by ring]
          gcongr; exact le_mul_of_one_le_right (by linarith) hC1

/-- **Siegel's lemma** over a number field `K`: there is `c ≥ 0` such that for any family of
linear forms `L i : ι → K` (`ι` finite, `N = card ι`) spanning a space of dimension `r < N`, and
any `H ≥ 0` bounding the absolute heights `Height.logHeight (L i) / [K : ℚ]` of the nonzero forms,
there is `x ≠ 0` with `L i ⬝ᵥ x = 0` for all `i` and
`Height.logHeight x / [K : ℚ] ≤ r / (N - r) * (H + log N) + c * N / (N - r)`. -/
@[faltings "thm_bvs_siegel_lemma"]
public theorem exists_ne_zero_dotProduct_eq_zero_logHeight_le (K : Type*) [Field K]
    [NumberField K] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ι : Type u} [Fintype ι] {κ : Type v} (L : κ → ι → K) (H : ℝ),
      Module.finrank K (Submodule.span K (Set.range L)) < Fintype.card ι → 0 ≤ H →
      (∀ i, L i ≠ 0 → Height.logHeight (L i) / Module.finrank ℚ K ≤ H) →
      ∃ x : ι → K, x ≠ 0 ∧ (∀ i, L i ⬝ᵥ x = 0) ∧
        Height.logHeight x / Module.finrank ℚ K ≤
          (Module.finrank K (Submodule.span K (Set.range L)) : ℝ) /
              (Fintype.card ι - Module.finrank K (Submodule.span K (Set.range L))) *
            (H + Real.log (Fintype.card ι)) +
          c * Fintype.card ι /
            (Fintype.card ι - Module.finrank K (Submodule.span K (Set.range L))) := by
  obtain ⟨c₀, hc₀, hsol⟩ := exists_const_integral_solution.{u, v} K
  refine ⟨Real.log c₀, Real.log_nonneg hc₀, fun {ι} _ {κ} L H hr hH hL => ?_⟩
  obtain ⟨ξ, hξ0, hξL, hξb⟩ := hsol L H hr hL
  set r := Module.finrank K (Submodule.span K (Set.range L))
  set N := Fintype.card ι
  have hNr : (0 : ℝ) < N - r := sub_pos.mpr (by exact_mod_cast hr)
  have hN : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hN)
  refine ⟨_, fun h ↦ hξ0 (funext fun l ↦ by simpa using congrFun h l), hξL,
    (logHeight_div_finrank_le_log_iSup_house ξ hξ0).trans ?_⟩
  have hB : 1 ≤ c₀ * (c₀ * N * Real.exp H) ^ ((r : ℝ) / (N - r)) :=
    one_le_mul_of_one_le_of_one_le hc₀ (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hc₀ (by exact_mod_cast hN)) (Real.one_le_exp hH))
      (by positivity))
  calc Real.log (⨆ l, house (ξ l : K))
      ≤ Real.log (c₀ * (c₀ * N * Real.exp H) ^ ((r : ℝ) / (N - r))) := by
        rcases (Real.iSup_nonneg fun l ↦ house_nonneg (ξ l : K)).eq_or_lt with h | h
        · rw [← h, Real.log_zero]; exact Real.log_nonneg hB
        · exact Real.log_le_log h (ciSup_le hξb)
    _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hN.ne',
          Real.log_exp]
        field_simp
        ring

end Faltings
