module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mathlib
public import Mordell.Attr
public import Mordell.NumberField.NormalizedAbv.Integer

/-!
# The normalized absolute values are absolute values

Let `K` be a number field and `w` a place of `K`. Bombieri's normalized absolute value
`|x|_w = |N_{K_w/ℚ_p}(x)|_p ^ (1/[K:ℚ])`, `Faltings.NumberFieldPlace.normalizedAbv w`, is an
absolute value on `K`: it is multiplicative, vanishes exactly at `0`, and satisfies the triangle
inequality.
At a finite place it is a positive power of the `𝔭`-adic absolute value, hence even
non-archimedean; at an infinite place defined by `σ` it is `|σ(·)| ^ t` with
`t = n_w / [K:ℚ] ∈ (0, 1]`, and `(a + b) ^ t ≤ a ^ t + b ^ t` for `a, b ≥ 0`.

## Main results

* `Faltings.NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv`: there is an
  `AbsoluteValue K ℝ` whose underlying function is `Faltings.NumberFieldPlace.normalizedAbv w`.
* `Faltings.NumberFieldPlace.normalizedAbv_mul`, `Faltings.NumberFieldPlace.normalizedAbv_prod`:
  multiplicativity of `|·|_w`.

## Implementation notes

The three properties are packaged as Mathlib's `AbsoluteValue K ℝ` (multiplicativity,
`v x = 0 ↔ x = 0`, subadditivity, nonnegativity), with its underlying function pinned to be
`Faltings.NumberFieldPlace.normalizedAbv w`; the properties are then `map_mul`,
`AbsoluteValue.eq_zero` and `AbsoluteValue.add_le` of that absolute value.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

namespace Faltings

open NumberField

/-- A power `x ↦ v x ^ t`, `0 < t ≤ 1`, of a real absolute value is an absolute value. -/
private noncomputable def absoluteValueRpow {R : Type*} [Semiring R] (v : AbsoluteValue R ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : AbsoluteValue R ℝ where
  toFun x := v x ^ t
  map_mul' x y := by simp only [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) t
  eq_zero' x := by simp [Real.rpow_eq_zero (v.nonneg x) ht0.ne']
  add_le' x y :=
    (Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) ht0.le).trans
      (Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) ht0.le ht1)

/-- The multiplicity of an infinite place is at most the degree of the number field. -/
private lemma mult_le_finrank {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K) :
    w.mult ≤ Module.finrank ℚ K :=
  InfinitePlace.sum_mult_eq (K := K) ▸
    Finset.single_le_sum (f := InfinitePlace.mult) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)

namespace NumberFieldPlace

/-- Bombieri's normalized absolute value `Faltings.NumberFieldPlace.normalizedAbv w` at a place
`w` of a number field `K` is an absolute value on `K`: `|xy|_w = |x|_w |y|_w`, `|x|_w = 0 ↔ x = 0`,
and `|x + y|_w ≤ |x|_w + |y|_w`. It is `|·|_v ^ t` for Mathlib's absolute value `|·|_v` at the
place, with `t = 1/[K:ℚ]` at a finite place and `t = n_w/[K:ℚ] ≤ 1` at an infinite one. -/
@[faltings "lem_ht_abs_is_absolute_value"]
theorem exists_absoluteValue_coe_eq_normalizedAbv {K : Type*} [Field K] [NumberField K]
    (w : NumberFieldPlace K) : ∃ v : AbsoluteValue K ℝ, ⇑v = normalizedAbv w := by
  have hD : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  rcases w with w | w
  · exact ⟨absoluteValueRpow w.1 (inv_pos.2 hD)
      (inv_le_one_of_one_le₀ (Nat.one_le_cast.2 Module.finrank_pos)), rfl⟩
  · refine ⟨absoluteValueRpow w.1 (t := w.mult / Module.finrank ℚ K)
      (div_pos (Nat.cast_pos.2 InfinitePlace.mult_pos) hD)
      ((div_le_one hD).2 (Nat.cast_le.2 (mult_le_finrank w))), ?_⟩
    ext x
    change w x ^ ((w.mult : ℝ) / Module.finrank ℚ K) = (w x ^ w.mult) ^ (Module.finrank ℚ K : ℝ)⁻¹
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), div_eq_mul_inv]

/-- Bombieri's normalized absolute value is multiplicative: `|xy|_w = |x|_w |y|_w`. -/
theorem normalizedAbv_mul {K : Type*} [Field K] [NumberField K] (w : NumberFieldPlace K)
    (x y : K) : w.normalizedAbv (x * y) = w.normalizedAbv x * w.normalizedAbv y := by
  obtain ⟨v, hv⟩ := exists_absoluteValue_coe_eq_normalizedAbv w
  rw [← hv]
  exact map_mul v x y

/-- Bombieri's normalized absolute value is multiplicative over finite products:
`|∏_{i ∈ s} f i|_w = ∏_{i ∈ s} |f i|_w`. -/
theorem normalizedAbv_prod {K : Type*} [Field K] [NumberField K] (w : NumberFieldPlace K)
    {ι : Type*} (s : Finset ι) (f : ι → K) :
    w.normalizedAbv (∏ i ∈ s, f i) = ∏ i ∈ s, w.normalizedAbv (f i) := by
  obtain ⟨v, hv⟩ := exists_absoluteValue_coe_eq_normalizedAbv w
  rw [← hv]
  exact map_prod v f s

end NumberFieldPlace

end Faltings

/-!
# The ultrametric inequality for normalized absolute values at finite places

Let `K` be a number field and `w` a finite place of `K`. Bombieri's normalized absolute value
`|·|_w = Faltings.NumberFieldPlace.normalizedAbv w` is non-archimedean:
`|x + y|_w ≤ max (|x|_w, |y|_w)` for all `x, y ∈ K`. It is the `[K : ℚ]`-th root of the
non-archimedean absolute value `w` of Mathlib, and `t ↦ t ^ (1 / [K : ℚ])` is monotone on
`[0, ∞)` and commutes with `max` there.

## Main results

* `Faltings.NumberFieldPlace.isNonarchimedean_normalizedAbv_inl`: `|·|_w` is non-archimedean at a
  finite place `w`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

open NumberField

namespace NumberFieldPlace

/-- At a finite place `w` of a number field `K`, Bombieri's normalized absolute value is
non-archimedean: `|x + y|_w ≤ max (|x|_w, |y|_w)` for all `x y : K`. -/
@[faltings "lem_ht_abs_ultrametric"]
theorem isNonarchimedean_normalizedAbv_inl {K : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) : IsNonarchimedean (normalizedAbv (.inl w : NumberFieldPlace K)) := by
  intro x y
  simp only [normalizedAbv_inl]
  rw [← Real.rpow_max (by positivity) (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (w.add_le x y) (by positivity)

end NumberFieldPlace

end Faltings

/-!
# The local triangle inequality

Let `K` be a number field and `w ∈ M_K` a place. For a nonempty finite family
`a_1, …, a_r ∈ K`,
`|a_1 + ⋯ + a_r|_w ≤ |r|_w ^ ε_w · maxᵢ |aᵢ|_w`,
where `|·|_w` is Bombieri's normalized absolute value and `ε_w` the archimedean indicator.
At a finite place (`ε_w = 0`) this is the ultrametric inequality; at an infinite place
(`ε_w = 1`) it is the triangle inequality, transported along the embedding defining `w`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_sum_le`: the local triangle inequality
  `|∑_{i ∈ s} a i|_w ≤ |#s|_w ^ ε_w * max_{i ∈ s} |a i|_w`.

## Implementation notes

The family is `a : ι → K` indexed by a nonempty `Finset` `s` of an arbitrary type; the source's
case is `s = Finset.univ` in `Fin r` with `r ≥ 1`. The maximum is `Finset.sup'`, which needs the
nonemptiness of `s`; the integer `r` is the element `(#s : K)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

namespace NumberFieldPlace

open NumberField Finset

/-- At an infinite place `w`, with `|x|_w = ‖σ x‖ ^ t`, the triangle inequality along `σ` raised
to the power `t` gives `|∑ aᵢ|_w ≤ |#s|_w · maxᵢ |aᵢ|_w`. -/
private theorem normalizedAbv_inr_sum_le {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (w : InfinitePlace K) {s : Finset ι} (hs : s.Nonempty) (a : ι → K) :
    normalizedAbv (.inr w) (∑ i ∈ s, a i) ≤
      normalizedAbv (.inr w) (#s : K) * s.sup' hs (fun i => normalizedAbv (.inr w) (a i)) := by
  obtain ⟨-, -, hx⟩ := localDegree_inr_eq_mult_and_normalizedAbv_inr_eq w w.embedding
    w.mk_embedding (w.comap (algebraMap ℚ K)) ⟨rfl⟩
  obtain ⟨j, hj, hjmax⟩ := s.exists_max_image (‖w.embedding <| a ·‖) hs
  have hsum : ‖w.embedding (∑ i ∈ s, a i)‖ ≤ #s * ‖w.embedding (a j)‖ := by
    simpa [map_sum] using (norm_sum_le _ _).trans (sum_le_card_nsmul s _ _ hjmax)
  set t : ℝ := _ / _
  rw [hx, hx, map_natCast, Complex.norm_natCast]
  calc _ ≤ ((#s : ℝ) * ‖w.embedding (a j)‖) ^ t :=
        Real.rpow_le_rpow (norm_nonneg _) hsum (by positivity)
    _ = (#s : ℝ) ^ t * normalizedAbv (.inr w) (a j) := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg _), hx]
    _ ≤ _ := by gcongr; exact le_sup' (fun i => normalizedAbv (.inr w) (a i)) hj

/-- For a place `w` of a number field `K` and a nonempty finite family `a i ∈ K`, `i ∈ s`,
`|∑_{i ∈ s} a i|_w ≤ |#s|_w ^ ε_w * max_{i ∈ s} |a i|_w`, where `|·|_w` is
`Faltings.NumberFieldPlace.normalizedAbv` and `ε_w` is
`Faltings.NumberFieldPlace.archimedeanIndicator`. At a finite place this is the ultrametric
inequality, at an infinite place the triangle inequality along the embedding defining `w`. -/
@[faltings "lem_ht_local_sum_bound"]
theorem normalizedAbv_sum_le {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (w : NumberFieldPlace K) {s : Finset ι} (hs : s.Nonempty) (a : ι → K) :
    w.normalizedAbv (∑ i ∈ s, a i) ≤
      w.normalizedAbv (#s : K) ^ w.archimedeanIndicator *
        s.sup' hs (fun i => w.normalizedAbv (a i)) := by
  rcases w with w | w
  · rw [archimedeanIndicator_inl, pow_zero, one_mul]
    exact (isNonarchimedean_normalizedAbv_inl w).apply_sum_le_sup hs
  · rw [archimedeanIndicator_inr, pow_one]
    exact normalizedAbv_inr_sum_le w hs a

end NumberFieldPlace

end Faltings
