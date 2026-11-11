module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mordell.NumberField.Place.LocalDegreeSum
public import Mordell.Height.Weil.LocalHeight

/-!
# Compatibility of the normalized absolute values with field extension

Let `k ⊆ K` be number fields, `v` a place of `k` and `x = (x_j)` a nonzero vector with entries
in `k`. With Bombieri's normalized absolute values `Faltings.NumberFieldPlace.normalizedAbv`,
`log max_j |x_j|_v = ∑_{w ∣ v} log max_j |x_j|_w`, the sum running over the places `w` of `K`
lying over `v`. This is the normalization that makes the height independent of the field of
definition.

The proof: for a place `w ∣ v` of `K` and `y ∈ k`, `|y|_w = |y|_v ^ (n_w / [K : k])` for natural
numbers `n_w` with `∑_{w ∣ v} n_w = [K : k]`. Since `t ↦ t ^ c` is increasing for `c ≥ 0`,
`max_j |x_j|_w = (max_j |x_j|_v) ^ (n_w / [K : k])`, and taking logarithms and summing over
`w ∣ v` gives the claim.

## Main results

* `Faltings.NumberFieldPlace.log_iSup_normalizedAbv_eq_finsum_liesOver`: the compatibility above.

## Implementation notes

The vector is indexed by an arbitrary finite type `ι` rather than `Fin (n + 1)`. The quantity
`max_j log |x_j|_v` is written `log (⨆ j, |x_j|_v)`: the logarithm is increasing, so the two agree,
and the second avoids `Real.log 0 = 0` at a vanishing entry. The sum over `w ∣ v` is a `finsum`
over the subtype of places lying over `v`, which is finite.

At an infinite place `n_w` is the local degree `[K_w : k_v]`, through
`NumberField.InfinitePlace.mult_mul_finrank`, and the sum is
`Faltings.NumberFieldPlace.finsum_localDegree_eq_finrank`. At a finite place `n_w = e_w f_w`,
through `NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`, and the sum is
`Ideal.sum_ramification_inertia_eq_finrank`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], proof of Lemma 1.2.3(i).
-/

@[expose] public section

namespace Faltings

open NumberField
open scoped NumberField.LiesOver

/-- If `|y|_w = |y|_v ^ (n_w / N)` with `∑ n_w = N > 0`, then
`log max_j |x_j|_v = ∑_w log max_j |x_j|_w`. -/
private theorem log_iSup_eq_finsum {ι W : Type*} [Finite ι] (n : W → ℕ) {N : ℕ} (hN : 0 < N)
    (hn : ∑ᶠ w, n w = N) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hpos : ∃ j, 0 < a j)
    (b : W → ι → ℝ) (hb : ∀ w j, b w j = a j ^ ((n w : ℝ) / N)) :
    Real.log (⨆ j, a j) = ∑ᶠ w, Real.log (⨆ j, b w j) := by
  obtain ⟨j1, hj1⟩ := hpos
  have : Nonempty ι := ⟨j1⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := a)
  have hle : ∀ j, a j ≤ a j0 := fun j => hj0 ▸ le_ciSup (Set.finite_range a).bddAbove j
  have ha0 : 0 < a j0 := hj1.trans_le (hle j1)
  have hbw : ∀ w, (⨆ j, b w j) = a j0 ^ ((n w : ℝ) / N) := by
    intro w
    refine le_antisymm (ciSup_le fun j => ?_) ?_
    · rw [hb]
      exact Real.rpow_le_rpow (ha j) (hle j) (by positivity)
    · rw [← hb]
      exact le_ciSup (Set.finite_range _).bddAbove j0
  have hsupp : (Function.support n).Finite := by
    by_contra h
    rw [finsum_of_infinite_support h] at hn
    omega
  simp_rw [hbw, ← hj0, Real.log_rpow ha0, div_mul_eq_mul_div, mul_div_assoc]
  have hcast : ∑ᶠ w, (n w : ℝ) = N := by
    rw [← hn]
    exact ((Nat.castAddMonoidHom ℝ).map_finsum hsupp).symm
  rw [← finsum_mul, hcast]
  field_simp

/-- `(a ^ m) ^ (1 / (N D)) = (a ^ (1 / D)) ^ (m / N)` for `a ≥ 0`. -/
private theorem pow_rpow_inv_mul {a : ℝ} (ha : 0 ≤ a) (m N D : ℕ) :
    (a ^ m) ^ ((N * D : ℕ) : ℝ)⁻¹ = (a ^ (D : ℝ)⁻¹) ^ ((m : ℝ) / N) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_mul ha]
  congr 1
  push_cast
  rw [mul_inv, div_eq_mul_inv]
  ring

section

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- `[K : ℚ] = [K : k] [k : ℚ]`. -/
private theorem finrank_rat_eq (k : Type*) [Field k] [NumberField k] [Algebra k K] :
    Module.finrank ℚ K = Module.finrank k K * Module.finrank ℚ k := by
  rw [mul_comm, Module.finrank_mul_finrank]

/-- The product `e f` of ramification index and inertia degree of a finite place over `k`. -/
private noncomputable def ef (k : Type*) [Field k] [NumberField k] [Algebra k K] :
    NumberFieldPlace K → ℕ
  | .inl w => (FinitePlace.maximalIdeal w).asIdeal.ramificationIdx (𝓞 k) *
      (FinitePlace.maximalIdeal w).asIdeal.inertiaDeg (𝓞 k)
  | .inr _ => 0

/-- At a finite place `w ∣ v`, `|y|_w = |y|_v ^ (e f / [K : k])` for `y ∈ k`. -/
private theorem normalizedAbv_inl_algebraMap (v : FinitePlace k) (w : FinitePlace K)
    (h : NumberFieldPlace.LiesOver (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k))
    (y : k) :
    NumberFieldPlace.normalizedAbv (.inl w : NumberFieldPlace K) (algebraMap k K y) =
      NumberFieldPlace.normalizedAbv (.inl v : NumberFieldPlace k) y ^
        ((ef k (.inl w : NumberFieldPlace K) : ℝ) / Module.finrank k K) := by
  have := (NumberFieldPlace.liesOver_inl_inl w v).1 h
  have key : w (algebraMap k K y) = v y ^ ef k (.inl w : NumberFieldPlace K) := by
    rw [← FinitePlace.norm_embedding_eq w, ← FinitePlace.norm_embedding_eq v,
      ← FinitePlace.equivHeightOneSpectrum_symm_apply,
      ← FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap (FinitePlace.maximalIdeal v)
        (FinitePlace.maximalIdeal w) y]
    rfl
  rw [NumberFieldPlace.normalizedAbv_inl, NumberFieldPlace.normalizedAbv_inl, key,
    finrank_rat_eq k, pow_rpow_inv_mul (apply_nonneg v y)]

/-- `∑_{w ∣ v} e_w f_w = [K : k]` for a finite place `v` of `k`. -/
private theorem finsum_ef (v : FinitePlace k) :
    ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver (.inl v : NumberFieldPlace k)}, ef k w.1 =
      Module.finrank k K := by
  classical
  set p := (FinitePlace.maximalIdeal v).asIdeal
  let g : p.primesOver (𝓞 K) → ℕ := fun q => q.1.ramificationIdx (𝓞 k) * q.1.inertiaDeg (𝓞 k)
  calc ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver (.inl v : NumberFieldPlace k)}, ef k w.1
      = ∑ᶠ w, g (NumberFieldPlace.liesOverInlEquiv v w) := finsum_congr fun w => by
        obtain ⟨w | w, h⟩ := w
        · rfl
        · exact h.elim
    _ = ∑ᶠ q, g q := finsum_comp_equiv _
    _ = ∑ q, g q := finsum_eq_sum_of_fintype _
    _ = Module.finrank (𝓞 k) (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
    _ = Module.finrank k K := (IsFractionRing.finrank_eq (𝓞 k) k (𝓞 K) K).symm

/-- At an infinite place `w ∣ v`, `|y|_w = |y|_v ^ ([K_w : k_v] / [K : k])` for `y ∈ k`. -/
private theorem normalizedAbv_inr_algebraMap (v : InfinitePlace k) (w : InfinitePlace K)
    (h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace k))
    (y : k) :
    NumberFieldPlace.normalizedAbv (.inr w : NumberFieldPlace K) (algebraMap k K y) =
      NumberFieldPlace.normalizedAbv (.inr v : NumberFieldPlace k) y ^
        ((NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace k)
            h : ℝ) / Module.finrank k K) := by
  have : w.LiesOver v := h
  have hw : w (algebraMap k K y) = v y := by
    rw [← InfinitePlace.comap_apply, InfinitePlace.LiesOver.comap_eq w v]
  have hm := InfinitePlace.mult_mul_finrank (v := v) w
  have hd : NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K)
      (.inr v : NumberFieldPlace k) h = Module.finrank v.Completion w.Completion := rfl
  rw [NumberFieldPlace.normalizedAbv_inr, NumberFieldPlace.normalizedAbv_inr, hw, ← hm, hd,
    pow_mul, finrank_rat_eq k, pow_rpow_inv_mul (pow_nonneg (apply_nonneg v y) _)]

end

/-- For number fields `k ⊆ K`, a place `v` of `k` and a nonzero vector `x : ι → k` on a finite
index type, `log max_j |x_j|_v` is the sum over the places `w` of `K` lying over `v` of
`log max_j |x_j|_w`, for Bombieri's normalized absolute values
`Faltings.NumberFieldPlace.normalizedAbv`. -/
@[faltings "lem_ht_normalization_compatible"]
theorem NumberFieldPlace.log_iSup_normalizedAbv_eq_finsum_liesOver {k K : Type*} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] {ι : Type*} [Finite ι]
    (v : NumberFieldPlace k) (x : ι → k) (hx : x ≠ 0) :
    Real.log (⨆ j, v.normalizedAbv (x j)) =
      ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver v},
        Real.log (⨆ j, w.1.normalizedAbv (algebraMap k K (x j))) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have hpos : ∃ j, 0 < v.normalizedAbv (x j) := ⟨j, v.normalizedAbv_pos hj⟩
  have hN : 0 < Module.finrank k K := Module.finrank_pos
  rcases v with v | v
  · refine log_iSup_eq_finsum (fun w => ef k w.1) hN (finsum_ef v) _
      (fun j => NumberFieldPlace.normalizedAbv_nonneg _ _) hpos _ fun w j => ?_
    obtain ⟨w | w, h⟩ := w
    · exact normalizedAbv_inl_algebraMap v w h (x j)
    · exact h.elim
  · refine log_iSup_eq_finsum (fun w => w.1.localDegree (.inr v) w.2) hN
      (NumberFieldPlace.finsum_localDegree_eq_finrank _) _
      (fun j => NumberFieldPlace.normalizedAbv_nonneg _ _) hpos _ fun w j => ?_
    obtain ⟨w | w, h⟩ := w
    · exact h.elim
    · exact normalizedAbv_inr_algebraMap v w h (x j)

end Faltings
