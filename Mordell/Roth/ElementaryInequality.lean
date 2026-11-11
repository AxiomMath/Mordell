module
public import Mathlib
public import Mordell.Attr

/-!
# An elementary inequality for sums of truncated linear functions

For integers `0 ≤ s ≤ r` with `r ≥ 1` and a real `t ≥ 0`, the sum
`∑_{ν=0}^{s} max (t - ν / r) 0` is at least `(s + 1) * min (t / 2) (t ^ 2 / 2)`.
If `s ≤ t r`, every term is `t - ν / r` and the average of these is `t - s / (2 r) ≥ t / 2`.
Otherwise, with `K = ⌊t r⌋ < s`, the first `K + 1` terms alone sum to at least
`(s + 1) t ^ 2 / 2`, which reduces to `(t r - K) (K + 1 - t r) ≥ 0`.

This is the estimate used in the proof of Roth's lemma to bound the index of a generalized
Wronskian from below.

## Main results

* `Faltings.mul_min_le_sum_range_max_sub_div`: the inequality above.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 635][bombieri1990]
-/

namespace Faltings

/-- Closed form of `∑_{ν < n} (t - ν / r)`. -/
private lemma sum_range_sub_div (n : ℕ) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ∑ ν ∈ Finset.range n, (t - (ν : ℝ) / r) = n * (t - (n - 1) / (2 * r)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- Dropping the truncation and all terms after the first `n` only decreases the sum. -/
private lemma mul_sub_div_le_sum_range_max (t : ℝ) {r : ℝ} (hr : r ≠ 0) {n m : ℕ}
    (hnm : n ≤ m) :
    (n : ℝ) * (t - (n - 1) / (2 * r)) ≤ ∑ ν ∈ Finset.range m, max (t - (ν : ℝ) / r) 0 := by
  rw [← sum_range_sub_div n t hr]
  exact (Finset.sum_le_sum fun _ _ => le_max_left _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnm)
      fun _ _ _ => le_max_right _ _)

/-- For `K ≤ t r ≤ K + 1` and `K + 1 ≤ s ≤ r`, the first `K + 1` terms `t - ν / r` already
sum to at least `(s + 1) t² / 2`: with `u = t r`, this is
`(s + 1) u² ≤ r (K + 1) (2 u - K)`, which follows from `(u - K) (K + 1 - u) ≥ 0`. -/
private lemma mul_sq_half_le_mul_sub {K s r t : ℝ} (hK : 0 ≤ K) (hKt : K ≤ t * r)
    (htK : t * r ≤ K + 1) (hKs : K + 1 ≤ s) (hsr : s ≤ r) :
    (s + 1) * (t ^ 2 / 2) ≤ (K + 1) * (t - K / (2 * r)) := by
  have hr : 0 < r := by linarith
  obtain ⟨u, rfl⟩ : ∃ u, t = u / r := ⟨t * r, by field_simp⟩
  rw [div_mul_cancel₀ _ hr.ne'] at hKt htK
  rw [← sub_nonneg, show (K + 1) * (u / r - K / (2 * r)) - (s + 1) * ((u / r) ^ 2 / 2)
      = (r * (K + 1) * (2 * u - K) - (s + 1) * u ^ 2) / (2 * r ^ 2) by field_simp]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.2 hKt) (sub_nonneg.2 htK)]

/-- For natural numbers `s ≤ r` with `1 ≤ r` and a real `t ≥ 0`,
`(s + 1) * min (t / 2) (t ^ 2 / 2) ≤ ∑_{ν = 0}^{s} max (t - ν / r) 0`. -/
@[faltings "lem_bvr_index_sum_inequality"]
public theorem mul_min_le_sum_range_max_sub_div {s r : ℕ} (hr : 1 ≤ r) (hsr : s ≤ r) {t : ℝ}
    (ht : 0 ≤ t) :
    ((s : ℝ) + 1) * min (t / 2) (t ^ 2 / 2) ≤
      ∑ ν ∈ Finset.range (s + 1), max (t - (ν : ℝ) / r) 0 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  by_cases hts : (s : ℝ) ≤ t * r
  · -- all `s + 1` terms are untruncated, and their average is `t - s / (2 r) ≥ t / 2`
    refine (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans <|
      le_trans ?_ (mul_sub_div_le_sum_range_max t hr0.ne' le_rfl)
    push_cast
    gcongr
    rw [add_sub_cancel_right, le_sub_comm, sub_half, div_le_div_iff₀ (by positivity) two_pos]
    linarith
  · -- keep the first `⌊t r⌋₊ + 1 ≤ s` terms
    push Not at hts
    have hK : ⌊t * r⌋₊ < s := Nat.floor_lt (by positivity) |>.2 hts
    refine (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans <|
      le_trans ?_ (mul_sub_div_le_sum_range_max t hr0.ne' (by omega : ⌊t * r⌋₊ + 1 ≤ s + 1))
    push_cast
    rw [add_sub_cancel_right]
    exact mul_sq_half_le_mul_sub (by positivity) (Nat.floor_le (by positivity))
      (Nat.lt_floor_add_one _).le (by exact_mod_cast hK) (by exact_mod_cast hsr)

end Faltings
