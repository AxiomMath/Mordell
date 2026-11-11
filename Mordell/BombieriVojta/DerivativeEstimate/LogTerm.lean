module
public import Mathlib
public import Mordell.Attr

/-!
# The logarithmic term in Bombieri's derivative estimate is small

For a fixed natural number `n`, the quantity `n * log ((δ₁ + n) * (δ₂ + n))` is `o(δ₁ + δ₂)`
as `δ₁ + δ₂ → ∞` through pairs `(δ₁, δ₂)` of nonnegative reals. This is the error term
appearing in Bombieri's estimate for derivatives (Lemma 6 of [Bombieri1990]).

The proof: since `(δ₁ + n) * (δ₂ + n) ≤ (δ₁ + δ₂ + n) ^ 2`, the quantity is at most
`2 n log (δ₁ + δ₂ + n)`, and `log (x + n) = o(x)` as `x → ∞`.

## Main results

* `Faltings.isLittleO_mul_log_mul_add_add`: the little-o statement, along the filter
  `comap (fun δ ↦ δ.1 + δ.2) atTop ⊓ 𝓟 {δ | 0 ≤ δ.1 ∧ 0 ≤ δ.2}` on `ℝ × ℝ`.

## Implementation notes

The limit "`δ₁ + δ₂ → ∞` with `δ₁, δ₂ ≥ 0`" is the filter on `ℝ × ℝ` obtained by pulling back
`atTop` along `δ ↦ δ.1 + δ.2` and restricting to the closed nonnegative quadrant. Integer
or natural-number values of `δ₁, δ₂` are obtained by composing with the casts.
The nonnegativity restriction cannot be dropped: along `δ = (-e^{t^2}, e^{t^2} + t)` the
sum tends to infinity like `t` while the logarithm grows like `2 t^2`.

## References

* [Bombieri1990] E. Bombieri, *The Mordell conjecture revisited*, §7, Lemma 6, p. 628.
-/

open Filter Asymptotics Real

namespace Faltings

/-- `log (x + c) = o(x)` as `x → ∞`. -/
private lemma isLittleO_log_add_const (c : ℝ) :
    (fun x : ℝ => log (x + c)) =o[atTop] id :=
  (isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right _ c tendsto_id)).trans_isBigO
    ((isBigO_refl _ _).add (isLittleO_const_id_atTop c).isBigO)

/-- For `a, b ≥ 0`, `n log ((a + n)(b + n))` is bounded in norm by `2 n log (a + b + n)`,
because `(a + n)(b + n) ≤ (a + b + n)²` and the logarithm is nonnegative once `n ≥ 1`. -/
private lemma norm_mul_log_mul_add_le (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(n : ℝ) * log ((a + n) * (b + n))‖ ≤ ‖2 * (n : ℝ) * log (a + b + n)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ log ((a + n) * (b + n)) := log_nonneg (by nlinarith)
  have hle : log ((a + n) * (b + n)) ≤ 2 * log (a + b + n) := by
    simpa [log_pow] using log_le_log (by positivity) (show _ ≤ (a + b + n) ^ 2 by nlinarith)
  rw [norm_of_nonneg (by positivity), norm_of_nonneg (by nlinarith)]
  nlinarith

/-- For fixed `n : ℕ`, `n * log ((δ₁ + n) * (δ₂ + n)) = o(δ₁ + δ₂)` as `δ₁ + δ₂ → ∞`
with `δ₁, δ₂ ≥ 0`. -/
@[faltings "lem_bvs_log_term_small"]
public theorem isLittleO_mul_log_mul_add_add (n : ℕ) :
    (fun δ : ℝ × ℝ => (n : ℝ) * log ((δ.1 + n) * (δ.2 + n))) =o[
      comap (fun δ : ℝ × ℝ => δ.1 + δ.2) atTop ⊓ 𝓟 {δ | 0 ≤ δ.1 ∧ 0 ≤ δ.2}]
      (fun δ : ℝ × ℝ => δ.1 + δ.2) := by
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_)
    (((isLittleO_log_add_const n).comp_tendsto
      (tendsto_comap.mono_left inf_le_left)).const_mul_left (2 * (n : ℝ)))
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with δ ⟨h1, h2⟩
  simpa using norm_mul_log_mul_add_le n h1 h2

end Faltings
