module
public import Mordell.BombieriVojta.Conclusion.ParametersSize

/-!
# Choice of the parameters `d₁, d₂, d` for large `D`

Let `g ≥ 2` be the genus, `s ≥ 1` and `N ≥ 2g + 1` the integers of Bombieri's auxiliary
embeddings, `0 < γ₀ ≤ 1/10` and `γ = γ₀ / (2 (g + γ₀))`. For two points `z, w` with Néron–Tate
norms `0 < |z| ≤ |w|`, let `(d₁, d₂, d) = Faltings.bombieriParameters g s N γ₀ |z| |w| D`.
Then for every `D₀`, all sufficiently large `D` give positive integers `d₁, d₂, d` with
`N ∣ dᵢ + s d`, so that `δᵢ = (dᵢ + s d) / N` are positive integers, all five at least `D₀`,
`d₂ ≤ d₁`, `g d² < d₁ d₂ < g² d²` and `d₁ d₂ - g d² > γ d₁ d₂`.

## Main results

* `Faltings.eventually_bombieriParameters`: the conditions above hold for all large `D`.

## Implementation notes

"For all `D ≥ D_*`" is written as `∀ᶠ D in Filter.atTop`. The norms `|z|, |w|` enter as the
real numbers `a, b`, as in `Faltings.bombieriParameters`. The quotient `δᵢ` is the integer
quotient `(dᵢ + s d) / N`, and its integrality is the separate divisibility `(N : ℤ) ∣ dᵢ + s d`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, p. 638
-/

namespace Faltings

open Filter

/-- The three product inequalities for real numbers `d, d₁, d₂` close to `c`, `κ c`, `μ c`
with `κ μ = g + γ₀`, once `c` is large. -/
private lemma product_bounds {g γ₀ κ μ c N d d₁ d₂ : ℝ} (hgr : 2 ≤ g) (hγ₀ : 0 < γ₀)
    (hγ₀' : γ₀ ≤ 1 / 10) (hκ0 : 0 < κ) (hμ0 : 0 < μ) (hκμ : κ * μ = g + γ₀) (hNr : 1 ≤ N)
    (h1 : 1 ≤ c) (hγc : 2 * (κ * N + 3 * g + N * μ) < γ₀ * c) (h3 : N * μ + 1 ≤ c)
    (hμc : N + 1 ≤ μ * c) (rd : c ≤ d) (rd' : d < c + 1) (rd₁ : κ * c ≤ d₁)
    (rd₁' : d₁ < κ * c + N) (rd₂ : μ * c - N < d₂) (rd₂' : d₂ ≤ μ * c) :
    g * d ^ 2 < d₁ * d₂ ∧ d₁ * d₂ < g ^ 2 * d ^ 2 ∧
      γ₀ / (2 * (g + γ₀)) * (d₁ * d₂) < d₁ * d₂ - g * d ^ 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hκc : 0 < κ * c := mul_pos hκ0 (by linarith)
  have hd₁pos : 0 < d₁ := by linarith
  have hPlo : (g + γ₀) * c ^ 2 - κ * N * c ≤ d₁ * d₂ := by
    have : κ * c * (μ * c - N) ≤ d₁ * d₂ :=
      mul_le_mul rd₁ rd₂.le (by linarith) hd₁pos.le
    have e : κ * c * (μ * c - N) = (g + γ₀) * c ^ 2 - κ * N * c := by rw [← hκμ]; ring
    linarith
  have hPhi : d₁ * d₂ ≤ (g + γ₀) * c ^ 2 + N * μ * c := by
    have : d₁ * d₂ ≤ (κ * c + N) * (μ * c) :=
      mul_le_mul rd₁'.le rd₂' (by linarith) (by linarith)
    have e : (κ * c + N) * (μ * c) = (g + γ₀) * c ^ 2 + N * μ * c := by rw [← hκμ]; ring
    linarith
  have hdsq : d ^ 2 ≤ (c + 1) ^ 2 := pow_le_pow_left₀ (by linarith) rd'.le 2
  have hdsq' : c ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hc0 rd 2
  have hcpos : 0 < c := by linarith
  have hg0 : 0 ≤ g := by linarith
  have t1 : 2 * (κ * N + 3 * g + N * μ) * c < γ₀ * c * c := mul_lt_mul_of_pos_right hγc hcpos
  have t2 : 0 ≤ κ * N * c := mul_nonneg (mul_nonneg hκ0.le (by linarith)) hc0
  have t3 : 0 ≤ N * μ * c := mul_nonneg (mul_nonneg (by linarith) hμ0.le) hc0
  have t4 : g * 1 ≤ g * c := mul_le_mul_of_nonneg_left h1 hg0
  have t5 : g * d ^ 2 ≤ g * (c + 1) ^ 2 := mul_le_mul_of_nonneg_left hdsq hg0
  have hE : γ₀ * c ^ 2 - (κ * N + 2 * g) * c - g ≤ d₁ * d₂ - g * d ^ 2 := by linarith
  have hX : 0 < γ₀ * c ^ 2 - 2 * (κ * N + 2 * g) * c - 2 * g - N * μ * c := by linarith
  have hgd : g * d ^ 2 < d₁ * d₂ := by linarith
  have hgd' : d₁ * d₂ < g ^ 2 * d ^ 2 := by
    have u1 : g * 2 ≤ g * g := mul_le_mul_of_nonneg_left hgr hg0
    have u2 : 0 ≤ (g ^ 2 - g - γ₀ - 1) * c ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg c)
    have u3 : (N * μ + 1) * c ≤ c * c := mul_le_mul_of_nonneg_right h3 hc0
    have u4 : g ^ 2 * c ^ 2 ≤ g ^ 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_left hdsq' (sq_nonneg _)
    linarith
  have hγ : γ₀ / (2 * (g + γ₀)) * (d₁ * d₂) < d₁ * d₂ - g * d ^ 2 := by
    have hgg : 0 < 2 * (g + γ₀) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hgg]
    have ha' : (γ₀ * c ^ 2 - (κ * N + 2 * g) * c - g) * (2 * (g + γ₀)) ≤
        (d₁ * d₂ - g * d ^ 2) * (2 * (g + γ₀)) :=
      mul_le_mul_of_nonneg_right hE hgg.le
    have hγP : γ₀ * (d₁ * d₂) ≤ γ₀ * ((g + γ₀) * c ^ 2 + N * μ * c) :=
      mul_le_mul_of_nonneg_left hPhi hγ₀.le
    have hγg : γ₀ * (N * μ * c) ≤ (g + γ₀) * (N * μ * c) :=
      mul_le_mul_of_nonneg_right (by linarith) t3
    have hXp := mul_pos (show 0 < g + γ₀ by positivity) hX
    linarith
  exact ⟨hgd, hgd', hγ⟩

/-- Dividing a multiple of `N > 0` by `N` in `ℤ` and casting to `ℝ` keeps a lower bound
`N B ≤ x` as `B ≤ x / N`. -/
private lemma le_cast_ediv {N : ℕ} {x : ℤ} {B : ℝ} (hN : (0 : ℝ) < N) (hx : (N : ℤ) ∣ x)
    (h : N * B ≤ x) : B ≤ ((x / N : ℤ) : ℝ) := by
  rw [Int.cast_div hx (by exact_mod_cast hN.ne'), Int.cast_natCast, le_div_iff₀ hN]
  linarith

/-- **Choice of parameters** (Bombieri). For `g ≥ 2`, `s ≥ 1`, `N ≥ 2g + 1`, `0 < γ₀ ≤ 1/10` and
Néron–Tate norms `0 < a ≤ b`, for every `D₀` and all sufficiently large `D` the triple
`(d₁, d₂, d) = bombieriParameters g s N γ₀ a b D` consists of positive integers with
`N ∣ dᵢ + s d`, the quotients `δᵢ = (dᵢ + s d) / N` are positive, `d₁, d₂, d, δ₁, δ₂ ≥ D₀`,
`d₂ ≤ d₁`, `g d² < d₁ d₂ < g² d²`, and `d₁ d₂ - g d² > γ d₁ d₂` with `γ = γ₀ / (2 (g + γ₀))`. -/
@[faltings "lem_bvr_parameter_choice"]
public theorem eventually_bombieriParameters {g : ℕ} (hg : 2 ≤ g) {s : ℤ} (hs : 1 ≤ s) {N : ℕ}
    (hN : 2 * g + 1 ≤ N) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1 / 10) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (D₀ : ℝ) :
    ∀ᶠ D in atTop, ∀ d₁ d₂ d : ℤ, bombieriParameters g s N γ₀ a b D = (d₁, d₂, d) →
      0 < d₁ ∧ 0 < d₂ ∧ 0 < d ∧
      (N : ℤ) ∣ d₁ + s * d ∧ (N : ℤ) ∣ d₂ + s * d ∧
      0 < (d₁ + s * d) / N ∧ 0 < (d₂ + s * d) / N ∧
      D₀ ≤ d₁ ∧ D₀ ≤ d₂ ∧ D₀ ≤ d ∧
      D₀ ≤ (((d₁ + s * d) / N : ℤ) : ℝ) ∧ D₀ ≤ (((d₂ + s * d) / N : ℤ) : ℝ) ∧
      d₂ ≤ d₁ ∧ (g : ℤ) * d ^ 2 < d₁ * d₂ ∧ d₁ * d₂ < (g : ℤ) ^ 2 * d ^ 2 ∧
      γ₀ / (2 * (g + γ₀)) * ((d₁ * d₂ : ℤ) : ℝ) < ((d₁ * d₂ - g * d ^ 2 : ℤ) : ℝ) := by
  have hb : 0 < b := ha.trans_le hab
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgr : (2 : ℝ) ≤ g := by exact_mod_cast hg
  set l := Real.sqrt (g + γ₀) with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 (by positivity)
  set κ := l * b / a with hκ
  set μ := l * a / b with hμ
  have hκ0 : 0 < κ := by positivity
  have hμ0 : 0 < μ := by positivity
  have hκμ : κ * μ = g + γ₀ := by
    rw [hκ, hμ, ← Real.sq_sqrt (show (0 : ℝ) ≤ g + γ₀ by positivity), ← hl]; field_simp
  have hμκ : μ ≤ κ := by rw [hκ, hμ, div_le_div_iff₀ hb ha]; gcongr
  have hc : Tendsto (fun D : ℝ => D / (a * b)) atTop atTop :=
    tendsto_id.atTop_div_const (mul_pos ha hb)
  filter_upwards [hc.eventually_ge_atTop 1,
    hc.eventually_gt_atTop (2 * (κ * N + 3 * g + N * μ) / γ₀),
    hc.eventually_ge_atTop (N * μ + 1),
    hc.eventually_ge_atTop ((N + |D₀| + 1) / μ),
    hc.eventually_ge_atTop (N * (|D₀| + 1))] with D h1 h2 h3 h4 h5 d₁ d₂ d h
  set c := D / (a * b) with hcdef
  rw [div_lt_iff₀ hγ₀] at h2
  rw [div_le_iff₀ hμ0, mul_comm] at h4
  have habs := abs_nonneg D₀
  have hD : 0 < D := (div_pos_iff_of_pos_right (mul_pos ha hb)).1 (by linarith)
  have hbd := bombieriParameters_bounds g s N γ₀ a b D hg hs hN hγ₀ hγ₀' ha hab hD
  simp only [h] at hbd
  obtain ⟨⟨hd0, hd1⟩, ⟨hA0, hA1⟩, ⟨hB0, hB1⟩⟩ := hbd
  have hA : l * D / a ^ 2 = κ * c := by rw [hκ, hcdef]; field_simp
  have hB : l * D / b ^ 2 = μ * c := by rw [hμ, hcdef]; field_simp
  rw [← hl, hA] at hA0 hA1
  rw [← hl, hB] at hB0 hB1
  obtain ⟨hgd, hgd', hγ⟩ := product_bounds (d := (d : ℝ)) (d₁ := (d₁ : ℝ)) (d₂ := (d₂ : ℝ))
    hgr hγ₀ hγ₀' hκ0 hμ0 hκμ hNr h1 (by linarith) h3 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  simp only [bombieriParameters, Prod.mk.injEq] at h
  obtain ⟨e₁, e₂, e⟩ := h
  have hdv₁ : (N : ℤ) ∣ d₁ + s * d :=
    ⟨-((-(s * d) - ⌈l * D / a ^ 2⌉) / N), by rw [← e₁, Int.emod_def, ← e]; ring⟩
  have hdv₂ : (N : ℤ) ∣ d₂ + s * d :=
    ⟨(⌊l * D / b ^ 2⌋ + s * d) / N, by rw [← e₂, Int.emod_def, ← e]; ring⟩
  have hsd : (d : ℝ) ≤ s * d :=
    le_mul_of_one_le_left (by linarith) (by exact_mod_cast hs)
  have hμκc : μ * c ≤ κ * c := mul_le_mul_of_nonneg_right hμκ (by linarith)
  have hD₀ := le_abs_self D₀
  have hN1 : |D₀| + 1 ≤ (N : ℝ) * (|D₀| + 1) := le_mul_of_one_le_left (by positivity) hNr
  have hq₁ := le_cast_ediv (B := |D₀| + 1) (by linarith) hdv₁ (by push_cast; linarith)
  have hq₂ := le_cast_ediv (B := |D₀| + 1) (by linarith) hdv₂ (by push_cast; linarith)
  refine ⟨by exact_mod_cast (by linarith : (0 : ℝ) < d₁),
    by exact_mod_cast (by linarith : (0 : ℝ) < d₂), by exact_mod_cast (by linarith : (0 : ℝ) < d),
    hdv₁, hdv₂, by exact_mod_cast (by linarith : (0 : ℝ) < ((d₁ + s * d) / N : ℤ)),
    by exact_mod_cast (by linarith : (0 : ℝ) < ((d₂ + s * d) / N : ℤ)),
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by exact_mod_cast (by linarith : (d₂ : ℝ) ≤ d₁), by exact_mod_cast hgd,
    by exact_mod_cast hgd', by push_cast; exact hγ⟩

end Faltings
