module
public import Mathlib
public import Mordell.Attr

/-!
# The final estimate in Bombieri's Lemma 7

Fix natural numbers `g ≥ 2`, `s ≥ 1`, `N ≥ 2g + 1` and `m`, and real constants `γ > 0`,
`c₁₃, c_k, c₁₄ ≥ 0`, together with a nonnegative function `ε₁₃` of the positive integer `d`
tending to `0`. For positive integers `d₁, d₂, d` with `g d² < d₁ d₂ < g² d²` put
`δᵢ = (dᵢ + s d) / N`. If `1 ≤ N_u ≤ (m + 1) N² δ₁ δ₂`,
`S ≥ γ d₁ d₂ - c₁₄ (δ₁ + δ₂) - (m + 1)(g - 1)²` and `0 ≤ H ≤ c₁₃ d + ε₁₃(d) d`, then once
`min d₁ d₂` is large enough (depending on `ε > 0`) we have `S > 0` and
`(N_u / S) (H + log N_u + c_k) ≤ c₁₃ (m + 1)(s + 1)² (d₁ + d₂) / γ + ε (d₁ + d₂)`.

This is the arithmetic at the end of the proof of Lemma 7 of [Bombieri1990]: `N_u` is the
number of unknowns, `S` a lower bound for the number of free unknowns after the linear
conditions, and `H` a bound for the heights of the linear forms, so that the left side is
the bound given by Siegel's lemma.

## Main results

* `Faltings.BombieriVojta.exists_pos_and_div_mul_add_log_le`: the estimate.

## Implementation notes

Bombieri's `o(d₁ + d₂)` is made explicit as: for every `ε > 0` there is a threshold on
`min d₁ d₂`. A threshold on `d₁ + d₂` alone would not suffice, since the correction
`c₁₄ (δ₁ + δ₂)` is then of the order of the main term `γ d₁ d₂`.

## References

* [Bombieri1990] E. Bombieri, *The Mordell conjecture revisited*, §8, p. 631.
-/

open Filter Real

namespace Faltings.BombieriVojta

/-- The key inequality of the estimate: if `d² ≤ a b`, then
`d (a + s d)(b + s d) ≤ (s + 1)² (a + b) a b`. -/
private lemma mul_mul_le_sq_mul_of_sq_le_mul {a b d s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) (hd2 : d ^ 2 ≤ a * b) :
    d * ((a + s * d) * (b + s * d)) ≤ (s + 1) ^ 2 * (a + b) * (a * b) := by
  have hdab : d ≤ a + b := by linarith [two_mul_le_add_of_sq_le_mul ha hb hd2]
  have h1 := mul_le_mul_of_nonneg_right hdab (mul_nonneg ha hb)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd2 (add_nonneg ha hb)) hs
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul hdab hd2 (sq_nonneg d) (add_nonneg ha hb))
    (sq_nonneg s)
  have h4 : 0 ≤ s * ((a + b) * (a * b)) := by positivity
  linarith

/-- The correction terms: if `x μ ≤ 2 P`, `μ ≤ P` and `2 A + B ≤ t μ` with `μ > 0`, then
`A x + B ≤ t P`. -/
private lemma mul_add_le_mul_of_mul_le {A B x μ P t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 0 < μ) (hxμ : x * μ ≤ 2 * P) (hμP : μ ≤ P) (ht : 2 * A + B ≤ t * μ) :
    A * x + B ≤ t * P := by
  refine le_of_mul_le_mul_right ?_ hμ
  linarith [mul_le_mul_of_nonneg_left hxμ hA, mul_le_mul_of_nonneg_left hμP hB,
    mul_le_mul_of_nonneg_right ht (hμ.le.trans hμP)]

/-- The logarithm of the number of unknowns: if `1 ≤ N_u ≤ M (a + s d)(b + s d)` with
`d ≤ a + b ≤ 2 g² d²`, then `log N_u ≤ log (4 M (1 + s)² g⁴) + 4 log d`. -/
private lemma log_le_log_add_four_mul_log {M a b d s g N_u : ℝ} (hM : 0 < M) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hd : 0 < d) (hs : 0 ≤ s) (hg : 0 < g) (hNu1 : 1 ≤ N_u)
    (hNu : N_u ≤ M * ((a + s * d) * (b + s * d))) (hdx : d ≤ a + b)
    (hx : a + b ≤ 2 * (g ^ 2 * d ^ 2)) :
    log N_u ≤ log (4 * M * (1 + s) ^ 2 * g ^ 4) + 4 * log d := by
  have hsd := mul_le_mul_of_nonneg_left hdx hs
  have h1 : (a + s * d) * (b + s * d) ≤ ((1 + s) * (2 * (g ^ 2 * d ^ 2))) ^ 2 := by
    rw [sq]
    have h : (1 + s) * (a + b) ≤ (1 + s) * (2 * (g ^ 2 * d ^ 2)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  calc log N_u ≤ log (4 * M * (1 + s) ^ 2 * g ^ 4 * d ^ 4) := log_le_log (by linarith)
        ((hNu.trans (mul_le_mul_of_nonneg_left h1 hM.le)).trans_eq (by ring))
    _ = _ := by rw [log_mul (by positivity) (by positivity), log_pow]; push_cast; ring

/-- The error term `ε₁₃(d) + A / d + 4 log d / d` tends to `0`. -/
private lemma tendsto_add_mul_one_div_add_four_mul_log_div {ε₁₃ : ℕ → ℝ}
    (h : Tendsto ε₁₃ atTop (nhds 0)) (A : ℝ) :
    Tendsto (fun d : ℕ => ε₁₃ d + A * (1 / (d : ℝ)) + 4 * (log d / d)) atTop (nhds 0) := by
  have hlog : Tendsto (fun d : ℕ => log (d : ℝ) / d) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  simpa using (h.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul A)).add (hlog.const_mul 4)

/-- The coefficient of the estimate: if `x ≤ ε γ / (4 B)` and
`η = min (1 / 2) (ε γ / (4 (c B + 1)))`, then `B (c + x) ≤ (c B + ε γ)(1 - η)`. -/
private lemma mul_add_le_mul_one_sub_min {B c x ε γ : ℝ} (hB : 0 < B) (hc : 0 ≤ c) (hε : 0 < ε)
    (hγ : 0 < γ) (hx : x ≤ ε * γ / (4 * B)) :
    B * (c + x) ≤ (c * B + ε * γ) * (1 - min (1 / 2) (ε * γ / (4 * (c * B + 1)))) := by
  have hBx : B * x ≤ ε * γ / 4 := by
    have := mul_le_mul_of_nonneg_left hx hB.le
    rwa [mul_div_assoc', mul_comm (4 : ℝ), ← div_div, mul_div_cancel_left₀ _ hB.ne'] at this
  have hη0 : 0 ≤ min (1 / 2 : ℝ) (ε * γ / (4 * (c * B + 1))) :=
    le_min (by norm_num) (by positivity)
  have hη := (le_div_iff₀ (by positivity)).mp
    (min_le_right (1 / 2 : ℝ) (ε * γ / (4 * (c * B + 1))))
  linarith [mul_le_mul_of_nonneg_right (min_le_left (1 / 2 : ℝ) (ε * γ / (4 * (c * B + 1))))
    (mul_pos hε hγ).le]

/-- The final estimate in the proof of Bombieri's Lemma 7: under the bounds on `N_u`, `S`
and `H`, for `min d₁ d₂` large enough, `S > 0` and
`(N_u / S) (H + log N_u + c_k) ≤ c₁₃ (m + 1)(s + 1)² (d₁ + d₂) / γ + ε (d₁ + d₂)`. -/
@[faltings "lem_bvs_lemma7_estimate"]
public theorem exists_pos_and_div_mul_add_log_le {g m N s : ℕ} (hg : 2 ≤ g) (hs : 1 ≤ s)
    (hN : 2 * g + 1 ≤ N) {γ c₁₃ c_k c₁₄ : ℝ} (hγ : 0 < γ) (hc₁₃ : 0 ≤ c₁₃) (hc_k : 0 ≤ c_k)
    (hc₁₄ : 0 ≤ c₁₄) {ε₁₃ : ℕ → ℝ} (hε₁₃ : ∀ d, 0 < d → 0 ≤ ε₁₃ d)
    (hε₁₃_tendsto : Tendsto ε₁₃ atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℕ, ∀ d₁ d₂ d : ℕ, 0 < d₁ → 0 < d₂ → 0 < d → D₁ ≤ min d₁ d₂ →
      g * d ^ 2 < d₁ * d₂ → d₁ * d₂ < g ^ 2 * d ^ 2 →
      ∀ N_u S H : ℝ,
        1 ≤ N_u →
        N_u ≤ (m + 1) * N ^ 2 * (((d₁ : ℝ) + s * d) / N) * (((d₂ : ℝ) + s * d) / N) →
        γ * d₁ * d₂ - c₁₄ * (((d₁ : ℝ) + s * d) / N + ((d₂ : ℝ) + s * d) / N)
          - (m + 1) * ((g : ℝ) - 1) ^ 2 ≤ S →
        0 ≤ H → H ≤ c₁₃ * d + ε₁₃ d * d →
        0 < S ∧
          N_u / S * (H + log N_u + c_k) ≤
            c₁₃ * (m + 1) * (s + 1) ^ 2 * ((d₁ : ℝ) + d₂) / γ + ε * ((d₁ : ℝ) + d₂) := by
  set B : ℝ := ((m : ℝ) + 1) * ((s : ℝ) + 1) ^ 2 with hB
  set C : ℝ := log (4 * ((m : ℝ) + 1) * (1 + (s : ℝ)) ^ 2 * (g : ℝ) ^ 4)
  -- the vanishing function of `d`, and the threshold `Dd` on `d`
  set F : ℕ → ℝ := fun d => ε₁₃ d + (C + c_k) * (1 / (d : ℝ)) + 4 * (log d / d) with hFdef
  have hF : Tendsto F atTop (nhds 0) :=
    tendsto_add_mul_one_div_add_four_mul_log_div hε₁₃_tendsto (C + c_k)
  obtain ⟨Dd, hDd⟩ := eventually_atTop.mp
    (hF.eventually (eventually_le_nhds (show 0 < ε * γ / (4 * B) by positivity)))
  -- the threshold `η₀` on the relative size of the correction terms
  set η₀ : ℝ := min (1 / 2) (ε * γ / (4 * (c₁₃ * B + 1)))
  have hη₀0 : 0 < η₀ := lt_min (by norm_num) (by positivity)
  set K : ℝ := 2 * (c₁₄ * (1 + s)) + (m + 1) * ((g : ℝ) - 1) ^ 2
  refine ⟨max (max 1 (g ^ 2 * Dd ^ 2)) ⌈K / (γ * η₀)⌉₊, ?_⟩
  intro d₁ d₂ d hd₁ hd₂ hd hD hlow hup N_u S H hNu1 hNu hS hH0 hH
  obtain ⟨⟨hD1, hD2⟩, hD3⟩ := by simpa only [max_le_iff] using hD
  have hminP : min d₁ d₂ ≤ d₁ * d₂ := (min_le_left _ _).trans (Nat.le_mul_of_pos_right _ hd₂)
  have hFd : F d ≤ ε * γ / (4 * B) := hDd d <| by
    have : g ^ 2 * Dd ^ 2 < g ^ 2 * d ^ 2 := by omega
    exact ((Nat.pow_lt_pow_iff_left two_ne_zero).mp (Nat.lt_of_mul_lt_mul_left this)).le
  -- the real inequalities between `d₁`, `d₂`, `d` and `μ = min d₁ d₂`
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd₁R : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hd₂R : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hlowR : (g : ℝ) * d ^ 2 < d₁ * d₂ := by exact_mod_cast hlow
  have hupR : (d₁ : ℝ) * d₂ < g ^ 2 * d ^ 2 := by exact_mod_cast hup
  have hd2P : (d : ℝ) ^ 2 ≤ d₁ * d₂ := by
    linarith [le_mul_of_one_le_left (sq_nonneg (d : ℝ)) (by linarith : (1 : ℝ) ≤ g)]
  have h2d := two_mul_le_add_of_sq_le_mul hd₁R.le hd₂R.le hd2P
  have hμ1 : (1 : ℝ) ≤ (min d₁ d₂ : ℕ) := by exact_mod_cast hD1
  have hμP : ((min d₁ d₂ : ℕ) : ℝ) ≤ d₁ * d₂ := by exact_mod_cast hminP
  have hxμ : ((d₁ : ℝ) + d₂) * (min d₁ d₂ : ℕ) ≤ 2 * (d₁ * d₂) := by
    push_cast
    linarith [mul_le_mul_of_nonneg_left (min_le_right (d₁ : ℝ) d₂) hd₁R.le,
      mul_le_mul_of_nonneg_left (min_le_left (d₁ : ℝ) d₂) hd₂R.le]
  have hKμ : K ≤ γ * η₀ * (min d₁ d₂ : ℕ) := by
    have h : K / (γ * η₀) ≤ ((min d₁ d₂ : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hD3)
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  -- `S ≥ (1 - η₀) γ d₁ d₂`
  have hδ : ((d₁ : ℝ) + s * d) / N + ((d₂ : ℝ) + s * d) / N ≤ (1 + s) * (d₁ + d₂) := by
    rw [← add_div]
    refine (div_le_self (by positivity) hNR).trans ?_
    linarith [mul_le_mul_of_nonneg_left h2d (Nat.cast_nonneg (α := ℝ) s)]
  have hE := mul_add_le_mul_of_mul_le (mul_nonneg hc₁₄ (by positivity)) (by positivity)
    (by linarith) hxμ hμP hKμ
  have hSlow : (1 - η₀) * γ * (d₁ * d₂) ≤ S := by
    linarith [mul_le_mul_of_nonneg_left hδ hc₁₄]
  have hSpos : 0 < S := by
    have : 0 < 1 - η₀ := by linarith [min_le_left (1 / 2 : ℝ) (ε * γ / (4 * (c₁₃ * B + 1)))]
    linarith [mul_pos (mul_pos this hγ) (mul_pos hd₁R hd₂R)]
  refine ⟨hSpos, ?_⟩
  -- the bound on `H + log N_u + c_k`
  have hNuA : N_u ≤ (m + 1) * (((d₁ : ℝ) + s * d) * ((d₂ : ℝ) + s * d)) := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    convert hNu using 1
    field_simp
  have hlog := log_le_log_add_four_mul_log (g := (g : ℝ)) (by positivity) hd₁R.le hd₂R.le hdR
    (by positivity) (by positivity) hNu1 hNuA (by linarith)
    (by linarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ d₁ + d₂) hμ1])
  have hT : H + log N_u + c_k ≤ d * (c₁₃ + F d) := by
    have : (d : ℝ) * (c₁₃ + F d) = c₁₃ * d + ε₁₃ d * d + C + c_k + 4 * log d := by
      simp only [hFdef]; field_simp; ring
    rw [this]; linarith
  have hT0 : 0 ≤ H + log N_u + c_k := by linarith [log_nonneg hNu1]
  -- the coefficient `B (c₁₃ + F d) ≤ (c₁₃ B + ε γ)(1 - η₀)`
  have hcoef : B * (c₁₃ + F d) ≤ (c₁₃ * B + ε * γ) * (1 - η₀) :=
    mul_add_le_mul_one_sub_min (by positivity) hc₁₃ hε hγ hFd
  rw [div_mul_eq_mul_div, div_le_iff₀ hSpos]
  calc N_u * (H + log N_u + c_k)
      ≤ (m + 1) * (((d₁ : ℝ) + s * d) * ((d₂ : ℝ) + s * d)) * (d * (c₁₃ + F d)) :=
        mul_le_mul hNuA hT hT0 (by positivity)
    _ = ((m : ℝ) + 1) * (c₁₃ + F d) * (d * (((d₁ : ℝ) + s * d) * ((d₂ : ℝ) + s * d))) := by ring
    _ ≤ ((m : ℝ) + 1) * (c₁₃ + F d) * ((s + 1) ^ 2 * (d₁ + d₂) * (d₁ * d₂)) := by
        refine mul_le_mul_of_nonneg_left (mul_mul_le_sq_mul_of_sq_le_mul hd₁R.le hd₂R.le
          (by positivity) hd2P) (mul_nonneg (by positivity)
          ((mul_nonneg_iff_of_pos_left hdR).mp (hT0.trans hT)))
    _ = ((d₁ : ℝ) + d₂) * (d₁ * d₂) * (B * (c₁₃ + F d)) := by ring
    _ ≤ ((d₁ : ℝ) + d₂) * (d₁ * d₂) * ((c₁₃ * B + ε * γ) * (1 - η₀)) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = (c₁₃ * (m + 1) * (s + 1) ^ 2 * ((d₁ : ℝ) + d₂) / γ + ε * ((d₁ : ℝ) + d₂)) *
          ((1 - η₀) * γ * (d₁ * d₂)) := by rw [hB]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hSlow (by positivity)

end Faltings.BombieriVojta
