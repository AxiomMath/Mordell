module
public import Mordell.BombieriVojta.Conclusion.Parameters

/-!
# Size of the parameters `d₁, d₂, d`

With `λ = √(g + γ₀)`, the parameters `(d₁, d₂, d) = bombieriParameters g s N γ₀ |z| |w| D` of
Bombieri's proof satisfy `0 ≤ d - D/(|z||w|) < 1`, `0 ≤ d₁ - λD/|z|² < N` and
`0 ≤ λD/|w|² - d₂ < N`: each parameter is its real target up to an error bounded independently of
`D`.

## Main results

* `Faltings.bombieriParameters_bounds`: the three two-sided bounds.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, p. 638
-/

namespace Faltings

/-- Rounding `x` up to `⌈x⌉` and then adding a residue modulo `N > 0` overshoots `x` by an amount
in `[0, N)`: `⌈x⌉ - x ∈ [0, 1)` and `m % N ∈ [0, N - 1]`. -/
private lemma ceil_add_emod_sub_mem_Ico (x : ℝ) (m : ℤ) {N : ℤ} (hN : 0 < N) :
    0 ≤ ((⌈x⌉ + m % N : ℤ) : ℝ) - x ∧ ((⌈x⌉ + m % N : ℤ) : ℝ) - x < N := by
  have h₀ : (0 : ℝ) ≤ (m % N : ℤ) := by exact_mod_cast Int.emod_nonneg m hN.ne'
  have h₁ : ((m % N : ℤ) : ℝ) + 1 ≤ N := by exact_mod_cast Int.emod_lt_of_pos m hN
  push_cast
  constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

/-- The dual of `ceil_add_emod_sub_mem_Ico`: rounding `y` down to `⌊y⌋` and then subtracting a
residue modulo `N > 0` undershoots `y` by an amount in `[0, N)`. -/
private lemma sub_floor_sub_emod_mem_Ico (y : ℝ) (m : ℤ) {N : ℤ} (hN : 0 < N) :
    0 ≤ y - ((⌊y⌋ - m % N : ℤ) : ℝ) ∧ y - ((⌊y⌋ - m % N : ℤ) : ℝ) < N := by
  have h := ceil_add_emod_sub_mem_Ico (-y) m hN
  rw [Int.ceil_neg] at h
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Size of the parameters.** Writing `(d₁, d₂, d) = bombieriParameters g s N γ₀ a b D` and
`λ = √(g + γ₀)`: `0 ≤ d - D/(a b) < 1`, `0 ≤ d₁ - λ D / a² < N` and `0 ≤ λ D / b² - d₂ < N`. -/
@[faltings "lem_bvr_parameter_bounds"]
public theorem bombieriParameters_bounds (g : ℕ) (s : ℤ) (N : ℕ) (γ₀ a b D : ℝ)
    (hg : 2 ≤ g) (hs : 1 ≤ s) (hN : 2 * g + 1 ≤ N) (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    let p := bombieriParameters g s N γ₀ a b D
    (0 ≤ (p.2.2 : ℝ) - D / (a * b) ∧ (p.2.2 : ℝ) - D / (a * b) < 1) ∧
    (0 ≤ (p.1 : ℝ) - Real.sqrt (g + γ₀) * D / a ^ 2 ∧
      (p.1 : ℝ) - Real.sqrt (g + γ₀) * D / a ^ 2 < N) ∧
    (0 ≤ Real.sqrt (g + γ₀) * D / b ^ 2 - (p.2.1 : ℝ) ∧
      Real.sqrt (g + γ₀) * D / b ^ 2 - (p.2.1 : ℝ) < N) := by
  have hN0 : (0 : ℤ) < N := by omega
  exact ⟨⟨sub_nonneg.2 (Int.le_ceil _), sub_lt_iff_lt_add'.2 (Int.ceil_lt_add_one _)⟩,
    ceil_add_emod_sub_mem_Ico _ _ hN0, sub_floor_sub_emod_mem_Ico _ _ hN0⟩

end Faltings
