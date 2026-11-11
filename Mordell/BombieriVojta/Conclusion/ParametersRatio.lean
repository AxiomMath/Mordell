module
public import Mordell.BombieriVojta.Conclusion.Parameters

/-!
# The ratio of the parameters `d₂ / d₁`

Let `(d₁, d₂, d) = Faltings.bombieriParameters g s N γ₀ |z| |w| D` be the parameters of
Bombieri's proof attached to `(γ₀, z, w, D)`. Since `d₁ ≥ √(g + γ₀) D / |z|² > 0` and
`d₂ ≤ √(g + γ₀) D / |w|²`, the ratio satisfies `d₂ / d₁ ≤ |z|² / |w|²`.

## Main results

* `Faltings.bombieriParameters_div_le`: `d₂ / d₁ ≤ a² / b²` for the parameters attached to
  `(γ₀, z, w, D)`, with `a = |z|` and `b = |w|`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, p. 638
-/

namespace Faltings

/-- Rounding `x` up to an integer in a prescribed residue class modulo `N ≠ 0` stays `≥ x`. -/
private lemma le_ceil_add_emod (x : ℝ) (r : ℤ) {N : ℤ} (hN : N ≠ 0) :
    x ≤ ((⌈x⌉ + r % N : ℤ) : ℝ) := by
  have : (0 : ℝ) ≤ (r % N : ℤ) := by exact_mod_cast Int.emod_nonneg r hN
  push_cast at this ⊢
  linarith [Int.le_ceil x]

/-- Rounding `y` down to an integer in a prescribed residue class modulo `N ≠ 0` stays `≤ y`. -/
private lemma floor_sub_emod_le (y : ℝ) (r : ℤ) {N : ℤ} (hN : N ≠ 0) :
    ((⌊y⌋ - r % N : ℤ) : ℝ) ≤ y := by
  have : (0 : ℝ) ≤ (r % N : ℤ) := by exact_mod_cast Int.emod_nonneg r hN
  push_cast at this ⊢
  linarith [Int.floor_le y]

/-- **Ratio of the parameters.** If `(d₁, d₂, d)` are the parameters attached to
`(γ₀, z, w, D)` (`Faltings.bombieriParameters`, with `a = |z|`, `b = |w|`), then
`d₂ / d₁ ≤ a² / b²`: the numerator is at most `√(g + γ₀) D / b²` and the denominator at least
`√(g + γ₀) D / a² > 0`. -/
@[faltings "lem_bvr_parameter_ratio"]
public theorem bombieriParameters_div_le {g : ℕ} {s : ℤ} {N : ℕ} {γ₀ a b D : ℝ}
    (hs : 1 ≤ s) (hN : 2 * g + 1 ≤ N) (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    ((bombieriParameters g s N γ₀ a b D).2.1 : ℝ) / (bombieriParameters g s N γ₀ a b D).1 ≤
      a ^ 2 / b ^ 2 := by
  have hN0 : (N : ℤ) ≠ 0 := by omega
  have hb : 0 < b := ha.trans_le hab
  calc _ ≤ (Real.sqrt (g + γ₀) * D / b ^ 2) / (Real.sqrt (g + γ₀) * D / a ^ 2) :=
        div_le_div₀ (by positivity) (floor_sub_emod_le _ _ hN0) (by positivity)
          (le_ceil_add_emod _ _ hN0)
    _ = a ^ 2 / b ^ 2 := by field_simp

end Faltings
