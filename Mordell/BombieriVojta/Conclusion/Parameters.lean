module
public import Mathlib
public import Mordell.Attr

/-!
# The parameters `d₁, d₂, d` of Bombieri's proof

In Section 10 of Bombieri's proof of the Mordell conjecture one fixes `0 < γ₀ ≤ 1/10`, two points
`z, w` of the curve with Néron–Tate norms `0 < |z| ≤ |w|`, and a large real `D > 0`, and chooses
the multidegree of the Vojta divisor as
`d = ⌈D / (|z| |w|)⌉`, `d₁` the least integer `≥ √(g + γ₀) D / |z|²` with `d₁ ≡ -s d (mod N)`,
and `d₂` the largest integer `≤ √(g + γ₀) D / |w|²` with `d₂ ≡ -s d (mod N)`.
Here `g` is the genus, `s` the integer making `s P × C + s C × P - Δ'` very ample, and `N` the
integer of the embedding `φ_{NP}`.

## Main definitions

* `Faltings.bombieriParameters g s N γ₀ a b D`: the triple `(d₁, d₂, d)` attached to
  `(γ₀, z, w, D)`, where `a = |z|` and `b = |w|`.

## Implementation notes

The parameters depend on `z` and `w` only through their Néron–Tate norms, so the definition takes
the two norms `a = |z|`, `b = |w|` as real numbers. The least integer `≥ x` congruent to `r`
modulo `N` is written `⌈x⌉ + (r - ⌈x⌉) % N`, and the largest integer `≤ y` congruent to `r` is
`⌊y⌋ - (⌊y⌋ - r) % N`; for `N > 0` these are the integers of the source (`Int.emod` takes values in
`[0, N)`). The conditions `0 < γ₀ ≤ 1/10`, `0 < |z| ≤ |w|`, `D > 0` and the standing ones on `g`,
`s`, `N` are not needed to write down the triple; they are hypotheses of the lemmas about it.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, p. 638
-/

namespace Faltings

/-- **The parameters `(d₁, d₂, d)` attached to `(γ₀, z, w, D)`** in Bombieri's proof, with
`a = |z|` and `b = |w|` the Néron–Tate norms of `z` and `w`: `d = ⌈D / (a b)⌉`, `d₁` is the least
integer `≥ √(g + γ₀) D / a²` with `d₁ ≡ -s d (mod N)`, and `d₂` is the largest integer
`≤ √(g + γ₀) D / b²` with `d₂ ≡ -s d (mod N)`. -/
@[expose, faltings "def_bvr_parameters"]
public noncomputable def bombieriParameters (g : ℕ) (s : ℤ) (N : ℕ) (γ₀ a b D : ℝ) :
    ℤ × ℤ × ℤ :=
  let d : ℤ := ⌈D / (a * b)⌉
  let x : ℝ := Real.sqrt (g + γ₀) * D / a ^ 2
  let y : ℝ := Real.sqrt (g + γ₀) * D / b ^ 2
  (⌈x⌉ + (-(s * d) - ⌈x⌉) % (N : ℤ), ⌊y⌋ - (⌊y⌋ + s * d) % (N : ℤ), d)

end Faltings
