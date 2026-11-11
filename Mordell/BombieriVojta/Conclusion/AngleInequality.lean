module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.ThetaPolarization
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma6
public import Mordell.BombieriVojta.Conclusion.Parameters
public import Mordell.BombieriVojta.Conclusion.Lemma8
public import Mordell.BombieriVojta.Conclusion.MainInequality
public import Mordell.BombieriVojta.Conclusion.ParametersSize
public import Mordell.BombieriVojta.Conclusion.ParametersChoice
public import Mordell.BombieriVojta.Conclusion.ParametersRatio
public import Mordell.NeronTate.Pairing.CauchySchwarz
public import Mordell.BombieriVojta.SmallSection.Lemma7
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.BombieriVojta.Height.NPNeronNorm
public import Mordell.Curve.DegreeOverRationalSubfield
public import StacksFrontier.AlgebraicGeometry.Curves.ModelFunctionFieldInvariance
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint

/-!
# The angle inequality

Let `C` be a smooth projective curve of genus `g ≥ 2` over a number field `k`, with a divisor
`P` of degree one, Jacobian `J`, Abel–Jacobi map `j = j_P`, Néron form `⟨ , ⟩` of the theta class
on `J(k̄)` and norm `|z| = √⟨z, z⟩`, where `⟨z, w⟩ = ⟨j z, j w⟩` for `z, w ∈ C(k̄)`. Fix the
standing data of Bombieri's Sections 9 and 10: a generic basis `x` of `H⁰(C, 𝒪(N P))`,
`N ≥ 2g + 1`, giving `φ_{NP}`, `ψ = φ_{NP} × φ_{NP}`, and a basis `y` of `H⁰(C × C, 𝒪(B))`,
`B = (s + 1)(P × C) + (s + 1)(C × P) - Δ`, generic for the projections and giving `φ_B`, and let
`Z` be the exceptional set. Then there are constants `c₄, c₁₈, c₁₉` such that for every
`0 < γ₀ ≤ 1 / 10` there is a constant `c₂₀` with
`⟨z, w⟩ / (|z| |w|) ≤ √(g + γ₀) / g + c₄ √(g + γ₀) 8 N ε +`
`c₁₉ (1 / |z| + 1 / |w|) + c₁₈ / (γ₀ |z|²)`
for all `0 < ε < 1` and all `z, w ∈ C(k̄) \ Z` with `|z| ≥ c₂₀ / ε` and `|z| / |w| ≤ ε`.

This is the conclusion of Vojta's argument in Bombieri's form: the auxiliary section of
Bombieri's Lemma 7 has small index at `(z, w)` (his Lemma 8), and substituting this into the
main inequality and letting the degree go to infinity bounds the angle between `j z` and `j w`.
The constant `c₄` is the one of the main inequality.

## Main results

* `Faltings.exists_neronPairing_div_le`: the angle inequality.

## Implementation notes

The setting is that of `Faltings.BombieriRoth.exists_neg_le_neronPairing_of_isAdmissiblePair`
(the main inequality) and `Faltings.exists_neronPairing_abelJacobi_le` (Bombieri's Theorem 1):
the curve `X : Faltings.CurveWithDegreeOneDivisor k`, its Jacobian `A`, the Abel–Jacobi map `j`
and the class `θ` of the reduced effective Cartier divisor `D` supported on
`Faltings.thetaDivisor` define `Faltings.neronPairing` on `J(k̄)`, and the standing data `x`,
`φ_{NP}`, `ψ`, `y`, `φ_B` live over `k` on `C` and `C ×_k C`. A point `z ∈ C(k̄)` is a morphism
`Spec k̄ ⟶ C` over `k`.

The exceptional set `Faltings.BombieriSiegel.exceptionalSet` is a set of `K`-rational points of
a curve over a field `K`. As in the main inequality, `z, w ∉ Z` is read at every number field
`K ⊆ k̄` (a `k`-embedding `ι : K → k̄`) over which `(z, w)` is defined: on the base change `C_K`
of `C`, with `x` replaced by its pull-back and `N P` by `Q ↦ N P(π Q)` for the projection
`π : C_K ⟶ C`, the two components of the `K`-point `p_K` of `C_K ×_K C_K` through which
`(z, w)` factors lie outside the exceptional set. The exceptional set is invariant under
enlarging `K`, so this is the source's condition.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, pp. 637–638
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings

open BombieriSiegel

section

open Filter BombieriRoth
open Stacks.ProjectiveFromSections (resT resO resM)

-- `Stacks.PicardFunctor.isVariety_curveOver` concludes `IsVariety ?k ?f` for every goal and
-- sends the search for `IsIntegral C` (behind `C.functionField`) through every field; the
-- curves here carry their own instances
attribute [-instance] Stacks.PicardFunctor.isVariety_curveOver

/-- If `α D ≤ β D + K` for all large `D`, then `α ≤ β`. -/
private theorem le_of_eventually_mul_le_mul_add {α β : ℝ} (K : ℝ)
    (h : ∀ᶠ D in atTop, α * D ≤ β * D + K) : α ≤ β := by
  by_contra hlt
  have hpos : 0 < α - β := sub_pos.2 (not_le.1 hlt)
  obtain ⟨D, hD, hD'⟩ := (h.and (eventually_gt_atTop ((|K| + 1) / (α - β)))).exists
  rw [div_lt_iff₀ hpos] at hD'
  nlinarith [le_abs_self K]

/-- The substitution step of the angle inequality, as an estimate between real numbers: if for all
large `D` the parameters `d₁, d₂, d` lie within the bounds of `Faltings.bombieriParameters_bounds`,
the pair `(i₁, i₂)` satisfies `iₗ ≤ 4 N ε dₗ`, and the main inequality holds, then dividing by `D`
and letting `D → ∞` bounds the angle `P / (a b)`. -/
private theorem angle_bound_of_eventually {g N c₄ c₁₇ c₁ γ₀ ε a b P : ℝ}
    (hg : 1 ≤ g) (hN : 0 ≤ N) (hc₄ : 0 ≤ c₄) (hc₁₇ : 0 ≤ c₁₇) (hc₁ : 0 ≤ c₁)
    (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) (hab : a ≤ b)
    (hP : |P| ≤ a * b)
    (h : ∀ᶠ D in atTop, ∃ d₁ d₂ d i₁ i₂ : ℝ,
      (0 ≤ d - D / (a * b) ∧ d - D / (a * b) < 1) ∧
      (0 ≤ d₁ - √(g + γ₀) * D / a ^ 2 ∧ d₁ - √(g + γ₀) * D / a ^ 2 < N) ∧
      (0 ≤ √(g + γ₀) * D / b ^ 2 - d₂ ∧ √(g + γ₀) * D / b ^ 2 - d₂ < N) ∧
      0 ≤ i₁ ∧ 0 ≤ i₂ ∧ i₁ ≤ 4 * N * ε * d₁ ∧ i₂ ≤ 4 * N * ε * d₂ ∧
      -c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2) - c₁₇ * (d₁ + i₁ + i₂) -
          c₁₇ * d₁ / (γ₀ / (2 * (g + γ₀))) ≤
        d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 - d * P + c₁ * (d₁ * a + d₂ * b)) :
    P / (a * b) ≤ √(g + γ₀) / g + c₄ * √(g + γ₀) * (8 * N * ε) +
      c₁ * √(g + 1) * (1 / a + 1 / b) +
      c₁₇ * √(g + 1) * (8 * N + 2 * g + 3) / (γ₀ * a ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  set l := √(g + γ₀) with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 (by linarith)
  have hl1 : l ≤ √(g + 1) := Real.sqrt_le_sqrt (by linarith)
  have hg0 : 0 < g := by linarith
  set r := √(g + 1)
  set M : ℝ := 8 * N + 2 * g + 3 with hMdef
  have hM : 0 ≤ M := by positivity
  set K : ℝ := c₄ * (4 * N * ε) * (N * a ^ 2) + c₁₇ * M * N / γ₀ +
    N * a ^ 2 / (2 * g) + a * b + c₁ * (N * a)
  have key := le_of_eventually_mul_le_mul_add (α := P / (a * b) - c₄ * l * (8 * N * ε) -
    c₁₇ * r * M / (γ₀ * a ^ 2)) (β := l / g + c₁ * r * (1 / a + 1 / b)) K ?_
  · linarith
  filter_upwards [h, eventually_gt_atTop 0] with D ⟨d₁, d₂, d, i₁, i₂, ⟨hd0, hd1⟩, ⟨hA0, hA1⟩,
    ⟨hB0, hB1⟩, hi₁, hi₂, hi₁', hi₂', hmain⟩ hD
  set X₁ := l * D / a ^ 2 with hX₁
  set Y₂ := l * D / b ^ 2 with hY₂
  have hXa : X₁ * a ^ 2 = l * D := by rw [hX₁]; field_simp
  have hYb : Y₂ * b ^ 2 = l * D := by rw [hY₂]; field_simp
  have hYX : Y₂ ≤ X₁ := by
    rw [hX₁, hY₂]; gcongr
  have hX0 : 0 ≤ X₁ := by positivity
  have hd₁X : X₁ ≤ d₁ := by linarith
  have hd₁X' : d₁ ≤ X₁ + N := by linarith
  have hd₂Y : d₂ ≤ Y₂ := by linarith
  have hd₁0 : 0 ≤ d₁ := hX0.trans hd₁X
  have hd₂d₁ : d₂ ≤ d₁ := (hd₂Y.trans hYX).trans hd₁X
  have hNε : 0 ≤ 4 * N * ε := by positivity
  have h1 : c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2) ≤
      c₄ * l * (8 * N * ε) * D + c₄ * (4 * N * ε) * (N * a ^ 2) := by
    have e1 : i₁ * a ^ 2 ≤ 4 * N * ε * (l * D + N * a ^ 2) := by
      calc i₁ * a ^ 2 ≤ 4 * N * ε * d₁ * a ^ 2 := by gcongr
        _ ≤ 4 * N * ε * ((X₁ + N) * a ^ 2) := by
          rw [mul_assoc]; gcongr
        _ = _ := by rw [add_mul, hXa]
    have e2 : i₂ * b ^ 2 ≤ 4 * N * ε * (l * D) := by
      calc i₂ * b ^ 2 ≤ 4 * N * ε * d₂ * b ^ 2 := by gcongr
        _ ≤ 4 * N * ε * (Y₂ * b ^ 2) := by
          rw [mul_assoc]; gcongr
        _ = _ := by rw [hYb]
    have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hc₄
    have e : c₄ * (4 * N * ε * (l * D + N * a ^ 2) + 4 * N * ε * (l * D)) =
      c₄ * l * (8 * N * ε) * D + c₄ * (4 * N * ε) * (N * a ^ 2) := by ring
    linarith
  have h2 : c₁₇ * (d₁ + i₁ + i₂) + c₁₇ * d₁ / (γ₀ / (2 * (g + γ₀))) ≤
      c₁₇ * r * M / (γ₀ * a ^ 2) * D + c₁₇ * M * N / γ₀ := by
    have hii : i₁ + i₂ ≤ 8 * N * d₁ := by
      have e1 : 4 * N * ε * d₂ ≤ 4 * N * ε * d₁ := by gcongr
      have e2 : 4 * N * ε * d₁ ≤ 4 * N * d₁ := by
        have := mul_le_mul_of_nonneg_left hε1.le (by positivity : 0 ≤ 4 * N * d₁)
        linarith [show 4 * N * d₁ * ε = 4 * N * ε * d₁ by ring]
      linarith
    have hdiv : c₁₇ * d₁ / (γ₀ / (2 * (g + γ₀))) = c₁₇ * d₁ * (2 * g / γ₀ + 2) := by
      field_simp
    have hcoef : 1 + 8 * N + (2 * g / γ₀ + 2) ≤ M / γ₀ := by
      rw [show M / γ₀ = (8 * N + 3) / γ₀ + 2 * g / γ₀ by rw [← add_div]; ring]
      have : 8 * N + 3 ≤ (8 * N + 3) / γ₀ := by
        rw [le_div_iff₀ hγ₀]
        have := mul_le_mul_of_nonneg_left hγ₀' (by positivity : 0 ≤ 8 * N + 3)
        linarith
      linarith
    have s1 : c₁₇ * (d₁ + i₁ + i₂) + c₁₇ * d₁ / (γ₀ / (2 * (g + γ₀))) ≤
        c₁₇ * (d₁ * (1 + 8 * N + (2 * g / γ₀ + 2))) := by
      rw [hdiv]
      have := mul_le_mul_of_nonneg_left hii hc₁₇
      have e : c₁₇ * (d₁ * (1 + 8 * N + (2 * g / γ₀ + 2))) =
        c₁₇ * d₁ + c₁₇ * (8 * N * d₁) + c₁₇ * d₁ * (2 * g / γ₀ + 2) := by ring
      linarith [show c₁₇ * (d₁ + i₁ + i₂) = c₁₇ * d₁ + c₁₇ * (i₁ + i₂) by ring]
    have s2 : c₁₇ * (d₁ * (1 + 8 * N + (2 * g / γ₀ + 2))) ≤ c₁₇ * ((X₁ + N) * (M / γ₀)) := by
      gcongr
    have s3 : c₁₇ * ((X₁ + N) * (M / γ₀)) =
        c₁₇ * l * M / (γ₀ * a ^ 2) * D + c₁₇ * M * N / γ₀ := by
      rw [hX₁]; field_simp
    have s4 : c₁₇ * l * M / (γ₀ * a ^ 2) * D ≤ c₁₇ * r * M / (γ₀ * a ^ 2) * D := by
      gcongr
    linarith
  have h3 : d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 ≤ l / g * D + N * a ^ 2 / (2 * g) := by
    have e1 : d₁ * a ^ 2 ≤ l * D + N * a ^ 2 := by
      calc d₁ * a ^ 2 ≤ (X₁ + N) * a ^ 2 := by gcongr
        _ = _ := by rw [add_mul, hXa]
    have e2 : d₂ * b ^ 2 ≤ l * D := by
      calc d₂ * b ^ 2 ≤ Y₂ * b ^ 2 := by gcongr
        _ = _ := hYb
    have e : d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 = (d₁ * a ^ 2 + d₂ * b ^ 2) / (2 * g) := by
      ring
    have e' : l / g * D + N * a ^ 2 / (2 * g) = (2 * (l * D) + N * a ^ 2) / (2 * g) := by
      field_simp
    rw [e, e']
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h4 : -(d * P) ≤ -(P / (a * b)) * D + a * b := by
    have hu : |d - D / (a * b)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have : -((d - D / (a * b)) * P) ≤ a * b := by
      have := neg_abs_le ((d - D / (a * b)) * P)
      rw [abs_mul] at this
      have := mul_le_mul hu hP (abs_nonneg _) zero_le_one
      linarith
    have e : d * P = (d - D / (a * b)) * P + P / (a * b) * D := by
      field_simp; ring
    linarith
  have h5 : c₁ * (d₁ * a + d₂ * b) ≤ c₁ * r * (1 / a + 1 / b) * D + c₁ * (N * a) := by
    have e1 : d₁ * a ≤ (X₁ + N) * a := by gcongr
    have e2 : d₂ * b ≤ Y₂ * b := by gcongr
    have e3 : (X₁ + N) * a + Y₂ * b = l * (1 / a + 1 / b) * D + N * a := by
      rw [hX₁, hY₂]; field_simp; ring
    have h' : l * (1 / a + 1 / b) * D ≤ r * (1 / a + 1 / b) * D := by gcongr
    have := mul_le_mul_of_nonneg_left
      ((add_le_add e1 e2).trans (e3.le.trans (add_le_add_left h' _))) hc₁
    linarith [show c₁ * (r * (1 / a + 1 / b) * D + N * a) =
      c₁ * r * (1 / a + 1 / b) * D + c₁ * (N * a) by ring]
  have e1 : (P / (a * b) - c₄ * l * (8 * N * ε) - c₁₇ * r * M / (γ₀ * a ^ 2)) * D =
      P / (a * b) * D - c₄ * l * (8 * N * ε) * D - c₁₇ * r * M / (γ₀ * a ^ 2) * D := by ring
  have e2 : (l / g + c₁ * r * (1 / a + 1 / b)) * D + K = l / g * D +
      c₁ * r * (1 / a + 1 / b) * D + K := by ring
  rw [e1, e2]
  have e3 : -c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2) = -(c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2)) := by ring
  have e4 : -(P / (a * b)) * D = -(P / (a * b) * D) := by ring
  linarith

/-- For large `D`, parameters within the bounds of `Faltings.bombieriParameters_bounds` satisfy
`d₂ / d₁ ≥ a² / (2 b²)`: the ratio tends to `a² / b²` as `D → ∞`. -/
private theorem eventually_div_mul_le_of_bounds {l a b N : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hb : 0 < b) (_hN : 0 ≤ N) :
    ∀ᶠ D in atTop, ∀ d₁ d₂ : ℝ, 0 ≤ d₁ → d₁ ≤ l * D / a ^ 2 + N → l * D / b ^ 2 - N ≤ d₂ →
      a ^ 2 / (2 * b ^ 2) * d₁ ≤ d₂ := by
  filter_upwards [eventually_ge_atTop (2 * b ^ 2 * N * (1 + a ^ 2 / (2 * b ^ 2)) / l)] with D hD
  intro d₁ d₂ hd₁ h1 h2
  have hq : 0 ≤ a ^ 2 / (2 * b ^ 2) := by positivity
  have e1 : a ^ 2 / (2 * b ^ 2) * d₁ ≤ a ^ 2 / (2 * b ^ 2) * (l * D / a ^ 2 + N) :=
    mul_le_mul_of_nonneg_left h1 hq
  have e2 : a ^ 2 / (2 * b ^ 2) * (l * D / a ^ 2 + N) =
      l * D / (2 * b ^ 2) + N * (a ^ 2 / (2 * b ^ 2)) := by field_simp
  have hD' : 2 * b ^ 2 * N * (1 + a ^ 2 / (2 * b ^ 2)) ≤ l * D := by
    rwa [div_le_iff₀ hl, mul_comm D] at hD
  have e3 : N * (1 + a ^ 2 / (2 * b ^ 2)) ≤ l * D / (2 * b ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e4 : l * D / b ^ 2 = 2 * (l * D / (2 * b ^ 2)) := by field_simp
  nlinarith

/-- The height hypothesis of Bombieri's Lemma 8 from the errata form of `h_{NP}`: if
`h(z) ≥ N / (2g) |z|² - c (1 + |z|)` and likewise for `w`, `|z| ≤ |w|`, `d₂ / d₁ ≥ |z|² / (2|w|²)`
and `|z| ≥ c₂₀ / ε` for a suitable `c₂₀`, then `min(d₁ h(z), d₂ h(w)) ≥ c₁₄ / (γ ε²) d₁`. -/
private theorem exists_div_mul_le_min_mul {g N c c₁₄ γ : ℝ} (hg : 1 ≤ g) (hN : 0 < N)
    (hc : 0 ≤ c) (hγ : 0 < γ) :
    ∃ c₂₀ : ℝ, 0 < c₂₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ a b hz hw d₁ d₂ : ℝ,
      c₂₀ / ε ≤ a → a ≤ b → N / (2 * g) * a ^ 2 - c * (1 + a) ≤ hz →
      N / (2 * g) * b ^ 2 - c * (1 + b) ≤ hw → 0 ≤ d₁ → a ^ 2 / (2 * b ^ 2) * d₁ ≤ d₂ →
      c₁₄ / (γ * ε ^ 2) * d₁ ≤ min (d₁ * hz) (d₂ * hw) := by
  set c₂₀ : ℝ := 1 + 32 * g * c / N + √(16 * g * |c₁₄| / (N * γ)) with hc₂₀
  have hg0 : 0 < g := by linarith
  have hs0 : 0 ≤ √(16 * g * |c₁₄| / (N * γ)) := Real.sqrt_nonneg _
  have hcg : 0 ≤ 32 * g * c / N := by positivity
  refine ⟨c₂₀, by positivity, fun ε hε hε1 a b hz hw d₁ d₂ ha hab hhz hhw hd₁ hd₂ => ?_⟩
  have hc₂₀a : c₂₀ ≤ a := by
    refine le_trans ?_ ha
    rw [le_div_iff₀ hε]
    have : c₂₀ * ε ≤ c₂₀ * 1 := mul_le_mul_of_nonneg_left hε1.le (by positivity)
    linarith
  have ha1 : 1 ≤ a := by linarith
  have hb0 : 0 < b := by linarith
  have herr : ∀ t : ℝ, c₂₀ ≤ t → c * (1 + t) ≤ N / (8 * g) * t ^ 2 := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith
    have h1 : 32 * g * c / N ≤ t := by linarith
    have h2 : 32 * g * c ≤ N * t := by rwa [div_le_iff₀ hN, mul_comm t] at h1
    have h3 : c * (1 + t) ≤ 2 * c * t := by nlinarith
    have h4 : 2 * c * t ≤ N / (8 * g) * t ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hza : N / (8 * g) * a ^ 2 ≤ hz := by
    have := herr a hc₂₀a
    have e : N / (2 * g) * a ^ 2 = 4 * (N / (8 * g) * a ^ 2) := by field_simp; ring
    nlinarith [show 0 ≤ N / (8 * g) * a ^ 2 by positivity]
  have hwb : N / (8 * g) * b ^ 2 ≤ hw := by
    have := herr b (hc₂₀a.trans hab)
    have e : N / (2 * g) * b ^ 2 = 4 * (N / (8 * g) * b ^ 2) := by field_simp; ring
    nlinarith [show 0 ≤ N / (8 * g) * b ^ 2 by positivity]
  have hmain : c₁₄ / (γ * ε ^ 2) ≤ N / (16 * g) * a ^ 2 := by
    have hsq : √(16 * g * |c₁₄| / (N * γ)) ≤ a * ε := by
      rw [div_le_iff₀ hε] at ha
      linarith
    have hsq2 : 16 * g * |c₁₄| / (N * γ) ≤ (a * ε) ^ 2 := by
      have := Real.sq_sqrt (show 0 ≤ 16 * g * |c₁₄| / (N * γ) by positivity)
      nlinarith [Real.sqrt_nonneg (16 * g * |c₁₄| / (N * γ))]
    rw [div_le_iff₀ (by positivity)] at hsq2
    rw [div_le_iff₀ (by positivity)]
    have e : N / (16 * g) * a ^ 2 * (γ * ε ^ 2) = (a * ε) ^ 2 * (N * γ) / (16 * g) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [le_abs_self c₁₄]
  refine le_min ?_ ?_
  · have : N / (16 * g) * a ^ 2 ≤ hz := by
      have : N / (16 * g) * a ^ 2 ≤ N / (8 * g) * a ^ 2 := by
        gcongr; linarith
      linarith
    calc c₁₄ / (γ * ε ^ 2) * d₁ ≤ N / (16 * g) * a ^ 2 * d₁ :=
          mul_le_mul_of_nonneg_right hmain hd₁
      _ ≤ hz * d₁ := mul_le_mul_of_nonneg_right this hd₁
      _ = d₁ * hz := mul_comm _ _
  · have e : a ^ 2 / (2 * b ^ 2) * d₁ * (N / (8 * g) * b ^ 2) = N / (16 * g) * a ^ 2 * d₁ := by
      field_simp; ring
    calc c₁₄ / (γ * ε ^ 2) * d₁ ≤ N / (16 * g) * a ^ 2 * d₁ :=
          mul_le_mul_of_nonneg_right hmain hd₁
      _ = a ^ 2 / (2 * b ^ 2) * d₁ * (N / (8 * g) * b ^ 2) := e.symm
      _ ≤ d₂ * hw := mul_le_mul hd₂ hwb (by positivity) (le_trans (by positivity) hd₂)

/-- The height of the family `F` mapped along `Γ(Spec k, ⊤) ≅ k` is at most the normalised
logarithmic height of the coefficients of `F`. -/
private theorem polynomialFamilyHeight_map_le {k : Type u} [Field k] [NumberField k] {ι σ : Type*}
    [Fintype ι] (F : ι → MvPolynomial σ Γ(Spec (.of k), ⊤))
    (hF : ∃ i, MvPolynomial.map (Scheme.ΓSpecIso (.of k)).hom.hom (F i) ≠ 0) :
    polynomialFamilyHeight (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).hom.hom (F i))
      hF ≤
    Height.logHeight (fun c : Σ i, (F i).support =>
      (Scheme.ΓSpecIso (.of k)).hom ((F c.1).coeff c.2)) / Module.finrank ℚ k := by
  classical
  set φ := (Scheme.ΓSpecIso (.of k)).hom.hom
  let f : ((i : ι) × (MvPolynomial.map φ (F i)).support) → ((i : ι) × (F i).support) :=
    fun α => ⟨α.1, α.2.1, MvPolynomial.support_map_subset φ (F α.1) α.2.2⟩
  have hy0 : (fun p : (i : ι) × (MvPolynomial.map φ (F i)).support =>
      (MvPolynomial.map φ (F p.1)).coeff p.2.1) ≠ 0 := by
    obtain ⟨i, hi⟩ := hF
    obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hi
    exact Function.ne_iff.mpr ⟨⟨i, I, MvPolynomial.mem_support_iff.mpr hI⟩, hI⟩
  have h1 := @weilHeight_eq_sumLocalHeight k _ _ _ _ _ (IsWellOrder.linearOrder WellOrderingRel)
    k _ _ _ _ (fun p : (i : ι) × (MvPolynomial.map φ (F i)).support =>
      (MvPolynomial.map φ (F p.1)).coeff p.2.1) hy0 rfl
  have h3 := BombieriVojta.HeightLowerBound.sumLocalHeight_eq_logHeight (K := k) hy0
  have hx : (fun p : (i : ι) × (MvPolynomial.map φ (F i)).support =>
      (MvPolynomial.map φ (F p.1)).coeff p.2.1) =
      (fun c : Σ i, (F i).support => (Scheme.ΓSpecIso (.of k)).hom ((F c.1).coeff c.2)) ∘ f := by
    funext α
    simp [f, φ, MvPolynomial.coeff_map]
  unfold polynomialFamilyHeight
  refine (h1.trans h3).trans_le ?_
  rw [hx]
  exact div_le_div_of_nonneg_right (Height.logHeight_comp_le f _) (Nat.cast_nonneg _)

/-- The image of a finitely generated algebra in an algebraic extension lies in a finite
extension. -/
private theorem exists_finiteDimensional_forall_mem {k A L : Type*} [Field k] [CommRing A]
    [Algebra k A] [hA : Algebra.FiniteType k A] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] (φ : A →ₐ[k] L) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧ ∀ a, φ a ∈ E := by
  obtain ⟨s, hs⟩ := hA.out
  refine ⟨IntermediateField.adjoin k (φ '' (s : Set A)), ?_, fun a => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · have ha : a ∈ Algebra.adjoin k (s : Set A) := by rw [hs]; trivial
    have : φ a ∈ (Algebra.adjoin k (s : Set A)).map φ := ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact IntermediateField.algebra_adjoin_le_adjoin k _ this

/-- A `L`-point of a scheme locally of finite type over `k`, for `L/k` algebraic, is defined
over a finite subextension `E` of `L/k`. -/
private theorem exists_isIntermediateField_comp_eq {k : Type u} [Field k] {S : Scheme.{u}}
    (f : S ⟶ Spec (.of k)) [LocallyOfFiniteType f] (L : Type u) [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] (p : Spec (.of L) ⟶ S)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ (E : IntermediateField k L) (_ : FiniteDimensional k E) (q : Spec (.of E) ⟶ S),
      Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫ q = p ∧
      q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.base (IsLocalRing.closedPoint L))) isOpen_univ
  have hrange : Set.range p.base ⊆ ((Scheme.Opens.ι (X := S) V).opensRange : Set S) := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    rwa [Subsingleton.elim y (IsLocalRing.closedPoint L)]
  set ι := Scheme.Opens.ι (X := S) V
  let p' := IsOpenImmersion.lift ι p hrange
  have hp' : p' ≫ ι = p := IsOpenImmersion.lift_fac _ _ _
  let A := Γ(S, V)
  let φ : A ⟶ CommRingCat.of L := Spec.preimage (p' ≫ hV.isoSpec.hom)
  have hφ : Spec.map φ = p' ≫ hV.isoSpec.hom := Spec.map_preimage _
  let ψ : CommRingCat.of k ⟶ A := Spec.preimage (hV.isoSpec.inv ≫ ι ≫ f)
  have hψ : Spec.map ψ = hV.isoSpec.inv ≫ ι ≫ f := Spec.map_preimage _
  have hψφ : ψ ≫ φ = CommRingCat.ofHom (algebraMap k L) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hp', hp]
  haveI : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft : ψ.hom.FiniteType := by
    rwa [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
  letI : Algebra k A := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType k A := hft
  let φa : A →ₐ[k] L :=
    { φ.hom with
      commutes' := fun c => by
        have := congrArg (fun h => h.hom c) hψφ
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        exact this }
  obtain ⟨E, hE, hmem⟩ := exists_finiteDimensional_forall_mem φa
  let φE : A →+* E := φa.toRingHom.codRestrict E.toSubring hmem
  refine ⟨E, hE, Spec.map (CommRingCat.ofHom φE) ≫ hV.isoSpec.inv ≫ ι, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom φE ≫ CommRingCat.ofHom (algebraMap E L) = φ := by
      ext a; rfl
    rw [this, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp']
  · rw [Category.assoc, Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext c
    have := congrArg (fun h => h.hom c) hψφ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    exact this

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- Transcendence of a rational function survives the base change of a curve to a finite
extension. -/
private theorem transcendental_functionFieldMap_of_isPullback {k E : Type u} [Field k] [Field E]
    [Algebra k E] [Algebra.IsAlgebraic k E] {C CK : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] [CK.Over (Spec (.of E))] [IsCurve E (CK ↘ Spec (.of E))]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    (π : CK ⟶ C) [IsDominant π]
    (hπ : π ≫ f = (CK ↘ Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (t : C.functionField) (ht : letI := functionFieldAlgebra k f; Transcendental k t) :
    letI := functionFieldAlgebra E (CK ↘ Spec (.of E))
    Transcendental E (π.functionFieldMap t) := by
  letI : Algebra E CK.functionField := functionFieldAlgebra E (CK ↘ Spec (.of E))
  letI : Algebra k C.functionField := functionFieldAlgebra k f
  haveI : IsCurve k ((CK ↘ Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    { topologicalKrullDim_eq_one :=
        (inferInstance : IsCurve E (CK ↘ Spec (.of E))).topologicalKrullDim_eq_one }
  letI : Algebra k CK.functionField :=
    functionFieldAlgebra k ((CK ↘ Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
  haveI : IsScalarTower k E CK.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    have h := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k E)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change (CK.germToFunctionField ⊤).hom
        (((CK ↘ Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom c)) =
      (CK.germToFunctionField ⊤).hom ((CK ↘ Spec (.of E)).appTop.hom
        ((Scheme.ΓSpecIso (.of E)).inv.hom (algebraMap k E c)))
    rw [h, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  let φk : C.functionField →ₐ[k] CK.functionField :=
    { π.functionFieldMap.hom with
      commutes' := fun c => functionFieldMap_algebraMap_of_isCurve k _ f π hπ c }
  intro halg
  have h1 : IsAlgebraic k (φk t) := halg.restrictScalars k
  exact ht ((isAlgebraic_algHom_iff φk φk.toRingHom.injective).1 h1)

/-- The ratio of two members of a basis is transcendental over `k`. -/
private theorem transcendental_div_of_linearIndependent {k : Type u} [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIntegral f] {n : ℕ}
    (x : Fin (n + 1) → C.functionField) (hn : 1 ≤ n)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x) :
    letI := functionFieldAlgebra k f
    Transcendental k (x (1 : Fin (n + 1)) / x 0) := by
  letI := functionFieldAlgebra k f
  refine FunctionField.transcendental_of_notMem_range f ?_
  rintro ⟨c, hc⟩
  have h01 : (0 : Fin (n + 1)) ≠ 1 := by
    rw [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one', Nat.one_mod_eq_one.2 (by omega)]
    exact zero_ne_one
  have hinj : Function.Injective (![0, 1] : Fin 2 → Fin (n + 1)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij.symm h01
    · rfl
  have hcomp : x ∘ (![0, 1] : Fin 2 → Fin (n + 1)) = ![x 0, x 1] := by
    ext i; fin_cases i <;> rfl
  have hli2 := hli.comp _ hinj
  rw [hcomp] at hli2
  have h0 : x 0 ≠ 0 := hli.ne_zero 0
  have h1 : x 1 = c • x 0 := by rw [Algebra.smul_def, hc, div_mul_cancel₀ _ h0]
  have := (LinearIndependent.pair_iff (R := k) (x := x 0) (y := x 1)).1 hli2 c (-1)
    (by rw [h1, neg_one_smul, add_neg_cancel])
  exact one_ne_zero (neg_eq_zero.1 this.2)

/-- The integer parameters `(d₁, d₂, d)` of `Faltings.bombieriParameters` for a large `D`, read as
natural numbers together with `δₗ = (dₗ + s d) / N`, and the bounds the angle inequality uses. -/
private theorem exists_nat_of_bombieriParameters {g : ℕ} (hg : 2 ≤ g) {sB : ℕ} (hsB : 1 ≤ sB)
    {N : ℕ} (hN : 2 * g + 1 ≤ N) {γ₀ a b D : ℝ} (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) (D₇ D₈ : ℕ)
    (hDp : ∀ d₁ d₂ d : ℤ, bombieriParameters g sB N γ₀ a b D = (d₁, d₂, d) →
      0 < d₁ ∧ 0 < d₂ ∧ 0 < d ∧
      (N : ℤ) ∣ d₁ + sB * d ∧ (N : ℤ) ∣ d₂ + sB * d ∧
      0 < (d₁ + sB * d) / N ∧ 0 < (d₂ + sB * d) / N ∧
      ((D₇ : ℝ) + D₈) ≤ d₁ ∧ ((D₇ : ℝ) + D₈) ≤ d₂ ∧ ((D₇ : ℝ) + D₈) ≤ d ∧
      ((D₇ : ℝ) + D₈) ≤ (((d₁ + sB * d) / N : ℤ) : ℝ) ∧
      ((D₇ : ℝ) + D₈) ≤ (((d₂ + sB * d) / N : ℤ) : ℝ) ∧
      d₂ ≤ d₁ ∧ (g : ℤ) * d ^ 2 < d₁ * d₂ ∧ d₁ * d₂ < (g : ℤ) ^ 2 * d ^ 2 ∧
      γ₀ / (2 * (g + γ₀)) * ((d₁ * d₂ : ℤ) : ℝ) < ((d₁ * d₂ - g * d ^ 2 : ℤ) : ℝ)) :
    ∃ d₁ d₂ d δ₁ δ₂ : ℕ, bombieriParameters g sB N γ₀ a b D = ((d₁ : ℤ), (d₂ : ℤ), (d : ℤ)) ∧
      N * δ₁ = d₁ + sB * d ∧ N * δ₂ = d₂ + sB * d ∧
      (0 : ℤ) < d₁ ∧ (0 : ℤ) < d₂ ∧ (0 : ℤ) < d ∧
      D₇ + D₈ ≤ d₁ ∧ D₇ + D₈ ≤ d₂ ∧ D₇ + D₈ ≤ d ∧
      (d₂ : ℤ) ≤ d₁ ∧ (g : ℤ) * (d : ℤ) ^ 2 < (d₁ : ℤ) * d₂ ∧
      (d₁ : ℤ) * d₂ < (g : ℤ) ^ 2 * (d : ℤ) ^ 2 ∧
      γ₀ / (2 * ((g : ℝ) + γ₀)) * ((d₁ : ℝ) * d₂) < (d₁ : ℝ) * d₂ - (g : ℝ) * (d : ℝ) ^ 2 ∧
      (0 ≤ (d : ℝ) - D / (a * b) ∧ (d : ℝ) - D / (a * b) < 1) ∧
      (0 ≤ (d₁ : ℝ) - √((g : ℝ) + γ₀) * D / a ^ 2 ∧
        (d₁ : ℝ) - √((g : ℝ) + γ₀) * D / a ^ 2 < N) ∧
      (0 ≤ √((g : ℝ) + γ₀) * D / b ^ 2 - (d₂ : ℝ) ∧
        √((g : ℝ) + γ₀) * D / b ^ 2 - (d₂ : ℝ) < N) := by
  obtain ⟨d₁', d₂', d', hq⟩ : ∃ d₁ d₂ d : ℤ,
      bombieriParameters g sB N γ₀ a b D = (d₁, d₂, d) := ⟨_, _, _, rfl⟩
  obtain ⟨h1, h2, h3, hdv1, hdv2, -, -, hD1, hD2, hD3, -, -, h21, hlo, hhi, hgap⟩ :=
    hDp d₁' d₂' d' hq
  have hbd := bombieriParameters_bounds g sB N γ₀ a b D hg
    (by exact_mod_cast hsB) hN hγ₀ hγ₀' ha hab hD
  simp only [hq] at hbd
  lift d₁' to ℕ using h1.le with d₁
  lift d₂' to ℕ using h2.le with d₂
  lift d' to ℕ using h3.le with d
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨c₁', hc₁'⟩ := hdv1
  obtain ⟨c₂', hc₂'⟩ := hdv2
  have hc₁0 : 0 ≤ c₁' := by
    by_contra hneg
    have : (N : ℤ) * c₁' < 0 := mul_neg_of_pos_of_neg hN0 (not_le.1 hneg)
    have : (0 : ℤ) ≤ d₁ + sB * d := by positivity
    linarith
  have hc₂0 : 0 ≤ c₂' := by
    by_contra hneg
    have : (N : ℤ) * c₂' < 0 := mul_neg_of_pos_of_neg hN0 (not_le.1 hneg)
    have : (0 : ℤ) ≤ d₂ + sB * d := by positivity
    linarith
  lift c₁' to ℕ using hc₁0 with δ₁
  lift c₂' to ℕ using hc₂0 with δ₂
  have hNδ₁ : N * δ₁ = d₁ + sB * d := by exact_mod_cast hc₁'.symm
  have hNδ₂ : N * δ₂ = d₂ + sB * d := by exact_mod_cast hc₂'.symm
  have hD1' : D₇ + D₈ ≤ d₁ := by
    have : ((D₇ + D₈ : ℕ) : ℝ) ≤ d₁ := by push_cast at hD1 ⊢; exact hD1
    exact_mod_cast this
  have hD2' : D₇ + D₈ ≤ d₂ := by
    have : ((D₇ + D₈ : ℕ) : ℝ) ≤ d₂ := by push_cast at hD2 ⊢; exact hD2
    exact_mod_cast this
  have hD3' : D₇ + D₈ ≤ d := by
    have : ((D₇ + D₈ : ℕ) : ℝ) ≤ d := by push_cast at hD3 ⊢; exact hD3
    exact_mod_cast this
  have hgapR : γ₀ / (2 * ((g : ℝ) + γ₀)) * ((d₁ : ℝ) * d₂) <
      (d₁ : ℝ) * d₂ - (g : ℝ) * (d : ℝ) ^ 2 := by
    push_cast at hgap
    exact hgap
  push_cast at hbd
  exact ⟨d₁, d₂, d, δ₁, δ₂, hq, hNδ₁, hNδ₂, h1, h2, h3, hD1', hD2', hD3', h21, hlo, hhi, hgapR,
    hbd.1, hbd.2.1, hbd.2.2⟩

/-- The main inequality with its constants replaced by their positive parts. -/
private theorem neg_le_of_neg_le_max {c₄ c₁₇ c₁ γ g a b P d₁ d₂ d i₁ i₂ : ℝ} (hγ : 0 < γ)
    (ha : 0 < a) (hb : 0 < b) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂)
    (h : -c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2) - c₁₇ * (d₁ + i₁ + i₂) - c₁₇ * d₁ / γ ≤
      d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 - d * P + c₁ * (d₁ * a + d₂ * b)) :
    -max c₄ 0 * (i₁ * a ^ 2 + i₂ * b ^ 2) - max c₁₇ 0 * (d₁ + i₁ + i₂) - max c₁₇ 0 * d₁ / γ ≤
      d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 - d * P + max c₁ 0 * (d₁ * a + d₂ * b) := by
  have hX : 0 ≤ i₁ * a ^ 2 + i₂ * b ^ 2 := by positivity
  have hY : 0 ≤ d₁ + i₁ + i₂ := by positivity
  have hY' : 0 ≤ d₁ / γ := by positivity
  have hZ : 0 ≤ d₁ * a + d₂ * b := by positivity
  have e1 : -max c₄ 0 * (i₁ * a ^ 2 + i₂ * b ^ 2) ≤ -c₄ * (i₁ * a ^ 2 + i₂ * b ^ 2) := by
    have := mul_le_mul_of_nonneg_right (le_max_left c₄ 0) hX
    linarith
  have e2 : c₁₇ * (d₁ + i₁ + i₂) ≤ max c₁₇ 0 * (d₁ + i₁ + i₂) :=
    mul_le_mul_of_nonneg_right (le_max_left c₁₇ 0) hY
  have e3 : c₁₇ * d₁ / γ ≤ max c₁₇ 0 * d₁ / γ := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left c₁₇ 0) hY'
  have e4 : c₁ * (d₁ * a + d₂ * b) ≤ max c₁ 0 * (d₁ * a + d₂ * b) :=
    mul_le_mul_of_nonneg_right (le_max_left c₁ 0) hZ
  linarith

open Classical in
/-- A representative `F₀` with coefficients in `Γ(Spec k, ⊤)` of a section `s`, of normalised
height at most `B ≥ 0`, read as a family of bihomogeneous polynomials over `k`: it still
represents `s`, and its height is at most `B`. -/
private theorem exists_family_of_isVojtaRepresentative {k : Type u} [Field k] [NumberField k]
    {X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (φ : X ⟶ projectiveSpaceOver m (Spec (.of k))) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F₀ : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤))
    (hF₀ : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F₀) {B : ℝ} (hB : 0 ≤ B)
    (hh : Height.logHeight (fun c : Σ i, (F₀ i).support =>
        (Scheme.ΓSpecIso (.of k)).hom ((F₀ c.1).coeff c.2)) / Module.finrank ℚ k ≤ B) :
    ∃ F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂),
      IsVojtaRepresentative ψ φ δ₁ δ₂ d s
        (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1) ∧
      (if hF : ∃ i, (F i).1 ≠ 0 then polynomialFamilyHeight (fun i => (F i).1) hF else 0) ≤ B := by
  let F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) := fun i =>
    ⟨MvPolynomial.map (Scheme.ΓSpecIso (.of k)).hom.hom (F₀ i),
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 fun c hc =>
        hF₀.1 i (by
          rw [MvPolynomial.coeff_map] at hc
          intro h0; exact hc (by rw [h0, map_zero]))⟩
  have hFF : (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1) = F₀ := by
    have e : (Scheme.ΓSpecIso (.of k)).inv.hom.comp (Scheme.ΓSpecIso (.of k)).hom.hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
    funext i
    simp only [F, MvPolynomial.map_map, e, MvPolynomial.map_id]
  refine ⟨F, by rw [hFF]; exact hF₀, ?_⟩
  split_ifs with hF
  · exact (polynomialFamilyHeight_map_le F₀ hF).trans hh
  · exact hB

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- If the generic point of `C` lies in the chart `φ_{NP}⁻¹ D₊(T₀)` and the generic point of
`C × C` in `φ_B⁻¹ D₊(T₀)`, then the chart `ψ⁻¹(pr₁⁻¹ D₊(T₀) ∩ pr₂⁻¹ D₊(T₀)) ∩ φ_B⁻¹ D₊(T₀)` of
`C × C` is nonempty. -/
private theorem chart_nonempty {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    [IsIntegral X.C] [IsIntegral (pullback X.f X.f)] {n m : ℕ}
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hηC : genericPoint X.C ∈
      (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0)
    (hηB : genericPoint ↥(pullback X.f X.f : Scheme.{u}) ∈ chartOne φB 0) :
    Nonempty (chartPair ψ 0 0 ⊓ chartOne φB 0 : (pullback X.f X.f).Opens) := by
  have hfst : (pullback.fst X.f X.f) (genericPoint ↥(pullback X.f X.f : Scheme.{u})) =
      genericPoint X.C :=
    map_genericPoint_of_isDominant _
  have hsnd : (pullback.snd X.f X.f) (genericPoint ↥(pullback X.f X.f : Scheme.{u})) =
      genericPoint X.C :=
    map_genericPoint_of_isDominant _
  refine ⟨⟨genericPoint _, ⟨?_, ?_⟩, hηB⟩⟩
  · change genericPoint _ ∈ (ψ ≫ pullback.fst _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0
    rw [reassoc_of% hψ₁]
    change (pullback.fst X.f X.f) (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ∈
      (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0
    rw [hfst]; exact hηC
  · change genericPoint _ ∈ (ψ ≫ pullback.snd _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0
    rw [reassoc_of% hψ₂]
    change (pullback.snd X.f X.f) (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ∈
      (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0
    rw [hsnd]; exact hηC

/-- **The base-changed section.** Let `C_E` be the base change of `C` to a field `E ⊇ k`, with
`ι_S : C_E ×_E C_E ⟶ C ×_k C` surjective, and let `ψ_E`, `φ_E` be base changes of `ψ`, `φ_B`
(their coordinates are the pull-backs of those of `ψ`, `φ_B`). If `s` is represented by `F` on
`C ×_k C`, some section `s_E` of `𝒪(V)` on `C_E ×_E C_E` is represented by `F` read over `E`. -/
private theorem exists_isVojtaRepresentative_of_baseChange {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) {E : Type u} [Field E] [Algebra k E]
    {n : ℕ} (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    {m : ℕ} (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (δ₁ δ₂ d : ℕ) (s : Γ(vojtaLineBundle (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
            Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hrep : IsVojtaRepresentative (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
            (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s
          (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1))
    [IsIntegral (pullback X.f X.f)]
    (hchart : Nonempty (chartPair (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) 0 0 ⊓
        chartOne φB 0 : (pullback X.f X.f).Opens))
    (CK : Scheme.{u}) [CK.Over (Spec (.of E))] (π : CK ⟶ X.C)
    (hπ : IsPullback π (CK ↘ Spec (.of E)) X.f (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    [IsIntegral (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)))]
    (ιS : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶ pullback X.f X.f) [Surjective ιS]
    (hιS : ιS ≫ pullback.fst X.f X.f = pullback.fst _ _ ≫ π)
    (ψK : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶
      pullback (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))
        (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)))
    (hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)) =
      pullback.fst _ _ ≫ (CK ↘ Spec (.of E)))
    (hψK₁ : ψK ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (hψK₂ : ψK ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (φK : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶ projectiveSpaceOver m (Spec (.of E)))
    (hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of E)) =
      ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) :
    ∃ sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤), IsVojtaRepresentative ψK φK δ₁ δ₂ d sK
      (fun i => MvPolynomial.map ((Scheme.ΓSpecIso (.of E)).inv.hom.comp (algebraMap k E))
        (F i).1) := by
  have hFK : ∀ i, (MvPolynomial.map ((Scheme.ΓSpecIso (.of E)).inv.hom.comp (algebraMap k E))
      (F i).1).IsWeightedHomogeneous
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂) :=
    fun i c hc => ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).1 (F i).2) (by
      rw [MvPolynomial.coeff_map] at hc
      intro h0; exact hc (by rw [h0, map_zero]))
  set ψ := pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
    (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP]) with hψdef
  set F' : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤) :=
    fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1
  have hF' : ∀ i, (F' i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂) := hrep.1
  haveI := hchart
  set A : Fin (m + 1) → (pullback X.f X.f).functionField := fun i =>
    (pullback X.f X.f).germToFunctionField (chartPair ψ 0 0 ⊓ chartOne φB 0) (resO inf_le_left
      ((F' i).eval₂ (coeffMap ψ (chartPair ψ 0 0)) (Sum.elim (xiFst ψ 0 0) (xiSnd ψ 0 0))))
  set η : Fin (m + 1) → (pullback X.f X.f).functionField := fun i =>
    (pullback X.f X.f).germToFunctionField (chartPair ψ 0 0 ⊓ chartOne φB 0)
      (resO inf_le_right (etaSec φB 0 i))
  have hAη := (exists_isVojtaRepresentative_iff_of_isIntegral ψ φB δ₁ δ₂ d F' hF' A η
    (fun _ => rfl) (fun _ => rfl)).1 ⟨_, hrep⟩
  haveI : IsDominant ιS := inferInstance
  set FK : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of E), ⊤) :=
    fun i => MvPolynomial.map ((Scheme.ΓSpecIso (.of E)).inv.hom.comp (algebraMap k E)) (F i).1
  have hψ1 : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP := pullback.lift_snd _ _ _
  have E₁ : ψK ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) :=
    hψK₁.trans (by rw [reassoc_of% hψ1])
  have E₂ : ψK ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) :=
    hψK₂.trans (by rw [reassoc_of% hψ2])
  have hU : chartPair ψK 0 0 ⊓ chartOne φK 0 = ιS ⁻¹ᵁ (chartPair ψ 0 0 ⊓ chartOne φB 0) := by
    change (ψK ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) ⁻¹ᵁ
        projChart n 0 ⊓
      (ψK ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) ⁻¹ᵁ
        projChart n 0 ⊓
      (φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of E))) ⁻¹ᵁ projChart m 0 =
      (ιS ≫ ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        projChart n 0 ⊓
      (ιS ≫ ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        projChart n 0 ⊓
      (ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ projChart m 0
    rw [E₁, E₂, hφK]
  haveI hchartK : Nonempty (chartPair ψK 0 0 ⊓ chartOne φK 0 :
      (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).Opens) := by
    obtain ⟨⟨y, hy⟩⟩ := hchart
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective ιS).surj y
    exact ⟨⟨x, by rw [hU]; exact hy⟩⟩
  set AK : Fin (m + 1) → (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).functionField :=
    fun i => (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
      (chartPair ψK 0 0 ⊓ chartOne φK 0) (resO inf_le_left
        ((FK i).eval₂ (coeffMap ψK (chartPair ψK 0 0)) (Sum.elim (xiFst ψK 0 0) (xiSnd ψK 0 0))))
  set ηK : Fin (m + 1) → (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).functionField :=
    fun i => (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
      (chartPair ψK 0 0 ⊓ chartOne φK 0) (resO inf_le_right (etaSec φK 0 i))
  obtain ⟨⟨xK, hxK⟩⟩ := id hchartK
  obtain ⟨⟨x₀, hx₀⟩⟩ := id hchart
  haveI : Nonempty (chartOne φK 0) := ⟨⟨xK, hxK.2⟩⟩
  haveI : Nonempty (chartOne φB 0) := ⟨⟨x₀, hx₀.2⟩⟩
  haveI : Nonempty (chartPair ψK 0 0) := ⟨⟨xK, hxK.1⟩⟩
  haveI : Nonempty (chartPair ψ 0 0) := ⟨⟨x₀, hx₀.1⟩⟩
  have hηK : ∀ i, ηK i = functionFieldMap ιS (η i) := by
    intro i
    change (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
        (chartPair ψK 0 0 ⊓ chartOne φK 0 :
          (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).Opens)
        (resO inf_le_right (etaSec φK 0 i)) =
      functionFieldMap ιS ((pullback X.f X.f).germToFunctionField
        (chartPair ψ 0 0 ⊓ chartOne φB 0 : (pullback X.f X.f).Opens)
        (resO inf_le_right (etaSec φB 0 i)))
    rw [Faltings.germToFunctionField_resO, Faltings.germToFunctionField_resO]
    haveI : Nonempty ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        projChart m 0) := ⟨⟨x₀, hx₀.2⟩⟩
    haveI : Nonempty (φK ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of E)) ⁻¹ᵁ
        projChart m 0)) := ⟨⟨xK, hxK.2⟩⟩
    exact Faltings.germToFunctionField_app_app ιS
      (φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) φK
      (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of E))) hφK
      (O := projChart m 0) (Faltings.projRatio.{u} m 0 i)
  have hxi : ∀ v, (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
      (chartPair ψK 0 0) (Sum.elim (xiFst ψK 0 0) (xiSnd ψK 0 0) v) =
      functionFieldMap ιS ((pullback X.f X.f).germToFunctionField (chartPair ψ 0 0)
        (Sum.elim (xiFst ψ 0 0) (xiSnd ψ 0 0) v)) := by
    rintro (ν | ν)
    · change (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField _
          (ψK.app _ (resO inf_le_left _)) =
        functionFieldMap ιS ((pullback X.f X.f).germToFunctionField _
          (ψ.app _ (resO inf_le_left _)))
      haveI : Nonempty (ψ ⁻¹ᵁ (pullback.fst
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ projChart n 0))) :=
        ⟨⟨x₀, hx₀.1.1⟩⟩
      haveI : Nonempty (ψK ⁻¹ᵁ (pullback.fst
          (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))
          (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) ⁻¹ᵁ projChart n 0))) :=
        ⟨⟨xK, hxK.1.1⟩⟩
      rw [Faltings.app_resO, Faltings.app_resO, Faltings.germToFunctionField_resO,
        Faltings.germToFunctionField_resO]
      haveI : Nonempty ((ψ ≫ pullback.fst _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0) :=
        ⟨⟨x₀, hx₀.1.1⟩⟩
      haveI : Nonempty (ψK ⁻¹ᵁ ((pullback.fst _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) ⁻¹ᵁ projChart n 0)) :=
        ⟨⟨xK, hxK.1.1⟩⟩
      exact Faltings.germToFunctionField_app_app ιS
        (ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ψK
        (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) E₁
        (O := projChart n 0) (Faltings.projRatio.{u} n 0 ν)
    · change (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField _
          (ψK.app _ (resO inf_le_right _)) =
        functionFieldMap ιS ((pullback X.f X.f).germToFunctionField _
          (ψ.app _ (resO inf_le_right _)))
      haveI : Nonempty (ψ ⁻¹ᵁ (pullback.snd
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ projChart n 0))) :=
        ⟨⟨x₀, hx₀.1.2⟩⟩
      haveI : Nonempty (ψK ⁻¹ᵁ (pullback.snd
          (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))
          (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) ⁻¹ᵁ projChart n 0))) :=
        ⟨⟨xK, hxK.1.2⟩⟩
      rw [Faltings.app_resO, Faltings.app_resO, Faltings.germToFunctionField_resO,
        Faltings.germToFunctionField_resO]
      haveI : Nonempty ((ψ ≫ pullback.snd _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ projChart n 0) :=
        ⟨⟨x₀, hx₀.1.2⟩⟩
      haveI : Nonempty (ψK ⁻¹ᵁ ((pullback.snd _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) ⁻¹ᵁ projChart n 0)) :=
        ⟨⟨xK, hxK.1.2⟩⟩
      exact Faltings.germToFunctionField_app_app ιS
        (ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ψK
        (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E))) E₂
        (O := projChart n 0) (Faltings.projRatio.{u} n 0 ν)
  have e₀ : (ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      ιS ≫ ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hψKπ, reassoc_of% hψ1, hφNP, Category.assoc, ← hπ.w]
    change _ = (ιS ≫ pullback.fst X.f X.f) ≫ X.f
    rw [hιS]
    simp only [Category.assoc]
  have hcoef : ∀ c : k,
      (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField (chartPair ψK 0 0)
        (coeffMap ψK (chartPair ψK 0 0)
          (((Scheme.ΓSpecIso (.of E)).inv.hom.comp (algebraMap k E)) c)) =
      functionFieldMap ιS ((pullback X.f X.f).germToFunctionField (chartPair ψ 0 0)
        (coeffMap ψ (chartPair ψ 0 0) ((Scheme.ΓSpecIso (.of k)).inv.hom c))) := by
    intro c
    have hnat := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k E)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
    change (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField _
        (resO le_top ((ψK ≫ pullback.fst _ _ ≫
          (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))).appTop
          ((Scheme.ΓSpecIso (.of E)).inv.hom (algebraMap k E c)))) =
      functionFieldMap ιS ((pullback X.f X.f).germToFunctionField _
        (resO le_top ((ψ ≫ pullback.fst _ _ ≫
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv.hom c))))
    haveI : Nonempty (⊤ : (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).Opens) :=
      ⟨⟨xK, trivial⟩⟩
    haveI : Nonempty (⊤ : (pullback X.f X.f).Opens) := ⟨⟨x₀, trivial⟩⟩
    haveI : Nonempty ((ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) ⁻¹ᵁ ⊤) := ⟨⟨x₀, trivial⟩⟩
    haveI : Nonempty ((ψK ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))) ⁻¹ᵁ
          (Spec.map (CommRingCat.ofHom (algebraMap k E)) ⁻¹ᵁ ⊤)) := ⟨⟨xK, trivial⟩⟩
    rw [Faltings.germToFunctionField_resO, Faltings.germToFunctionField_resO, hnat]
    exact Faltings.germToFunctionField_app_app ιS
      (ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
      (ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)))
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) e₀ (O := ⊤)
      ((Scheme.ΓSpecIso (.of k)).inv.hom c)
  have hAK : ∀ i, AK i = functionFieldMap ιS (A i) := by
    intro i
    change (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
        (chartPair ψK 0 0 ⊓ chartOne φK 0 :
          (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).Opens) (resO inf_le_left
          ((FK i).eval₂ (coeffMap ψK (chartPair ψK 0 0))
            (Sum.elim (xiFst ψK 0 0) (xiSnd ψK 0 0)))) =
      functionFieldMap ιS ((pullback X.f X.f).germToFunctionField
        (chartPair ψ 0 0 ⊓ chartOne φB 0 : (pullback X.f X.f).Opens) (resO inf_le_left
          ((F' i).eval₂ (coeffMap ψ (chartPair ψ 0 0)) (Sum.elim (xiFst ψ 0 0) (xiSnd ψ 0 0)))))
    rw [Faltings.germToFunctionField_resO, Faltings.germToFunctionField_resO]
    change ((pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))).germToFunctionField
        (chartPair ψK 0 0)).hom _ = functionFieldMap ιS
          (((pullback X.f X.f).germToFunctionField (chartPair ψ 0 0)).hom _)
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left,
      MvPolynomial.eval₂_map, MvPolynomial.eval₂_map]
    congr 1
    · ext c; exact hcoef c
    · funext v; exact hxi v
  obtain ⟨sK, hsK⟩ := (exists_isVojtaRepresentative_iff_of_isIntegral ψK φK δ₁ δ₂ d FK hFK AK ηK
    (fun _ => rfl) (fun _ => rfl)).2 fun i j => by
      have h := congrArg (functionFieldMap ιS) (hAη i j)
      rw [map_mul, map_mul, map_pow, map_pow] at h
      rw [hAK, hAK, hηK, hηK]
      exact h
  exact ⟨sK, hsK⟩

/-- **The base-change block.** For a `k̄`-point `p` of `C ×_k C` and a section `s` of
`𝒪(V)` represented by `F`, there are a number field `E ⊆ k̄` over which `p` is defined, the base
change `C_E` of `C`, the base changes `ψ_E`, `φ_E` of `ψ`, `φ_B`, a section `s_E` represented by
`F`, and the `E`-point `p_E` of `C_E ×_E C_E` through which `p` factors. -/
private theorem block_exists {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (N : ℕ) {n : ℕ} (x : Fin (n + 1) → X.C.functionField)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    {m : ℕ} (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (δ₁ δ₂ d : ℕ) (s : Γ(vojtaLineBundle (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
            Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hrep : IsVojtaRepresentative (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
            (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s
          (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1))
    [IsIntegral (pullback X.f X.f)]
    (hchart : Nonempty (chartPair (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) 0 0 ⊓
        chartOne φB 0 : (pullback X.f X.f).Opens))
    (ht : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      letI := functionFieldAlgebra k X.f
      Transcendental k (x 1 / x 0))
    (p : Spec (.of kbar) ⟶ pullback X.f X.f)
    (hp : p ≫ pullback.fst X.f X.f ≫ X.f = Spec.map (CommRingCat.ofHom (algebraMap k kbar)))
    (R : Prop) (hR :
      -- a number field `K ⊆ k̄` over which `p` is defined, and the base change `C_K`
      ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
        (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
        (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
        pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          hπ.w.symm hπ.w.symm
      ∀ (_hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
          Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        -- the base changes `ψ_K, φ_K` of `ψ, φ_B`, and the section `s_K` represented by `F`
        (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
          pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
            (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
        (_hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
          pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
        (_hψK₁ : ψK ≫ pullback.fst _ _ ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (_hψK₂ : ψK ≫ pullback.snd _ _ ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
          projectiveSpaceOver m (Spec (.of K)))
        (_hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) =
          pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
        (_hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
          ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
        (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
        (_hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
          ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
        -- the `K`-point `p_K` through which `p` factors
        (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
        [pK.IsOver (Spec (.of K))]
        (_hpK : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ pK ≫ ιS = p),
        R) : R := by
  haveI : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  obtain ⟨E, hE, q, hqp, hqk⟩ :=
    exists_isIntermediateField_comp_eq (pullback.fst X.f X.f ≫ X.f) kbar p hp
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  haveI : FiniteDimensional ℚ E := Module.Finite.trans k E
  haveI : NumberField E := ⟨⟩
  let CK := pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  letI : CK.Over (Spec (.of E)) := ⟨pullback.snd _ _⟩
  have hπ : IsPullback (pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (CK ↘ Spec (.of E)) X.f (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    IsPullback.of_hasPullback X.f _
  haveI : SmoothOfRelativeDimension 1 (CK ↘ Spec (.of E)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hπ inferInstance
  haveI : Smooth (CK ↘ Spec (.of E)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : IsProper (CK ↘ Spec (.of E)) :=
    MorphismProperty.of_isPullback (P := @IsProper) hπ inferInstance
  haveI : GeometricallyIrreducible (CK ↘ Spec (.of E)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hπ inferInstance
  haveI : IsCurve E (CK ↘ Spec (.of E)) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one (CK ↘ Spec (.of E))
  haveI : IsLocallyNoetherian CK := LocallyOfFiniteType.isLocallyNoetherian (CK ↘ Spec (.of E))
  haveI : IsIntegral CK := inferInstance
  haveI : IsDominant (pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
    inferInstance
  set π := pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k E)))
  let ιS : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶ pullback X.f X.f :=
    pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      hπ.w.symm hπ.w.symm
  have hq₁ : (q ≫ pullback.fst X.f X.f) ≫ X.f =
      𝟙 (Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    rw [Category.assoc, hqk, Category.id_comp]
  have hq₂ : (q ≫ pullback.snd X.f X.f) ≫ X.f =
      𝟙 (Spec (.of E)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
    rw [Category.assoc, ← pullback.condition, hqk, Category.id_comp]
  let zK : Spec (.of E) ⟶ CK := pullback.lift _ _ hq₁
  let wK : Spec (.of E) ⟶ CK := pullback.lift _ _ hq₂
  have hzw : zK ≫ (CK ↘ Spec (.of E)) = wK ≫ (CK ↘ Spec (.of E)) := by
    change zK ≫ pullback.snd _ _ = wK ≫ pullback.snd _ _
    rw [pullback.lift_snd, pullback.lift_snd]
  let pK : Spec (.of E) ⟶ pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) :=
    pullback.lift zK wK hzw
  let a₁ : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶
      projectiveSpaceOver n (Spec (.of E)) :=
    pullback.lift (pullback.fst _ _ ≫ (CK ↘ Spec (.of E)))
      (ιS ≫ pullback.fst X.f X.f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (terminal.hom_ext _ _)
  let a₂ : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶
      projectiveSpaceOver n (Spec (.of E)) :=
    pullback.lift (pullback.fst _ _ ≫ (CK ↘ Spec (.of E)))
      (ιS ≫ pullback.snd X.f X.f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (terminal.hom_ext _ _)
  let ψK : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶
      pullback (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E))
        (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)) :=
    pullback.lift a₁ a₂ (by
      change a₁ ≫ pullback.fst _ _ = a₂ ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst])
  let φK : pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E)) ⟶
      projectiveSpaceOver m (Spec (.of E)) :=
    pullback.lift (pullback.fst _ _ ≫ (CK ↘ Spec (.of E)))
      (ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
      (terminal.hom_ext _ _)
  have hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of E)) ↘ Spec (.of E)) =
      pullback.fst _ _ ≫ (CK ↘ Spec (.of E)) := by
    change ψK ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hψK₁ : ψK ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) := by
    change ψK ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hψK₂ : ψK ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of E)) =
      ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) := by
    change ψK ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd_assoc, pullback.lift_snd]
  have hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of E)) ↘ Spec (.of E)) =
      pullback.fst _ _ ≫ (CK ↘ Spec (.of E)) := pullback.lift_fst _ _ _
  have hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of E)) =
      ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) := pullback.lift_snd _ _ _
  have hpKι : pK ≫ ιS = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ιS, pullback.lift_fst, pullback.lift_fst_assoc, pK, zK]
      exact pullback.lift_fst _ _ _
    · simp only [Category.assoc, ιS, pullback.lift_snd, pullback.lift_snd_assoc, pK, wK]
      exact pullback.lift_fst _ _ _
  have hpK : Spec.map (CommRingCat.ofHom (E.val : E →+* kbar)) ≫ pK ≫ ιS = p := by
    rw [hpKι]; exact hqp
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hE)
  haveI : IsFinite π := MorphismProperty.of_isPullback (P := @IsFinite) hπ.flip inferInstance
  let P' : X.C →₀ ℤ := X.P.mapDomain Subtype.val
  have hfin : (π.base ⁻¹' (P'.support : Set X.C)).Finite :=
    π.finite_preimage P'.support.finite_toSet
  let DK : CK →₀ ℤ := Finsupp.ofSupportFinite (fun Q => (N : ℤ) * P' (π.base Q))
    (hfin.subset fun Q hQ => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hQ
      exact Finsupp.mem_support_iff.2 hQ.2)
  have hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q) := fun Q => rfl
  haveI : pK.IsOver (Spec (.of E)) := ⟨by
    have h1 : pK ≫ pullback.snd _ _ ≫ (CK ↘ Spec (.of E)) = 𝟙 _ := by
      change pK ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd_assoc, pullback.lift_snd]
    have h2 : Spec (.of E) ↘ Spec (.of E) = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom (algebraMap E E)) = _
      rw [Algebra.algebraMap_self]; exact Spec.map_id _
    rw [h2, ← h1]
    rfl⟩
  have hξ : letI := functionFieldAlgebra E (CK ↘ Spec (.of E))
      Transcendental E (π.functionFieldMap (x 1) / π.functionFieldMap (x 0)) := by
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.of_finite k E
    have := transcendental_functionFieldMap_of_isPullback X.f π hπ.w (x 1 / x 0) ht
    rwa [map_div₀] at this
  haveI : GeometricallyIntegral (CK ↘ Spec (.of E)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hπ inferInstance
  haveI : IsIntegral (pullback (CK ↘ Spec (.of E)) (CK ↘ Spec (.of E))) := inferInstance
  have hS : IsPullback ιS (pullback.snd _ _ ≫ (CK ↘ Spec (.of E)))
      (pullback.fst X.f X.f ≫ X.f) (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
    have h := isPullback_map hπ
    rwa [pullback.condition (f := CK ↘ Spec (.of E)) (g := CK ↘ Spec (.of E))] at h
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k E))) := inferInstance
  haveI : Surjective ιS := MorphismProperty.of_isPullback (P := @Surjective) hS.flip inferInstance
  obtain ⟨sK, hsK⟩ := exists_isVojtaRepresentative_of_baseChange X φNP hφNP φB δ₁ δ₂ d s F hrep
    hchart CK π hπ ιS (pullback.lift_fst _ _ _) ψK hψKπ hψK₁ hψK₂ φK hφK
  exact hR E E.val CK π hπ hξ DK hDK ψK hψKπ hψK₁ hψK₂ φK hφKπ hφK sK hsK pK hpK

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- Bombieri's Lemma 8 at `(z, w)`, with the parameters `(d₁, d₂, d)` of `(γ₀, z, w, D)` and
its height hypothesis from the errata form of `h_{NP}`: for `|z| ≥ c₂₀ / ε` large there is,
for all large `D`, a pair `i` admissible for the small section at `(z, w)` with
`iₗ ≤ 4 N ε dₗ`. -/
private theorem exists_pos_forall_eventually_isAdmissiblePair {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0)
    (c₁₀' γ₀ : ℝ) (hγ₀ : 0 < γ₀) (hγ₀' : γ₀ ≤ 1 / 10) :
    let g : ℝ := genus X.f
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    let γ : ℝ := γ₀ / (2 * (g + γ₀))
    ∃ c₂₀ : ℝ, 0 < c₂₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f,
    c₂₀ / ε ≤ √(pair z z) → √(pair z z) ≤ √(pair w w) → √(pair z z) / √(pair w w) ≤ ε →
    (∀ (p : Spec (.of kbar) ⟶ pullback X.f X.f),
      z.left = p ≫ pullback.fst X.f X.f → w.left = p ≫ pullback.snd X.f X.f →
      ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
        (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
        (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK]
        [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
        pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          hπ.w.symm hπ.w.symm
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
          Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
        [pK.IsOver (Spec (.of K))]
        (_hpK : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ pK ≫ ιS = p),
        pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ ∧
        pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀) →
    ∀ (p : Spec (.of kbar) ⟶ pullback X.f X.f),
      z.left = p ≫ pullback.fst X.f X.f → w.left = p ≫ pullback.snd X.f X.f →
    ∀ᶠ D in atTop, ∀ d₁ d₂ d δ₁ δ₂ : ℕ,
      bombieriParameters (genus X.f) sB N γ₀ √(pair z z) √(pair w w) D =
        ((d₁ : ℤ), (d₂ : ℤ), (d : ℤ)) →
      N * δ₁ = d₁ + sB * d → N * δ₂ = d₂ + sB * d →
    ∀ s : Γ(vojtaLineBundle (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
        (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤),
      s ≠ 0 →
    ∀ F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂),
      IsVojtaRepresentative (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s
        (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1) →
      (if hF : ∃ i, (F i).1 ≠ 0 then polynomialFamilyHeight (fun i => (F i).1) hF else 0) ≤
        c₁₀' * (d₁ + d₂) / γ + 0 →
      -- a number field `K ⊆ k̄` over which `p` is defined, and the base change `C_K`
      ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
        (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
        (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
        pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          hπ.w.symm hπ.w.symm
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
          Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        -- the base changes `ψ_K, φ_K` of `ψ, φ_B`, and the section `s_K` represented by `F`
        (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
          pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
            (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
        (_hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
          pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
        (_hψK₁ : ψK ≫ pullback.fst _ _ ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (_hψK₂ : ψK ≫ pullback.snd _ _ ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
          projectiveSpaceOver m (Spec (.of K)))
        (_hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) =
          pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
        (_hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
          ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
        (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
        (_hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
          ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
        -- the `K`-point `p_K` through which `p` factors
        (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
        [pK.IsOver (Spec (.of K))]
        (_hpK : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ pK ≫ ιS = p),
        -- `z, w ∉ Z`, and `i` admissible for `s` at `(z, w)`
        pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
        pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
        ∃ i : ℕ × ℕ, (i.1 : ℝ) ≤ 4 * N * ε * d₁ ∧ (i.2 : ℝ) ≤ 4 * N * ε * d₂ ∧
          IsAdmissiblePair (vojtaLineBundle ψK φK δ₁ δ₂ d) sK pK i := by
  intro g pair γ
  obtain rfl : ψ = pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
      (by rw [Category.comp_id, hφNP]) := by
    apply pullback.hom_ext
    · rw [hψ₁, pullback.lift_fst]
    · rw [hψ₂, pullback.lift_snd]
  have hg1 : (1 : ℝ) ≤ g := by
    have : (2 : ℝ) ≤ g := show (2 : ℝ) ≤ (genus X.f : ℝ) by exact_mod_cast hg
    linarith
  have hNr : (0 : ℝ) ≤ N := N.cast_nonneg
  have hγ : 0 < γ := by positivity
  obtain ⟨c₁₄, -, hLem8⟩ := exists_isAdmissiblePair_div_add_div_le X hg kbar N hN hn x hx
    hxbpf Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx _ hψ₁ hψ₂ hkC hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ DB hDB y hy
    hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3 c₁₀'
  obtain ⟨cNP, hNP⟩ := exists_abs_weilHeight_sub_neronPairing_le X A hg j hj D hrad hsupp N hN
    φNP hφNP hφNPL kbar
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨c₂₀, hc₂₀, hmin⟩ := exists_div_mul_le_min_mul (g := g) (c := max cNP 0) (c₁₄ := c₁₄)
    hg1 hN0 (le_max_right _ _) hγ
  refine ⟨c₂₀, hc₂₀, fun ε hε hε1 z w hz hab hzwε _ p hzp hwp => ?_⟩
  set a := √(pair z z) with ha_def
  set b := √(pair w w) with hb_def
  have ha : 0 < a := (div_pos hc₂₀ hε).trans_le hz
  have hb : 0 < b := ha.trans_le hab
  have hl : 0 < √(g + γ₀) := Real.sqrt_pos.2 (by linarith)
  obtain ⟨D₀, hD₀⟩ := hLem8 γ hγ (fun _ => 0) (Asymptotics.isLittleO_zero _ _)
  filter_upwards [eventually_bombieriParameters (g := genus X.f) hg (s := (sB : ℤ))
      (by exact_mod_cast hsB) hN hγ₀ hγ₀' ha hab (D₀ : ℝ),
    eventually_div_mul_le_of_bounds hl ha hb hNr, eventually_gt_atTop 0]
    with Dp hDp hratio hDpos
  intro d₁ d₂ d δ₁ δ₂ hq hNδ₁ hNδ₂ s hs F hrep hheight K _ _ _ ι CK _ π hπ _ _ _ _ xK ιS hξ DK
    hDK ψK h1 h2 h3 φK h4 h5 sK h6 pK _ hpK hz' hw'
  obtain ⟨hd₁0, hd₂0, -, -, -, -, -, hD1, hD2, hD3, -, -, -, hlo, hhi, hgap⟩ := hDp _ _ _ hq
  have hbd := bombieriParameters_bounds (genus X.f) sB N γ₀ a b Dp hg (by exact_mod_cast hsB) hN
    hγ₀ hγ₀' ha hab hDpos
  have hrat := bombieriParameters_div_le (g := genus X.f) (s := (sB : ℤ)) (N := N)
    (by exact_mod_cast hsB) hN hγ₀ hγ₀' ha hab hDpos
  simp only [hq] at hbd hrat
  push_cast at hbd hrat hD1 hD2 hD3 hgap
  have hd₁pos : (0 : ℝ) < d₁ := by exact_mod_cast hd₁0
  have hε2 : (d₂ : ℝ) / d₁ ≤ ε ^ 2 := by
    refine hrat.trans ?_
    rw [← div_pow]
    have h0 : 0 ≤ a / b := by positivity
    exact pow_le_pow_left₀ h0 hzwε 2
  haveI : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  letI : Algebra ℚ kbar := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
  have hheightZ : ∀ (c : Fin (n + 1) → kbar) (hc : c ≠ 0)
      (v : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f), _ →
      N / (2 * g) * √(pair v v) ^ 2 - max cNP 0 * (1 + √(pair v v)) ≤
        weilHeight (Projectivization.mk kbar c hc) := fun c hc v hv => by
    have := hNP v c hc hv
    have e : cNP * (1 + √(pair v v)) ≤ max cNP 0 * (1 + √(pair v v)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [abs_le] at this
    change N / (2 * g) * √(pair v v) ^ 2 - _ ≤ _
    linarith [this.1]
  obtain ⟨i, hi, hile⟩ := hD₀ d₁ d₂ d δ₁ δ₂ (by exact_mod_cast hD1) (by exact_mod_cast hD2)
    (by exact_mod_cast hD3) hgap (by exact_mod_cast hlo) (by exact_mod_cast hhi) hNδ₁ hNδ₂
    s hs F hrep hheight p ε hε hε1 hε2 (fun c c' hc hc' hcz hcw =>
      hmin ε hε hε1 a b _ _ d₁ d₂ hz hab
        (hheightZ c hc z (by rw [hzp]; simpa only [Category.assoc] using hcz))
        (hheightZ c' hc' w (by rw [hwp]; simpa only [Category.assoc] using hcw))
        d₁.cast_nonneg
        (hratio d₁ d₂ d₁.cast_nonneg (by linarith [hbd.2.1.2]) (by linarith [hbd.2.2.2])))
    K ι CK π hπ hξ DK hDK ψK h1 h2 h3 φK h4 h5 sK h6 pK hpK hz' hw'
  have hi2 : (0 : ℝ) ≤ (i.2 : ℝ) / d₂ := by positivity
  have hi1 : (i.1 : ℝ) / d₁ ≤ 4 * N * ε := by linarith
  have hd₂pos : (0 : ℝ) < d₂ := by exact_mod_cast hd₂0
  have hi1' : (0 : ℝ) ≤ (i.1 : ℝ) / d₁ := by positivity
  exact ⟨i, (div_le_iff₀ hd₁pos).1 hi1, (div_le_iff₀ hd₂pos).1 (by linarith), hi⟩

end

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **The angle inequality** (Bombieri). Let `X = (C, P)` be a curve of genus `g ≥ 2` over a
number field `k` with a divisor `P` of degree one, `⟨ , ⟩ = Faltings.neronPairing` its Néron
form on `J(k̄)`, `⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`, with the standing data of
Bombieri's Sections 9–10 over `k`: a generic basis `x` of `L(N P)` giving `φNP`,
`ψ = φNP × φNP`, and a basis `y` of `H⁰(C × C, 𝒪(B))` generic for the projections giving `φB`.
There are `c₄, c₁₈, c₁₉` such that for every `0 < γ₀ ≤ 1 / 10` there is `c₂₀` with
`⟨z, w⟩ / (|z| |w|) ≤ √(g + γ₀) / g + c₄ √(g + γ₀) (8 N ε) +`
`c₁₉ (1 / |z| + 1 / |w|) + c₁₈ / (γ₀ |z|²)`
whenever `0 < ε < 1`, `c₂₀ / ε ≤ |z|`, `|z| / |w| ≤ ε` and `z, w` lie outside
`Faltings.BombieriSiegel.exceptionalSet` over every number field `K ⊆ k̄` over which `(z, w)` is
defined. -/
@[faltings "lem_bvr_angle_inequality"]
public theorem exists_neronPairing_div_le {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0)
    :
    let g : ℝ := genus X.f
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ c₄ c₁₈ c₁₉ : ℝ, ∀ γ₀ : ℝ, 0 < γ₀ → γ₀ ≤ 1 / 10 → ∃ c₂₀ : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f,
      c₂₀ / ε ≤ √(pair z z) → √(pair z z) / √(pair w w) ≤ ε →
      -- `z, w ∉ Z`, read over every number field `K ⊆ k̄` over which `(z, w)` is defined
      (∀ (p : Spec (.of kbar) ⟶ pullback X.f X.f),
        z.left = p ≫ pullback.fst X.f X.f → w.left = p ≫ pullback.snd X.f X.f →
        ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
          (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
          (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK]
          [IsDominant π],
        let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
        let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
          pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            hπ.w.symm hπ.w.symm
        ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
            Transcendental K (xK 1 / xK 0))
          (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
          (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
          [pK.IsOver (Spec (.of K))]
          (_hpK : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ pK ≫ ιS = p),
          pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ ∧
          pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀) →
      pair z w / (√(pair z z) * √(pair w w)) ≤
        √(g + γ₀) / g + c₄ * √(g + γ₀) * (8 * N * ε) +
          c₁₉ * (1 / √(pair z z) + 1 / √(pair w w)) + c₁₈ / (γ₀ * √(pair z z) ^ 2) := by
  open Filter BombieriRoth in
  intro g pair
  obtain rfl : ψ = pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
      (by rw [Category.comp_id, hφNP]) := by
    apply pullback.hom_ext
    · rw [hψ₁, pullback.lift_fst]
    · rw [hψ₂, pullback.lift_snd]
  obtain ⟨c₁₀, hL7⟩ := exists_ne_zero_isVojtaRepresentative_logHeight_le X hg sB hsB N hN hn x hx
    φNP hφNP (fun ν j => by
      haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      letI := functionFieldAlgebra k X.f
      have hx0 : ∀ i, x i ≠ 0 := hx.linearIndependent.ne_zero
      have hη := (exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx j).fst
      exact ⟨hη, @hφNPx j ν ⟨⟨_, hη⟩⟩⟩) φB hφB hφBB
    ⟨_, (exists_germ_app_ratio_eq_div φB y (hy 0) _ _ hφBy).fst⟩
  let c₁₀' : ℝ := max c₁₀ 0 + 1
  have hc₁₀' : c₁₀' = max c₁₀ 0 + 1 := rfl
  obtain ⟨c₁, c₄, c₁₇, hMI⟩ := exists_neg_le_neronPairing_of_isAdmissiblePair X A hg j hj D hrad
    hsupp kbar N hN hn x hx hxbpf Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx _ hψ₁ hψ₂ hkC hkX ι₁ ι₂ hι₁ hι₂
    sB hsB heΔ DB hDB y hy hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3 c₁₀'
  have hg1 : (1 : ℝ) ≤ g := by
    have : (2 : ℝ) ≤ g := show (2 : ℝ) ≤ (genus X.f : ℝ) by exact_mod_cast hg
    linarith
  have hNr : (0 : ℝ) ≤ N := N.cast_nonneg
  refine ⟨max c₄ 0, max c₁₇ 0 * √(g + 1) * (8 * N + 2 * g + 3), max c₁ 0 * √(g + 1),
    fun γ₀ hγ₀ hγ₀' => ?_⟩
  let γ : ℝ := γ₀ / (2 * (g + γ₀))
  have hγ : 0 < γ := by positivity
  obtain ⟨c₂₀, hc₂₀, hL8⟩ := exists_pos_forall_eventually_isAdmissiblePair X A hg j hj D
    hrad hsupp kbar N hN hn x hx hxbpf Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx _ hψ₁ hψ₂ hkC hkX ι₁ ι₂
    hι₁ hι₂ sB hsB heΔ DB hDB y hy hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2
    hBG3 c₁₀' γ₀ hγ₀ hγ₀'
  have hchart := by
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    letI := functionFieldAlgebra k X.f
    have hx0 : ∀ i, x i ≠ 0 := hx.linearIndependent.ne_zero
    exact chart_nonempty X φNP (pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
        (by rw [Category.comp_id, hφNP]) (by rw [Category.comp_id, hφNP]))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) φB
      (exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0).fst
      (exists_germ_app_ratio_eq_div φB y (hy 0) _ _ hφBy).fst
  have ht : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      letI := functionFieldAlgebra k X.f
      Transcendental k (x 1 / x 0) := by
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    exact transcendental_div_of_linearIndependent X.f x (by omega) hx.linearIndependent
  refine ⟨c₂₀, fun ε hε hε1 z w hz hzw hZ => ?_⟩
  let a := √(pair z z)
  let b := √(pair w w)
  rw [show √(pair z z) = a from rfl, show √(pair w w) = b from rfl]
  have hzw' : a / b ≤ ε := hzw
  have ha : 0 < a := (div_pos hc₂₀ hε).trans_le hz
  have hc4 : 0 ≤ max c₄ 0 := le_max_right _ _
  have hc17 : 0 ≤ max c₁₇ 0 := le_max_right _ _
  have hc1 : 0 ≤ max c₁ 0 := le_max_right _ _
  rcases (Real.sqrt_nonneg (pair w w) : (0 : ℝ) ≤ b).eq_or_lt with hb0 | hb
  · have hb' : b = 0 := hb0.symm
    simp only [hb', mul_zero, div_zero, add_zero]
    have : 0 ≤ √(g + γ₀) / g := by positivity
    positivity
  have hab : a ≤ b := by
    rw [div_le_iff₀ hb] at hzw'
    nlinarith
  have hP : |pair z w| ≤ a * b :=
    abs_neronPairing_le_sqrt_mul_sqrt X A (one_le_two.trans hg) j hj D hrad hsupp kbar _ _
  let p : Spec (.of kbar) ⟶ pullback X.f X.f := pullback.lift z.left w.left
    ((Over.w z).trans (Over.w w).symm)
  have hzp : z.left = p ≫ pullback.fst X.f X.f := (pullback.lift_fst _ _ _).symm
  have hwp : w.left = p ≫ pullback.snd X.f X.f := (pullback.lift_snd _ _ _).symm
  have hR := hL8 ε hε hε1 z w hz hab hzw' hZ p hzp hwp
  obtain ⟨D₇, hD₇⟩ := hL7 γ hγ (1 / γ) (by positivity)
  obtain ⟨D₈, hD₈⟩ := hMI γ hγ (fun _ => 0) (Asymptotics.isLittleO_zero _ _)
  have hpar := eventually_bombieriParameters (g := genus X.f) hg (s := (sB : ℤ))
    (by exact_mod_cast hsB) hN hγ₀ hγ₀' ha hab ((D₇ : ℝ) + D₈)
  have h := angle_bound_of_eventually (c₄ := max c₄ 0) (c₁₇ := max c₁₇ 0) (c₁ := max c₁ 0)
    hg1 hNr hc4 hc17 hc1 hγ₀ (by linarith) hε hε1 ha hab hP (by
      refine (hpar.and (hR.and (eventually_gt_atTop 0))).mono fun D hDall => ?_
      obtain ⟨hDp, hDR, hD⟩ := hDall
      obtain ⟨d₁, d₂, d, δ₁, δ₂, hq, hNδ₁, hNδ₂, h1, h2, h3, hD1', hD2', hD3', h21, hlo, hhi,
        hgap, hbd₁, hbd₂, hbd₃⟩ :=
        exists_nat_of_bombieriParameters hg hsB hN hγ₀ hγ₀' ha hab hD D₇ D₈ hDp
      have hc₁' : ((d₁ : ℤ) + sB * d) = N * δ₁ := by exact_mod_cast hNδ₁.symm
      have hc₂' : ((d₂ : ℤ) + sB * d) = N * δ₂ := by exact_mod_cast hNδ₂.symm
      have hgapR : γ * ((d₁ : ℝ) * d₂) < (d₁ : ℝ) * d₂ - (genus X.f : ℝ) * (d : ℝ) ^ 2 := hgap
      have hloR : ((genus X.f : ℕ) : ℝ) * (d : ℝ) ^ 2 < (d₁ : ℝ) * d₂ := by
        exact_mod_cast hlo
      have hhiR : (d₁ : ℝ) * d₂ < ((genus X.f : ℕ) : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
        exact_mod_cast hhi
      obtain ⟨s, hs, F₀, hF₀, hh⟩ := hD₇ d₁ d₂ δ₁ δ₂ d (by exact_mod_cast (by omega : D₇ ≤ d₁))
        (by exact_mod_cast (by omega : D₇ ≤ d₂)) (by exact_mod_cast hc₁')
        (by exact_mod_cast hc₂') ⟨by exact_mod_cast h1, by exact_mod_cast h2,
          by exact_mod_cast h3, hlo, hhi⟩ (by push_cast; exact hgapR)
      obtain ⟨F, hrep, hheight⟩ := exists_family_of_isVojtaRepresentative _ φB δ₁ δ₂ d s F₀ hF₀
        (B := c₁₀' * (d₁ + d₂) / γ + 0) (by rw [add_zero]; positivity) (hh.trans (by
          push_cast
          rw [add_zero, hc₁₀', add_mul, add_div, one_div, inv_mul_eq_div]
          gcongr
          all_goals first | exact le_max_left _ _ | simp))
      have hMI' := fun i : ℕ × ℕ => hD₈ d₁ d₂ d δ₁ δ₂ (by omega) (by omega) (by omega) hNδ₁ hNδ₂
        (by exact_mod_cast h21) hloR hhiR hgapR s hs F hrep hheight p z w hzp hwp i
      obtain ⟨i, hi₁, hi₂, hmain⟩ : ∃ i : ℕ × ℕ, (i.1 : ℝ) ≤ 4 * N * ε * d₁ ∧
          (i.2 : ℝ) ≤ 4 * N * ε * d₂ ∧
          -c₄ * (i.1 * a ^ 2 + i.2 * b ^ 2) - c₁₇ * (d₁ + i.1 + i.2) -
            c₁₇ * d₁ / γ ≤ d₁ / (2 * g) * a ^ 2 + d₂ / (2 * g) * b ^ 2 - d * pair z w +
              c₁ * (d₁ * a + d₂ * b) := by
        refine block_exists X kbar N x φNP hφNP φB δ₁ δ₂ d s F hrep hchart ht p
          (by rw [← Category.assoc, ← hzp]; exact Over.w z) _ ?_
        intro K _ _ _ ι CK _ π hπ _ _ _ _ xK ιS hξ DK hDK ψK h1 h2 h3 φK h4 h5 sK h6 pK _ hpK
        obtain ⟨hz', hw'⟩ := hZ p hzp hwp K ι CK π hπ hξ DK hDK pK hpK
        obtain ⟨i, hi1, hi2, hadm⟩ := hDR d₁ d₂ d δ₁ δ₂ hq hNδ₁ hNδ₂ s hs F hrep hheight
          K ι CK π hπ hξ DK hDK ψK h1 h2 h3 φK h4 h5 sK h6 pK hpK hz' hw'
        exact ⟨i, hi1, hi2, hMI' i K ι CK π hπ hξ DK hDK ψK h1 h2 h3 φK h4 h5 sK h6 pK hpK
          hz' hw' hadm⟩
      exact ⟨d₁, d₂, d, i.1, i.2, hbd₁, hbd₂, hbd₃, i.1.cast_nonneg, i.2.cast_nonneg, hi₁, hi₂,
        neg_le_of_neg_le_max hγ ha hb d₁.cast_nonneg d₂.cast_nonneg i.1.cast_nonneg
          i.2.cast_nonneg hmain⟩)
  calc pair z w / (a * b) ≤ _ := h
    _ = _ := by ring

end Faltings
