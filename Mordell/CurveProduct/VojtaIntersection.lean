module

public import Mathlib
public import Mordell.Attr
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Diagonal
public import Mordell.CurveProduct.IntersectionCanonical
public import Mordell.CurveProduct.Intersection
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import Mordell.CurveProduct.IntersectionHN

/-!
# Self-intersection and canonical degree of `V`

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one, let
`X = C ×_k C`, and for integers `d₁, d₂, d` let `V = d₁ (P × C) + d₂ (C × P) + d Δ'`, where
`Δ' = Δ - P × C - C × P` and `Δ` is the diagonal. Let `K_X = ⋀² Ω_{X/k}` be the canonical
sheaf of the surface `X`. Then

`V² = 2 (d₁ d₂ - g d²)` and `K_X · V = (2g - 2)(d₁ + d₂)`.

They follow by bilinearity from the intersection numbers of `P × C`, `C × P` and `Δ`: the class
`Δ'` is orthogonal to `P × C`, to `C × P` and to `K_X`, and `Δ'² = -2g`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass_self_and_canonical`:
  the two values above.

## Implementation notes

The class of `V` in `Pic(X)` is `Faltings.CurveWithDegreeOneDivisor.vojtaClass X d₁ d₂ d`.
The intersection pairing on `Pic(X)` is `AlgebraicGeometry.picardIntersection` for the proper
structure morphism `pr₁ ≫ f`, the closed subscheme `Z = X` (the identity) and `d = 2`, as in
`Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass`. The canonical sheaf enters
through its class: `K_X = AlgebraicGeometry.Scheme.Modules.exteriorPower Ω_{X/k} 2` is
invertible because `Ω_{X/k}` is locally free of rank `2`
(`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`), and its class is
`Stacks.SheafOfModules.picardClass` of it. The genus is `AlgebraicGeometry.genus X.f`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3 and Section 8
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The algebra of the computation: a symmetric bilinear form with the intersection numbers of
`P × C`, `C × P`, `Δ` gives `V² = 2 (d₁ d₂ - g d²)`. -/
private lemma bilin_self {G : Type*} [AddCommGroup G] (B : G →ₗ[ℤ] G →ₗ[ℤ] ℤ)
    (hS : ∀ x y, B x y = B y x) (a b δ : G) (g : ℤ) (haa : B a a = 0) (hbb : B b b = 0)
    (hab : B a b = 1) (hδa : B δ a = 1) (hδb : B δ b = 1) (hδδ : B δ δ = 2 - 2 * g)
    (d₁ d₂ d : ℤ) :
    B (d₁ • a + d₂ • b + d • (δ - a - b)) (d₁ • a + d₂ • b + d • (δ - a - b)) =
      2 * (d₁ * d₂ - g * d ^ 2) := by
  simp only [map_add, map_sub, map_zsmul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, haa, hbb, hab, hS b a, hδa, hS a δ, hδb, hS b δ, hδδ]
  ring

/-- The algebra of the computation for `K_X · V`. -/
private lemma bilin_canonical {G : Type*} [AddCommGroup G] (B : G →ₗ[ℤ] G →ₗ[ℤ] ℤ)
    (K a b δ : G) (g : ℤ) (hKa : B K a = 2 * g - 2) (hKb : B K b = 2 * g - 2)
    (hKδ : B K δ = 4 * g - 4) (d₁ d₂ d : ℤ) :
    B K (d₁ • a + d₂ • b + d • (δ - a - b)) = (2 * g - 2) * (d₁ + d₂) := by
  simp only [map_add, map_sub, map_zsmul, smul_eq_mul, hKa, hKb, hKδ]
  ring

/-- `vojtaClass` in terms of `P × C`, `C × P` and `Δ`. -/
private lemma vojtaClass_eq_combination {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    (d₁ d₂ d : ℤ) :
    X.vojtaClass d₁ d₂ d = d₁ • X.vojtaClass 1 0 0 + d₂ • X.vojtaClass 0 1 0 +
      d • (X.vojtaClass 1 1 1 - X.vojtaClass 1 0 0 - X.vojtaClass 0 1 0) := by
  unfold vojtaClass
  dsimp only
  module

/-- On `X = C ×_k C` for a curve `(C, P)` of genus `g` with a divisor of degree one, the class
`V = vojtaClass X d₁ d₂ d` of `d₁ (P × C) + d₂ (C × P) + d Δ'` satisfies, for the intersection
pairing `picardIntersection` on `Pic(X)` and the class `K_X` of `⋀² Ω_{X/k}`,
`V² = 2 (d₁ d₂ - g d²)` and `K_X · V = (2g - 2)(d₁ + d₂)`. -/
@[faltings "lem_nt_intersection_vojta"]
theorem picardIntersection_vojtaClass_self_and_canonical (X : CurveWithDegreeOneDivisor k)
    (d₁ d₂ d : ℤ) :
    haveI : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
        (IsPullback.of_hasPullback X.f X.f).flip
        (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
    haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
      smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (pullback.fst X.f X.f ≫ X.f) 2
    let I := picardIntersection k (pullback.fst X.f X.f ≫ X.f) (𝟙 _) 2 (by
      rcases isEmpty_or_nonempty ↥(pullback X.f X.f) with h | h
      · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
      · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
          (pullback.fst X.f X.f ≫ X.f)).le)
    let K := Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2)
      (Scheme.Modules.isInvertible_exteriorPower_self _ 2)
    I ![X.vojtaClass d₁ d₂ d, X.vojtaClass d₁ d₂ d] = 2 * (d₁ * d₂ - genus X.f * d ^ 2) ∧
      I ![K, X.vojtaClass d₁ d₂ d] = (2 * (genus X.f : ℤ) - 2) * (d₁ + d₂) := by
  intro I K
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := picardIntersection_vojtaClass X
  obtain ⟨c₁, c₂, c₃⟩ := picardIntersection_canonical_vojtaClass X
  haveI : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback X.f X.f).flip (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
  haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
  haveI : Nonempty ↥(pullback X.f X.f) := ⟨(pullback.diagonal X.f).base (Classical.arbitrary X.C)⟩
  have hS : ∀ x y, toBilin I x y = toBilin I y x := picardIntersection_comm k _
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (pullback.fst X.f X.f ≫ X.f))
  rw [vojtaClass_eq_combination X d₁ d₂ d]
  exact ⟨bilin_self (toBilin I) hS _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ d₁ d₂ d,
    bilin_canonical (toBilin I) K _ _ _ _ c₁ c₂ c₃ d₁ d₂ d⟩

end Faltings.CurveWithDegreeOneDivisor
