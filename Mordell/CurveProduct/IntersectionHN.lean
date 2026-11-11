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

/-!
# Intersection numbers with `H_N`

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one, let
`X = C ×_k C`, and for an integer `N` let `H_N = N (P × C) + N (C × P)`. For integers
`d₁, d₂, d` let `V = d₁ (P × C) + d₂ (C × P) + d Δ'`, where `Δ' = Δ - P × C - C × P` and `Δ` is
the diagonal, and let `K_X = ⋀² Ω_{X/k}` be the canonical sheaf of the surface `X`. Then

`H_N · V = N (d₁ + d₂)` and `H_N · K_X = 4 N (g - 1)`.

Both follow by bilinearity: `Δ'` is orthogonal to `P × C` and `C × P`, `(P × C) · (C × P) = 1`,
`(P × C)² = (C × P)² = 0`, and `K_X` has degree `2g - 2` on each of `P × C` and `C × P`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass_hN_and_canonical`:
  the two values above.

## Implementation notes

The class of `V` in `Pic(X)` is `Faltings.CurveWithDegreeOneDivisor.vojtaClass X d₁ d₂ d`, and
`H_N` is its value `vojtaClass X N N 0`. The intersection pairing on `Pic(X)` is
`AlgebraicGeometry.picardIntersection` for the proper structure morphism `pr₁ ≫ f`, the closed
subscheme `Z = X` (the identity) and `d = 2`, as in
`Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass_self_and_canonical`. The
canonical sheaf enters through its class, `Stacks.SheafOfModules.picardClass` of the invertible
sheaf `AlgebraicGeometry.Scheme.Modules.exteriorPower Ω_{X/k} 2`. The genus is
`AlgebraicGeometry.genus X.f`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3 and Section 8
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- A multilinear form in two variables, as a bilinear map. -/
@[expose] public def toBilin {G : Type*} [AddCommGroup G] (I : MultilinearMap ℤ (fun _ : Fin 2 => G) ℤ) :
    G →ₗ[ℤ] G →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => I ![x, y]) (fun _ _ _ => I.cons_add _ _ _)
    (fun _ _ _ => I.cons_smul _ _ _) (fun a _ _ => (I.curryLeft a).cons_add _ _ _)
    (fun _ a _ => (I.curryLeft a).cons_smul _ _ _)

/-- On a proper surface, the intersection pairing of two classes is symmetric. -/
public lemma picardIntersection_comm (k : Type*) [Field k] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hX : topologicalKrullDim X = 2)
    (x y : Stacks.SheafOfModules.PicardGroup X.presheaf X.ringCatIsSheaf) :
    picardIntersection k f (𝟙 X) 2 (by simp [hX]) ![x, y] =
      picardIntersection k f (𝟙 X) 2 (by simp [hX]) ![y, x] := by
  rw [picardIntersection_apply, picardIntersection_apply]
  exact (intersectionNumber_congr_family _ _ (𝟙 _) 2 _ (by ext q; fin_cases q <;> rfl)).trans
    (intersectionNumber_comp_perm k f (𝟙 X) 2 (by simp [hX]) (fun q => picardRep (![y, x] q))
      (Equiv.swap 0 1))

/-- The algebra of `H_N · V`: for a symmetric bilinear form with the intersection numbers of
`a = P × C`, `b = C × P` and `δ = Δ`,
`(N a + N b) · (d₁ a + d₂ b + d (δ - a - b)) = N (d₁ + d₂)`. -/
private lemma bilin_hN {G : Type*} [AddCommGroup G] (B : G →ₗ[ℤ] G →ₗ[ℤ] ℤ)
    (hS : ∀ x y, B x y = B y x) (a b δ : G) (haa : B a a = 0) (hbb : B b b = 0)
    (hab : B a b = 1) (hδa : B δ a = 1) (hδb : B δ b = 1) (N d₁ d₂ d : ℤ) :
    B (N • a + N • b) (d₁ • a + d₂ • b + d • (δ - a - b)) = N * (d₁ + d₂) := by
  simp only [map_add, map_sub, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    haa, hbb, hab, hS b a, hS a δ, hS b δ, hδa, hδb]
  ring

/-- The algebra of `H_N · K_X`: if `K · a = K · b = 2g - 2`, then
`(N a + N b) · K = 4 N (g - 1)`. -/
private lemma bilin_hN_canonical {G : Type*} [AddCommGroup G] (B : G →ₗ[ℤ] G →ₗ[ℤ] ℤ)
    (hS : ∀ x y, B x y = B y x) (K a b : G) (g : ℤ) (hKa : B K a = 2 * g - 2)
    (hKb : B K b = 2 * g - 2) (N : ℤ) : B (N • a + N • b) K = 4 * N * (g - 1) := by
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hS a K, hS b K, hKa, hKb]
  ring

/-- On `X = C ×_k C` for a curve `(C, P)` of genus `g` with a divisor of degree one, the class
`H_N = vojtaClass X N N 0` of `N (P × C) + N (C × P)` satisfies, for the intersection pairing
`picardIntersection` on `Pic(X)`, the class `V = vojtaClass X d₁ d₂ d` and the class `K_X` of
`⋀² Ω_{X/k}`: `H_N · V = N (d₁ + d₂)` and `H_N · K_X = 4 N (g - 1)`. -/
@[faltings "lem_nt_intersection_h_n"]
theorem picardIntersection_vojtaClass_hN_and_canonical (X : CurveWithDegreeOneDivisor k)
    (N d₁ d₂ d : ℤ) :
    haveI : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
        (IsPullback.of_hasPullback X.f X.f).flip
        (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
    haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
      smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
      (pullback.fst X.f X.f ≫ X.f) 2
    let I := picardIntersection k (pullback.fst X.f X.f ≫ X.f) (𝟙 _) 2 (by
      rcases isEmpty_or_nonempty ↥(pullback X.f X.f) with h | h
      · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
      · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
          (pullback.fst X.f X.f ≫ X.f)).le)
    let K := Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2)
      (Scheme.Modules.isInvertible_exteriorPower_self _ 2)
    I ![X.vojtaClass N N 0, X.vojtaClass d₁ d₂ d] = N * (d₁ + d₂) ∧
      I ![X.vojtaClass N N 0, K] = 4 * N * ((genus X.f : ℤ) - 1) := by
  intro I K
  obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := picardIntersection_vojtaClass X
  obtain ⟨c₁, c₂, -⟩ := picardIntersection_canonical_vojtaClass X
  haveI : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback X.f X.f).flip (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
  haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
  haveI : Nonempty ↥(pullback X.f X.f) := ⟨(pullback.diagonal X.f).base (Classical.arbitrary X.C)⟩
  have hS : ∀ x y, toBilin I x y = toBilin I y x := picardIntersection_comm k _
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (pullback.fst X.f X.f ≫ X.f))
  have hH : X.vojtaClass N N 0 = N • X.vojtaClass 1 0 0 + N • X.vojtaClass 0 1 0 := by
    rw [vojtaClass_eq_coords X N N 0, zero_smul, add_zero]
  rw [hH, vojtaClass_eq_coords X d₁ d₂ d]
  exact ⟨bilin_hN (toBilin I) hS _ _ _ h₁ h₂ h₃ h₄ h₅ N d₁ d₂ d,
    bilin_hN_canonical (toBilin I) hS K _ _ _ c₁ c₂ N⟩

end Faltings.CurveWithDegreeOneDivisor
