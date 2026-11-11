module
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import Mordell.CurveProduct.CanonicalSheaf
public import Mordell.CurveProduct.IntersectionPullback
public import Mordell.Jacobian.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.DifferentialsDegreeGenus
public import Mordell.CurveProduct.Intersection

/-!
# Intersection numbers with the canonical class on `C × C`

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one, let
`X = C ×_k C` with projections `pr₁, pr₂`, and let `Δ ⊆ X` be the diagonal. Write `P × C` and
`C × P` for the classes `pr₁^*[𝒪_C(P)]` and `pr₂^*[𝒪_C(P)]` in `Pic(X)`, and `K_X` for the
class of the canonical sheaf `⋀² Ω_{X/k}` of the surface `X`. Since
`K_X = pr₁^* Ω_{C/k} + pr₂^* Ω_{C/k}` and `deg Ω_{C/k} = 2g - 2`, the intersection pairing on
`X` gives

`K_X · (P × C) = K_X · (C × P) = 2g - 2`, `K_X · Δ = 4g - 4`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.picardIntersection_canonical_vojtaClass`: the three
  values above.

## Implementation notes

The classes are values of `Faltings.CurveWithDegreeOneDivisor.vojtaClass`: `P × C` is
`vojtaClass 1 0 0`, `C × P` is `vojtaClass 0 1 0` and `[𝒪_X(Δ)]` is `vojtaClass 1 1 1`. The
canonical class is `Stacks.SheafOfModules.picardClass` of
`AlgebraicGeometry.Scheme.Modules.exteriorPower` of the relative differentials of
`pr₁ ≫ f : X ⟶ Spec k` in degree `2`; it is invertible because `X` is smooth of relative
dimension `2` over `k`, so `Ω_{X/k}` is locally free of rank `2`
(`Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials`,
`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`). The intersection pairing on
`Pic(X)` is `AlgebraicGeometry.picardIntersection` for the proper structure morphism `pr₁ ≫ f`,
the closed subscheme `Z = X` and `d = 2`, as for
`Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass`. The genus is
`AlgebraicGeometry.genus X.f`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
-/

open Faltings (coord_identities schemePullbackClassHom_eq_picardClass_pullbackObj)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- On `C ×_k C`, the canonical class splits: for every invertible `N`,
`K_X · N = (pr₁^* Ω_{C/k} · N) + (pr₂^* Ω_{C/k} · N)`, from `⋀² Ω_{X/k} ≅ pr₁^* Ω ⊗ pr₂^* Ω` and
additivity of the intersection number in the first slot. -/
private lemma picardIntersection_canonical_eq_add {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (hd : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞))
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 f.relativeDifferentials]
    [hK : SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2
      (Scheme.Modules.exteriorPower (pullback.fst f f ≫ f).relativeDifferentials 2)]
    (N : (pullback f f).Modules)
    [hN : SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 N] :
    picardIntersection k (pullback.fst f f ≫ f) (𝟙 _) 2 hd
        ![Stacks.SheafOfModules.picardClass _ _
            (Scheme.Modules.exteriorPower (pullback.fst f f ≫ f).relativeDifferentials 2) hK,
          Stacks.SheafOfModules.picardClass _ _ N hN] =
      @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hd
          ![(Scheme.Modules.pullback (pullback.fst f f)).obj f.relativeDifferentials, N]
          (Fin.forall_fin_two.2 ⟨isInvertible_pullbackObj _ _, hN⟩) +
        @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hd
          ![(Scheme.Modules.pullback (pullback.snd f f)).obj f.relativeDifferentials, N]
          (Fin.forall_fin_two.2 ⟨isInvertible_pullbackObj _ _, hN⟩) := by
  have := isInvertible_pullbackObj (pullback.fst f f) f.relativeDifferentials
  have := isInvertible_pullbackObj (pullback.snd f f) f.relativeDifferentials
  exact (picardIntersection_picardClass_pair k _ hd _ N).trans
    (intersectionNumber_pair_eq_add_of_iso_tensorObj k _ hd _ _ _ N
      (nonempty_exteriorPower_relativeDifferentials_pullback_iso_tensorObj k f).some)

/-- On `X = C ×_k C` for a curve `(C, P)` of genus `g` with a divisor of degree one, with
`P × C = vojtaClass 1 0 0`, `C × P = vojtaClass 0 1 0`, `Δ = vojtaClass 1 1 1` and `K_X` the
class of the canonical sheaf `⋀² Ω_{X/k}`, the intersection pairing `picardIntersection` on
`Pic(X)` satisfies `K_X · (P × C) = K_X · (C × P) = 2g - 2` and `K_X · Δ = 4g - 4`. -/
@[faltings "lem_nt_intersection_canonical"]
public theorem picardIntersection_canonical_vojtaClass (X : CurveWithDegreeOneDivisor k) :
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
    let K := Stacks.SheafOfModules.picardClass _ _
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2)
      (Scheme.Modules.isInvertible_exteriorPower_self _ 2)
    I ![K, X.vojtaClass 1 0 0] = 2 * (genus X.f : ℤ) - 2 ∧
      I ![K, X.vojtaClass 0 1 0] = 2 * (genus X.f : ℤ) - 2 ∧
      I ![K, X.vojtaClass 1 1 1] = 4 * (genus X.f : ℤ) - 4 := by
  intro I K
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback X.f X.f).flip
      (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
  have : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
    (pullback.fst X.f X.f ≫ X.f) 2
  have : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2) :=
    Scheme.Modules.isInvertible_exteriorPower_self _ 2
  obtain ⟨hΔ, -, -⟩ := isEffectiveCartierDivisor_ker_diagonal k X.f
  -- `M = 𝒪_X(Δ)`
  let M := Stacks.Divisors.invertibleSheaf (pullback.diagonal X.f).ker
  have : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2 M := Stacks.Divisors.isInvertible_invertibleSheaf_picard _
  -- `A` represents `[𝒪_C(P)]`, of degree one, and `Ω = Ω_{C/k}` has degree `2g - 2`
  let A : X.C.Modules := picardRep X.classP
  let Ω : X.C.Modules := X.f.relativeDifferentials
  have hdimC := topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  have hdegA : invertibleCurveDegree k X.f hdimC A = 1 :=
    (invertibleCurveDegreeHom_picardClass k X.f hdimC A _).symm.trans
      ((congrArg _ (picardClass_picardRep _)).trans (X.invertibleCurveDegreeHom_classP hdimC))
  have hdegΩ : invertibleCurveDegree k X.f hdimC Ω = 2 * genus X.f - 2 := by
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.f.appTop) :=
      isIso_globalSections_of_geometricallyIntegral k X.f
    exact invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two X.f
  have hX : topologicalKrullDim ↥(pullback X.f X.f) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    simp [topologicalKrullDim_pullback_self k X.f]
  have hsplit := picardIntersection_canonical_eq_add X.f hX
  obtain ⟨Q1, Q2⟩ := intersectionNumber_pullback_curve_prod_self k X.f Ω A M (Iso.refl _)
  obtain ⟨R1, -⟩ := intersectionNumber_pullback_curve_prod_self k X.f A Ω M (Iso.refl _)
  refine ⟨?_, ?_, ?_⟩
  · rw [vojtaClass_one_zero_zero, schemePullbackClassHom_eq_picardClass_pullbackObj]
    refine ((hsplit _).trans (congrArg₂ (· + ·) (Q2 0).1
      ((intersectionNumber_pair_swap k _ hX _ _).trans R1))).trans ?_
    rw [hdegA, hdegΩ]
    ring
  · rw [vojtaClass_zero_one_zero, schemePullbackClassHom_eq_picardClass_pullbackObj]
    refine ((hsplit _).trans (congrArg₂ (· + ·) Q1 (Q2 1).1)).trans ?_
    rw [hdegA, hdegΩ]
    ring
  · rw [vojtaClass_one_one_one]
    refine ((hsplit M).trans (congrArg₂ (· + ·) (Q2 0).2 (Q2 1).2)).trans ?_
    rw [hdegΩ]
    ring

end Faltings.CurveWithDegreeOneDivisor
