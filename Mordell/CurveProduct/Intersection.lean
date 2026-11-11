module
public import Mordell.AlgebraicGeometry.PicardPullback
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.IntersectionPullback
public import Mordell.Jacobian.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.DifferentialsDegreeGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativelyAmple

/-!
# Intersection numbers on `C × C`

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one, let
`X = C ×_k C` with projections `pr₁, pr₂`, and let `Δ ⊆ X` be the diagonal. Write `P × C` and
`C × P` for the classes `pr₁^*[𝒪_C(P)]` and `pr₂^*[𝒪_C(P)]` in `Pic(X)`. The intersection
pairing on the proper surface `X` takes the values

`(P × C)² = (C × P)² = 0`, `(P × C) · (C × P) = 1`, `Δ · (P × C) = Δ · (C × P) = 1`,
`Δ² = 2 - 2g`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.picardIntersection_vojtaClass`: the six values above.

## Implementation notes

The classes are values of `Faltings.CurveWithDegreeOneDivisor.vojtaClass`: `P × C` is
`vojtaClass 1 0 0`, `C × P` is `vojtaClass 0 1 0` and `[𝒪_X(Δ)]` is `vojtaClass 1 1 1`. The
intersection pairing on `Pic(X)` is `AlgebraicGeometry.picardIntersection` for the proper
structure morphism `pr₁ ≫ f`, the closed subscheme `Z = X` (the identity) and `d = 2`; on
classes of invertible modules it is `AlgebraicGeometry.intersectionNumber`
(`AlgebraicGeometry.picardIntersection_picardClass`). The bound `dim X ≤ 2` it requires holds
because `X` is smooth of relative dimension `2` over `k`. The genus is
`AlgebraicGeometry.genus X.f`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3 and Section 8
* [Stacks Project, Tag 0BEP]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- `deg Δ^* 𝒪(-Δ) = deg Ω = 2g - 2`. -/
private lemma invertibleCurveDegree_pullback_diagonal_negativeTwist (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.diagonal f)).obj
        (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker))] :
    invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)
      ((Scheme.Modules.pullback (pullback.diagonal f)).obj
        (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker)) = 2 * genus f - 2 := by
  have e : Scheme.Hom.relativeDifferentials f ≅
      (Scheme.Modules.pullback (pullback.diagonal f)).obj
        (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker) :=
    Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f ≪≫
      Stacks.CartierConormal.conormalSheafIsoPullbackSelf (pullback.diagonal f) ≪≫
      (RingedSpaceModuleAdjunction.modulePullback _).mapIso
        (idealSheafIsoSubschemeιOfKerEq (pullback.diagonal f) rfl)
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve k f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one f
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  rw [← invertibleCurveDegree_eq_of_iso k f _ e]
  exact invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two f

/-- The degree of a pulled-back invertible module is the degree homomorphism at the pulled-back
class. -/
private lemma invertibleCurveDegree_pullback_eq_degreeHom (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (g : Y ⟶ Spec (.of k)) [IsProper g]
    (hY : topologicalKrullDim Y ≤ 1) (L : Z.Modules)
    [hL : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 ((Scheme.Modules.pullback φ).obj L)] :
    invertibleCurveDegree k g hY ((Scheme.Modules.pullback φ).obj L) =
      invertibleCurveDegreeHom k g hY (Stacks.Picard.schemePullbackClassHom φ
        (Stacks.SheafOfModules.picardClass _ _ L hL)) :=
  (invertibleCurveDegreeHom_picardClass k _ hY _ (isInvertible_pullbackObj _ _)).symm.trans
    (congrArg _ (Stacks.Picard.pullbackClass_classOf φ.toLRSHom.toShHom L hL).symm)

/-- `Δ² = 2 - 2g`: by `intersectionNumber_diagonal_eq_invertibleCurveDegree` it is
`deg Δ^* 𝒪(Δ) = -deg Δ^* 𝒪(-Δ)`, and `Δ^* 𝒪(-Δ)` is the conormal sheaf `Ω_C`, of degree
`2g - 2`. -/
private lemma intersectionNumber_diagonal_self (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (M : (pullback f f).Modules)
    [hM : SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 M]
    (eM : M ≅ Stacks.Divisors.invertibleSheaf (pullback.diagonal f).ker)
    (hX : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞)) (h) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hX ![M, M] h =
      2 - 2 * genus f := by
  have hN : SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2
      (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker) :=
    (isEffectiveCartierDivisor_ker_diagonal k f).1
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.diagonal f)).obj
        (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker)) :=
    isInvertible_pullbackObj _ _
  have := isInvertible_pullbackObj (pullback.diagonal f) M
  have h1 : Stacks.SheafOfModules.picardClass _ _ M hM =
      -Stacks.SheafOfModules.picardClass _ _
        (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker) hN :=
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)).2 ⟨eM⟩).trans
      ((neg_neg _).symm.trans
        (congrArg Neg.neg (Stacks.Divisors.negativeTwistPicardClass_eq_neg _).symm))
  have hdeg := (invertibleCurveDegree_pullback_eq_degreeHom k (pullback.diagonal f) f _
    (Stacks.Divisors.negativeTwist (pullback.diagonal f).ker)).symm.trans
    (invertibleCurveDegree_pullback_diagonal_negativeTwist k f)
  rw [intersectionNumber_diagonal_eq_invertibleCurveDegree k f M M eM,
    invertibleCurveDegree_pullback_eq_degreeHom k (pullback.diagonal f)]
  refine (congrArg (fun x => invertibleCurveDegreeHom k f _
    (Stacks.Picard.schemePullbackClassHom (pullback.diagonal f) x)) h1).trans ?_
  dsimp only
  rw [map_neg, map_neg, hdeg]
  ring

/-- The pull-back of a class is the class of the pull-back of its representative `picardRep`. -/
public lemma schemePullbackClassHom_eq_picardClass_pullbackObj {Y Z : Scheme.{u}} (φ : Y ⟶ Z)
    (c : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClassHom φ c =
      Stacks.SheafOfModules.picardClass _ _ ((Scheme.Modules.pullback φ).obj (picardRep c))
        (isInvertible_pullbackObj _ _) :=
  (congrArg (Stacks.Picard.schemePullbackClassHom φ) (picardClass_picardRep c).symm).trans
    (schemePullbackClassHom_picardClass φ _ _)

end Faltings

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The representative `picardRep X.classP` of `[𝒪_C(P)]` has degree one. -/
public lemma invertibleCurveDegree_picardRep_classP (X : CurveWithDegreeOneDivisor k)
    (hdimC : topologicalKrullDim X.C ≤ 1) :
    invertibleCurveDegree k X.f hdimC (picardRep X.classP) = 1 :=
  (invertibleCurveDegreeHom_picardClass k X.f hdimC _ _).symm.trans
    ((congrArg _ (picardClass_picardRep _)).trans (X.invertibleCurveDegreeHom_classP hdimC))

/-- On `X = C ×_k C` for a curve `(C, P)` of genus `g` with a divisor of degree one, with
`P × C = vojtaClass 1 0 0`, `C × P = vojtaClass 0 1 0` and `Δ = vojtaClass 1 1 1`, the
intersection pairing `picardIntersection` on `Pic(X)` satisfies `(P × C)² = (C × P)² = 0`,
`(P × C) · (C × P) = 1`, `Δ · (P × C) = Δ · (C × P) = 1` and `Δ² = 2 - 2g`. -/
@[faltings "lem_nt_intersection_numbers_c_times_c"]
public theorem picardIntersection_vojtaClass (X : CurveWithDegreeOneDivisor k) :
    let I := picardIntersection k (pullback.fst X.f X.f ≫ X.f) (𝟙 _) 2 (by
      have : SmoothOfRelativeDimension 1 (pullback.fst X.f X.f) :=
        (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
          (IsPullback.of_hasPullback X.f X.f).flip
          (inferInstanceAs (SmoothOfRelativeDimension 1 X.f))
      have : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
        smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
      rcases isEmpty_or_nonempty ↥(pullback X.f X.f) with h | h
      · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
      · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
          (pullback.fst X.f X.f ≫ X.f)).le)
    I ![X.vojtaClass 1 0 0, X.vojtaClass 1 0 0] = 0 ∧
      I ![X.vojtaClass 0 1 0, X.vojtaClass 0 1 0] = 0 ∧
      I ![X.vojtaClass 1 0 0, X.vojtaClass 0 1 0] = 1 ∧
      I ![X.vojtaClass 1 1 1, X.vojtaClass 1 0 0] = 1 ∧
      I ![X.vojtaClass 1 1 1, X.vojtaClass 0 1 0] = 1 ∧
      I ![X.vojtaClass 1 1 1, X.vojtaClass 1 1 1] = 2 - 2 * (genus X.f : ℤ) := by
  intro I
  let A : X.C.Modules := picardRep X.classP
  obtain ⟨hΔ, -, -⟩ := isEffectiveCartierDivisor_ker_diagonal k X.f
  let M : (pullback X.f X.f).Modules := Stacks.Divisors.invertibleSheaf (pullback.diagonal X.f).ker
  have hM : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2 M := Stacks.Divisors.isInvertible_invertibleSheaf_picard _
  have hΔM : Stacks.Divisors.picardClass (pullback.diagonal X.f).ker =
      Stacks.SheafOfModules.picardClass _ _ M hM := rfl
  have hdegA := X.invertibleCurveDegree_picardRep_classP
    (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  have hX : topologicalKrullDim ↥(pullback X.f X.f) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    simp [topologicalKrullDim_pullback_self k X.f]
  obtain ⟨P1, P2⟩ := intersectionNumber_pullback_curve_prod_self k X.f A A M (Iso.refl _)
  obtain ⟨P20, P20'⟩ := P2 0
  obtain ⟨P21, P21'⟩ := P2 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vojtaClass_one_zero_zero, schemePullbackClassHom_eq_picardClass_pullbackObj]
    exact (picardIntersection_picardClass_pair k _ hX _ _).trans P20
  · rw [vojtaClass_zero_one_zero, schemePullbackClassHom_eq_picardClass_pullbackObj]
    exact (picardIntersection_picardClass_pair k _ hX _ _).trans P21
  · rw [vojtaClass_one_zero_zero, vojtaClass_zero_one_zero,
      schemePullbackClassHom_eq_picardClass_pullbackObj,
      schemePullbackClassHom_eq_picardClass_pullbackObj]
    refine (picardIntersection_picardClass_pair k _ hX _ _).trans (P1.trans ?_)
    rw [hdegA, mul_one]
  · rw [vojtaClass_one_one_one, vojtaClass_one_zero_zero, hΔM,
      schemePullbackClassHom_eq_picardClass_pullbackObj]
    exact (picardIntersection_picardClass_pair k _ hX _ _).trans
      ((intersectionNumber_pair_swap k _ hX _ _).trans (P20'.trans hdegA))
  · rw [vojtaClass_one_one_one, vojtaClass_zero_one_zero, hΔM,
      schemePullbackClassHom_eq_picardClass_pullbackObj]
    exact (picardIntersection_picardClass_pair k _ hX _ _).trans
      ((intersectionNumber_pair_swap k _ hX _ _).trans (P21'.trans hdegA))
  · rw [vojtaClass_one_one_one, hΔM]
    exact (picardIntersection_picardClass_pair k _ hX _ _).trans
      (intersectionNumber_diagonal_self k X.f M (Iso.refl _) hX _)

end Faltings.CurveWithDegreeOneDivisor
