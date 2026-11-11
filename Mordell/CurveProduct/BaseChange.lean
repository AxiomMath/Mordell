module

public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Height.DiagonalLowerBound
public import Mordell.BombieriVojta.Height.Lemma2
public import Mordell.BombieriVojta.Height.DeltaPrimeNeronPairing
public import Mordell.CurveProduct.Embedding.NP
public import Mordell.CurveProduct.Embedding.B
public import Mordell.CurveProduct.Intersection
public import Mordell.Jacobian.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist

/-!
# Base change of a curve with a divisor of degree one

For a field extension `K/k`, `C ×_k K` is again a curve with a divisor of degree one, and
`K`-points of `C` lift to sections of `C_K`. The stability of the Vojta classes
`vojtaClass X d₁ d₂ d` under this base change is `Faltings.schemePullbackClassHom_map_vojtaClass`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-! ### The base-changed curve -/

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The base change `C ×_k K` of a curve `X = (C, P)`, with a divisor of degree one whose class
is the pull-back of `[𝒪_C(P)]`: every Picard class of a smooth curve is the class of a divisor,
and pull-back along the field extension preserves degrees. -/
public lemma exists_baseChange (X : CurveWithDegreeOneDivisor k) :
    ∃ (XK : CurveWithDegreeOneDivisor K) (π : XK.C ⟶ X.C),
      IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      XK.classP = Stacks.Picard.schemePullbackClassHom π X.classP := by
  have := isSmoothProjectiveCurve_pullback_snd X.f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  set f' := pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : Smooth f' := SmoothOfRelativeDimension.smooth 1 f'
  have : IsCurve K f' := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one f'
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have := LocallyOfFiniteType.isLocallyNoetherian f'
  obtain ⟨D, hD⟩ := Stacks.Zeta.exists_divisorClass_eq f'
    (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f _) X.classP)
  have hdim' := (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f')).le
  have hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)).le
  have hdeg : (D.sum fun x n => n * (f'.residueDegree x.1 : ℤ)) = 1 := by
    have := invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
      (IsPullback.of_hasPullback X.f _) hdim hdim' X.classP
    rw [X.invertibleCurveDegreeHom_classP] at this
    rw [← this]
    change _ = invertibleCurveDegreeHom K f' hdim' (Stacks.Picard.schemePullbackClassHom _ X.classP)
    rw [← hD, Stacks.Zeta.divisorClass_apply, map_finsuppSum]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_zsmul, Stacks.Zeta.pointClass, degree_pointIdeal_of_isCurve f' hdim', smul_eq_mul]
  refine ⟨⟨_, f', D, hdeg⟩, pullback.fst X.f _, IsPullback.of_hasPullback X.f _, ?_⟩
  rw [← hD, Stacks.Zeta.divisorClass_apply]
  rfl

/-- Every `K`-point of `C` over `k` is the image under `π` of a section of `XK ⟶ Spec K`. -/
public lemma exists_section_homMk_eq (X : CurveWithDegreeOneDivisor k)
    (XK : CurveWithDegreeOneDivisor K) {π : XK.C ⟶ X.C}
    (h : IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    ∃ z' : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _},
      Over.homMk (z'.1 ≫ π) (by simp [h.w, reassoc_of% z'.2]) = z :=
  ⟨⟨h.lift z.left (𝟙 _) (by simpa using Over.w z), h.lift_snd _ _ _⟩,
    Over.OverMorphism.ext (h.lift_fst _ _ _)⟩

end BaseChange

end Faltings
