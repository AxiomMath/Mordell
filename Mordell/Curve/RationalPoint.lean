module

public import Mordell.FunctionField.Place.Basic
public import Mordell.FunctionField.SmoothProjectiveModel
public import Mordell.Curve.PlacesClosedPoints
public import Mordell.Curve.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import Mordell.AlgebraicGeometry.RationalPoint
public import Mordell.Curve.Normal
public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothVectorFields
public import Mordell.Curve.DegreeOneDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SectionPoint
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes

/-!
# Rational points of curves

A section `σ` of a smooth projective geometrically integral curve `f : C ⟶ Spec k` gives a curve
with a divisor of degree one, `CurveWithDegreeOneDivisor.ofSection`; and `C(k)` is finite as soon
as the `Ω`-points of `C` defined over an intermediate field `K` of `Ω / k` are.
-/

public section

universe u v

open AlgebraicGeometry CategoryTheory

namespace Faltings

/-- The curve `f : C ⟶ Spec k` with the divisor `P = σ(pt)` of a rational point `σ`, a section of
`f`: the image of `σ` is a closed point of residue degree one, so `P` has degree one. -/
@[expose] noncomputable def CurveWithDegreeOneDivisor.ofSection (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (σ : Spec (.of k) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    CurveWithDegreeOneDivisor k where
  C := C
  f := f
  isSmoothProjectiveCurve :=
    { toSmoothOfRelativeDimension := Stacks.Curves.smoothOfRelativeDimension_one_of_isCurve f }
  P := Finsupp.single ⟨σ (IsLocalRing.closedPoint k),
    ProjectiveLineCriterion.isClosed_singleton_of_section f σ hσ _⟩ 1
  degree_P := by
    rw [Finsupp.sum_single_index (by simp), one_mul]
    exact_mod_cast (Stacks.Chow.residueDegree_eq_one_of_section f σ hσ _).1

/-- **Rational points are points defined over `K`.** Let `f : C ⟶ Spec k` be a scheme over a
field `k`, `Ω` a field extension of `k` and `K` an intermediate field of `Ω / k`. If the set of
`Ω`-points `z : Spec Ω ⟶ C` over `k` defined over `K` (factoring through `Spec Ω ⟶ Spec K`) is
finite, then so is the set `C(k)` of sections of `f`: a section `σ` gives the `Ω`-point
`Spec Ω ⟶ Spec k ⟶ C`, defined over `K`, and `σ` is recovered from it since `Spec Ω ⟶ Spec k`
is an epimorphism. -/
theorem finite_setOf_comp_eq_id_of_finite (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (Ω : Type u) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (h : {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk f |
      ∃ q : Spec (.of K) ⟶ C, z.left = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ q}.Finite) :
    {σ : Spec (.of k) ⟶ C | σ ≫ f = 𝟙 _}.Finite := by
  set π : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hπ
  have : Flat π := by
    rw [hπ, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective π := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have hπK : π = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have := h.to_subtype
  refine Set.finite_coe_iff.mp (Finite.of_injective (β := {z : Over.mk π ⟶ Over.mk f |
      ∃ q : Spec (.of K) ⟶ C, z.left = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ q})
    (fun σ => ⟨Over.homMk (π ≫ σ.1) (by
        have hσ : σ.1 ≫ f = 𝟙 _ := σ.2
        simp [hσ]),
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ σ.1, by simp [hπK]⟩) ?_)
  intro σ τ hστ
  exact Subtype.ext ((cancel_epi π).1 (congrArg CommaMorphism.left (congrArg Subtype.val hστ)))

end Faltings

end
