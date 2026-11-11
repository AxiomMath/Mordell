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
# Places of degree one are rational points

Let `K` be a perfect field, `F/K` an algebraic function field of one variable and `(C, φ)` a
smooth projective model of `F/K`, with structure morphism `f : C ⟶ Spec K` and
`φ : K(C) ≃ₐ[K] F`. The places of `F/K` of degree one are in bijection with the `K`-rational
points of `C`, i.e. the sections `s : Spec K ⟶ C` of `f`. The bijection sends a place `v` to the
rational point `s` whose image `x = s(pt)` is the centre of `v`: the valuation ring `𝒪_v` is the
image under `φ` of the local ring `𝒪_{C,x} ⊆ K(C)`.

## Main results

* `Faltings.FunctionField.exists_equiv_isDegreeOne_section`: there is an equivalence between
  the places of degree one of `F/K` and the sections of the structure morphism of `C`, sending
  each place to the rational point at which it is centred.
* `Faltings.CurveWithDegreeOneDivisor.ofSection`: a curve with a rational point `σ`, with the
  divisor `P = σ(pt)` of degree one.
* `Faltings.finite_setOf_comp_eq_id_of_finite`: `C(k)` is finite as soon as the set of
  `Ω`-points of `C` defined over an intermediate field `K` of `Ω / k` is.

## Implementation notes

The bijection is stated as an equivalence together with its characterising property: the place
`v` is centred at the image of the closed point of `Spec K` under the rational point attached to
`v`, i.e. `𝒪_v = φ(𝒪_{C,x})` with `𝒪_{C,x}` embedded in `K(C)` by the generization map
`algebraMap (C.presheaf.stalk x) C.functionField`, which needs `C` integral; this comes from the
curve structure `M.isCurve`, brought into the statement as a local instance. Since a place has
a unique centre, this pins the equivalence. The set `C(K)` is the set of sections `s` with
`s ≫ f = 𝟙 _`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.1.14
* [Stacks, Tag 01J6], [Stacks, Tag 0BY1]
-/

public section

universe u v

open AlgebraicGeometry CategoryTheory

namespace Faltings.FunctionField

/-- The residue field at the generic point of a curve is not of rank one over the base field:
it is the function field, of transcendence degree one. -/
private lemma rank_residueField_genericPoint_ne_one (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    letI : Algebra K (C.residueField (genericPoint C)) :=
      (Spec.preimage (C.fromSpecResidueField (genericPoint C) ≫ f)).hom.toAlgebra
    Module.rank K (C.residueField (genericPoint C)) ≠ 1 := by
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  let : Algebra K (C.residueField (genericPoint C)) :=
    (Spec.preimage (C.fromSpecResidueField (genericPoint C) ≫ f)).hom.toAlgebra
  intro h1
  let e : C.functionField ≃ₐ[K] C.residueField (genericPoint C) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (C.residue (genericPoint C)).hom
      ⟨RingHom.injective _, C.residue_surjective _⟩) fun a ↦ by
      change _ = (Spec.preimage (C.fromSpecResidueField (genericPoint C) ≫ f)).hom a
      rw [preimage_fromSpecResidueField_comp]
      rfl
  have : Module.Finite K (C.residueField (genericPoint C)) :=
    Module.rank_lt_aleph0_iff.mp (h1 ▸ Cardinal.one_lt_aleph0)
  have htr := trdeg_functionField_eq_one K f
  rw [e.trdeg_eq, trdeg_eq_zero] at htr
  exact zero_ne_one htr

/-- If `v` is the place centred at the closed point `x`, then `κ(x)` has rank one over `K`
exactly when `v` has degree one: the two residue fields are `K`-isomorphic. -/
private lemma rank_residueField_eq_one_iff_isDegreeOne (K : Type u) [Field K] (F : Type v)
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F)
    {x : C} (hx : IsClosed {x}) {v : Place K F}
    (hv : (v.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x) C.functionField)) :
    letI : Algebra K (C.residueField x) :=
      (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom.toAlgebra
    Module.rank K (C.residueField x) = 1 ↔ v.IsDegreeOne := by
  let : Algebra K (C.residueField x) :=
    (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom.toAlgebra
  obtain ⟨e, -⟩ := exists_algEquiv_residueField_place K F f φ hx v hv
  rw [Place.IsDegreeOne, ← Cardinal.lift_eq_one.{v}, e.toLinearEquiv.lift_rank_eq,
    Cardinal.lift_eq_one]

/-- On a normal proper curve, sending a place to its centre is a bijection from the places of
degree one onto the points whose residue field has rank one over `K`. -/
private lemma bijOn_centre (K : Type u) [Field K] (F : Type v)
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsNormal C]
    [IsProper f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F)
    (c : Place K F → C) (hc : ∀ v, IsClosed {c v} ∧ (v.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk (c v)) C.functionField)) :
    Set.BijOn c {v | v.IsDegreeOne}
      {x | letI : Algebra K (C.residueField x) :=
          (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom.toAlgebra
        Module.rank K (C.residueField x) = 1} := by
  refine ⟨fun v hv ↦ (rank_residueField_eq_one_iff_isDegreeOne K F f φ (hc v).1 (hc v).2).2 hv,
    fun v _ w _ hvw ↦ Place.ext ?_, fun x hx ↦ ?_⟩
  · change (v.toSubalgebra : Set F) = w.toSubalgebra
    rw [(hc v).2, (hc w).2, hvw]
  · have hxc := isClosed_singleton_of_ne_genericPoint K f
      (x := x) (by rintro rfl; exact rank_residueField_genericPoint_ne_one K f hx)
    obtain ⟨v, hv⟩ := exists_place_eq_image_stalk K F f φ hxc
    obtain rfl : c v = x :=
      (existsUnique_isClosed_place_eq_image_stalk K F f φ v).unique (hc v) ⟨hxc, hv⟩
    exact ⟨v, (rank_residueField_eq_one_iff_isDegreeOne K F f φ hxc hv).1 hx, rfl⟩

/-- Let `K` be a perfect field, `F/K` a function field and `M` a smooth projective model of
`F/K`. There is an equivalence `e` between the places of `F/K` of degree one and the
`K`-rational points of `M.C` (sections of `M.f`), such that every place `v` is centred at the
image of the closed point of `Spec K` under `e v`: `𝒪_v` is `M.φ` of the local ring
`𝒪_{C,x} ⊆ K(C)` at that point. -/
@[faltings "thm_ff_degree_one_places_are_rational_points"]
theorem exists_equiv_isDegreeOne_section (K : Type u) [Field K] [PerfectField K]
    (F : Type v) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (M : SmoothProjectiveModel K F) :
    haveI := M.isCurve
    ∃ e : {v : Place K F // v.IsDegreeOne} ≃ {s : Spec (.of K) ⟶ M.C // s ≫ M.f = 𝟙 _},
      ∀ v, (v.1.toSubalgebra : Set F) =
        M.φ '' Set.range
          (algebraMap (M.C.presheaf.stalk ((e v).1 (IsLocalRing.closedPoint K)))
            M.C.functionField) := by
  have := M.isCurve
  have := M.smooth
  have := M.isProjectiveVariety
  have : IsNormal M.C := isNormal_of_smooth K M.f
  have : IsProper M.f := inferInstance
  choose c hc using fun v ↦ (existsUnique_isClosed_place_eq_image_stalk K F M.f M.φ v).exists
  have hD := bijOn_centre K F M.f M.φ c hc
  have hS := bijOn_rank_residueField_eq_one K M.f
  refine ⟨hD.equiv c |>.trans (hS.equiv _).symm, fun v ↦ ?_⟩
  have h : ((hS.equiv _).symm (hD.equiv c v)).1 (IsLocalRing.closedPoint K) = c v :=
    congrArg Subtype.val ((hS.equiv _).apply_symm_apply (hD.equiv c v))
  exact h ▸ (hc v).2

end Faltings.FunctionField

end
