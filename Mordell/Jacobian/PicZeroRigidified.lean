module
public import Mordell.Jacobian.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# The functor `P⁰_C` as a quotient, and its rigidification

Let `f : C ⟶ Spec k` be a smooth projective curve. For a `k`-scheme `T`, the group
`P⁰_C(T)` is the quotient of the classes of `C ×_k T` of degree zero on every fibre by the
classes pulled back from `T`. When `T` has a `C`-point `c`, every element of `P⁰_C(T)` has a
unique representative that is trivial along the section of `c` (its *rigidification*). Over a
field extension `E/k` and a point `c₀ ∈ C(E)`, this identifies the `Pic⁰` of `C_E` rigidified
along `c₀` with `P⁰_C` restricted to `E`-schemes.

## Main definitions

* `Faltings.relativePicZeroFunctor.degreeZero f T`, `Faltings.relativePicZeroFunctor.baseClasses
  f T`: the classes of `C ×_k T` of degree zero on every fibre, and among them those pulled back
  from `T`; `P⁰_C(T)` is their quotient.
* `Faltings.relativePicZeroFunctor.rigidify f T c`: the rigidification of a degree-zero class
  along the section of a `C`-point `c` of `T`.
* `Faltings.relativePicZeroFunctor.curveOver k f E`: the curve `C_E ⟶ Spec E` over a field
  extension `E/k`.
* `Faltings.relativePicZeroFunctor.rigidified k f E c₀`: the `Pic⁰` of `C_E` rigidified along
  the section of a point `c₀ ∈ C(E)`, a functor on `E`-schemes valued in groups.

## Main results

* `Faltings.relativePicZeroFunctor.mk_rigidify`,
  `Faltings.relativePicZeroFunctor.eq_of_mk_eq_of_pointSection_eq_zero`: rigidification does not
  change the class in `P⁰_C(T)`, and a class has at most one rigidified representative.
* `Faltings.relativePicZeroFunctor.rigidifiedIso`: the rigidified `Pic⁰` of `C_E` is `P⁰_C`
  restricted to `E`-schemes; so a scheme representing the one represents the other.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 1.
* [Stacks] The Stacks Project, Tag 0B9Q.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Faltings

namespace relativePicZeroFunctor

/-- The morphism `Spec L ⟶ Spec K` of a field extension. -/
@[expose] public noncomputable abbrev specMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (.of L) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section PicZero

/-! ### The functor `P⁰_C` as a quotient -/

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

open Stacks.RigidifiedPicard Stacks.Picard

/-- The fibres of `C ⟶ Spec k` have dimension at most one. -/
public theorem topologicalKrullDim_fiber_le_one :
    ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s =>
  (topologicalKrullDim_fiber_spec f s).trans_le
    (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)

/-- The classes of `C ×_k T` of degree zero on every fibre. -/
@[expose] public noncomputable abbrev degreeZero (T : Over (Spec (.of k))) :
    AddSubgroup (smallOfScheme (bc f T)) :=
  (degree f (topologicalKrullDim_fiber_le_one f) T).ker

/-- The classes pulled back from `T`, among those of degree zero. -/
@[expose] public noncomputable abbrev baseClasses (T : Over (Spec (.of k))) :
    AddSubgroup (degreeZero f T) :=
  (smallSchemePullbackClassHom (bcProj f T)).range.addSubgroupOf (degreeZero f T)

/-- The pullback of a class of degree zero along `T ⟶ U` has degree zero. -/
public theorem bcMap_mem_degreeZero {T U : Over (Spec (.of k))} (g : T ⟶ U) (z : degreeZero f U) :
    smallSchemePullbackClassHom (bcMap f g) z.1 ∈ degreeZero f T := by
  rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_bcMap, (AddMonoidHom.mem_ker.1 z.2)]
  rfl

/-- The pullback of degree-zero classes along `T ⟶ U`. -/
@[expose] public noncomputable def degreeZeroMap {T U : Over (Spec (.of k))} (g : T ⟶ U) :
    degreeZero f U →+ degreeZero f T :=
  ((smallSchemePullbackClassHom (bcMap f g)).comp (degreeZero f U).subtype).codRestrict _
    (bcMap_mem_degreeZero f g)

/-- The functor `P⁰_C` on the class of a degree-zero class. -/
public theorem map_mk {T U : Over (Spec (.of k))} (g : T ⟶ U)
    (z : degreeZero f U) :
    (relativePicZeroFunctor k f ⋙ forget AddCommGrpCat).map g.op
        (QuotientAddGroup.mk z : degreeZero f U ⧸ baseClasses f U) =
      (QuotientAddGroup.mk (degreeZeroMap f g z) : degreeZero f T ⧸ baseClasses f T) := rfl

/-- **`𝒪_U = q_*𝒪_{C_U}` universally**: for every base change `q : V ⟶ U` of `C ⟶ Spec k`, the
comparison of structure sheaves is an isomorphism, `C` being proper and geometrically
integral. -/
public theorem isIso_c_of_isPullback {U V : Scheme.{u}} {p : V ⟶ C} {q : V ⟶ U}
    {h : U ⟶ Spec (.of k)} (hpb : IsPullback p q f h) : IsIso q.toLRSHom.toHom.c := by
  have hΓ := isIso_globalSections_of_geometricallyIntegral k f
  have hf : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have hc : IsIso f.toLRSHom.toHom.c :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop f).2
      (ConcreteCategory.bijective_of_isIso f.appTop)
  have hu : IsIso (Scheme.Modules.unitToPushforwardUnit f) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      f).1 hc
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
    q).2 (Stacks.AlgebraicGeometry.AffinePushforward.isIso_unitToPushforwardUnit_of_isPullback
      hpb hu)

/-- The section `T ⟶ C ×_k T` of the projection given by a `C`-point `c` of `T`. -/
@[expose] public noncomputable def pointSection (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) :
    T.left ⟶ bc f T :=
  pullback.lift (f := f) (g := T.hom) c.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w c)

omit [IsSmoothProjectiveCurve k f] in
/-- The point section is a section of the projection `C ×_k T ⟶ T`. -/
public theorem pointSection_bcProj (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) :
    pointSection f T c ≫ bcProj f T = 𝟙 _ :=
  pullback.lift_snd _ _ _

omit [IsSmoothProjectiveCurve k f] in
/-- The point section of `c`, followed by the projection to `C`, is `c`. -/
public theorem pointSection_fst (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) :
    pointSection f T c ≫ pullback.fst f T.hom = c.left :=
  pullback.lift_fst _ _ _

omit [IsSmoothProjectiveCurve k f] in
/-- The point section is compatible with the base change along `g : T ⟶ U`. -/
public theorem pointSection_bcMap {T U : Over (Spec (.of k))} (g : T ⟶ U) (c : U ⟶ Over.mk f) :
    pointSection f T (g ≫ c) ≫ bcMap f g = g.left ≫ pointSection f U c := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, pointSection_fst, Category.assoc, pointSection_fst,
      Over.comp_left]
  · rw [Category.assoc, bcMap_snd, ← Category.assoc, pointSection_bcProj, Category.id_comp,
      Category.assoc, pointSection_bcProj, Category.comp_id]

/-- **Classes pulled back from the base have degree zero.** -/
public theorem degree_bcProj (T : Over (Spec (.of k))) (n : smallOfScheme T.left) :
    degree f (topologicalKrullDim_fiber_le_one f) T
        (smallSchemePullbackClassHom (bcProj f T) n) = 0 := by
  funext t
  rw [degree_apply, smallEquiv_smallSchemePullbackClassHom, relativeInvertibleDegreeHomAt_apply,
    schemePullbackClass_comp, Scheme.Hom.fiber_fac, ← schemePullbackClass_comp,
    Stacks.Picard.eq_zero_of_subsingleton (schemePullbackClass (T.left.fromSpecResidueField t) _)]
  have h0 : schemePullbackClass (Scheme.Hom.fiberToSpecResidueField (bcProj f T) t) 0 = 0 :=
    (schemePullbackClassHom.{u} _).map_zero
  rw [h0, map_zero]
  rfl

/-- The class pulled back from the base, as a class of degree zero. -/
@[expose] public noncomputable def baseClass (T : Over (Spec (.of k))) (n : smallOfScheme T.left) :
    degreeZero f T :=
  ⟨smallSchemePullbackClassHom (bcProj f T) n, AddMonoidHom.mem_ker.2 (degree_bcProj f T n)⟩

/-- A class pulled back from the base lies in `baseClasses`. -/
public theorem baseClass_mem_baseClasses (T : Over (Spec (.of k))) (n : smallOfScheme T.left) :
    baseClass f T n ∈ baseClasses f T :=
  AddSubgroup.mem_addSubgroupOf.2 ⟨n, rfl⟩

/-- The rigidification of a class of degree zero along a `C`-point: subtract the pullback of its
restriction to the section. -/
@[expose] public noncomputable def rigidify (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f)
    (z : degreeZero f T) : degreeZero f T :=
  z - baseClass f T (smallSchemePullbackClassHom (pointSection f T c) z.1)

/-- A rigidified class restricts to zero along the point section. -/
public theorem pointSection_rigidify (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f)
    (z : degreeZero f T) :
    smallSchemePullbackClassHom (pointSection f T c) (rigidify f T c z).1 = 0 := by
  simp only [rigidify, baseClass, AddSubgroup.coe_sub, map_sub, smallSchemePullbackClassHom_comp,
    reassoc_of% pointSection_bcProj, sub_self]

/-- Rigidification does not change the class in `P⁰_C(T)`. -/
public theorem mk_rigidify (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) (z : degreeZero f T) :
    (QuotientAddGroup.mk (rigidify f T c z) : degreeZero f T ⧸ baseClasses f T) =
        QuotientAddGroup.mk z := by
  rw [QuotientAddGroup.eq]
  have : -rigidify f T c z + z =
      baseClass f T (smallSchemePullbackClassHom (pointSection f T c) z.1) := by
    simp only [rigidify]; abel
  rw [this]
  exact baseClass_mem_baseClasses f T _

/-- Two classes of degree zero with the same image in `P⁰_C(T)`, both trivial along the
point section of `c`, are equal. -/
public theorem eq_of_mk_eq_of_pointSection_eq_zero (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f)
    {z z' : degreeZero f T}
    (h : (QuotientAddGroup.mk z : degreeZero f T ⧸ baseClasses f T) = QuotientAddGroup.mk z')
    (hz : smallSchemePullbackClassHom (pointSection f T c) z.1 = 0)
    (hz' : smallSchemePullbackClassHom (pointSection f T c) z'.1 = 0) : z = z' := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_addSubgroupOf.1 h
  have hn0 : n = 0 := by
    have := congrArg (smallSchemePullbackClassHom (pointSection f T c)) hn
    rw [smallSchemePullbackClassHom_comp, pointSection_bcProj,
        smallSchemePullbackClassHom_id] at this
    rw [this]
    simp [hz, hz']
  rw [hn0, map_zero] at hn
  exact neg_add_eq_zero.1 (Subtype.ext hn.symm)

end PicZero

section RelBase

/-! ### `C ×_k T` as a curve over `T` -/

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (T : Over (Spec (.of k)))

open Stacks.RigidifiedPicard Stacks.Picard

/-- A `T`-scheme as a `k`-scheme. -/
@[expose] public noncomputable abbrev forgetBase (U : Over T.left) : Over (Spec (.of k)) :=
  Over.mk (U.hom ≫ T.hom)

/-- A morphism of `T`-schemes as a morphism of `k`-schemes. -/
@[expose] public noncomputable abbrev forgetBaseMap {V U : Over T.left} (a : V ⟶ U) :
    forgetBase T V ⟶ forgetBase T U :=
  Over.homMk a.left (by simp only [Over.mk_hom, ← Category.assoc, Over.w a])

/-- The `C`-point of a `T`-scheme induced by a `C`-point of `T`. -/
@[expose] public noncomputable abbrev forgetBasePoint (c : T ⟶ Over.mk f) (U : Over T.left) :
    forgetBase T U ⟶ Over.mk f :=
  Over.homMk (U.hom ≫ c.left) (by
    simp only [Over.mk_hom, Category.assoc]; rw [show c.left ≫ f = T.hom from Over.w c])

/-- `(C ×_k T) ×_T U ≅ C ×_k U`. -/
@[expose] public noncomputable abbrev bcForgetIso (U : Over T.left) :
    bc (bcProj f T) U ≅ bc f (forgetBase T U) :=
  pullbackLeftPullbackSndIso f T.hom U.hom

omit [IsSmoothProjectiveCurve k f] in
/-- `bcForgetIso` commutes with the projections to `C`. -/
@[reassoc]
public theorem bcForgetIso_hom_fst (U : Over T.left) :
    (bcForgetIso f T U).hom ≫ pullback.fst f (forgetBase T U).hom =
      pullback.fst (bcProj f T) U.hom ≫ pullback.fst f T.hom :=
  pullbackLeftPullbackSndIso_hom_fst f T.hom U.hom

omit [IsSmoothProjectiveCurve k f] in
/-- `bcForgetIso` commutes with the projections to `U`. -/
@[reassoc]
public theorem bcForgetIso_hom_snd (U : Over T.left) :
    (bcForgetIso f T U).hom ≫ pullback.snd f (forgetBase T U).hom =
      pullback.snd (bcProj f T) U.hom :=
  pullbackLeftPullbackSndIso_hom_snd f T.hom U.hom

omit [IsSmoothProjectiveCurve k f] in
/-- `bcForgetIso` is natural in the `T`-scheme `U`. -/
public theorem bcMap_bcForgetIso {V U : Over T.left} (a : V ⟶ U) :
    bcMap (bcProj f T) a ≫ (bcForgetIso f T U).hom =
      (bcForgetIso f T V).hom ≫ bcMap f (forgetBaseMap T a) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcForgetIso_hom_fst, bcMap_fst, bcMap_fst_assoc]
  · simp only [Category.assoc, bcForgetIso_hom_snd, bcMap_snd, bcForgetIso_hom_snd_assoc,
      Over.homMk_left]

omit [IsSmoothProjectiveCurve k f] in
/-- Under `bcForgetIso`, the base change to `U` of the point section of `c` is the point section
of the induced `C`-point of `U`. -/
public theorem bcSection_bcForgetIso (c : T ⟶ Over.mk f) (U : Over T.left) :
    bcSection (bcProj f T) (pointSection f T c) (pointSection_bcProj f T c) U ≫
        (bcForgetIso f T U).hom =
      pointSection f (forgetBase T U) (forgetBasePoint f T c U) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcForgetIso_hom_fst, bcSection_comp_fst_assoc, pointSection_fst,
      Over.homMk_left]
  · simp only [Category.assoc, bcForgetIso_hom_snd]
    exact (bcSection_comp_snd _ _ _ U).trans
        (pointSection_bcProj f (forgetBase T U) (forgetBasePoint f T c U)).symm

/-- The comparison of structure sheaves of `(C ×_k T) ×_T U ⟶ U` is an isomorphism. -/
public theorem isIso_c_bcProj_bcProj (U : Over T.left) :
    IsIso (bcProj (bcProj f T) U).toLRSHom.toHom.c :=
  isIso_c_of_isPullback f
    ((IsPullback.of_hasPullback (bcProj f T) U.hom).paste_horiz (IsPullback.of_hasPullback f T.hom))

end RelBase

section BaseCurve

/-! ### The curve `C_E` over a field extension `E` -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (E : Type u) [Field E] [Algebra k E]

open Stacks.RigidifiedPicard

/-- The structure morphism `C_E ⟶ Spec E`. -/
@[expose] public noncomputable abbrev curveOver : bc f (Over.mk (specMap k E)) ⟶ Spec (.of E) :=
  bcProj f (Over.mk (specMap k E))

/-- `C_E ⟶ Spec E` is smooth of relative dimension one. -/
public theorem smoothOfRelativeDimension_curveOver :
    SmoothOfRelativeDimension 1 (curveOver k f E) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback f _) inferInstance

/-- `C_E ⟶ Spec E` is proper. -/
public theorem isProper_curveOver : IsProper (curveOver k f E) :=
  MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback f _) inferInstance

/-- `C_E ⟶ Spec E` is geometrically integral. -/
public theorem geometricallyIntegral_curveOver : GeometricallyIntegral (curveOver k f E) :=
  MorphismProperty.of_isPullback (P := @GeometricallyIntegral) (IsPullback.of_hasPullback f _)
    inferInstance

/-- `C_E ⟶ Spec E` is smooth. -/
public theorem smooth_curveOver : Smooth (curveOver k f E) :=
  have := smoothOfRelativeDimension_curveOver k f E
  SmoothOfRelativeDimension.smooth 1 _

/-- `C_E ⟶ Spec E` is geometrically irreducible. -/
public theorem geometricallyIrreducible_curveOver : GeometricallyIrreducible (curveOver k f E) :=
  have := geometricallyIntegral_curveOver k f E
  inferInstance

/-- `C_E` is a curve over `E`. -/
public theorem isCurve_curveOver : IsCurve E (curveOver k f E) :=
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _

/-- `C_E` has dimension at most one. -/
public theorem topologicalKrullDim_curveOver :
    topologicalKrullDim (bc f (Over.mk (specMap k E)) : Scheme.{u}) ≤ 1 :=
  have := isCurve_curveOver k f E
  (IsCurve.topologicalKrullDim_eq_one (k := E) (f := curveOver k f E)).le

/-- `C_E ⟶ Spec E` is projective. -/
public theorem isProjectiveMorphism_curveOver : IsProjectiveMorphism (curveOver k f E) :=
  have := isCurve_curveOver k f E
  have := isProper_curveOver k f E
  Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
    _ (topologicalKrullDim_curveOver k f E)

end BaseCurve

section PointedTransport

/-! ### The rigidified `Pic⁰` of `C_E` at a point of `C_E` as Faltings' `P⁰_C` -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (E : Type u) [Field E] [Algebra k E]
  (c₀ : Over.mk (specMap k E) ⟶ Over.mk f)

open Stacks.RigidifiedPicard Stacks.Picard

/-- The fibres of `C_E ⟶ Spec E` have dimension at most one. -/
public theorem topologicalKrullDim_fiber_curveOver_le_one :
    ∀ s, topologicalKrullDim ↥((curveOver k f E).fiber s) ≤ 1 :=
  topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) (Over.mk (specMap k E))

/-- Carrying a class of `C_E ×_E U` to `C ×_k U` along `bcForgetIso` preserves its fibrewise
degree. -/
public theorem degree_bcForgetIso_inv (U : Over (Spec (.of E)))
    (y : smallOfScheme (bc (curveOver k f E) U)) :
    degree f (topologicalKrullDim_fiber_le_one f) (forgetBase (Over.mk (specMap k E)) U)
        (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv y) =
      degree (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E) U y := by
  have := isProper_curveOver k f E
  have hsq : IsPullback (bcForgetIso f (Over.mk (specMap k E)) U).inv
      (bcProj f (forgetBase (Over.mk (specMap k E)) U)) (bcProj (curveOver k f E) U) (𝟙 U.left) :=
    haveI : IsIso (𝟙 U.left) := IsIso.id _
    IsPullback.of_horiz_isIso ⟨by erw [Category.comp_id]; rw [Iso.inv_comp_eq, bcForgetIso_hom_snd]⟩
  simp only [degree, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    smallEquiv_smallSchemePullbackClassHom]
  rw [relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback hsq]
  rfl

/-- The rigidified `Pic⁰` of `C_E` at the section of the point `c₀`, as a functor to groups. -/
@[expose] public noncomputable abbrev rigidified : (Over (Spec (.of E)))ᵒᵖ ⥤ GrpCat.{u} :=
  functorZero (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
    (pointSection f (Over.mk (specMap k E)) c₀) (pointSection_bcProj f _ c₀)

omit [IsSmoothProjectiveCurve k f] in
/-- The inverse of `bcForgetIso` is natural in the `E`-scheme `U`. -/
public theorem bcForgetIso_inv_bcMap {U' U : Over (Spec (.of E))} (g : U' ⟶ U) :
    (bcForgetIso f (Over.mk (specMap k E)) U').inv ≫ bcMap (curveOver k f E) g =
      bcMap f ((Over.map (specMap k E)).map g) ≫ (bcForgetIso f (Over.mk (specMap k E)) U).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact bcMap_bcForgetIso f (Over.mk (specMap k E)) g

omit [IsSmoothProjectiveCurve k f] in
/-- Restricting along the point section commutes with carrying a class from `C_E ×_E U` to
`C ×_k U`. -/
public theorem pointSection_bcForgetIso_inv (U : Over (Spec (.of E)))
    (y : smallOfScheme (bc (curveOver k f E) U)) :
    smallSchemePullbackClassHom
        (pointSection f (forgetBase (Over.mk (specMap k E)) U)
            (forgetBasePoint f (Over.mk (specMap k E)) c₀ U))
        (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv y) =
      smallSchemePullbackClassHom (bcSection (curveOver k f E) (pointSection f _ c₀)
        (pointSection_bcProj f _ c₀) U) y := by
  rw [← bcSection_bcForgetIso, smallSchemePullbackClassHom_comp, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The comparison of the rigidified `Pic⁰` of `C_E` with `P⁰_C` at an `E`-scheme `U`: a
rigidified class on `C_E ×_E U` is carried to `C ×_k U` along `bcForgetIso` and taken modulo the
classes pulled back from `U`. -/
@[expose] public noncomputable def rigidifiedToFun (U : Over (Spec (.of E)))
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) :
    (relativePicZeroFunctor k f ⋙ forget AddCommGrpCat).obj
      (op ((Over.map (specMap k E)).obj U)) :=
  (QuotientAddGroup.mk (⟨smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv
      (Multiplicative.toAdd x).1.1, by
        rw [AddMonoidHom.mem_ker, degree_bcForgetIso_inv]
        exact funext ((mem_groupZero_iff _ _ _ _ _ _).1 (Multiplicative.toAdd x).2)⟩ :
      degreeZero f _) : degreeZero f _ ⧸ baseClasses f _)

/-- The comparison `rigidifiedToFun` is injective. -/
public theorem rigidifiedToFun_injective (U : Over (Spec (.of E))) :
    Function.Injective (rigidifiedToFun k f E c₀ U) := by
  have hrig : ∀ x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U),
      smallSchemePullbackClassHom
        (pointSection f (forgetBase (Over.mk (specMap k E)) U)
            (forgetBasePoint f (Over.mk (specMap k E)) c₀ U))
        (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv
          (Multiplicative.toAdd x).1.1) = 0 := fun x => by
    rw [pointSection_bcForgetIso_inv]
    exact (Multiplicative.toAdd x).1.2
  intro x x' h
  have h' := eq_of_mk_eq_of_pointSection_eq_zero f _
    (forgetBasePoint f (Over.mk (specMap k E)) c₀ U) h (hrig x)
    (hrig x')
  have h'' := congrArg Subtype.val h'
  have hinj : Function.Injective
      (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv) := by
    intro a b hab
    have := congrArg (smallSchemePullbackClassHom
        (bcForgetIso f (Over.mk (specMap k E)) U).hom) hab
    rwa [smallSchemePullbackClassHom_comp, smallSchemePullbackClassHom_comp, Iso.hom_inv_id,
      smallSchemePullbackClassHom_id, smallSchemePullbackClassHom_id] at this
  exact Multiplicative.toAdd.injective (Subtype.ext (Subtype.ext (hinj h'')))

/-- The comparison `rigidifiedToFun` is surjective. -/
public theorem rigidifiedToFun_surjective (U : Over (Spec (.of E))) :
    Function.Surjective (rigidifiedToFun k f E c₀ U) := by
  intro y
  induction y using QuotientAddGroup.induction_on with | H z => ?_
  set zr := rigidify f _ (forgetBasePoint f (Over.mk (specMap k E)) c₀ U) z
  have hzr := pointSection_rigidify f _ (forgetBasePoint f (Over.mk (specMap k E)) c₀ U) z
  set y₀ := smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).hom zr.1
  have hy₀ : smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv
      y₀ = zr.1 := by
    rw [smallSchemePullbackClassHom_comp, Iso.inv_hom_id, smallSchemePullbackClassHom_id]
  have hgrp : y₀ ∈ group (curveOver k f E) (pointSection f _ c₀)
      (pointSection_bcProj f _ c₀) U := by
    rw [group, AddMonoidHom.mem_ker, ← pointSection_bcForgetIso_inv, hy₀]
    exact hzr
  have hdeg : (⟨y₀, hgrp⟩ : group _ _ _ U) ∈ groupZero (curveOver k f E)
      (topologicalKrullDim_fiber_curveOver_le_one k f E)
      (pointSection f _ c₀) (pointSection_bcProj f _ c₀) U := by
    rw [mem_groupZero_iff]
    intro t
    have := degree_bcForgetIso_inv k f E U y₀
    rw [hy₀, AddMonoidHom.mem_ker.1 zr.2] at this
    exact (congrFun this t).symm
  let x₀ : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U) :=
    Multiplicative.ofAdd (⟨⟨y₀, hgrp⟩, hdeg⟩ : groupZero (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E)
      (pointSection f _ c₀) (pointSection_bcProj f _ c₀) U)
  refine ⟨x₀, ?_⟩
  have h1 : (⟨smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv y₀,
      by rw [hy₀]; exact zr.2⟩ : degreeZero f (forgetBase (Over.mk (specMap k E)) U)) = zr :=
          Subtype.ext hy₀
  exact (congrArg (QuotientAddGroup.mk (s := baseClasses f _)) h1).trans (mk_rigidify f _ _ z)

/-- The comparison `rigidifiedToFun` is bijective. -/
public theorem rigidifiedToFun_bijective (U : Over (Spec (.of E))) :
    Function.Bijective (rigidifiedToFun k f E c₀ U) :=
  ⟨rigidifiedToFun_injective k f E c₀ U, rigidifiedToFun_surjective k f E c₀ U⟩

/-- **The rigidified `Pic⁰` of `C_E` is Faltings' `P⁰_C` on `E`-schemes.** -/
@[expose] public noncomputable def rigidifiedIso :
    rigidified k f E c₀ ⋙ forget GrpCat ≅
      (Over.map (specMap k E)).op ⋙ relativePicZeroFunctor k f ⋙ forget AddCommGrpCat :=
  NatIso.ofComponents
    (fun U => (Equiv.ofBijective _ (rigidifiedToFun_bijective k f E c₀ U.unop)).toIso)
    (fun {U U'} g => by
      ext x
      change rigidifiedToFun k f E c₀ U'.unop ((rigidified k f E c₀ ⋙ forget GrpCat).map g x) =
        (relativePicZeroFunctor k f ⋙ forget AddCommGrpCat).map
          ((Over.map (specMap k E)).map g.unop).op (rigidifiedToFun k f E c₀ U.unop x)
      rw [rigidifiedToFun, rigidifiedToFun, map_mk]
      congr 1
      apply Subtype.ext
      change smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U'.unop).inv
          (smallSchemePullbackClassHom (bcMap (curveOver k f E) g.unop)
            (Multiplicative.toAdd x).1.1) =
        smallSchemePullbackClassHom (bcMap f ((Over.map (specMap k E)).map g.unop))
          (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U.unop).inv
            (Multiplicative.toAdd x).1.1)
      rw [smallSchemePullbackClassHom_comp, smallSchemePullbackClassHom_comp,
          bcForgetIso_inv_bcMap])

/-- The components of `rigidifiedIso` are `rigidifiedToFun`. -/
public theorem rigidifiedIso_hom_app (U : (Over (Spec (.of E)))ᵒᵖ)
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj U) :
    (rigidifiedIso k f E c₀).hom.app U x = rigidifiedToFun k f E c₀ U.unop x :=
  rfl

end PointedTransport

end relativePicZeroFunctor

end Faltings
