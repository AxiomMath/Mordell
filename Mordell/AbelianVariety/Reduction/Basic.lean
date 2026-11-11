module

public import Mathlib
public import Mordell.Attr

/-!
# The reduction map of an abelian scheme over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `L` and residue field `κ(s)` at the
closed point `s` of `Spec R`, and let `𝒜` be an abelian scheme over `R` with generic fibre
`A = 𝒜 ×_R Spec L`. By the universal property of the fibre product, an `L`-point of `A` over
`Spec L` is the same as an `L`-point of `𝒜` over `Spec R`. For `P ∈ A(L)` choose a section
`P̃ ∈ 𝒜(R)` restricting to `P` on the generic point, if there is one, and take the unit section
otherwise. The *reduction* of `P` is the restriction of `P̃` to the closed point,
`red P = P̃ ∘ (Spec κ(s) → Spec R) ∈ 𝒜(κ(s))`.

## Main definitions

* `Faltings.reductionMap`: the reduction map `A(L) → 𝒜(κ(s))`.

## Implementation notes

A group scheme over `W = Spec R` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over W)`,
and for `T` over `W` its `T`-points are the morphisms `T ⟶ 𝒜.X` in `Over W`. The `R`-points are
the morphisms from the terminal object `𝟙_ (Over W)`, and the unit section is `η[𝒜.X]`.
The generic fibre is `(Over.pullback (Spec.map (algebraMap R L))).obj 𝒜.X`, and its `L`-points
are the morphisms `𝟙_ (Over (Spec L)) ⟶ A`. The identification `A(L) = 𝒜(L)` is the adjunction
`CategoryTheory.Over.mapPullbackAdj`, so a point of `A(L)` becomes a morphism over `W` from
`Spec L` to `𝒜`. Restriction of a section along `T → W` is precomposition with
`CategoryTheory.CartesianMonoidalCategory.toUnit T`.
Being an abelian scheme is spelled out as in `Faltings.HasGoodReduction`: the structure morphism
is flat, proper and locally of finite presentation, and every fibre over
`AlgebraicGeometry.Scheme.fromSpecResidueField` is proper and geometrically integral.

## References

* [J. H. Silverman, *The arithmetic of elliptic curves*][silvermanAEC], §VII.2
* [J. S. Milne, *Abelian varieties*][milneAV], proof of Theorem IV.3.5
* [The Stacks Project][stacks], Tag 0BX5
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

/-- The *reduction map* `A(L) → 𝒜(κ(s))` of an abelian scheme `𝒜` over a discrete valuation ring
`R` with fraction field `L`, where `A` is the generic fibre: a point `P ∈ A(L)`, viewed as an
`L`-point of `𝒜` over `R`, is sent to `P̃ ∘ (Spec κ(s) → Spec R)`, where `P̃ ∈ 𝒜(R)` is a chosen
section restricting to `P` on `Spec L` if one exists, and the unit section otherwise. -/
@[faltings "def_mw_reduction_map"]
noncomputable def reductionMap (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (_hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj 𝒜.X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ⟶ 𝒜.X :=
  open Classical in
  toUnit _ ≫
    if h : ∃ Q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X,
        toUnit _ ≫ Q = ((Over.mapPullbackAdj
          (Spec.map (CommRingCat.ofHom (algebraMap R L)))).homEquiv _ _).symm P
    then h.choose else η[𝒜.X]

end Faltings


/-!
# Points of an abelian scheme over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `L` and `𝒜` an abelian scheme over
`Spec R`. An `R`-point of `𝒜` is a section `Spec R ⟶ 𝒜` of the structure morphism, and an
`L`-point is a morphism `Spec L ⟶ 𝒜` over `Spec R`. Precomposition with `Spec L ⟶ Spec R`
sends `R`-points to `L`-points. Since `𝒜 → Spec R` is proper, the valuative criterion of
properness says every `L`-point extends uniquely to an `R`-point, so restriction is bijective;
it is a group homomorphism because the group laws on points are postcomposition with the group
structure maps of `𝒜`. Hence restriction is a group isomorphism `𝒜(R) ≃* 𝒜(L)`.

## Main results

* `Faltings.exists_mulEquiv_points_fractionRing`: restriction to the generic point is a group
  isomorphism from the `R`-points to the `L`-points of an abelian scheme over a discrete
  valuation ring `R` with fraction field `L`.

## Implementation notes

A group scheme over `Spec R` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over (Spec R))`;
its `T`-points for `T` over `Spec R` are the morphisms `T ⟶ 𝒜.X` in `Over (Spec R)`, with the
group structure Mathlib puts on morphisms into a group object. Being an abelian scheme is spelled
out as flatness, properness and local finite presentation of the structure morphism, together
with every fibre over `AlgebraicGeometry.Scheme.fromSpecResidueField` being proper and
geometrically integral. The restriction map is pinned by its underlying morphism of schemes,
`(e P).left = Spec.map (algebraMap R L) ≫ P.left`.

## References

* [The Stacks Project][stacks], Tag 0BX5
* [J. S. Milne, *Abelian Varieties*][milneAV], IV.3.5
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace Faltings

/-- The valuative criterion as a statement about points: if `X ⟶ Spec R` satisfies the
valuative criterion and `L` is the fraction field of the valuation ring `R`, then restricting
sections `Spec R ⟶ X` along `Spec L ⟶ Spec R` is a bijection onto the `L`-points of `X`. -/
private lemma bijective_restrict_of_valuativeCriterion (R L : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (X : Over (Spec (CommRingCat.of R))) (hV : ValuativeCriterion X.hom) :
    Function.Bijective fun P : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X ↦
      (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R L))) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ P := by
  set iL := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have hw (P : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ X) : P.left ≫ X.hom = 𝟙 _ := Over.w P
  refine ⟨fun P P' h ↦ ?_, fun Q ↦ ?_⟩
  · let S : ValuativeCommSq X.hom := ⟨R, L, iL ≫ P.left, 𝟙 _,
      ⟨by rw [Category.assoc, hw P]; exact Category.comp_id _⟩⟩
    have := (hV S).some.instSubsingleton
    have h' : iL ≫ P.left = iL ≫ P'.left := congrArg CommaMorphism.left h
    exact Over.OverMorphism.ext <| congrArg CommSq.LiftStruct.l <|
      Subsingleton.elim (α := S.commSq.LiftStruct) ⟨P.left, rfl, hw P⟩ ⟨P'.left, h'.symm, hw P'⟩
  · let S : ValuativeCommSq X.hom :=
      ⟨R, L, Q.left, 𝟙 _, ⟨(Over.w Q).trans (Category.comp_id _).symm⟩⟩
    let l : S.commSq.LiftStruct := (hV S).some.default
    exact ⟨Over.homMk l.l (by simpa using l.fac_right), Over.OverMorphism.ext l.fac_left⟩

/-- Let `R` be a discrete valuation ring with fraction field `L` and `𝒜` an abelian scheme over
`Spec R` (a group scheme whose structure morphism is flat, proper and locally of finite
presentation, with all fibres proper and geometrically integral). Then restriction along
`Spec L ⟶ Spec R`, sending a section `P` to `Spec.map (algebraMap R L) ≫ P.left`, is a group
isomorphism from the `R`-points of `𝒜` to its `L`-points. -/
@[faltings "lem_mw_points_extend_uniquely"]
theorem exists_mulEquiv_points_fractionRing (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback ((Spec (CommRingCat.of R)).fromSpecResidueField w)).obj
        𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback
        ((Spec (CommRingCat.of R)).fromSpecResidueField w)).obj 𝒜.X).hom) :
    ∃ e : (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ 𝒜.X) ≃*
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ 𝒜.X),
      ∀ P, (e P).left = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ P.left := by
  have hP := ‹IsProper 𝒜.X.hom›
  rw [IsProper.eq_valuativeCriterion] at hP
  let j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R L))) (by simp)
  let φ : (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ 𝒜.X) →* (_ ⟶ 𝒜.X) :=
    { toFun := (j ≫ ·)
      map_one' := MonObj.comp_one j
      map_mul' := MonObj.comp_mul j }
  exact ⟨.ofBijective φ (bijective_restrict_of_valuativeCriterion R L 𝒜.X hP.1.1.1),
    fun _ ↦ rfl⟩

end Faltings


/-!
# The reduction map is a group homomorphism

Let `R` be a discrete valuation ring with fraction field `L` and residue field `κ(s)`, and let
`𝒜` be an abelian scheme over `R` with generic fibre `A`. The reduction map
`Faltings.reductionMap : A(L) → 𝒜(κ(s))` is a group homomorphism: every point of `A(L)` extends
uniquely to a section in `𝒜(R)`, extension is inverse to the group isomorphism `𝒜(R) → 𝒜(L)`,
and restriction to the closed point commutes with the group laws, which are given by
postcomposition with the group structure maps.

## Main definitions

* `Faltings.mapPullbackAdjMulEquiv`: for a group object `G` over `Y` and `f : X ⟶ Y`, the
  `T`-points of `G` and of its base change along `f` are isomorphic groups.

## Main results

* `Faltings.existsUnique_extension`: every point of `𝒜(L)` extends uniquely to `𝒜(R)`.
* `Faltings.reductionMap_eq_of_extension`: `red P` is the restriction to the closed point of any
  section `Q ∈ 𝒜(R)` extending `P`; this characterises `Faltings.reductionMap`.
* `Faltings.reductionMap_mul`: `red (P * Q) = red P * red Q`.

## Implementation notes

The group structure on the generic fibre `(Over.pullback (Spec.map (algebraMap R L))).obj 𝒜.X`
is the one transported by the pullback functor, `(Over.pullback _).mapGrp.obj 𝒜`, whose
underlying object is the generic fibre by definition. The group structure on
`𝒜(κ(s)) = (Over.mk (Spec κ(s) → Spec R) ⟶ 𝒜.X)` is that of the points of the group object `𝒜`.

## References

* [J. H. Silverman, *The arithmetic of elliptic curves*][silvermanAEC], §VII.2
* [J. S. Milne, *Abelian varieties*][milneAV], proof of Theorem IV.3.5
* [The Stacks Project][stacks], Tag 0BX5
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

/-- Base change along `f` identifies `T`-points of a group object `G` over `Y` with `T`-points
of its base change, as groups: the hom-equivalence of `Over.mapPullbackAdj f` is multiplicative. -/
noncomputable def mapPullbackAdjMulEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Grp (Over Y))
    (T : Over X) :
    ((Over.map f).obj T ⟶ G.X) ≃* (T ⟶ ((Over.pullback f).mapGrp.obj G).X) where
  __ := (Over.mapPullbackAdj f).homEquiv _ _
  map_mul' g h := by
    simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_mul]
    exact MonObj.comp_mul (M := ((Over.pullback f).mapGrp.obj G).X) _ _ _

/-- The inverse of `Faltings.mapPullbackAdjMulEquiv` composes a point of the base change with the
first projection `X ×_Y G → G`. -/
@[simp]
lemma mapPullbackAdjMulEquiv_symm_left {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Grp (Over Y))
    (T : Over X) (P : T ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    ((mapPullbackAdjMulEquiv f G T).symm P).left = P.left ≫ pullback.fst G.X.hom f := by
  change (((Over.mapPullbackAdj f).homEquiv _ _).symm P).left = _
  erw [Adjunction.homEquiv_counit]
  simp only [Over.comp_left, Over.mapPullbackAdj_counit_app, Over.homMk_left]
  rfl

/-- Every `L`-point of an abelian scheme `𝒜` over `R` extends uniquely to an `R`-point of `𝒜`. -/
theorem existsUnique_extension (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (P : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj
      (𝟙_ (Over (Spec (CommRingCat.of L)))) ⟶ 𝒜.X) :
    ∃! Q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X, toUnit _ ≫ Q = P := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points_fractionRing R L 𝒜 hfib
  refine ⟨e.symm (Over.homMk P.left (by simp)), ?_, fun Q hQ ↦ e.injective ?_⟩
  · ext1
    have h := he (e.symm (Over.homMk P.left (by simp)))
    rw [MulEquiv.apply_symm_apply] at h
    simp only [Over.homMk_left] at h
    conv_rhs => rw [h]
    simp
  · ext1
    simpa [he] using congrArg CommaMorphism.left hQ

/-- The reduction of an `L`-point `P` is the restriction to the closed point of any `R`-point `Q`
extending `P`. -/
theorem reductionMap_eq_of_extension (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    {P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj 𝒜.X}
    {Q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X}
    (hQ : toUnit _ ≫ Q = ((Over.mapPullbackAdj
      (Spec.map (CommRingCat.ofHom (algebraMap R L)))).homEquiv _ _).symm P) :
    reductionMap R L 𝒜 hfib P = toUnit _ ≫ Q := by
  unfold reductionMap
  split_ifs with h
  · rw [(existsUnique_extension R L 𝒜 hfib _).unique h.choose_spec hQ]
  · exact (h ⟨Q, hQ⟩).elim

/-- The reduction map `Faltings.reductionMap` of an abelian scheme `𝒜` over a discrete valuation
ring `R` with fraction field `L` is a group homomorphism from the `L`-points of the generic fibre
to the `κ(s)`-points of `𝒜`: `red (P * Q) = red P * red Q`. -/
@[faltings "lem_mw_reduction_map"]
theorem reductionMap_mul (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (P Q : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj 𝒜).X) :
    reductionMap R L 𝒜 hfib (P * Q) = reductionMap R L 𝒜 hfib P * reductionMap R L 𝒜 hfib Q := by
  set Φ := (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R L)))).homEquiv
    (𝟙_ (Over (Spec (CommRingCat.of L)))) 𝒜.X
  obtain ⟨P', hP', -⟩ := existsUnique_extension R L 𝒜 hfib (Φ.symm P)
  obtain ⟨Q', hQ', -⟩ := existsUnique_extension R L 𝒜 hfib (Φ.symm Q)
  rw [reductionMap_eq_of_extension R L 𝒜 hfib hP', reductionMap_eq_of_extension R L 𝒜 hfib hQ',
    reductionMap_eq_of_extension R L 𝒜 hfib (P := P * Q) (Q := P' * Q')
      (by rw [MonObj.comp_mul, hP', hQ']
          exact (map_mul (mapPullbackAdjMulEquiv _ 𝒜 _).symm P Q).symm), MonObj.comp_mul]

end Faltings
