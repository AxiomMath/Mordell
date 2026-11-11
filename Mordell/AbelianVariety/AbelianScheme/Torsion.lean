module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion

/-!
# Base change of the `n`-torsion of an abelian scheme

Let `𝒜` be an abelian scheme over a scheme `W` and `n ∈ ℤ`. The `n`-torsion subscheme `𝒜[n]` is
the fibre product `𝒜 ×_{[n], 𝒜, e} W` of multiplication by `n` and the unit section. For a
morphism of schemes `g : W' ⟶ W`, multiplication by `n` and the unit section of
`𝒜_{W'} = 𝒜 ×_W W'` are the base changes of those of `𝒜`, and fibre products commute with base
change, so `(𝒜 ×_W W')[n] = 𝒜[n] ×_W W'`: the base change of the inclusion `𝒜[n] → 𝒜` exhibits
`𝒜[n] ×_W W'` as the `n`-torsion subscheme of `𝒜 ×_W W'`.

## Main results

* `Faltings.isPullback_pullbackMap_torsion`: the base change of the `n`-torsion of an abelian
  scheme is the `n`-torsion of the base change.

## Implementation notes

A group scheme over `W` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over W)`; its base
change along `g` is `(CategoryTheory.Over.pullback g).mapGrp.obj 𝒜`, with the group structure
carried along by the monoidal functor `Over.pullback g`. Multiplication by `n` is
`𝟙 𝒜.X ^ n` in the group `𝒜.X ⟶ 𝒜.X` of endomorphisms, and the unit section is `η[𝒜.X]`, a
morphism from the terminal object `𝟙_ (Over W)`, which is `W` over itself. The `n`-torsion is the
pullback `CategoryTheory.Limits.pullback (𝟙 𝒜.X ^ n) η[𝒜.X]` in `Over W`. The equality
`(𝒜 ×_W W')[n] = 𝒜[n] ×_W W'` is stated as a `CategoryTheory.IsPullback` square: the base change
of the inclusion `𝒜[n] → 𝒜`, together with the structure morphism of `𝒜[n] ×_W W'`, is a
pullback of multiplication by `n` and the unit section of `𝒜 ×_W W'`. This identifies the two
subschemes of `𝒜 ×_W W'` through the canonical maps, not just up to an abstract isomorphism.
Being an abelian scheme is spelled out as in `Faltings.isAbelianScheme_pullbackObj`.

## References

* [The Stacks Project][stacks], Tag 03RO
* [D. Mumford, *Geometric Invariant Theory*][mumfordGIT], Definition 6.1
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

/-- A monoidal functor between cartesian monoidal categories commutes with the `n`-th power of
the identity of a group object: `F [n]_G = [n]_{F G}`. -/
private lemma map_id_zpow {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (G : Grp C) (n : ℤ) :
    F.map (𝟙 G.X ^ n) = 𝟙 (F.mapGrp.obj G).X ^ n :=
  (map_zpow (H := (F.mapGrp.obj G).X ⟶ (F.mapGrp.obj G).X) F.homMonoidHom (𝟙 G.X) n).trans
    (congrArg (· ^ n) (F.map_id G.X))

/-- Let `𝒜` be an abelian scheme over `W`, `g : W' ⟶ W` a morphism of schemes and `n ∈ ℤ`. Then
the base change along `g` of the inclusion of the `n`-torsion `𝒜[n] = 𝒜 ×_{[n], 𝒜, e} W`
exhibits `𝒜[n] ×_W W'` as the `n`-torsion of `𝒜 ×_W W'`: the square formed with multiplication
by `n` and the unit section of `𝒜 ×_W W'` is a pullback. -/
@[faltings "lem_mw_torsion_subscheme_base_change"]
theorem isPullback_pullbackMap_torsion {W W' : Scheme.{u}} (g : W' ⟶ W) (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom)
    (n : ℤ) :
    IsPullback ((Over.pullback g).map (pullback.fst (𝟙 𝒜.X ^ n) η[𝒜.X]))
      (toUnit ((Over.pullback g).obj (pullback (𝟙 𝒜.X ^ n) η[𝒜.X])))
      (𝟙 ((Over.pullback g).mapGrp.obj 𝒜).X ^ n) η[((Over.pullback g).mapGrp.obj 𝒜).X] := by
  refine ((IsPullback.of_hasPullback _ _).map (Over.pullback g)).of_iso (Iso.refl _) (Iso.refl _)
    (Functor.Monoidal.εIso (Over.pullback g)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) ?_
    (by simp [Functor.mapGrp])
  simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact map_id_zpow (Over.pullback g) 𝒜 n

end Faltings


/-!
# The `n`-torsion of an abelian scheme is separated and locally of finite type

Let `𝒜` be an abelian scheme over a scheme `W` and `n ≥ 1`. The `n`-torsion subscheme `𝒜[n]` is
the fibre product `𝒜 ×_{[n], 𝒜, e} W` of multiplication by `n` and the unit section. Since
`𝒜 → W` is proper, it is separated, so the unit section `e : W → 𝒜` is a closed immersion; its
base change `𝒜[n] → 𝒜` is then a closed immersion, and the composite `𝒜[n] → 𝒜 → W` is separated
and locally of finite type.

## Main results

* `Faltings.isSeparated_and_locallyOfFiniteType_torsion`: the structure morphism of the
  `n`-torsion of an abelian scheme is separated and locally of finite type.

## Implementation notes

A group scheme over `W` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over W)`.
Multiplication by `n` is `𝟙 𝒜.X ^ n` in the group `𝒜.X ⟶ 𝒜.X` of endomorphisms, the unit
section is `η[𝒜.X]`, and the `n`-torsion is the pullback
`CategoryTheory.Limits.pullback (𝟙 𝒜.X ^ n) η[𝒜.X]` in `Over W`, exactly as in
`Faltings.isPullback_pullbackMap_torsion`. Being an abelian scheme is spelled out as in
`Faltings.isAbelianScheme_pullbackObj`.

## References

* [The Stacks Project][stacks], Tags 01KM, 024T, 03RO
* [J. S. Milne, *Abelian Varieties*][milneAV], I.7.2
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

/-- The unit section of a monoid scheme over `W` with separated structure morphism is a closed
immersion: it is a section of a separated morphism. -/
private lemma isClosedImmersion_eta_left {W : Scheme.{u}} (G : Over W) [MonObj G]
    [IsSeparated G.hom] : IsClosedImmersion η[G].left :=
  have : IsClosedImmersion (η[G].left ≫ G.hom) := by rw [Over.w]; dsimp; infer_instance
  .of_comp _ G.hom

/-- Let `𝒜` be an abelian scheme over `W` and `n ≥ 1`. Then the structure morphism
`𝒜[n] → W` of the `n`-torsion `𝒜[n] = 𝒜 ×_{[n], 𝒜, e} W` is separated and locally of finite
type. -/
@[faltings "lem_mw_torsion_scheme_separated"]
theorem isSeparated_and_locallyOfFiniteType_torsion {W : Scheme.{u}} (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom)
    (n : ℤ) (hn : 0 < n) :
    IsSeparated (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom ∧
      LocallyOfFiniteType (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom := by
  have : IsClosedImmersion (pullback.fst (𝟙 𝒜.X ^ n) η[𝒜.X]).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback _ _).map (Over.forget W)).flip
      (isClosedImmersion_eta_left 𝒜.X)
  rw [← Over.w (pullback.fst _ _)]
  exact ⟨inferInstance, inferInstance⟩

end Faltings


/-!
# The `n`-torsion of an abelian scheme is unramified when `n` is invertible

Let `𝒜` be an abelian scheme over a scheme `W` and `n ≥ 1` an integer which is a unit in
`Γ(W, 𝒪_W)`. The `n`-torsion subscheme `𝒜[n] = 𝒜 ×_{[n], 𝒜, e} W` is then unramified over `W`:
its structure morphism is locally of finite type and formally unramified.

The structure morphism is locally of finite type by
`Faltings.isSeparated_and_locallyOfFiniteType_torsion`. Its fibre over a point `w` is the
`n`-torsion of the abelian variety `𝒜_w` over `κ(w)`, a base change of multiplication by `n` on
`𝒜_w`, which is étale because `n ∈ κ(w)ˣ` (Stacks, Tag 0BFH). An étale morphism is unramified,
and unramifiedness of a morphism locally of finite type is detected on fibres (Stacks, Tag 0475).

## Main results

* `Faltings.locallyOfFiniteType_and_formallyUnramified_torsion`: for `n` invertible on `W`, the
  structure morphism `𝒜[n] → W` is locally of finite type and formally unramified.

## Implementation notes

A group scheme over `W` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over W)`.
Multiplication by `n` is `𝟙 𝒜.X ^ n` in the group `𝒜.X ⟶ 𝒜.X`, the unit section is `η[𝒜.X]`,
and the `n`-torsion is the pullback `CategoryTheory.Limits.pullback (𝟙 𝒜.X ^ n) η[𝒜.X]` in
`Over W`, whose structure morphism to `W` is its `hom`; this is the same object as in
`Faltings.isPullback_pullbackMap_torsion`, which identifies its fibre over `w` with the
`n`-torsion of `𝒜_w`. Mathlib has no single predicate for an unramified morphism of schemes;
following [Stacks, Tag 02G3] and [EGA IV₄, 17.3.1] it is the conjunction of
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.FormallyUnramified`. "Invertible on
`W`" is `IsUnit` of the image of `n` in the global sections `Γ(W, ⊤)`. Being an abelian scheme is
spelled out as in `Faltings.isAbelianScheme_pullbackObj`.

## References

* [The Stacks Project][stacks], Tags 02G3, 02G8, 03RO, 0475, 0BFH
* [D. Mumford, *Abelian Varieties*][mumfordAV]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

open MonoidalCategory in
/-- The fibre of the `n`-torsion of an abelian scheme over a point `w` is étale over `κ(w)`
when `n` is invertible on the base. -/
private lemma etale_fiberToSpecResidueField_torsion {W : Scheme.{u}} (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom)
    (n : ℤ) (hn : IsUnit (n : Γ(W, ⊤))) (w : W) :
    Etale ((pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom.fiberToSpecResidueField w) := by
  let g := W.fromSpecResidueField w
  let A : Over (Spec (.of (W.residueField w))) := ((Over.pullback g).mapGrp.obj 𝒜).X
  let : GrpObj A := ((Over.pullback g).mapGrp.obj 𝒜).grp
  obtain ⟨hP, hG⟩ := hfib w
  have : IsProper A.hom := hP
  have : GeometricallyIntegral A.hom := hG
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety _ A.hom := .mk (toIsVariety := .mk)
  have : IsAbelianVariety _ A := ⟨⟩
  have hu : IsUnit ((n : ℤ) : W.residueField w) := by
    simpa using hn.map (W.presheaf.germ ⊤ w trivial ≫ W.residue w).hom
  have := Stacks.Groupoids.etale_zpow_id_of_isUnit _ A n hu
  have sq := (isPullback_pullbackMap_torsion g 𝒜 hfib n).map (Over.forget _)
  have : Etale ((toUnit ((Over.pullback g).obj (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]))).left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq this
  change Etale ((Over.pullback g).obj (pullback (𝟙 𝒜.X ^ n) η[𝒜.X])).hom
  rw [← Over.w (toUnit ((Over.pullback g).obj (pullback (𝟙 𝒜.X ^ n) η[𝒜.X])))]
  have : IsIso (𝟙_ (Over (Spec (W.residueField w)))).hom := inferInstanceAs (IsIso (𝟙 _))
  infer_instance

/-- Let `𝒜` be an abelian scheme over a scheme `W` and `n ≥ 1` an integer invertible on `W`.
Then the `n`-torsion subscheme `𝒜[n] = 𝒜 ×_{[n], 𝒜, e} W` is unramified over `W`: its structure
morphism is locally of finite type and formally unramified. -/
@[faltings "lem_mw_torsion_scheme_unramified"]
theorem locallyOfFiniteType_and_formallyUnramified_torsion {W : Scheme.{u}} (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom)
    (n : ℤ) (hn1 : 1 ≤ n) (hn : IsUnit (n : Γ(W, ⊤))) :
    LocallyOfFiniteType (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom ∧
      FormallyUnramified (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom := by
  have := (isSeparated_and_locallyOfFiniteType_torsion 𝒜 hfib n hn1).2
  have : Unramified (pullback (𝟙 𝒜.X ^ n) η[𝒜.X]).hom :=
    (unramified_iff_unramified_fiberToSpecResidueField _).mpr fun w =>
      have := etale_fiberToSpecResidueField_torsion 𝒜 hfib n hn w
      inferInstance
  exact ⟨inferInstance, inferInstance⟩

end Faltings
