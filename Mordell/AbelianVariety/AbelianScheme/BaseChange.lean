module

public import Mathlib
public import Mordell.Attr

/-!
# Base change of abelian schemes

An abelian scheme over a scheme `W` is a group scheme `𝒜 → W` that is flat, proper and of finite
presentation, and all of whose fibres `𝒜_w = 𝒜 ×_W Spec κ(w)` are abelian varieties over the
residue fields `κ(w)`. For any morphism of schemes `g : W' ⟶ W`, the base change
`𝒜_{W'} = 𝒜 ×_W W'`, with the group structure carried along by the base-change functor, is again
an abelian scheme over `W'`.

## Main results

* `Faltings.isAbelianScheme_pullbackObj`: the base change of an abelian scheme along an arbitrary
  morphism of schemes is an abelian scheme.
* `Faltings.flat_mapGrp_obj`, `Faltings.isProper_mapGrp_obj`,
  `Faltings.locallyOfFinitePresentation_mapGrp_obj`, `Faltings.fibres_mapGrp_obj`: the same,
  one condition at a time.

## Implementation notes

A group scheme over `W` is an object `𝒜 : CategoryTheory.Grp (CategoryTheory.Over W)`. Its base
change along `g` is `(CategoryTheory.Over.pullback g).mapGrp.obj 𝒜`: the pullback functor is
monoidal for the cartesian monoidal structures, so it carries group objects to group objects,
and the group structure on `𝒜 ×_W W'` is the canonical one. Being an abelian scheme is spelled
out as the conjunction of `AlgebraicGeometry.Flat`, `AlgebraicGeometry.IsProper`,
`AlgebraicGeometry.LocallyOfFinitePresentation` of the structure morphism (with properness,
locally of finite presentation is finite presentation), together with, for every point `w`, the
fibre over `AlgebraicGeometry.Scheme.fromSpecResidueField` being proper and geometrically
integral over `κ(w)`, which is what an abelian variety over a field is.

## References

* [D. Mumford, *Geometric Invariant Theory*][mumfordGIT], Definition 6.1
* [The Stacks Project][stacks], Tags 01U9, 01W4, 01TS
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Faltings

/-- A group scheme all of whose fibres are geometrically integral is geometrically integral. -/
private lemma geometricallyIntegral_of_fibres {W : Scheme.{u}} (X : Over W)
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj X).hom) :
    GeometricallyIntegral X.hom :=
  (GeometricallyIntegral.iff_geometricallyIntegral_fiber _).2 fun w ↦ (hfib w).2

/-- The base change of a flat group scheme is flat. -/
lemma flat_mapGrp_obj {W W' : Scheme.{u}} (g : W' ⟶ W) (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] : Flat ((Over.pullback g).mapGrp.obj 𝒜).X.hom :=
  inferInstanceAs (Flat (pullback.snd 𝒜.X.hom g))

/-- The base change of a proper group scheme is proper. -/
lemma isProper_mapGrp_obj {W W' : Scheme.{u}} (g : W' ⟶ W) (𝒜 : Grp (Over W))
    [IsProper 𝒜.X.hom] : IsProper ((Over.pullback g).mapGrp.obj 𝒜).X.hom :=
  inferInstanceAs (IsProper (pullback.snd 𝒜.X.hom g))

/-- The base change of a group scheme locally of finite presentation is locally of finite
presentation. -/
lemma locallyOfFinitePresentation_mapGrp_obj {W W' : Scheme.{u}} (g : W' ⟶ W)
    (𝒜 : Grp (Over W)) [LocallyOfFinitePresentation 𝒜.X.hom] :
    LocallyOfFinitePresentation ((Over.pullback g).mapGrp.obj 𝒜).X.hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd 𝒜.X.hom g))

/-- The fibres of the base change of a proper group scheme with geometrically integral fibres are
proper and geometrically integral. -/
lemma fibres_mapGrp_obj {W W' : Scheme.{u}} (g : W' ⟶ W) (𝒜 : Grp (Over W))
    [IsProper 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom)
    (w' : W') :
    IsProper ((Over.pullback (W'.fromSpecResidueField w')).obj
        ((Over.pullback g).mapGrp.obj 𝒜).X).hom ∧
      GeometricallyIntegral ((Over.pullback (W'.fromSpecResidueField w')).obj
        ((Over.pullback g).mapGrp.obj 𝒜).X).hom := by
  have := geometricallyIntegral_of_fibres 𝒜.X hfib
  exact ⟨inferInstanceAs (IsProper (pullback.snd (pullback.snd 𝒜.X.hom g) _)),
    inferInstanceAs (GeometricallyIntegral (pullback.snd (pullback.snd 𝒜.X.hom g) _))⟩

/-- Let `𝒜` be an abelian scheme over `W`: a group scheme over `W` whose structure morphism is
flat, proper and locally of finite presentation and all of whose fibres `𝒜 ×_W Spec κ(w)` are
proper and geometrically integral over `κ(w)`. Then for every morphism of schemes `g : W' ⟶ W`
the base change `𝒜 ×_W W'`, with its induced group structure, is an abelian scheme over `W'`. -/
@[faltings "lem_mw_abelian_scheme_base_change"]
theorem isAbelianScheme_pullbackObj {W W' : Scheme.{u}} (g : W' ⟶ W) (𝒜 : Grp (Over W))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (W.fromSpecResidueField w)).obj 𝒜.X).hom) :
    Flat ((Over.pullback g).mapGrp.obj 𝒜).X.hom ∧
      IsProper ((Over.pullback g).mapGrp.obj 𝒜).X.hom ∧
      LocallyOfFinitePresentation ((Over.pullback g).mapGrp.obj 𝒜).X.hom ∧
      ∀ w', IsProper ((Over.pullback (W'.fromSpecResidueField w')).obj
          ((Over.pullback g).mapGrp.obj 𝒜).X).hom ∧
        GeometricallyIntegral ((Over.pullback (W'.fromSpecResidueField w')).obj
          ((Over.pullback g).mapGrp.obj 𝒜).X).hom :=
  ⟨flat_mapGrp_obj g 𝒜, isProper_mapGrp_obj g 𝒜, locallyOfFinitePresentation_mapGrp_obj g 𝒜,
    fibres_mapGrp_obj g 𝒜 hfib⟩

end Faltings
