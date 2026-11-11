module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Fields of definition of projective varieties

Let `X` be a projective variety over a field `K` (in the source `K = \bar{ℚ}`) and let `k` be a
number field with an embedding `k → K`. A *field of definition* of `X` is `k` together with a
`k`-variety `X_k` and an isomorphism of `K`-schemes `X ≅ X_k ×_k K`. Given fields of definition
of `X` and `Y` over the same `k`, a morphism `X ⟶ Y` is *defined over `k`* if, under these
isomorphisms, it is the base change of a `k`-morphism `X_k ⟶ Y_k`.

## Main definitions

* `Faltings.FieldOfDefinition K f k`: a field of definition `k` of the projective variety
  `f : X ⟶ Spec K`, i.e. a `k`-variety `X_k` and an isomorphism `X ≅ X_k ×_{Spec k} Spec K`
  over `Spec K`.
* `Faltings.FieldOfDefinition.IsDefinedOver`: a morphism `X ⟶ Y` is the base change of a
  `k`-morphism of the given models.

## Implementation notes

The embedding `k → K` is an `Algebra k K` instance, and the base change `X_k ×_k K` is the
fibre product `pullback (X_k ⟶ Spec k) (Spec K ⟶ Spec k)`, a `K`-scheme through its second
projection. The isomorphism is required to commute with the structure morphisms to `Spec K`.
The base change of a `k`-morphism `g : X_k ⟶ Y_k` is `pullback.map g (𝟙 _) (𝟙 _)`.
Varieties are in the sense of `AlgebraicGeometry.IsVariety` (integral, separated, of finite
type over the field), projective varieties in the sense of
`AlgebraicGeometry.IsProjectiveVariety`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][Bombieri1990], Sec. 2
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Faltings

/-- A **field of definition** `k` of a projective variety `f : X ⟶ Spec K`: a `k`-variety
`X_k` (`model`, with structure morphism `toSpec`) and an isomorphism `X ≅ X_k ×_k K` of
`K`-schemes. -/
@[faltings "def_ht_variety_field_of_definition"]
public structure FieldOfDefinition (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProjectiveVariety K f]
    (k : Type u) [Field k] [NumberField k] [Algebra k K] where
  /-- The model `X_k` of `X` over `k`. -/
  model : Scheme.{u}
  /-- The structure morphism `X_k ⟶ Spec k`. -/
  toSpec : model ⟶ Spec (.of k)
  /-- The model is a `k`-variety. -/
  isVariety : IsVariety k toSpec
  /-- The isomorphism `X ≅ X_k ×_k K`. -/
  iso : X ≅ pullback toSpec (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  /-- The isomorphism `X ≅ X_k ×_k K` is one of `K`-schemes. -/
  iso_hom_snd : iso.hom ≫ pullback.snd _ _ = f

namespace FieldOfDefinition

variable {K : Type u} [Field K] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of K)}
  [IsProjectiveVariety K f] {g : Y ⟶ Spec (.of K)} [IsProjectiveVariety K g]
  {k : Type u} [Field k] [NumberField k] [Algebra k K]

/-- A morphism `φ : X ⟶ Y` is **defined over `k`** (with respect to fields of definition
`F` of `X` and `G` of `Y`) if it is the base change `ψ ×_k K` of a `k`-morphism
`ψ : X_k ⟶ Y_k`, transported along `X ≅ X_k ×_k K` and `Y ≅ Y_k ×_k K`. -/
@[expose, faltings "def_ht_variety_field_of_definition"]
public def IsDefinedOver (F : FieldOfDefinition K f k) (G : FieldOfDefinition K g k)
    (φ : X ⟶ Y) : Prop :=
  ∃ (ψ : F.model ⟶ G.model) (hψ : ψ ≫ G.toSpec = F.toSpec),
    φ = F.iso.hom ≫ pullback.map _ _ _ _ ψ (𝟙 _) (𝟙 _) (by simp [hψ]) (by simp) ≫ G.iso.inv

end FieldOfDefinition

end Faltings


/-!
# The residue field and the degree of a point over a field of definition

Let `X` be a projective variety over a field `K` (in the source `K = \bar{ℚ}`), let `k` be a
field of definition of `X`, with model `X_k` and isomorphism `X ≅ X_k ×_k K`, and let
`p ∈ X(K)` be a `K`-point, i.e. a section `p : Spec K ⟶ X` of the structure morphism. The
image of `p` in `X_k` is the point `x` underlying the composite
`Spec K ⟶ X ≅ X_k ×_k K ⟶ X_k`, and this composite is the same as a point `x` together with an
embedding of the residue field `κ(x) ⟶ K`. Since the composite lies over `Spec k`, this
embedding is `k`-linear, and its image is the subfield `k(p)` of `K` containing `k`. Its degree
`[k(p) : k]` is the *degree of `p` over `k`*.

## Main definitions

* `Faltings.FieldOfDefinition.pointResidueField F p hp`: the residue field `k(p) ⊆ K` of the
  image of the `K`-point `p` in the model `X_k`.
* `Faltings.FieldOfDefinition.pointDegree F p hp`: the degree `[k(p) : k]`.

## Implementation notes

A `K`-point of `f : X ⟶ Spec K` is a morphism `p : Spec K ⟶ X` with `p ≫ f = 𝟙`. The
embedding `κ(x) ⟶ K` is `Scheme.descResidueField (Scheme.stalkClosedPointTo q)` for
`q = p ≫ F.iso.hom ≫ pullback.fst _ _`, the second component of
`AlgebraicGeometry.Scheme.SpecToEquivOfField K X_k q`. The section condition `p ≫ f = 𝟙` makes
`q` lie over `Spec k` along `Spec K ⟶ Spec k`, so the image of `κ(x)` contains the image of `k`.
That image is an `IntermediateField k K`. The degree is `Module.finrank`, which is `0` when the
extension is infinite; for a variety over a number field it is finite.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][Bombieri1990], Sec. 2
* [Z. Gao, *Lecture notes on heights*][Gao2022], proof of Prop. 5.1.3(ii)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Faltings

namespace FieldOfDefinition

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
  [IsProjectiveVariety K f] {k : Type u} [Field k] [NumberField k] [Algebra k K]

/-- The residue field `k(p) ⊆ K` of the image in `X_k` of a `K`-point `p` of `X`, for a field of
definition `F` of `X` over `k`: the image in `K` of the residue field `κ(x)` of the image point
`x ∈ X_k`, under the embedding `κ(x) ⟶ K` induced by `Spec K ⟶ X ≅ X_k ×_k K ⟶ X_k`. -/
@[expose, faltings "def_ht_residue_field_point"]
public noncomputable def pointResidueField (F : FieldOfDefinition K f k)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) : IntermediateField k K :=
  Subfield.toIntermediateField (F.model.descResidueField
    (Scheme.stalkClosedPointTo (p ≫ F.iso.hom ≫ pullback.fst _ _))).hom.fieldRange fun c => by
    set q := p ≫ F.iso.hom ≫ pullback.fst _ _
    have hq : q ≫ F.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      simp only [q, Category.assoc, pullback.condition]
      rw [← Category.assoc F.iso.hom, F.iso_hom_snd, ← Category.assoc, hp, Category.id_comp]
    have h1 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap k K))
    have h2 : ∀ g (_ : g = q ≫ F.toSpec),
        (Spec (.of k)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint K)) trivial ≫
          Scheme.stalkClosedPointTo g =
        (Spec (.of k)).presheaf.germ ⊤ _ trivial ≫ F.toSpec.stalkMap _ ≫
          F.model.residue _ ≫ F.model.descResidueField (Scheme.stalkClosedPointTo q) := by
      rintro g rfl
      rw [Scheme.stalkClosedPointTo_comp, Scheme.residue_descResidueField]
      rfl
    have h3 := h2 _ hq.symm
    rw [h1] at h3
    have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv c)) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4
    exact ⟨_, h4.symm.trans (by simp)⟩

/-- The degree `[k(p) : k]` of a `K`-point `p` of `X` over a field of definition `k` of `X`. -/
@[faltings "def_ht_residue_field_point"]
public noncomputable abbrev pointDegree (F : FieldOfDefinition K f k)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) : ℕ :=
  Module.finrank k (F.pointResidueField p hp)

end FieldOfDefinition

end Faltings
