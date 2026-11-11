module

public import Mordell.FunctionField.Place.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import Mordell.Curve.Topology

/-!
# Local rings at closed points of a normal curve are places

Let `F/K` be an algebraic function field of one variable, `f : C ⟶ Spec K` a normal curve over
`K`, and `φ : K(C) ≃ₐ[K] F` an isomorphism of `K`-algebras, where `K(C)` is a `K`-algebra through
`f` on global sections followed by the germ at the generic point. For a closed point `x` of `C`
the stalk `𝒪_{C,x}` is a Noetherian local normal domain of dimension `1` with fraction field
`K(C)`, hence a discrete valuation ring and a valuation ring of `K(C)` which is not a field; it
contains the image of `K`. Transporting along `φ`, the image of `𝒪_{C,x}` in `F` is a place of
`F/K`.

## Main results

* `Faltings.FunctionField.exists_place_eq_image_stalk`: for a closed point `x` of a normal curve
  `C` and a `K`-algebra isomorphism `φ : C.functionField ≃ₐ[K] F`, there is a place
  `v : Faltings.Place K F` whose carrier is `φ` of the image of
  `algebraMap (C.presheaf.stalk x) C.functionField`.

## Implementation notes

The subring `𝒪_{C,x} ⊆ K(C)` is the range of the injective generization map
`algebraMap (C.presheaf.stalk x) C.functionField`
(`IsFractionRing.injective`). A place is a structure, so
"the subring is a place" is stated as the existence of a place with that carrier; the place is
unique by `Faltings.Place.ext`. Normality is `AlgebraicGeometry.IsNormal C`.

## References

* [Stacks, Tag 0B8Y], [Stacks, Tag 00PD], [Stacks, Tag 00IB]
-/

open AlgebraicGeometry CategoryTheory

universe u v

public section

namespace Faltings.FunctionField

/-- A Noetherian local integrally closed domain of Krull dimension one is a valuation ring
which is not a field. -/
private lemma valuationRing_and_not_isField (R : Type*) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R] (h : ringKrullDim R = 1) :
    ValuationRing R ∧ ¬ IsField R := by
  have hnf : ¬ IsField R := fun hR => by
    let := hR.toField
    exact one_ne_zero (h.symm.trans (ringKrullDim_eq_zero_of_field R))
  have hle : Ring.KrullDimLE 1 R := by rw [Ring.krullDimLE_iff, h]; rfl
  have : IsDedekindDomain R :=
    { maximalOfPrime := Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hle _ }
  exact ⟨((IsDiscreteValuationRing.TFAE R hnf).out 3 2).mp this, hnf⟩

/-- A valuation ring `R` of a field `L`, not itself a field and containing the image of `K`,
is carried by any `K`-algebra isomorphism `φ : L ≃ₐ[K] F` to a place of `F`. -/
private lemma exists_place_of_valuationRing {K R L F : Type*} [CommRing K] [CommRing R]
    [IsDomain R] [ValuationRing R] [Field L] [Field F] [Algebra R L] [IsFractionRing R L]
    [Algebra K L] [Algebra K F] (hR : ¬ IsField R)
    (hK : ∀ a : K, algebraMap K L a ∈ (algebraMap R L).range) (φ : L ≃ₐ[K] F) :
    ∃ v : Place K F, (v.toSubalgebra : Set F) = φ '' Set.range (algebraMap R L) := by
  let A : Subalgebra K F :=
    { (algebraMap R L).range.map φ.toRingEquiv.toRingHom with
      algebraMap_mem' := fun a => ⟨_, hK a, φ.commutes a⟩ }
  refine ⟨{ toSubalgebra := A
            mem_or_inv_mem' := fun z => ?_
            neg_mem' := fun h => neg_mem (s := A) h
            ne_top := fun htop => hR ?_ }, by ext; simp [A]⟩
  · rcases ValuationRing.isInteger_or_isInteger R (φ.symm z) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact .inl ⟨_, ⟨r, hr⟩, by simp⟩
    · exact .inr ⟨_, ⟨r, hr⟩, by simp [map_inv₀]⟩
  · have hsurj : Function.Surjective (algebraMap R L) := fun w => by
      obtain ⟨_, ⟨r, rfl⟩, hr⟩ : φ w ∈ A := htop ▸ Algebra.mem_top
      exact ⟨r, φ.injective hr⟩
    exact (RingEquiv.ofBijective _ ⟨IsFractionRing.injective R L, hsurj⟩).toMulEquiv.isField
      (Field.toIsField _)

/-- Let `F/K` be a function field, `f : C ⟶ Spec K` a normal curve and `φ : K(C) ≃ₐ[K] F` an
isomorphism of `K`-algebras. For every closed point `x` of `C`, the image under `φ` of the local
ring `𝒪_{C,x} ⊆ K(C)` is the carrier of a place of `F/K`. -/
@[faltings "lem_ff_closed_point_place"]
theorem exists_place_eq_image_stalk (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsNormal C]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F)
    {x : C} (hx : IsClosed {x}) :
    ∃ v : Place K F, (v.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x) C.functionField) := by
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim := ringKrullDim_stalk_eq_one_of_isCurve K f hx
  have : IsIntegrallyClosed (C.presheaf.stalk x) := IsNormal.stalk_normal x
  obtain ⟨_, hnf⟩ := valuationRing_and_not_isField _ hdim
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  exact exists_place_of_valuationRing hnf (fun a => ⟨C.presheaf.germ ⊤ x trivial
    (f.appTop ((Scheme.ΓSpecIso (.of K)).inv a)),
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C) (U := ⊤) _ _⟩) φ

end Faltings.FunctionField

end

/-!
# Residue fields of corresponding closed points and places

Let `F/K` be an algebraic function field of one variable, `f : C ⟶ Spec K` a curve over `K` and
`φ : K(C) ≃ₐ[K] F` an isomorphism of `K`-algebras, where `K(C)` is a `K`-algebra through `f`.
Let `x` be a closed point of `C` and `v` a place of `F/K` whose valuation ring is the image under
`φ` of the local ring `𝒪_{C,x} ⊆ K(C)`. Then `φ` restricts to a ring isomorphism
`𝒪_{C,x} ≅ 𝒪_v`, which maps the maximal ideal onto the maximal ideal, and so induces an
isomorphism of `K`-algebras `κ(x) ≅ κ(v)` of residue fields, compatible with the residue maps.

## Main results

* `Faltings.FunctionField.exists_algEquiv_residueField_place`: the isomorphism `κ(x) ≃ₐ[K] κ(v)`
  induced by `φ`, characterised by `κ(x) ∋ [a] ↦ [φ a]`.

## Implementation notes

`κ(x)` is `C.residueField x`, a `K`-algebra through `C.fromSpecResidueField x ≫ f`; `κ(v)` is
`Faltings.Place.ResidueField v` with its `K`-algebra structure `K → 𝒪_v → κ(v)`.

## References

* [R. Hartshorne, *Algebraic Geometry*], I.6, II.6
-/

public section

open AlgebraicGeometry CategoryTheory

namespace Faltings.FunctionField

/-- The `K`-algebra structure of `κ(x)` induced by `f` is `K → Γ(C) → 𝒪_{C,x} → κ(x)`. -/
public lemma preimage_fromSpecResidueField_comp {R : CommRingCat.{u}} {C : Scheme.{u}}
    (f : C ⟶ Spec R) (x : C) :
    Spec.preimage (C.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ C.presheaf.germ ⊤ x trivial ≫ C.residue x := by
  apply Spec.map_injective
  have h₁ : f = C.toSpecΓ ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [Spec.map_preimage, Scheme.fromSpecResidueField]
  conv_lhs => rw [h₁, Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc]
  simp only [Spec.map_comp, Category.assoc]

/-- An injective ring hom whose range is the carrier of a subring `S` is a ring isomorphism
onto `S`. -/
private noncomputable def equivOfRangeEq {A R : Type*} [Ring A] [Ring R] (ι : A →+* R)
    (hι : Function.Injective ι) (S : Subring R) (h : (S : Set R) = Set.range ι) : A ≃+* S :=
  RingEquiv.ofBijective (ι.codRestrict S fun a => show ι a ∈ (S : Set R) from h ▸ ⟨a, rfl⟩)
    ⟨fun _ _ hab => hι congr($hab.1), fun b => by
      obtain ⟨a, ha⟩ := h ▸ show (b : R) ∈ (S : Set R) from b.2
      exact ⟨a, Subtype.ext ha⟩⟩

/-- Let `F/K` be a function field, `f : C ⟶ Spec K` a curve, `φ : K(C) ≃ₐ[K] F` an isomorphism of
`K`-algebras, `x` a closed point of `C` and `v` a place of `F/K` with `𝒪_v = φ(𝒪_{C,x})`. Then `φ`
induces an isomorphism of `K`-algebras `κ(x) ≃ₐ[K] κ(v)` sending the residue class of `a ∈ 𝒪_{C,x}`
to the residue class of `φ a ∈ 𝒪_v`. -/
@[faltings "lem_ff_closed_point_residue_iso"]
theorem exists_algEquiv_residueField_place (K : Type u) [Field K] (F : Type v) [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F)
    {x : C} (hx : IsClosed {x}) (v : Place K F)
    (hv : (v.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x) C.functionField)) :
    letI : Algebra K (C.residueField x) :=
      (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom.toAlgebra
    ∃ e : C.residueField x ≃ₐ[K] v.ResidueField,
      ∀ (a : C.presheaf.stalk x) (b : v.toValuationSubring),
        φ (algebraMap (C.presheaf.stalk x) C.functionField a) = (b : F) →
          e (C.residue x a) = IsLocalRing.residue v.toValuationSubring b := by
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  let : Algebra K (C.residueField x) :=
    (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom.toAlgebra
  let ι := (φ : C.functionField →+* F).comp (algebraMap (C.presheaf.stalk x) C.functionField)
  let e₀ : C.presheaf.stalk x ≃+* v.toValuationSubring := equivOfRangeEq ι
    (φ.injective.comp (IsFractionRing.injective (C.presheaf.stalk x) C.functionField))
    v.toValuationSubring.toSubring (by rw [RingHom.coe_comp, Set.range_comp]; exact hv)
  let e₁ : C.residueField x ≃+* v.ResidueField := IsLocalRing.ResidueField.mapEquiv e₀
  have he : ∀ (a : C.presheaf.stalk x) (b : v.toValuationSubring),
      φ (algebraMap _ C.functionField a) = (b : F) →
        e₁ (C.residue x a) = IsLocalRing.residue v.toValuationSubring b := fun a b h => by
    rw [← show e₀ a = b from Subtype.ext h]; rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := e₁) fun r => ?_, he⟩
  set t := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom r
  have h₁ : algebraMap K (C.residueField x) r = C.residue x (C.presheaf.germ ⊤ x trivial t) := by
    change (Spec.preimage (C.fromSpecResidueField x ≫ f)).hom r = _
    rw [preimage_fromSpecResidueField_comp]; rfl
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  have h₂ : φ (algebraMap _ C.functionField (C.presheaf.germ ⊤ x trivial t)) = algebraMap K F r :=
    (congrArg φ
      (Scheme.algebraMap_germ_eq_germToFunctionField (X := C) (U := ⊤) (x := x) trivial t)).trans
        (φ.commutes r)
  rw [h₁, he _ ⟨algebraMap K F r, v.toSubalgebra.algebraMap_mem r⟩ h₂]
  rfl

end Faltings.FunctionField

end

/-!
# Places of a function field and closed points of a normal proper model

Let `F/K` be an algebraic function field of one variable, `f : C ⟶ Spec K` a normal proper curve
over `K`, and `φ : K(C) ≃ₐ[K] F` an isomorphism of `K`-algebras, where `K(C)` is a `K`-algebra
through `f` on global sections followed by the germ at the generic point. Every place `v` of
`F/K` is centred at exactly one closed point of `C`: there is a unique closed point `x` with
`𝒪_v = φ(𝒪_{C,x})`. Existence comes from the valuative criterion of properness applied to the
valuation ring `φ⁻¹(𝒪_v)` of `K(C)`, together with normality, which makes `𝒪_{C,x}` a discrete
valuation ring and hence maximal for domination; uniqueness holds because local rings of
distinct points of an integral separated scheme are distinct subrings of the function field.

## Main results

* `Faltings.FunctionField.existsUnique_isClosed_place_eq_image_stalk`: for every place
  `v : Faltings.Place K F` there is a unique closed point `x : C` such that the carrier of `v`
  is `φ` of the image of `algebraMap (C.presheaf.stalk x) C.functionField`.

## Implementation notes

The subring `𝒪_{C,x} ⊆ K(C)` is the range of the injective generization map
`algebraMap (C.presheaf.stalk x) C.functionField`
(`IsFractionRing.injective`). Normality is
`AlgebraicGeometry.IsNormal C` and properness is `AlgebraicGeometry.IsProper f`.

## References

* [Stacks, Tag 0BX5], [Stacks, Tag 0B8Y], [Stacks, Tag 02NF], [Stacks, Tag 00I9]
-/

open AlgebraicGeometry CategoryTheory

public section

namespace Faltings.FunctionField

/-- If `h : Spec R ⟶ X` restricts along `Spec.map g` to the canonical morphism
`Spec 𝒪_{X,y} ⟶ X`, then the local homomorphism `𝒪_{X, h 𝔪} ⟶ R` attached to `h`, followed by
`g`, is the generization map `𝒪_{X, h 𝔪} ⟶ 𝒪_{X,y}`. -/
public lemma stalkClosedPointTo_comp_eq_stalkSpecializes {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] {y : X} (g : R ⟶ X.presheaf.stalk y) (h : Spec R ⟶ X)
    (hh : Spec.map g ≫ h = X.fromSpecStalk y) (hy : y ⤳ h (IsLocalRing.closedPoint R)) :
    Scheme.stalkClosedPointTo h ≫ g = X.presheaf.stalkSpecializes hy := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk _), Spec.map_comp, Category.assoc,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hh,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` followed by a morphism to an affine scheme
`Spec R` is `Spec` of the composite `R → Γ(X, ⊤) → 𝒪_{X,x}`. -/
public lemma fromSpecStalk_comp_eq_SpecMap {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (x : X) :
    X.fromSpecStalk x ≫ f =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  calc X.fromSpecStalk x ≫ f
      = X.fromSpecStalk x ≫ (f ≫ (Spec R).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by simp
    _ = _ := by
      rw [Scheme.toSpecΓ_naturality, ← Category.assoc, ← Category.assoc,
        Scheme.fromSpecStalk_toSpecΓ]
      simp only [Spec.map_comp, Category.assoc]

/-- A valuation subring `W` dominating a valuation subring `V` equals it: if `V` is the range of
`ι : R →+* L` and `ι` factors through a local homomorphism `ρ : R →+* W`, then `V = W`. -/
private lemma eq_of_range_eq_of_isLocalHom {L R : Type*} [Field L] [CommRing R] {ι : R →+* L}
    {V W : ValuationSubring L} (hV : Set.range ι = V) (ρ : R →+* W) [IsLocalHom ρ]
    (hρ : ∀ s, (ρ s : L) = ι s) : V = W := by
  have hι : ∀ x, x ∈ V ↔ ∃ s, ι s = x := fun x => by rw [← SetLike.mem_coe, ← hV]; rfl
  have hle : V.toSubring ≤ W.toSubring := fun x hx => by
    obtain ⟨s, rfl⟩ := (hι x).1 hx
    exact hρ s ▸ (ρ s).2
  refine ValuationSubring.toLocalSubring_injective
    (V.isMax_toLocalSubring.eq_of_le ⟨hle, ⟨fun t ht => ?_⟩⟩)
  obtain ⟨s, hs⟩ := (hι t).1 t.2
  have hρs : ρ s = Subring.inclusion hle t := Subtype.ext (by rw [hρ, hs]; rfl)
  have hts : t = ι.codRestrict V.toSubring (fun s => (hι _).2 ⟨s, rfl⟩) s := Subtype.ext hs.symm
  exact hts ▸ (isUnit_of_map_unit ρ s (hρs ▸ ht)).map _

/-- If the valuation subring `W` of `F` is the image under `φ : L ≃+* F` of the range of `ι`,
then the range of `ι` is the valuation subring `φ⁻¹ W` of `L`. -/
private lemma range_eq_comap {L F R E : Type*} [Field L] [Field F] [CommRing R]
    [EquivLike E L F] [RingEquivClass E L F] (φ : E) (W : ValuationSubring F)
    {ι : R →+* L} (hW : (W : Set F) = φ '' Set.range ι) :
    Set.range ι = W.comap (φ : L →+* F) := by
  rw [ValuationSubring.coe_comap, hW]
  exact ((EquivLike.injective φ).preimage_image _).symm

/-- The local ring at the generic point of an integral scheme is all of its function field.
The point is a variable `x = genericPoint X`, so that `algebraMap` is the generization map rather
than the identity of `X.functionField`. -/
private lemma algebraMap_stalk_surjective_of_eq_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {x : X} (hx : x = genericPoint X) :
    Function.Surjective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  subst hx
  refine fun a => ⟨a, ?_⟩
  change (X.presheaf.stalkSpecializes _).hom a = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Let `F/K` be a function field, `f : C ⟶ Spec K` a normal proper curve and
`φ : K(C) ≃ₐ[K] F` an isomorphism of `K`-algebras. For every place `v` of `F/K` there is a unique
closed point `x` of `C` such that `𝒪_v` is the image under `φ` of the local ring
`𝒪_{C,x} ⊆ K(C)`. -/
@[faltings "prop_ff_places_closed_points"]
theorem existsUnique_isClosed_place_eq_image_stalk (K : Type u) [Field K] (F : Type v) [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsNormal C] [IsProper f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F)
    (w : Place K F) :
    ∃! x : C, IsClosed {x} ∧ (w.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x) C.functionField) := by
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  let A : ValuationSubring C.functionField :=
    w.toValuationSubring.comap (φ : C.functionField →+* F)
  let ψ : K →+* A := (algebraMap K C.functionField).codRestrict A.toSubring fun a =>
    show φ _ ∈ w.toSubalgebra by rw [φ.commutes]; exact w.toSubalgebra.algebraMap_mem a
  let g : CommRingCat.of A ⟶ C.functionField := CommRingCat.ofHom (algebraMap A C.functionField)
  have comm : C.fromSpecStalk (genericPoint C) ≫ f =
      Spec.map g ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [fromSpecStalk_comp_eq_SpecMap, ← Spec.map_comp]
    rfl
  let S : ValuativeCommSq f :=
    { R := A, K := C.functionField, i₁ := C.fromSpecStalk (genericPoint C),
      i₂ := Spec.map (CommRingCat.ofHom ψ), commSq := ⟨comm⟩ }
  have lift_of : ∀ h : Spec (.of A) ⟶ C, Spec.map g ≫ h = C.fromSpecStalk (genericPoint C) →
      h ≫ f = Spec.map (CommRingCat.ofHom ψ) := by
    intro h hh
    rw [← Spec.map_preimage (h ≫ f)]
    congr 1
    have : Spec.map (Spec.preimage (h ≫ f) ≫ g) = Spec.map (CommRingCat.ofHom ψ ≫ g) := by
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, hh, comm, Spec.map_comp]
    ext a
    exact congr($(Spec.map_injective this).hom a)
  have centre : ∀ h : Spec (.of A) ⟶ C, Spec.map g ≫ h = C.fromSpecStalk (genericPoint C) →
      IsClosed {h (IsLocalRing.closedPoint (CommRingCat.of A))} ∧ (w.toSubalgebra : Set F) =
        φ '' Set.range (algebraMap
          (C.presheaf.stalk (h (IsLocalRing.closedPoint (CommRingCat.of A)))) C.functionField) := by
    intro h hh
    set x := h (IsLocalRing.closedPoint (CommRingCat.of A))
    have hηx : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial
    let ρ := Scheme.stalkClosedPointTo h
    have hρ : ∀ s, ((ρ.hom s : A) : C.functionField) =
        algebraMap (C.presheaf.stalk x) C.functionField s := fun s =>
      congr($(stalkClosedPointTo_comp_eq_stalkSpecializes g h hh hηx).hom s)
    have hxη : x ≠ genericPoint C := by
      rintro hxη
      apply w.ne_top
      rw [eq_top_iff]
      intro z _
      obtain ⟨s, hs⟩ := algebraMap_stalk_surjective_of_eq_genericPoint hxη (φ.symm z)
      have hz : φ.symm z ∈ A := hs ▸ hρ s ▸ (ρ.hom s).2
      simpa using (show φ (φ.symm z) ∈ w.toSubalgebra from hz)
    have hxc : IsClosed {x} := isClosed_singleton_of_ne_genericPoint K f hxη
    obtain ⟨v, hv⟩ := exists_place_eq_image_stalk K F f φ hxc
    refine ⟨hxc, ?_⟩
    have hvw := eq_of_range_eq_of_isLocalHom (range_eq_comap φ v.toValuationSubring hv) ρ.hom hρ
    rw [← hv]
    ext z
    exact (by simpa [A] using congr(φ.symm z ∈ $hvw).symm :
      z ∈ w.toValuationSubring ↔ z ∈ v.toValuationSubring)
  have lift_at : ∀ x : C, (w.toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x) C.functionField) →
      ∃ h : Spec (.of A) ⟶ C, Spec.map g ≫ h = C.fromSpecStalk (genericPoint C) ∧
        h (IsLocalRing.closedPoint (CommRingCat.of A)) = x := by
    intro x hx
    have hrange := range_eq_comap φ w.toValuationSubring hx
    let e : C.presheaf.stalk x ≃+* A := RingEquiv.ofBijective
      ((algebraMap (C.presheaf.stalk x) C.functionField).codRestrict A.toSubring
        fun s => (hrange.le ⟨s, rfl⟩ :))
      ⟨fun s t hst => IsFractionRing.injective (C.presheaf.stalk x) C.functionField
          congr($hst.1),
       fun a => by obtain ⟨s, hs⟩ := hrange.ge a.2; exact ⟨s, Subtype.ext hs⟩⟩
    have hg : CommRingCat.ofHom (e : C.presheaf.stalk x →+* A) ≫ g =
        C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial) := rfl
    refine ⟨Spec.map (CommRingCat.ofHom (e : C.presheaf.stalk x →+* A)) ≫ C.fromSpecStalk x,
      ?_, ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, hg, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    · have : IsLocalHom (CommRingCat.ofHom (e : C.presheaf.stalk x →+* A)).hom :=
        inferInstanceAs (IsLocalHom (e : C.presheaf.stalk x →+* A))
      change C.fromSpecStalk x (Spec.map (CommRingCat.ofHom (e : C.presheaf.stalk x →+* A))
        (IsLocalRing.closedPoint (CommRingCat.of A))) = x
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨l⟩ := ((UniversallyClosed.eq_valuativeCriterion.le _ _ f inferInstance).1 S).exists_lift
  refine ⟨l.l (IsLocalRing.closedPoint (CommRingCat.of A)), centre l.l l.fac_left, ?_⟩
  rintro y ⟨-, hy⟩
  obtain ⟨h, hh, rfl⟩ := lift_at y hy
  have := IsSeparated.valuativeCriterion f S
  exact congr($(Subsingleton.elim (⟨h, hh, lift_of h hh⟩ : S.commSq.LiftStruct) l).l _)

end Faltings.FunctionField

end
