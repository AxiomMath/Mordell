module

public import Mathlib

/-!
# Residue fields of points over a field extension

A scheme receiving a flat surjection from an integral scheme is integral, the values of sections
at a `K`-point are read through its residue field, and the residue fields of `K`-points of a
`k`-scheme, read inside `K`, are contained in the images of the residue fields of the points below
them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Faltings

section ResidueField

/-- A scheme receiving a flat surjective morphism from an integral scheme is integral: it is
irreducible as a continuous image of an irreducible space, and reduced because the stalk maps of
a flat surjective morphism are faithfully flat, hence injective. -/
lemma isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegral X]
    [Flat π] [Surjective π] : IsIntegral Y := by
  have : IrreducibleSpace Y :=
    Function.Surjective.irreducibleSpace π.base.hom.continuous ‹Surjective π›.surj
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := ‹Surjective π›.surj y
    algebraize [(π.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (π x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap π x) (π.toLRSHom.prop x)
    exact isReduced_of_injective _ ‹RingHom.FaithfullyFlat _›.injective
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- A field extension induces a flat surjective morphism of spectra. -/
lemma flat_surjective_Spec_map {A B : Type u} [Field A] [Field B] (g : A →+* B) :
    Flat (Spec.map (CommRingCat.ofHom g)) ∧ Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨?_, ⟨fun y => ⟨IsLocalRing.closedPoint B, Subsingleton.elim _ _⟩⟩⟩
  rw [Flat.SpecMap_iff]
  algebraize [g]
  exact inferInstanceAs (Module.Flat A B)

variable {K : Type u} [Field K]

/-- The value at a `K`-point `g` of a section `s` of `Y` is the image of the germ of `s` under
the stalk map `𝒪_{Y, g(pt)} ⟶ K` of `g`. -/
theorem ΓSpecIso_appLE_eq {Y : Scheme.{u}} (g : Spec (.of K) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (Scheme.ΓSpecIso (.of K)).hom (g.appLE U ⊤ h s) =
      Scheme.stalkClosedPointTo g (Y.presheaf.germ U _ (h trivial) s) := by
  have := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo g U (h trivial))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this]
  rfl

/-- The value at a `K`-point `q ≫ ψ` of a section of `Z` lies in the image of the residue field
of the point `q(pt)` of `Y`. -/
theorem ΓSpecIso_appLE_comp_mem {Y Z : Scheme.{u}} (q : Spec (.of K) ⟶ Y) (ψ : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ U) (s : Γ(Z, U)) :
    (Scheme.ΓSpecIso (.of K)).hom ((q ≫ ψ).appLE U ⊤ h s) ∈
      (Y.descResidueField (Scheme.stalkClosedPointTo q)).hom.fieldRange := by
  rw [ΓSpecIso_appLE_eq, Scheme.stalkClosedPointTo_comp]
  refine ⟨Y.residue _ (ψ.stalkMap _ (Z.presheaf.germ U _ (h trivial) s)), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField]
  rfl

/-- The residue field of a `K`-point `g ≫ h` is contained in that of `g`. -/
lemma fieldRange_descResidueField_comp_le {Y W : Scheme.{u}} (g : Spec (.of K) ⟶ Y)
    (h : Y ⟶ W) {q : Spec (.of K) ⟶ W} (hq : g ≫ h = q) :
    (W.descResidueField (Scheme.stalkClosedPointTo q)).hom.fieldRange ≤
      (Y.descResidueField (Scheme.stalkClosedPointTo g)).hom.fieldRange := by
  subst hq
  rintro _ ⟨y, rfl⟩
  exact ⟨(Scheme.Hom.residueFieldMap h _).hom y,
    (congrArg (fun φ => φ.hom y) (Scheme.descResidueField_stalkClosedPointTo_comp h g)).symm⟩

/-- For a field `M` and an embedding `ι : M → K`, the values of the stalk map at the `K`-point
`Spec K ⟶ Spec M` lie in `ι(M)`. -/
lemma range_stalkClosedPointTo_Spec_map_le {M : Type u} [Field M] (ι : M →+* K) :
    (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι))).hom.range ≤ ι.range := by
  rintro _ ⟨t, rfl⟩
  have hV := isAffineOpen_top (Spec (.of M))
  let := TopCat.Presheaf.algebra_section_stalk (Spec (.of M)).presheaf
    (⟨(Spec.map (CommRingCat.ofHom ι)) (IsLocalRing.closedPoint K), trivial⟩ :
      (⊤ : (Spec (.of M)).Opens))
  have hloc := hV.isLocalization_stalk
    ⟨(Spec.map (CommRingCat.ofHom ι)) (IsLocalRing.closedPoint K), trivial⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (hV.primeIdealOf
    ⟨(Spec.map (CommRingCat.ofHom ι)) (IsLocalRing.closedPoint K), trivial⟩).asIdeal.primeCompl t
  have hgerm (b : Γ(Spec (.of M), ⊤)) :
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι))).hom
        (algebraMap Γ(Spec (.of M), ⊤) _ b) = ι ((Scheme.ΓSpecIso (.of M)).hom b) :=
    congrArg (fun φ => φ.hom b) (Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom ι))
  have hunit : IsUnit ((Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι))).hom
      (algebraMap Γ(Spec (.of M), ⊤) _ (s : Γ(Spec (.of M), ⊤)))) :=
    (IsLocalization.map_units _ s).map _
  have heq : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι))).hom
      (IsLocalization.mk' _ a s) =
        ι ((Scheme.ΓSpecIso (.of M)).hom a) * (ι ((Scheme.ΓSpecIso (.of M)).hom s))⁻¹ := by
    rw [← hgerm, ← hgerm, eq_mul_inv_iff_mul_eq₀ hunit.ne_zero, ← map_mul,
      IsLocalization.mk'_spec]
  exact heq ▸ mul_mem ⟨_, rfl⟩ (inv_mem (s := ι.fieldRange) ⟨_, rfl⟩)

/-- The residue field of a `K`-point factoring through `Spec M`, for a field `M` embedded in `K`
by `ι`, lies in `ι(M)`. -/
lemma fieldRange_descResidueField_le {Y : Scheme.{u}} {M : Type u} [Field M]
    (ι : M →+* K) (r : Spec (.of M) ⟶ Y) {q : Spec (.of K) ⟶ Y}
    (hq : Spec.map (CommRingCat.ofHom ι) ≫ r = q) :
    (Y.descResidueField (Scheme.stalkClosedPointTo q)).hom.fieldRange ≤ ι.fieldRange := by
  refine (fieldRange_descResidueField_comp_le _ r hq).trans ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨t, rfl⟩ := Scheme.residue_surjective _ _ z
  have e := congrArg (fun φ => φ.hom t)
    (Scheme.residue_descResidueField (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ι))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  obtain ⟨m, hm⟩ := range_stalkClosedPointTo_Spec_map_le ι ⟨t, rfl⟩
  exact ⟨m, hm.trans e.symm⟩

end ResidueField

end Faltings
