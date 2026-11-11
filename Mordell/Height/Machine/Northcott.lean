module

public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.AlgebraicGeometry.FieldOfDefinition
public import Mordell.Height.Weil.Northcott
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.AlgebraicGeometry.PointResidueField

/-!
# Weil's theorem: the Northcott property

Let `X` be a smooth projective variety over an algebraic extension `K` of `ℚ` (in the source,
`K = ℚ̄`), `φ : X ⟶ ℙⁿ_K` a projective embedding, and `k` a number field over which `X` and
`φ` are defined. For every `δ ≥ 1` and every `B ∈ ℝ` there are only finitely many `K`-points
`p` of `X` with `[k(p) : k] ≤ δ` and `h_φ(p) ≤ B`.

## Main results

* `Faltings.ProjectiveEmbedding.finite_setOf_pointDegree_le_height_le`: the set
  `{p ∈ X(K) | [k(p) : k] ≤ δ ∧ h_φ(p) ≤ B}` is finite.
* `Faltings.FieldOfDefinition.finiteDimensional_pointResidueField`: for `K / k` algebraic, the
  residue field `k(p)` of a `K`-point is a finite extension of `k`.
* `Faltings.FieldOfDefinition.comp_toSpec`: the image of a `K`-point in the model `X_k` lies over
  `Spec k`.

## Implementation notes

The field of definition of `X` is a `Faltings.FieldOfDefinition` `F`, with model `X_k` and
`X ≅ X_k ×_k K`. The embedding `φ` is defined over `k` when it is the base change of a
`k`-morphism `X_k ⟶ ℙⁿ_k`. Since `ℙⁿ_K = Spec K ×_ℤ ℙⁿ_ℤ` and `φ` is a morphism over `Spec K`,
this says exactly that the component `X ⟶ ℙⁿ_ℤ` of `φ` factors as
`X ≅ X_k ×_k K ⟶ X_k ⟶ ℙⁿ_ℤ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2, Weil's Theorem (iv).
* [Z. Gao, *Heights*][gao2022], Prop. 5.1.3.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

namespace Faltings

namespace FieldOfDefinition

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
  [IsProjectiveVariety K f] {k : Type u} [Field k] [NumberField k] [Algebra k K]

/-- The image of a `K`-point in the model lies over `Spec k`. -/
theorem comp_toSpec (F : FieldOfDefinition K f k) (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) :
    (p ≫ F.iso.hom ≫ pullback.fst _ _) ≫ F.toSpec =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  simp only [Category.assoc, pullback.condition]
  rw [← Category.assoc F.iso.hom, F.iso_hom_snd, ← Category.assoc, hp, Category.id_comp]

/-- **The residue field of a `K`-point is finite over the field of definition.**
For a `K`-point `p` of `X`, `K / k` algebraic, the field `k(p)` is a finite extension of `k`:
it lies in the image of the coordinate ring of an affine open of the model, a finitely generated
`k`-algebra which is algebraic over `k`. -/
theorem finiteDimensional_pointResidueField [Algebra.IsAlgebraic k K]
    (F : FieldOfDefinition K f k) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    FiniteDimensional k (F.pointResidueField p hp) := by
  set q := p ≫ F.iso.hom ≫ pullback.fst _ _
  have hq := F.comp_toSpec p hp
  have := F.isVariety
  set x := q (IsLocalRing.closedPoint K)
  obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    F.model.isBasis_affineOpens (show x ∈ (⊤ : F.model.Opens) from trivial)
  have hVq : (⊤ : (Spec (.of K)).Opens) ≤ q ⁻¹ᵁ V := fun a _ => by
    rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]; exact hxV
  have hVt : V ≤ F.toSpec ⁻¹ᵁ ⊤ := le_top
  have hFT := HasRingHomProperty.appLE @LocallyOfFiniteType F.toSpec inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hVt
  set α : k →+* Γ(F.model, V) := (F.toSpec.appLE ⊤ V hVt).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom
  set θ : Γ(F.model, V) →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom.comp (q.appLE V ⊤ hVq).hom
  have hθα : ∀ c, θ (α c) = algebraMap k K c := by
    intro c
    change (Scheme.ΓSpecIso (.of K)).hom ((F.toSpec.appLE ⊤ V hVt ≫
      q.appLE V ⊤ hVq)
      ((Scheme.ΓSpecIso (.of k)).inv c)) = _
    rw [Scheme.Hom.appLE_comp_appLE q F.toSpec ⊤ V ⊤ hVt hVq]
    generalize_proofs h'
    revert h'
    rw [hq]
    intro h'
    have h := congrArg (fun g => (Scheme.ΓSpecIso (.of K)).hom (g.hom c))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply,
      CommRingCat.hom_ofHom] at h
    rw [Stacks.ProjectiveSpaceChartRatio.appLE_top_top, ← h]
  let : Algebra k Γ(F.model, V) := α.toAlgebra
  have : Algebra.FiniteType k Γ(F.model, V) :=
    hFT.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  let θ' : Γ(F.model, V) →ₐ[k] K := { θ with commutes' := hθα }
  have : Algebra.FiniteType k θ'.range :=
    Algebra.FiniteType.of_surjective θ'.rangeRestrict θ'.rangeRestrict_surjective
  have : Algebra.IsIntegral k θ'.range := ⟨fun y =>
    (isIntegral_algHom_iff θ'.range.val Subtype.val_injective).1
      (Algebra.IsAlgebraic.isAlgebraic (y : K)).isIntegral⟩
  have : Module.Finite k θ'.range := Algebra.IsIntegral.finite
  have hsub : (F.pointResidueField p hp).toSubalgebra ≤ θ'.range := by
    intro e he
    obtain ⟨r, rfl⟩ := he
    obtain ⟨t, rfl⟩ := F.model.residue_surjective x r
    rw [← CommRingCat.comp_apply, Scheme.residue_descResidueField]
    let := TopCat.Presheaf.algebra_section_stalk F.model.presheaf (⟨x, hxV⟩ : V)
    have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl t
    have hgerm : ∀ b, (Scheme.stalkClosedPointTo q).hom
        (algebraMap Γ(F.model, V) (F.model.presheaf.stalk x) b) = θ b :=
      fun b => (ΓSpecIso_appLE_eq q V hVq b).symm
    have hunit : IsUnit (θ s) := by
      rw [← hgerm]; exact (IsLocalization.map_units _ s).map _
    have heq : (Scheme.stalkClosedPointTo q).hom (IsLocalization.mk' _ a s) = θ a * (θ s)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hunit.ne_zero, ← hgerm, ← hgerm, ← map_mul,
        IsLocalization.mk'_spec]
    rw [heq]
    exact θ'.range.mul_mem ⟨a, rfl⟩ (Subalgebra.inv_mem_of_algebraic θ'.range
      (x := ⟨θ s, s, rfl⟩) (Algebra.IsAlgebraic.isAlgebraic _))
  exact Module.Finite.of_injective (Subalgebra.inclusion hsub).toLinearMap
    (Subalgebra.inclusion_injective hsub)

end FieldOfDefinition

section Helpers

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section ImagePoint

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
  [IsProjectiveVariety K f] {n : ℕ}

/-- The image `φ(p) ∈ ℙ K (Fin (n + 1) → K)` of a `K`-point `p` under a projective embedding,
read through the dictionary of `ProjectiveEmbedding.height`. -/
private noncomputable def imagePoint (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) : ℙ K (Fin (n + 1) → K) :=
  let b := Pi.basisFun K (Fin (n + 1))
  let q : Spec (.of K) ⟶ projectiveSpaceOfModule K (Fin (n + 1) → K) :=
    p.1 ≫ φ.hom ≫ (projectiveSpaceOfModuleIso b).inv
  have hq : q ≫ projectiveSpaceOfModuleToSpec K (Fin (n + 1) → K) = 𝟙 _ := by
    simp only [q, Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
    rw [φ.hom_over, p.2]
  (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual K _
      (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient K _ ⟨q, hq⟩)).map
    b.toDualEquiv.symm.toLinearMap b.toDualEquiv.symm.injective

/-- The height of `p` relative to `φ` is the Weil height of `imagePoint φ p`. -/
private theorem height_eq [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] [Smooth f]
    (φ : ProjectiveEmbedding f n) (p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) :
    φ.height p = weilHeight (imagePoint φ p) := rfl

/-- A closed immersion is a monomorphism, so `imagePoint φ` is injective. -/
private theorem imagePoint_injective (φ : ProjectiveEmbedding f n) :
    Function.Injective (imagePoint φ) := by
  have := φ.isClosedImmersion
  intro p₁ p₂ h
  have h1 := Projectivization.map_injective _
    (Pi.basisFun K (Fin (n + 1))).toDualEquiv.symm.injective h
  have h2 := congrArg Subtype.val
    ((ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient K _).injective
      ((ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual K _).injective h1))
  exact Subtype.ext ((cancel_mono φ.hom).1
    ((cancel_mono _).1 (by simpa only [Category.assoc] using h2)))

/-- In a chart `D₊(Tᵢ)` containing it, `φ(p)` is the class of its affine coordinates. -/
private theorem imagePoint_eq_mk_chartVal (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) (i : Fin (n + 1))
    (hi : ⊤ ≤ ((p.1 ≫ φ.hom) ≫ (polynomialComparison K n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K n) (MvPolynomial.X i)) :
    imagePoint φ p = Projectivization.mk K (chartVal _ i hi) (chartVal_ne_zero _ i hi) := by
  refine dictionary_eq_mk_chartVal (p.1 ≫ φ.hom) _ (Category.assoc _ _ _).symm ?_ i hi
  have h := (polynomialComparison K n).toBase
  simp only [Category.assoc, projToSpecCoeff] at h ⊢
  rw [h]
  exact (congrArg (p.1 ≫ ·) φ.hom_over).trans p.2

/-- When `φ` is defined over `k`, the affine coordinates of `φ(p)` lie in the residue field
`k(p)`: they are values at `p` of sections of `ℙⁿ_ℤ` pulled back along the model. -/
private theorem chartVal_mem {k : Type u} [Field k] [NumberField k] [Algebra k K]
    (F : FieldOfDefinition K f k) (φ : ProjectiveEmbedding f n)
    (hφ : ∃ ψ : F.model ⟶ projectiveSpaceAtUniverse.{u} n,
      φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        F.iso.hom ≫ pullback.fst _ _ ≫ ψ)
    (p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) (i : Fin (n + 1))
    (hi : ⊤ ≤ ((p.1 ≫ φ.hom) ≫ (polynomialComparison K n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K n) (MvPolynomial.X i)) (j : Fin (n + 1)) :
    chartVal _ i hi j ∈ F.pointResidueField p.1 p.2 := by
  obtain ⟨ψ, hψ⟩ := hφ
  set w := (p.1 ≫ φ.hom) ≫ (polynomialComparison K n).iso.hom
  set cpm := coordinateProjMap K n (integralGradedHom K n) (mapDomain_integralGradedHom_eq_top K n)
  have he : Proj.basicOpen (polyGrading K n) (MvPolynomial.X i) ≤
      cpm ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) :=
    (Stacks.ProjectiveSpaceChartRatio.coordinateProjMap_preimage_basicOpen K n i).ge
  have hwc : w ≫ cpm = (p.1 ≫ F.iso.hom ≫ pullback.fst _ _) ≫ ψ := by
    simp only [w, cpm, Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_coordinateProjMap, hψ]
  have key : ∀ h', chartVal w i hi j = (Scheme.ΓSpecIso (.of K)).hom ((w ≫ cpm).appLE _ ⊤ h'
      ((Proj.awayToSection (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)).hom
        (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j))) := by
    intro h'
    unfold chartVal
    rw [← Stacks.ProjectiveSpaceChartRatio.chartBaseChange_coordFracAt,
      ← Stacks.ProjectiveSpaceChartRatio.appLE_awayToSection_coordinateProjMap K n i he,
      ← Scheme.Hom.appLE_comp_appLE w cpm _ _ ⊤ he hi]
    rfl
  have h' : ⊤ ≤ (w ≫ cpm) ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) :=
    fun x hx => he (hi hx)
  rw [key h']
  revert h'
  rw [hwc]
  intro h'
  exact ΓSpecIso_appLE_comp_mem _ ψ _ h' _

/-- **The degree bound.** When `φ` is defined over `k`, the field `ℚ(φ(p))` lies in `k(p)`, so
`[ℚ(φ(p)) : ℚ] ≤ [k(p) : k] [k : ℚ]`. -/
private theorem degreeOfPoint_imagePoint_le {k : Type u} [Field k] [NumberField k] [Algebra k K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (F : FieldOfDefinition K f k) (φ : ProjectiveEmbedding f n)
    (hφ : ∃ ψ : F.model ⟶ projectiveSpaceAtUniverse.{u} n,
      φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        F.iso.hom ≫ pullback.fst _ _ ≫ ψ)
    (p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) :
    degreeOfPoint ℚ (imagePoint φ p) ≤
      F.pointDegree p.1 p.2 * Module.finrank ℚ k := by
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.tower_top (K := ℚ) k
  have := F.finiteDimensional_pointResidueField p.1 p.2
  set E := F.pointResidueField p.1 p.2
  obtain ⟨i, hi⟩ := exists_mem_basicOpen (p.1 ≫ φ.hom) (IsLocalRing.closedPoint K)
  replace hi : ⊤ ≤ ((p.1 ≫ φ.hom) ≫ (polynomialComparison K n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K n) (MvPolynomial.X i) := fun a _ => by
    rwa [Subsingleton.elim a (IsLocalRing.closedPoint K)]
  have hle : pointField ℚ (imagePoint φ p) ≤ E.restrictScalars ℚ := by
    rw [pointField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, b, hb, rfl⟩
    rw [imagePoint_eq_mk_chartVal φ p i hi] at hb ⊢
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K (chartVal _ i hi)
      (chartVal_ne_zero _ i hi)
    rw [← hc] at hb ⊢
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hb ⊢
    rw [mul_div_mul_left _ _ c.ne_zero]
    exact E.div_mem (chartVal_mem F φ hφ p i hi a) (chartVal_mem F φ hφ p i hi b)
  have : FiniteDimensional ℚ E := Module.Finite.trans k E
  have : FiniteDimensional ℚ (E.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ E)
  calc degreeOfPoint ℚ (imagePoint φ p) ≤ Module.finrank ℚ (E.restrictScalars ℚ) :=
        IntermediateField.finrank_le_of_le_right hle
    _ = _ := (Module.finrank_mul_finrank ℚ k E).symm.trans (mul_comm _ _)

end ImagePoint

end Helpers

/-- **Weil's theorem (Northcott property).** Let `X` be a smooth projective variety over an
algebraic extension `K / ℚ`, `F` a field of definition `k` of `X` (a number field), and
`φ : X ⟶ ℙⁿ_K` a projective embedding defined over `k`. Then for all `δ ≥ 1` and `B : ℝ` there
are only finitely many `K`-points `p` of `X` with `[k(p) : k] ≤ δ` and `h_φ(p) ≤ B`. -/
@[faltings "thm_ht_weil_northcott"]
public theorem ProjectiveEmbedding.finite_setOf_pointDegree_le_height_le {K : Type u} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
    [IsProjectiveVariety K f] [Smooth f] {k : Type u} [Field k] [NumberField k] [Algebra k K]
    (F : FieldOfDefinition K f k) {n : ℕ} (φ : ProjectiveEmbedding f n)
    (hφ : ∃ ψ : F.model ⟶ projectiveSpaceAtUniverse.{u} n,
      φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        F.iso.hom ≫ pullback.fst _ _ ≫ ψ)
    {δ : ℕ} (hδ : 1 ≤ δ) (B : ℝ) :
    {p : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} |
      F.pointDegree p.1 p.2 ≤ δ ∧ φ.height p ≤ B}.Finite := by
  have hT := finite_setOf_weilHeight_le_of_degreeOfPoint_le (K := K) (ι := Fin (n + 1))
    (le_max_right B 0) (Nat.mul_le_mul hδ (Module.finrank_pos (R := ℚ) (M := k)))
  refine (hT.preimage (imagePoint_injective φ).injOn).subset fun p hp => ?_
  refine ⟨(height_eq φ p ▸ hp.2).trans (le_max_left _ _), ?_⟩
  exact (degreeOfPoint_imagePoint_le F φ hφ p).trans (Nat.mul_le_mul_right _ hp.1)

end Faltings
