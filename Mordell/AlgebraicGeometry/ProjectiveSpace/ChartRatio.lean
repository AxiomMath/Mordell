module

public import Mordell.BombieriVojta.Height.Basic
public import Mordell.BombieriVojta.Taylor.MonomialBound
public import Mordell.BombieriVojta.Taylor.SeparatedVariables
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Weil.Representative
public import Mordell.BombieriVojta.TripleFunction.FirstCoefficient
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.Height.Machine.IsomorphicPullbacks

/-!
# Chart ratios of morphisms to `ℙʳ_K` and homogeneous coordinates of points

For `f : Y ⟶ ℙʳ_K`: the pulled-back chart `chartOf`, the germ `ratioOf` of `T_ν / T_j`, the
predicate `IsCoordinatesOf` for coordinate vectors of `K`-points `q ≫ f`, and the homogeneous
coordinates of `k`-points of `ℙʳ_k` under the `𝐏(k^{r+1}) ≅ ℙʳ_k` dictionary.
-/

open Faltings (chartVal_eq_of_comp chartVal_self iota_mem_iff mem_asHomogeneousIdeal_iff_eval_chartVal)
open Faltings.BombieriVojta (const_comp const_eq ev_const exists_stalk_hom ext_of_germ ne_zero_of_maximalIdeal_eq stalkClosedPointTo_comp_over_germ stalkCongr_const)

open Faltings (chartVal coordPoint exists_mem_basicOpen toDualEquiv_apply_apply top_le_preimage_of_mem)
open Faltings.BombieriVojta (const ev_eq_zero_of_mem stalkClosedPointTo_fromSpecStalk_eq stalkClosedPointTo_germ_of_eq)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing _root_.NumberField Module
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings.BombieriVojta.HeightLowerBound

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

section ProjCharts

open HomogeneousLocalization in
/-- `(g / f) · (f / g) = 1` in a homogeneous localization in which `f` and `g` are inverted. -/
public lemma mapId_mul_mapId {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
    {P : Submonoid A} {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hf' : f ∈ 𝒜 (1 • 1))
    (hg' : g ∈ 𝒜 (1 • 1)) (hfP : Submonoid.powers f ≤ P) (hgP : Submonoid.powers g ≤ P) :
    mapId 𝒜 hfP (Away.mk 𝒜 hf 1 g hg') * mapId 𝒜 hgP (Away.mk 𝒜 hg 1 f hf') = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_one]
  change Localization.mk g ⟨f ^ 1, hfP ⟨1, rfl⟩⟩ * Localization.mk f ⟨g ^ 1, hgP ⟨1, rfl⟩⟩ = 1
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one, mul_one]
  exact mul_comm _ _

open HomogeneousLocalization in
/-- On `D₊(T_j) ∩ D₊(T_k)` the functions `T_k / T_j` and `T_j / T_k` are inverse to each other:
the product of their germs at a common point is `1`. -/
public lemma germ_ratio_mul_germ_ratio (r : ℕ) (j k : Fin (r + 1))
    (x : letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)))
    (hj : letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j))
    (hk : letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
      x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)) :
    letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
    (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).presheaf.germ _ x hj
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1
            (MvPolynomial.X k) (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k))) *
      (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).presheaf.germ _ x hk
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k) 1
            (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))) =
        1 := by
  letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
  have e1 := congr($(ProjectiveSpectrum.Proj.awayToSection_germ
    (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (MvPolynomial.X j) x hj)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1
            (MvPolynomial.X k) (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k)))
  have e2 := congr($(ProjectiveSpectrum.Proj.awayToSection_germ
    (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (MvPolynomial.X k) x hk)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k) 1
            (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  erw [e1, e2, CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul]
  refine (congrArg _ ?_).trans (map_one _)
  exact mapId_mul_mapId _ _ _ _ _ (Submonoid.powers_le.mpr hj) (Submonoid.powers_le.mpr hk)

end ProjCharts

section Charts

variable {K : Type u} [Field K]

/-- The chart `D₊(T_j)` of the integral model of `ℙʳ`, pulled back along `f`. -/
@[expose] public noncomputable def chartOf {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K)))
    (j : Fin (r + 1)) : Y.Opens :=
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  (f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X j)

/-- The germ at `y` of the pull-back along `f` of `T_ν / T_j` (zero off the chart). -/
@[expose] public noncomputable def ratioOf {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (y : Y) (ν j : Fin (r + 1)) :
    Y.presheaf.stalk y :=
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  haveI := Classical.propDecidable (y ∈ chartOf f j)
  if h : y ∈ chartOf f j then
    Y.presheaf.germ (chartOf f j) y h
      ((f ≫ projectiveSpaceOver.toIntegralAtUniverse r _).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))
  else 0

/-- On the overlap of two charts, `(T_k / T_j) (T_j / T_k) = 1`. -/
public lemma ratioOf_mul_ratioOf {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) {y : Y} {j k : Fin (r + 1)}
    (hj : y ∈ chartOf f j) (hk : y ∈ chartOf f k) :
    ratioOf f y k j * ratioOf f y j k = 1 := by
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  simp only [ratioOf, dif_pos hj, dif_pos hk]
  have e := fun (U : (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1))
      (ULift.{u} ℤ))).Opens) (hU : (f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) y ∈ U) t =>
    congr($(Scheme.Hom.germ_stalkMap (f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) U y hU) t)
  simp only [CommRingCat.comp_apply] at e
  refine Eq.trans (congrArg₂ (· * ·) (e _ hj _).symm (e _ hk _).symm) ?_
  rw [← map_mul]
  exact (congrArg _ (germ_ratio_mul_germ_ratio r j k _ hj hk)).trans (map_one _)

/-- The nonzero vector `a` is a coordinate vector of the `K`-point `q ≫ f` of `ℙʳ`. -/
@[expose] public def IsCoordinatesOf {Y : Scheme.{u}} {r : ℕ} (f : Y ⟶ projectiveSpaceOver r (Spec (.of K)))
    (q : Spec (.of K) ⟶ Y) (a : Fin (r + 1) → K) : Prop :=
  a ≠ 0 ∧ ∀ j, a j ≠ 0 → q (closedPoint K) ∈ chartOf f j ∧
    ∀ ν, (Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν j) = a ν / a j

/-- A coordinate of a point lying on the chart `D₊(T_k)` is nonzero. -/
public lemma IsCoordinatesOf.ne_zero {Y : Scheme.{u}} {r : ℕ}
    {f : Y ⟶ projectiveSpaceOver r (Spec (.of K))} {q : Spec (.of K) ⟶ Y} {a : Fin (r + 1) → K}
    (ha : IsCoordinatesOf f q a) {k : Fin (r + 1)} (hk : q (closedPoint K) ∈ chartOf f k) :
    a k ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha.1
  obtain ⟨hjc, hjr⟩ := ha.2 j hj
  have h1 := congrArg (Scheme.stalkClosedPointTo q).hom (ratioOf_mul_ratioOf f hjc hk)
  rw [map_mul, map_one, hjr k] at h1
  intro h0
  rw [h0, zero_div, zero_mul] at h1
  exact zero_ne_one h1

/-- On any chart `D₊(T_k)` containing the point, `a_ν = a_k (T_ν / T_k)(q)`. -/
public lemma IsCoordinatesOf.eq_mul {Y : Scheme.{u}} {r : ℕ}
    {f : Y ⟶ projectiveSpaceOver r (Spec (.of K))} {q : Spec (.of K) ⟶ Y} {a : Fin (r + 1) → K}
    (ha : IsCoordinatesOf f q a) {k : Fin (r + 1)} (hk : q (closedPoint K) ∈ chartOf f k)
    (ν : Fin (r + 1)) :
    a ν = a k * (Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν k) := by
  rw [(ha.2 k (ha.ne_zero hk)).2 ν, mul_div_cancel₀ _ (ha.ne_zero hk)]

/-- Pulling the chart functions back along a morphism. -/
public lemma ratioOf_comp {Y Z : Scheme.{u}} {r : ℕ} (h : Y ⟶ Z)
    (f : Z ⟶ projectiveSpaceOver r (Spec (.of K))) (g : Y ⟶ projectiveSpaceOver r (Spec (.of K)))
    (hg : g = h ≫ f) (y : Y) (ν k : Fin (r + 1)) :
    ratioOf g y ν k = h.stalkMap y (ratioOf f (h y) ν k) := by
  subst hg
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  by_cases hk : h y ∈ chartOf f k
  · have hk' : y ∈ chartOf (h ≫ f) k := hk
    simp only [ratioOf, dif_pos hk, dif_pos hk']
    have e := congr($(Scheme.Hom.germ_stalkMap h (chartOf f k) y hk)
      (((f ≫ projectiveSpaceOver.toIntegralAtUniverse r _).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))))
    simp only [CommRingCat.comp_apply] at e
    exact e.symm
  · have hk' : y ∉ chartOf (h ≫ f) k := hk
    simp only [ratioOf, dif_neg hk, dif_neg hk', map_zero]

/-- The germ of the pull-back of `T_ν / T_k` along `f` is `ratioOf f y ν k` on the chart. -/
public lemma germ_app_eq_ratioOf {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (y : Y) (k ν : Fin (r + 1))
    (hk : letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
      y ∈ f ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of K)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k))) :
    letI := (MvPolynomial.gradedAlgebra (σ := Fin (r + 1)) (R := ULift.{u} ℤ))
    Y.presheaf.germ _ y hk (f.app _ ((projectiveSpaceOver.toIntegralAtUniverse r _).app _
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)
        (HomogeneousLocalization.Away.mk _
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k) 1 (MvPolynomial.X ν)
          (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))) =
      ratioOf f y ν k := by
  have hk' : y ∈ chartOf f k := hk
  simp only [ratioOf, dif_pos hk']
  rfl

/-- A coordinate vector of `p ≫ h` for `f` is a representative, in the sense of the value
formula, of `p` for `g = h ≫ f`. -/
public lemma IsCoordinatesOf.eq_mul_comp {X Y : Scheme.{u}} {r : ℕ} (h : X ⟶ Y)
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (g : X ⟶ projectiveSpaceOver r (Spec (.of K)))
    (hg : g = h ≫ f) (p : Spec (.of K) ⟶ X) {a : Fin (r + 1) → K}
    (ha : IsCoordinatesOf f (p ≫ h) a) {k : Fin (r + 1)} (hk : p (closedPoint K) ∈ chartOf g k)
    (ν : Fin (r + 1)) :
    a ν = a k * (Scheme.stalkClosedPointTo p).hom (ratioOf g (p (closedPoint K)) ν k) := by
  have hk' : (p ≫ h) (closedPoint K) ∈ chartOf f k := by subst hg; exact hk
  rw [ha.eq_mul hk' ν, ratioOf_comp h f g hg, Scheme.stalkClosedPointTo_comp]
  rfl

/-- Constants through a morphism equal to the structure morphism. -/
public lemma appTop_germ_eq_const {X : Scheme.{u}} [X.Over (Spec (.of K))]
    (h : X ⟶ Spec (.of K)) (hh : h = X ↘ Spec (.of K)) (x : X) (t : Γ(Spec (.of K), ⊤)) :
    (h.appTop ≫ X.presheaf.germ ⊤ x trivial).hom t =
      const x ((Scheme.ΓSpecIso (.of K)).hom t) := by
  subst hh
  have e : (Scheme.ΓSpecIso (.of K)).inv ((Scheme.ΓSpecIso (.of K)).hom t) = t :=
    Iso.hom_inv_id_apply _ _
  exact (congrArg (fun s => ((X ↘ Spec (.of K)).appTop ≫
    X.presheaf.germ ⊤ x trivial).hom s) e).symm

end Charts

section HomogeneousCoordinates

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section RationalPoints

open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The `k`-point `t(p)` of `𝐏(k^{r+1})` attached to a `k`-point `p` of `X` and a morphism
`t : X ⟶ ℙʳ_k` over `Spec k`. -/
@[expose] public noncomputable def kPoint {f : X ⟶ Spec (.of k)} {r : ℕ}
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (ht : t ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) = f)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) :
    {q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (r + 1) → k) //
      q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _} :=
  ⟨p.1 ≫ t ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (r + 1)))).inv.left, by
    show p.1 ≫ (t ≫ (projectiveSpaceOfModuleIso (Pi.basisFun k (Fin (r + 1)))).inv) ≫
      projectiveSpaceOfModuleToSpec k _ = _
    rw [Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec, ht, p.2]⟩

/-- The homogeneous coordinates of `t(p)` are the chart values of `p ≫ t` in any chart
containing it. -/
public theorem coordPoint_kPoint {f : X ⟶ Spec (.of k)} {r : ℕ}
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (ht : t ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) = f)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) (i : Fin (r + 1))
    (hi : ⊤ ≤ ((p.1 ≫ t) ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i)) :
    coordPoint (kPoint t ht p) =
      Projectivization.mk k (chartVal _ i hi) (chartVal_ne_zero _ i hi) :=
  dictionary_eq_mk_chartVal (p.1 ≫ t) _ (Category.assoc _ _ _).symm
    (by rw [Category.assoc, Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff, Category.assoc]; erw [ht]; rw [p.2]) i hi

end RationalPoints

end HomogeneousCoordinates

end Faltings.BombieriVojta.HeightLowerBound
