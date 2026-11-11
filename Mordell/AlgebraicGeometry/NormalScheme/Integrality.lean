module

public import Mordell.BombieriVojta.Norm.ReducedRepresentation
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycleSupplement
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.Curve.Topology
public import Mordell.AlgebraicGeometry.NormalScheme.Order

/-!
# Regularity of coordinates and integrality on normal curves

Regular points of a chart function of a morphism to `ℙⁿ` lie in its chart, functions regular
wherever `ζ` is regular are integral over `k[ζ]` on a proper normal curve, and regularity and
integrality are transported along morphisms of integral schemes and algebraic evaluations.
-/

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order

universe u

attribute [local instance] MvPolynomial.gradedAlgebra in
open Stacks.SectionsToProjectiveSpace in
/-- **Regular points of `ξ_a` lie in the chart `D₊(T₀)`.** Let `φ : C ⟶ ℙⁿ_S` be a morphism from a
normal curve whose chart functions `T_ν / T_j` are `x_ν / x_j`, where the `x j` are sections
of `𝒪(E)` with `x 0, x a` without common zero. If `x a / x 0` is regular at `c`, then `φ c` lies
in the standard open `D₊(T₀)`. -/
public theorem mem_preimage_basicOpen_of_mem_range {k : Type u} [Field k] {C : Scheme.{u}}
    [IsLocallyNoetherian C] [IsNormal C] (f₀ : C ⟶ Spec (.of k)) [IsCurve k f₀]
    {n : ℕ} (E : C → ℤ) (x : Fin (n + 1) → C.functionField) (hx : ∀ j, x j ≠ 0)
    (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z) {S : Scheme.{u}}
    (φ : C ⟶ projectiveSpaceOver n S)
    (hφ : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let U : Fin (n + 1) → C.Opens := fun j =>
        φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φ.app _ ((projectiveSpaceOver.toIntegralAtUniverse n S).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    {a : Fin (n + 1)}
    (hG1 : ∀ z, Order.coheight z = 1 → C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    {c : C} (hc : x a / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField)) :
    c ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)
  set ψ : C ⟶ AlgebraicGeometry.Proj 𝒜 := φ ≫ projectiveSpaceOver.toIntegralAtUniverse n S
    with hψ
  change c ∈ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0)
  have hX : ∀ i, MvPolynomial.X i ∈ 𝒜 1 := fun i => MvPolynomial.isHomogeneous_X _ i
  have hX' : ∀ i, MvPolynomial.X i ∈ 𝒜 (1 • 1) := fun i => by simpa using hX i
  obtain ⟨hg0, hξ⟩ := BombieriRoth.exists_germ_app_ratio_eq_div_of_chart φ x hx hφ 0
  change genericPoint C ∈ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) at hg0
  have hξ' : ∀ j, C.presheaf.germ _ (genericPoint C) hg0 (ψ.app _ (Proj.awayToSection 𝒜
      (MvPolynomial.X 0) (HomogeneousLocalization.Away.mk 𝒜 (hX 0) 1 (MvPolynomial.X j)
        (hX' j)))) = x j / x 0 := hξ
  have hgen : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  by_contra hc0
  have hcg : c ≠ genericPoint C := fun h => hc0 (h ▸ hg0)
  have hc1 : Order.coheight c = 1 := IsCurve.coheight_eq_one f₀ hcg
  have hord : 0 ≤ C.ord (x a / x 0) c :=
    (ord_nonneg_iff hc1 (div_ne_zero (hx a) (hx 0))).mpr hc
  rw [ord_div (hx a) (hx 0)] at hord
  have h0 : C.ord (x 0) c + E c = 0 := by
    rcases hG1 c hc1 with h | h
    · exact h
    · have := hxE 0 c
      omega
  have hreg : ∀ j, x j / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) :=
    fun j => by
      refine (ord_nonneg_iff hc1 (div_ne_zero (hx j) (hx 0))).mp ?_
      rw [ord_div (hx j) (hx 0)]
      have := hxE j c
      omega
  have hy0 : MvPolynomial.X 0 ∈ (ψ c).asHomogeneousIdeal := by
    by_contra h
    exact hc0 h
  obtain ⟨j, hj⟩ : ∃ j, φ c ∈ ProjectiveSpace.standardOpen n S j :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [ProjectiveSpace.iSup_standardOpen_eq_top]; trivial)
  change ψ c ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) at hj
  have hcj : c ∈ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := hj
  have hnu : ¬ IsUnit (C.presheaf.germ _ c hcj (ψ.app _ (Proj.awayToSection 𝒜 (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X 0) (hX' 0))))) := by
    rw [(Scheme.Hom.germ_stalkMap_apply ψ _ c hcj _).symm]
    intro hu
    have hu' := isUnit_of_map_unit (ψ.stalkMap c).hom _ hu
    exact ((isUnit_germ_awayToSection_iff 𝒜 (hX j) 1 _ (hX' 0) (ψ c) hj).mp hu') hy0
  have hgj : genericPoint C ∈ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := hgen _ ⟨c, hcj⟩
  have hrel : C.presheaf.germ _ (genericPoint C) hgj (ψ.app _ (Proj.awayToSection 𝒜
      (MvPolynomial.X j) (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X 0)
        (hX' 0)))) * (x j / x 0) = 1 := by
    rw [← hξ' j]
    change C.presheaf.germ _ (genericPoint C) hgj _ * C.presheaf.germ _ (genericPoint C) hg0 _ = 1
    rw [(Scheme.Hom.germ_stalkMap_apply ψ _ _ hgj _).symm,
      (Scheme.Hom.germ_stalkMap_apply ψ _ _ hg0 _).symm, ← RingHom.map_mul]
    exact (congrArg (ψ.stalkMap (genericPoint C))
      (germ_mul_germ_awayToSection 𝒜 (hX j) (hX 0) (hX' j) (hX' 0) (ψ (genericPoint C)) hgj
        hg0)).trans (map_one _)
  obtain ⟨t, ht⟩ := hreg j
  apply hnu
  refine isUnit_iff_exists_inv.mpr ⟨t, ?_⟩
  apply IsFractionRing.injective (C.presheaf.stalk c) C.functionField
  have : Nonempty (ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) := ⟨⟨_, hgj⟩⟩
  rw [RingHom.map_mul, ht, Scheme.algebraMap_germ_eq_germToFunctionField, RingHom.map_one]
  exact hrel

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}}

variable [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] (f₀ : C ⟶ Spec (.of k))
  [IsCurve k f₀]

include f₀ in
/-- On a normal curve, a rational function is regular at `c` or its inverse vanishes at `c`. -/
public theorem mem_range_or_exists_mem_maximalIdeal (c : C) (h : C.functionField) :
    h ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) ∨
      ∃ t ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk c),
        algebraMap (C.presheaf.stalk c) C.functionField t * h = 1 := by
  by_cases hc : c = genericPoint C
  · left
    subst hc
    refine ⟨h, ?_⟩
    change (C.presheaf.stalkSpecializes _).hom h = h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    (IsCurve.coheight_eq_one f₀ hc)
  by_cases hmem : h ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField)
  · exact Or.inl hmem
  right
  have h0 : h ≠ 0 := fun h0 => hmem ⟨0, by rw [h0, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk c) h with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact absurd ⟨t, ht⟩ hmem
  refine ⟨t, ?_, by rw [ht, inv_mul_cancel₀ h0]⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem
  refine ⟨↑hu.unit⁻¹, ?_⟩
  rw [← inv_inv h, ← ht]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← RingHom.map_mul, IsUnit.val_inv_mul, RingHom.map_one]

/-- **Integrality of the sections of a chart.** Let `C` be a proper normal curve over `k` and `U`
an open containing every point at which `ξ` is regular. Then every section of `𝒪_C` over `U` is
integral over `k[ξ]`. -/
public theorem germToFunctionField_mem_integralClosure [IsProper f₀] [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f₀.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ξ : C.functionField) (U : C.Opens) [Nonempty U]
    (hU : ∀ c : C, ξ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ U)
    (s : Γ(C, U)) :
    C.germToFunctionField U s ∈ integralClosure (Algebra.adjoin k {ξ}) C.functionField := by
  by_contra hns
  obtain ⟨V, hTV, hsV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure (Algebra.adjoin k {ξ}) C.functionField).toSubring) hns
  have hRV : ∀ y ∈ Algebra.adjoin k {ξ}, y ∈ V := fun y hy =>
    hTV (show algebraMap (Algebra.adjoin k {ξ}) C.functionField ⟨y, hy⟩ ∈
      integralClosure (Algebra.adjoin k {ξ}) C.functionField from
      Subalgebra.algebraMap_mem _ _)
  have hV : ∀ c : k, C.presheaf.germ ⊤ (genericPoint C) trivial
      (f₀.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) ∈ V := fun c => by
    rw [← hkC]
    exact hRV _ (Subalgebra.algebraMap_mem _ c)
  obtain ⟨c, ρ, hρl, hρ⟩ := exists_isLocalHom_stalk f₀ V hV
  have hξV : ξ ∈ V := hRV ξ (Algebra.subset_adjoin rfl)
  have hξc : ξ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) := by
    refine (mem_range_or_exists_mem_maximalIdeal (C := C) f₀ c ξ).resolve_right ?_
    rintro ⟨t, ht, htξ⟩
    refine (IsLocalRing.mem_maximalIdeal _).mp ht (isUnit_of_map_unit ρ t ?_)
    refine isUnit_iff_exists_inv.mpr ⟨⟨ξ, hξV⟩, Subtype.ext ?_⟩
    change (ρ t : C.functionField) * ξ = 1
    rw [hρ, htξ]
  have hcU := hU c hξc
  apply hsV
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := C) hcU, ← hρ]
  exact (ρ _).2

/-- **Integrality from orders of vanishing.** On a proper normal curve over `k`, if a rational
function `w` is regular at every codimension-one point at which `ζ` is regular, then `w` is
integral over `k[ζ]`. -/
public theorem mem_integralClosure_of_ord_nonneg [IsProper f₀] [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f₀.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {ζ w : C.functionField} (hζ : ζ ≠ 0) (hw : w ≠ 0)
    (h : ∀ c : C, coheight c = 1 → 0 ≤ C.ord ζ c → 0 ≤ C.ord w c) :
    w ∈ integralClosure (Algebra.adjoin k {ζ}) C.functionField := by
  by_contra hns
  obtain ⟨V, hTV, hsV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure (Algebra.adjoin k {ζ}) C.functionField).toSubring) hns
  have hRV : ∀ y ∈ Algebra.adjoin k {ζ}, y ∈ V := fun y hy =>
    hTV (show algebraMap (Algebra.adjoin k {ζ}) C.functionField ⟨y, hy⟩ ∈
      integralClosure (Algebra.adjoin k {ζ}) C.functionField from
      Subalgebra.algebraMap_mem _ _)
  have hV : ∀ c : k, C.presheaf.germ ⊤ (genericPoint C) trivial
      (f₀.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) ∈ V := fun c => by
    rw [← hkC]
    exact hRV _ (Subalgebra.algebraMap_mem _ c)
  obtain ⟨c, ρ, hρl, hρ⟩ := exists_isLocalHom_stalk f₀ V hV
  have hζc : ζ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) := by
    refine (mem_range_or_exists_mem_maximalIdeal f₀ c ζ).resolve_right ?_
    rintro ⟨t, ht, htζ⟩
    refine (IsLocalRing.mem_maximalIdeal _).mp ht (isUnit_of_map_unit ρ t ?_)
    refine isUnit_iff_exists_inv.mpr ⟨⟨ζ, hRV ζ (Algebra.subset_adjoin rfl)⟩, Subtype.ext ?_⟩
    change (ρ t : C.functionField) * ζ = 1
    rw [hρ, htζ]
  have hwc : w ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) := by
    by_cases hcg : c = genericPoint C
    · subst hcg
      refine ⟨w, ?_⟩
      change (C.presheaf.stalkSpecializes _).hom w = w
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have hc1 := IsCurve.coheight_eq_one f₀ hcg
    exact (ord_nonneg_iff hc1 hw).mp (h c hc1 ((ord_nonneg_iff hc1 hζ).mpr hζc))
  obtain ⟨s, rfl⟩ := hwc
  exact hsV (hρ s ▸ (ρ s).2)

/-- **Integrality from the absence of common zeros.** On a proper normal curve, let `g, g', g''`
be nonzero rational functions with `div g + D, div g' + D, div g'' + D ≥ 0` at every
codimension-one point. If no codimension-one point is a zero of both `div g' + D` and
`div g'' + D`, then every pole of `g / g''` is a pole of `g' / g''`, so `g / g''` is integral over
`k[g' / g'']`. -/
public theorem div_mem_integralClosure_of_not_common_zero [IsProper f₀]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f₀.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {D : C → ℤ} {g g' g'' : C.functionField} (h0 : g ≠ 0) (h0' : g' ≠ 0) (h0'' : g'' ≠ 0)
    (hg : ∀ c, 0 ≤ C.ord g c + D c) (hg' : ∀ c, 0 ≤ C.ord g' c + D c)
    (hg'' : ∀ c, 0 ≤ C.ord g'' c + D c)
    (hno : ∀ c : C, coheight c = 1 → ¬(0 < C.ord g' c + D c ∧ 0 < C.ord g'' c + D c)) :
    g / g'' ∈ integralClosure (Algebra.adjoin k {g' / g''}) C.functionField := by
  refine mem_integralClosure_of_ord_nonneg f₀ hkC (div_ne_zero h0' h0'') (div_ne_zero h0 h0'')
    fun c hc h => ?_
  rw [ord_div h0' h0''] at h
  rw [ord_div h0 h0'']
  have := hno c hc
  have := hg c
  have := hg' c
  have := hg'' c
  omega

end Curve

/-- A morphism `pr : X ⟶ C` of integral schemes whose map `ι` on function fields is compatible
with germs is compatible with the stalk maps. -/
public theorem algebraMap_stalkMap {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (pr : X ⟶ C) (ι : C.functionField →+* X.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = X.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    (q : X) (t : C.presheaf.stalk (pr q)) :
    algebraMap (X.presheaf.stalk q) X.functionField (pr.stalkMap q t) =
      ι (algebraMap (C.presheaf.stalk (pr q)) C.functionField t) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq C.presheaf t
  have : Nonempty U := ⟨⟨pr q, hU⟩⟩
  have : Nonempty (pr ⁻¹ᵁ U) := ⟨⟨q, hU⟩⟩
  have hq : q ∈ pr ⁻¹ᵁ U := hU
  rw [Scheme.Hom.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hq,
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C) hU, hι]

/-- Let `pr : X ⟶ C` be a morphism to a normal curve, with map `ι` on function fields compatible
with germs. A rational function `g` on `C` with `ι g` regular at `q` is regular at `pr q`. -/
public theorem mem_range_stalk_of_map_mem_range {k : Type u} [Field k] {X C : Scheme.{u}}
    [IsIntegral X] [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] (f₀ : C ⟶ Spec (.of k))
    [IsCurve k f₀] (pr : X ⟶ C) (ι : C.functionField →+* X.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = X.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    (q : X) {g : C.functionField}
    (hg : ι g ∈ Set.range (algebraMap (X.presheaf.stalk q) X.functionField)) :
    g ∈ Set.range (algebraMap (C.presheaf.stalk (pr q)) C.functionField) := by
  refine (mem_range_or_exists_mem_maximalIdeal f₀ (pr q) g).resolve_right ?_
  rintro ⟨t, ht, htg⟩
  obtain ⟨t', ht'⟩ := hg
  have h1 : algebraMap (X.presheaf.stalk q) X.functionField (pr.stalkMap q t * t') = 1 := by
    rw [map_mul, algebraMap_stalkMap pr ι hι q t, ht', ← map_mul, htg, map_one]
  have hu : IsUnit (pr.stalkMap q t) := isUnit_iff_exists_inv.mpr
    ⟨t', IsFractionRing.injective (X.presheaf.stalk q) X.functionField (by rw [h1, map_one])⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp ht (isUnit_of_map_unit _ t hu)

/-- In a pushout square of commutative rings, the target is generated by the images of the two
legs: a subring containing both images is everything. -/
public theorem mem_of_isPushout {R S₁ S₂ B : CommRingCat.{u}} {f₁ : R ⟶ S₁} {f₂ : R ⟶ S₂}
    {g₁ : S₁ ⟶ B} {g₂ : S₂ ⟶ B} (h : IsPushout f₁ f₂ g₁ g₂) (T : Subring B)
    (h₁ : ∀ s, g₁ s ∈ T) (h₂ : ∀ s, g₂ s ∈ T) (b : B) : b ∈ T := by
  let i : CommRingCat.of T ⟶ B := CommRingCat.ofHom T.subtype
  let g₁' : S₁ ⟶ CommRingCat.of T := CommRingCat.ofHom (g₁.hom.codRestrict T h₁)
  let g₂' : S₂ ⟶ CommRingCat.of T := CommRingCat.ofHom (g₂.hom.codRestrict T h₂)
  have hw : f₁ ≫ g₁' = f₂ ≫ g₂' := by
    ext x
    exact congr($(h.w).hom x)
  have hid : h.desc g₁' g₂' hw ≫ i = 𝟙 B := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc, Category.comp_id]
      rfl
    · rw [← Category.assoc, h.inr_desc, Category.comp_id]
      rfl
  have hb : (h.desc g₁' g₂' hw ≫ i).hom b = b := by rw [hid]; rfl
  rw [← hb]
  exact (h.desc g₁' g₂' hw b).2

/-- Let `φ : F →ₐ[k] L` and let `ξ ∈ F` with `φ ξ` and the constants in the image of `A → L`.
An element of `F` integral over `k[ξ]` maps to an element of `L` integral over `A`. -/
public theorem isIntegral_map_of_mem_integralClosure {k F L A : Type*} [Field k] [Field F]
    [Field L] [Algebra k F] [Algebra k L] [CommRing A] [Algebra A L] (φ : F →ₐ[k] L) (ξ : F)
    (hξ : φ ξ ∈ Set.range (algebraMap A L))
    (hk : ∀ c : k, algebraMap k L c ∈ Set.range (algebraMap A L)) {y : F}
    (hy : y ∈ integralClosure (Algebra.adjoin k {ξ}) F) : IsIntegral A (φ y) := by
  set T := integralClosure A L
  have hrange : ∀ z ∈ Set.range (algebraMap A L), z ∈ T := by
    rintro _ ⟨a, rfl⟩
    exact Subalgebra.algebraMap_mem _ a
  have hle : ∀ z ∈ Algebra.adjoin k {ξ}, φ z ∈ T := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.mp hz]
      exact hrange _ hξ
    | algebraMap c =>
      rw [AlgHom.commutes]
      exact hrange _ (hk c)
    | add z w _ _ hz hw =>
      rw [map_add]
      exact T.add_mem hz hw
    | mul z w _ _ hz hw =>
      rw [map_mul]
      exact T.mul_mem hz hw
  let θ : Algebra.adjoin k {ξ} →+* T :=
    { toFun := fun z => ⟨φ (z : F), hle z z.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun z w => Subtype.ext (map_mul φ (z : F) w)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun z w => Subtype.ext (map_add φ (z : F) w) }
  obtain ⟨p, hpm, hp⟩ := (show IsIntegral (Algebra.adjoin k {ξ}) y from hy)
  have hT : IsIntegral T (φ y) := by
    refine ⟨p.map θ, hpm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap T L).comp θ =
        φ.toRingHom.comp (algebraMap (Algebra.adjoin k {ξ}) F) := by
      ext z
      rfl
    rw [hcomp, show φ y = φ.toRingHom y from rfl, ← Polynomial.hom_eval₂, hp, map_zero]
  exact isIntegral_trans (R := A) (A := T) (φ y) hT

/-- In a normal local ring of an integral scheme containing the constants, a rational function
`ξ` with `m(ξ)` regular for a monic nonconstant `m ∈ k[X]` is regular. -/
public theorem mem_range_stalk_of_aeval_mem {k : Type*} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [Algebra k X.functionField] (y : X) [IsIntegrallyClosed (X.presheaf.stalk y)]
    (κ : k →+* X.presheaf.stalk y)
    (hκ : (algebraMap (X.presheaf.stalk y) X.functionField).comp κ = algebraMap k X.functionField)
    {ξ : X.functionField} {m : Polynomial k} (hm : m.Monic) (hdeg : m.natDegree ≠ 0)
    (h : Polynomial.aeval ξ m ∈ Set.range (algebraMap (X.presheaf.stalk y) X.functionField)) :
    ξ ∈ Set.range (algebraMap (X.presheaf.stalk y) X.functionField) := by
  have hP : Polynomial.aeval ξ (m.map κ) = Polynomial.aeval ξ m := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hκ]
    rfl
  obtain ⟨g, hg⟩ := h
  have hint : IsIntegral (X.presheaf.stalk y) (Polynomial.aeval ξ (m.map κ)) := by
    rw [hP, ← hg]
    exact isIntegral_algebraMap
  have := IsIntegral.of_aeval_monic (hm.map κ) (by rwa [hm.natDegree_map]) hint
  exact IsIntegrallyClosed.isIntegral_iff.mp this

/-- **Coordinates regular over a point.** Let `X` be a normal scheme whose local rings contain
the constants `k`, `ξ` a family of rational functions and `p` a point with coordinates algebraic
over `k`. If every polynomial vanishing at `p` gives, evaluated at `ξ`, a function of nonnegative
order at the codimension-one generizations of `q`, then every `ξ j` is regular at `q`. -/
public theorem mem_range_stalk_of_forall_aeval {k : Type*} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [Algebra k X.functionField]
    (κ : ∀ y : X, k →+* X.presheaf.stalk y)
    (hκ : ∀ y, (algebraMap (X.presheaf.stalk y) X.functionField).comp (κ y) =
      algebraMap k X.functionField)
    {σ Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] (p : σ → Ω)
    (ξ : σ → X.functionField) (q : X)
    (hq : ∀ r : MvPolynomial σ k, MvPolynomial.aeval p r = 0 →
      ∀ w, w ⤳ q → coheight w = 1 → 0 ≤ X.ord (MvPolynomial.aeval ξ r) w) (j : σ) :
    ξ j ∈ Set.range (algebraMap (X.presheaf.stalk q) X.functionField) := by
  have hpj : IsIntegral k (p j) := (Algebra.IsAlgebraic.isAlgebraic (p j)).isIntegral
  set r : MvPolynomial σ k := Polynomial.aeval (MvPolynomial.X j) (minpoly k (p j))
  have hr : MvPolynomial.aeval p r = 0 := by
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    exact minpoly.aeval k (p j)
  have hrξ : MvPolynomial.aeval ξ r = Polynomial.aeval (ξ j) (minpoly k (p j)) := by
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  refine mem_range_stalk_of_forall_ord_nonneg q fun w hwq hw1 => ?_
  by_cases h0 : ξ j = 0
  · rw [h0]; simp
  have : IsIntegrallyClosed (X.presheaf.stalk w) := IsNormal.stalk_normal w
  refine (ord_nonneg_iff hw1 h0).mpr (mem_range_stalk_of_aeval_mem w _ (hκ w) (minpoly.monic hpj)
    (minpoly.natDegree_pos hpj).ne' ?_)
  rw [← hrξ]
  by_cases h1 : MvPolynomial.aeval ξ r = 0
  · rw [h1]; exact ⟨0, map_zero _⟩
  · exact (ord_nonneg_iff hw1 h1).mp (hq r hr w hwq hw1)

/-- Evaluation of polynomials at a point with coordinates in an algebraic extension `Ω` of `k`
has maximal kernel: its image is a domain algebraic over `k`, hence a field. -/
public theorem isMaximal_ker_aeval {k σ Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (p : σ → Ω) :
    (RingHom.ker (MvPolynomial.aeval (R := k) p)).IsMaximal := by
  let := (Subalgebra.isField_of_algebraic (MvPolynomial.aeval (R := k) p).range).toField
  rw [← AlgHom.ker_rangeRestrict]
  exact RingHom.ker_isMaximal_of_surjective _ (AlgHom.rangeRestrict_surjective _)

end Faltings
