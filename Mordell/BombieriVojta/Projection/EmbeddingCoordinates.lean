module

public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.Height.NPNeronNorm
public import Mordell.Curve.DegreeOverRationalSubfield
public import Mordell.Polynomial.Eisenstein.Finite
public import Mordell.Polynomial.Eisenstein.Infinite
public import Mordell.Height.Affine.Eval
public import Mordell.BombieriVojta.Taylor.AlgebraicFunction
public import Mordell.Height.Affine.Ratio
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Embedding.B
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorGeneration

/-!
# Coordinates of the embeddings `φ_{NP}` and `φ_B`

Sections of an invertible sheaf with a regular meromorphic section, read as a Riemann–Roch space
`L(D)`; a `k`-basis of `L(D)` from a basis of global sections; and the coordinates of the
embeddings `φ_{NP}` of `C` and `φ_B` of `C ×_k C` given by such bases.
-/

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open _root_.NumberField Module

universe u

namespace Faltings.BombieriSiegel

section NPData

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- **Sections of an invertible sheaf as a Riemann–Roch space.** On a normal locally Noetherian
integral scheme `Y`, let `L` be invertible with a regular meromorphic section `s₀` and let `D` be
a Weil divisor whose class is the Weil divisor class of `L`. Then there is `h ≠ 0` with
`D = div h + div s₀`, and the generic coordinates `ρ(t)` (`t ∈ Γ(Y, L)`) against `s₀` are exactly
`h · L(D)`, where `L(D) = {w | w = 0 ∨ ord_Z w + D_Z ≥ 0 for all prime divisors Z}`. -/
public theorem exists_mul_genericCoord_iff {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    [IsNormal Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s₀ : MeromorphicSection Y.sheaf L) (hs₀ : IsRegularMeromorphicSection Y.sheaf L s₀)
    (D : WeilDivisor Y)
    (hD : weilDivisorClassOfInvertibleSheaf Y L = (D : weilDivisorClassGroup Y)) :
    ∃ h : Y.functionField, h ≠ 0 ∧
      (∀ Z, D.val Z = Y.ord h Z.genericPoint + orderOfVanishingMeromorphic Y L s₀ hs₀ Z) ∧
      ∀ w : Y.functionField,
      ((w = 0 ∨ ∀ Z : PrimeDivisor Y, 0 ≤ Y.ord w Z.genericPoint + D.val Z) ↔
        ∃ t : Γ(L, ⊤), Stacks.Zeta.genericCoord Y L s₀ hs₀ t = h * w) := by
  have hdvr : ∀ Z : PrimeDivisor Y, IsDiscreteValuationRing (Y.presheaf.stalk Z.genericPoint) :=
    fun Z => isDiscreteValuationRing_stalk_of_coheight_eq_one (PrimeDivisor.coheight_genericPoint Z)
  set E := weilDivisorOfMeromorphicSection Y L s₀ hs₀
  have hcls : ((D - E : WeilDivisor Y) : weilDivisorClassGroup Y) = 0 := by
    rw [QuotientAddGroup.mk_sub, ← hD, weilDivisorClassOfInvertibleSheaf_eq Y L s₀ hs₀, sub_self]
  obtain ⟨u, hu⟩ := (mk_eq_zero_iff Y _).1 hcls
  set h := (Stacks.Chow.rationalFunctionsEquivFunctionField Y).val (u : _)
  have hh : h ≠ 0 :=
    (u.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField Y).val.toRingHom).ne_zero
  have hDZ : ∀ Z : PrimeDivisor Y, D.val Z = Y.ord h Z.genericPoint +
      orderOfVanishingMeromorphic Y L s₀ hs₀ Z := fun Z => by
    have := congrArg (fun W : WeilDivisor Y => W.val Z) hu
    simp only [principalDivisor_apply] at this
    change Y.ord h Z.genericPoint = D.val Z - E.val Z at this
    rw [this, weilDivisorOfMeromorphicSection_apply]
    ring
  refine ⟨h, hh, hDZ, fun w => ?_⟩
  have key : ∀ Z : PrimeDivisor Y, w ≠ 0 → (0 ≤ Y.ord w Z.genericPoint + D.val Z ↔
      0 ≤ Y.ord (h * w) Z.genericPoint + orderOfVanishingMeromorphic Y L s₀ hs₀ Z) :=
    fun Z hw => by
      rw [Scheme.ord_mul hh hw, hDZ]
      constructor <;> intro <;> linarith
  constructor
  · intro hw
    refine Stacks.Zeta.exists_genericCoord_eq Y L s₀ hs₀ hdvr _ fun Z => ?_
    rcases hw with rfl | hw
    · exact Or.inl (mul_zero h)
    by_cases hw0 : w = 0
    · exact Or.inl (by rw [hw0, mul_zero])
    exact Or.inr ((key Z hw0).1 (hw Z))
  · rintro ⟨t, ht⟩
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    refine Or.inr fun Z => (key Z hw0).2 ?_
    have := hdvr Z
    rcases Stacks.Zeta.genericCoord_mem Y L s₀ hs₀ t Z with h0 | h0
    · exact absurd (ht.symm.trans h0) (mul_ne_zero hh hw0)
    · rwa [ht] at h0

/-- **A basis of `L(D)` read on the sections of `L`.** Over a field `k`, with the
`k`-structure of `k(Y)` that of the structure morphism, a `k`-basis `x` of `L(D)` (`D` of the
class of `L`) comes from a `k`-basis `b` of `Γ(Y, L)`: `ρ(b_a) = h x_a` for some `h ≠ 0`. -/
public theorem exists_basis_genericCoord_eq_mul {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Y.Over (Spec (.of k))]
    [Algebra k Y.functionField]
    (hk : ∀ c : k, algebraMap k Y.functionField c = Y.presheaf.germ ⊤ (genericPoint Y) trivial
      (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k Y c))
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s₀ : MeromorphicSection Y.sheaf L) (hs₀ : IsRegularMeromorphicSection Y.sheaf L s₀)
    (D : WeilDivisor Y)
    (hD : weilDivisorClassOfInvertibleSheaf Y L = (D : weilDivisorClassGroup Y))
    {ι : Type*} (x : ι → Y.functionField) (hx : LinearIndependent k x)
    (hxD : ∀ w : Y.functionField, w ∈ Submodule.span k (Set.range x) ↔
      (w = 0 ∨ ∀ Z : PrimeDivisor Y, 0 ≤ Y.ord w Z.genericPoint + D.val Z)) :
    ∃ h : Y.functionField, h ≠ 0 ∧ ∃ b : Module.Basis ι k Γ(L, ⊤),
      ∀ a, Stacks.Zeta.genericCoord Y L s₀ hs₀ (b a) = h * x a := by
  obtain ⟨h, hh, -, hiff⟩ := exists_mul_genericCoord_iff L s₀ hs₀ D hD
  set ρ := Stacks.Zeta.genericCoord Y L s₀ hs₀
  have ht : ∀ a, ∃ t, ρ t = h * x a := fun a =>
    (hiff _).1 ((hxD _).1 (Submodule.subset_span ⟨a, rfl⟩))
  choose t ht using ht
  have hρsmul : ∀ (c : k) t', ρ (c • t') = c • ρ t' := fun c t' => by
    change ρ ((Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k Y c) •
      t') = _
    refine (Stacks.Zeta.genericCoord_smul Y L s₀ hs₀ _ t').trans ?_
    rw [Algebra.smul_def, hk]
  let ρl : Γ(L, ⊤) →ₗ[k] Y.functionField :=
    { toFun := ρ, map_add' := Stacks.Zeta.genericCoord_add Y L s₀ hs₀, map_smul' := hρsmul }
  have hρinj : Function.Injective ρl := Stacks.Zeta.genericCoord_injective Y L s₀ hs₀
  have hli : LinearIndependent k t := by
    refine LinearIndependent.of_comp ρl ?_
    have h1 : ⇑ρl ∘ t = ⇑(LinearMap.mulLeft k h) ∘ x := funext ht
    rw [h1]
    exact hx.map' _ (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hh))
  have hsp : ⊤ ≤ Submodule.span k (Set.range t) := by
    intro u _
    have hu : h⁻¹ * ρ u ∈ Submodule.span k (Set.range x) :=
      (hxD _).2 ((hiff _).2 ⟨u, by rw [mul_inv_cancel_left₀ hh]⟩)
    have hmap : Submodule.map ρl (Submodule.span k (Set.range t)) =
        Submodule.map (LinearMap.mulLeft k h) (Submodule.span k (Set.range x)) := by
      rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
      exact congrArg _ (congrArg Set.range (funext ht))
    have hmem : ρl u ∈ Submodule.map ρl (Submodule.span k (Set.range t)) := by
      rw [hmap]
      exact ⟨_, hu, by simp [mul_inv_cancel_left₀ hh]; rfl⟩
    obtain ⟨u', hu', he⟩ := hmem
    rwa [← hρinj he]
  exact ⟨h, hh, Module.Basis.mk hli hsp, fun a => by rw [Module.Basis.mk_apply]; exact ht a⟩

/-- **The data of `φ_{NP}` on the basis `x`**: an invertible sheaf `L` of class `N [P]`, a regular
meromorphic section `s₀` of `L`, a nonzero `h ∈ k(C)` and a `k`-basis `b` of `Γ(C, L)` whose
coordinates against `s₀` are `ρ(b_a) = h x_a`. -/
public lemma exists_basis_genericCoord_eq {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (N : ℕ)
    {n : ℕ} (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
    ∃ (L : X.C.Modules) (hLinv : Stacks.Ample.IsInvertibleModule X.C L),
      Stacks.SheafOfModules.picardClass X.C.presheaf
          (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
        (N : ℤ) • X.P.sum (fun x n =>
          haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
          haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
          haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
          n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) ∧
      haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.C.sheaf.obj
        X.C.ringCatSheaf.property L :=
        (show Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatSheaf.2 L
          from hLinv).toAlgebraicGeometry
      ∃ (s₀ : MeromorphicSection X.C.sheaf L) (hs₀ : IsRegularMeromorphicSection X.C.sheaf L s₀)
        (h : X.C.functionField) (b : Module.Basis (Fin (n + 1)) k Γ(L, ⊤)),
        h ≠ 0 ∧ ∀ a, Stacks.Zeta.genericCoord X.C L s₀ hs₀ (b a) = h * x a := by
  let : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have := Stacks.Zeta.isNormal_of_curve X.f
  set D' : Stacks.Zeta.ClosedPoint X.C →₀ ℤ := (N : ℤ) • X.P
  obtain ⟨L, hLinv, hL⟩ : ∃ (L : X.C.Modules) (hLinv : Stacks.Ample.IsInvertibleModule X.C L),
      Stacks.SheafOfModules.picardClass X.C.presheaf
          (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
        Stacks.Zeta.divisorClass X.f D' :=
    ⟨_, (Stacks.Picard.picardRepresentative X.C.toRingedSpace
        (Stacks.Zeta.divisorClass X.f D')).property,
      Stacks.Picard.classOf_picardRepresentative X.C.toRingedSpace _⟩
  refine ⟨L, hLinv, ?_, ?_⟩
  · rw [hL, map_zsmul, Stacks.Zeta.divisorClass_apply]
    rfl
  have hLi : Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatSheaf.2 L := hLinv
  have hAG : AlgebraicGeometry.SheafOfModules.IsInvertible X.C.sheaf.obj
      X.C.ringCatSheaf.property L := hLi.toAlgebraicGeometry
  obtain ⟨s₀, hs₀⟩ := exists_isRegularMeromorphicSection_of_isIntegral X.C L
  refine ⟨s₀, hs₀, ?_⟩
  let := functionFieldAlgebra k X.f
  have hD : weilDivisorClassOfInvertibleSheaf X.C L =
      (Stacks.Zeta.toWeil X.f D' : weilDivisorClassGroup X.C) := by
    rw [← Stacks.Zeta.firstChern_divisorClass X.f D', ← hL]
    exact (weilDivisorClassOfPicardClass_picardClass X.C L).symm
  have hD'Q : ∀ Q : Stacks.Zeta.ClosedPoint X.C,
      D' Q = ((N : ℤ) • X.P.mapDomain Subtype.val) Q.1 := fun Q => by
    simp only [D', Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
  have hxD : ∀ w : X.C.functionField, w ∈ Submodule.span k (Set.range x) ↔
      (w = 0 ∨ ∀ Z : PrimeDivisor X.C,
        0 ≤ X.C.ord w Z.genericPoint + (Stacks.Zeta.toWeil X.f D').val Z) := by
    intro w
    rw [← SetLike.mem_coe, hx.span_eq]
    simp only [Set.mem_ofPred_eq, Stacks.Zeta.toWeil_val_apply]
    refine or_congr Iff.rfl ⟨fun hQ Z => ?_, fun hZ Q hQc => ?_⟩
    · rw [hD'Q]
      exact hQ _ (Stacks.Zeta.closedPointOfPrimeDivisor X.f Z).2
    · have := hZ (Stacks.Zeta.primeDivisorOfClosedPoint X.f ⟨Q, hQc⟩)
      rwa [Stacks.Zeta.closedPointOfPrimeDivisor_primeDivisorOfClosedPoint, hD'Q,
        Stacks.Zeta.primeDivisorOfClosedPoint, PrimeDivisor.genericPoint_ofCoheightOne] at this
  obtain ⟨h, hh, b, hb⟩ := exists_basis_genericCoord_eq_mul (k := k) (fun _ => rfl) L s₀ hs₀
    _ hD x hx.linearIndependent hxD
  exact ⟨h, b, hh, hb⟩

/-- **The chart ratios at the generic point**: the germ of `b_i / b_{i₀}` at the generic point is
the quotient `ρ(b_i) / ρ(b_{i₀})` of the generic coordinates. -/
public lemma germ_ratio_mul_genericCoord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L]
    (s₀ : MeromorphicSection X.sheaf L) (hs₀ : IsRegularMeromorphicSection X.sheaf L s₀)
    {ι : Type*} (b : ι → Γ(L, ⊤)) (i₀ i : ι)
    (hη : genericPoint X ∈ Stacks.ProjectiveFromSections.nvCover b i₀) :
    (X.presheaf.germ _ (genericPoint X) hη).hom (Stacks.ProjectiveFromSections.ratio b i₀ i) *
        Stacks.Zeta.genericCoord X L s₀ hs₀ (b i₀) = Stacks.Zeta.genericCoord X L s₀ hs₀ (b i) := by
  set U := Stacks.ProjectiveFromSections.nvCover b i₀
  have h := congrArg (L.presheaf.germ U (genericPoint X) hη).hom
    (Stacks.ProjectiveFromSections.ratio_smul b i₀ i)
  rw [Stacks.ModuleStalk.germ_smul] at h
  have hres : ∀ t : Γ(L, ⊤), (L.presheaf.germ U (genericPoint X) hη).hom
      (Stacks.ProjectiveFromSections.resT U t) =
        (L.presheaf.germ ⊤ (genericPoint X) trivial).hom t :=
    fun t => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hres, hres, Stacks.Zeta.genericCoord_spec X L s₀ hs₀,
    Stacks.Zeta.genericCoord_spec X L s₀ hs₀, smul_smul] at h
  exact smul_left_injective X.functionField (Stacks.Zeta.genericValue_ne_zero X L s₀ hs₀) h

/-- **The morphism of a generating family at the generic point** is the `k(Y)`-point whose
homogeneous coordinates are the generic coordinates `y_i`, for `ρ(b_i) = h y_i`. -/
private theorem fromSpecStalk_genericPoint_comp_toProjectiveSpaceOver {Y : Scheme.{u}}
    [IsIntegral Y]
    [IsLocallyNoetherian Y] (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s₀ : MeromorphicSection Y.sheaf L) (hs₀ : IsRegularMeromorphicSection Y.sheaf L s₀)
    {m : ℕ} (b : Fin (m + 1) → Γ(L, ⊤)) (hgen : Stacks.ProjectiveFromSections.GeneratesStalks b)
    {S : Scheme.{u}} (g : Y ⟶ S) (h : Y.functionField) (hh : h ≠ 0)
    (y : Fin (m + 1) → Y.functionField)
    (hb : ∀ i, Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i) = h * y i)
    (hy : ∀ i, y i ≠ 0) :
    Y.fromSpecStalk (genericPoint Y) ≫
        Stacks.ProjectiveFromSections.toProjectiveSpaceOver b hgen g =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
        (Y.fromSpecStalk _ ≫ g) := by
  obtain ⟨i₀, hi₀⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks b hgen
    (genericPoint Y)
  have hratio : ∀ k, (Y.presheaf.germ _ (genericPoint Y) hi₀).hom
      (Stacks.ProjectiveFromSections.ratio b i₀ k) = (y i₀)⁻¹ * y k := fun k => by
    have h1 := germ_ratio_mul_genericCoord L s₀ hs₀ b i₀ k hi₀
    rw [hb, hb] at h1
    have h2 : h * y i₀ ≠ 0 := mul_ne_zero hh (hy i₀)
    rw [← eq_div_iff h2] at h1
    rw [h1]
    field_simp
  refine Limits.pullback.hom_ext ?_ ?_
  · simp
  · rw [Category.assoc]
    erw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]
    rw [fromSpecStalk_comp_toProjectiveSpaceAtUniverse b hgen hi₀, projectiveSpacePoint]
    set u : Γ(Spec (.of Y.functionField), ⊤)ˣ :=
      Units.map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom.toMonoidHom
        (Units.mk0 (y i₀)⁻¹ (inv_ne_zero (hy i₀)))
    have hfun : (fun k => (Scheme.ΓSpecIso (Y.presheaf.stalk (genericPoint Y))).inv
        ((Y.presheaf.germ _ (genericPoint Y) hi₀).hom
          (Stacks.ProjectiveFromSections.ratio b i₀ k))) =
        fun k => (u : Γ(Spec (.of Y.functionField), ⊤)) *
          (Scheme.ΓSpecIso (.of Y.functionField)).inv (y k) := funext fun k => by
      rw [hratio, map_mul]
      rfl
    rw [Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr hfun _
      (by rw [← hfun]; exact span_range_ΓSpecIso_inv _ (span_range_germ_ratio b hi₀))]
    exact Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance _ _ _ _

/-- **A generating family has a member of order exactly `-div s₀` at each prime divisor.** -/
private theorem exists_ord_genericCoord_add_eq_zero {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s₀ : MeromorphicSection Y.sheaf L) (hs₀ : IsRegularMeromorphicSection Y.sheaf L s₀)
    {ι : Type*} (b : ι → Γ(L, ⊤)) (hgen : Stacks.ProjectiveFromSections.GeneratesStalks b)
    (Z : PrimeDivisor Y) [IsDiscreteValuationRing (Y.presheaf.stalk Z.genericPoint)] :
    ∃ i, Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i) ≠ 0 ∧
      Y.ord (Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i)) Z.genericPoint +
        orderOfVanishingMeromorphic Y L s₀ hs₀ Z = 0 := by
  classical
  have hZ1 := PrimeDivisor.coheight_genericPoint Z
  set ξ := Z.genericPoint
  have hsp := (genericPoint_spec Y).specializes (Set.mem_univ ξ)
  set sp := L.presheaf.stalkSpecializes hsp
  obtain ⟨m, hm, c, hc⟩ := (orderOfVanishingMeromorphicData Y L s₀ hs₀ Z).2.1
  have hval : Stacks.Zeta.genericValue Y L s₀ = c • sp m :=
    meromorphicGenericValue_eq Y L s₀ _ hc
  have hord : orderOfVanishingMeromorphic Y L s₀ hs₀ Z = Y.ord c ξ :=
    (orderOfVanishingMeromorphicData Y L s₀ hs₀ Z).2.2 m hm c hc
  obtain ⟨hc0, hm0⟩ : c ≠ 0 ∧ sp m ≠ 0 := by
    have := Stacks.Zeta.genericValue_ne_zero Y L s₀ hs₀
    rw [hval] at this
    exact smul_ne_zero_iff.mp this
  have hr : ∀ i, ∃ r : Y.presheaf.stalk ξ, (L.presheaf.germ ⊤ ξ trivial) (b i) = r • m :=
    fun i => by
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hm ▸ Submodule.mem_top
        (x := (L.presheaf.germ ⊤ ξ trivial) (b i)))
      exact ⟨r, hr.symm⟩
  choose r hr using hr
  have hρ : ∀ i, Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i) * c =
      algebraMap (Y.presheaf.stalk ξ) Y.functionField (r i) := fun i => by
    have h1 := Stacks.Zeta.genericCoord_spec Y L s₀ hs₀ (b i)
    have h2 : (L.presheaf.germ ⊤ (genericPoint Y) trivial) (b i) =
        sp ((L.presheaf.germ ⊤ ξ trivial) (b i)) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
    rw [h2, hr, Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ (r i) m, hval,
      smul_smul, ← algebraMap_functionField_eq_stalkSpecializes] at h1
    exact (smul_left_injective _ hm0 h1).symm
  obtain ⟨t, a, ha⟩ := hgen ξ m
  have hr' : ∀ i, (L.presheaf.Γgerm ξ).hom (b i) = r i • m := hr
  have hsum : ∑ i ∈ t, a i * r i = 1 := by
    have h1 : m = (∑ i ∈ t, a i * r i) • m := by
      conv_lhs => rw [ha]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [hr', mul_smul]
    have h2 := congrArg sp h1
    rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ _ m,
      ← algebraMap_functionField_eq_stalkSpecializes] at h2
    have h3 : (1 : Y.functionField) • sp m = _ • sp m := (one_smul _ _).trans h2
    have h4 := smul_left_injective _ hm0 h3
    exact IsFractionRing.injective (Y.presheaf.stalk ξ) Y.functionField
      (by rw [map_one]; exact h4.symm)
  obtain ⟨i, -, hi⟩ : ∃ i ∈ t, IsUnit (a i * r i) := by
    by_contra hno
    push Not at hno
    have : ∑ i ∈ t, a i * r i ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk ξ) :=
      Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).2 (hno i hi)
    rw [hsum] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this isUnit_one
  have hri : IsUnit (r i) := isUnit_of_mul_isUnit_right hi
  have hρ0 : Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i) ≠ 0 := by
    intro h0
    have := hρ i
    rw [h0, zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
    exact hri.ne_zero this
  refine ⟨i, hρ0, ?_⟩
  rw [hord, ← Scheme.ord_mul hρ0 hc0, hρ i]
  exact Stacks.Zeta.ord_algebraMap_isUnit hZ1 hri

/-- **The function-field basis of the sections of an invertible sheaf.** On a normal locally
Noetherian integral scheme over `k`, let `L` be invertible of Weil divisor class `[D]`, with `D` a
divisor given on the points (zero off codimension one), and `b` a `k`-basis of `Γ(Y, L)`
generating `L`. There are nonzero `y_i ∈ k(Y)` with `div y_i + D ≥ 0`, linearly independent and
spanning `L(D)`, with no common zero of `div y_i + D` along any prime divisor, such that the
morphism `φ_b` at the generic point is the point `[y_0 : … : y_m]`. -/
private theorem exists_genericCoord_basis_facts {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Y.Over (Spec (.of k))]
    [Algebra k Y.functionField]
    (hk : ∀ c : k, algebraMap k Y.functionField c = Y.presheaf.germ ⊤ (genericPoint Y) trivial
      (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k Y c))
    (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (D : Y → ℤ) (hD0 : ∀ q, Order.coheight q ≠ 1 → D q = 0)
    (DW : WeilDivisor Y) (hDW : ∀ Z, DW.val Z = D Z.genericPoint)
    (hD : weilDivisorClassOfInvertibleSheaf Y L = (DW : weilDivisorClassGroup Y))
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) k Γ(L, ⊤))
    (hgen : Stacks.ProjectiveFromSections.GeneratesStalks ⇑b) {S : Scheme.{u}} (g : Y ⟶ S) :
    ∃ (y : Fin (m + 1) → Y.functionField) (hy : ∀ i, y i ≠ 0),
      (∀ i q, 0 ≤ Y.ord (y i) q + D q) ∧ LinearIndependent k y ∧
      (∀ h : Y.functionField, (∀ q, 0 ≤ Y.ord h q + D q) →
        h ∈ Submodule.span k (Set.range y)) ∧
      (∀ q : Y, Order.coheight q = 1 → ∃ i, Y.ord (y i) q + D q = 0) ∧
      Y.fromSpecStalk (genericPoint Y) ≫
          Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen g =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
          (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (y i))
          (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
            ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
          (Y.fromSpecStalk _ ≫ g) := by
  obtain ⟨s₀, hs₀⟩ := exists_isRegularMeromorphicSection_of_isIntegral Y L
  obtain ⟨h, hh, hDZ, hiff⟩ := exists_mul_genericCoord_iff L s₀ hs₀ DW hD
  have hdvr : ∀ Z : PrimeDivisor Y, IsDiscreteValuationRing (Y.presheaf.stalk Z.genericPoint) :=
    fun Z => isDiscreteValuationRing_stalk_of_coheight_eq_one (PrimeDivisor.coheight_genericPoint Z)
  set ρ := Stacks.Zeta.genericCoord Y L s₀ hs₀
  have hρsmul : ∀ (c : k) t', ρ (c • t') = c • ρ t' := fun c t' => by
    change ρ ((Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k Y c) •
      t') = _
    refine (Stacks.Zeta.genericCoord_smul Y L s₀ hs₀ _ t').trans ?_
    rw [Algebra.smul_def, hk]
  let ρl : Γ(L, ⊤) →ₗ[k] Y.functionField :=
    { toFun := ρ, map_add' := Stacks.Zeta.genericCoord_add Y L s₀ hs₀, map_smul' := hρsmul }
  have hρinj : Function.Injective ρl := Stacks.Zeta.genericCoord_injective Y L s₀ hs₀
  set y : Fin (m + 1) → Y.functionField := fun i => h⁻¹ * ρ (b i) with hydef
  have hb : ∀ i, ρ (b i) = h * y i := fun i => by simp [y, mul_inv_cancel_left₀ hh]
  have hy : ∀ i, y i ≠ 0 := fun i h0 => by
    have : ρl (b i) = ρl 0 := by
      change ρ (b i) = ρ 0
      rw [hb, h0, mul_zero, (ρl.map_zero : ρl 0 = 0).symm]
      rfl
    exact b.ne_zero i (hρinj this)
  have hcond : ∀ w : Y.functionField, (w = 0 ∨ ∀ Z : PrimeDivisor Y,
      0 ≤ Y.ord w Z.genericPoint + DW.val Z) → ∀ q, 0 ≤ Y.ord w q + D q ∨ w = 0 := by
    intro w hw q
    rcases hw with rfl | hw
    · exact Or.inr rfl
    refine Or.inl ?_
    by_cases hq : Order.coheight q = 1
    · have := hw (PrimeDivisor.ofCoheightOne q hq)
      rwa [hDW, PrimeDivisor.genericPoint_ofCoheightOne] at this
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq, hD0 q hq, add_zero]
  refine ⟨y, hy, fun i q => ?_, ?_, fun w hw => ?_, fun q hq => ?_, ?_⟩
  · exact ((hcond _ ((hiff _).2 ⟨b i, hb i⟩)) q).resolve_right (hy i)
  · have h1 : y = ⇑(LinearMap.mulLeft k h⁻¹) ∘ ⇑ρl ∘ ⇑b := rfl
    rw [h1]
    exact (b.linearIndependent.map' ρl (LinearMap.ker_eq_bot.2 hρinj)).map'
      _ (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (inv_ne_zero hh)))
  · obtain ⟨t, ht⟩ := (hiff w).1 (Or.inr fun Z => by
      have := hw Z.genericPoint
      rwa [← hDW] at this)
    have hspan : Submodule.map ρl (Submodule.span k (Set.range ⇑b)) =
        Submodule.map (LinearMap.mulLeft k h) (Submodule.span k (Set.range y)) := by
      rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
      exact congrArg _ (congrArg Set.range (funext hb))
    have hmem : ρl t ∈ Submodule.map (LinearMap.mulLeft k h) (Submodule.span k (Set.range y)) := by
      rw [← hspan, b.span_eq]
      exact ⟨t, Submodule.mem_top, rfl⟩
    obtain ⟨w', hw', he⟩ := hmem
    have : w' = w := mul_left_cancel₀ hh (he.trans ht)
    rwa [← this]
  · have := hdvr (PrimeDivisor.ofCoheightOne q hq)
    obtain ⟨i, hi0, hi⟩ := exists_ord_genericCoord_add_eq_zero L s₀ hs₀ (⇑b) hgen
      (PrimeDivisor.ofCoheightOne q hq)
    refine ⟨i, ?_⟩
    have hD' := hDZ (PrimeDivisor.ofCoheightOne q hq)
    rw [hDW, PrimeDivisor.genericPoint_ofCoheightOne] at hD'
    rw [PrimeDivisor.genericPoint_ofCoheightOne, show Stacks.Zeta.genericCoord Y L s₀ hs₀ (b i) =
      h * y i from hb i, Scheme.ord_mul hh (hy i)] at hi
    rw [hD']
    linarith
  · exact fromSpecStalk_genericPoint_comp_toProjectiveSpaceOver L s₀ hs₀ (⇑b) hgen g h hh y hb hy

open Classical in
/-- The class of an integral effective Cartier divisor `E` is `[E]`, the prime divisor
generated by `E`, whose generic point is the generic point of the support of `E`. -/
private lemma exists_primeDivisor_firstChern_picardClass {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (E : Y.IdealSheafData) [IsIntegral E.subscheme]
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) :
    ∃ F : PrimeDivisor Y,
      IsGenericPoint F.genericPoint ((E.support : TopologicalSpace.Closeds Y) : Set Y) ∧
      ∃ W : WeilDivisor Y, (∀ Z, W.val Z = if Z = F then 1 else 0) ∧
        Stacks.Zeta.firstChern Y (Stacks.Divisors.picardClass E) = W := by
  refine ⟨PrimeDivisor.ofEffectiveCartier E hE, ?_,
    (PrimeDivisor.ofEffectiveCartier E hE).toWeilDivisor, fun Z => ?_, ?_⟩
  · exact (PrimeDivisor.support_eq_closure_genericPoint _).symm.trans
      (PrimeDivisor.support_ofEffectiveCartier E hE)
  · by_cases h : Z = PrimeDivisor.ofEffectiveCartier E hE
    · subst h; simp
    · simp [h, PrimeDivisor.toWeilDivisor_val_of_ne h]
  · have := hE
    have := Stacks.Divisors.isInvertible_invertibleSheaf_picard E
    exact (weilDivisorClassOfPicardClass_picardClass Y _).trans
      (weilDivisorClassOfInvertibleSheaf_eq_toWeilDivisor E)

open Classical in
/-- **`B` read as a Weil divisor.** The first Chern class of `[𝒪(B)]`, `B = (s+1)(P × C) +
(s+1)(C × P) - Δ`, is the class of the Weil divisor with coefficients `DB`, and `DB` vanishes off
the points of codimension one. -/
private lemma exists_weilDivisor_vojtaClass {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    (sB : ℕ)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0)) :
    (∀ q, Order.coheight q ≠ 1 → DB q = 0) ∧
      ∃ DW : WeilDivisor (pullback X.f X.f), (∀ Z, DW.val Z = DB Z.genericPoint) ∧
        Stacks.Zeta.firstChern _ (X.vojtaClass sB sB (-1)) = DW := by
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hfib : ∀ (p : pullback X.f X.f ⟶ X.C) [Flat p] [GeometricallyIntegral p]
      (c : Stacks.Zeta.ClosedPoint X.C), ∃ F : PrimeDivisor (pullback X.f X.f),
        IsGenericPoint F.genericPoint (p.base ⁻¹' {c.1}) ∧
        ∃ W : WeilDivisor (pullback X.f X.f), (∀ Z, W.val Z = if Z = F then 1 else 0) ∧
          haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f c
          Stacks.Zeta.firstChern _ (Stacks.Picard.schemePullbackClassHom p
            (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal c))) = W := by
    intro p _ _ c
    have := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f c
    have hpd : Stacks.Divisors.IsPullbackDefined p (Stacks.Zeta.pointIdeal c) :=
      Stacks.Divisors.isPullbackDefined_of_flat p _ inferInstance
    have hE : Stacks.Divisors.IsEffectiveCartierDivisor ((Stacks.Zeta.pointIdeal c).comap p) :=
      hpd
    set ι := (Stacks.Zeta.pointIdeal c).subschemeι
    have hI : IsIntegral (Stacks.Zeta.pointIdeal c).subscheme :=
      StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ isIrreducible_singleton
    have hsupp : (((Stacks.Zeta.pointIdeal c).support : TopologicalSpace.Closeds X.C) :
        Set X.C) = {c.1} := by
      rw [Stacks.Zeta.pointIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hpt : ∀ a, ι a = c.1 := fun a => by
      have h' : ι a ∈ (((Stacks.Zeta.pointIdeal c).support : TopologicalSpace.Closeds X.C) :
          Set X.C) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨a, rfl⟩
      rwa [hsupp] at h'
    have hS : Subsingleton (Stacks.Zeta.pointIdeal c).subscheme :=
      ⟨fun a b => ι.isClosedEmbedding.injective ((hpt a).trans (hpt b).symm)⟩
    have hPint : IsIntegral (pullback p ι) :=
      ((geometrically_eq_universally IsIntegral).le p
        (GeometricallyIntegral.geometrically_isIntegral (f := p))) _ _ _
        (IsPullback.of_hasPullback p ι).flip hI hS
    have : Nonempty ((Stacks.Zeta.pointIdeal c).comap p).subscheme :=
      ⟨((Stacks.Zeta.pointIdeal c).comapIso p).inv (Nonempty.some inferInstance)⟩
    have hint : IsIntegral ((Stacks.Zeta.pointIdeal c).comap p).subscheme :=
      isIntegral_of_isOpenImmersion ((Stacks.Zeta.pointIdeal c).comapIso p).hom
    obtain ⟨F, hF, W, hW, hc⟩ := exists_primeDivisor_firstChern_picardClass _ hE
    refine ⟨F, ?_, W, hW, ?_⟩
    · rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        hsupp] at hF
    · have := hpd
      exact (congrArg _ (Stacks.Divisors.schemePullbackClass_picardClass p _)).trans hc
  choose F₁ hF₁ W₁ hW₁ hc₁ using hfib (pullback.fst X.f X.f)
  choose F₂ hF₂ W₂ hW₂ hc₂ using hfib (pullback.snd X.f X.f)
  obtain ⟨hEΔ, hIΔ, -⟩ := Faltings.isEffectiveCartierDivisor_ker_diagonal k X.f
  obtain ⟨FΔ, hFΔ, WΔ, hWΔ, hcΔ⟩ := exists_primeDivisor_firstChern_picardClass _ hEΔ
  have hΔd : Δ = pullback.diagonal X.f := pullback.hom_ext (by simp [hΔ₁]) (by simp [hΔ₂])
  have hFΔe : FΔ.genericPoint = eΔ := by
    rw [Scheme.Hom.support_ker,
      ((pullback.diagonal X.f).isClosedEmbedding.isClosed_range).closure_eq, ← hΔd] at hFΔ
    exact hFΔ.eq heΔ
  have hgen₁ : ∀ (Z : PrimeDivisor (pullback X.f X.f)) c,
      IsGenericPoint Z.genericPoint ((pullback.fst X.f X.f).base ⁻¹' {c.1}) ↔ Z = F₁ c :=
    fun Z c => ⟨fun h => PrimeDivisor.genericPoint_injective (h.eq (hF₁ c)), fun h => h ▸ hF₁ c⟩
  have hgen₂ : ∀ (Z : PrimeDivisor (pullback X.f X.f)) c,
      IsGenericPoint Z.genericPoint ((pullback.snd X.f X.f).base ⁻¹' {c.1}) ↔ Z = F₂ c :=
    fun Z c => ⟨fun h => PrimeDivisor.genericPoint_injective (h.eq (hF₂ c)), fun h => h ▸ hF₂ c⟩
  have hgenΔ : ∀ Z : PrimeDivisor (pullback X.f X.f), Z.genericPoint = eΔ ↔ Z = FΔ :=
    fun Z => ⟨fun h => PrimeDivisor.genericPoint_injective (h.trans hFΔe.symm),
      fun h => h ▸ hFΔe⟩
  refine ⟨fun q hq => ?_, ((sB : ℤ) + 1) • X.P.sum (fun c a => a • W₁ c) +
    ((sB : ℤ) + 1) • X.P.sum (fun c a => a • W₂ c) - WΔ, fun Z => ?_, ?_⟩
  · have h1 : ∀ c : Stacks.Zeta.ClosedPoint X.C,
        ¬ IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) := fun c h =>
      hq (h.eq (hF₁ c) ▸ PrimeDivisor.coheight_genericPoint (F₁ c))
    have h2 : ∀ c : Stacks.Zeta.ClosedPoint X.C,
        ¬ IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) := fun c h =>
      hq (h.eq (hF₂ c) ▸ PrimeDivisor.coheight_genericPoint (F₂ c))
    have h3 : q ≠ eΔ := fun h => hq (h ▸ hFΔe ▸ PrimeDivisor.coheight_genericPoint FΔ)
    rw [hDB]
    simp [h1, h2, h3, Finsupp.sum]
  · have hsum : ∀ (W : Stacks.Zeta.ClosedPoint X.C → WeilDivisor (pullback X.f X.f)),
        (X.P.sum fun c a => a • W c).val Z = X.P.sum fun c a => a * (W c).val Z := fun W => by
      rw [← AddSubgroup.coe_subtype, map_finsuppSum, Finsupp.sum, Finsupp.sum,
        Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
    rw [hDB, AddSubgroup.coe_sub, AddSubgroup.coe_add, AddSubgroup.coe_zsmul,
      AddSubgroup.coe_zsmul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hsum, hsum,
      hWΔ, smul_eq_mul, smul_eq_mul]
    congr 1
    · congr 1
      · congr 1
        refine Finsupp.sum_congr fun c _ => ?_
        rw [hW₁, if_congr (hgen₁ Z c).symm rfl rfl]
        split_ifs <;> simp
      · congr 1
        refine Finsupp.sum_congr fun c _ => ?_
        rw [hW₂, if_congr (hgen₂ Z c).symm rfl rfl]
        split_ifs <;> simp
    · exact if_congr (hgenΔ Z).symm rfl rfl
  · have hcls : ∀ (p : pullback X.f X.f ⟶ X.C)
        (W : Stacks.Zeta.ClosedPoint X.C → WeilDivisor (pullback X.f X.f))
        (_ : ∀ c, haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f c
          Stacks.Zeta.firstChern _ (Stacks.Picard.schemePullbackClassHom p
            (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal c))) = W c),
        Stacks.Zeta.firstChern _ (Stacks.Picard.schemePullbackClassHom p (X.P.sum fun x n =>
          haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
          n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))) =
          ((X.P.sum fun c a => a • W c : WeilDivisor (pullback X.f X.f)) :
            weilDivisorClassGroup (pullback X.f X.f)) := by
      intro p W hc
      rw [map_finsuppSum, map_finsuppSum, ← QuotientAddGroup.mk'_apply, map_finsuppSum]
      refine Finsupp.sum_congr fun c _ => ?_
      rw [map_zsmul, map_zsmul, hc c, map_zsmul]
      rfl
    have e₁ := hcls _ W₁ hc₁
    have e₂ := hcls _ W₂ hc₂
    unfold Faltings.CurveWithDegreeOneDivisor.vojtaClass
    dsimp only
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_sub, map_sub, e₁, e₂, hcΔ,
      QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, QuotientAddGroup.mk_zsmul,
      QuotientAddGroup.mk_zsmul]
    generalize ((X.P.sum fun c a => a • W₁ c : WeilDivisor (pullback X.f X.f)) :
      weilDivisorClassGroup (pullback X.f X.f)) = a
    generalize ((X.P.sum fun c a => a • W₂ c : WeilDivisor (pullback X.f X.f)) :
      weilDivisorClassGroup (pullback X.f X.f)) = b
    generalize ((WΔ : WeilDivisor (pullback X.f X.f)) :
      weilDivisorClassGroup (pullback X.f X.f)) = d
    simp only [add_smul, one_smul, smul_sub, neg_one_smul, natCast_zsmul]
    abel

open Classical in
/-- **BV's basis `y` of `L(B)` on `C × C`.** From an invertible sheaf `L` on `C ×_k C` of class
`[𝒪(B)]`, `B = (s+1)(P × C) + (s+1)(C × P) - Δ`, and a `k`-basis `b` of `Γ(L)` generating `L`,
the generic coordinates give nonzero `y_i ∈ k(C × C)` with `div y_i + B ≥ 0`, a basis of `L(B)`
without base points in codimension one, and `φ_B = φ_b` is `[y_0 : … : y_m]` at the generic
point. -/
private theorem exists_vojtaBasis_facts {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (sB : ℕ)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    (L : (pullback X.f X.f).Modules)
    [hLinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f) L]
    (hL : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      X.vojtaClass sB sB (-1))
    {m : ℕ} (b : letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
      Module.Basis (Fin (m + 1)) k Γ(L, ⊤))
    (hgen : Stacks.ProjectiveFromSections.GeneratesStalks ⇑b) :
    ∃ (y : Fin (m + 1) → (pullback X.f X.f).functionField) (hy : ∀ i, y i ≠ 0),
      (∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q) ∧
      LinearIndependent k y ∧
      (∀ h : (pullback X.f X.f).functionField,
        (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y)) ∧
      (∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
        ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0) ∧
      (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen
            (pullback.fst X.f X.f ≫ X.f) =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
          (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
          (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
            ((Ne.isUnit (hy 0)).map
              (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
          ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f) := by
  let : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsNormal (pullback X.f X.f) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field (pullback.fst X.f X.f ≫ X.f))
  have hLi : Stacks.SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2 L := hLinv
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback X.f X.f).sheaf.obj
      (pullback X.f X.f).ringCatSheaf.property L := hLi.toAlgebraicGeometry
  obtain ⟨hD0, DW, hDW, hcls⟩ := exists_weilDivisor_vojtaClass X Δ hΔ₁ hΔ₂ sB heΔ DB hDB
  have hD : weilDivisorClassOfInvertibleSheaf _ L = (DW : weilDivisorClassGroup _) := by
    rw [← hcls, ← hL]
    exact (weilDivisorClassOfPicardClass_picardClass _ L).symm
  exact exists_genericCoord_basis_facts hkX L DB hD0 DW hDW hD b hgen _

open Classical in
/-- **BV's coordinates `y` of `φ_B` exist.** Let `X = (C, P)` be a curve over a number field `k`
with a divisor of degree one, and `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` on `C ×_k C`, with
coefficients `DB` on the points. For all `s` large enough there are `m`, a closed immersion
`φ_B : C ×_k C ⟶ ℙᵐ_k` over `k` with `[φ_B^* 𝒪(1)] = [𝒪(B)]`, and nonzero `y₀, …, yₘ ∈ k(C × C)`
with `div yᵢ + B ≥ 0`, forming a `k`-basis of `L(B)`, without common zero along any prime
divisor, such that `φ_B` at the generic point is `[y₀ : … : yₘ]`. -/
public theorem exists_vojtaEmbedding_coordinates {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c))) :
    ∃ s₀ : ℕ, ∀ (sB : ℕ), s₀ ≤ sB →
    ∀ {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (_heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (_hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0)),
    ∃ (m : ℕ) (y : Fin (m + 1) → (pullback X.f X.f).functionField) (hy : ∀ i, y i ≠ 0),
    (∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q) ∧
    LinearIndependent k y ∧
    (∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y)) ∧
    (∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0) ∧
    ∃ (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
      (_hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
        pullback.fst X.f X.f ≫ X.f)
      (_ : IsClosedImmersion φB)
      (hinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))),
    Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr hinv) =
      X.vojtaClass sB sB (-1) ∧
    (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f) := by
  obtain ⟨s₀, hs₀⟩ := X.isClosedImmersion_toProjectiveSpaceOver_vojtaClass
  refine ⟨s₀.toNat, fun sB hsB eΔ heΔ DB hDB => ?_⟩
  let : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
  set c := X.vojtaClass sB sB (-1)
  obtain ⟨L, hLinv, hL⟩ : ∃ (L : (pullback X.f X.f).Modules)
      (hLinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f) L),
      Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
          (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) = c :=
    ⟨_, (Stacks.Picard.picardRepresentative (pullback X.f X.f).toRingedSpace c).property,
      Stacks.Picard.classOf_picardRepresentative _ _⟩
  obtain ⟨-, hpos, hbasis⟩ := hs₀ sB (le_trans (Int.self_le_toNat s₀) (by exact_mod_cast hsB))
    L hL
  have : Module.Finite k Γ(L, ⊤) := Module.finite_of_finrank_pos hpos
  set m := Module.finrank k Γ(L, ⊤) - 1
  have hm : Module.finrank k Γ(L, ⊤) = m + 1 := by omega
  let b : Module.Basis (Fin (m + 1)) k Γ(L, ⊤) := Module.finBasisOfFinrankEq k _ hm
  obtain ⟨hgen, hci, ⟨eα, hα, -⟩, -⟩ := hbasis b
  obtain ⟨y, hy, hyD, hyli, hyspan, hybpf, hφBy⟩ :=
    exists_vojtaBasis_facts X Δ hΔ₁ hΔ₂ hkX sB heΔ DB hDB L hL b hgen
  let φB := Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen
    (pullback.fst X.f X.f ≫ X.f)
  have hinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1))) :=
    inferInstance
  refine ⟨m, y, hy, hyD, hyli, hyspan, hybpf, φB, ?_, hci, hinv, ?_, hφBy⟩
  · exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _
  · have e := (Scheme.Modules.pullbackComp φB
      (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).app
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≪≫ @asIso _ _ _ _ eα hα
    exact ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ L _ _).mpr ⟨e⟩).trans hL

end NPData

end Faltings.BombieriSiegel
