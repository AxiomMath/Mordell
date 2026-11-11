module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import Mordell.BombieriVojta.Conclusion.BoundedNorm
public import Mordell.BombieriVojta.Projection.GenericCoordinatesBExist
public import Mordell.BombieriVojta.Conclusion.Theorem2
public import Mordell.Jacobian.Existence
public import Mordell.Jacobian.AbelJacobi
public import Mordell.Jacobian.Theta.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.GlobalSectionsGenericStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorGeneration
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.CurveProduct.Embedding.NP
public import Mordell.CurveProduct.Embedding.B
public import Mordell.BombieriVojta.Projection.GenericBasisExists
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PrincipalDivisorClass
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedSubschemeSmoothPullback
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import Mordell.CurveProduct.Diagonal
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible

/-!
# Finiteness of rational points on curves of genus at least two

Let `k` be a number field and `C` a smooth projective geometrically integral curve over `k` of
genus `g = dim_k H¹(C, 𝒪_C) ≥ 2`. Then the set `C(k)` of `k`-rational points of `C` is finite.
This is the Mordell conjecture, proved here by the method of Vojta and Bombieri: Vojta's
inequality bounds the number of points of large Néron–Tate norm in each cone of the
Mordell–Weil lattice of the Jacobian, and Northcott's theorem bounds the points of small norm.

## Main results

* `Faltings.finite_setOf_comp_eq_id_of_two_le_genus`: `C(k)` is finite.

## Implementation notes

The curve is a morphism `f : C ⟶ Spec k`, with `AlgebraicGeometry.IsCurve k f` (an integral
separated scheme of finite type over `k` of dimension one),
`AlgebraicGeometry.IsProjectiveVariety k f`, `Smooth f` and `GeometricallyIntegral f`.
The genus is `AlgebraicGeometry.genus f`, the `k`-dimension of `H¹(C, 𝒪_C)`.
A `k`-rational point is a section `σ : Spec k ⟶ C` of `f`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, Theorem 2
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

section

open CategoryTheory.Limits

section GenericCoord

open Stacks.Zeta Opposite TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)

omit [IsLocallyNoetherian X] in
/-- The coordinate of a global section against a meromorphic section is compatible with ratios:
if `t = u t'` on a nonempty open `U`, then `ρ(t) = u ρ(t')`. -/
private theorem genericCoord_eq_mul_of_res_eq_smul {U : X.Opens} [Nonempty U] (u : Γ(X, U))
    (t t' : Γ(L, ⊤))
    (h : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t =
      u • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t') :
    genericCoord X L s hs t = X.germToFunctionField U u * genericCoord X L s hs t' := by
  have hη : genericPoint X ∈ U := by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty U›
    exact (genericPoint_spec X).mem_open_set_iff U.2 |>.mpr ⟨x, trivial, hx⟩
  apply (genericBasisEquiv X L s hs).injective
  rw [genericBasisEquiv_apply, genericBasisEquiv_apply, ← genericCoord_spec, mul_smul,
    ← genericCoord_spec]
  rw [← L.presheaf.germ_res_apply (homOfLE le_top) _ hη t,
    ← L.presheaf.germ_res_apply (homOfLE le_top) _ hη t', h,
    Stacks.ModuleStalk.germ_smul L (genericPoint X) U hη u]

/-- The order of the inverse of a nonzero rational function. -/
private theorem ord_inv_of_ne_zero {a : X.functionField} (ha : a ≠ 0) (ξ : X) :
    X.ord a⁻¹ ξ = -X.ord a ξ := by
  have hone : X.ord (1 : X.functionField) ξ = 0 := by simp
  have h := X.ord_mul (x := ξ) ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, hone] at h
  omega

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The germ of a global section at a point of its nonvanishing locus is a basis of the stalk. -/
private theorem isStalkBasis_germ_of_mem_nonvanishingLocus (t : Γ(L, ⊤)) {x : X}
    (hx : x ∈ Stacks.Ample.nonvanishingLocus L t) :
    Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ ⊤ x trivial t) := by
  obtain ⟨U, eU, e, hxU, -⟩ := Stacks.Chow.exists_affine_frame_subset X L x ⊤ trivial
  have hsmul := Stacks.ChernCap42.germ_restrict_eq_smul L t hxU
    (Stacks.Divisors.frameSections X L eU)
  rw [L.presheaf.germ_res_apply (homOfLE (le_top (a := U.1))) x hxU t] at hsmul
  rw [hsmul]
  refine (Stacks.ChernCap42.isStalkBasis_germ_frameSections L eU x hxU).smul_of_isUnit ?_
  by_contra hu
  apply hx
  rw [show (L.presheaf.Γgerm x).hom t = L.presheaf.germ ⊤ x trivial t from rfl, hsmul]
  exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal
    ((IsLocalRing.mem_maximalIdeal _).2 hu) _

variable {L} in
/-- **Global sections of an invertible module as a Riemann–Roch space.** If the Weil divisor
class of `L` is that of `D`, there is an injective additive map `c : Γ(X, L) → K(X)`,
semilinear over `Γ(X, 𝒪_X)`, compatible with ratios of sections, whose image is
`{a | a = 0 ∨ ord_Z(a) + D(Z) ≥ 0 for every prime divisor Z}`. -/
private theorem exists_coord_of_weilDivisorClass_eq [IsNormal X]
    (hdvr : ∀ Z : PrimeDivisor X, IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint))
    (D : WeilDivisor X)
    (hD : weilDivisorClassOfInvertibleSheaf X L = (D : weilDivisorClassGroup X)) :
    ∃ c : Γ(L, ⊤) → X.functionField, Function.Injective c ∧
      (∀ t t', c (t + t') = c t + c t') ∧
      (∀ (r : Γ(X, ⊤)) t, c (r • t) = X.presheaf.germ ⊤ (genericPoint X) trivial r * c t) ∧
      (∀ (U : X.Opens) [Nonempty U] (u : Γ(X, U)) (t t' : Γ(L, ⊤)),
        L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t =
          u • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t' →
        c t = X.germToFunctionField U u * c t') ∧
      (∀ a, (∃ t, c t = a) ↔
        (a = 0 ∨ ∀ Z : PrimeDivisor X, 0 ≤ X.ord a Z.genericPoint + D.val Z)) ∧
      (∀ t, c t ≠ 0 → genericPoint X ∈ Stacks.Ample.nonvanishingLocus L t) ∧
      ∀ (t : Γ(L, ⊤)) (Z : PrimeDivisor X),
        Z.genericPoint ∈ Stacks.Ample.nonvanishingLocus L t →
        X.ord (c t) Z.genericPoint + D.val Z = 0 := by
  obtain ⟨σ, hσ⟩ := exists_isRegularMeromorphicSection_of_isIntegral X L
  rw [weilDivisorClassOfInvertibleSheaf_eq X L σ hσ] at hD
  obtain ⟨f, hf⟩ := (mem_principalWeilDivisors_iff X _).1 (QuotientAddGroup.eq.1 hD)
  set F := (Stacks.Chow.rationalFunctionsEquivFunctionField X).val f with hFdef
  have hF0 : F ≠ 0 :=
    (f.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toRingHom).ne_zero
  have hDZ : ∀ Z : PrimeDivisor X, D.val Z =
      orderOfVanishingMeromorphic X L σ hσ Z + X.ord F Z.genericPoint := by
    intro Z
    have := congrArg (fun E : WeilDivisor X => E.val Z) hf
    simp only [principalDivisor_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply,
      Pi.neg_apply, weilDivisorOfMeromorphicSection_apply] at this
    rw [← hFdef] at this
    omega
  have hgc0 : genericCoord X L σ hσ 0 = 0 := by simpa using genericCoord_add X L σ hσ 0 0
  refine ⟨fun t => F⁻¹ * genericCoord X L σ hσ t, fun t t' h => ?_, fun t t' => ?_,
    fun r t => ?_, fun U _ u t t' h => ?_, fun a => ?_, fun t ht => ?_, fun t Z hZ => ?_⟩
  · exact genericCoord_injective X L σ hσ (mul_left_cancel₀ (inv_ne_zero hF0) h)
  · simp only [genericCoord_add, mul_add]
  · simp only [genericCoord_smul]; ring
  · simp only [genericCoord_eq_mul_of_res_eq_smul L σ hσ u t t' h]; ring
  · constructor
    · rintro ⟨t, rfl⟩
      by_cases h0 : genericCoord X L σ hσ t = 0
      · exact Or.inl (by simp only [h0, mul_zero])
      refine Or.inr fun Z => ?_
      have := hdvr Z
      have hm := (genericCoord_mem X L σ hσ t Z).resolve_left h0
      simp only
      rw [Scheme.ord_mul (inv_ne_zero hF0) h0, ord_inv_of_ne_zero hF0, hDZ Z]
      omega
    · rintro (rfl | ha)
      · exact ⟨0, by simp only [hgc0, mul_zero]⟩
      by_cases ha0 : a = 0
      · exact ⟨0, by simp only [hgc0, mul_zero, ha0]⟩
      obtain ⟨t, ht⟩ := exists_genericCoord_eq X L σ hσ hdvr (F * a) fun Z => by
        refine Or.inr ?_
        have := ha Z
        rw [Scheme.ord_mul hF0 ha0]
        rw [hDZ Z] at this
        omega
      refine ⟨t, ?_⟩
      simp only [ht, ← mul_assoc, inv_mul_cancel₀ hF0, one_mul]
  · -- a section with nonzero coordinate does not vanish at the generic point
    have hgc : genericCoord X L σ hσ t ≠ 0 := fun h => ht (by simp only [h, mul_zero])
    have hne : L.presheaf.germ ⊤ (genericPoint X) trivial t ≠ 0 := by
      rw [genericCoord_spec X L σ hσ t]
      exact smul_ne_zero hgc (genericValue_ne_zero X L σ hσ)
    intro hmem
    change (L.presheaf.Γgerm (genericPoint X)).hom t ∈
      Stacks.ModuleStalk.maximalSmul L (genericPoint X) at hmem
    have hbot : IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq.mp
        (Field.toIsField (X.functionField)))
    rw [Stacks.ModuleStalk.maximalSmul, hbot, Submodule.bot_smul] at hmem
    exact hne hmem
  · -- the order of a section at a point where it does not vanish
    have := hdvr Z
    have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
    have hb := isStalkBasis_germ_of_mem_nonvanishingLocus L t hZ
    have ht0 : t ≠ 0 := by
      rintro rfl
      have := hb.injective (a₁ := 0) (a₂ := 1) (by simp)
      exact zero_ne_one this
    have hgc : genericCoord X L σ hσ t ≠ 0 := fun h =>
      ht0 (genericCoord_injective X L σ hσ (h.trans hgc0.symm))
    have hsv : σ = meromorphicSectionOfGenericStalk X L (genericValue X L σ) :=
      meromorphicSectionOfGenericStalk_eq_of_hom_eq X L _ σ
        (constantGenericStalkModuleSection_meromorphicGenericValue X L σ)
    have hcoord : Stacks.Divisors.IsCoordinateAt L Z.genericPoint (genericValue X L σ)
        (genericCoord X L σ hσ t)⁻¹ := by
      refine ⟨L.presheaf.germ ⊤ Z.genericPoint trivial t, hb, ?_⟩
      rw [Stacks.Divisors.toGenericStalk_germ (W := ⊤) (x := Z.genericPoint) trivial trivial,
        genericCoord_spec X L σ hσ t,
        smul_smul, inv_mul_cancel₀ hgc, one_smul]
    have hord := orderOfVanishingMeromorphic_eq_ord_of_isCoordinateAt L σ hσ Z _ hsv _ hcoord
    rw [ord_inv_of_ne_zero hgc] at hord
    simp only
    rw [Scheme.ord_mul (inv_ne_zero hF0) hgc, ord_inv_of_ne_zero hF0, hDZ Z, hord]
    ring

end GenericCoord

open Stacks.ProjectiveFromSections in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- On the chart `φ⁻¹ D₊(Tⱼ)`, the morphism of a generating family pulls `Tᵥ / Tⱼ` back to the
ratio `sᵥ / sⱼ`, read in the function field. -/
private theorem germToFunctionField_chart_eq {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : GeneratesStalks s) {S : Scheme.{u}} (f : X ⟶ S) (j ν : Fin (n + 1))
    [Nonempty (nvCover s j)]
    [Nonempty ((toProjectiveSpaceOver s hs f) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)))] :
    X.germToFunctionField _ ((toProjectiveSpaceOver s hs f).app _
      ((projectiveSpaceOver.toIntegralAtUniverse n S).app _
        (Proj.awayToSection _ (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
    X.germToFunctionField (nvCover s j) (ratio s j ν) := by
  have hpin := ι_toProjectiveSpaceAtUniverse s hs j
  have hle := Stacks.TwistPullbackPinned.nvCover_le_preimage_basicOpen s
    (toProjectiveSpaceAtUniverse s hs) j hpin
  have key := Stacks.TwistPullbackPinned.appLE_coordFrac_chart s
    (toProjectiveSpaceAtUniverse s hs) j ν hpin
  rw [← key]
  have : Nonempty ((toProjectiveSpaceAtUniverse s hs) ⁻¹ᵁ Proj.basicOpen
      (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X j)) :=
    let ⟨⟨x, hx⟩⟩ := ‹Nonempty (nvCover s j)›; ⟨⟨x, hle hx⟩⟩
  have e := Faltings.germToFunctionField_app_congr (toProjectiveSpaceOver_snd s hs f)
    (O := Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} n) (MvPolynomial.X j))
    ‹_› ‹_› ((Proj.awayToSection _ (MvPolynomial.X j)).hom
      (Stacks.TwistPullbackPinned.coordFrac.{u} j ν))
  refine e.trans ?_
  exact (Faltings.germToFunctionField_resO hle _).symm

open Stacks.ProjectiveFromSections in
/-- A coordinate `c : Γ(X, L) → K(X)` compatible with ratios of sections sends the ratio
`sᵥ / sⱼ` on the nonvanishing locus of `sⱼ` to `c sᵥ / c sⱼ`. -/
private theorem germToFunctionField_ratio_eq_div {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] {ι : Type*} (s : ι → Γ(L, ⊤)) (j ν : ι)
    [Nonempty (nvCover s j)] {c : Γ(L, ⊤) → X.functionField}
    (hc : ∀ (U : X.Opens) [Nonempty U] (u : Γ(X, U)) (t t' : Γ(L, ⊤)),
      L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t =
        u • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t' →
      c t = X.germToFunctionField U u * c t')
    (hj : c (s j) ≠ 0) :
    X.germToFunctionField (nvCover s j) (ratio s j ν) = c (s ν) / c (s j) := by
  rw [hc _ (ratio s j ν) (s ν) (s j) (ratio_smul s j ν).symm, mul_div_cancel_right₀ _ hj]

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule
  MvPolynomial.gradedAlgebra in
/-- **The embedding `φ_{NP}` given by a generic basis.** For `N ≥ 2g + 1` and `n = N - g` there
are a generic basis `x` of `L(N P)` without base points and a closed immersion
`φ_{NP} : C ⟶ ℙⁿ_k` over `k` with `φ_{NP}^* 𝒪(1)` of class `N [P]`, pulling `Tᵥ / Tⱼ` back to
`xᵥ / xⱼ`. -/
private theorem exists_NP_data {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f) [IsIntegral X.C]
    [IsLocallyNoetherian X.C]
    (p : {x : X.C // IsClosed ({x} : Set X.C)}) (hp : X.f.residueDegree p.1 = 1)
    (hP : X.P = Finsupp.single p 1)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f) :
    ∃ (x : Fin (n + 1) → X.C.functionField)
      (_ : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        BombieriSiegel.IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
      (_ : ∀ c, Order.coheight c = 1 →
        ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
      (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
      (_ : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
      (_ : IsClosedImmersion φNP)
      (hinv : Stacks.Ample.IsInvertibleModule X.C
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))),
      Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr hinv) =
      (N : ℤ) • X.P.sum (fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) ∧
      (letI : ∀ r : ℕ,
          GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
          fun _ => MvPolynomial.gradedAlgebra
        let U : Fin (n + 1) → X.C.Opens := fun j =>
          φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j))
        ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
          (X.C.germToFunctionField (U j)).hom
            (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
              (Proj.awayToSection _ (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk
                  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                  (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
            x ν / x j) := by
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  let : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  let := functionFieldAlgebra k X.f
  have : IsNormal X.C := Stacks.Zeta.isNormal_of_curve X.f
  have hdvr : ∀ Z : PrimeDivisor X.C,
      IsDiscreteValuationRing (X.C.presheaf.stalk Z.genericPoint) := fun Z =>
    Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one X.f _
      (PrimeDivisor.coheight_genericPoint Z)
  -- the invertible module `𝒪(N P)`
  set cNP : Stacks.Picard.ofScheme X.C := (N : ℤ) • X.P.sum (fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) with hcNP
  obtain ⟨L, hLs, hLc⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ cNP
  have hLinv : Stacks.Ample.IsInvertibleModule X.C L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).mp hLs
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.C.sheaf.obj
      X.C.ringCatSheaf.property L := hLs.toAlgebraicGeometry
  -- its Weil divisor class is that of `N P`
  have hW : weilDivisorClassOfInvertibleSheaf X.C L =
      (Stacks.Zeta.toWeil X.f ((N : ℤ) • X.P) : weilDivisorClassGroup X.C) := by
    have h1 : weilDivisorClassOfInvertibleSheaf X.C L = Stacks.Zeta.firstChern X.C cNP := by
      rw [← hLc]
      exact (weilDivisorClassOfPicardClass_picardClass X.C L).symm
    have h2 : cNP = Stacks.Zeta.divisorClass X.f ((N : ℤ) • X.P) := by
      rw [map_zsmul, Stacks.Zeta.divisorClass_apply]
      rfl
    rw [h1, h2, Stacks.Zeta.firstChern_divisorClass]
  obtain ⟨c, hcinj, hcadd, hcsmul, hcratio, hcimg, hcnv, hcord⟩ :=
    exists_coord_of_weilDivisorClass_eq hdvr _ hW
  -- the generic basis `ℓ` of `L(N P)`
  set P' : X.C →₀ ℤ := X.P.mapDomain Subtype.val with hP'
  have hP'single : P' = Finsupp.single p.1 1 := by rw [hP', hP, Finsupp.mapDomain_single]
  have hPclosed : ∀ Q ∈ P'.support, IsClosed ({Q} : Set X.C) := by
    intro Q hQ
    rw [hP'single] at hQ
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hQ)]
    exact p.2
  have hPdeg : ∑ᶠ Q : X.C, P' Q * (X.f.residueDegree Q : ℤ) = 1 := by
    rw [hP'single, finsum_eq_single _ p.1 (fun Q hQ => by
      rw [Finsupp.single_apply, ite_eq_right (Ne.symm hQ), zero_mul])]
    simp [hp]
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ℓ, hℓ⟩ := BombieriSiegel.exists_isGenericBasis k X.f hg P' hPclosed hPdeg N hN n hn hn2
  have hNP : ∀ Q (hQ : IsClosed ({Q} : Set X.C)),
      ((N : ℤ) • P') Q = ((N : ℤ) • X.P) ⟨Q, hQ⟩ := by
    intro Q hQ
    rw [Finsupp.smul_apply, Finsupp.smul_apply, hP',
      ← Finsupp.mapDomain_apply_of_injective Subtype.val_injective X.P ⟨Q, hQ⟩]
  have hrange : ∀ a, (∃ t, c t = a) ↔
      a ∈ (Submodule.span k (Set.range ℓ) : Set X.C.functionField) := by
    intro a
    rw [hcimg a, hℓ.span_eq]
    simp only [Set.mem_ofPred_eq]
    refine or_congr Iff.rfl ⟨fun h Q hQ => ?_, fun h Z => ?_⟩
    · have := h (Stacks.Zeta.primeDivisorOfClosedPoint X.f ⟨Q, hQ⟩)
      rw [Stacks.Zeta.toWeil_val_apply,
        Stacks.Zeta.closedPointOfPrimeDivisor_primeDivisorOfClosedPoint] at this
      rw [hNP Q hQ]
      simpa [Stacks.Zeta.primeDivisorOfClosedPoint] using this
    · have hcl := (Stacks.Zeta.closedPointOfPrimeDivisor X.f Z).2
      have := h Z.genericPoint hcl
      rw [Stacks.Zeta.toWeil_val_apply]
      rw [show Z.genericPoint = (Stacks.Zeta.closedPointOfPrimeDivisor X.f Z).1 from rfl,
        hNP _ hcl] at this
      exact this
  -- the coordinate is `k`-linear
  let : Module k Γ(L, ⊤) :=
    Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k X.C L
  let cl : Γ(L, ⊤) →ₗ[k] X.C.functionField :=
    { toFun := c
      map_add' := hcadd
      map_smul' := fun a t => by
        rw [RingHom.id_apply, Algebra.smul_def]
        exact hcsmul _ t }
  -- the basis `b` of `Γ(C, L)` with coordinates `ℓ`
  have hmem : ∀ i, ∃ t, c t = ℓ i := fun i =>
    (hrange (ℓ i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  choose b hb using hmem
  have hclb : cl ∘ b = ℓ := funext hb
  have hli : LinearIndependent k b :=
    LinearIndependent.of_comp cl (hclb ▸ hℓ.linearIndependent)
  have hsp : ⊤ ≤ Submodule.span k (Set.range b) := by
    intro t _
    obtain ⟨t', ht', heq⟩ : c t ∈ (Submodule.span k (Set.range b)).map cl := by
      rw [Submodule.map_span, ← Set.range_comp, hclb]
      exact (hrange (c t)).1 ⟨t, rfl⟩
    rw [← hcinj heq]
    exact ht'
  let B : Module.Basis (Fin (n + 1)) k Γ(L, ⊤) := Module.Basis.mk hli hsp
  have hcB : ∀ i, c (B i) = ℓ i := fun i => by rw [Module.Basis.mk_apply hli hsp i, hb]
  obtain ⟨-, hx, hci, α, hαiso, -⟩ := X.isClosedImmersion_toProjectiveSpaceOver N hN L hLc B
  have : IsIso α := hαiso
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let e : L ≅ (Scheme.Modules.pullback
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑B hx X.f)).obj
      ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)) :=
    (asIso α).symm ≪≫
      ((Scheme.Modules.pullbackComp (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑B hx X.f)
        (projectiveSpaceOver.toIntegralAtUniverse n _)).app _).symm
  have hinv := Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e
  refine ⟨ℓ, hℓ, ?_, Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑B hx X.f,
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _, hci,
    hinv, ?_, ?_⟩
  · -- `ℓ` has no base points: some `Bᵢ` does not vanish at each point
    intro q hq
    obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _ hx q
    refine ⟨i, ?_⟩
    have h := hcord (B i) (PrimeDivisor.ofCoheightOne q hq)
      (by rw [PrimeDivisor.genericPoint_ofCoheightOne]; exact hi)
    rw [PrimeDivisor.genericPoint_ofCoheightOne, Stacks.Zeta.toWeil_val_apply, hcB] at h
    have hcl := (Stacks.Zeta.closedPointOfPrimeDivisor X.f (PrimeDivisor.ofCoheightOne q hq)).2
    have hq' : (Stacks.Zeta.closedPointOfPrimeDivisor X.f (PrimeDivisor.ofCoheightOne q hq)).1 =
        q := PrimeDivisor.genericPoint_ofCoheightOne q hq
    rw [← hNP _ hcl, hq'] at h
    exact h
  · -- the class of `φ^* 𝒪(1)`
    rw [← hLc]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e.symm⟩
  · -- the chart formula
    intro _ j ν _
    have hj0 : ℓ j ≠ 0 := hℓ.linearIndependent.ne_zero j
    have : Nonempty (Stacks.ProjectiveFromSections.nvCover ⇑B j) :=
      ⟨⟨genericPoint X.C, hcnv (B j) (by rw [hcB]; exact hj0)⟩⟩
    rw [germToFunctionField_chart_eq ⇑B hx X.f j ν,
      germToFunctionField_ratio_eq_div _ j ν hcratio (by rw [hcB]; exact hj0), hcB, hcB]

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule
  MvPolynomial.gradedAlgebra in
open Classical in
/-- **The embedding `φ_B` with generic coordinates.** For `s` large, a basis `y` of
`H⁰(C × C, 𝒪(B))`, `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ`, giving a closed immersion
`φ_B` with `φ_B^* 𝒪(1)` of class `B`, and generic for the projections `π_{ab}` of the generic
basis `x` (hypothesis (B)). -/
private theorem exists_B_data {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f) [IsIntegral X.C]
    [IsLocallyNoetherian X.C] [IsIntegral (pullback X.f X.f)]
    [IsLocallyNoetherian (pullback X.f X.f)]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      BombieriSiegel.IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t)) :
    ∃ (sB : ℕ) (_ : 1 ≤ sB) (eΔ : ↥(pullback X.f X.f : Scheme.{u}))
      (_ : IsGenericPoint eΔ (Set.range (pullback.diagonal X.f).base))
      (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
      (_ : ∀ q, DB q =
        (sB + 1 : ℤ) * X.P.sum (fun c a =>
          if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
        (sB + 1 : ℤ) * X.P.sum (fun c a =>
          if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
        (if q = eΔ then 1 else 0))
      (m : ℕ) (y : Fin (m + 1) → (pullback X.f X.f).functionField)
      (hy : ∀ i, y i ≠ 0)
      (_ : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
      (_ : LinearIndependent k y)
      (_ : ∀ h : (pullback X.f X.f).functionField,
        (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
      (_ : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
        ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
      (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
      (_ : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
        pullback.fst X.f X.f ≫ X.f)
      (_ : IsClosedImmersion φB)
      (hinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
        ((Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))),
      Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        ((Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr hinv) = X.vojtaClass sB sB (-1) ∧
      (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫ φB =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
          (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
          (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
            ((Ne.isUnit (hy 0)).map
              (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
          ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
        0 < (pullback X.f X.f).ord (y i) q + DB q →
        0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
          0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
        i.val = 1 → i'.val = 2 → ∀ q q',
        0 < (pullback X.f X.f).ord (y i) q + DB q →
        0 < (pullback X.f X.f).ord (y i') q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
          0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
        0 < (pullback X.f X.f).ord (y i) q + DB q →
        0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
        0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
        ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
        ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
          (∀ r ∈ 𝔪, r ≠ 0 →
            (∀ q, q ⤳ p → Order.coheight q = 1 →
              0 ≤ (pullback X.f X.f).ord
                (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
            ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
              0 < (pullback X.f X.f).ord
                (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
          ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0) := by
  -- the generic point of the diagonal
  have heΔ : IsGenericPoint ((pullback.diagonal X.f).base (genericPoint X.C))
      (Set.range (pullback.diagonal X.f).base) := by
    have h := (genericPoint_spec X.C).image (pullback.diagonal X.f).base.hom.continuous
    rwa [Set.image_univ,
      (pullback.diagonal X.f).isClosedEmbedding.isClosed_range.closure_eq] at h
  -- the very ample class `B` and a basis `y` of `H⁰(𝒪(B))` giving `φ_B`
  obtain ⟨s₀, hs₀⟩ := BombieriSiegel.exists_vojtaEmbedding_coordinates X (pullback.diagonal X.f)
    (pullback.diagonal_fst X.f) (pullback.diagonal_snd X.f) hkX
  set sB : ℕ := max 1 s₀
  set DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ := fun q =>
    (sB + 1 : ℤ) * X.P.sum (fun c a =>
      if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
    (sB + 1 : ℤ) * X.P.sum (fun c a =>
      if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
    (if q = (pullback.diagonal X.f).base (genericPoint X.C) then 1 else 0)
  obtain ⟨m, y, hy, hyD, hyli, hyspan, hybpf, φB, hφB, hφBci, hφBinv, hφBB, hφBy⟩ :=
    hs₀ sB (le_max_right _ _) heΔ DB (fun q => rfl)
  have := hφBci
  have := hφBinv
  -- (B) for a suitable change of coordinates `g`
  obtain ⟨g, hy', hyD', hyli', hyspan', hybpf', ⟨φB', hφB', hci', hinv', hcl', hφBy'⟩, hG1, hG1',
      hG2, hG3⟩ := exists_isGenericForProjections_map X hg N hN hn x hx hxbpf
    (pullback.diagonal X.f) (pullback.diagonal_fst X.f) (pullback.diagonal_snd X.f) φNP hφNP hφNPx
    hkC hkX ι₁ ι₂ hι₁ hι₂ sB (le_max_left _ _) heΔ DB (fun q => rfl) y hy hyD hyli hyspan hybpf
    φB hφB hφBB hφBy
  exact ⟨sB, le_max_left _ _, _, heΔ, DB, fun q => rfl, m, _, hy', hyD', hyli', hyspan', hybpf',
    φB', hφB', hci', hinv', hcl', hφBy', hG1, hG1', hG2, hG3⟩

/-- The data of Vojta's theorem exist for a curve with a rational point. -/
private theorem exists_vojtaGamma {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p : {x : X.C // IsClosed ({x} : Set X.C)}) (hp : X.f.residueDegree p.1 = 1)
    (hP : X.P = Finsupp.single p 1) :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ γ : ℝ, 1 < γ ∧ ∀ (K : IntermediateField k kbar) [FiniteDimensional k K],
      haveI := A.isAbelianVariety
      letI := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
      letI : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :=
        Hom.commGroup
      let S := {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f |
        (∃ q : Spec (.of K) ⟶ X.C,
          z.left = Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ q) ∧
        γ ≤ √(pair z z)}
      S.Finite := by
  intro pair
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : IsIntegral X.C := GeometricallyIntegral.isIntegral_of_subsingleton X.f
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : IsLocallyNoetherian (pullback X.f X.f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst X.f X.f ≫ X.f)
  have : IsIntegral (pullback X.f X.f) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst X.f X.f)
  -- (N): the generic basis `x` of `L(N P)` and the embedding `φ_{NP}`
  obtain ⟨x, hx, hxbpf, φNP, hφNP, hφNPci, hφNPinv, hφNPL, hφNPx⟩ :=
    exists_NP_data X hg p hp hP (2 * genus X.f + 1) le_rfl rfl
  have := hφNPci
  have := hφNPinv
  -- the `k`-structures of the function fields and the pull-backs `pr₁^*`, `pr₂^*`
  let : Algebra k X.C.functionField := functionFieldAlgebra k X.f
  let : Algebra k (pullback X.f X.f).functionField := RingHom.toAlgebra
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.fst X.f X.f ≫ X.f).appTop ≫
      (pullback X.f X.f).presheaf.germ ⊤ _ trivial).hom
  have hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  have : Surjective X.f := ⟨fun z => ⟨genericPoint X.C, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.fst X.f X.f) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.f X.f).flip
      inferInstance
  have : Surjective (pullback.snd X.f X.f) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback X.f X.f)
      inferInstance
  have : Nonempty (⊤ : X.C.Opens) := ⟨⟨genericPoint X.C, trivial⟩⟩
  have hcomm : ∀ (pr : pullback X.f X.f ⟶ X.C) [IsDominant pr],
      pr ≫ X.f = pullback.fst X.f X.f ≫ X.f → ∀ c : k,
        functionFieldMap pr (algebraMap k X.C.functionField c) =
          algebraMap k (pullback X.f X.f).functionField c := by
    intro pr _ hpr c
    have : Nonempty (pr ⁻¹ᵁ (⊤ : X.C.Opens)) := ⟨⟨genericPoint _, trivial⟩⟩
    refine (Faltings.functionFieldMap_germToFunctionField pr (O := ⊤) _).trans ?_
    rw [hkX, ← hpr]
    rfl
  let ι₁ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField :=
    { toRingHom := functionFieldMap (pullback.fst X.f X.f)
      commutes' := hcomm _ rfl }
  let ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField :=
    { toRingHom := functionFieldMap (pullback.snd X.f X.f)
      commutes' := hcomm _ pullback.condition.symm }
  have hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)), ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t) :=
    fun U _ _ t => Faltings.functionFieldMap_germToFunctionField _ t
  have hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)), ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t) :=
    fun U _ _ t => Faltings.functionFieldMap_germToFunctionField _ t
  -- (B): the basis `y` and the embedding `φ_B`
  obtain ⟨sB, hsB, eΔ, heΔ, DB, hDB, m, y, hy, hyD, hyli, hyspan, hybpf, φB, hφB, hφBci,
      hφBinv, hφBB, hφBy, hBG1, hBG1', hBG2, hBG3⟩ :=
    exists_B_data X hg (2 * genus X.f + 1) le_rfl rfl x hx hxbpf φNP hφNP hφNPx
      rfl hkX ι₁ ι₂ hι₁ hι₂
  have := hφBci
  have := hφBinv
  obtain ⟨γ, hγ, hK⟩ := finite_setOf_le_neronNorm_abelJacobi X A hg j hj D hrad hsupp kbar
    (2 * genus X.f + 1) le_rfl rfl x hx hxbpf (pullback.diagonal X.f)
    (pullback.diagonal_fst X.f) (pullback.diagonal_snd X.f) φNP hφNP hφNPL hφNPx
    (pullback.map _ _ _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
      (by rw [Category.comp_id, hφNP]))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) rfl hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ DB hDB
    y hy hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3
  exact ⟨γ, hγ, fun K _ => (hK K).1⟩

/-- A curve of genus at least two with a rational point has finitely many rational points. -/
private theorem finite_of_comp_eq_id (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f]
    [Smooth f] [GeometricallyIntegral f] (hg : 2 ≤ genus f)
    (σ₀ : Spec (.of k) ⟶ C) (hσ₀ : σ₀ ≫ f = 𝟙 _) :
    {σ : Spec (.of k) ⟶ C | σ ≫ f = 𝟙 _}.Finite := by
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have : IsSmoothProjectiveCurve k f := {}
  -- the rational point `σ₀` as a divisor of degree one
  have hσp : Set.range σ₀.base = {σ₀.base (IsLocalRing.closedPoint k)} := by
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨w, hw⟩ => hw ▸ congrArg _ (Subsingleton.elim w _), fun h => ⟨_, h.symm⟩⟩
  have hσcl : IsClosed ({σ₀.base (IsLocalRing.closedPoint k)} : Set C) := by
    have := isClosedImmersion_of_comp_eq_id f σ₀ hσ₀
    exact hσp ▸ σ₀.isClosedEmbedding.isClosed_range
  let p : {x : C // IsClosed ({x} : Set C)} := ⟨_, hσcl⟩
  have hp : f.residueDegree p.1 = 1 := (Stacks.Chow.residueDegree_eq_one_of_section f σ₀ hσ₀ _).1
  let X : CurveWithDegreeOneDivisor k :=
    { C := C, f := f, P := Finsupp.single p 1, degree_P := by simp [hp] }
  obtain ⟨⟨A⟩, -⟩ := Jacobian.nonempty_and_existsUnique_iso k X
  obtain ⟨j, hj, -⟩ := existsUnique_isAbelJacobiMap X A
  obtain ⟨D, hD, hrad, hsupp⟩ : ∃ D : A.J.left.IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧ D.radical = D ∧
        (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj := by
    have := A.isAbelianVariety
    have : Smooth A.J.hom := smooth_of_isAbelianVariety k A.J
    have : IsLocallyNoetherian A.J.left := LocallyOfFiniteType.isLocallyNoetherian A.J.hom
    obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A (one_le_two.trans hg) j hj
    have := Z.integral
    have hZv : Z.idealSheaf = Scheme.IdealSheafData.vanishingIdeal Z.idealSheaf.support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
    refine ⟨Z.idealSheaf, ?_, ?_, hZ⟩
    · refine isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid
        Z.idealSheaf Z.codimension_one fun x _ => ?_
      have := isRegularLocalRing_stalk_of_smooth_over_field A.J.hom x
      exact IsRegularLocalRing.uniqueFactorizationMonoid _
    · rw [← Scheme.IdealSheafData.vanishingIdeal_support, ← hZv]
  let kbar := AlgebraicClosure k
  obtain ⟨γ, hγ, hS⟩ := exists_vojtaGamma X A hg j hj D hrad hsupp kbar p hp rfl
  have hfin₁ := hS ⊥
  have hfin₂ := finite_setOf_neronNorm_abelJacobi_lt X A hg j hj D hrad hsupp kbar ⊥ γ
    (by linarith)
  set ι : Spec (.of kbar) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    with hι
  have : IsDominant ι := by
    refine ⟨?_⟩
    rw [DenseRange, show Set.range ι.base = Set.univ from Set.eq_univ_of_forall fun x => by
      obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (.of kbar)))
      exact ⟨y, Subsingleton.elim _ _⟩]
    exact dense_univ
  have hT := (hfin₁.union hfin₂).image (fun z => z.left)
  refine Set.Finite.of_finite_image (f := fun σ => ι ≫ σ) (hT.subset ?_)
    fun σ hσ τ hτ h => ext_of_isDominant_of_isSeparated f
      ((show σ ≫ f = 𝟙 _ from hσ).trans (show τ ≫ f = 𝟙 _ from hτ).symm) ι h
  · rintro _ ⟨σ, hσ, rfl⟩
    have hw : (ι ≫ σ) ≫ X.f = ι := by
      change (ι ≫ σ) ≫ f = ι
      rw [Category.assoc, show σ ≫ f = 𝟙 _ from hσ, Category.comp_id]
    let z : Over.mk ι ⟶ Over.mk X.f := Over.homMk (ι ≫ σ) hw
    have hq : ∃ q : Spec (.of (⊥ : IntermediateField k kbar)) ⟶ X.C,
        z.left = Spec.map (CommRingCat.ofHom (algebraMap (⊥ : IntermediateField k kbar) kbar))
          ≫ q := by
      refine ⟨Spec.map (CommRingCat.ofHom (algebraMap k (⊥ : IntermediateField k kbar))) ≫ σ, ?_⟩
      change ι ≫ σ = _
      rw [← Category.assoc, ← Spec.map_comp, hι]
      congr 2
    refine ⟨z, ?_, rfl⟩
    by_cases hle : γ ≤ √(neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (z ≫ j)))
    · exact Or.inl ⟨hq, hle⟩
    · exact Or.inr ⟨hq, lt_of_not_ge hle⟩

end

/-- **Faltings' theorem (the Mordell conjecture).** Let `k` be a number field and `C` a smooth
projective geometrically integral curve over `k` (`f : C ⟶ Spec k`) of genus
`AlgebraicGeometry.genus f = dim_k H¹(C, 𝒪_C) ≥ 2`. Then `C` has only finitely many
`k`-rational points, i.e. finitely many sections `σ : Spec k ⟶ C` of `f`. -/
@[faltings "thm_bvr_finiteness_rational_points"]
public theorem finite_setOf_comp_eq_id_of_two_le_genus (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f]
    [Smooth f] [GeometricallyIntegral f] (hg : 2 ≤ genus f) :
    {σ : Spec (.of k) ⟶ C | σ ≫ f = 𝟙 _}.Finite := by
  rcases Set.eq_empty_or_nonempty {σ : Spec (.of k) ⟶ C | σ ≫ f = 𝟙 _} with h | ⟨σ₀, hσ₀⟩
  · exact h ▸ Set.finite_empty
  · exact finite_of_comp_eq_id k f hg σ₀ hσ₀

end Faltings
