module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen

/-!
# A morphism to projective space at the generic point

If a morphism `φ : Y ⟶ ℙʳ_S` from an integral scheme restricts at the generic point to the point
`(s₀ : … : s_r)` with `s₀ ≠ 0`, then the generic point lies in the standard open `φ⁻¹ D₊(T₀)`,
and the pull-back of `T_ν / T₀` has germ `s_ν / s₀` there.

## Main results

* `Faltings.BombieriRoth.exists_germ_app_ratio_eq_div`: the affine coordinates of `φ` at the
  generic point.
* `Faltings.BombieriRoth.exists_germ_app_ratio_eq_div_of_chart`: the same, for `φ` given by its
  chart functions `T_ν / T_j ↦ s_ν / s_j` with every `s_ν ≠ 0`; the generic point then lies in
  every chart.
* `Faltings.BombieriRoth.fromSpecStalk_appLE_apply`: the sections of `Spec 𝒪_{Y,x} ⟶ Y` are the
  germs at `x`.
-/

namespace Faltings.BombieriRoth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

/-- The sections of `Spec 𝒪_{Y,x} ⟶ Y` over an open `W` are the germs at `x`, restricted. -/
public theorem fromSpecStalk_appLE_apply {Y : Scheme.{u}} (x : Y) {U : Y.Opens} (hx : x ∈ U)
    {W : (Spec (Y.presheaf.stalk x)).Opens} (e : W ≤ Y.fromSpecStalk x ⁻¹ᵁ U) (t : Γ(Y, U)) :
    (Y.fromSpecStalk x).appLE U W e t = resTop W ((Scheme.ΓSpecIso _).inv
      (Y.presheaf.germ U x hx t)) := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [CommRingCat.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The affine coordinates of a morphism to `ℙʳ` at the generic point.** If `φ : Y ⟶ ℙʳ_S`
restricts at the generic point to the point `(s₀ : … : s_r)` with `s₀ ≠ 0`, then the generic
point lies in `φ⁻¹ D₊(T₀)`, and the pull-back of `T_ν / T₀` has germ `s_ν / s₀` there. -/
public theorem exists_germ_app_ratio_eq_div {Y S : Scheme.{u}} [IsIntegral Y] {r : ℕ}
    (φ : Y ⟶ projectiveSpaceOver r S) (s : Fin (r + 1) → Y.functionField) (hs0 : s 0 ≠ 0)
    (hspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) = ⊤)
    (σ : Spec (.of Y.functionField) ⟶ S)
    (hφ : Y.fromSpecStalk (genericPoint Y) ≫ φ =
      toProjectiveSpaceOver (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) hspan σ) :
    ∃ h : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)), ∀ ν : Fin (r + 1),
      Y.presheaf.germ _ (genericPoint Y) h (φ.app _
        ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
              (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
        s ν / s 0 := by
  set j := Y.fromSpecStalk (genericPoint Y) with hj
  set sK : Fin (r + 1) → Γ(Spec (.of Y.functionField), ⊤) :=
    fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i) with hsK
  set B := Proj.basicOpen (coordGrading.{u} r) (MvPolynomial.X 0) with hBdef
  have hX0 : (MvPolynomial.X 0 : coordRing.{u} r) ∈ coordGrading.{u} r 1 :=
    X_mem_coordGrading_one 0
  set ψ' := φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S with hψ'
  have hg : j ≫ ψ' = toProjectiveSpaceAtUniverse sK hspan := by
    rw [hψ', ← Category.assoc, hφ, toProjectiveSpaceOver_snd]
  have hunit : IsUnit (sK 0) := (Ne.isUnit hs0).map _
  have hpre : toProjectiveSpaceAtUniverse sK hspan ⁻¹ᵁ B = ⊤ := by
    rw [hBdef, preimage_basicOpen]
    exact Scheme.basicOpen_of_isUnit _ hunit
  have hpre' : j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) = ⊤ := by
    change (j ≫ ψ') ⁻¹ᵁ B = ⊤
    rw [hg, hpre]
  have hmem : genericPoint Y ∈ ψ' ⁻¹ᵁ B := by
    have h2 : IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)) ∈ j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) := by
      rw [hpre']; trivial
    have h3 : j (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
      Scheme.fromSpecStalk_closedPoint
    rw [← h3]
    exact h2
  refine ⟨hmem, fun ν => ?_⟩
  set W := (Spec (.of Y.functionField)).basicOpen (sectionsHom sK (MvPolynomial.X 0)) with hW
  have hWtop : W = ⊤ := by
    rw [hW, sectionsHom_X]
    exact Scheme.basicOpen_of_isUnit _ hunit
  have : Nonempty W := by
    rw [hWtop]
    exact ⟨⟨IsLocalRing.closedPoint Y.functionField, trivial⟩⟩
  have hinjF : Function.Injective (fun z : Y.functionField =>
      resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv z)) :=
    (map_injective_of_isIntegral _ (homOfLE le_top)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Y.functionField)).inv).1
  have hle : W ≤ j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) := by
    rw [hpre']
    exact le_top
  have hXν : (MvPolynomial.X ν : coordRing.{u} r) ∈ coordGrading.{u} r (1 • 1) := by
    rw [smul_eq_mul, mul_one]; exact X_mem_coordGrading_one ν
  set a := HomogeneousLocalization.Away.mk (coordGrading.{u} r) hX0 1 (MvPolynomial.X ν) hXν
    with ha
  apply hinjF
  dsimp only
  refine Eq.trans (fromSpecStalk_appLE_apply (genericPoint Y) hmem hle
    (ψ'.app B (Proj.awayToSection (coordGrading.{u} r) (MvPolynomial.X 0) a))).symm ?_
  have hc : ∀ (g g' : Spec (.of Y.functionField) ⟶ projectiveSpaceAtUniverse.{u} r) (h : g = g')
      (e : W ≤ g ⁻¹ᵁ B), g.appLE B W e = g'.appLE B W (h ▸ e) := by
    intro g g' h e
    subst h
    rfl
  have h2 : ψ'.app B ≫ j.appLE _ W hle =
      (toProjectiveSpaceAtUniverse sK hspan).appLE B W (hg ▸ hle) :=
    (Scheme.Hom.comp_appLE j ψ' B W hle).symm.trans (hc _ _ hg hle)
  have h3 := Stacks.LinearSystemScheme.awayToSection_comp_appLE_fromOfGlobalSections
    (𝒜 := coordGrading.{u} r) (sectionsHom sK) (map_irrelevant_eq_top sK hspan) one_pos hX0
  have h4 : (j.appLE _ W hle) (ψ'.app B (Proj.awayToSection (coordGrading.{u} r)
      (MvPolynomial.X 0) a)) = Stacks.ProjGlobalSectionsAppTop.projAwayHom (coordGrading.{u} r)
        (sectionsHom sK) a := by
    have h5 := congrArg (fun F => F.hom a) h3
    simp only [CommRingCat.hom_ofHom] at h5
    rw [← h5]
    change (ψ'.app B ≫ j.appLE _ W hle) _ = _
    rw [h2]
    rfl
  rw [h4, Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk, pow_one]
  have hu : resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
      resTop W (sectionsHom sK (MvPolynomial.X 0)) = 1 :=
    (isUnit_resTop_basicOpen (sectionsHom sK (MvPolynomial.X 0))).val_inv_mul
  have hv : resTop W (sK 0) *
      resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹) = 1 := by
    rw [← map_mul, hsK, ← map_mul, mul_inv_cancel₀ hs0, map_one, map_one]
  have e : ∀ i, resTop W (sectionsHom sK (MvPolynomial.X i)) = resTop W (sK i) := fun i => by
    rw [sectionsHom_X]
  change resTop W (sectionsHom sK (MvPolynomial.X ν)) *
    resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) = _
  rw [e ν, div_eq_mul_inv, map_mul, map_mul]
  congr 1
  calc resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0))
      = resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
          (resTop W (sK 0) * resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹)) := by
        rw [hv, mul_one]
    _ = (resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
          resTop W (sectionsHom sK (MvPolynomial.X 0))) *
          resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹) := by
        rw [e 0, mul_assoc]
    _ = _ := by rw [hu, one_mul]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The charts of a morphism to `ℙʳ` given by its chart functions.** Let `φ : Y ⟶ ℙʳ_S` be a
morphism from an integral scheme whose chart functions `φ^*(T_ν / T_j)` are `s_ν / s_j` in the
function field on every nonempty chart `φ⁻¹ D₊(T_j)`, with every `s_ν ≠ 0`. Then the generic
point lies in every chart `φ⁻¹ D₊(T_l)`, and the germ there of `φ^*(T_ν / T_l)` is
`s_ν / s_l`. -/
public theorem exists_germ_app_ratio_eq_div_of_chart {Y S : Scheme.{u}} [IsIntegral Y] {r : ℕ}
    (φ : Y ⟶ projectiveSpaceOver r S) (s : Fin (r + 1) → Y.functionField) (hs : ∀ i, s i ≠ 0)
    (hφ : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let U : Fin (r + 1) → Y.Opens := fun j =>
        φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (r + 1)) [Nonempty (U j)],
        (Y.germToFunctionField (U j)).hom
          (φ.app _ ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          s ν / s j)
    (l : Fin (r + 1)) :
    ∃ h : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X l)), ∀ ν : Fin (r + 1),
      Y.presheaf.germ _ (genericPoint Y) h (φ.app _
        ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X l)
            (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ l) 1
              (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
        s ν / s l := by
  set g := φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S with hg
  -- some chart `D₊(T_{j₀})` contains the image of the generic point
  have hη : g.base (genericPoint Y) ∈ (⨆ i : Fin (r + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)) := by
    rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top]; trivial
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hη
  have hj₀' : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j₀)) := hj₀
  have : Nonempty (φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j₀))) := ⟨⟨_, hj₀'⟩⟩
  -- on that chart `T_l / T_{j₀}` is `s_l / s_{j₀} ≠ 0` at the generic point, so `T_l ≠ 0` there
  have hmem : genericPoint Y ∈ Y.basicOpen (φ.app _
      ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j₀) (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X _ j₀) 1 (MvPolynomial.X l)
            (by simpa using MvPolynomial.isHomogeneous_X _ l))))) := by
    rw [Scheme.mem_basicOpen _ _ _ hj₀']
    refine Ne.isUnit ?_
    have e := hφ j₀ l
    refine fun h0 => div_ne_zero (hs l) (hs j₀) (e.symm.trans ?_)
    exact h0
  have h3 : g.base (genericPoint Y) ∈ (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).basicOpen
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j₀) (HomogeneousLocalization.Away.mk _
          (MvPolynomial.isHomogeneous_X _ j₀) 1 (MvPolynomial.X l)
          (by simpa using MvPolynomial.isHomogeneous_X _ l))) := by
    have : genericPoint Y ∈ g ⁻¹ᵁ (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).basicOpen
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j₀) (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X _ j₀) 1 (MvPolynomial.X l)
            (by simpa using MvPolynomial.isHomogeneous_X _ l))) := by
      erw [Scheme.preimage_basicOpen]; exact hmem
    exact this
  erw [Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk _ _ one_pos] at h3
  have hl : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X l)) := h3.2
  have : Nonempty (φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X l))) := ⟨⟨_, hl⟩⟩
  exact ⟨hl, fun ν => hφ l ν⟩

end Faltings.BombieriRoth
