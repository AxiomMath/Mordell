module
public import Mordell.BombieriVojta.Admissible.BiorderIdeal
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Norm.Relation
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.Polynomial.HasseDeriv
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.BombieriVojta.Norm.SectionRatioEval
public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import Mordell.BombieriVojta.Admissible.VanishingTransferTaylor
public import Mordell.BombieriVojta.Admissible.VanishingTransferSections

/-!
# `T` vanishes at least as much as `s`

Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `N ≥ 2g + 1`, `n = N - g`, and `x₀, …, xₙ` a generic basis of `L(NP)` giving
`φ_{NP} : C → ℙⁿ` and `ψ = φ_{NP} × φ_{NP}`; let `φ_B : C × C → ℙᵐ` be given by a basis
`y₀, …, y_m` of `H⁰(C × C, 𝒪(B))` generic for the projections, and
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. Let `s ≠ 0` be a global section of `𝒪(V)` with
representative `{F_i}` over `k`, let `K ⊇ k` be a number field, `C_K` the base change of `C`, and
`z, w` `K`-points of `C_K` outside the exceptional set `Z`; let `1 ≤ a, b ≤ n` and
`p₀ = (ξ_a(z), ξ'_b(w))`. Let `(U_i, V_i)` be reduced representations of the norms of
`η_i = y_i / y_0` down to `k(ξ_a, ξ'_b)`, and `i₀ ≠ 0` with `U_{i₀}(p₀) ≠ 0`; put
`T = T_{i₀} = G_0 / V_{i₀}^d`. If `e` is a local generator of `𝒪(V)` on `C_K × C_K` at `(z, w)`
and `σ = s / e` lies in `J_{A,B}`, then every divided derivative `∂_{(i₁, i₂)} T` with `i₁ ≤ A`,
`i₂ ≤ B` vanishes at `p₀`.

The proof writes `s / e_j = F_j(ξ, ξ')` for a chart where `y_j(z, w) ≠ 0`, deduces
`F_{i₀}(ξ, ξ') ∈ J_{A,B}`, passes to the norm `G_{i₀}` by the local factor of the norm, then to
`T = G_{i₀} U_{i₀}^{-d}` since `U_{i₀}` is a unit near `p₀`, and reads off the Taylor
coefficients of `T` at `p₀` in `K⟦ξ_a - ξ_a(z), ξ'_b - ξ'_b(w)⟧`.

## Main results

* `Faltings.BombieriRoth.eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal`: if
  `s / e ∈ J_{A,B}` then `∂_{(i₁, i₂)} T (p₀) = 0` for `i₁ ≤ A`, `i₂ ≤ B`.

## Implementation notes

The standing data are over the number field `k`, in the form of
`Faltings.BombieriRoth.exists_neg_le_neronPairing_of_isAdmissiblePair`: the curve is a
`Faltings.CurveWithDegreeOneDivisor`, `C × C = pullback X.f X.f`, and the norms, the reduced
representations and `T` live in `k(C × C)` over `k⟮ξ_a, ξ'_b⟯`. The source's points of
`C(k̄)` are read on the base change `C_K` to a number field `K` over which they are defined, as
in the main inequality: `(z, w)` is a `K`-point `p_K` of `C_K × C_K`, the line bundle there is
`vojtaLineBundle ψK φK δ₁ δ₂ d` for the base changes `ψK, φK` of `ψ, φ_B`, with the section `s_K`
represented by the same `F`, and `J_{A,B}` is `Faltings.completedStalkBiorderIdeal` at `p_K`.
The ring `R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k`, mapped to `k⟮ξ_a, ξ'_b⟯` by
`X₀ ↦ ξ_a`, `X₁ ↦ ξ'_b`; the polynomial `T` is any element of `R` with image `polynomialT …` (it
exists and is unique). The value `ξ_a(z)` is the constant `t₀ ∈ K` with `g - t₀ ∈ 𝔪_z` for the
germ `g` of `π^* ξ_a` at `z`, written as in `Faltings.BombieriSiegel.exceptionalSet`, and
`∂_I T(p₀)` is `aeval ![t₀, t₀'] (∂_I T)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 633.
-/

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriRoth.VanishingTransfer

namespace Taylor

open _root_.MvPolynomial

variable {K : Type*} [CommRing K]

/-- Divided derivatives commute with a change of coefficients. -/
private theorem hasseDeriv_map {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (I : σ →₀ ℕ) (p : MvPolynomial σ R) :
    Faltings.MvPolynomial.hasseDeriv I (MvPolynomial.map f p) =
      MvPolynomial.map f (Faltings.MvPolynomial.hasseDeriv I p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial J r =>
    rw [MvPolynomial.map_monomial, Faltings.MvPolynomial.hasseDeriv_monomial,
      Faltings.MvPolynomial.hasseDeriv_monomial, MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, MvPolynomial.map_monomial]
    simp

end Taylor

/-! ### Affine coordinates and the generic point of `C × C` -/

namespace Charts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Faltings Faltings.BombieriRoth Faltings.BombieriSiegel Faltings.BombieriVojta

open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem exists_germ_app_ratio_eq_div_of_ne_zero {Y S : Scheme.{u}} [IsIntegral Y] {r : ℕ}
    (φ : Y ⟶ projectiveSpaceOver r S) (s : Fin (r + 1) → Y.functionField) (k : Fin (r + 1))
    (hsk : s k ≠ 0)
    (hspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) = ⊤)
    (σ : Spec (.of Y.functionField) ⟶ S)
    (hφ : Y.fromSpecStalk (genericPoint Y) ≫ φ =
      toProjectiveSpaceOver (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) hspan σ) :
    ∃ h : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)), ∀ ν : Fin (r + 1),
      Y.presheaf.germ _ (genericPoint Y) h (φ.app _
        ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X k)
            (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ k) 1
              (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
        s ν / s k := by
  set j := Y.fromSpecStalk (genericPoint Y) with hj
  set sK : Fin (r + 1) → Γ(Spec (.of Y.functionField), ⊤) :=
    fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i) with hsK
  set B := Proj.basicOpen (coordGrading.{u} r) (MvPolynomial.X k) with hBdef
  have hX0 : (MvPolynomial.X k : coordRing.{u} r) ∈ coordGrading.{u} r 1 :=
    X_mem_coordGrading_one k
  set ψ' := φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S with hψ'
  have hg : j ≫ ψ' = toProjectiveSpaceAtUniverse sK hspan := by
    rw [hψ', ← Category.assoc, hφ, toProjectiveSpaceOver_snd]
  have hunit : IsUnit (sK k) := (Ne.isUnit hsk).map _
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
  set W := (Spec (.of Y.functionField)).basicOpen (sectionsHom sK (MvPolynomial.X k)) with hW
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
    (ψ'.app B (Proj.awayToSection (coordGrading.{u} r) (MvPolynomial.X k) a))).symm ?_
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
      (MvPolynomial.X k) a)) = Stacks.ProjGlobalSectionsAppTop.projAwayHom (coordGrading.{u} r)
        (sectionsHom sK) a := by
    have h5 := congrArg (fun F => F.hom a) h3
    simp only [CommRingCat.hom_ofHom] at h5
    rw [← h5]
    change (ψ'.app B ≫ j.appLE _ W hle) _ = _
    rw [h2]
    rfl
  rw [h4, Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk, pow_one]
  have hu : resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X k)) *
      resTop W (sectionsHom sK (MvPolynomial.X k)) = 1 :=
    (isUnit_resTop_basicOpen (sectionsHom sK (MvPolynomial.X k))).val_inv_mul
  have hv : resTop W (sK k) *
      resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s k)⁻¹) = 1 := by
    rw [← map_mul, hsK, ← map_mul, mul_inv_cancel₀ hsk, map_one, map_one]
  have e : ∀ i, resTop W (sectionsHom sK (MvPolynomial.X i)) = resTop W (sK i) := fun i => by
    rw [sectionsHom_X]
  change resTop W (sectionsHom sK (MvPolynomial.X ν)) *
    resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X k)) = _
  rw [e ν, div_eq_mul_inv, map_mul, map_mul]
  congr 1
  calc resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X k))
      = resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X k)) *
          (resTop W (sK k) * resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s k)⁻¹)) := by
        rw [hv, mul_one]
    _ = (resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X k)) *
          resTop W (sectionsHom sK (MvPolynomial.X k))) *
          resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s k)⁻¹) := by
        rw [e k, mul_assoc]
    _ = _ := by rw [hu, one_mul]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Off the chart `D₊(T₀)` of `ℙʳ_S`, the affine coordinate `T₀ / T_k` of the chart `D₊(T_k)` is
not a unit. -/
private theorem not_isUnit_germ_ratio (S : Scheme.{u}) (r : ℕ) (k : Fin (r + 1))
    (y : projectiveSpaceOver r S)
    (hy : y ∈ projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k))
    (hy0 : y ∉ projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)) :
    ¬IsUnit ((projectiveSpaceOver r S).presheaf.germ _ y hy
      ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ k) 1
            (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X _ 0))))) := by
  intro hu
  set ψ := projectiveSpaceOver.toIntegralAtUniverse r S with hψ
  have hz : ψ y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X k) := hy
  set t := HomogeneousLocalization.Away.mk
    (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
    (MvPolynomial.isHomogeneous_X _ k) 1 (MvPolynomial.X 0)
    (by simpa using MvPolynomial.isHomogeneous_X _ 0) with ht
  have h1 : (projectiveSpaceOver r S).presheaf.germ _ y hy (ψ.app _
      ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)).hom t)) =
      ψ.stalkMap y ((projectiveSpaceAtUniverse.{u} r).presheaf.germ _ (ψ y) hz
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X k)).hom t)) :=
    (Scheme.Hom.germ_stalkMap_apply ψ _ y hz _).symm
  rw [h1] at hu
  have hu' := (isUnit_map_iff (ψ.stalkMap y).hom _).mp hu
  have h2 := congrArg (fun F => F.hom t)
    (ProjectiveSpectrum.Proj.awayToSection_germ
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (MvPolynomial.X k) (ψ y) hz)
  have h4 := hu'
  erw [h2] at h4
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h4
  have h3 := (isUnit_map_iff (Proj.stalkIso'
    (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (ψ y)).symm _).mp h4
  apply hy0
  change ψ y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X 0)
  refine (Proj.mem_basicOpen _ (MvPolynomial.X 0) (ψ y)).mpr fun hmem => ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at h3
  simp only [t, HomogeneousLocalization.Away.mk] at h3
  erw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk] at h3
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at h3
  exact h3 hmem

section Curve

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- At a point of coheight one, a nonzero non-unit of the local ring has positive order. -/
private theorem ord_pos_of_not_isUnit' {x : X} (hx : Order.coheight x = 1)
    {r : X.presheaf.stalk x} (hr0 : r ≠ 0) (hr : ¬IsUnit r) :
    0 < X.ord (algebraMap _ X.functionField r) x := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    Stacks.Chow.krullDimLE_one_stalk_of_coheight_eq_one hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk x) (mem_nonZeroDivisors_of_ne_zero hr0))
  rw [Stacks.Chow.ord_algebraMap_eq_ringOrd hx hr0 hm.symm, Nat.cast_pos]
  by_contra hle
  have hm0 : Ring.ord (X.presheaf.stalk x) r = 0 := by
    simp [← hm, Nat.eq_zero_of_not_pos hle]
  exact hr (Ideal.span_singleton_eq_top.mp
    (Ideal.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp hm0)))

end Curve

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- If `φ : C ⟶ ℙⁿ_S` has chart functions `T_ν / T_j ↦ x_ν / x_j` and `ord_Q x₀ ≤ ord_Q x_i`
for every `i` at a point `Q` of coheight one, then `φ Q` lies in the chart `D₊(T₀)`. -/
public theorem mem_chart_zero_of_ord_le {S C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    {n : ℕ} (φ : C ⟶ projectiveSpaceOver n S) (x : Fin (n + 1) → C.functionField)
    (hx : ∀ i, x i ≠ 0)
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
    (Q : C) (hQ : Order.coheight Q = 1) (hord : ∀ i, C.ord (x 0) Q ≤ C.ord (x i) Q) :
    φ Q ∈ projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0) := by
  by_contra hy0
  have hcov : φ Q ∈ ⨆ i, Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.coordChart n S i := by
    rw [Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.iSup_coordChart_eq_top]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hi' : φ Q ∈ projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) := hi
  obtain ⟨hη, hgerm⟩ := exists_germ_app_ratio_eq_div_of_chart φ x hx hφ i
  have hQi : Q ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)) := hi'
  set t := (projectiveSpaceOver.toIntegralAtUniverse n S).app _
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ i) 1
        (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X _ 0))) with ht
  set r := C.presheaf.germ _ Q hQi (φ.app _ t) with hrdef
  have hr : algebraMap _ C.functionField r = x 0 / x i := by
    rw [← hgerm 0, hrdef]
    exact congr($(C.presheaf.germ_stalkSpecializes (U := φ ⁻¹ᵁ _) hQi
      ((genericPoint_spec C).specializes (Set.mem_univ Q))) (φ.app _ t))
  have hnu : ¬IsUnit r := by
    rw [hrdef, ← Scheme.Hom.germ_stalkMap_apply φ _ Q hi' t]
    intro hu
    exact not_isUnit_germ_ratio S n i (φ Q) hi' hy0 ((isUnit_map_iff (φ.stalkMap Q).hom _).mp hu)
  have hr0 : r ≠ 0 := fun h => by
    rw [h, map_zero] at hr
    exact div_ne_zero (hx 0) (hx i) hr.symm
  have hpos := ord_pos_of_not_isUnit' hQ hr0 hnu
  rw [hr, ord_div (hx 0) (hx i)] at hpos
  have := hord i
  omega

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **A point outside the exceptional set lies in the chart `D₊(T₀)`.** Let `φ : C ⟶ ℙⁿ_S` have
chart functions `T_ν / T_j ↦ x_ν / x_j`, with every `x_ν ≠ 0`, and let `z` be a `K`-point of `C`
outside `Faltings.BombieriSiegel.exceptionalSet`. Then `φ z` lies in `D₊(T₀)`: every `x_a / x_0`
is regular at `z` (clauses (1) and (4) of the exceptional set), so on a chart `D₊(T_i)` through
`φ z` the function `T₀ / T_i = x_0 / x_i` is a unit at `z`. -/
public theorem mem_chart_zero_of_notMem_exceptionalSet {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsLocallyNoetherian C] [IsIntegral C] (D : C →₀ ℤ)
    {n : ℕ} (x : Fin (n + 1) → C.functionField) (hx : ∀ i, x i ≠ 0)
    (ht : letI := functionFieldAlgebra K f; Transcendental K (x 1 / x 0))
    {S : Scheme.{u}} (φ : C ⟶ projectiveSpaceOver n S)
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
    (z : Spec (.of K) ⟶ C) (hz : z ≫ f = 𝟙 _) (hZ : z ∉ exceptionalSet K f D x ht) :
    φ (z (IsLocalRing.closedPoint K)) ∈ projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0) := by
  set Q := z (IsLocalRing.closedPoint K) with hQ
  have hreg : ∀ a : Fin (n + 1), a ≠ 0 → ∃ g : C.presheaf.stalk Q,
      algebraMap _ C.functionField g = x a / x 0 := by
    intro a ha
    simp only [exceptionalSet, Set.mem_ofPred_eq, not_and, not_or] at hZ
    obtain ⟨h1, -, -, h4⟩ := hZ hz
    have h4' := h4 h1
    push Not at h4'
    obtain ⟨g, hg, -⟩ := h4' a ha
    exact ⟨g, hg⟩
  by_contra hy0
  have hcov : φ Q ∈ ⨆ i, Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.coordChart n S i := by
    rw [Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.iSup_coordChart_eq_top]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hi' : φ Q ∈ projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) := hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hy0 hi'
  obtain ⟨hη, hgerm⟩ := exists_germ_app_ratio_eq_div_of_chart φ x hx hφ i
  have hQi : Q ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)) := hi'
  set t := (projectiveSpaceOver.toIntegralAtUniverse n S).app _
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ i) 1
        (MvPolynomial.X 0) (by simpa using MvPolynomial.isHomogeneous_X _ 0))) with ht
  set r := C.presheaf.germ _ Q hQi (φ.app _ t) with hrdef
  have hr : algebraMap _ C.functionField r = x 0 / x i := by
    rw [← hgerm 0, hrdef]
    exact congr($(C.presheaf.germ_stalkSpecializes (U := φ ⁻¹ᵁ _) hQi
      ((genericPoint_spec C).specializes (Set.mem_univ Q))) (φ.app _ t))
  have hnu : ¬IsUnit r := by
    rw [hrdef, ← Scheme.Hom.germ_stalkMap_apply φ _ Q hi' t]
    intro hu
    exact not_isUnit_germ_ratio S n i (φ Q) hi' hy0
      ((isUnit_map_iff (φ.stalkMap Q).hom _).mp hu)
  obtain ⟨g, hg⟩ := hreg i hi0
  apply hnu
  refine IsUnit.of_mul_eq_one (a := r) g (IsFractionRing.injective (C.presheaf.stalk Q)
    C.functionField ?_)
  rw [map_mul, map_one, hr, hg, div_mul_div_comm, mul_comm (x 0), div_self
    (mul_ne_zero (hx i) (hx 0))]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Chart functions under base change.** Let `π : C' ⟶ C` be dominant, and let
`φ' : C' ⟶ ℙⁿ_{S'}` and `φ : C ⟶ ℙⁿ_S` become `φ' ≫ ι = π ≫ φ ≫ ι` in `ℙⁿ_ℤ`. If `φ` has chart
functions `T_ν / T_j ↦ x_ν / x_j`, then `φ'` has chart functions
`T_ν / T_j ↦ π^* x_ν / π^* x_j`. -/
public theorem germToFunctionField_chart_eq_of_comp_eq {S S' C C' : Scheme.{u}} [IsIntegral C]
    [IsIntegral C'] (π : C' ⟶ C) [IsDominant π] {n : ℕ}
    (φ : C ⟶ projectiveSpaceOver n S) (φ' : C' ⟶ projectiveSpaceOver n S')
    (hφ' : φ' ≫ projectiveSpaceOver.toIntegralAtUniverse n S' =
      π ≫ φ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
    (x : Fin (n + 1) → C.functionField)
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
          x ν / x j) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let U' : Fin (n + 1) → C'.Opens := fun j =>
        φ' ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S' ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U' j)],
        (C'.germToFunctionField (U' j)).hom
          (φ'.app _ ((projectiveSpaceOver.toIntegralAtUniverse n S').app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          functionFieldMap π (x ν) / functionFieldMap π (x j) := by
  intro U' j ν hne
  obtain ⟨⟨y, hy⟩⟩ := hne
  have : Nonempty ((φ ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j)) := by
    have hy' : y ∈ (φ' ≫ projectiveSpaceOver.toIntegralAtUniverse n S') ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j) := hy
    rw [hφ'] at hy'
    exact ⟨⟨π y, hy'⟩⟩
  have : Nonempty (φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j))) := ‹_›
  have : Nonempty (U' j) := ⟨⟨y, hy⟩⟩
  rw [← map_div₀, ← hφ j ν]
  exact germToFunctionField_app_app π (φ ≫ projectiveSpaceOver.toIntegralAtUniverse n S) φ'
    (projectiveSpaceOver.toIntegralAtUniverse n S') hφ' _

/-- The germ at the generic point of a pulled-back section depends on the morphism only. -/
private theorem germ_app_congr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (e : g = g') {V : Y.Opens}
    {x : X} (h : x ∈ g ⁻¹ᵁ V) (t : Γ(Y, V)) :
    X.presheaf.germ _ x h (g.app V t) = X.presheaf.germ _ x (e ▸ h) (g'.app V t) := by
  subst e
  rfl

/-- **Pulling back along a surjection between integral schemes.** If `pr : X ⟶ C` is surjective
and `ι : k(C) → k(X)` is the pull-back on germs, then for an open `U ∋ η_C` the generic point of
`X` lies in `pr⁻¹ U` and the germ there of `pr^* t` is `ι` of the germ of `t`. -/
private theorem exists_germ_app_eq_of_surjective {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (pr : X ⟶ C) (hsurj : Function.Surjective pr) (ι : C.functionField → X.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = X.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    {U : C.Opens} (hU : genericPoint C ∈ U) (t : Γ(C, U)) :
    ∃ h : genericPoint X ∈ pr ⁻¹ᵁ U, X.presheaf.germ _ (genericPoint X) h (pr.app U t) =
      ι (C.presheaf.germ U (genericPoint C) hU t) := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨z, hz⟩ := hsurj (genericPoint C)
  have hz' : z ∈ pr ⁻¹ᵁ U := by
    change pr z ∈ U
    rw [hz]
    exact hU
  have : Nonempty (pr ⁻¹ᵁ U) := ⟨⟨z, hz'⟩⟩
  have hmem : genericPoint X ∈ pr ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (pr ⁻¹ᵁ U).isOpen).mpr ⟨z, trivial, hz'⟩
  exact ⟨hmem, (hι U t).symm⟩

/-- The affine evaluation of a bihomogeneous form is the form evaluated at the affine coordinates
`pr₁ (x_ν / x_j)`, `pr₂ (x_ν / x_j)`. -/
private theorem affineEvaluation_eq_aeval {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι)
    (hxj : x j ≠ 0) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ) :
    affineEvaluation pr₁ pr₂ x j δ F =
      MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν / x j)) (fun ν => pr₂ (x ν / x j))) F.1 := by
  have hc₁ : pr₁ (x j) ≠ 0 := (map_ne_zero pr₁).mpr hxj
  have hc₂ : pr₂ (x j) ≠ 0 := (map_ne_zero pr₂).mpr hxj
  have he : (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)) : ι ⊕ ι → L) =
      Sum.elim (fun ν => pr₁ (x j) * pr₁ (x ν / x j)) (fun ν => pr₂ (x j) * pr₂ (x ν / x j)) := by
    funext ν
    rcases ν with ν | ν
    · simp [map_div₀, mul_div_cancel₀ _ hc₁]
    · simp [map_div₀, mul_div_cancel₀ _ hc₂]
  change MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) F.1 /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2) = _
  rw [he, aeval_sumElim_mul_of_isWeightedHomogeneous
    ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2)]
  field_simp

/-- **Coefficients through the structure morphism.** If the coefficient map `c ∘ e` is the
structure map of `L`, and `ξ, ξ'` are the affine coordinates `pr₁ (x_ν / x_j)`,
`pr₂ (x_ν / x_j)`, then evaluating `F` with coefficients mapped by `e` is its affine
evaluation. -/
private theorem eval₂_map_eq_affineEvaluation {k K L ι A : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [CommRing A] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι)
    (hxj : x j ≠ 0) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (e : k →+* A) (c : A →+* L) (hc : ∀ a, c (e a) = algebraMap k L a) (ξ ξ' : ι → L)
    (hξ : ∀ ν, ξ ν = pr₁ (x ν / x j)) (hξ' : ∀ ν, ξ' ν = pr₂ (x ν / x j)) :
    MvPolynomial.eval₂ c (Sum.elim ξ ξ') (MvPolynomial.map e F.1) =
      affineEvaluation pr₁ pr₂ x j δ F := by
  rw [MvPolynomial.eval₂_map, show c.comp e = algebraMap k L from RingHom.ext hc,
    ← MvPolynomial.aeval_def, funext hξ, funext hξ',
    affineEvaluation_eq_aeval pr₁ pr₂ x j hxj]

/-- Two morphisms out of an integral scheme that agree on `Spec` of its function field pull back
global sections to the same rational function. -/
private theorem germ_appTop_eq_of_fromSpecStalk_comp_eq {Y S : Scheme.{u}} [IsIntegral Y]
    {g g' : Y ⟶ S}
    (h : Y.fromSpecStalk (genericPoint Y) ≫ g = Y.fromSpecStalk (genericPoint Y) ≫ g')
    (t : Γ(S, ⊤)) :
    Y.presheaf.germ ⊤ (genericPoint Y) trivial (g.appTop t) =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial (g'.appTop t) := by
  have : Nonempty (⊤ : (Spec (.of Y.functionField)).Opens) :=
    ⟨⟨IsLocalRing.closedPoint Y.functionField, trivial⟩⟩
  have hinj : Function.Injective (fun z : Y.functionField =>
      resTop (⊤ : (Spec (.of Y.functionField)).Opens)
        ((Scheme.ΓSpecIso (.of Y.functionField)).inv z)) :=
    (map_injective_of_isIntegral _ (homOfLE le_top)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Y.functionField)).inv).1
  apply hinj
  dsimp only
  have hc : ∀ (k₁ k₂ : Spec (.of Y.functionField) ⟶ S) (e : k₁ = k₂),
      k₁.appLE ⊤ ⊤ (fun _ _ => trivial) = k₂.appLE ⊤ ⊤ (fun _ _ => trivial) := by
    intro k₁ k₂ e
    subst e
    rfl
  refine (fromSpecStalk_appLE_apply (U := ⊤) (genericPoint Y) trivial (fun _ _ => trivial)
    (g.appTop t)).symm.trans (Eq.trans ?_ (fromSpecStalk_appLE_apply (U := ⊤) (genericPoint Y)
      trivial (fun _ _ => trivial) (g'.appTop t)))
  have k₁ := Scheme.Hom.comp_appLE (Y.fromSpecStalk (genericPoint Y)) g ⊤ ⊤ (fun _ _ => trivial)
  have k₂ := Scheme.Hom.comp_appLE (Y.fromSpecStalk (genericPoint Y)) g' ⊤ ⊤ (fun _ _ => trivial)
  exact congrArg (fun F => F.hom t) (k₁.symm.trans ((hc _ _ h).trans k₂))

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- At the generic point of `C ×_k C`, the dehomogenisation of a bihomogeneous form on the chart
`D₊(x₀) × D₊(x₀')`, with coefficients through the structure morphism, is its affine
evaluation `F(ξ, ξ')`. -/
public theorem eval₂_germ_eq_affineEvaluation {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP) (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    [Algebra k C.functionField] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (δ : ℕ × ℕ)
    (G : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) δ) :
    ∃ (hx : genericPoint X ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ
        (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X 0)))
      (hx' : genericPoint X ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ
        (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X 0))),
      MvPolynomial.eval₂ ((ψ ≫ pullback.fst _ _ ≫
          (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop ≫
            X.presheaf.germ ⊤ (genericPoint X) trivial).hom
        (Sum.elim
          (fun ν => X.presheaf.germ _ (genericPoint X) hx ((ψ ≫ pullback.fst _ _).app _
            ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X 0)
                (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
                  (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))))
          (fun ν => X.presheaf.germ _ (genericPoint X) hx' ((ψ ≫ pullback.snd _ _).app _
            ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X 0)
                (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
                  (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν)))))))
        (MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom G.1) =
      affineEvaluation ι₁ ι₂ x 0 δ G := by
  have hs₁ : Function.Surjective pr₁ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.1
  have hs₂ : Function.Surjective pr₂ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.2
  obtain ⟨hxC, hξC⟩ := exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  have hx₁ := (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC 0).1
  have hx₂ := (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC 0).1
  refine ⟨hψ₁ ▸ hx₁, hψ₂ ▸ hx₂,
    eval₂_map_eq_affineEvaluation ι₁ ι₂ x 0 (hx0 0) δ G _ _ ?_ _ _ ?_ ?_⟩
  · intro c₀
    rw [hkX]
    have e₁ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
        pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [← Category.assoc, hψ₁, Category.assoc]
    have e₂ : C.fromSpecStalk (genericPoint C) ≫
        (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) =
        C.fromSpecStalk (genericPoint C) ≫ f := by
      rw [hφNP]
    have hC := germ_appTop_eq_of_fromSpecStalk_comp_eq (Y := C)
      (g := φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) (g' := f) e₂
      ((Scheme.ΓSpecIso (.of k)).inv c₀)
    obtain ⟨_, h₁⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      ((φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c₀))
    obtain ⟨_, h₂⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c₀))
    rw [hC] at h₁
    have h₃ : (ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop =
        (pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))).appTop := by
      rw [e₁]
    change X.presheaf.germ ⊤ (genericPoint X) trivial ((ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop _) = _
    rw [h₃]
    exact h₁.trans h₂.symm
  · intro ν
    refine (germ_app_congr hψ₁ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC _).snd.trans
      (congrArg ι₁ (hξC ν))
  · intro ν
    refine (germ_app_congr hψ₂ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC _).snd.trans
      (congrArg ι₂ (hξC ν))

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The representative identity at the generic point.** If `{F_i}` represents `s ≠ 0` in
`𝒪(V)`, then there is `g ∈ k(C ×_k C)` with `F_i(ξ, ξ') = g · (y_i / y_0)ᵈ` for every `i`, where
`F_i(ξ, ξ')` is the affine evaluation at `ξ_ν = pr₁^*(x_ν / x_0)`, `ξ'_ν = pr₂^*(x_ν / x_0)`: the
morphisms `φ_{NP}` and `φ_B` restrict at the generic points to `(x_0 : … : x_n)` and
`(y_0 : … : y_m)`. -/
public theorem exists_affineEvaluation_eq_mul_pow_of_isVojtaRepresentative {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) {n m : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP) (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    [Algebra k C.functionField] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hyspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) = ⊤)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) hyspan
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    (δ₁ δ₂ d : ℕ) (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1)) :
    ∃ g : X.functionField, ∀ j,
      affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F j) = g * (y j / y 0) ^ d := by
  obtain ⟨hyX, hηX⟩ := exists_germ_app_ratio_eq_div_of_ne_zero φB y 0 (hy 0) _ _ hφB
  refine ⟨vojtaSectionRatio ψ φB δ₁ δ₂ d s, fun j => ?_⟩
  obtain ⟨hx, hx', hev⟩ := eval₂_germ_eq_affineEvaluation hX x hx0 φNP hφNP hφNPx ψ hψ₁ hψ₂
    hkX ι₁ ι₂ hι₁ hι₂ (δ₁, δ₂) (F j)
  rw [← hev, IsVojtaRepresentative.eval₂_eq_vojtaSectionRatio_mul_pow ψ φB δ₁ δ₂ d s hs _ hF
    hx hx' hyX j]
  exact congrArg (fun z => vojtaSectionRatio ψ φB δ₁ δ₂ d s * z ^ d) (hηX j)

end Charts

/-! ### Integrality over `K[ξ_a, ξ'_b]` and the norm -/

namespace Integrality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Faltings Faltings.BombieriRoth Faltings.BombieriSiegel Faltings.BombieriVojta

section Norm

open scoped IntermediateField.algebraAdjoinAdjoin

/-- **A norm is divisible by the element, with cofactor in `k[t, u, y]`.** If `t, u` are
algebraically independent over `k`, `L` is finite over `E = k(t, u)` and `y ∈ L` is integral over
`k[t, u]`, then `Norm_{L/E} y = y · h` for some `h` in the `k`-algebra generated by `t, u, y`. -/
public theorem exists_mem_adjoin_norm_eq_mul {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t u : L}
    (hinj : Function.Injective (MvPolynomial.aeval ![t, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    [FiniteDimensional (IntermediateField.adjoin k {t, u}) L]
    {y : L} (hy : IsIntegral (Algebra.adjoin k {t, u}) y) :
    ∃ h ∈ Algebra.adjoin k {t, u, y},
      (Algebra.norm (IntermediateField.adjoin k {t, u}) y : L) = y * h := by
  set A := Algebra.adjoin k ({t, u} : Set L)
  set E := IntermediateField.adjoin k ({t, u} : Set L)
  have hA : A = (MvPolynomial.aeval ![t, u] : MvPolynomial (Fin 2) k →ₐ[k] L).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]
    rfl
  let e : MvPolynomial (Fin 2) k ≃ₐ[k] A :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hA.symm)
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyE : IsIntegral E y := hy.tower_top
  have hmin : minpoly E y = (minpoly A y).map (algebraMap A E) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' E hy
  set P := minpoly A y with hP
  set κ := Module.finrank (IntermediateField.adjoin E {y}) L with hκ
  have hκpos : 0 < κ := Module.finrank_pos
  set pb := IntermediateField.adjoin.powerBasis hyE
  have hnorm : Algebra.norm E y = ((-1) ^ pb.dim * (minpoly E y).coeff 0) ^ κ := by
    rw [Algebra.norm_eq_norm_adjoin E y]
    congr 1
    have hg : IntermediateField.AdjoinSimple.gen E y = pb.gen :=
      (IntermediateField.adjoin.powerBasis_gen hyE).symm
    rw [hg, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← hg, IntermediateField.minpoly_gen]
  have hc : ((minpoly E y).coeff 0 : L) = algebraMap A L (P.coeff 0) := by
    rw [hmin, Polynomial.coeff_map]
    rfl
  have hroot : y * Polynomial.aeval y P.divX + algebraMap A L (P.coeff 0) = 0 := by
    have h0 : Polynomial.aeval y P = 0 := minpoly.aeval A y
    rw [← Polynomial.X_mul_divX_add P, map_add, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C] at h0
    exact h0
  have hAle : ∀ a : A, (a : L) ∈ Algebra.adjoin k {t, u, y} := fun a =>
    Algebra.adjoin_mono (by intro z hz; rcases hz with rfl | rfl <;> simp) a.2
  have hyS : y ∈ Algebra.adjoin k {t, u, y} := Algebra.subset_adjoin (by simp)
  have hQ : Polynomial.aeval y P.divX ∈ Algebra.adjoin k {t, u, y} := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Subalgebra.mul_mem _ (hAle _) (Subalgebra.pow_mem _ hyS _)
  refine ⟨-(((-1) ^ pb.dim) ^ κ * (algebraMap A L (P.coeff 0)) ^ (κ - 1) *
    Polynomial.aeval y P.divX), ?_, ?_⟩
  · refine Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) hQ)
    · exact Subalgebra.pow_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _
        (Subalgebra.one_mem _)) _) _
    · exact Subalgebra.pow_mem _ (hAle _) _
  · rw [hnorm]
    simp only [IntermediateField.coe_pow, IntermediateField.coe_mul, IntermediateField.coe_neg,
      IntermediateField.coe_one, hc]
    have hcy : algebraMap A L (P.coeff 0) = -(y * Polynomial.aeval y P.divX) := by
      linear_combination hroot
    obtain ⟨κ', hκ'⟩ := Nat.exists_eq_add_of_lt hκpos
    rw [hκ', Nat.add_sub_cancel, mul_pow, pow_succ (algebraMap A L (P.coeff 0)), hcy]
    ring

end Norm

end Integrality

/-! ### The local ring at `(z, w)` -/

namespace Local

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Faltings Faltings.BombieriRoth Faltings.BombieriSiegel Faltings.BombieriVojta

private theorem maximalIdeal_eq_span_of_notMem_exceptionalSet {K : Type u} [Field K]
    {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (x : Fin (n + 1) → C.functionField)
    (ht : letI := functionFieldAlgebra K f; Transcendental K (x 1 / x 0))
    {z : Spec (.of K) ⟶ C} (hzZ : z ∉ exceptionalSet K f D x ht) (hz : z ≫ f = 𝟙 _)
    {j : Fin (n + 1)} (hj : j ≠ 0) {t₀ : K} {g : C.presheaf.stalk (z (closedPoint K))}
    (hg : algebraMap _ C.functionField g = x j / x 0)
    (hgt : g - ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (z (closedPoint K)) trivial).hom t₀ ∈ maximalIdeal _) :
    maximalIdeal _ = Ideal.span {g - ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (z (closedPoint K)) trivial).hom t₀} ∧
    ¬ 0 < C.ord (x 0) (z (closedPoint K)) + D (z (closedPoint K)) := by
  set c : K →+* C.presheaf.stalk (z (closedPoint K)) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (z (closedPoint K)) trivial).hom with hc
  have hA : ¬ 0 < C.ord (x 0) (z (closedPoint K)) + D (z (closedPoint K)) :=
    fun hA => hzZ ⟨hz, Or.inl hA⟩
  have hNU : ¬ (∀ g' : C.presheaf.stalk (z (closedPoint K)),
      algebraMap _ C.functionField g' = x j / x 0 →
        ∀ a : K, maximalIdeal (C.presheaf.stalk (z (closedPoint K))) ≠ Ideal.span {g' - c a}) :=
    fun hN => hzZ ⟨hz, Or.inr (Or.inr (Or.inr ⟨hA, j, hj, hN⟩))⟩
  push Not at hNU
  obtain ⟨g', hg', a', hm⟩ := hNU
  have hgg : g' = g := IsFractionRing.injective _ C.functionField (hg'.trans hg.symm)
  subst hgg
  refine ⟨?_, hA⟩
  by_cases ha : a' = t₀
  · rw [← ha]; exact hm
  exfalso
  have hmem : c a' - c t₀ ∈ maximalIdeal (C.presheaf.stalk (z (closedPoint K))) := by
    have h1 : g' - c a' ∈ maximalIdeal (C.presheaf.stalk (z (closedPoint K))) :=
      hm ▸ Ideal.mem_span_singleton_self _
    have := sub_mem hgt h1
    rwa [show g' - c t₀ - (g' - c a') = c a' - c t₀ by ring] at this
  have hu : IsUnit (c a' - c t₀) := by
    rw [← map_sub]
    exact (Ne.isUnit (sub_ne_zero.mpr ha)).map _
  exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

private theorem algebraMap_stalkMap_eq {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] (pr : X ⟶ C)
    (ι : C.functionField → X.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = X.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    (q : X) (g : C.presheaf.stalk (pr q)) :
    algebraMap (X.presheaf.stalk q) X.functionField (pr.stalkMap q g) =
      ι (algebraMap _ C.functionField g) := by
  obtain ⟨V, hV, t, rfl⟩ := C.presheaf.exists_germ_eq g
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (pr ⁻¹ᵁ V) := ⟨⟨q, hV⟩⟩
  rw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
  exact (hι V t).symm

private theorem finiteDimensional_adjoin_of_isIntegral {F L : Type*} [Field F] [Field L]
    [Algebra F L]
    {α β : L} (hβ : IsIntegral (Algebra.adjoin F {α}) β)
    (htop : IntermediateField.adjoin F {α, β} = ⊤) :
    FiniteDimensional (IntermediateField.adjoin F {α}) L := by
  set E := IntermediateField.adjoin F {α}
  have hle : ∀ z ∈ Algebra.adjoin F {α}, z ∈ E := fun z hz =>
    (IntermediateField.algebra_adjoin_le_adjoin F {α}) hz
  have hβE : IsIntegral E β := by
    obtain ⟨p, hpm, hp⟩ := hβ
    let θ : Algebra.adjoin F {α} →+* E :=
      { toFun := fun z => ⟨z, hle z z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    refine ⟨p.map θ, hpm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  have hfin : FiniteDimensional E (IntermediateField.adjoin E {β}) :=
    IntermediateField.adjoin.finiteDimensional hβE
  have htop' : IntermediateField.adjoin E {β} = ⊤ := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top,
      show ({α} : Set L) ∪ {β} = {α, β} from (Set.insert_eq α {β}).symm]
    exact htop
  rw [htop'] at hfin
  exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional

/-- **(G1) gives integrality.** If `x` satisfies (G1) for `D` and `div x_i + D ≥ 0` for every `i`,
then every `x_ν / x_0` is integral over `K[x_a / x_0]` for `a ≠ 0`. -/
private theorem div_mem_integralClosure_of_satisfiesG1 {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsProper f] [IsNormal C] [IsLocallyNoetherian C]
    (D : C →₀ ℤ) {n : ℕ} (x : Fin (n + 1) → C.functionField) (hx0 : ∀ i, x i ≠ 0)
    (hD : ∀ i Q, 0 ≤ C.ord (x i) Q + D Q) (hG1 : SatisfiesG1 K f D x)
    {a : Fin (n + 1)} (ha : a ≠ 0) (ν : Fin (n + 1)) :
    letI := functionFieldAlgebra K f
    x ν / x 0 ∈ integralClosure (Algebra.adjoin K {x a / x 0}) C.functionField :=
  letI := functionFieldAlgebra K f
  Faltings.div_mem_integralClosure_of_not_common_zero f (fun _ => rfl) (hx0 ν) (hx0 a) (hx0 0)
    (hD ν) (hD a) (hD 0) fun c hc h =>
      hG1 a ha c (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint K f
        fun he => FunctionField.coheight_genericPoint_ne_one C (he ▸ hc)) ⟨h.2, h.1⟩

/-- **(G1) and (G2) give finiteness.** `K(C)` is finite over `K(x_a / x_0)` for `a ≠ 0`. -/
private theorem finiteDimensional_adjoin_div_of_satisfiesG1 {K : Type u} [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsProper f] [IsNormal C]
    [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ} (hn : 2 ≤ n) (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (hD : ∀ i Q, 0 ≤ C.ord (x i) Q + D Q) (hG1 : SatisfiesG1 K f D x)
    (hG2 : SatisfiesG2 K f x) {a : Fin (n + 1)} (ha : a ≠ 0) :
    letI := functionFieldAlgebra K f
    FiniteDimensional (IntermediateField.adjoin K {x a / x 0}) C.functionField := by
  let := functionFieldAlgebra K f
  obtain ⟨j, hj0, hja⟩ : ∃ j : Fin (n + 1), j ≠ 0 ∧ a ≠ j := by
    by_cases h1 : (a : ℕ) = 1
    · exact ⟨⟨2, by omega⟩, fun h => by simp [Fin.ext_iff] at h,
        fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h,
        fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
  exact finiteDimensional_adjoin_of_isIntegral ((mem_integralClosure_iff _ _).mp
    (div_mem_integralClosure_of_satisfiesG1 f D x hx0 hD hG1 ha j)) (hG2 a j ha hj0 hja)

/-- The image of `k(t)` under `ι` lies in any intermediate field containing `ι t`. -/
private theorem map_mem_of_mem_adjoin_simple {k F L : Type*} [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] (ι : F →ₐ[k] L) {t : F} {E : IntermediateField k L}
    (ht : ι t ∈ E) {c : F} (hc : c ∈ IntermediateField.adjoin k {t}) : ι c ∈ E := by
  have : (IntermediateField.adjoin k {t}).map ι ≤ E := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
    exact ht
  exact this ⟨c, hc, rfl⟩

/-- **The norm relation for `T_i`.** If `L` is finite over `k(ξ_a, ξ'_b)` and
`F_j(ξ, ξ') = g · η_jᵈ` for every `j`, with `η₀ = 1`, then `T_i · U_iᵈ` is the norm of
`F_i(ξ, ξ')`. -/
public theorem polynomialT_mul_pow_eq_formNorm {k K L ι R : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [CommRing R]
    (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) (ha : a ≠ j) (hb : b ≠ j) (δ : ℕ × ℕ)
    {m d : ℕ}
    [Algebra R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})]
    [FaithfulSMul R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})]
    [FiniteDimensional
      (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) L]
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (g : L) (η : Fin (m + 1) → L) (hη₀ : η 0 = 1)
    (hF : ∀ i, affineEvaluation pr₁ pr₂ x j δ (F i) = g * η i ^ d)
    {U V : Fin (m + 1) → R}
    (hUV : IsReducedNormRepresentation R
      (K := IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) η U V)
    (i : Fin (m + 1)) :
    polynomialT pr₁ pr₂ x j a b δ F η U V hUV d i * algebraMap R _ (U i) ^ d =
      formNorm pr₁ pr₂ x j a b δ (F i) := by
  unfold polynomialT
  by_cases hg : g = 0
  · have hN0 : ∀ j, formNorm pr₁ pr₂ x _ a b δ (F j) = 0 := fun j => by
      unfold formNorm
      rw [hF j, hg, zero_mul]
      exact Algebra.norm_zero
    rw [hN0 0, hN0 i, zero_div, zero_mul]
  · rw [div_mul_eq_mul_div, hUV.formNorm_mul_num_pow_eq pr₁ pr₂ x j a b ha hb δ F g hg η hη₀ hF,
      mul_div_cancel_right₀ _ (pow_ne_zero d <|
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R _)).mpr (hUV.ne_zero i))]

/-- If `r - t` lies in the maximal ideal at `g q`, for `q` the image of a `K`-point `p`, then
`g^♯ r` takes the value `t` at `p`. -/
private theorem stalkClosedPointTo_stalkMap_eq {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ (X ↘ Spec (.of K)) = 𝟙 _) (g : X ⟶ Y)
    (hg : g ≫ (Y ↘ Spec (.of K)) = X ↘ Spec (.of K)) {r : Y.presheaf.stalk (g (p (closedPoint K)))}
    {t : K} (hr : r - const (g (p (closedPoint K))) t ∈ maximalIdeal _) :
    (Scheme.stalkClosedPointTo p).hom (g.stalkMap _ r) = t := by
  have hm : g.stalkMap _ r - const (p (closedPoint K)) t ∈ maximalIdeal _ := by
    rw [const_comp g hg _ t, ← map_sub]
    exact (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp hr (isUnit_of_map_unit _ _ hu)
  have := ev_eq_zero_of_mem p hm
  rwa [map_sub, ev_const p hp, sub_eq_zero] at this

/-- A `K`-point of a curve over `K` is a point of coheight one. -/
private theorem coheight_eq_one_of_comp_eq_id {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] (z : Spec (.of K) ⟶ C) (hz : z ≫ f = 𝟙 _) :
    Order.coheight (z (closedPoint K)) = 1 := by
  apply IsCurve.coheight_eq_one f
  intro h
  have : IsClosedImmersion (z ≫ f) := by rw [hz]; infer_instance
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z f
  have hcl : IsClosed ({z (closedPoint K)} : Set C) := by
    have := z.isClosedEmbedding.isClosed_range
    convert this using 1
    ext y
    constructor
    · rintro rfl
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x (closedPoint K)]
      rfl
  have hdim := ringKrullDim_stalk_eq_one_of_isCurve K f hcl
  rw [h, ringKrullDim_eq_zero_of_isField (Field.toIsField C.functionField)] at hdim
  exact zero_ne_one hdim

/-- The germ at `q` of a section, read in the function field, is its germ at the generic point. -/
private theorem algebraMap_germ_eq_germ {X : Scheme.{u}} [IsIntegral X] {W : X.Opens} {q : X}
    (hq : q ∈ W) (t : Γ(X, W)) (hη : genericPoint X ∈ W) :
    algebraMap (X.presheaf.stalk q) X.functionField (X.presheaf.germ W q hq t) =
      X.presheaf.germ W (genericPoint X) hη t :=
  congr($(X.presheaf.germ_stalkSpecializes hq
    ((genericPoint_spec X).specializes (Set.mem_univ q))) t)

/-- The germ of a polynomial expression in restricted sections. -/
private theorem germ_eval₂_res {X : Scheme.{u}} {ι R : Type*} [CommRing R] {W V₁ V₂ : X.Opens}
    (hW₁ : W ≤ V₁) (hW₂ : W ≤ V₂) {x : X} (hx : x ∈ W) (c : R →+* Γ(X, ⊤))
    (t₁ : ι → Γ(X, V₁)) (t₂ : ι → Γ(X, V₂)) (Fp : MvPolynomial (ι ⊕ ι) R) :
    X.presheaf.germ W x hx (MvPolynomial.eval₂ ((X.presheaf.map (homOfLE le_top).op).hom.comp c)
      (Sum.elim (fun ν => X.presheaf.map (homOfLE hW₁).op (t₁ ν))
        (fun ν => X.presheaf.map (homOfLE hW₂).op (t₂ ν))) Fp) =
    MvPolynomial.eval₂ ((X.presheaf.germ ⊤ x trivial).hom.comp c)
      (Sum.elim (fun ν => X.presheaf.germ V₁ x (hW₁ hx) (t₁ ν))
        (fun ν => X.presheaf.germ V₂ x (hW₂ hx) (t₂ ν))) Fp := by
  refine (MvPolynomial.eval₂_comp_left (X.presheaf.germ W x hx).hom _ _ _).trans ?_
  congr 1
  · ext r
    exact X.presheaf.germ_res_apply _ _ _ _
  · funext ν
    rcases ν with ν | ν
    · exact X.presheaf.germ_res_apply _ _ _ _
    · exact X.presheaf.germ_res_apply _ _ _ _

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The dehomogenised evaluation under base change.** Let `X = C ×_k C` carry the affine
coordinates `ξ_ν = pr₁^*(x_ν / x_0)`, `ξ'_ν = pr₂^*(x_ν / x_0)` of `φ_{NP}`, and let `g : Y ⟶ X`
and `ψ' : Y ⟶ ℙⁿ_K × ℙⁿ_K` satisfy `ψ' ≫ prᵢ = g ≫ prᵢ ≫ φ_{NP}` in `ℙⁿ_ℤ`, compatibly with
`Spec K ⟶ Spec k`. At a point `q` of `Y` in the chart `D₊(T₀) × D₊(T₀')` of `ψ'`, the
dehomogenisation of a bihomogeneous form `G` over `k`, with its coefficients mapped to `K`, is the
image under `g^♯` of an element of `𝒪_{X, g q}` whose image in `k(X)` is the affine evaluation
`G(ξ, ξ')`. -/
private theorem exists_algebraMap_eq_affineEvaluation_and_stalkMap_eq {k K : Type u} [Field k]
    [Field K] [Algebra k K] {C X Y : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C} {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    [Algebra k C.functionField] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (g : Y ⟶ X)
    (ψ' : Y ⟶ pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
      (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
    (hψ'₁ : ψ' ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      g ≫ pr₁ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (hψ'₂ : ψ' ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      g ≫ pr₂ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (hψ'S : ψ' ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) = g ≫ pr₁ ≫ f)
    (δ : ℕ × ℕ)
    (G : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) δ)
    (q : Y)
    (hq₁ : q ∈ (ψ' ≫ pullback.fst _ _) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)))
    (hq₂ : q ∈ (ψ' ≫ pullback.snd _ _) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0))) :
    ∃ G' : X.presheaf.stalk (g q),
      algebraMap _ X.functionField G' = affineEvaluation ι₁ ι₂ x 0 δ G ∧
      g.stalkMap q G' =
        MvPolynomial.eval₂ ((ψ' ≫ pullback.fst _ _ ≫
            (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))).appTop ≫
              Y.presheaf.germ ⊤ q trivial).hom
          (Sum.elim
            (fun ν => Y.presheaf.germ _ q hq₁ ((ψ' ≫ pullback.fst _ _).app _
              ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K))).app _
                (Proj.awayToSection
                  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                  (MvPolynomial.X 0)
                  (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
                    (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))))
            (fun ν => Y.presheaf.germ _ q hq₂ ((ψ' ≫ pullback.snd _ _).app _
              ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K))).app _
                (Proj.awayToSection
                  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                  (MvPolynomial.X 0)
                  (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
                    (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν)))))))
          (MvPolynomial.map ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) G.1) := by
  set B := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X 0) with hB
  set r : Fin (n + 1) → Γ(projectiveSpaceAtUniverse.{u} n, B) := fun ν =>
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
        (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν)) with hr
  set ι := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) with hι
  set V : C.Opens := φNP ⁻¹ᵁ (ι ⁻¹ᵁ B) with hV
  have hg₁ : pr₁ (g q) ∈ V := by
    have h : q ∈ (ψ' ≫ pullback.fst _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K))) ⁻¹ᵁ B := hq₁
    rw [hψ'₁] at h
    exact h
  have hg₂ : pr₂ (g q) ∈ V := by
    have h : q ∈ (ψ' ≫ pullback.snd _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K))) ⁻¹ᵁ B := hq₂
    rw [hψ'₂] at h
    exact h
  have : Nonempty V := ⟨⟨_, hg₁⟩⟩
  have : Nonempty (pr₁ ⁻¹ᵁ V) := ⟨⟨_, hg₁⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ V) := ⟨⟨_, hg₂⟩⟩
  let cR : k →+* X.presheaf.stalk (g q) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pr₁ ≫ f).appTop ≫ X.presheaf.germ ⊤ (g q) trivial).hom
  let ξ : Fin (n + 1) → X.presheaf.stalk (g q) := fun ν =>
    pr₁.stalkMap (g q) (C.presheaf.germ V _ hg₁ (φNP.app _ (ι.app B (r ν))))
  let ξ' : Fin (n + 1) → X.presheaf.stalk (g q) := fun ν =>
    pr₂.stalkMap (g q) (C.presheaf.germ V _ hg₂ (φNP.app _ (ι.app B (r ν))))
  refine ⟨MvPolynomial.eval₂ cR (Sum.elim ξ ξ') G.1, ?_, ?_⟩
  · rw [Charts.affineEvaluation_eq_aeval ι₁ ι₂ x 0 (hx0 0), MvPolynomial.aeval_def,
      MvPolynomial.eval₂_comp_left]
    congr 1
    · ext c
      rw [hkX c]
      exact algebraMap_germ_eq_germ (W := ⊤) (q := g q) trivial _ trivial
    · funext ν
      rcases ν with ν | ν
      · change algebraMap _ _ (pr₁.stalkMap (g q) _) = ι₁ (x ν / x 0)
        rw [algebraMap_stalkMap_eq pr₁ ι₁ hι₁, Scheme.algebraMap_germ_eq_germToFunctionField]
        exact congrArg ι₁ (hφNPx 0 ν)
      · change algebraMap _ _ (pr₂.stalkMap (g q) _) = ι₂ (x ν / x 0)
        rw [algebraMap_stalkMap_eq pr₂ ι₂ hι₂, Scheme.algebraMap_germ_eq_germToFunctionField]
        exact congrArg ι₂ (hφNPx 0 ν)
  · rw [MvPolynomial.eval₂_map]
    refine (MvPolynomial.eval₂_comp_left (g.stalkMap q).hom _ _ _).trans ?_
    congr 1
    · ext c
      have hnat : (Scheme.ΓSpecIso (.of K)).inv (algebraMap k K c) =
          (Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop
            ((Scheme.ΓSpecIso (.of k)).inv c) :=
        congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))) c)
      refine (Scheme.Hom.germ_stalkMap_apply g ⊤ q trivial _).trans ?_
      refine (Charts.germ_app_congr hψ'S.symm (V := ⊤) (x := q) trivial
        ((Scheme.ΓSpecIso (.of k)).inv c)).trans ?_
      exact congrArg (fun t => Y.presheaf.germ ⊤ q trivial ((ψ' ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))).appTop t)) hnat.symm
    · funext ν
      rcases ν with ν | ν
      · refine ((congrArg (g.stalkMap q) (Scheme.Hom.germ_stalkMap_apply pr₁ V (g q) hg₁ _)).trans
          (Scheme.Hom.germ_stalkMap_apply g _ q hg₁ _)).trans ?_
        exact (Charts.germ_app_congr hψ'₁ (V := B) (x := q) hq₁ (r ν)).symm
      · refine ((congrArg (g.stalkMap q) (Scheme.Hom.germ_stalkMap_apply pr₂ V (g q) hg₂ _)).trans
          (Scheme.Hom.germ_stalkMap_apply g _ q hg₂ _)).trans ?_
        exact (Charts.germ_app_congr hψ'₂ (V := B) (x := q) hq₂ (r ν)).symm

end Local

end Faltings.BombieriRoth.VanishingTransfer

namespace Faltings.BombieriRoth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing BombieriSiegel
  BombieriVojta

attribute [local instance] MvPolynomial.gradedAlgebra in
open BombieriVojta VanishingTransfer in
/-- **Lifts to `𝒪_{C × C, ι q}`.** For the map `ι : C_K × C_K ⟶ C × C` over `π : C_K ⟶ C` and a
`K`-point `q` of `C_K × C_K` with both projections in the chart `D₊(T₀)` of `φ_{NP} ∘ π`, the
affine coordinates `ξ_{j₁} = pr₁^*(x_{j₁} / x_0)`, `ξ'_{j₂}`, the constants and `F_{i₀}(ξ, ξ')`
lift to the local ring of `C × C` at `ι q`, with images under `ι^♯` the germs of `π^* ξ_{j₁}`,
`π^* ξ'_{j₂}`, the constants of `C_K × C_K` and a multiple of `σ` for `σ e = s_K`. -/
private theorem exists_stalk_lifts {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    [IsIntegral X.C] {n : ℕ} (x : Fin (n + 1) → X.C.functionField) (hx0 : ∀ i, x i ≠ 0)
    [IsIntegral (pullback X.f X.f)]
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
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
          ((pullback.snd X.f X.f).app U t))
    {m : ℕ} (δ₁ δ₂ d : ℕ)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (K : Type u) [Field K] [Algebra k K]
    (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
    (hπ : π ≫ X.f = (CK ↘ Spec (.of K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)))
    [IsIntegral CK] [IsDominant π]
    (ιS : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) ⟶ pullback X.f X.f)
    (hι₁S : ιS ≫ pullback.fst X.f X.f = pullback.fst _ _ ≫ π)
    (hι₂S : ιS ≫ pullback.snd X.f X.f = pullback.snd _ _ ≫ π)
    (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
      pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
    (hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
      pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
    (hψK₁ : ψK ≫ pullback.fst _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (hψK₂ : ψK ≫ pullback.snd _ _ ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
      projectiveSpaceOver m (Spec (.of K)))
    (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
    (hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
      ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
    (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
    (j₁ j₂ : Fin (n + 1))
    {gz : CK.presheaf.stalk ((pK ≫ pullback.fst _ _) (closedPoint K))}
    (hgzL : algebraMap _ CK.functionField gz = functionFieldMap π (x j₁) / functionFieldMap π (x 0))
    {gw : CK.presheaf.stalk ((pK ≫ pullback.snd _ _) (closedPoint K))}
    (hgwL : algebraMap _ CK.functionField gw = functionFieldMap π (x j₂) / functionFieldMap π (x 0))
    (hD₁ : (π ≫ φNP) ((pK ≫ pullback.fst _ _) (closedPoint K)) ∈
      projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0))
    (hD₂ : (π ≫ φNP) ((pK ≫ pullback.snd _ _) (closedPoint K)) ∈
      projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0))
    (U : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).Opens) (hqU : pK (closedPoint K) ∈ U)
    (e : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, U))
    (σ : Γ((pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))), U))
    (hσ : σ • e = (vojtaLineBundle ψK φK δ₁ δ₂ d).presheaf.map (homOfLE le_top).op sK)
    (i₀ : Fin (m + 1)) :
    ∃ (cR : k →+* (pullback X.f X.f).presheaf.stalk (ιS (pK (closedPoint K))))
      (ζ₁ ζ₂ G' : (pullback X.f X.f).presheaf.stalk (ιS (pK (closedPoint K))))
      (w : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.stalk (pK (closedPoint K))),
      algebraMap _ (pullback X.f X.f).functionField ζ₁ = ι₁ (x j₁) / ι₁ (x 0) ∧
      algebraMap _ (pullback X.f X.f).functionField ζ₂ = ι₂ (x j₂) / ι₂ (x 0) ∧
      (∀ c, algebraMap _ (pullback X.f X.f).functionField (cR c) =
        algebraMap k (pullback X.f X.f).functionField c) ∧
      algebraMap _ (pullback X.f X.f).functionField G' =
        affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F i₀) ∧
      ιS.stalkMap (pK (closedPoint K)) ζ₁ =
        (pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap (pK (closedPoint K)) gz ∧
      ιS.stalkMap (pK (closedPoint K)) ζ₂ =
        (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap (pK (closedPoint K)) gw ∧
      (∀ c, ιS.stalkMap (pK (closedPoint K)) (cR c) =
        const (pK (closedPoint K)) (algebraMap k K c)) ∧
      ιS.stalkMap (pK (closedPoint K)) G' =
        (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ U _ hqU σ * w := by
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  have hφπ := Charts.germToFunctionField_chart_eq_of_comp_eq π φNP (π ≫ φNP)
    (Category.assoc _ _ _) x hφNPx
  set q : ↥(pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) := pK (closedPoint K) with hqdef
  set B := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X 0) with hB
  set ιk := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) with hιk
  set ιK := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) with hιK
  have hq₁ : q ∈ (ψK ≫ pullback.fst _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B) := by
    have h : q ∈ (ιS ≫ pullback.fst X.f X.f ≫ φNP ≫ ιk) ⁻¹ᵁ B := by
      rw [← Category.assoc ιS, hι₁S]
      exact hD₁
    rw [← hψK₁] at h
    exact h
  have hq₂ : q ∈ (ψK ≫ pullback.snd _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B) := by
    have h : q ∈ (ιS ≫ pullback.snd X.f X.f ≫ φNP ≫ ιk) ⁻¹ᵁ B := by
      rw [← Category.assoc ιS, hι₂S]
      exact hD₂
    rw [← hψK₂] at h
    exact h
  have hψS : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) = ιS ≫ pullback.fst X.f X.f ≫ X.f := by
    calc _ = (ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) := by simp only [Category.assoc]
      _ = pullback.fst _ _ ≫ (CK ↘ Spec (.of K)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k K)) := by rw [hψKπ, Category.assoc]
      _ = _ := by rw [← hπ, ← Category.assoc, ← hι₁S, Category.assoc]
  let r : Fin (n + 1) → Γ(projectiveSpaceAtUniverse.{u} n, B) := fun ν =>
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
        (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))
  have hV₁ : pullback.fst X.f X.f (ιS q) ∈ φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B) := by
    have h : q ∈ (ιS ≫ pullback.fst X.f X.f ≫ φNP ≫ ιk) ⁻¹ᵁ B := by rw [← hψK₁]; exact hq₁
    exact h
  have hV₂ : pullback.snd X.f X.f (ιS q) ∈ φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B) := by
    have h : q ∈ (ιS ≫ pullback.snd X.f X.f ≫ φNP ≫ ιk) ⁻¹ᵁ B := by rw [← hψK₂]; exact hq₂
    exact h
  have : Nonempty (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B)) := ⟨⟨_, hV₁⟩⟩
  have : Nonempty ((π ≫ φNP) ⁻¹ᵁ (ιk ⁻¹ᵁ B)) := ⟨⟨_, hD₁⟩⟩
  have : Nonempty (π ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) := ⟨⟨_, hD₁⟩⟩
  let ζ₁ : (pullback X.f X.f).presheaf.stalk (ιS q) := (pullback.fst X.f X.f).stalkMap (ιS q)
    (X.C.presheaf.germ _ _ hV₁ (φNP.app _ (ιk.app B (r j₁))))
  let ζ₂ : (pullback X.f X.f).presheaf.stalk (ιS q) := (pullback.snd X.f X.f).stalkMap (ιS q)
    (X.C.presheaf.germ _ _ hV₂ (φNP.app _ (ιk.app B (r j₂))))
  have hζ₁L : algebraMap _ (pullback X.f X.f).functionField ζ₁ = ι₁ (x j₁) / ι₁ (x 0) := by
    rw [Local.algebraMap_stalkMap_eq _ ι₁ hι₁, Scheme.algebraMap_germ_eq_germToFunctionField,
      ← map_div₀]
    exact congrArg ι₁ (hφNPx 0 j₁)
  have hζ₂L : algebraMap _ (pullback X.f X.f).functionField ζ₂ = ι₂ (x j₂) / ι₂ (x 0) := by
    rw [Local.algebraMap_stalkMap_eq _ ι₂ hι₂, Scheme.algebraMap_germ_eq_germToFunctionField,
      ← map_div₀]
    exact congrArg ι₂ (hφNPx 0 j₂)
  have hgz' : CK.presheaf.germ (π ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) _ hD₁
      (π.app _ (φNP.app _ (ιk.app B (r j₁)))) = gz := by
    apply IsFractionRing.injective (CK.presheaf.stalk _) CK.functionField
    have e2 : CK.germToFunctionField ((π ≫ φNP) ⁻¹ᵁ (ιk ⁻¹ᵁ B))
        ((π ≫ φNP).app _ (ιk.app B (r j₁))) =
          functionFieldMap π (x j₁) / functionFieldMap π (x 0) :=
        hφπ 0 j₁
    rw [hgzL, ← e2]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := CK)
      (U := (π ≫ φNP) ⁻¹ᵁ (ιk ⁻¹ᵁ B)) hD₁
      ((π ≫ φNP).app _ (ιk.app B (r j₁)))
  have hgw' : CK.presheaf.germ (π ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) _ hD₂
      (π.app _ (φNP.app _ (ιk.app B (r j₂)))) = gw := by
    apply IsFractionRing.injective (CK.presheaf.stalk _) CK.functionField
    have e2 : CK.germToFunctionField ((π ≫ φNP) ⁻¹ᵁ (ιk ⁻¹ᵁ B))
        ((π ≫ φNP).app _ (ιk.app B (r j₂))) =
          functionFieldMap π (x j₂) / functionFieldMap π (x 0) :=
        hφπ 0 j₂
    rw [hgwL, ← e2]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := CK)
      (U := (π ≫ φNP) ⁻¹ᵁ (ιk ⁻¹ᵁ B)) hD₂
      ((π ≫ φNP).app _ (ιk.app B (r j₂)))
  have hζ₁Θ : ιS.stalkMap q ζ₁ =
      (pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz := by
    rw [← hgz']
    have e1 := Scheme.Hom.germ_stalkMap_apply (pullback.fst X.f X.f) (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B)) (ιS q)
      hV₁ (φNP.app _ (ιk.app B (r j₁)))
    have e2 := Scheme.Hom.germ_stalkMap_apply ιS ((pullback.fst X.f X.f) ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) q
      hV₁ ((pullback.fst X.f X.f).app _ (φNP.app _ (ιk.app B (r j₁))))
    have e3 := Charts.germ_app_congr hι₁S (V := φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B)) (x := q) hV₁
      (φNP.app _ (ιk.app B (r j₁)))
    have e4 := Scheme.Hom.germ_stalkMap_apply
      (pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) (π ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) q hD₁
      (π.app _ (φNP.app _ (ιk.app B (r j₁))))
    exact (congrArg (ιS.stalkMap q) e1).trans (e2.trans (e3.trans e4.symm))
  have hζ₂Θ : ιS.stalkMap q ζ₂ =
      (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw := by
    rw [← hgw']
    have e1 := Scheme.Hom.germ_stalkMap_apply (pullback.snd X.f X.f) (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B)) (ιS q)
      hV₂ (φNP.app _ (ιk.app B (r j₂)))
    have e2 := Scheme.Hom.germ_stalkMap_apply ιS ((pullback.snd X.f X.f) ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) q
      hV₂ ((pullback.snd X.f X.f).app _ (φNP.app _ (ιk.app B (r j₂))))
    have e3 := Charts.germ_app_congr hι₂S (V := φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B)) (x := q) hV₂
      (φNP.app _ (ιk.app B (r j₂)))
    have e4 := Scheme.Hom.germ_stalkMap_apply
      (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) (π ⁻¹ᵁ (φNP ⁻¹ᵁ (ιk ⁻¹ᵁ B))) q hD₂
      (π.app _ (φNP.app _ (ιk.app B (r j₂))))
    exact (congrArg (ιS.stalkMap q) e1).trans (e2.trans (e3.trans e4.symm))
  let cR : k →+* (pullback X.f X.f).presheaf.stalk (ιS q) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.fst X.f X.f ≫ X.f).appTop ≫
      (pullback X.f X.f).presheaf.germ ⊤ (ιS q) trivial).hom
  have hcRL : ∀ c, algebraMap _ (pullback X.f X.f).functionField (cR c) =
      algebraMap k (pullback X.f X.f).functionField c := fun c => by
    rw [hkX c]
    exact Local.algebraMap_germ_eq_germ (W := ⊤) trivial _ trivial
  have hS : (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ≫ (CK ↘ Spec (.of K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) = ιS ≫ pullback.fst X.f X.f ≫ X.f := by
    rw [← pullback.condition, Category.assoc, ← hπ, ← Category.assoc, ← hι₁S, Category.assoc]
  have hcRΘ : ∀ c, ιS.stalkMap q (cR c) = const q (algebraMap k K c) := by
    intro c
    have hnat : (Scheme.ΓSpecIso (.of K)).inv (algebraMap k K c) =
        (Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop ((Scheme.ΓSpecIso (.of k)).inv c) :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))) c)
    refine (Scheme.Hom.germ_stalkMap_apply ιS ⊤ q trivial _).trans ?_
    refine (Charts.germ_app_congr hS.symm (V := ⊤) (x := q) trivial
      ((Scheme.ΓSpecIso (.of k)).inv c)).trans ?_
    exact congrArg (fun t => (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ ⊤ q
      trivial ((pullback.snd _ _ ≫ (CK ↘ Spec (.of K))).appTop t)) hnat.symm
  obtain ⟨G', hG'L, hG'Θ⟩ := Local.exists_algebraMap_eq_affineEvaluation_and_stalkMap_eq x hx0 φNP
    hφNPx hkX ι₁ ι₂ hι₁ hι₂ ιS ψK hψK₁ hψK₂ hψS (δ₁, δ₂) (F i₀) q hq₁ hq₂
  set W : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).Opens :=
    U ⊓ ((ψK ≫ pullback.fst _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B) ⊓ (ψK ≫ pullback.snd _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B)) with hWdef
  have hqW : q ∈ W := ⟨hqU, hq₁, hq₂⟩
  obtain ⟨v, hv⟩ := Sections.exists_eval₂_eq_mul_of_smul_eq ψK φK δ₁ δ₂ d sK _ hsK U W
    inf_le_left (fun _ h => h.2.1) (fun _ h => h.2.2) e σ hσ i₀
  have hfσ : ιS.stalkMap q G' =
      (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ U q hqU σ *
        (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ W q hqW v := by
    rw [hG'Θ]
    have h := (Local.germ_eval₂_res (W := W) (V₁ := (ψK ≫ pullback.fst _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B))
      (V₂ := (ψK ≫ pullback.snd _ _) ⁻¹ᵁ (ιK ⁻¹ᵁ B)) (fun _ h => h.2.1) (fun _ h => h.2.2) hqW
      _ _ _ _).symm.trans
      (congrArg (fun t =>
        (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ W q hqW t)
        hv)
    rw [map_mul, (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ_res_apply] at h
    exact h
  exact ⟨cR, ζ₁, ζ₂, G', _, hζ₁L, hζ₂L, hcRL, hG'L, hζ₁Θ, hζ₂Θ, hcRΘ, hfσ⟩

open BombieriSiegel VanishingTransfer in
/-- **The norm relation in a local ring of `C × C`.** If `ζ₁, ζ₂, G'` in the local ring at a point
of `C × C` lift `ξ_a, ξ'_b` and `F_{i₀}(ξ, ξ')`, and `c` lifts the constants, then
`T(ζ₁, ζ₂) · U_{i₀}(ζ₁, ζ₂)ᵈ` is a multiple of `G'` there: the norm of `F_{i₀}(ξ, ξ')` down to
`k(ξ_a, ξ'_b)` is `F_{i₀}(ξ, ξ') h` with `h ∈ k[ξ_a, ξ'_b, F_{i₀}(ξ, ξ')]`. -/
private theorem exists_eval₂_mul_pow_eq_mul {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) [IsIntegral X.C] [IsLocallyNoetherian X.C]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    [IsIntegral (pullback X.f X.f)]
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
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
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
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
          ((pullback.snd X.f X.f).app U t))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1))
    (a b : Fin n)
    [Algebra (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})]
    (hR : ∀ r : MvPolynomial (Fin 2) k,
      (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) r :
          (pullback X.f X.f).functionField) =
        MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] r)
    (Un Vd : Fin (m + 1) → MvPolynomial (Fin 2) k)
    (hUV : IsReducedNormRepresentation
      (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (MvPolynomial (Fin 2) k) (fun i => y i / y 0) Un Vd)
    (i₀ : Fin (m + 1)) (T : MvPolynomial (Fin 2) k)
    (hT : algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) T =
      polynomialT ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) F (fun i => y i / y 0) Un Vd hUV d i₀)
    {pt : ↥(pullback X.f X.f : Scheme.{u})} (cR : k →+* (pullback X.f X.f).presheaf.stalk pt)
    (ζ₁ ζ₂ G' : (pullback X.f X.f).presheaf.stalk pt)
    (hcR : ∀ c, algebraMap _ (pullback X.f X.f).functionField (cR c) =
      algebraMap k (pullback X.f X.f).functionField c)
    (hζ₁ : algebraMap _ (pullback X.f X.f).functionField ζ₁ = ι₁ (x a.succ) / ι₁ (x 0))
    (hζ₂ : algebraMap _ (pullback X.f X.f).functionField ζ₂ = ι₂ (x b.succ) / ι₂ (x 0))
    (hG' : algebraMap _ (pullback X.f X.f).functionField G' =
      affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F i₀)) :
    ∃ h' : (pullback X.f X.f).presheaf.stalk pt,
      MvPolynomial.eval₂ cR ![ζ₁, ζ₂] T * MvPolynomial.eval₂ cR ![ζ₁, ζ₂] (Un i₀) ^ d =
        G' * h' := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hkC' : ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f := hkC
  subst hkC'
  let : Algebra k X.C.functionField := functionFieldAlgebra k X.f
  have hPcl : ∀ Q ∈ (X.P.mapDomain Subtype.val).support, IsClosed ({Q} : Set X.C) := by
    intro Q hQ
    classical
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hQ)
    exact c.2
  have hli := hx.linearIndependent
  have hspan := hx.span_eq
  have hG1 := hx.satisfiesG1
  have hG2 := hx.satisfiesG2
  have hx0 : ∀ i, x i ≠ 0 := hli.ne_zero
  have hmemx : ∀ i (Q : X.C), 0 ≤ X.C.ord (x i) Q + ((N : ℤ) • X.P.mapDomain Subtype.val) Q :=
    ord_add_nonneg_of_span_eq X.f (isClosed_of_mem_support_smul hPcl _) hli hspan
  have hγeval : ∀ Q : MvPolynomial (Fin 2) k,
      algebraMap _ (pullback X.f X.f).functionField (MvPolynomial.eval₂ cR ![ζ₁, ζ₂] Q) =
        (algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) Q :
            (pullback X.f X.f).functionField) := by
    intro Q
    rw [hR Q, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext c
      exact hcR c
    · funext i
      fin_cases i
      · exact hζ₁
      · exact hζ₂
  have : IsNormal X.C := isNormal_of_smooth_over_field X.f
  have hfin : ∀ {a' : Fin (n + 1)}, a' ≠ 0 →
      FiniteDimensional (IntermediateField.adjoin k {x a' / x 0}) X.C.functionField :=
    Local.finiteDimensional_adjoin_div_of_satisfiesG1 X.f _ (by omega) x hx0 hmemx hG1 hG2
  have htr : ∀ {a' : Fin (n + 1)}, a' ≠ 0 → Transcendental k (x a' / x 0) := fun ha' =>
    have := hfin ha'
    transcendental_of_finiteDimensional
      (by rw [AlgebraicGeometry.trdeg_functionField_eq_one k X.f]; exact one_ne_zero)
  have hinj : Function.Injective (MvPolynomial.aeval
      ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] :
        MvPolynomial (Fin 2) k →ₐ[k] (pullback X.f X.f).functionField) := by
    rw [← map_div₀, ← map_div₀]
    exact injective_aeval_of_transcendental X.f (IsPullback.of_hasPullback X.f X.f) (fun _ => rfl)
      ι₁ ι₂ hι₁ hι₂ (htr (Fin.succ_ne_zero a)) (htr (Fin.succ_ne_zero b))
  have hξE : ι₁ (x a.succ / x 0) ∈
      IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} := by
    rw [map_div₀]; exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hξ'E : ι₂ (x b.succ / x 0) ∈
      IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} := by
    rw [map_div₀]; exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have : FiniteDimensional
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (pullback X.f X.f).functionField := by
    have := hfin (Fin.succ_ne_zero a)
    have := hfin (Fin.succ_ne_zero b)
    exact finite_of_isPullback X.f (IsPullback.of_hasPullback X.f X.f) ι₁ ι₂ hι₁ hι₂ _ _ _
      (fun _ => Local.map_mem_of_mem_adjoin_simple ι₁ hξE)
      (fun _ => Local.map_mem_of_mem_adjoin_simple ι₂ hξ'E)
  have hI : ∀ (ι : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
      (S : Set (pullback X.f X.f).functionField) {a' : Fin (n + 1)}, a' ≠ 0 →
      ι (x a' / x 0) ∈ S → ∀ ν, IsIntegral (Algebra.adjoin k S) (ι (x ν / x 0)) :=
    fun ι S _ ha' hs ν => Faltings.isIntegral_map_of_mem_integralClosure
      (A := Algebra.adjoin k S) ι _ ⟨⟨_, Algebra.subset_adjoin hs⟩, rfl⟩
      (fun c => ⟨algebraMap k _ c, rfl⟩)
      (Local.div_mem_integralClosure_of_satisfiesG1 X.f _ x hx0 hmemx hG1 ha' ν)
  have hzint : IsIntegral (Algebra.adjoin k
      {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F i₀)) := by
    rw [Charts.affineEvaluation_eq_aeval ι₁ ι₂ x 0 (hx0 0)]
    refine Faltings.BombieriRoth.isIntegral_aeval ?_ _
    rintro (ν | ν)
    · exact hI ι₁ _ (Fin.succ_ne_zero a) (by rw [map_div₀]; exact Set.mem_insert _ _) ν
    · exact hI ι₂ _ (Fin.succ_ne_zero b) (by rw [map_div₀]; exact Set.mem_insert_of_mem _ rfl) ν
  obtain ⟨h, hhS, hh⟩ := Integrality.exists_mem_adjoin_norm_eq_mul hinj hzint
  have hrange : ∀ z ∈ Algebra.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0),
      affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F i₀)}, ∃ o : (pullback X.f X.f).presheaf.stalk pt,
        algebraMap _ (pullback X.f X.f).functionField o = z := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl | rfl
      · exact ⟨ζ₁, hζ₁⟩
      · exact ⟨ζ₂, hζ₂⟩
      · exact ⟨G', hG'⟩
    | algebraMap c => exact ⟨_, hcR c⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨o₁, rfl⟩ := h₁
      obtain ⟨o₂, rfl⟩ := h₂
      exact ⟨o₁ + o₂, map_add _ _ _⟩
    | mul z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨o₁, rfl⟩ := h₁
      obtain ⟨o₂, rfl⟩ := h₂
      exact ⟨o₁ * o₂, map_mul _ _ _⟩
  obtain ⟨h', hh'⟩ := hrange h hhS
  have hFS : FaithfulSMul (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun Q₁ Q₂ hQ => hinj ?_
    have := congrArg Subtype.val hQ
    rwa [hR, hR] at this
  obtain ⟨g₀, hg₀⟩ := Charts.exists_affineEvaluation_eq_mul_pow_of_isVojtaRepresentative
    (IsPullback.of_hasPullback X.f X.f) x hx0 φNP hφNP hφNPx ψ hψ₁ hψ₂ hkX ι₁ ι₂ hι₁ hι₂ y hy _ φB
    hφBy δ₁ δ₂ d s hs F hF
  have hrelE : algebraMap (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) T *
      algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
        (Un i₀) ^ d = formNorm ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) (F i₀) := by
    rw [hT]
    exact Local.polynomialT_mul_pow_eq_formNorm ι₁ ι₂ x 0 a.succ b.succ (Fin.succ_ne_zero a)
      (Fin.succ_ne_zero b) (δ₁, δ₂) F g₀ _ (div_self (hy 0)) hg₀ hUV i₀
  have hEL := congrArg (fun z : IntermediateField.adjoin k
    {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} => (z : (pullback X.f X.f).functionField))
    hrelE
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow] at hEL
  have hrelL : algebraMap _ (pullback X.f X.f).functionField
      (MvPolynomial.eval₂ cR ![ζ₁, ζ₂] T * (MvPolynomial.eval₂ cR ![ζ₁, ζ₂] (Un i₀)) ^ d) =
      algebraMap _ (pullback X.f X.f).functionField (G' * h') := by
    rw [map_mul, map_pow, hγeval, hγeval, hEL, map_mul, hG', hh']
    exact hh
  exact ⟨h', IsFractionRing.injective _ _ hrelL⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical VanishingTransfer in
/-- **`T` vanishes at least as much as `s`** (Bombieri). In the standing setting of Sections 9–10
over a number field `k` (a curve `X = (C, P)` of genus `g ≥ 2` with a divisor of degree one, a
generic basis `x` of `L(N P)` giving `φNP`, `ψ = φNP × φNP`, a basis `y` of `H⁰(C × C, 𝒪(B))`
generic for the projections giving `φB`), let `s ≠ 0` be a section of
`Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d` with representative `F` over `k`. Let `K ⊇ k` be a number
field, `C_K` the base change, `s_K` the section of the base-changed bundle represented by `F`, and
`p_K = (z, w)` a `K`-point of `C_K × C_K` with `z, w` outside
`Faltings.BombieriSiegel.exceptionalSet`. Let `1 ≤ a, b ≤ n`, `p₀ = (ξ_a(z), ξ'_b(w)) = (t₀, t₀')`,
`(U, V)` reduced representations of the norms of `η_i = y_i / y_0` in `k[ξ_a, ξ'_b]`, `i₀ ≠ 0`
with `U_{i₀}(p₀) ≠ 0`, and `T ∈ k[X₀, X₁]` with image `polynomialT … i₀`. If `e` is a local
generator of `𝒪(V_K)` at `p_K` and `σ = s_K / e` has image in `J_{A,B}`
(`Faltings.completedStalkBiorderIdeal`), then the divided derivatives `∂_{(i₁, i₂)} T`
(`Faltings.MvPolynomial.hasseDeriv`) vanish at `p₀` for all `i₁ ≤ A`, `i₂ ≤ B`. -/
@[faltings "lem_bvr_vanishing_transfer"]
public theorem eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f)
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
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
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
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
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0)
    -- the Vojta data: `d₁, d₂, d` positive integers with `δᵢ = (dᵢ + sB d) / N` integers
    (d₁ d₂ d δ₁ δ₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 0 < d)
    (hδ₁N : N * δ₁ = d₁ + sB * d) (hδ₂N : N * δ₂ = d₂ + sB * d)
    -- the section `s ≠ 0` of `𝒪(V)` and its representative with coefficients in `k`
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1)) :
    -- a number field `K ⊇ k` and the base change `C_K` (the `K`-block of the main inequality)
    ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K]
      (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
      (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
    let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
    let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
      pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        hπ.w.symm hπ.w.symm
    ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
        Transcendental K (xK 1 / xK 0))
      (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
      -- the base changes `ψ_K, φ_K` of `ψ, φ_B`, and the section `s_K` represented by `F`
      (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
      (_hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hψK₁ : ψK ≫ pullback.fst _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (_hψK₂ : ψK ≫ pullback.snd _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        projectiveSpaceOver m (Spec (.of K)))
      (_hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
        ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
      (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
      (_hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
      -- the `K`-point `p_K = (z, w)` of `C_K × C_K`
      (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
      [pK.IsOver (Spec (.of K))],
      -- `z, w ∉ Z`
      pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
      pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
    -- the indices `1 ≤ a, b ≤ n` and the point `p₀ = (ξ_a(z), ξ'_b(w)) = (t₀, t₀')` of `K²`
    ∀ (a b : Fin n) (t₀ t₀' : K),
      (∃ g : CK.presheaf.stalk ((pK ≫ pullback.fst _ _) (closedPoint K)),
        algebraMap _ CK.functionField g = xK a.succ / xK 0 ∧
        g - ((Scheme.ΓSpecIso (.of K)).inv ≫ (CK ↘ Spec (.of K)).appTop ≫
          CK.presheaf.germ ⊤ _ trivial).hom t₀ ∈ maximalIdeal _) →
      (∃ g : CK.presheaf.stalk ((pK ≫ pullback.snd _ _) (closedPoint K)),
        algebraMap _ CK.functionField g = xK b.succ / xK 0 ∧
        g - ((Scheme.ΓSpecIso (.of K)).inv ≫ (CK ↘ Spec (.of K)).appTop ≫
          CK.presheaf.germ ⊤ _ trivial).hom t₀' ∈ maximalIdeal _) →
    -- `R = k[ξ_a, ξ'_b] → k(ξ_a, ξ'_b)` and reduced representations of the norms of `η_i`
    ∀ [Algebra (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})],
      (∀ r : MvPolynomial (Fin 2) k,
        (algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) r :
            (pullback X.f X.f).functionField) =
          MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] r) →
    ∀ (Un Vd : Fin (m + 1) → MvPolynomial (Fin 2) k)
      (hUV : IsReducedNormRepresentation
        (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
        (MvPolynomial (Fin 2) k) (fun i => y i / y 0) Un Vd)
    -- the index `i₀ ≠ 0` with `U_{i₀}(p₀) ≠ 0`
      (i₀ : Fin (m + 1)), i₀ ≠ 0 → MvPolynomial.aeval ![t₀, t₀'] (Un i₀) ≠ 0 →
    -- a local generator `e` of `𝒪(V_K)` at `p_K` and `σ = s_K / e ∈ J_{A,B}`
    ∀ (U : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).Opens)
      (hqU : pK (closedPoint K) ∈ U) (e : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, U)),
      (∀ (W : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).Opens) (hWU : W ≤ U),
        Function.Bijective fun c :
            Γ((pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) : Scheme), W) =>
          c • (vojtaLineBundle ψK φK δ₁ δ₂ d).presheaf.map (homOfLE hWU).op e) →
    ∀ σ : Γ((pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) : Scheme), U),
      σ • e = (vojtaLineBundle ψK φK δ₁ δ₂ d).presheaf.map (homOfLE le_top).op sK →
    ∀ {A B' : ℕ}, algebraMap _ _
        ((pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ U _ hqU σ) ∈
      completedStalkBiorderIdeal (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) (pK (closedPoint K))
        A B' →
    -- `T ∈ R` with image `T_{i₀}`
    ∀ T : MvPolynomial (Fin 2) k,
      algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) T =
        polynomialT ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) F (fun i => y i / y 0) Un Vd hUV d i₀ →
    ∀ i₁ ≤ A, ∀ i₂ ≤ B',
      MvPolynomial.aeval ![t₀, t₀']
        (Faltings.MvPolynomial.hasseDeriv (Finsupp.single 0 i₁ + Finsupp.single 1 i₂) T) = 0 := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hkC' : ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f := hkC
  subst hkC'
  let : Algebra k X.C.functionField := functionFieldAlgebra k X.f
  intro K _ _ _ CK _ π hπ _ _ _ _ xK ιS hξ₁₀ DK _hDK ψK hψKπ hψK₁ hψK₂ φK _hφKπ _hφK sK hsK pK _
    hzZ hwZ a b t₀ t₀' ht₀ ht₀' _ hR Un Vd hUV i₀ hi₀ hU U hqU e he σ hσ A B' hJ T hT
  have hp : pK ≫ (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ↘ Spec (.of K)) = 𝟙 _ :=
    comp_over_eq_id pK
  have hwf : (pK ≫ pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) ≫
      (CK ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc]
    exact hp
  have hzf : (pK ≫ pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) ≫
      (CK ↘ Spec (.of K)) = 𝟙 _ := by
    rwa [Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨gz, hgzL, hgz⟩ := ht₀
  obtain ⟨gw, hgwL, hgw⟩ := ht₀'
  obtain ⟨hmz, -⟩ := Local.maximalIdeal_eq_span_of_notMem_exceptionalSet (CK ↘ Spec (.of K)) DK
    xK hξ₁₀ hzZ hzf (Fin.succ_ne_zero a) hgzL hgz
  obtain ⟨hmw, -⟩ := Local.maximalIdeal_eq_span_of_notMem_exceptionalSet (CK ↘ Spec (.of K)) DK
    xK hξ₁₀ hwZ hwf (Fin.succ_ne_zero b) hgwL hgw
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  have hx0 : ∀ i, x i ≠ 0 := hx.linearIndependent.ne_zero
  have hxK0 : ∀ i, xK i ≠ 0 := fun i => (map_ne_zero _).mpr (hx0 i)
  have hφπ := Charts.germToFunctionField_chart_eq_of_comp_eq π φNP (π ≫ φNP)
    (Category.assoc _ _ _) x hφNPx
  have hD₁ := Charts.mem_chart_zero_of_notMem_exceptionalSet (CK ↘ Spec (.of K)) DK xK hxK0 hξ₁₀
    (π ≫ φNP) hφπ _ hzf hzZ
  have hD₂ := Charts.mem_chart_zero_of_notMem_exceptionalSet (CK ↘ Spec (.of K)) DK xK hxK0 hξ₁₀
    (π ≫ φNP) hφπ _ hwf hwZ
  have hι₁S : ιS ≫ pullback.fst X.f X.f = pullback.fst _ _ ≫ π := by simp [ιS]
  have hι₂S : ιS ≫ pullback.snd X.f X.f = pullback.snd _ _ ≫ π := by simp [ιS]
  set q : ↥(pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) := pK (closedPoint K) with hqdef
  obtain ⟨cR, ζ₁, ζ₂, G', w, hζ₁L, hζ₂L, hcRL, hG'L, hζ₁Θ, hζ₂Θ, hcRΘ, hG'Θ⟩ :=
    exists_stalk_lifts X x hx0 φNP hφNPx hkX ι₁ ι₂ hι₁ hι₂ δ₁ δ₂ d F K CK π hπ.w ιS hι₁S hι₂S ψK
      hψKπ hψK₁ hψK₂ φK sK hsK pK a.succ b.succ hgzL hgwL hD₁ hD₂ U hqU e σ hσ i₀
  obtain ⟨h', hh'⟩ := exists_eval₂_mul_pow_eq_mul X hg N hN hn x hx φNP hφNP hφNPx ψ hψ₁ hψ₂ hkC
    hkX ι₁ ι₂ hι₁ hι₂ y hy φB hφBy δ₁ δ₂ d s hs F hF a b hR Un Vd hUV i₀ T hT cR ζ₁ ζ₂ G' hcRL
    hζ₁L hζ₂L hG'L
  have hΘeval : ∀ Q : MvPolynomial (Fin 2) k,
      ιS.stalkMap q (MvPolynomial.eval₂ cR ![ζ₁, ζ₂] Q) =
        MvPolynomial.eval₂ ((const (K := K) q).comp (algebraMap k K))
          ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
            (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw] Q := by
    intro Q
    refine (MvPolynomial.eval₂_comp_left (ιS.stalkMap q).hom _ _ Q).trans ?_
    congr 1
    · ext c
      exact hcRΘ c
    · funext i
      fin_cases i
      · exact hζ₁Θ
      · exact hζ₂Θ
  have hĝz0 : (Scheme.stalkClosedPointTo pK).hom
      ((pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz) = t₀ :=
    Local.stalkClosedPointTo_stalkMap_eq pK hp _ pullback.condition hgz
  have hĝw0 : (Scheme.stalkClosedPointTo pK).hom
      ((pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw) = t₀' :=
    Local.stalkClosedPointTo_stalkMap_eq pK hp _ rfl hgw
  have hevQ : ∀ Q : MvPolynomial (Fin 2) k, (Scheme.stalkClosedPointTo pK).hom
      (MvPolynomial.eval₂ ((const (K := K) q).comp (algebraMap k K))
        ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
          (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw] Q) =
      MvPolynomial.aeval ![t₀, t₀'] Q := by
    intro Q
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def]
    congr 1
    · ext c
      exact ev_const pK hp _
    · funext i
      fin_cases i
      · exact hĝz0
      · exact hĝw0
  have hυ : IsUnit (MvPolynomial.eval₂ ((const (K := K) q).comp (algebraMap k K))
      ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
        (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw] (Un i₀)) := by
    by_contra hnu
    exact hU ((hevQ (Un i₀)).symm.trans (ev_eq_zero_of_mem pK ((mem_maximalIdeal _).mpr hnu)))
  have hkey := congrArg (ιS.stalkMap q) hh'
  rw [map_mul, map_pow, map_mul, hΘeval, hΘeval, hG'Θ] at hkey
  have hυd := hυ.pow d
  have hτ : MvPolynomial.eval₂ (const (K := K) q)
      ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
        (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw]
        (MvPolynomial.map (algebraMap k K) T) =
      (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ U q hqU σ *
        (w * ιS.stalkMap q h' * ↑hυd.unit⁻¹) := by
    rw [MvPolynomial.eval₂_map, ← mul_assoc, ← mul_assoc, ← hkey, mul_assoc,
      IsUnit.mul_val_inv, mul_one]
  have hJτ : algebraMap _ (AdicCompletion (maximalIdeal _) _)
      (MvPolynomial.eval₂ (const (K := K) q)
        ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
          (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw]
        (MvPolynomial.map (algebraMap k K) T)) ∈
      completedStalkBiorderIdeal (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) q A B' := by
    rw [hτ, map_mul]
    exact Ideal.mul_mem_right _ _ hJ
  have hvec : ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q
        (@id (CK.presheaf.stalk ((pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) q)) gz -
          const (K := K) (Y := CK) ((pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) q)
            t₀) + const (K := K) q t₀,
      (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q
        (@id (CK.presheaf.stalk ((pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) q)) gw -
          const (K := K) (Y := CK) ((pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) q)
            t₀') + const (K := K) q t₀'] =
      ![(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gz,
        (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap q gw] := by
    rw [map_sub, map_sub, const_comp (K := K) (pullback.fst _ _) pullback.condition q t₀,
      const_comp (K := K) (pullback.snd _ _) rfl q t₀', sub_add_cancel, sub_add_cancel]
    rfl
  rw [← hvec] at hJτ
  have hTay := Taylor.eval_hasseDeriv_eq_zero_of_mem pK hp hzf hwf hmz hmw t₀ t₀'
    (MvPolynomial.map (algebraMap k K) T) A B' hJτ
  intro i₁ hi₁ i₂ hi₂
  rw [MvPolynomial.aeval_def, ← MvPolynomial.eval_map, ← Taylor.hasseDeriv_map]
  exact hTay i₁ hi₁ i₂ hi₂

end Faltings.BombieriRoth
