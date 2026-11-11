module
public import Mordell.BombieriVojta.Representative.ChartBase
public import Mordell.BombieriVojta.Representative.Vanishing
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule
import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
import StacksFrontier.AlgebraicGeometry.GradedSectionsModule.IntGraded

/-!
# Forms on the standard charts of projective space

Let `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`, with homogeneous coordinates `(x, x')` and `y`.
On the chart `D₊(T_k)` of the integral model `ℙʳ_ℤ` the section of `𝒪(a)` given by a monomial
`T^β` of degree `a` is `∏_ν (T_ν / T_k)^{β_ν}` times the section `T_k^a`. Pulling back along `ψ`
and `φ`, on the chart `ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂}))` a form `F` of bidegree `(δ₁, δ₂)`
restricts to `F(ξ, ξ') · x_{j₁}^{δ₁} x'_{j₂}^{δ₂}`, where `ξ_ν = x_ν / x_{j₁}` and
`ξ'_ν = x'_ν / x'_{j₂}`, and on `φ⁻¹ D₊(T_k)` the section `y_i^d` restricts to `η_i^d · y_k^d`,
where `η_i = y_i / y_k`. On an integral `X` these reduce identities between restrictions of forms
to identities of rational functions.

## Main results

* `Faltings.resT_vojtaFormRestriction`, `Faltings.resT_vojtaCoordinatePow`: on the charts
  `Faltings.chartPair ψ j₁ j₂` and `Faltings.chartOne φ k`, a form restricts to
  `F(ξ, ξ') · x_{j₁}^{δ₁} x'_{j₂}^{δ₂}` (`Faltings.baseSec`) and `y_i^d` to `η_i^d · y_k^d`
  (`Faltings.etaSec`).
* `Faltings.resT_prodSection_eq_smul`, `Faltings.resT_pullbackGlobalSections_eq_smul`: products
  and pullbacks of global sections respect such factorisations on an open.
* `Faltings.eq_zero_of_res_eq_zero`: on an integral scheme, a global section of an invertible
  module vanishing on a nonempty open vanishes.
* `Faltings.germ_div_vojtaFormRestriction`, `Faltings.vojtaFormRestriction_eq_zero_iff`: if `ψ`
  lifts two dominant maps `X ⟶ C` through `φ_{NP} : C ⟶ ℙⁿ_S` and `x_{i₀}` does not vanish
  identically on `C`, then the germ of `F|_X / (x_{i₀}^{δ₁} x'_{i₀}^{δ₂})` at the generic point of
  `X` is `F(ξ, ξ')`, and `F|_X = 0` if and only if `F(ξ, ξ') = 0`.

## Implementation notes

* `ℙʳ_ℤ` is `AlgebraicGeometry.Proj` of `ℤ[T_0, …, T_r]` graded by degree (`Faltings.projGrading`),
  its twisting sheaves are `Faltings.projTwist`, its charts `Faltings.projChart` and the functions
  `T_ν / T_k` are `Faltings.projRatio`. The charts of `ℙⁿ_S` and `ℙᵐ_S` are pulled back along
  `AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse`.
* Restrictions of sections are `Stacks.ProjectiveFromSections.resT` (from `⊤`) and
  `Stacks.ProjectiveFromSections.resO` (of functions); products of global sections are
  `Stacks.ProductFamilyTwist.prodSection`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings

universe u

open TopologicalSpace Opposite MonoidalCategory
open Stacks.ProjectiveFromSections (resT resO resM)

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

/-- If `t = r • t₀` on `T`, then `f^* t = f^* r • f^* t₀` on `f⁻¹ T`. -/
public theorem resT_pullbackGlobalSections_eq_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {T : Y.Opens} {t t₀ : Γ(M, ⊤)} {r : Γ(Y, T)}
    (h : resT T t = r • resT T t₀) :
    resT (f ⁻¹ᵁ T) (pullbackGlobalSections f M t) =
      f.app T r • resT (f ⁻¹ᵁ T) (pullbackGlobalSections f M t₀) := by
  rw [resT_pullbackGlobalSections, resT_pullbackGlobalSections, h, pullbackUnitApp_smul]

/-- If `t = r • t₀` on `T`, then also on every smaller open. -/
public theorem resT_eq_smul_of_le {X : Scheme.{u}} {M : X.Modules} {T T' : X.Opens}
    (hT : T' ≤ T) {t t₀ : Γ(M, ⊤)} {r : Γ(X, T)} (h : resT T t = r • resT T t₀) :
    resT T' t = resO hT r • resT T' t₀ := by
  rw [← Stacks.ProjectiveFromSections.resM_resT hT, h, Stacks.ProjectiveFromSections.resM_smul,
    Stacks.ProjectiveFromSections.resM_resT]

/-- The product of two global sections, restricted to an open, is the image of the restriction of
the second factor under multiplication by the first. -/
public theorem resT_prodSection_eq_mulLeft {X : Scheme.{u}} {F G : X.Modules} (s : Γ(F, ⊤))
    (t : Γ(G, ⊤)) (T : X.Opens) :
    resT T (Stacks.ProductFamilyTwist.prodSection s t) =
      (Stacks.TensorSectionNonvanishing.mulLeft (Stacks.ProductFamilyTwist.unitOfSection F s)
        G).app T (resT T t) := by
  have h : Stacks.ProductFamilyTwist.prodSection s t =
      (Stacks.TensorSectionNonvanishing.mulLeft (Stacks.ProductFamilyTwist.unitOfSection F s)
        G).app ⊤ t := by
    rw [Stacks.ProductFamilyTwist.prodSection, Stacks.TensorSectionNonvanishing.unitMul_eq_mulLeft,
      Stacks.SectionProduct.globalSection_comp,
      Stacks.ProductFamilyTwist.globalSection_unitOfSection]
  rw [h]
  exact (PresheafOfModules.naturality_apply (Stacks.TensorSectionNonvanishing.mulLeft
    (Stacks.ProductFamilyTwist.unitOfSection F s) G).val (homOfLE (le_top : T ≤ ⊤)).op t).symm

/-- Products of global sections are bilinear on an open. -/
public theorem resT_prodSection_eq_smul {X : Scheme.{u}} {F G : X.Modules} {T : X.Opens}
    {s s₀ : Γ(F, ⊤)} {t t₀ : Γ(G, ⊤)} {r r' : Γ(X, T)} (hs : resT T s = r • resT T s₀)
    (ht : resT T t = r' • resT T t₀) :
    resT T (Stacks.ProductFamilyTwist.prodSection s t) =
      (r * r') • resT T (Stacks.ProductFamilyTwist.prodSection s₀ t₀) := by
  rw [Stacks.ProductFamilyRatio.resT_prodSection, hs, Stacks.ProductFamilyRatio.mulSec_smul,
    ← Stacks.ProductFamilyRatio.resT_prodSection, resT_prodSection_eq_mulLeft, ht,
    Scheme.Modules.Hom.app_smul, ← resT_prodSection_eq_mulLeft, mul_smul]

/-- In a localization, `∏ (f_ν / s)^{β_ν} · s^{∑ β} = ∏ f_ν^{β_ν}`. -/
private theorem prod_mk_pow_mul {A : Type*} [CommRing A] {S : Submonoid A} {ι : Type*}
    (t : Finset ι) (f : ι → A) (s : A) (hs : s ∈ S) (β : ι → ℕ) :
    (∏ ν ∈ t, (Localization.mk (f ν) ⟨s, hs⟩ : Localization S) ^ β ν) *
      Localization.mk (s ^ ∑ ν ∈ t, β ν) 1 = Localization.mk (∏ ν ∈ t, f ν ^ β ν) 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Localization.mk_one]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, pow_add,
      ← one_mul (1 : S), ← Localization.mk_mul, ← Localization.mk_mul (f a ^ β a), ← ih]
    have : (Localization.mk (f a) ⟨s, hs⟩ : Localization S) ^ β a * Localization.mk (s ^ β a) 1 =
        Localization.mk (f a ^ β a) 1 := by
      rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      exact ⟨1, by simp; ring⟩
    rw [← this]
    ring

/-- On an integral scheme, a global section of an invertible module that vanishes on a nonempty
open vanishes. -/
public theorem eq_zero_of_res_eq_zero {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {W : X.Opens} (hW : (W : Set X).Nonempty)
    (t : Γ(M, ⊤)) (h : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t = 0) : t = 0 := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  have hz : ∀ x : X, ∃ z, x ∈ V z := fun x => Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  choose z hxz using hz
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} X)
    (fun x : (⊤ : X.Opens) => V (z x.1)) ⊤ (fun x => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨⟨x, trivial⟩, hxz x⟩) _ _ fun x => ?_
  obtain ⟨x, -⟩ := x
  let τ := (htriv (z x)).some
  obtain ⟨y, hyV, hyW⟩ : ((V (z x) : Set X) ∩ W).Nonempty :=
    nonempty_preirreducible_inter (V (z x)).isOpen W.isOpen ⟨x, hxz x⟩ hW
  let c := Stacks.NonvanishingOpen.triv τ (𝟙 _)
    (M.presheaf.map (homOfLE (le_top : V (z x) ≤ ⊤)).op t)
  have hc : X.presheaf.map (homOfLE (inf_le_left : V (z x) ⊓ W ≤ V (z x))).op c = 0 := by
    rw [← Stacks.NonvanishingOpen.triv_res τ (𝟙 _) _ (homOfLE inf_le_left)]
    have : M.presheaf.map (homOfLE (inf_le_left : V (z x) ⊓ W ≤ V (z x))).op
        (M.presheaf.map (homOfLE (le_top : V (z x) ≤ ⊤)).op t) =
        M.presheaf.map (homOfLE (inf_le_right : V (z x) ⊓ W ≤ W)).op
          (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl
    rw [this, h, map_zero]
    exact map_zero _
  have hc0 : c = 0 := by
    apply germ_injective_of_isIntegral X y hyV
    rw [map_zero, ← X.presheaf.germ_res (homOfLE (inf_le_left : V (z x) ⊓ W ≤ V (z x))) y
      ⟨hyV, hyW⟩, CommRingCat.comp_apply, hc, map_zero]
  have : M.presheaf.map (homOfLE (le_top : V (z x) ≤ ⊤)).op t = 0 := by
    refine (τ.θ (V (z x)) (𝟙 _)).injective ?_
    exact hc0.trans (map_zero _).symm
  rw [map_zero]
  exact this

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem val_mul_apply (r : ℕ) {U : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens}
    (c d : Γ(AlgebraicGeometry.Proj (projGrading.{u} r), U)) (x : U) :
    ((c * d).1 x).val = (c.1 x).val * (d.1 x).val := by
  rw [← HomogeneousLocalization.val_mul]
  exact congrArg HomogeneousLocalization.val (Proj.mul_apply (projGrading.{u} r) (V := op U) c d x)

private theorem val_one_apply (r : ℕ) {U : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens}
    (x : U) :
    ((1 : Γ(AlgebraicGeometry.Proj (projGrading.{u} r), U)).1 x).val = 1 :=
  (congrArg HomogeneousLocalization.val (Proj.one_apply (projGrading.{u} r) (V := op U) x)).trans
    HomogeneousLocalization.val_one

private theorem val_pow_apply (r : ℕ) {U : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens}
    (c : Γ(AlgebraicGeometry.Proj (projGrading.{u} r), U)) (x : U) (n : ℕ) :
    ((c ^ n).1 x).val = (c.1 x).val ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact val_one_apply r x
  | succ n ih => rw [pow_succ, val_mul_apply, ih, pow_succ]

private theorem val_prod_apply (r : ℕ) {U : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens}
    {ι : Type*} (s : Finset ι) (c : ι → Γ(AlgebraicGeometry.Proj (projGrading.{u} r), U)) (x : U) :
    ((∏ i ∈ s, c i).1 x).val = ∏ i ∈ s, ((c i).1 x).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact val_one_apply r x
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, val_mul_apply, ih]

/-- On the chart `D₊(T_k)`, the section of `𝒪(a)` given by a monomial `T^β` of degree `a` is
`∏_ν (T_ν / T_k) ^ β_ν` times the section given by `T_k ^ a`. -/
public theorem resT_degreeSection_monomial (r a : ℕ) (k : Fin (r + 1)) (β : Fin (r + 1) →₀ ℕ)
    (hβ : β.degree = a) :
    resT (L := projTwist.{u} r (a : ℤ)) (projChart r k)
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) a
        ⟨MvPolynomial.monomial β 1, MvPolynomial.isHomogeneous_monomial _ hβ⟩) =
      (∏ ν, projRatio r k ν ^ β ν) • resT (L := projTwist.{u} r (a : ℤ)) (projChart r k)
        (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) a
          ⟨MvPolynomial.X k ^ a, MvPolynomial.isHomogeneous_X_pow k a⟩) := by
  apply Subtype.ext
  funext x
  obtain ⟨x, hx⟩ := x
  have e := val_prod_apply r Finset.univ (fun ν => projRatio r k ν ^ β ν) ⟨x, hx⟩
  simp only [val_pow_apply, val_projRatio] at e
  change (Localization.mk (MvPolynomial.monomial β 1) 1 : Localization _) =
    ((∏ ν, projRatio r k ν ^ β ν).1 ⟨x, hx⟩).val * Localization.mk (MvPolynomial.X k ^ a) 1
  refine Eq.trans ?_ (congrArg (· * Localization.mk (MvPolynomial.X k ^ a) 1) e).symm
  have hsum : ∑ ν, β ν = a := by rw [← hβ, Finsupp.degree_eq_sum]
  rw [← hsum]
  refine Eq.trans ?_
    (prod_mk_pow_mul Finset.univ MvPolynomial.X _ _ β).symm
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]

/-- The restriction to `X` of the monomial `x^{α₁} x'^{α₂}` of bidegree `(δ₁, δ₂)`, the summand of
`Faltings.vojtaFormRestriction`. -/
@[expose] public noncomputable def monoSec {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) :
    Γ((Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback
            (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (projTwist.{u} n (δ₁ : ℤ))) ⊗
        (Scheme.Modules.pullback
            (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (projTwist.{u} n (δ₂ : ℤ)))), ⊤) :=
  if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
    pullbackGlobalSections ψ _ (Stacks.ProductFamilyTwist.prodSection
      (pullbackGlobalSections
        (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
        (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S) _
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} n) δ₁
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ h.1⟩)))
      (pullbackGlobalSections
        (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
        (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S) _
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} n) δ₂
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ h.2⟩))))
  else 0

/-- `Faltings.vojtaFormRestriction` is the sum of the restricted monomials `Faltings.monoSec`. -/
public theorem vojtaFormRestriction_eq_sum {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (F : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) :
    vojtaFormRestriction ψ δ₁ δ₂ F = ∑ α ∈ F.support,
      (ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop (F.coeff α) •
        monoSec ψ δ₁ δ₂ α :=
  rfl

/-- The section `x_{j₁}^{δ₁} x'_{j₂}^{δ₂}` restricted to `X`. -/
@[expose] public noncomputable def baseSec {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (j₁ j₂ : Fin (n + 1)) :
    Γ((Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback
            (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (projTwist.{u} n (δ₁ : ℤ))) ⊗
        (Scheme.Modules.pullback
            (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (projTwist.{u} n (δ₂ : ℤ)))), ⊤) :=
  pullbackGlobalSections ψ _ (Stacks.ProductFamilyTwist.prodSection
    (pullbackGlobalSections
      (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
      (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S) _
        (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} n) δ₁
          ⟨MvPolynomial.X j₁ ^ δ₁, MvPolynomial.isHomogeneous_X_pow j₁ δ₁⟩)))
    (pullbackGlobalSections
      (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
      (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S) _
        (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} n) δ₂
          ⟨MvPolynomial.X j₂ ^ δ₂, MvPolynomial.isHomogeneous_X_pow j₂ δ₂⟩))))

/-- The open `ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂}))` of `X`. -/
public noncomputable abbrev chartPair {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (j₁ j₂ : Fin (n + 1)) : X.Opens :=
  ψ ⁻¹ᵁ (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart n j₁) ⊓
    pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart n j₂))

/-- The affine coordinate `ξ_ν = x_ν / x_{j₁}` on `chartPair ψ j₁ j₂`. -/
public noncomputable abbrev xiFst {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (j₁ j₂ ν : Fin (n + 1)) : Γ(X, chartPair ψ j₁ j₂) :=
  ψ.app _ (resO inf_le_left
    ((pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).app _
    ((projectiveSpaceOver.toIntegralAtUniverse n S).app _ (projRatio n j₁ ν))))

/-- The affine coordinate `ξ'_ν = x'_ν / x'_{j₂}` on `chartPair ψ j₁ j₂`. -/
public noncomputable abbrev xiSnd {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (j₁ j₂ ν : Fin (n + 1)) : Γ(X, chartPair ψ j₁ j₂) :=
  ψ.app _ (resO inf_le_right
    ((pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).app _
    ((projectiveSpaceOver.toIntegralAtUniverse n S).app _ (projRatio n j₂ ν))))

/-- On `ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂}))`, the monomial `x^{α₁} x'^{α₂}` of bidegree
`(δ₁, δ₂)` is `ξ^{α₁} ξ'^{α₂} · x_{j₁}^{δ₁} x'_{j₂}^{δ₂}`. -/
public theorem resT_monoSec {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (j₁ j₂ : Fin (n + 1)) (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ)
    (h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂) :
    resT (chartPair ψ j₁ j₂) (monoSec ψ δ₁ δ₂ α) =
      ((∏ ν, xiFst ψ j₁ j₂ ν ^ α (Sum.inl ν)) * ∏ ν, xiSnd ψ j₁ j₂ ν ^ α (Sum.inr ν)) •
        resT (chartPair ψ j₁ j₂) (baseSec ψ δ₁ δ₂ j₁ j₂) := by
  rw [monoSec, dite_eq_left h, baseSec]
  have h₁ := resT_degreeSection_monomial n δ₁ j₁ _ h.1
  have h₂ := resT_degreeSection_monomial n δ₂ j₂ _ h.2
  let A₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
    (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart n j₁)
  let A₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
    (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart n j₂)
  have k₁ := resT_eq_smul_of_le (inf_le_left : A₁ ⊓ A₂ ≤ A₁)
    (resT_pullbackGlobalSections_eq_smul
      (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
      (resT_pullbackGlobalSections_eq_smul (projectiveSpaceOver.toIntegralAtUniverse n S) h₁))
  have k₂ := resT_eq_smul_of_le (inf_le_right : A₁ ⊓ A₂ ≤ A₂)
    (resT_pullbackGlobalSections_eq_smul
      (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
      (resT_pullbackGlobalSections_eq_smul (projectiveSpaceOver.toIntegralAtUniverse n S) h₂))
  rw [resT_pullbackGlobalSections_eq_smul ψ (resT_prodSection_eq_smul k₁ k₂)]
  congr 1
  simp only [Finsupp.comapDomain_apply]
  have e : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (c : Fin (n + 1) → A) (β : Fin (n + 1) → ℕ),
      φ.hom (∏ ν, c ν ^ β ν) = ∏ ν, φ.hom (c ν) ^ β ν := fun φ c β => by
    simp only [map_prod, map_pow]
  rw [map_mul]
  refine congrArg₂ (fun a b : Γ(X, chartPair ψ j₁ j₂) => a * b) ?_ ?_
  · exact e ((projectiveSpaceOver.toIntegralAtUniverse n S).app _ ≫
      (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).app _ ≫
      (Limits.pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
        (homOfLE inf_le_left).op ≫ ψ.app _) _ _
  · exact e ((projectiveSpaceOver.toIntegralAtUniverse n S).app _ ≫
      (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).app _ ≫
      (Limits.pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
        (homOfLE inf_le_right).op ≫ ψ.app _) _ _

/-- Restriction of global sections commutes with finite sums. -/
public theorem resT_sum {X : Scheme.{u}} {M : X.Modules} (T : X.Opens) {ι : Type*}
    (s : Finset ι) (t : ι → Γ(M, ⊤)) : resT T (∑ i ∈ s, t i) = ∑ i ∈ s, resT T (t i) :=
  map_sum _ _ _

/-- The ring map through which the coefficients of a form act on sections over `W`. -/
public noncomputable abbrev coeffMap {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (W : X.Opens) : Γ(S, ⊤) →+* Γ(X, W) :=
  ((ψ ≫ pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ≫
    (projectiveSpaceOver n S ↘ S)).appTop ≫ X.presheaf.map (homOfLE le_top).op).hom

/-- **A form restricted to a chart.** On `ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂}))`, the
restriction of a form `P` of bidegree `(δ₁, δ₂)` is `P(ξ, ξ') · x_{j₁}^{δ₁} x'_{j₂}^{δ₂}`. -/
public theorem resT_vojtaFormRestriction {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (j₁ j₂ : Fin (n + 1)) (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) :
    resT (chartPair ψ j₁ j₂) (vojtaFormRestriction ψ δ₁ δ₂ P) =
      P.eval₂ (coeffMap ψ (chartPair ψ j₁ j₂)) (Sum.elim (xiFst ψ j₁ j₂) (xiSnd ψ j₁ j₂)) •
        resT (chartPair ψ j₁ j₂) (baseSec ψ δ₁ δ₂ j₁ j₂) := by
  rw [vojtaFormRestriction_eq_sum, MvPolynomial.eval₂_eq', Finset.sum_smul]
  refine (resT_sum _ _ _).trans (Finset.sum_congr rfl fun α hα => ?_)
  have hdeg := degree_comapDomain_of_weight (hP (MvPolynomial.mem_support_iff.mp hα))
  refine (Stacks.ProjectiveFromSections.resM_smul _ _ _).trans ?_
  refine (congrArg (_ • ·) (resT_monoSec ψ δ₁ δ₂ j₁ j₂ α hdeg)).trans ?_
  refine (smul_smul _ _ _).trans ?_
  rw [Fintype.prod_sum_type]
  rfl

/-- The open `φ⁻¹ D₊(T_k)` of `X`. -/
public noncomputable abbrev chartOne {S X : Scheme.{u}} {m : ℕ}
    (φ : X ⟶ projectiveSpaceOver m S) (k : Fin (m + 1)) : X.Opens :=
  φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ projChart m k)

/-- The function `η_i = y_i / y_k` on `φ⁻¹ D₊(T_k)`. -/
public noncomputable abbrev etaSec {S X : Scheme.{u}} {m : ℕ}
    (φ : X ⟶ projectiveSpaceOver m S) (k i : Fin (m + 1)) : Γ(X, chartOne φ k) :=
  φ.app _ ((projectiveSpaceOver.toIntegralAtUniverse m S).app _ (projRatio m k i))

/-- On `φ⁻¹ D₊(T_k)`, `y_i^d = η_i^d · y_k^d`. -/
public theorem resT_vojtaCoordinatePow {S X : Scheme.{u}} {m : ℕ}
    (φ : X ⟶ projectiveSpaceOver m S) (d : ℕ) (k i : Fin (m + 1)) :
    resT (chartOne φ k) (vojtaCoordinatePow φ d i) =
      etaSec φ k i ^ d • resT (chartOne φ k) (vojtaCoordinatePow φ d k) := by
  have hβ : (Finsupp.single i d).degree = d := by simp
  have h := resT_degreeSection_monomial m d k (Finsupp.single i d) hβ
  have hX : (⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩ : projGrading.{u} m d) =
      ⟨MvPolynomial.monomial (Finsupp.single i d) 1,
        MvPolynomial.isHomogeneous_monomial _ hβ⟩ :=
    Subtype.ext (MvPolynomial.X_pow_eq_monomial)
  have hprod : ∏ ν, projRatio m k ν ^ (Finsupp.single i d) ν = projRatio m k i ^ d := by
    rw [Fintype.prod_eq_single i fun ν hν => by rw [Finsupp.single_eq_of_ne hν, pow_zero],
      Finsupp.single_eq_same]
  rw [hprod, ← hX] at h
  have h' := resT_pullbackGlobalSections_eq_smul φ
    (resT_pullbackGlobalSections_eq_smul (projectiveSpaceOver.toIntegralAtUniverse m S) h)
  refine h'.trans ?_
  congr 1
  exact (map_pow ((projectiveSpaceOver.toIntegralAtUniverse m S).app _ ≫ φ.app _).hom _ d)

/-- A point of `D₊(T_j)` lies in the nonvanishing locus of the section `T_j ^ a` of `𝒪(a)`. -/
private theorem mem_nonvanishingLocus_degreeSection_X_pow (r a : ℕ) (j : Fin (r + 1))
    (p : AlgebraicGeometry.Proj (projGrading.{u} r)) (hp : p ∈ projChart r j) :
    p ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (projGrading.{u} r))
      (projTwist.{u} r a)
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) a
        ⟨MvPolynomial.X j ^ a, MvPolynomial.isHomogeneous_X_pow j a⟩) := by
  obtain ⟨a, rfl⟩ : ∃ b, a = b * 1 := ⟨a, (mul_one a).symm⟩
  rw [Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
    _ (Stacks.AlgebraicGeometry.ProjTwistTensorPow.adjoin_degreeOne_integralModel r) one_pos a]
  rw [SetLike.mem_coe, Proj.mem_basicOpen]
  rw [Proj.mem_basicOpen] at hp
  exact fun hmem => hp (Ideal.IsPrime.mem_of_pow_mem (ProjectiveSpectrum.isPrime _) _ hmem)

/-- The unit section of `𝒪(0)` vanishes nowhere. -/
public theorem mem_nonvanishingLocus_degreeSection_one (r : ℕ)
    (p : AlgebraicGeometry.Proj (projGrading.{u} r)) :
    p ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (projGrading.{u} r))
      (projTwist.{u} r ((0 : ℕ) : ℤ))
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) 0
        ⟨1, MvPolynomial.isHomogeneous_one _ _⟩) := by
  have h :=
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
    _ (Stacks.AlgebraicGeometry.ProjTwistTensorPow.adjoin_degreeOne_integralModel r) one_pos 0
    ⟨1, MvPolynomial.isHomogeneous_one _ _⟩
  refine (congrArg (p ∈ ·) h).mpr ?_
  rw [SetLike.mem_coe, Proj.mem_basicOpen]
  exact p.asHomogeneousIdeal.toIdeal.ne_top_iff_one.mp p.isPrime.ne_top

open Stacks.TensorSectionNonvanishing in
/-- The product of two sections of invertible modules does not vanish where neither factor
does. -/
public theorem mem_nonvanishingLocus_prodSection {X : Scheme.{u}} {F G : X.Modules}
    [Stacks.Ample.IsInvertibleModule X F] [Stacks.Ample.IsInvertibleModule X G]
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) {x : X} (hs : x ∈ Stacks.Ample.nonvanishingLocus F s)
    (ht : x ∈ Stacks.Ample.nonvanishingLocus G t) :
    x ∈ Stacks.Ample.nonvanishingLocus (F ⊗ G) (Stacks.ProductFamilyTwist.prodSection s t) := by
  have h := nonvanishingLocus_unitMul (Stacks.ProductFamilyTwist.unitOfSection F s)
    (Stacks.ProductFamilyTwist.unitOfSection G t)
  rw [Stacks.ProductFamilyTwist.globalSection_unitOfSection,
    Stacks.ProductFamilyTwist.globalSection_unitOfSection] at h
  exact (congrArg (x ∈ ·) h).mpr ⟨hs, ht⟩

/-- A section pulled back from the integral model does not vanish where the original does. -/
public theorem mem_nonvanishingLocus_pullbackGlobalSections {X Y : Scheme.{u}} (i : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) {x : X} (hx : i.base x ∈ Stacks.Ample.nonvanishingLocus M s) :
    x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj M)
      (pullbackGlobalSections i M s) :=
  (congrArg (x ∈ ·)
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i M s)).mp hx

/-- `x_{j₁}^{δ₁} x'_{j₂}^{δ₂}` does not vanish on `ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂}))`. -/
public theorem mem_nonvanishingLocus_baseSec {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (j₁ j₂ : Fin (n + 1)) {x : X} (hx : x ∈ chartPair ψ j₁ j₂) :
    x ∈ Stacks.Ample.nonvanishingLocus _ (baseSec ψ δ₁ δ₂ j₁ j₂) := by
  refine mem_nonvanishingLocus_pullbackGlobalSections ψ _ _ ?_
  refine mem_nonvanishingLocus_prodSection _ _ ?_ ?_
  · refine mem_nonvanishingLocus_pullbackGlobalSections _ _ _ ?_
    refine mem_nonvanishingLocus_pullbackGlobalSections _ _ _ ?_
    exact mem_nonvanishingLocus_degreeSection_X_pow n δ₁ j₁ _ hx.1
  · refine mem_nonvanishingLocus_pullbackGlobalSections _ _ _ ?_
    refine mem_nonvanishingLocus_pullbackGlobalSections _ _ _ ?_
    exact mem_nonvanishingLocus_degreeSection_X_pow n δ₂ j₂ _ hx.2

/-- The standard opens `D₊(T_i^d)` cover projective space over the integers. -/
public lemma exists_mem_basicOpen_X_pow (m d : ℕ)
    (p : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))) :
    ∃ i, p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i ^ d) := by
  have hadj : Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ) 0)
      (Set.range (MvPolynomial.X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) (ULift.{u} ℤ))) =
        ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    clear ‹q ∈ ⊤›
    induction q using MvPolynomial.induction_on with
    | C r =>
      exact Subalgebra.algebraMap_mem _
        (⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩ :
          MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ) 0)
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hcov := Proj.iSup_basicOpen_eq_top'
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) MvPolynomial.X
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X _ i⟩) hadj
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ▸ TopologicalSpace.Opens.mem_top p)
  refine ⟨i, ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, Proj.mem_basicOpen]
    exact p.asHomogeneousIdeal.toIdeal.ne_top_iff_one.mp p.isPrime.ne_top
  · rwa [Proj.basicOpen_pow _ _ _ hd]

/-- `Faltings.resT_degreeSection_monomial`, with the product written as a `Finsupp.prod`. -/
public theorem resT_degreeSection_monomial_finsuppProd (r d : ℕ) (k : Fin (r + 1))
    (α : Fin (r + 1) →₀ ℕ) (hα : α.degree = d) :
    resT (L := projTwist.{u} r (d : ℤ)) (projChart r k)
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) d
        ⟨MvPolynomial.monomial α 1, MvPolynomial.isHomogeneous_monomial _ hα⟩) =
      (α.prod fun ν e => projRatio.{u} r k ν ^ e) •
        resT (L := projTwist.{u} r (d : ℤ)) (projChart r k)
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) d
            ⟨MvPolynomial.X k ^ d, MvPolynomial.isHomogeneous_X_pow k d⟩) := by
  rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _]
  exact resT_degreeSection_monomial r d k α hα

/-- The chart `D₊(T_{i₀})` lies in the nonvanishing locus of the section `T_{i₀} ^ δ` of `𝒪(δ)`. -/
public theorem projChart_le_nonvanishingOpen (r δ : ℕ) (i₀ : Fin (r + 1)) :
    projChart.{u} r i₀ ≤ Stacks.NonvanishingOpen.nonvanishingOpen _ (projTwist.{u} r δ)
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) δ
        ⟨MvPolynomial.X i₀ ^ δ, MvPolynomial.isHomogeneous_X_pow i₀ δ⟩) := by
  intro p hp
  exact (Set.ext_iff.mp (nonvanishingLocus_degreeSection r δ _) p).mpr
    (mem_basicOpen_X_pow δ i₀ p hp)

/-- The pullback along `q` of the section `T_{i₀} ^ δ` of `𝒪(δ)` vanishes nowhere on
`q⁻¹ D₊(T_{i₀})`. -/
public theorem preimage_projChart_le_nvOpen {S Y : Scheme.{u}} {n : ℕ}
    (q : Y ⟶ projectiveSpaceOver n S) (i₀ : Fin (n + 1)) (δ : ℕ) :
    q ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart.{u} n i₀) ≤
      Stacks.ProjectiveFromSections.nvOpen _ (pullbackGlobalSections q _
        (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S) (projTwist.{u} n δ)
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} n) δ
            ⟨MvPolynomial.X i₀ ^ δ, MvPolynomial.isHomogeneous_X_pow i₀ δ⟩))) := by
  rw [Stacks.ProjectiveFromSections.nvOpen,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
  exact q.preimage_mono (le_of_le_of_eq
    (Scheme.Hom.preimage_mono _ (projChart_le_nonvanishingOpen n δ i₀))
    (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections
      _ _ _).symm)

/-! ### The diagonal chart `x_{i₀} x'_{i₀} ≠ 0` -/

/-- The open set of `ℙⁿ_S ×_S ℙⁿ_S` on which `x_{i₀} x'_{i₀}` does not vanish. -/
public noncomputable abbrev chartOpen (S : Scheme.{u}) (n : ℕ) (i₀ : Fin (n + 1)) :
    (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).Opens :=
  pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart.{u} n i₀) ⊓
    pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ
      (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ projChart.{u} n i₀)

/-- On the chart `x_{i₀} x'_{i₀} ≠ 0`, the restriction of the monomial `x^{α₁} x'^{α₂}` of bidegree
`(δ₁, δ₂)` is `ξ^{α₁} ξ'^{α₂}` times `x_{i₀}^{δ₁} x'_{i₀}^{δ₂}`. -/
public theorem resT_monoSec_chartOpen {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (i₀ : Fin (n + 1)) (δ₁ δ₂ : ℕ) (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ)
    (h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂) :
    resT (ψ ⁻¹ᵁ chartOpen S n i₀) (monoSec ψ δ₁ δ₂ α) =
      ψ.app (chartOpen S n i₀)
        (resO inf_le_left (Scheme.Hom.app
            (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
            ((projectiveSpaceOver.toIntegralAtUniverse n S).app (projChart.{u} n i₀)
              ((α.comapDomain Sum.inl Sum.inl_injective.injOn).prod
                fun ν e => projRatio.{u} n i₀ ν ^ e))) *
          resO inf_le_right (Scheme.Hom.app
            (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
            ((projectiveSpaceOver.toIntegralAtUniverse n S).app (projChart.{u} n i₀)
              ((α.comapDomain Sum.inr Sum.inr_injective.injOn).prod
                fun ν e => projRatio.{u} n i₀ ν ^ e)))) •
        resT (ψ ⁻¹ᵁ chartOpen S n i₀) (baseSec ψ δ₁ δ₂ i₀ i₀) := by
  rw [monoSec, dite_eq_left h, baseSec]
  refine resT_pullbackGlobalSections_eq_smul ψ (resT_prodSection_eq_smul ?_ ?_)
  · exact resT_eq_smul_of_le inf_le_left (resT_pullbackGlobalSections_eq_smul _
      (resT_pullbackGlobalSections_eq_smul _
        (resT_degreeSection_monomial_finsuppProd n δ₁ i₀ _ h.1)))
  · exact resT_eq_smul_of_le inf_le_right (resT_pullbackGlobalSections_eq_smul _
      (resT_pullbackGlobalSections_eq_smul _
        (resT_degreeSection_monomial_finsuppProd n δ₂ i₀ _ h.2)))

attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj in
/-- The section `x_{i₀}^{δ₁} x'_{i₀}^{δ₂}` vanishes nowhere on `ψ⁻¹ W`, `W` the chart
`x_{i₀} x'_{i₀} ≠ 0`. -/
public theorem preimage_chartOpen_le_nonvanishingOpen {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (i₀ : Fin (n + 1)) (δ₁ δ₂ : ℕ) :
    ψ ⁻¹ᵁ chartOpen S n i₀ ≤
      Stacks.NonvanishingOpen.nonvanishingOpen X _ (baseSec ψ δ₁ δ₂ i₀ i₀) := by
  rw [baseSec,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
  refine ψ.preimage_mono ?_
  rw [← Stacks.ProjectiveFromSections.nvOpen, Stacks.ProductFamilyTwist.nvOpen_prodSection]
  exact inf_le_inf (preimage_projChart_le_nvOpen _ i₀ δ₁) (preimage_projChart_le_nvOpen _ i₀ δ₂)

/-- If `ψ` lifts the two dominant maps `p₁, p₂ : X → C` through `φNP`, and `x_{i₀}` does not vanish
identically on `C`, then the chart `x_{i₀} x'_{i₀} ≠ 0` meets the image of the irreducible `X`. -/
public theorem nonempty_preimage_chartOpen {S X C : Scheme.{u}} [IrreducibleSpace X] {n : ℕ}
    (i₀ : Fin (n + 1)) (φNP : C ⟶ projectiveSpaceOver n S) (p₁ p₂ : X ⟶ C)
    [IsDominant p₁] [IsDominant p₂]
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (h₁ : ψ ≫ pullback.fst _ _ = p₁ ≫ φNP) (h₂ : ψ ≫ pullback.snd _ _ = p₂ ≫ φNP)
    [hU : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ projChart.{u} n i₀)] :
    ((ψ ⁻¹ᵁ chartOpen S n i₀ : X.Opens) : Set X).Nonempty := by
  set U := (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ projChart.{u} n i₀
  obtain ⟨⟨z, hz⟩⟩ := hU
  obtain ⟨a, ha⟩ := (IsDominant.denseRange (f := p₁)).exists_mem_open U.isOpen ⟨z, hz⟩
  obtain ⟨b, hb⟩ := (IsDominant.denseRange (f := p₂)).exists_mem_open U.isOpen ⟨z, hz⟩
  obtain ⟨y, hy1, hy2⟩ := nonempty_preirreducible_inter (p₁ ⁻¹ᵁ U).isOpen (p₂ ⁻¹ᵁ U).isOpen
    ⟨a, ha⟩ ⟨b, hb⟩
  have e1 : (pullback.fst _ _ : pullback (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S) ⟶ _).base (ψ.base y) = φNP.base (p₁.base y) :=
    congrArg (fun h : X ⟶ projectiveSpaceOver n S => h.base y) h₁
  have e2 : (pullback.snd _ _ : pullback (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S) ⟶ _).base (ψ.base y) = φNP.base (p₂.base y) :=
    congrArg (fun h : X ⟶ projectiveSpaceOver n S => h.base y) h₂
  refine ⟨y, ?_, ?_⟩
  · change (projectiveSpaceOver.toIntegralAtUniverse n S).base
      ((pullback.fst _ _ : pullback (projectiveSpaceOver n S ↘ S)
        (projectiveSpaceOver n S ↘ S) ⟶ _).base (ψ.base y)) ∈ projChart.{u} n i₀
    rw [e1]
    exact hy1
  · change (projectiveSpaceOver.toIntegralAtUniverse n S).base
      ((pullback.snd _ _ : pullback (projectiveSpaceOver n S ↘ S)
        (projectiveSpaceOver n S ↘ S) ⟶ _).base (ψ.base y)) ∈ projChart.{u} n i₀
    rw [e2]
    exact hy2

/-- The germ at the generic point of `X` of `ψ^* (Q^* (g^* a))`, for `ψ ≫ Q = p ≫ φ`, is the
pullback along `p` of the rational function `(φ ≫ g)^* a`. -/
public theorem germ_app_app_app {X Y Z C T : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (ψ : X ⟶ Y) (Q : Y ⟶ Z) (g : Z ⟶ T) (p : X ⟶ C) [IsDominant p] (φ : C ⟶ Z)
    (hψ : ψ ≫ Q = p ≫ φ) {D : T.Opens} {V : Y.Opens} (hV : V ≤ Q ⁻¹ᵁ (g ⁻¹ᵁ D))
    [Nonempty (ψ ⁻¹ᵁ V)] [Nonempty ((φ ≫ g) ⁻¹ᵁ D)] (a : Γ(T, D)) :
    X.germToFunctionField (ψ ⁻¹ᵁ V) (ψ.app V (resO hV (Q.app (g ⁻¹ᵁ D) (g.app D a)))) =
      functionFieldMap p (C.germToFunctionField ((φ ≫ g) ⁻¹ᵁ D) ((φ ≫ g).app D a)) := by
  have hle : ψ ⁻¹ᵁ V ≤ (ψ ≫ Q ≫ g) ⁻¹ᵁ D := fun x (hx : ψ.base x ∈ V) => hV hx
  have e1 : ψ.app V (resO hV (Q.app (g ⁻¹ᵁ D) (g.app D a))) =
      (ψ ≫ Q ≫ g).appLE D (ψ ⁻¹ᵁ V) hle a := by
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE ψ,
      ← ConcreteCategory.comp_apply (Y.presheaf.map (homOfLE hV).op), Scheme.Hom.map_appLE]
    rfl
  have e2 : ψ ≫ Q ≫ g = p ≫ (φ ≫ g) := by rw [← Category.assoc, hψ, Category.assoc]
  rw [e1]
  have e3 : ∀ (h h' : X ⟶ T) (hh : h = h') (e : ψ ⁻¹ᵁ V ≤ h ⁻¹ᵁ D),
      h.appLE D (ψ ⁻¹ᵁ V) e a = h'.appLE D (ψ ⁻¹ᵁ V) (hh ▸ e) a := by
    rintro h h' rfl e
    rfl
  rw [e3 _ _ e2, Scheme.Hom.comp_appLE]
  exact (Scheme.Hom.functionFieldMap_germToFunctionField p (U := (φ ≫ g) ⁻¹ᵁ D)
    (V := ψ ⁻¹ᵁ V) _ _).symm

private lemma ringHom_finsuppProd_pow {R L ι : Type*} [CommSemiring R] [CommSemiring L]
    (F : R →+* L) (β : ι →₀ ℕ) (r : ι → R) :
    F (β.prod fun ν e => r ν ^ e) = β.prod fun ν e => F (r ν) ^ e := by
  simp [map_finsuppProd]

attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj in
/-- On the chart `x_{i₀} x'_{i₀} ≠ 0`, the restriction to the integral scheme `X` of a form `P` of
bidegree `(δ₁, δ₂)` is `P(ξ, ξ')` times `x_{i₀}^{δ₁} x'_{i₀}^{δ₂}`, where `ξ_ν = pr₁^* x_ν`,
`ξ'_ν = pr₂^* x_ν` for the affine coordinates `x_ν = T_ν / T_{i₀}` on `C`. -/
public theorem germ_div_vojtaFormRestriction {S X C : Scheme.{u}} [IsIntegral X]
    [IsIntegral C] {n : ℕ} {k : Type*} [Field k] [Algebra k C.functionField]
    [Algebra k X.functionField] (i₀ : Fin (n + 1)) (φNP : C ⟶ projectiveSpaceOver n S)
    (p₁ p₂ : X ⟶ C)
    [IsDominant p₁] [IsDominant p₂]
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (h₁ : ψ ≫ pullback.fst _ _ = p₁ ≫ φNP) (h₂ : ψ ≫ pullback.snd _ _ = p₂ ≫ φNP)
    [Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ projChart.{u} n i₀)]
    (pr₁ pr₂ : C.functionField →ₐ[k] X.functionField)
    (hpr₁ : ∀ a, pr₁ a = functionFieldMap p₁ a) (hpr₂ : ∀ a, pr₂ a = functionFieldMap p₂ a)
    (c₀ : Γ(S, ⊤) →+* k)
    (hc₀ : ∀ a, algebraMap k X.functionField (c₀ a) = X.presheaf.germ ⊤ (genericPoint X) trivial
      ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop a))
    (δ₁ δ₂ : ℕ) (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    (hPm : P.map c₀ ∈ MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    [Nonempty (ψ ⁻¹ᵁ chartOpen S n i₀)]
    (hWnv : ψ ⁻¹ᵁ chartOpen S n i₀ ≤
      Stacks.NonvanishingOpen.nonvanishingOpen X _ (baseSec ψ δ₁ δ₂ i₀ i₀)) :
    X.germToFunctionField (ψ ⁻¹ᵁ chartOpen S n i₀)
        (Stacks.ProjectiveFromSections.div (baseSec ψ δ₁ δ₂ i₀ i₀) hWnv
          (resT (ψ ⁻¹ᵁ chartOpen S n i₀) (vojtaFormRestriction ψ δ₁ δ₂ P))) =
      BombieriVojta.affineEvaluation pr₁ pr₂
        (fun ν => C.germToFunctionField _
          ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S).app _ (projRatio.{u} n i₀ ν)))
        i₀ (δ₁, δ₂) ⟨P.map c₀, hPm⟩ := by
  classical
  set g := projectiveSpaceOver.toIntegralAtUniverse n S
  set W : X.Opens := ψ ⁻¹ᵁ chartOpen S n i₀ with hWdef
  set x : Fin (n + 1) → C.functionField := fun ν => C.germToFunctionField _
    ((φNP ≫ g).app _ (projRatio.{u} n i₀ ν)) with hx
  -- on `W`, the restriction of `P` is `c • x_{i₀}^{δ₁} x'_{i₀}^{δ₂}`
  let A : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(X, W) := fun α =>
    ψ.app (chartOpen S n i₀)
      (resO inf_le_left (Scheme.Hom.app
          (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
          (g.app (projChart.{u} n i₀)
            ((α.comapDomain Sum.inl Sum.inl_injective.injOn).prod
              fun ν e => projRatio.{u} n i₀ ν ^ e))) *
        resO inf_le_right (Scheme.Hom.app
          (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)) _
          (g.app (projChart.{u} n i₀)
            ((α.comapDomain Sum.inr Sum.inr_injective.injOn).prod
              fun ν e => projRatio.{u} n i₀ ν ^ e))))
  let c : Γ(X, W) := ∑ α ∈ P.support,
    resO (le_top : W ≤ ⊤)
      ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop (P.coeff α)) * A α
  have hres : resT W (vojtaFormRestriction ψ δ₁ δ₂ P) = c • resT W (baseSec ψ δ₁ δ₂ i₀ i₀) := by
    rw [vojtaFormRestriction_eq_sum]
    simp only [c, Finset.sum_smul]
    refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun α hα => ?_)
    have hdeg := degree_comapDomain_of_weight (hP (MvPolynomial.mem_support_iff.mp hα))
    calc resT W ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop (P.coeff α) •
          monoSec ψ δ₁ δ₂ α)
        = resO (le_top : W ≤ ⊤) ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop
            (P.coeff α)) • resT W (monoSec ψ δ₁ δ₂ α) :=
          Stacks.ProjectiveFromSections.resM_smul _ _ _
      _ = _ := by rw [resT_monoSec_chartOpen ψ i₀ δ₁ δ₂ α hdeg, smul_smul]
  -- the germ of `c` at the generic point is `P(ξ, ξ')`
  have hgerm : X.germToFunctionField W c = BombieriVojta.affineEvaluation pr₁ pr₂ x i₀ (δ₁, δ₂)
      ⟨P.map c₀, hPm⟩ := by
    have hx0 : x i₀ = 1 := by
      change C.germToFunctionField _ ((φNP ≫ g).app _ (projRatio.{u} n i₀ i₀)) = 1
      rw [projRatio_self]
      exact ((φNP ≫ g).app _ ≫ C.germToFunctionField _).hom.map_one
    have hev : BombieriVojta.affineEvaluation pr₁ pr₂ x i₀ (δ₁, δ₂) ⟨P.map c₀, hPm⟩ =
        MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) (P.map c₀) /
          (pr₁ (x i₀) ^ δ₁ * pr₂ (x i₀) ^ δ₂) := rfl
    rw [hev, hx0, map_one, map_one, one_pow, one_pow, mul_one, div_one,
      MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_eq]
    simp only [c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hA : X.germToFunctionField W (A α) =
        (α.comapDomain Sum.inl Sum.inl_injective.injOn).prod (fun ν e => pr₁ (x ν) ^ e) *
          (α.comapDomain Sum.inr Sum.inr_injective.injOn).prod (fun ν e => pr₂ (x ν) ^ e) := by
      have k1 := germ_app_app_app ψ _ g p₁ φNP h₁ (D := projChart.{u} n i₀) (V := chartOpen S n i₀)
        inf_le_left ((α.comapDomain Sum.inl Sum.inl_injective.injOn).prod
          fun ν e => projRatio.{u} n i₀ ν ^ e)
      have k2 := germ_app_app_app ψ _ g p₂ φNP h₂ (D := projChart.{u} n i₀) (V := chartOpen S n i₀)
        inf_le_right ((α.comapDomain Sum.inr Sum.inr_injective.injOn).prod
          fun ν e => projRatio.{u} n i₀ ν ^ e)
      simp only [A, map_mul]
      refine (congrArg₂ (· * ·) k1 k2).trans ?_
      simp only [hpr₁, hpr₂, hx]
      congr 1
      · exact ringHom_finsuppProd_pow ((functionFieldMap p₁).comp
          ((φNP ≫ g).app _ ≫ C.germToFunctionField _).hom) _ _
      · exact ringHom_finsuppProd_pow ((functionFieldMap p₂).comp
          ((φNP ≫ g).app _ ≫ C.germToFunctionField _).hom) _ _
    rw [map_mul, hA, RingHom.comp_apply, hc₀]
    congr 1
    · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      change _ = α.prod fun i e => Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)) i ^ e
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
      simp only [Finsupp.comapDomain_apply, Sum.elim_inl, Sum.elim_inr]
  rw [← hgerm, ← Stacks.ProjectiveFromSections.eq_div _ _ hres.symm]

attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj in
/-- A form `P` of bidegree `(δ₁, δ₂)` restricts to zero on the integral scheme `X` if and only if
`P(ξ, ξ') = 0` in the function field of `X`, where `ξ_ν = pr₁^* x_ν` and `ξ'_ν = pr₂^* x_ν` for the
affine coordinates `x_ν = T_ν / T_{i₀}` on `C`, as soon as `x_{i₀}` does not vanish identically on
`C`. -/
public theorem vojtaFormRestriction_eq_zero_iff {S X C : Scheme.{u}} [IsIntegral X]
    [IsIntegral C] {n : ℕ} {k : Type*} [Field k] [Algebra k C.functionField]
    [Algebra k X.functionField] (i₀ : Fin (n + 1)) (φNP : C ⟶ projectiveSpaceOver n S)
    (p₁ p₂ : X ⟶ C) [IsDominant p₁] [IsDominant p₂]
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (h₁ : ψ ≫ pullback.fst _ _ = p₁ ≫ φNP) (h₂ : ψ ≫ pullback.snd _ _ = p₂ ≫ φNP)
    [Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ⁻¹ᵁ projChart.{u} n i₀)]
    (pr₁ pr₂ : C.functionField →ₐ[k] X.functionField)
    (hpr₁ : ∀ a, pr₁ a = functionFieldMap p₁ a) (hpr₂ : ∀ a, pr₂ a = functionFieldMap p₂ a)
    (c₀ : Γ(S, ⊤) →+* k)
    (hc₀ : ∀ a, algebraMap k X.functionField (c₀ a) = X.presheaf.germ ⊤ (genericPoint X) trivial
      ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop a))
    (δ₁ δ₂ : ℕ) (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    (hPm : P.map c₀ ∈ MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) :
    vojtaFormRestriction ψ δ₁ δ₂ P = 0 ↔
      BombieriVojta.affineEvaluation pr₁ pr₂
        (fun ν => C.germToFunctionField _
          ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n S).app _ (projRatio.{u} n i₀ ν)))
        i₀ (δ₁, δ₂) ⟨P.map c₀, hPm⟩ = 0 := by
  have hW : ((ψ ⁻¹ᵁ chartOpen S n i₀ : X.Opens) : Set X).Nonempty :=
    nonempty_preimage_chartOpen i₀ φNP p₁ p₂ ψ h₁ h₂
  have : Nonempty (ψ ⁻¹ᵁ chartOpen S n i₀) := hW.to_subtype
  have hWnv := preimage_chartOpen_le_nonvanishingOpen ψ i₀ δ₁ δ₂
  rw [← germ_div_vojtaFormRestriction i₀ φNP p₁ p₂ ψ h₁ h₂ pr₁ pr₂ hpr₁ hpr₂ c₀ hc₀ δ₁ δ₂ P hP hPm
    hWnv, map_eq_zero_iff _ (Scheme.germToFunctionField_injective X _)]
  constructor
  · intro h0
    refine (Stacks.ProjectiveFromSections.eq_div _ hWnv ?_).symm
    rw [zero_smul, h0]
    exact (map_zero _).symm
  · intro h0
    have h1 := Stacks.ProjectiveFromSections.div_smul _ hWnv
      (resT (ψ ⁻¹ᵁ chartOpen S n i₀) (vojtaFormRestriction ψ δ₁ δ₂ P))
    rw [h0, zero_smul] at h1
    exact eq_zero_of_res_eq_zero _ hW _ h1.symm

/-! ### Pulled-back twisting sheaves -/

/-- `φ^*𝒪(d)`, for `φ : Y ⟶ ℙⁿ_S`. -/
public noncomputable abbrev twistPb {S Y : Scheme.{u}} {n : ℕ}
    (φ : Y ⟶ projectiveSpaceOver n S) (d : ℕ) : Y.Modules :=
  (Scheme.Modules.pullback φ).obj
    ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
      (projTwist.{u} n d))

/-- `φ^*𝒪(d)` is invertible. -/
public instance {S Y : Scheme.{u}} {n : ℕ} (φ : Y ⟶ projectiveSpaceOver n S) (d : ℕ) :
    Stacks.Ample.IsInvertibleModule Y (twistPb φ d) := by
  dsimp only [twistPb, projTwist]; infer_instance

/-- The section `φ^* T_j ^ d` vanishes nowhere on the chart `φ⁻¹ D₊(T_j)`. -/
public theorem chartOne_le_nvOpen {S Y : Scheme.{u}} {n : ℕ} (φ : Y ⟶ projectiveSpaceOver n S)
    (j : Fin (n + 1)) (d : ℕ) :
    chartOne φ j ≤ Stacks.ProjectiveFromSections.nvOpen _ (vojtaCoordinatePow φ d j) :=
  preimage_projChart_le_nvOpen φ j d

/-- `Faltings.resT_vojtaCoordinatePow`, with the power taken on the integral model: on the chart
`φ⁻¹ D₊(T_j)`, `φ^* T_ν^d = φ^*((T_ν / T_j)^d) · φ^* T_j^d`. -/
public theorem resT_vojtaCoordinatePow_eq_app_pow_smul {S Y : Scheme.{u}} {n : ℕ}
    (φ : Y ⟶ projectiveSpaceOver n S) (d : ℕ) (j ν : Fin (n + 1)) :
    resT (chartOne φ j) (vojtaCoordinatePow φ d ν) =
      φ.app _ ((projectiveSpaceOver.toIntegralAtUniverse n S).app (projChart.{u} n j)
        (projRatio.{u} n j ν ^ d)) • resT (chartOne φ j) (vojtaCoordinatePow φ d j) := by
  rw [resT_vojtaCoordinatePow φ d j ν]
  congr 1
  exact (map_pow ((projectiveSpaceOver.toIntegralAtUniverse n S).app _ ≫ φ.app _).hom _ d).symm

end ProjectiveSpace

end Faltings
