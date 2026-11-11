module
public import Mordell.BombieriVojta.Representative.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio

/-!
# The standard charts of the integral model of projective space

`ℙʳ_ℤ` is `AlgebraicGeometry.Proj` of `ℤ[T_0, …, T_r]` graded by degree
(`Faltings.projGrading`). This file names its twisting sheaves `𝒪(a)` (`Faltings.projTwist`), its
standard charts `D₊(T_k)` (`Faltings.projChart`) and the functions `T_ν / T_k` on them
(`Faltings.projRatio`), and records how the unit of `f^* ⊣ f_*` (`Faltings.pullbackUnitApp`) and
germs at the generic point interact with restriction of sections.

## Main definitions

* `Faltings.projGrading`, `Faltings.projTwist`, `Faltings.projChart`, `Faltings.projRatio`.
* `Faltings.pullbackUnitApp f t`: the image of a section `t` under the unit of `f^* ⊣ f_*`.

## Main results

* `Faltings.degree_comapDomain_of_weight`: a monomial of weight `(δ₁, δ₂)` in `x, x'` has degree
  `δ₁` in `x` and `δ₂` in `x'`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings

universe u

open TopologicalSpace Opposite
open Stacks.ProjectiveFromSections (resT resO)

/-- The image of a section under the unit of `f^* ⊣ f_*`. -/
public noncomputable abbrev pullbackUnitApp {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    {T : Y.Opens} (t : Γ(M, T)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ T) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app T t

/-- The unit of `f^* ⊣ f_*` is `f^♯`-semilinear on sections. -/
public theorem pullbackUnitApp_smul {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {T : Y.Opens}
    (r : Γ(Y, T)) (t : Γ(M, T)) : pullbackUnitApp f (r • t) = f.app T r • pullbackUnitApp f t :=
  Scheme.Modules.Hom.app_smul _ r t

/-- The unit of `f^* ⊣ f_*` commutes with restriction of sections. -/
public theorem pullbackUnitApp_res {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {T T' : Y.Opens}
    (h : T' ≤ T) (t : Γ(M, T)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (pullbackUnitApp f t) =
      pullbackUnitApp f (M.presheaf.map (homOfLE h).op t) :=
  (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op t).symm

/-- The pullback of a global section, restricted to `f⁻¹ T`, is the image under the unit of
`f^* ⊣ f_*` of its restriction to `T`. -/
public theorem resT_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (T : Y.Opens) (t : Γ(M, ⊤)) :
    resT (f ⁻¹ᵁ T) (pullbackGlobalSections f M t) = pullbackUnitApp f (resT T t) := by
  rw [← pullbackUnitApp_res]
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ T ≤ ⊤)).op
    (((Scheme.Modules.pullback f).obj M).presheaf.map (eqToHom (by simp)).op
      (pullbackUnitApp f t)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The image of a restricted section in the function field is that of the section. -/
public theorem germToFunctionField_resO {X : Scheme.{u}} [IrreducibleSpace X] {V W : X.Opens}
    (h : V ≤ W) [Nonempty V] [Nonempty W] (a : Γ(X, W)) :
    X.germToFunctionField V (resO h a) = X.germToFunctionField W a :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ a

/-- Pulling back along `h` and then restricting is restricting and then pulling back. -/
public theorem app_resO {X Y : Scheme.{u}} (h : X ⟶ Y) {O O' : Y.Opens} (hO : O' ≤ O)
    (t : Γ(Y, O)) : h.app O' (resO hO t) = resO (h.preimage_mono hO) (h.app O t) :=
  congr($(h.naturality (homOfLE hO).op) t)

/-- A monomial of weight `(δ₁, δ₂)`, for the weight giving `x_ν = Sum.inl ν` weight `(1, 0)` and
`x'_ν = Sum.inr ν` weight `(0, 1)`, has `x`-degree `δ₁` and `x'`-degree `δ₂`. -/
public theorem degree_comapDomain_of_weight {ι : Type*} [Finite ι] {α : (ι ⊕ ι) →₀ ℕ}
    {δ₁ δ₂ : ℕ}
    (h : Finsupp.weight (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))))
      α = (δ₁, δ₂)) :
    (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ := by
  classical
  have := Fintype.ofFinite ι
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at h
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [Finsupp.comapDomain_apply]
  constructor
  · have := congrArg Prod.fst h
    simpa [Prod.fst_sum] using this
  · have := congrArg Prod.snd h
    simpa [Prod.snd_sum] using this

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The grading of `ℤ[T_0, …, T_r]` by degree, whose `Proj` is `ℙʳ_ℤ`. -/
public abbrev projGrading (r : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)

/-- The twisting sheaf `𝒪(a)` on `ℙʳ_ℤ`. -/
public noncomputable abbrev projTwist (r : ℕ) (a : ℤ) :
    (AlgebraicGeometry.Proj (projGrading.{u} r)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf (projGrading.{u} r) a

/-- The standard chart `D₊(T_k)` of `ℙʳ_ℤ`. -/
public noncomputable abbrev projChart (r : ℕ) (k : Fin (r + 1)) :
    (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens :=
  Proj.basicOpen (projGrading.{u} r) (MvPolynomial.X k)

/-- The function `T_ν / T_k` on the chart `D₊(T_k)` of `ℙʳ_ℤ`. -/
public noncomputable abbrev projRatio (r : ℕ) (k ν : Fin (r + 1)) :
    Γ(AlgebraicGeometry.Proj (projGrading.{u} r), projChart r k) :=
  Proj.awayToSection _ (MvPolynomial.X k)
    (HomogeneousLocalization.Away.mk (projGrading.{u} r) (MvPolynomial.isHomogeneous_X _ k) 1
      (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))

/-- The value of `T_ν / T_k` at a point of `D₊(T_k)`. -/
public theorem val_projRatio (r : ℕ) (k ν : Fin (r + 1)) (x : projChart.{u} r k) :
    ((projRatio r k ν).1 x).val = Localization.mk (MvPolynomial.X ν)
      ⟨MvPolynomial.X k, x.2⟩ := by
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  erw [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  simp

/-- `T_j / T_j = 1`. -/
public theorem projRatio_self (r : ℕ) (j : Fin (r + 1)) : projRatio.{u} r j j = 1 := by
  have : HomogeneousLocalization.Away.mk (projGrading.{u} r) (MvPolynomial.isHomogeneous_X _ j) 1
      (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X _ j) = 1 := by
    apply HomogeneousLocalization.val_injective
    erw [HomogeneousLocalization.Away.val_mk]
    rw [HomogeneousLocalization.val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp⟩
  rw [projRatio, this, map_one]

end ProjectiveSpace

end Faltings
