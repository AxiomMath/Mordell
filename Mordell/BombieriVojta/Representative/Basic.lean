module
public import Mordell.BombieriVojta.LineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFixedTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProductFamilyTwist.Basic

/-!
# Representatives of sections of `𝒪(V)`

In Section 6 of Bombieri's proof of the Mordell conjecture, `ψ : C × C → ℙⁿ × ℙⁿ` and
`φ_B : C × C → ℙᵐ` are projective embeddings with homogeneous coordinates `(x, x')` and `y`, and
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. A *representative* (or *collection of forms associated to*)
a global section `s` of `𝒪(V)` is a family `F = (F_i)_{0 ≤ i ≤ m}` of bihomogeneous forms of
bidegree `(δ₁, δ₂)` in `x₀, …, xₙ` and `x'₀, …, x'ₙ` with
`F_i|_{C × C} = s · y_i^d` in `H⁰(C × C, ψ^*𝒪(δ₁, δ₂))` for every `i`; one writes
`s = (F_i(x, x') / y_i^d)|_{C × C}`.

As for `Faltings.vojtaLineBundle`, the definitions are made for an arbitrary scheme `X` over an
arbitrary base `S`, with morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`.

## Main definitions

* `Faltings.vojtaCoordinatePow φ d i`: the global section `y_i^d|_X` of `φ^*𝒪(d)`.
* `Faltings.vojtaFormRestriction ψ δ₁ δ₂`: the restriction `F ↦ F|_X` of forms of bidegree
  `(δ₁, δ₂)` to global sections of `ψ^*(pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂))`.
* `Faltings.IsVojtaRepresentative ψ φ δ₁ δ₂ d s F`: the family `F` of forms is a representative
  of the global section `s` of `Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d`.

## Main results

* `Faltings.prodSection_eq_leftUnitor_inv_tensorHom`: the product of two global sections is the
  global section of `λ_𝟙⁻¹ ≫ (a ⊗ b)`.
* `Faltings.isVojtaRepresentative_iff`: `IsVojtaRepresentative` with the restriction of forms
  and the products of sections written out.

## Implementation notes

* The forms have coefficients in `Γ(S, 𝒪_S)`, which act on sections over `X` through the
  structure morphism `X ⟶ S`. The source's forms over `k̄` and sections defined over `k̄` are the
  case `S = Spec k̄`, after base change of `C × C` and the two embeddings.
* The variables `x_ν`, `x'_ν` are `Sum.inl ν`, `Sum.inr ν` in
  `MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)`, and bihomogeneity of bidegree `(δ₁, δ₂)`
  is `MvPolynomial.IsWeightedHomogeneous` for the `ℕ × ℕ`-valued weight giving `x_ν` the weight
  `(1, 0)` and `x'_ν` the weight `(0, 1)`, the convention of
  `Faltings.BombieriVojta.affineEvaluation`. The integers `δ₁, δ₂, d` are natural numbers, as
  they must be for forms of bidegree `(δ₁, δ₂)` and for `y_i^d` to exist.
* The restriction `F|_X` of a form is `∑_α c_α · ψ^*(pr₁^* x^{α₁} ⊗ pr₂^* x'^{α₂})`, where
  `x^{α₁}` is the global section of `𝒪(δ₁)` on `ℙⁿ_S` pulled back from the section
  `ProjectiveSpectrum.Proj.degreeSection` of the integral model, and likewise for `y_i^d`.
  Monomials not of bidegree `(δ₁, δ₂)` are sent to `0`, so `vojtaFormRestriction ψ δ₁ δ₂` is
  defined, and additive, on all polynomials; on forms of bidegree `(δ₁, δ₂)` it is the
  restriction. Products of global sections are `Stacks.ProductFamilyTwist.prodSection`.
* Since `𝒪(V)` is written with `φ^*𝒪(-d)` in place of `φ^*𝒪(d)⁻¹`, the product `s · y_i^d`
  is formed with the canonical multiplication `φ^*𝒪(-d) ⊗ φ^*𝒪(d) ⟶ φ^*𝒪(0)`, the pullback
  of `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`. Its value lies in
  `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(0)`, and the identity `F_i|_X = s · y_i^d` is stated there, the left
  side tensored with the unit section `1` of `𝒪(0)`. Since `𝒪(0) ≅ 𝒪` carries `1` to `1`, this
  is the source's identity in `H⁰(X, ψ^*𝒪(δ₁, δ₂))`, read through the canonical isomorphism
  `ψ^*𝒪(δ₁, δ₂) ≅ ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(0)`, and no non-canonical identification of `𝒪(0)` with
  `𝒪` enters.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

section

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  MvPolynomial.gradedAlgebra

/-- `vojtaCoordinatePow φ d i` is the global section `y_i^d|_X` of `φ^*𝒪(d)`, for
`φ : X ⟶ ℙᵐ_S` and `y_0, …, y_m` the homogeneous coordinates of `ℙᵐ_S`: the section `y_i^d` of
`𝒪(d)` on the integral model `ℙᵐ_ℤ`, pulled back to `ℙᵐ_S` and then along `φ`. -/
@[expose] public noncomputable def vojtaCoordinatePow {S X : Scheme.{u}} {m : ℕ}
    (φ : X ⟶ projectiveSpaceOver m S) (d : ℕ) (i : Fin (m + 1)) :
    Γ((Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m S)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (d : ℤ))), ⊤) :=
  pullbackGlobalSections φ _
    (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse m S) _
      (ProjectiveSpectrum.Proj.degreeSection
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) d
        ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩))

/-- `vojtaFormRestriction ψ δ₁ δ₂` is the restriction `F ↦ F|_X` of bihomogeneous forms of
bidegree `(δ₁, δ₂)` in `x_ν = Sum.inl ν`, `x'_ν = Sum.inr ν` with coefficients in `Γ(S, ⊤)` to
global sections of `ψ^*(pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂))`, for `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S`. It sends
`∑_α c_α x^{α₁} x'^{α₂}` to `∑_α c_α · ψ^*(pr₁^* x^{α₁} ⊗ pr₂^* x'^{α₂})`, the coefficients
acting through `X ⟶ S`, and a monomial not of bidegree `(δ₁, δ₂)` to `0`. -/
@[expose] public noncomputable def vojtaFormRestriction {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) :
    MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤) →+
      Γ((Scheme.Modules.pullback ψ).obj
        ((Scheme.Modules.pullback
            (pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (δ₁ : ℤ))) ⊗
        (Scheme.Modules.pullback
            (pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (δ₂ : ℤ)))), ⊤) :=
  let g := projectiveSpaceOver.toIntegralAtUniverse n S
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)
  let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  -- the section of `𝒪(a)` on `ℙⁿ_S` given by the monomial `x^β` of degree `a`
  let form : ∀ (a : ℕ) (β : Fin (n + 1) →₀ ℕ), β.degree = a →
      Γ((Scheme.Modules.pullback g).obj (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (a : ℤ)), ⊤) :=
    fun a β h => pullbackGlobalSections g _
      (ProjectiveSpectrum.Proj.degreeSection 𝒜 a
        ⟨MvPolynomial.monomial β 1, MvPolynomial.isHomogeneous_monomial _ h⟩)
  let twist : ℤ → (projectiveSpaceOver n S).Modules := fun a =>
    (Scheme.Modules.pullback g).obj (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 a)
  let L : X.Modules := (Scheme.Modules.pullback ψ).obj
    ((Scheme.Modules.pullback p₁).obj (twist δ₁) ⊗ (Scheme.Modules.pullback p₂).obj (twist δ₂))
  -- the restriction of the monomial `x^{α₁} x'^{α₂}`
  let mono : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(L, ⊤) := fun α =>
    if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
        (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
      pullbackGlobalSections ψ _ (Stacks.ProductFamilyTwist.prodSection
        (pullbackGlobalSections p₁ _ (form δ₁ _ h.1))
        (pullbackGlobalSections p₂ _ (form δ₂ _ h.2)))
    else 0
  let σ : X ⟶ S := ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)
  (Finsupp.liftAddHom fun α =>
    { toFun := fun c => σ.appTop c • mono α
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

/-- `IsVojtaRepresentative ψ φ δ₁ δ₂ d s F`: the family `F = (F_i)_{0 ≤ i ≤ m}` is a representative
of the global section `s` of `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(-d)`. That is, every `F_i` is a
bihomogeneous form of bidegree `(δ₁, δ₂)` in the variables `x_ν = Sum.inl ν` and
`x'_ν = Sum.inr ν`, and `F_i|_X = s · y_i^d` for every `i` (`vojtaFormRestriction`,
`vojtaCoordinatePow`), where `y_0, …, y_m` are the homogeneous coordinates of `ℙᵐ_S`. The identity
is read in `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(0)`, with the canonical multiplication `𝒪(-d) ⊗ 𝒪(d) ⟶ 𝒪(0)` on the
right and the unit section of `𝒪(0)` on the left. -/
@[expose, faltings "def_bv_representative"]
public noncomputable def IsVojtaRepresentative {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) : Prop :=
  -- `𝒪(a)` on `ℙʳ_S`, pulled back from the integral model
  let g : ∀ r : ℕ, projectiveSpaceOver r S ⟶ projectiveSpaceAtUniverse.{u} r := fun r =>
    projectiveSpaceOver.toIntegralAtUniverse r S
  let T : ∀ r : ℕ, ℤ → (projectiveSpaceAtUniverse.{u} r).Modules := fun r a =>
    ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (g r)).obj (T r a)
  let e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  let O₁ := (Scheme.Modules.pullback (pullback.fst _ _)).obj (twist n δ₁)
  let O₂ := (Scheme.Modules.pullback (pullback.snd _ _)).obj (twist n δ₂)
  let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
  let M : X.Modules := (Scheme.Modules.pullback φ).obj (twist m (-(d : ℤ)))
  let N : X.Modules := (Scheme.Modules.pullback φ).obj (twist m d)
  let Z : X.Modules := (Scheme.Modules.pullback φ).obj (twist m 0)
  -- the canonical multiplication `φ^*𝒪(-d) ⊗ φ^*𝒪(d) ⟶ φ^*𝒪(0)`
  let μ : M ⊗ N ⟶ Z :=
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ (twist m (-(d : ℤ))) (twist m d)).inv ≫
      (Scheme.Modules.pullback φ).map
        ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (g m) (T m (-(d : ℤ))) (T m d)).inv ≫
          (Scheme.Modules.pullback (g m)).map
            ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (T m (-(d : ℤ))) (T m d)).hom ≫
              Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (-(d : ℤ)) d ≫
              eqToHom (congrArg (T m) (neg_add_cancel (d : ℤ)))))
  -- the unit section of `φ^*𝒪(0)`
  let one : Γ(Z, ⊤) := pullbackGlobalSections φ (twist m 0)
    (pullbackGlobalSections (g m) (T m 0)
      (ProjectiveSpectrum.Proj.degreeSection
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 0
        ⟨1, MvPolynomial.isHomogeneous_one _ _⟩))
  (∀ i, (F i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) ∧
    ∀ i, e (L ⊗ Z) ((e _).symm (Stacks.ProductFamilyTwist.prodSection s
        (vojtaCoordinatePow φ d i)) ≫ (α_ L M N).hom ≫ (L ◁ μ)) =
      Stacks.ProductFamilyTwist.prodSection (vojtaFormRestriction ψ δ₁ δ₂ (F i)) one

/-- The product `Stacks.ProductFamilyTwist.prodSection a b` of two global sections is the
global section of `λ_𝟙⁻¹ ≫ (a ⊗ b)`, the two sections read as morphisms out of the monoidal
unit. -/
public theorem prodSection_eq_leftUnitor_inv_tensorHom {X : Scheme.{u}} {A B : X.Modules}
    (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    Stacks.ProductFamilyTwist.prodSection a b =
      Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ ((λ_ (𝟙_ X.Modules)).inv ≫
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm a ⊗ₘ
          (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm b)) := by
  refine congrArg (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _) ?_
  rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, whiskerRight_id]
  simp [Stacks.TensorSectionNonvanishing.unitMul, Stacks.TensorSectionNonvanishing.mulRight,
    Stacks.ProductFamilyTwist.unitOfSection]

/-- `IsVojtaRepresentative ψ φ δ₁ δ₂ d s F` with everything written out: the restriction of a
form is the sum over its support of the restricted monomials, and products of global sections
are `λ_𝟙⁻¹ ≫ (a ⊗ b)` (`prodSection_eq_leftUnitor_inv_tensorHom`). -/
public theorem isVojtaRepresentative_iff {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) :
    IsVojtaRepresentative ψ φ δ₁ δ₂ d s F ↔
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  -- `𝒪(a)` on `ℙʳ_S`, pulled back from the integral model
  let g : ∀ r : ℕ, projectiveSpaceOver r S ⟶ projectiveSpaceAtUniverse.{u} r := fun r =>
    projectiveSpaceOver.toIntegralAtUniverse r S
  let T : ∀ r : ℕ, ℤ → (projectiveSpaceAtUniverse.{u} r).Modules := fun r a =>
    ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (g r)).obj (T r a)
  -- the section of `𝒪(a)` on `ℙʳ_S` given by an integral form of degree `a`
  let form : ∀ (r a : ℕ), MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a →
      Γ(twist r a, ⊤) := fun r a p =>
    pullbackGlobalSections (g r) (T r a)
      (ProjectiveSpectrum.Proj.degreeSection
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a p)
  let e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
  let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
  let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
  let M : X.Modules := (Scheme.Modules.pullback φ).obj (twist m (-(d : ℤ)))
  let N : X.Modules := (Scheme.Modules.pullback φ).obj (twist m d)
  let Z : X.Modules := (Scheme.Modules.pullback φ).obj (twist m 0)
  -- the product of two global sections
  let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
    fun {Y} {_ _} a b =>
      let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
      eY _ ((λ_ (𝟙_ Y.Modules)).inv ≫ ((eY _).symm a ⊗ₘ (eY _).symm b))
  -- the canonical multiplication `φ^*𝒪(-d) ⊗ φ^*𝒪(d) ⟶ φ^*𝒪(0)`
  let μ : M ⊗ N ⟶ Z :=
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ (twist m (-(d : ℤ))) (twist m d)).inv ≫
      (Scheme.Modules.pullback φ).map
        ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (g m) (T m (-(d : ℤ))) (T m d)).inv ≫
          (Scheme.Modules.pullback (g m)).map
            ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (T m (-(d : ℤ))) (T m d)).hom ≫
              Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (-(d : ℤ)) d ≫
              eqToHom (congrArg (T m) (neg_add_cancel (d : ℤ)))))
  -- `y_i^d` restricted to `X`, and the unit section of `φ^*𝒪(0)`
  let y : Fin (m + 1) → Γ(N, ⊤) := fun i =>
    pullbackGlobalSections φ (twist m d)
      (form m d ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)
  let one : Γ(Z, ⊤) := pullbackGlobalSections φ (twist m 0)
    (form m 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩)
  -- the restriction of a bihomogeneous form of bidegree `(δ₁, δ₂)` to `X`
  let σ : X ⟶ S := ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)
  let mono : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(L, ⊤) := fun α =>
    if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
        (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
      pullbackGlobalSections ψ (O₁ ⊗ O₂) (tensorSec
        (pullbackGlobalSections p₁ (twist n δ₁)
          (form n δ₁ ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
            MvPolynomial.isHomogeneous_monomial _ h.1⟩))
        (pullbackGlobalSections p₂ (twist n δ₂)
          (form n δ₂ ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
            MvPolynomial.isHomogeneous_monomial _ h.2⟩)))
    else 0
  let restrict : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤) → Γ(L, ⊤) := fun P =>
    ∑ α ∈ P.support, σ.appTop (P.coeff α) • mono α
  (∀ i, (F i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) ∧
    ∀ i, e (L ⊗ Z) ((e _).symm (tensorSec s (y i)) ≫ (α_ L M N).hom ≫ (L ◁ μ)) =
      tensorSec (restrict (F i)) one
 := by
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  simp only [vojtaFormRestriction, vojtaCoordinatePow, AddMonoidHom.comp_apply,
    Finsupp.liftAddHom_apply, prodSection_eq_leftUnitor_inv_tensorHom]
  rfl

end

end Faltings
