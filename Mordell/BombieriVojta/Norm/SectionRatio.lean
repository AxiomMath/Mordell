module
public import Mordell.BombieriVojta.LineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.VeryAmpleFixedTwist.Basic

/-!
# The rational function `g = s / (x₀^{δ₁} x₀'^{δ₂} / y₀^d)`

In Section 9 of Bombieri's proof of the Mordell conjecture, `ψ : C × C → ℙⁿ × ℙⁿ` and
`φ_B : C × C → ℙᵐ` are projective embeddings with homogeneous coordinates `(x, x')` and `y`, and
`s` is a global section of `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. On the open set
`U = D(x₀ x₀' y₀)` where `x₀`, `x₀'` and `y₀` do not vanish, the section
`e = x₀^{δ₁} x₀'^{δ₂} y₀^{-d}` of `𝒪(V)` is regular and nowhere vanishing, so `s|_U = g_U · e` for
a unique regular function `g_U` on `U`. Its image in the function field is the rational function
`g = s / (x₀^{δ₁} x₀'^{δ₂} / y₀^d)` on `C × C`.

As for `Faltings.vojtaLineBundle`, the definition is made for an integral scheme `X` over an
arbitrary base `S`, with morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`.

## Main definitions

* `Faltings.vojtaSectionRatio ψ φ δ₁ δ₂ d s`: the rational function
  `s / (x₀^{δ₁} x₀'^{δ₂} y₀^{-d})` in the function field of `X`.

## Implementation notes

* `U` is `ψ⁻¹(pr₁⁻¹ D₊(x₀) ∩ pr₂⁻¹ D₊(x₀)) ∩ φ⁻¹ D₊(y₀)`, where `D₊(x₀) ⊆ ℙʳ_S` is the preimage of
  the standard open `D₊(T₀)` of the integral model `Proj ℤ[T₀, …, T_r]`. This is the locus where
  the section `x₀ x₀' y₀` does not vanish.
* `x₀^{δ₁}` and `x₀'^{δ₂}` are the global sections of `𝒪(δ₁)` and `𝒪(δ₂)` pulled back from
  `ProjectiveSpectrum.Proj.degreeSection` of the monomial `T₀^δ`, as in
  `Faltings.IsVojtaRepresentative`. `y₀^{-d}` is the section `(T₀ / 1)^{-d}` of `𝒪(-d)` over
  `D₊(T₀)` given by `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioSection`, pulled back along
  `φ`; recall that `𝒪(V)` is written with `φ^*𝒪(-d)` in place of `φ^*𝒪(d)⁻¹`.
* The product `x₀^{δ₁} x₀'^{δ₂} ⊗ y₀^{-d}` is formed on the open subscheme `U`, where all three
  factors are global sections, and carried into `ι^*𝒪(V)` by the comparison
  `Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso` for the inclusion `ι : U ⟶ X`.
* The coefficient `g_U` is chosen among the `f ∈ Γ(U, 𝒪_U)` with `f • e = s|_U`; such an `f`
  exists and is unique because `e` generates `𝒪(V)` freely on `U`. When `U` is empty, or no such
  `f` exists, the value is `0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

/-- Bombieri's rational function `g = s / (x₀^{δ₁} x₀'^{δ₂} / y₀^d)` for a global section `s` of
`𝒪(V) = Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d` on an integral scheme `X`: on the open set `U` where
`x₀`, `x₀'` and `y₀` do not vanish, `s|_U = g_U • e` with `e = x₀^{δ₁} x₀'^{δ₂} y₀^{-d}`, and `g`
is the image of `g_U` in the function field of `X`. -/
@[expose, faltings "def_bvr_function_g"]
public noncomputable def vojtaSectionRatio {S X : Scheme.{u}} [IsIntegral X] {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) : X.functionField :=
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let 𝒜 : ∀ r : ℕ, ℕ → Submodule (ULift.{u} ℤ) (MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun r => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
  let g : ∀ r : ℕ, projectiveSpaceOver r S ⟶ projectiveSpaceAtUniverse.{u} r := fun r =>
    projectiveSpaceOver.toIntegralAtUniverse r S
  let T : ∀ r : ℕ, ℤ → (projectiveSpaceAtUniverse.{u} r).Modules := fun r a =>
    ProjectiveSpectrum.Proj.twistingSheaf (𝒜 r) a
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (g r)).obj (T r a)
  -- sections over an open, pulled back along a morphism
  let pull : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Modules) (V : Z.Opens),
      Γ(F, V) ⟶ Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ V) := fun f F V =>
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V
  -- the product of two global sections
  let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
    fun {Y} {_ _} a b =>
      let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
      eY _ ((λ_ (𝟙_ Y.Modules)).inv ≫ ((eY _).symm a ⊗ₘ (eY _).symm b))
  -- the section `x^a` of `𝒪(a)` on `ℙʳ_S` given by the monomial `x₀^a`
  let x₀pow : ∀ (r a : ℕ), Γ(twist r a, ⊤) := fun r a =>
    pullbackGlobalSections (g r) (T r a)
      (ProjectiveSpectrum.Proj.degreeSection (𝒜 r) a
        ⟨MvPolynomial.X 0 ^ a, MvPolynomial.isHomogeneous_X_pow 0 a⟩)
  -- the standard open `D₊(x₀)` of `ℙʳ_S`
  let D₀ : ∀ r : ℕ, (projectiveSpaceAtUniverse.{u} r).Opens := fun r =>
    ProjectiveSpectrum.basicOpen (𝒜 r) (MvPolynomial.X 0)
  let D : ∀ r : ℕ, (projectiveSpaceOver r S).Opens := fun r => g r ⁻¹ᵁ D₀ r
  let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
  let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
  let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
  let M : X.Modules := (Scheme.Modules.pullback φ).obj (twist m (-(d : ℤ)))
  -- the open set `D(x₀ x₀' y₀)` of `X` and its inclusion
  let U : X.Opens := ψ ⁻¹ᵁ (p₁ ⁻¹ᵁ D n ⊓ p₂ ⁻¹ᵁ D n) ⊓ φ ⁻¹ᵁ D m
  let ι : (U : Scheme.{u}) ⟶ X := U.ι
  -- `y₀^{-d}`, a section of `𝒪(-d)` over `D₊(y₀)`
  let yinv₀ : Γ(T m (-(d : ℤ)), D₀ m) :=
    Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioSection (𝒜 m) (p := MvPolynomial.X 0)
      (q := 1) (e := 0) (d := 1) (n := -(d : ℤ)) (c := -(d : ℤ))
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _))
      (SetLike.one_mem_graded _) (by simp) (W := D₀ m) (by rw [mul_one]; exact le_rfl)
  -- `y₀^{-d}` restricted to `U`, as a global section of `ι^* φ^* 𝒪(-d)`
  let yinv : Γ((Scheme.Modules.pullback ι).obj M, ⊤) :=
    ((Scheme.Modules.pullback ι).obj M).presheaf.map
      (homOfLE (fun x _ => x.2.2) : (⊤ : (U : Scheme.{u}).Opens) ⟶ ι ⁻¹ᵁ φ ⁻¹ᵁ D m).op
      (pull ι M _ (pull φ (twist m (-(d : ℤ))) (D m) (pull (g m) (T m (-(d : ℤ))) (D₀ m) yinv₀)))
  -- `x₀^{δ₁} x₀'^{δ₂}` restricted to `U`
  let xpow : Γ((Scheme.Modules.pullback ι).obj L, ⊤) :=
    pullbackGlobalSections ι L (pullbackGlobalSections ψ (O₁ ⊗ O₂)
      (tensorSec (pullbackGlobalSections p₁ _ (x₀pow n δ₁))
        (pullbackGlobalSections p₂ _ (x₀pow n δ₂))))
  -- the generator `e = x₀^{δ₁} x₀'^{δ₂} y₀^{-d}` of `𝒪(V)` on `U`
  let e : Γ((Scheme.Modules.pullback ι).obj (vojtaLineBundle ψ φ δ₁ δ₂ d), ⊤) :=
    let eU := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv (U : Scheme.{u})
    eU _ ((eU _).symm (tensorSec xpow yinv) ≫
      (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι L M).inv)
  let sU : Γ((Scheme.Modules.pullback ι).obj (vojtaLineBundle ψ φ δ₁ δ₂ d), ⊤) :=
    pullbackGlobalSections ι _ s
  letI := Classical.propDecidable
  if hU : Nonempty U then
    haveI := hU
    X.germToFunctionField U (U.topIso.hom
      (if h : ∃ f : Γ((U : Scheme.{u}), ⊤), f • e = sU then h.choose else 0))
  else 0

end Faltings
