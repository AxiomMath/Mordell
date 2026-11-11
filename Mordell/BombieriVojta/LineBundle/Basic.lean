module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The line bundle `𝒪(V)` of the Vojta divisor

In Section 6 of Bombieri's proof of the Mordell conjecture, `C` is a curve over a number field `k`,
`ψ = φ_{NP} × φ_{NP} : C × C → ℙⁿ × ℙⁿ` is the product of the embedding given by a basis of
`H⁰(C, 𝒪(NP))`, `φ_B : C × C → ℙᵐ` is the embedding given by a basis of `H⁰(C × C, 𝒪(B))`, and
`δ₁, δ₂, d` are integers. The invertible sheaf
`𝒪(V) = ψ^* 𝒪_{ℙⁿ × ℙⁿ}(δ₁, δ₂) ⊗ φ_B^* 𝒪_{ℙᵐ}(d)⁻¹` on `C × C` is the sheaf whose sections
are represented by bihomogeneous forms of bidegree `(δ₁, δ₂)` divided by `y_i^d`.

The construction only uses the two morphisms and the three integers, so it is made for an
arbitrary scheme `X` over an arbitrary base `S`, with morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and
`φ : X ⟶ ℙᵐ_S`.

## Main definitions

* `Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d`: the `𝒪_X`-module
  `ψ^*(pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂)) ⊗ φ^*𝒪(-d)`.

## Implementation notes

* `𝒪_{ℙʳ_S}(a)` is the pullback along `ℙʳ_S ⟶ ℙʳ_ℤ` of the twisting sheaf
  `ProjectiveSpectrum.Proj.twistingSheaf` of degree `a` on `Proj ℤ[T₀, …, T_r]`, the same
  convention as `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf` (the case `a = 1`).
* `𝒪_{ℙⁿ × ℙⁿ}(δ₁, δ₂)` is `pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂)` on the fibre product `ℙⁿ_S ×_S ℙⁿ_S`.
* The factor `φ^*𝒪(d)⁻¹` is written `φ^*𝒪(-d)`. On projective space `𝒪(-d)` is the tensor
  inverse of `𝒪(d)`, and pullback is monoidal, so the two sheaves are canonically isomorphic;
  this form avoids carrying the invertibility of `φ^*𝒪(d)` as an instance argument.
* Tensor products are taken in `Stacks.SheafInternalHom.schemeMonoidalCategory`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

/-- The invertible sheaf `𝒪(V) = ψ^*𝒪_{ℙⁿ × ℙⁿ}(δ₁, δ₂) ⊗ φ^*𝒪_{ℙᵐ}(d)⁻¹` of Bombieri's
Section 6, for morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`. Here
`𝒪(δ₁, δ₂) = pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂)` and the inverse of `φ^*𝒪(d)` is written `φ^*𝒪(-d)`. -/
@[expose, faltings "def_bv_line_bundle_vojta"]
public noncomputable def vojtaLineBundle {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) : X.Modules :=
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse r S)).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a)
  (Scheme.Modules.pullback ψ).obj
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj (twist n δ₁) ⊗
        (Scheme.Modules.pullback (pullback.snd _ _)).obj (twist n δ₂)) ⊗
    (Scheme.Modules.pullback φ).obj (twist m (-d))

end Faltings
