module
public import Mordell.BombieriVojta.LineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme

/-!
# The functions `G_{ijj'}`

In Section 6 of Bombieri's proof of the Mordell conjecture, `ψ = φ_{NP} × φ_{NP} : C × C → ℙⁿ × ℙⁿ`
has coordinates `(x, x') = (x₀, …, xₙ, x'₀, …, x'ₙ)`, `φ_B : C × C → ℙᵐ` has coordinates
`y₀, …, yₘ`, and `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` (`Faltings.vojtaLineBundle`). For indices
`i, j, j'` the quotient `e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` is a section of `𝒪(V)` on the
open set `U_{ijj'}` where `y_i`, `x_j ∘ pr₁` and `x'_{j'} ∘ pr₂` do not vanish, and for a global
section `s` of `𝒪(V)` the function `G_{ijj'} = s / e_{ijj'}` is the coordinate of `s` in that
frame, a rational function on `C × C`. A non-vanishing triple at a point `(z, w)` is exactly a
triple for which `(z, w) ∈ U_{ijj'}`.

## Main definitions

* `Faltings.BombieriVojta.tripleFunction`: the rational function `G_{ijj'} = s / e_{ijj'}`.

## Implementation notes

* As for `Faltings.vojtaLineBundle`, `C × C` is an arbitrary scheme `X` over an arbitrary base `S`,
  with morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`; the coordinates `x_j`, `x'_{j'}`,
  `y_i` are the pullbacks of the coordinate sections `T_k` of `𝒪(1)` along
  `ψ ≫ pr₁`, `ψ ≫ pr₂` and `φ`.
* `x_j^{δ₁}` is the pullback of the section `T_j ^ δ₁` of `𝒪(δ₁)` on the standard chart
  `D₊(T_j)` (`Stacks.PicardUFD.twistChartGenerator`), and dividing by `y_i^d` is tensoring with
  the section `T_i ^ (-d)` of `𝒪(-d)` on `D₊(T_i)`, the factor `φ^*𝒪(d)⁻¹` of `𝒪(V)` being
  written `φ^*𝒪(-d)`. Products of sections are `Stacks.SectionTensorFormula.tensorSection`.
* The quotient `s / e` is the preimage of `s|_U` under `g ↦ g • e` on `Γ(X, U)`, read in the
  function field by `AlgebraicGeometry.Scheme.germToFunctionField`. Since `e` generates `𝒪(V)` on
  `U`, this preimage is unique; the definition uses `Function.invFun`, so that it needs no proof
  of that fact.
* The point `(z, w)` is a point `x` of the scheme `X`, and the non-vanishing of `y_i`, `x_j`,
  `x'_{j'}` at it is the membership of `x` in the three inverse images of standard charts. It
  makes `U` non-empty, which is what the passage to the function field needs.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

namespace Faltings.BombieriVojta

universe u

/-- The rational function `G_{ijj'} = s / e_{ijj'}` on `X` (Bombieri's `C × C`), for a global
section `s` of `𝒪(V) = vojtaLineBundle ψ φ δ₁ δ₂ d` and a triple `(i, j, j')` that is non-vanishing
at the point `x`. Here `e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` is the section of `𝒪(V)` on
`U = ψ⁻¹(pr₁⁻¹ D₊(T_j) ∩ pr₂⁻¹ D₊(T_{j'})) ∩ φ⁻¹ D₊(T_i)` built from the coordinate sections of
the twisting sheaves, and `G_{ijj'}` is the image in the function field of the function `g` on `U`
with `s|_U = g • e_{ijj'}`. -/
@[expose, faltings "def_bv_triple_function"]
public noncomputable def tripleFunction {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) (x : X) (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (hx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j'))) :
    X.functionField :=
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory
  letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let chart : ∀ (r : ℕ) (k : Fin (r + 1)), (projectiveSpaceOver r S).Opens := fun r k =>
    projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse r S)).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a)
  let pb : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) (T : Z.Opens),
      Γ(M, T) → Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ T) := fun f M T t =>
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app T t
  let gen : ∀ (r : ℕ) (a : ℤ) (k : Fin (r + 1)), Γ(twist r a, chart r k) := fun r a k =>
    pb _ _ _ (Stacks.PicardUFD.twistChartGenerator (ULift.{u} ℤ) a k).val
  let res : ∀ {Y : Scheme.{u}} (M : Y.Modules) {T T' : Y.Opens}, T' ≤ T → Γ(M, T) → Γ(M, T') :=
    fun M _ _ h t => M.presheaf.map (homOfLE h).op t
  let fst := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let snd := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let W := fst ⁻¹ᵁ chart n j ⊓ snd ⁻¹ᵁ chart n j'
  let a := Stacks.SectionTensorFormula.tensorSection _ _
    (res _ inf_le_left (pb fst _ _ (gen n δ₁ j)))
    (res _ inf_le_right (pb snd _ _ (gen n δ₂ j')))
  let U := ψ ⁻¹ᵁ W ⊓ φ ⁻¹ᵁ chart m i
  let e : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, U) := Stacks.SectionTensorFormula.tensorSection _ _
    (res _ inf_le_left (pb ψ _ _ a)) (res _ inf_le_right (pb φ _ _ (gen m (-d) i)))
  haveI : Nonempty U := ⟨⟨x, ⟨hx.2.1, hx.2.2⟩, hx.1⟩⟩
  X.germToFunctionField U
    (Function.invFun (fun g : Γ(X, U) => g • e) (res _ le_top s))

end Faltings.BombieriVojta
