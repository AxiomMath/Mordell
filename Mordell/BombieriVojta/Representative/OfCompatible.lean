module
public import Mordell.BombieriVojta.Representative.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule
public import Mordell.BombieriVojta.Representative.BasicSystem

/-!
# Compatible forms define a section of `𝒪(V)`

In Section 6 of Bombieri's proof of the Mordell conjecture, `ψ : C × C → ℙⁿ × ℙⁿ` and
`φ_B : C × C → ℙᵐ` are projective embeddings with homogeneous coordinates `(x, x')` and `y`, and
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. Conversely to the existence of representatives, let
`F_0, …, F_m` be bihomogeneous forms of bidegree `(δ₁, δ₂)` such that
`F_i · y_j^d = F_j · y_i^d` in `H⁰(C × C, ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d))` for all `i, j`. Then the
local sections `F_i / y_i^d` on the opens `{y_i ≠ 0}` glue, and there is exactly one global section
`s` of `𝒪(V)` of which `(F_i)` is a representative.

The proof separates the monoidal content from the geometry. In a closed monoidal abelian
category, let `N` have a two-sided tensor inverse `M`, with `μ : M ⊗ N ≅ Z`, and let
`y_i : 𝟙 ⟶ N` be jointly epimorphic. Compatible `F_i : 𝟙 ⟶ L` descend along the epimorphism
`⨁ 𝟙 ⟶ N` to `f : N ⟶ L` with `y_i ≫ f = F_i`: the descent vanishes on the kernel because
`− ⊗ N` is faithful and the `K ◁ y_j` are jointly epimorphic (`− ⊗ −` has a right adjoint). Since
`− ⊗ N` is an equivalence, `f` corresponds to a unique `s : 𝟙 ⟶ L ⊗ M`. On `X`, the sections
`y_i^d` of `φ^*𝒪(d)` are jointly epimorphic because their nonvanishing loci, the preimages of the
`D₊(T_i^d)`, cover `X`, and on a trivialising open where `y_i^d` does not vanish every local
section is a multiple of it; the multiplication `𝒪(-d) ⊗ 𝒪(d) ⟶ 𝒪(0) ≅ 𝒪` is an isomorphism.

## Main results

* `Faltings.existsUnique_isVojtaRepresentative`: a family of bihomogeneous forms of bidegree
  `(δ₁, δ₂)` satisfying `F_i y_j^d = F_j y_i^d` is a representative of a unique global section
  of `Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d`.

## Implementation notes

* As for `Faltings.vojtaLineBundle` and `Faltings.IsVojtaRepresentative`, the statement is made
  for an arbitrary scheme `X` over an arbitrary base `S`, with morphisms
  `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`, and for all `δ₁, δ₂, d ≥ 0`. The gluing argument
  only uses that the opens `φ⁻¹ D₊(y_i)` cover `X` and that `y_i^d` generates `φ^*𝒪(d)` on
  `φ⁻¹ D₊(y_i)`, which hold for every morphism to `ℙᵐ_S`.
* The restriction `F|_X` of a form and the sections `y_i^d|_X` are those of
  `Faltings.IsVojtaRepresentative`, and the product `F_i|_X · y_j^d|_X` is taken in
  `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(d)` through the identification
  `Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv` of global sections with morphisms out
  of the monoidal unit.
* The gluing itself is `Faltings.existsUnique_isVojtaRepresentative_of_compatible`, stated with
  the named restrictions `Faltings.vojtaFormRestriction`, `Faltings.vojtaCoordinatePow` and the
  products `Stacks.ProductFamilyTwist.prodSection`; the hypothesis here is rewritten into that form.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

/-- Let `F_0, …, F_m` be bihomogeneous forms of bidegree `(δ₁, δ₂)` in `x_ν = Sum.inl ν` and
`x'_ν = Sum.inr ν` with `F_i|_X · y_j^d = F_j|_X · y_i^d` in `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(d)` for all
`i, j`, where `y_0, …, y_m` are the homogeneous coordinates of `ℙᵐ_S`. Then there is a unique
global section `s` of `vojtaLineBundle ψ φ δ₁ δ₂ d` such that `(F_i)` is a representative of `s`
in the sense of `IsVojtaRepresentative`. -/
@[faltings "lem_bv_section_from_forms"]
public theorem existsUnique_isVojtaRepresentative {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    (hFy :
      letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      letI : ∀ r : ℕ,
          GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
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
      let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
      let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
      let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
      let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
      let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
      let N : X.Modules := (Scheme.Modules.pullback φ).obj (twist m d)
      -- the product of two global sections
      let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
        fun {Y} {_ _} a b =>
          let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
          eY _ ((λ_ (𝟙_ Y.Modules)).inv ≫ ((eY _).symm a ⊗ₘ (eY _).symm b))
      -- `y_i^d` restricted to `X`
      let y : Fin (m + 1) → Γ(N, ⊤) := fun i =>
        pullbackGlobalSections φ (twist m d)
          (form m d ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)
      -- the restriction of a bihomogeneous form of bidegree `(δ₁, δ₂)` to `X`
      let σ : X ⟶ S := ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)
      let mono : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(L, ⊤) := fun α =>
        if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
            (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
          pullbackGlobalSections ψ (O₁ ⊗ O₂) (tensorSec
            (pullbackGlobalSections p₁ (twist n δ₁)
              (form n δ₁
                ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
                MvPolynomial.isHomogeneous_monomial _ h.1⟩))
            (pullbackGlobalSections p₂ (twist n δ₂)
              (form n δ₂
                ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
                MvPolynomial.isHomogeneous_monomial _ h.2⟩)))
        else 0
      let restrict : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤) → Γ(L, ⊤) := fun P =>
        ∑ α ∈ P.support, σ.appTop (P.coeff α) • mono α
      ∀ i j, tensorSec (restrict (F i)) (y j) = tensorSec (restrict (F j)) (y i)) :
    ∃! s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤), IsVojtaRepresentative ψ φ δ₁ δ₂ d s F := by
  refine existsUnique_isVojtaRepresentative_of_compatible ψ φ δ₁ δ₂ d F hF fun i j => ?_
  have h := hFy i j
  simp only [vojtaFormRestriction, vojtaCoordinatePow, AddMonoidHom.comp_apply,
    Finsupp.liftAddHom_apply, prodSection_eq_leftUnitor_inv_tensorHom]
  exact h

end Faltings
