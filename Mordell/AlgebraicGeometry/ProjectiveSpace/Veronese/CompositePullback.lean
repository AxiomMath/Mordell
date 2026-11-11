module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.Pullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections

/-!
# Pullback of `𝒪(1)` under a Veronese composite

Let `S` be a scheme, `X` a scheme, `φ : X ⟶ ℙⁿ_S` a morphism and `e ≥ 1`. Let
`Φ_e : ℙⁿ ⟶ ℙᴺ` be the Veronese morphism of degree `e`, whose homogeneous coordinates `y_J` are
the monomials `x^J` of degree `e` (so `N + 1 = binom (n + e) n`). The Veronese composite
`φ^{(e)} = Φ_e ∘ φ` pulls the hyperplane sheaf back to the `e`-th tensor power of `φ^* 𝒪(1)`:
`(φ^{(e)})^* 𝒪(1) ≅ (φ^* 𝒪(1))^{⊗ e}`. This is `Φ_e^* 𝒪(1) ≅ 𝒪(e)`
(`Faltings.nonempty_pullback_veronese_twistingSheafAtUniverse_iso`) pulled back along `φ`.

## Main results

* `Faltings.nonempty_pullback_veronese_projectiveSpaceTwistingSheaf_iso`:
  `(φ^{(e)})^* 𝒪(1) ≅ (φ^* 𝒪(1))^{⊗ e}` as modules on `X`.

## Implementation notes

Projective space over `S` is `AlgebraicGeometry.projectiveSpaceOver n S`, the base change of the
integral model `AlgebraicGeometry.projectiveSpaceAtUniverse n = Proj ℤ[x₀, …, xₙ]`, and its
hyperplane sheaf `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf` is the pullback
of `𝒪(1)` from the integral model. The Veronese morphism `V` is a morphism of integral models,
pinned, as in `Faltings.ProjectiveEmbedding.exists_veronese`, by its charts: for an ordering
`σ` of the monomials of degree `e`, `V` maps `D₊(x_i)` into `D₊(y_{σ (e • eᵢ)})` and pulls
`y_{σ J} / y_{σ (e • eᵢ)}` back to `x^J / x_i ^ e`. These conditions determine `V`. The Veronese
composite of `φ` is any `ψ : X ⟶ ℙᴺ_S` whose composite with the projection to the integral model
is `φ` followed by the projection and `V`. The hyperplane sheaf is pulled back from the integral
model, so the conclusion does not need `ψ` to lie over `S`. The tensor power is
`Stacks.Ample.tensorPowModule`, the tensor power of an invertible module used by
`Faltings.eventually_isVeryAmple_tensorModules_tensorPowModule`. The source works over `Q̄`
with `X` a projective variety; the statement holds over any base scheme `S` and for any `X`.

## References

* [Hartshorne, *Algebraic Geometry*, II Ex. 5.13][hartshorne1977]
* [Gao, *An Introduction to Diophantine Geometry*, proof of Prop. 5.1.3(iii)][gao2022]
-/

open AlgebraicGeometry CategoryTheory MvPolynomial Stacks.AmpleProjectiveImmersion
open Stacks.SectionsToProjectiveSpace Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

universe u

namespace Faltings

/-- **Pullback of `𝒪(1)` under a Veronese composite.** Let `V : ℙⁿ ⟶ ℙᴺ` be the Veronese
morphism of degree `e`, whose coordinates are the monomials of degree `e` ordered by `σ`, given on
the charts `D₊(x_i)` by `y_{σ J} / y_{σ (e • eᵢ)} ↦ x^J / x_i ^ e`. If `ψ : X ⟶ ℙᴺ_S` is the
Veronese composite of `φ : X ⟶ ℙⁿ_S`, that is, `φ` followed by `V`, then
`ψ^* 𝒪(1) ≅ (φ^* 𝒪(1))^{⊗ e}`. -/
@[faltings "lem_ht_veronese_embedding_pullback"]
public theorem nonempty_pullback_veronese_projectiveSpaceTwistingSheaf_iso
    {S X : Scheme.{u}} {n : ℕ} (e : ℕ) (he : 1 ≤ e) (N : ℕ)
    (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = e} ≃ Fin (N + 1))
    (V : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hV : ∀ i : Fin (n + 1),
      ∃ g : Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))) ⟶
          Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)))),
        g ≫ Proj.awayι (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) one_pos =
          Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) one_pos ≫ V ∧
        ∀ J : {I : Fin (n + 1) →₀ ℕ // I.degree = e},
          g.appTop ((Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) 1
                (MvPolynomial.X (σ J))
                ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))) =
            (Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) e (monomial J.1 1)
                ((mem_homogeneousSubmodule _ _).2
                  (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2)))))
    (φ : X ⟶ projectiveSpaceOver n S) (ψ : X ⟶ projectiveSpaceOver N S)
    (hψ : ψ ≫ projectiveSpaceOver.toIntegralAtUniverse N S =
      φ ≫ projectiveSpaceOver.toIntegralAtUniverse n S ≫ V) :
    Nonempty ((Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf N S) ≅
      Stacks.Ample.tensorPowModule X
        ((Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n S)) e) := by
  obtain ⟨c⟩ := nonempty_pullback_veronese_twistingSheafAtUniverse_iso e he N σ V hV
  exact ⟨(Scheme.Modules.pullbackComp ψ (projectiveSpaceOver.toIntegralAtUniverse N S)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hψ).app _ ≪≫
    ((Scheme.Modules.pullbackComp φ
      (projectiveSpaceOver.toIntegralAtUniverse n S ≫ V)).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (((Scheme.Modules.pullbackComp (projectiveSpaceOver.toIntegralAtUniverse n S) V).app
        _).symm ≪≫
      (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).mapIso c ≪≫
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso n S
        (e : ℤ)).symm) ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso φ (projectiveSpaceTwistingSheaf n S) e⟩

end Faltings
