module

public import Mordell.Height.Class.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety

/-!
# The Weil height is a height for the hyperplane class

On projective space `ℙⁿ_k` over a field `k` algebraic over `ℚ` (in the source, `k = ℚ̄`), the
absolute logarithmic Weil height `h` is a height associated to the class `c = [𝒪(1)]` of the
hyperplane sheaf: `h_c = h + O(1)`.

The proof is the case `φ = 𝟙` of a more general fact: the height `h_φ` relative to a
projective embedding `φ` is a height for the class `cl(φ) ⊗ 1` (take `m = 1`, `γ = [φ]` and
bound `0`). The identity of `ℙⁿ_k` is a projective embedding, its class is `[𝒪(1)]` (the
pullback of a sheaf along the identity is the sheaf itself), and the height relative to it is
the Weil height.

## Main results

* `Faltings.isHeightOfClass_weilHeight_projectiveSpaceOver`: the Weil height, read on the
  `k`-points of `ℙⁿ_k`, is a height associated to `[𝒪(1)] ⊗ 1 ∈ Pic(ℙⁿ_k) ⊗ ℚ`.

## Implementation notes

`ℙⁿ_k` is `AlgebraicGeometry.projectiveSpaceOver n (Spec k)`, with its structure morphism; it
is smooth (`AlgebraicGeometry.projectiveSpaceOver.smooth`) and a projective variety, the latter
assembled from `AlgebraicGeometry.projectiveSpaceOverRing.isVariety` and
`AlgebraicGeometry.isProjectiveMorphism_projectiveSpaceOver`. The hyperplane sheaf is
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec k) 1`, and its class is
`Scheme.picardClass`. A `k`-point `p` (a section of the structure morphism) is read as a point
of `ℙ k (Fin (n + 1) → k)` by the dictionary used for `Faltings.ProjectiveEmbedding.height`:
the standard-basis isomorphism `AlgebraicGeometry.projectiveSpaceOfModuleIso`, the
identification of `k`-points of `𝐏(V)` with lines of functionals on `V`, and the dual basis.
The base field is an algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`.

## References

* [Z. Gao, *Heights*][gao2022], Prop. 5.1.3.
* [Hindry, Silverman, *Diophantine Geometry*, Thm. B.3.2(a)][hindrysilverman2000]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

/-- **The Weil height is a height for `[𝒪(1)]`.** On `ℙⁿ_k`, `k / ℚ` algebraic, the function
sending a `k`-point `p` to the absolute logarithmic Weil height `Faltings.weilHeight` of its
homogeneous coordinates is a height associated to the class `[𝒪(1)] ⊗ 1` of the hyperplane
sheaf, in the sense of `Faltings.IsHeightOfClass`; that is, `h_{[𝒪(1)]} = h + O(1)`. -/
@[faltings "lem_ht_height_class_projective_space"]
public theorem isHeightOfClass_weilHeight_projectiveSpaceOver {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (n : ℕ) :
    haveI : IsProjectiveVariety k (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) :=
      { toIsVariety := projectiveSpaceOverRing.isVariety k n
        isProjective := isProjectiveMorphism_projectiveSpaceOver n _ }
    IsHeightOfClass (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      ((projectiveSpaceOver n (Spec (.of k))).picardClass
          (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1)
          (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1)
        ⊗ₜ[ℤ] (1 : ℚ))
      (fun p => weilHeight
        ((ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
          (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _
            ⟨p.1 ≫ (projectiveSpaceOfModuleIso (Pi.basisFun k (Fin (n + 1)))).inv, by
              rw [Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec, p.2]⟩)).map
          (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.toLinearMap
          (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.injective)) := by
  haveI : IsProjectiveVariety k (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) :=
    { toIsVariety := projectiveSpaceOverRing.isVariety k n
      isProjective := isProjectiveMorphism_projectiveSpaceOver n _ }
  let φ : ProjectiveEmbedding (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) n :=
    ⟨𝟙 _, inferInstance, Category.id_comp _⟩
  convert isHeightOfClass_height φ using 1
  · rw [embeddingClass_apply_of]
    exact congrArg (· ⊗ₜ[ℤ] (1 : ℚ)) (Stacks.SheafOfModules.pullbackPicardClass_id _ _).symm
  · funext p
    simp [φ, ProjectiveEmbedding.height]

end Faltings
