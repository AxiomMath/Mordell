module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Embedding
public import Mordell.Height.Weil.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.RelativeLinearAction
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import Mordell.Height.Machine.EmbeddingGroup

/-!
# The height relative to a projective embedding

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`) and `φ : X ⟶ ℙⁿ_k` a projective embedding. The height of a `k`-point `p` of `X`
relative to `φ` is the absolute logarithmic Weil height of its image:
`h_φ(p) = h(φ(p))`.

## Main definitions

* `Faltings.ProjectiveEmbedding.height`: the height `h_φ(p) = h(φ(p))` of a `k`-point `p` of `X`.

## Implementation notes

A `k`-point of `X` is a section `p : Spec k ⟶ X` of the structure morphism `f`. Its image
`φ ∘ p` is a `k`-point of the scheme `ℙⁿ_k`, which is read as a point of
`ℙ k (Fin (n + 1) → k)` through the standard dictionary: the coordinate isomorphism
`𝐏(kⁿ⁺¹) = Proj (Sym_k kⁿ⁺¹) ≅ ℙⁿ_k` given by the standard basis
(`AlgebraicGeometry.projectiveSpaceOfModuleIso`), the identification of `k`-points of
`𝐏(V)` with one-dimensional quotients of `V`, that is with lines of functionals on `V`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual`), and the
dual-basis identification of a functional `ψ` with its coordinate vector `(ψ(e_j))_j`. The
homogeneous coordinates of `φ(p)` are thus the values at `φ(p)` of the coordinate forms
`T_0, …, T_n`, as in the source.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

/-- The point `φ(p) ∈ ℙⁿ(k)` of a `k`-point `p` of `X` under a projective embedding
`φ : X ⟶ ℙⁿ_k`: the `k`-point `φ ∘ p` of `ℙⁿ_k`, read as a point of `ℙ k (Fin (n + 1) → k)` whose
homogeneous coordinates are the values at `φ(p)` of the coordinate forms `T_0, …, T_n`. -/
public noncomputable def ProjectiveEmbedding.toPoint {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] {n : ℕ} (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) : ℙ k (Fin (n + 1) → k) :=
  let b := Pi.basisFun k (Fin (n + 1))
  let q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (n + 1) → k) :=
    p.1 ≫ φ.hom ≫ (projectiveSpaceOfModuleIso b).inv
  have hq : q ≫ projectiveSpaceOfModuleToSpec k (Fin (n + 1) → k) = 𝟙 _ := by
    simp only [q, Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
    rw [φ.hom_over, p.2]
  let ψ : ℙ k (Module.Dual k (Fin (n + 1) → k)) :=
    ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
      (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ ⟨q, hq⟩)
  ψ.map b.toDualEquiv.symm.toLinearMap b.toDualEquiv.symm.injective

/-- A closed immersion is a monomorphism, so distinct `k`-points have distinct images. -/
public theorem ProjectiveEmbedding.toPoint_injective {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] {n : ℕ} (φ : ProjectiveEmbedding f n) :
    Function.Injective φ.toPoint := by
  have := φ.isClosedImmersion
  intro p₁ p₂ h
  have h1 := Projectivization.map_injective _
    (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.injective h
  have h2 := congrArg Subtype.val
    ((ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _).injective
      ((ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _).injective h1))
  exact Subtype.ext ((cancel_mono φ.hom).1
    ((cancel_mono _).1 (by simpa only [Category.assoc] using h2)))

/-- The **height relative to a projective embedding** `φ : X ⟶ ℙⁿ_k` of a `k`-point `p` of a
smooth projective variety `X` over `k / ℚ` algebraic: `h_φ(p) = h(φ(p))`, the absolute
logarithmic Weil height `Faltings.weilHeight` of the image point `φ(p) ∈ ℙⁿ(k)`, whose
homogeneous coordinates are the values at `φ(p)` of the coordinate forms `T_0, …, T_n`. -/
@[faltings "def_ht_height_embedding"]
public noncomputable def ProjectiveEmbedding.height {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {n : ℕ} (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) : ℝ :=
  let b := Pi.basisFun k (Fin (n + 1))
  let q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (n + 1) → k) :=
    p.1 ≫ φ.hom ≫ (projectiveSpaceOfModuleIso b).inv
  have hq : q ≫ projectiveSpaceOfModuleToSpec k (Fin (n + 1) → k) = 𝟙 _ := by
    simp only [q, Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
    rw [φ.hom_over, p.2]
  let ψ : ℙ k (Module.Dual k (Fin (n + 1) → k)) :=
    ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
      (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ ⟨q, hq⟩)
  weilHeight (ψ.map b.toDualEquiv.symm.toLinearMap b.toDualEquiv.symm.injective)

/-- The height `h_φ(p)` is the Weil height of the image point `φ.toPoint p`. -/
public theorem ProjectiveEmbedding.height_def {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {n : ℕ} (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) : φ.height p = weilHeight (φ.toPoint p) :=
  rfl

end Faltings


/-!
# The height relative to an element of `Emb(X)`

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), with structure morphism `f : X ⟶ Spec k`. Each projective embedding `φ` of `X`
gives a height function `h_φ : X(k) → ℝ`. The map `γ ↦ h_γ` on the free abelian group
`Emb(X)` of formal combinations of projective embeddings is the `ℤ`-linear extension of
`φ ↦ h_φ`: for `γ = ∑ nᵢ φᵢ`, `h_γ = ∑ nᵢ h_{φᵢ}`.

## Main definitions

* `Faltings.EmbeddingGroup.height`: the additive homomorphism `γ ↦ h_γ` from `Emb(X)` to
  the real-valued functions on `X(k)`.

## Implementation notes

The extension is `FreeAbelianGroup.lift` of `⟨n, φ⟩ ↦ h_φ`, so it is bundled as an
`AddMonoidHom` and is characterised by `FreeAbelianGroup.lift_apply_of`: on a generator
`FreeAbelianGroup.of ⟨n, φ⟩` it is `Faltings.ProjectiveEmbedding.height φ`. A `k`-point of `X`
is a section of `f`. The base field is an algebraic extension `k / ℚ`; the source's case is
`k = ℚ̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Faltings

/-- The **height relative to an element `γ` of `Emb(X)`**: the `ℤ`-linear extension
`γ ↦ h_γ` of `φ ↦ h_φ = Faltings.ProjectiveEmbedding.height φ` to the free abelian group
`Faltings.EmbeddingGroup f` of projective embeddings, so that `h_{∑ nᵢ φᵢ} = ∑ nᵢ h_{φᵢ}`
as functions on the `k`-points (sections of `f`) of `X`. -/
@[faltings "def_ht_height_emb_combination"]
public noncomputable def EmbeddingGroup.height {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [Smooth f] :
    EmbeddingGroup f →+ ({p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ) :=
  FreeAbelianGroup.lift fun e => e.2.height

end Faltings
