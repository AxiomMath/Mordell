module

public import Mathlib
public import Mordell.Height.Machine.EmbeddingGroup
public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.ProductEmbedding
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.ProductPullback
public import Mordell.Height.Weil.Segre
public import Mordell.Height.Weil.ZeroCoordinates
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates

/-!
# An embedding realizing a positive combination of embeddings

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), with structure morphism `f : X ⟶ Spec k`. If `γ = ∑ nᵢ φᵢ ∈ Emb(X)` is a nonempty
combination of projective embeddings `φᵢ` with positive coefficients `nᵢ`, then there is a single
projective embedding `Φ_γ` of `X` with the same height, `h_{Φ_γ} = h_γ`, and the same class,
`cl(Φ_γ) = cl(γ)`.

The embedding is an iterated Segre product. For projective embeddings `Φ₁ : X ⟶ ℙʳ_k` and
`Φ₂ : X ⟶ ℙᵐ_k`, the Segre product `Φ₁ ⊗ Φ₂` is a projective embedding
(`Faltings.ProjectiveEmbedding.exists_hom_eq_segreProduct`), its class is
`cl(Φ₁) + cl(Φ₂)` because `(Φ₁ ⊗ Φ₂)^* 𝒪(1) ≅ Φ₁^* 𝒪(1) ⊗ Φ₂^* 𝒪(1)`
(`Faltings.nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso`), and its height is
`h_{Φ₁} + h_{Φ₂}` (`Faltings.weilHeight_segreMap`). For the last point the homogeneous
coordinates of `(Φ₁ ⊗ Φ₂)(p)` are computed: on the chart `D₊(Z_{ij})` the affine coordinate
`Z_{ab} / Z_{ij}` pulls back along the Segre morphism to the ratio of the sections `X_a Y_b` and
`X_i Y_j` of `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`, which is the product of the ratios `X_a / X_i` and
`Y_b / Y_j`. Repeating each `φᵢ` exactly `nᵢ` times in the list of factors gives `Φ_γ`.

## Main definitions

* `Faltings.kPointProjectivization`: the point of `ℙ k (Fin (n + 1) → k)` of a `k`-point of
  `ℙⁿ_k`.
* `Faltings.intVal`: the values `(T_j / T_i)(z)` of the affine coordinates of a chart `D₊(Tᵢ)`
  of the integral model `ℙⁿ_ℤ` at a `k`-point `z` lying in it.

## Main results

* `Faltings.EmbeddingGroup.exists_projectiveEmbedding_height_eq_and_embeddingClass_eq`: the
  embedding `Φ_γ`.
* `Faltings.kPointProjectivization_eq_mk_intVal`: the homogeneous coordinates of a `k`-point of
  `ℙⁿ_k` are its integral chart values.
* `Faltings.kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint`: a `k`-point of `ℙⁿ_k`
  lying over the point `projectiveSpacePoint c` of `ℙⁿ_ℤ` is the class of `c`.
* `Faltings.exists_kPointProjectivization_segreProduct`: the homogeneous coordinates of the Segre
  product of two morphisms `X ⟶ ℙʳ_k`, `X ⟶ ℙᵐ_k` at a `k`-point are the products `P_a Q_b` of
  those of the factors.
* `Faltings.weilHeight_mk_mul_comp_equiv`: the point with coordinates `P_a Q_b`, in any order,
  has height `h(P) + h(Q)`.

## Implementation notes

The combination is an indexed family `φ : ι → Σ n, ProjectiveEmbedding f n` over a nonempty
finite type `ι` with coefficients `c : ι → ℕ`, all positive; the `φ i` need not be distinct.
The embedding `Φ_γ` is the generator `FreeAbelianGroup.of ⟨N, Φ⟩` of `Emb(X)`, and the two
equalities are those of `Faltings.EmbeddingGroup.height` and `Faltings.embeddingClass` on it.

The multiple `nᵢ φᵢ` is realized by the Segre product of `nᵢ` copies of `φᵢ` rather than by the
Veronese composite `φᵢ^{(nᵢ)}`: both have height `nᵢ h_{φᵢ}` and class `nᵢ cl(φᵢ)`, and the
Segre product carries the identification of the pullback of `𝒪(1)` as invertible modules on `X`,
which is what `Faltings.embeddingClass` reads.

The homogeneous coordinates of a `k`-point of `ℙⁿ_k`, read through the dictionary of
`Faltings.ProjectiveEmbedding.height`, are its values of the affine coordinates `T_j / T_i` of
a chart `D₊(Tᵢ)` of the integral model `ℙⁿ_ℤ` containing it.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

universe u v

namespace Faltings

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section Step

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [IsProjectiveVariety k f] [Smooth f]

/-- **The Segre product step.** For projective embeddings `Φ₁ : X ⟶ ℙʳ_k` and `Φ₂ : X ⟶ ℙᵐ_k`,
the Segre product `Φ₁ ⊗ Φ₂` is a projective embedding with `h_{Φ₁ ⊗ Φ₂} = h_{Φ₁} + h_{Φ₂}` and
`cl(Φ₁ ⊗ Φ₂) = cl(Φ₁) + cl(Φ₂)`. -/
private theorem exists_height_add_embeddingClass_add [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    {r m : ℕ} (Φ₁ : Faltings.ProjectiveEmbedding f r) (Φ₂ : Faltings.ProjectiveEmbedding f m) :
    ∃ Φ : Faltings.ProjectiveEmbedding f (r * m + r + m),
      Φ.height = Φ₁.height + Φ₂.height ∧
      Faltings.embeddingClass f (FreeAbelianGroup.of ⟨_, Φ⟩) =
        Faltings.embeddingClass f (FreeAbelianGroup.of ⟨_, Φ₁⟩) +
          Faltings.embeddingClass f (FreeAbelianGroup.of ⟨_, Φ₂⟩) := by
  have h : Φ₁.hom ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) =
      Φ₂.hom ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k) :=
    Φ₁.hom_over.trans Φ₂.hom_over.symm
  obtain ⟨Φ, hΦ⟩ := Faltings.ProjectiveEmbedding.exists_hom_eq_segreProduct Φ₁.hom Φ₂ h
  refine ⟨Φ, ?_, ?_⟩
  · funext p
    simp only [Pi.add_apply, ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization]
    have hy : (p.1 ≫ Faltings.segreProduct Φ₁.hom Φ₂.hom h) ≫
        projectiveSpaceOver (r * m + r + m) (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ := by
      rw [← hΦ, Category.assoc, Φ.hom_over, p.2]
    rw [kPointProjectivization_congr (congrArg (p.1 ≫ ·) hΦ) _ hy]
    obtain ⟨P, Q, hP, hQ, hPQ, h1, h2, h3⟩ :=
      exists_kPointProjectivization_segreProduct Φ₁.hom Φ₂.hom h p.1 hy
      (by rw [Category.assoc, Φ₁.hom_over, p.2]) (by rw [Category.assoc, Φ₂.hom_over, p.2])
    rw [h1, h2, h3]
    exact weilHeight_mk_mul_comp_equiv _ P Q hP hQ hPQ
  · simp only [embeddingClass, FreeAbelianGroup.lift_apply_of]
    obtain ⟨α⟩ := Faltings.nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso
      Φ₁.hom Φ₂.hom h
    rw [← hΦ] at α
    have h1 := Stacks.RingedSpace.modulePullback_isInvertible Φ₁.hom.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver r (Spec (.of k)) 1)
    have h2 := Stacks.RingedSpace.modulePullback_isInvertible Φ₂.hom.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver m (Spec (.of k)) 1)
    exact ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ h1 h2)).mpr ⟨α⟩).trans
      (Stacks.SheafOfModules.picardClass_schemeTensor X _ _ h1 h2)

end Step

section Assembly

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f]

/-- **A nonempty list of projective embeddings is realized by one embedding**: iterated Segre
products give an embedding whose height and class are the sums along the list. -/
private theorem exists_height_eq_sum_embeddingClass_eq_sum
    (l : List (Σ n : ℕ, Faltings.ProjectiveEmbedding f n)) (hl : l ≠ []) :
    ∃ (N : ℕ) (Φ : Faltings.ProjectiveEmbedding f N),
      Φ.height = (l.map fun e => e.2.height).sum ∧
      Faltings.embeddingClass f (FreeAbelianGroup.of ⟨N, Φ⟩) =
        (l.map fun e => Faltings.embeddingClass f (FreeAbelianGroup.of e)).sum := by
  induction l with
  | nil => exact absurd rfl hl
  | cons e t ih =>
    by_cases ht : t = []
    · subst ht
      exact ⟨e.1, e.2, by simp, by simp; exact (add_zero _).symm⟩
    · obtain ⟨N, Φ, h1, h2⟩ := ih ht
      obtain ⟨Ψ, h3, h4⟩ := exists_height_add_embeddingClass_add e.2 Φ
      exact ⟨_, Ψ, by rw [h3, h1, List.map_cons, List.sum_cons],
        by rw [h4, h2, List.map_cons, List.sum_cons]⟩

end Assembly

/-- The sum along the list in which each `φ i` is repeated `c i` times. -/
private theorem sum_map_flatMap_replicate {α ι G : Type*} [Fintype ι] [AddCommMonoid G]
    (φ : ι → α) (c : ι → ℕ) (g : α → G) :
    (((Finset.univ.toList : List ι).flatMap fun i => List.replicate (c i) (φ i)).map g).sum =
      ∑ i, c i • g (φ i) := by
  simp [List.flatMap_def, List.sum_flatten, List.map_replicate, List.sum_replicate]

/-- The list in which each `φ i` is repeated `c i > 0` times is nonempty. -/
private theorem flatMap_replicate_ne_nil {α ι : Type*} [Fintype ι] [Nonempty ι] (φ : ι → α)
    (c : ι → ℕ) (hc : ∀ i, 0 < c i) :
    ((Finset.univ.toList : List ι).flatMap fun i => List.replicate (c i) (φ i)) ≠ [] := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  simp only [ne_eq, List.flatMap_eq_nil_iff, Finset.mem_toList, Finset.mem_univ,
    List.replicate_eq_nil_iff, forall_const, not_forall]
  exact ⟨i, (hc i).ne'⟩

/-- If `γ = ∑ i, c i • φ i` is a combination, over a nonempty finite index type, of projective
embeddings `φ i` of a smooth projective variety `X` with positive coefficients `c i`, then there
is a projective embedding `Φ : X ⟶ ℙᴺ_k` with `h_Φ = h_γ` (`Faltings.EmbeddingGroup.height`) and
`cl(Φ) = cl(γ)` (`Faltings.embeddingClass`). -/
@[faltings "lem_ht_emb_operations"]
theorem EmbeddingGroup.exists_projectiveEmbedding_height_eq_and_embeddingClass_eq
    {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f]
    {ι : Type v} [Fintype ι] [Nonempty ι] (φ : ι → Σ n : ℕ, ProjectiveEmbedding f n)
    (c : ι → ℕ) (hc : ∀ i, 0 < c i) :
    ∃ (N : ℕ) (Φ : ProjectiveEmbedding f N),
      Φ.height = EmbeddingGroup.height f (∑ i, c i • FreeAbelianGroup.of (φ i)) ∧
      embeddingClass f (FreeAbelianGroup.of ⟨N, Φ⟩) =
        embeddingClass f (∑ i, c i • FreeAbelianGroup.of (φ i)) := by
  obtain ⟨N, Φ, h1, h2⟩ := exists_height_eq_sum_embeddingClass_eq_sum _
    (flatMap_replicate_ne_nil φ c hc)
  refine ⟨N, Φ, ?_, ?_⟩
  · rw [h1, sum_map_flatMap_replicate, map_sum]
    simp only [map_nsmul, EmbeddingGroup.height, FreeAbelianGroup.lift_apply_of]
  · rw [h2, sum_map_flatMap_replicate, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_nsmul _ _ _).symm

end Faltings
