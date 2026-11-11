module

public import Mordell.Height.Machine.EmbeddingGroup
public import Mordell.Height.Machine.EmbeddingHeight

/-!
# Heights associated to divisor classes

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), with structure morphism `f : X ⟶ Spec k`, and let `c ∈ Pic(X) ⊗ ℚ`. A function
`h : X(k) → ℝ` is a *height associated to `c`* if there are an integer `m ≥ 1` and an element
`γ` of `Emb(X)` with `cl(γ) ⊗ 1 = m c` such that `h - (1/m) h_γ` is bounded on `X(k)`.

For a class `c ∈ Pic(X)`, a height associated to `c` is one associated to `c ⊗ 1`, and for a
divisor `D` a height associated to `D` is one associated to `cl(D) ⊗ 1`, with
`cl(D) = Faltings.picardClassOfWeilDivisor f D`.

## Main definitions

* `Faltings.IsHeightOfClass f c h`: `h` is a height associated to `c ∈ Pic(X) ⊗ ℚ`.

## Implementation notes

`Pic(X) ⊗ ℚ` is the tensor product `X.picardGroup ⊗[ℤ] ℚ` of abelian groups, and `m c` is the
`ℕ`-action. A `k`-point of `X` is a section of `f`. Boundedness of `h - (1/m) h_γ` is stated as
the existence of a uniform bound `C` on its absolute value. The variants for `c ∈ Pic(X)` and for
a divisor `D` are the instances `IsHeightOfClass f (c ⊗ₜ 1)` and
`IsHeightOfClass f (picardClassOfWeilDivisor f D ⊗ₜ 1)`; they are not separate declarations.
The base field is an algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Hindry, Silverman, *Diophantine Geometry*, B.3][hindrysilverman2000]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

/-- A function `h : X(k) → ℝ` on the `k`-points of a smooth projective variety `X` over `k`
is a **height associated to** a class `c ∈ Pic(X) ⊗ ℚ` if there are an integer `m ≥ 1` and
`γ ∈ Emb(X)` with `cl(γ) ⊗ 1 = m c` such that `h - (1/m) h_γ` is bounded. -/
@[faltings "def_ht_height_divisor_class"]
public def IsHeightOfClass {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f]
    (c : X.picardGroup ⊗[ℤ] ℚ) (h : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ) : Prop :=
  ∃ (m : ℕ) (γ : EmbeddingGroup f), 0 < m ∧ embeddingClass f γ ⊗ₜ[ℤ] (1 : ℚ) = m • c ∧
    ∃ C : ℝ, ∀ x, |h x - (m : ℝ)⁻¹ * EmbeddingGroup.height f γ x| ≤ C

/-- The height `h_φ` relative to a projective embedding `φ` is a height associated to its class
`cl(φ) ⊗ 1`. -/
public lemma isHeightOfClass_height {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] {n : ℕ} (φ : ProjectiveEmbedding f n) :
    IsHeightOfClass f (embeddingClass f (.of ⟨n, φ⟩) ⊗ₜ[ℤ] (1 : ℚ)) φ.height :=
  ⟨1, .of ⟨n, φ⟩, one_pos, (one_smul _ _).symm, 0, fun x => by
    simp [EmbeddingGroup.height]⟩

end Faltings
