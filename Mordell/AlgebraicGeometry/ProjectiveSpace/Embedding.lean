module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Projective embeddings

Let `X` be a projective variety over a field `k`, with structure morphism `f : X ⟶ Spec k`.
A *projective embedding* of `X` is a closed immersion `φ : X ⟶ ℙⁿ_k` of `k`-schemes into
projective `n`-space over `k`, for some `n`.

## Main definitions

* `Faltings.ProjectiveEmbedding`: a closed immersion of `k`-schemes `X ⟶ ℙⁿ_k`.
* `Faltings.ProjectiveEmbedding.baseChange`: the base change `X ⟶ ℙⁿ_K` of a projective
  embedding `A ⟶ ℙⁿ_k`, for `X = A ×_k K`.

## Implementation notes

Projective space `ℙⁿ_k` is `AlgebraicGeometry.projectiveSpaceOver n (Spec k)`, the base change
of `Proj ℤ[T₀, …, Tₙ]` to `Spec k`, with homogeneous coordinates indexed by `Fin (n + 1)`; its
structure morphism to `Spec k` is the canonical one. The dimension `n` is a parameter of the
type, so the projective embeddings of `X` into all projective spaces are the dependent pairs
`Σ n, ProjectiveEmbedding f n`. The base field is an arbitrary field `k`; the case of the source
is `k = \bar{ℚ}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.7][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- A **projective embedding** of a projective variety `X` over a field `k`, with structure
morphism `f : X ⟶ Spec k`: a closed immersion `X ⟶ ℙⁿ_k` of `k`-schemes. -/
@[faltings "def_ht_projective_embedding"]
public structure ProjectiveEmbedding {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (n : ℕ) where
  /-- The underlying morphism `X ⟶ ℙⁿ_k`. -/
  hom : X ⟶ projectiveSpaceOver n (Spec (.of k))
  /-- The underlying morphism is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion hom
  /-- The underlying morphism is a morphism over `Spec k`. -/
  hom_over : hom ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = f

section BaseChange

open CategoryTheory.Limits

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A X : Scheme.{u}} {fA : A ⟶ Spec (.of k)} [IsProjectiveVariety k fA]
  {fX : X ⟶ Spec (.of K)} [IsProjectiveVariety K fX] {p : X ⟶ A}

/-- The base change `X ⟶ ℙⁿ_K` of a morphism `φ : A ⟶ ℙⁿ_k`, for `X = A ×_k K`. -/
@[expose] public noncomputable def baseChangeHom {n : ℕ}
    (φ : A ⟶ projectiveSpaceOver n (Spec (.of k))) :
    X ⟶ projectiveSpaceOver n (Spec (.of K)) :=
  pullback.lift fX (p ≫ φ ≫ pullback.snd _ _) (terminal.hom_ext _ _)

omit [Algebra k K] [IsProjectiveVariety K fX] in
/-- The base change `X ⟶ ℙⁿ_K` of `φ` lies over `fX : X ⟶ Spec K`. -/
public lemma baseChangeHom_fst {n : ℕ} (φ : A ⟶ projectiveSpaceOver n (Spec (.of k))) :
    baseChangeHom (fX := fX) (p := p) φ ≫ pullback.fst _ _ = fX :=
  pullback.lift_fst _ _ _

omit [Algebra k K] [IsProjectiveVariety K fX] in
/-- The base change `X ⟶ ℙⁿ_K` of `φ`, followed by the second projection of `ℙⁿ_K`, is `p ≫ φ`
followed by the second projection of `ℙⁿ_k`. -/
public lemma baseChangeHom_snd {n : ℕ} (φ : A ⟶ projectiveSpaceOver n (Spec (.of k))) :
    baseChangeHom (fX := fX) (p := p) φ ≫ pullback.snd _ _ = p ≫ φ ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

omit [IsProjectiveVariety K fX] in
/-- For a projective embedding `φ` of `A`, the base change of `φ` followed by `ℙⁿ_K ⟶ ℙⁿ_k`
is `p ≫ φ`. -/
public lemma baseChangeHom_comp_projectiveSpaceOverMap
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K)))) {n : ℕ}
    (φ : ProjectiveEmbedding fA n) :
    baseChangeHom (fX := fX) (p := p) φ.hom ≫
        projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      p ≫ φ.hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc, baseChangeHom_fst,
      Category.assoc, show φ.hom ≫ pullback.fst _ _ = fA from φ.hom_over, hX.w]
  · rw [Category.assoc, projectiveSpaceOverMap_snd]
    exact (baseChangeHom_snd φ.hom).trans (Category.assoc _ _ _).symm

/-- The base change of a projective embedding of `A` is a projective embedding of `X`. -/
@[expose] public noncomputable def ProjectiveEmbedding.baseChange
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K)))) {n : ℕ}
    (φ : ProjectiveEmbedding fA n) : ProjectiveEmbedding fX n where
  hom := baseChangeHom (p := p) φ.hom
  isClosedImmersion := by
    have hpb : IsPullback (baseChangeHom (fX := fX) (p := p) φ.hom) p
        (projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K)))) φ.hom := by
      refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := pullback.fst _ _)
        (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k K))) ?_
        (baseChangeHom_comp_projectiveSpaceOverMap hX φ)
        (isPullback_projectiveSpaceOverMap n _).flip
      rw [baseChangeHom_fst, show φ.hom ≫ pullback.fst _ _ = fA from φ.hom_over]
      exact hX.flip
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip φ.isClosedImmersion
  hom_over := baseChangeHom_fst _

end BaseChange

end Faltings
