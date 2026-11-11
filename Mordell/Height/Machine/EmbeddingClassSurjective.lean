module

public import Mathlib
public import Mordell.Height.Machine.EmbeddingGroup
public import Mordell.AlgebraicGeometry.VeryAmple.Twist

/-!
# Every Picard class is a difference of embedding classes

Let `X` be a smooth projective variety over a field `k`. Every class `c ∈ Pic(X)` is of the
form `cl(ψ) - cl(φ)` for two projective embeddings `φ : X ⟶ ℙᵐ_k`, `ψ : X ⟶ ℙⁿ_k`, where
`cl = Faltings.embeddingClass f` sends an embedding to the class of the pullback of `𝒪(1)`.
In particular `Faltings.embeddingClass f` is surjective.

Write `c = [M]`, choose a projective embedding `φ₀` of `X` and put `L₀ = φ₀^* 𝒪(1)`. By Serre's
twisting theorem `Faltings.eventually_isVeryAmple_tensorModules_tensorPowModule`, applied to
`M ⊗ M` and to `M`, there is one integer `a` with `(M ⊗ M) ⊗ L₀^{⊗ a} ≅ ψ^* 𝒪(1)` and
`M ⊗ L₀^{⊗ a} ≅ φ^* 𝒪(1)` for projective embeddings `ψ`, `φ`. Then
`cl(ψ) - cl(φ) = (2[M] + [L₀^{⊗ a}]) - ([M] + [L₀^{⊗ a}]) = [M]`.

## Main results

* `Faltings.exists_embeddingClass_sub_eq`: every `c : X.picardGroup` is
  `cl(ψ) - cl(φ)` for projective embeddings `φ`, `ψ` of `X`.

## Implementation notes

The base is an arbitrary field `k`; the case of the source is `k = \bar{ℚ}`.

The source realises the subtracted class `a[L₀]` by the Veronese composite `φ₀^{(a)}`, whose
pullback of `𝒪(1)` is `L₀^{⊗ a}`. Here the subtracted class is `[M ⊗ L₀^{⊗ a}]` instead, which
is very ample by the same twisting theorem; only additivity of the Picard class under tensor
product is then needed, and no computation of the class of `L₀^{⊗ a}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The Picard class is additive on `Stacks.RelativeVeryAmple.tensorModules`. -/
public lemma picardClass_tensorModules (A B : X.Modules)
    [hA : Stacks.Ample.IsInvertibleModule X A] [hB : Stacks.Ample.IsInvertibleModule X B] :
    X.picardClass (Stacks.RelativeVeryAmple.tensorModules X A B) inferInstance =
      X.picardClass A hA + X.picardClass B hB :=
  (X.picardClass_tensorSheaf _ _ hA hB _).symm

/-- Every class in the Picard group of a smooth projective variety `X` over a field `k` is a
difference `cl(ψ) - cl(φ)` of the classes `Faltings.embeddingClass` of two projective
embeddings `φ : X ⟶ ℙᵐ_k` and `ψ : X ⟶ ℙⁿ_k`. -/
@[faltings "lem_ht_cl_surjective"]
public theorem exists_embeddingClass_sub_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f] (c : X.picardGroup) :
    ∃ (m n : ℕ) (φ : ProjectiveEmbedding f m) (ψ : ProjectiveEmbedding f n),
      embeddingClass f (FreeAbelianGroup.of ⟨n, ψ⟩) -
        embeddingClass f (FreeAbelianGroup.of ⟨m, φ⟩) = c := by
  obtain ⟨n₀, i, hi, hif⟩ := (inferInstance : IsProjectiveVariety k f).isProjective
  let φ₀ : ProjectiveEmbedding f n₀ := ⟨i, hi, hif⟩
  obtain ⟨M, hM, rfl⟩ : ∃ (M : X.Modules) (hM : Stacks.Ample.IsInvertibleModule X M),
      X.picardClass M hM = c :=
    Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf c
  let L₀ := (Scheme.Modules.pullback φ₀.hom).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n₀ (Spec (.of k)))
  have hL₀ : IsVeryAmple f L₀ := ⟨n₀, φ₀, ⟨Iso.refl _⟩⟩
  obtain ⟨a, ⟨n, ψ, ⟨e₁⟩⟩, ⟨m, φ, ⟨e₂⟩⟩⟩ :=
    ((eventually_isVeryAmple_tensorModules_tensorPowModule f L₀ hL₀
      (Stacks.RelativeVeryAmple.tensorModules X M M)).and
    (eventually_isVeryAmple_tensorModules_tensorPowModule f L₀ hL₀ M)).exists
  refine ⟨m, n, φ, ψ, ?_⟩
  rw [embeddingClass_apply_of_eq_picardClass, embeddingClass_apply_of_eq_picardClass,
    (X.picardClass_eq_iff _ _ _ inferInstance).2 ⟨e₁.symm⟩,
    (X.picardClass_eq_iff _ _ _ inferInstance).2 ⟨e₂.symm⟩,
    picardClass_tensorModules, picardClass_tensorModules, picardClass_tensorModules]
  have key : ∀ {G : Type (u + 1)} [AddCommGroup G] (a b : G), a + a + b - (a + b) = a := by
    intros; abel
  exact key _ _

/-- The class homomorphism `cl : Emb(X) → Pic(X)` of a smooth projective variety over a field is
surjective. -/
public theorem embeddingClass_surjective {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f] :
    Function.Surjective (embeddingClass f) := fun c => by
  obtain ⟨m, n, φ, ψ, h⟩ := exists_embeddingClass_sub_eq f c
  exact ⟨_, by rw [map_sub]; exact h⟩

end Faltings
