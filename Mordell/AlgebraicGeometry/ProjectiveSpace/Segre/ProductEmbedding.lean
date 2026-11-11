module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Embedding
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Product
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedImmersion

/-!
# Segre products with an embedding are embeddings

Let `X` be a projective variety over a field `k`, `f : X ⟶ ℙʳ_k` a morphism over `k` and
`ψ : X ⟶ ℙᵐ_k` a projective embedding. Then the Segre product
`f ⊗ ψ : X ⟶ ℙ^{(r+1)(m+1)-1}_k` is again a projective embedding: since `ψ` is a closed
immersion and `ℙʳ_k` is separated over `k`, the graph-like map `(f, ψ)` into
`ℙʳ_k ×_k ℙᵐ_k` is a closed immersion, and the Segre morphism is a closed immersion.

## Main results

* `Faltings.ProjectiveEmbedding.exists_hom_eq_segreProduct`: there is a projective embedding
  of `X` whose underlying morphism is `Faltings.segreProduct f ψ.hom h`.

## References

* [Gao, *An Introduction to Diophantine Geometry*, Prop. 5.1.3(iii)][gao2022]
* [Bombieri, *The Mordell conjecture revisited*, §2][bombieri1990]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings

/-- A morphism into a fibre product whose second component is a closed immersion is itself a
closed immersion, when the first factor is separated over the base. -/
private lemma isClosedImmersion_pullback_lift {X Y Z S : Scheme.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    {a : Y ⟶ S} {b : Z ⟶ S} [IsSeparated a] [IsClosedImmersion g] (h : f ≫ a = g ≫ b) :
    IsClosedImmersion (pullback.lift f g h) :=
  have : IsClosedImmersion (pullback.lift f g h ≫ pullback.snd a b) := by
    rwa [pullback.lift_snd]
  .of_comp _ (pullback.snd a b)

/-- The Segre morphism is a morphism over the base. -/
private lemma segreMorphism_comp_over (r m : ℕ) (S : Scheme.{u}) :
    segreMorphism r m S ≫ (projectiveSpaceOver (r * m + r + m) S ↘ S) =
      pullback.fst _ _ ≫ (projectiveSpaceOver r S ↘ S) :=
  projectiveSpaceOver.liftAtUniverse_fst _ _ _

/-- If `ψ` is a projective embedding of a projective variety `X` over `k` and `f : X ⟶ ℙʳ_k`
is a morphism over `k`, then the Segre product `f ⊗ ψ` is a projective embedding: `(f, ψ)` is
a closed immersion because its second component `ψ` is, and the Segre morphism is one. -/
@[faltings "lem_ht_product_embedding_closed_immersion"]
public theorem ProjectiveEmbedding.exists_hom_eq_segreProduct {k : Type u} [Field k]
    {X : Scheme.{u}} {p : X ⟶ Spec (.of k)} [IsProjectiveVariety k p] {r m : ℕ}
    (f : X ⟶ projectiveSpaceOver r (Spec (.of k))) (ψ : ProjectiveEmbedding p m)
    (h : f ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) =
      ψ.hom ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) :
    ∃ φ : ProjectiveEmbedding p (r * m + r + m), φ.hom = segreProduct f ψ.hom h := by
  have := ψ.isClosedImmersion
  have := isClosedImmersion_pullback_lift h
  have := isClosedImmersion_segreMorphism r m (Spec (.of k))
  refine ⟨⟨segreProduct f ψ.hom h, inferInstanceAs (IsClosedImmersion (_ ≫ _)), ?_⟩, rfl⟩
  simp only [segreProduct, Category.assoc, segreMorphism_comp_over, pullback.lift_fst_assoc, h,
    ψ.hom_over]

end Faltings
