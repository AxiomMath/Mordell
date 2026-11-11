module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Basic
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective

/-!
# The Segre morphism is a closed immersion

For `n m : ℕ` and a base scheme `S`, the Segre morphism
`Faltings.segreMorphism n m S : ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S`, given by the forms
`z_{ij} = x_i y_j`, is a closed immersion.

## Main results

* `Faltings.isClosedImmersion_segreMorphism`: the Segre morphism over any base scheme `S` is a
  closed immersion.

## Implementation notes

Over the integral models this is `AlgebraicGeometry.Segre.isClosedImmersion_segreMorphism`.
`Faltings.segreMorphism n m S` is the base change of that morphism along `S ⟶ Spec ℤ`, through
the identifications `ℙⁿ_S ×_S ℙᵐ_S ≅ (ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ) ×_ℤ S` and
`ℙ^{nm+n+m}_S ≅ ℙ^{nm+n+m}_ℤ ×_ℤ S`; closed immersions are stable under base change. The
existential form `Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding` asserts only that
some closed immersion over `S` exists; the statement here is about the Segre morphism itself.
The source's case is `S = Spec Q̄`.

## References

* [Hartshorne, *Algebraic Geometry*, II Ex. 5.11][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings

/-- `ℙⁿ_S` is the base change of `ℙⁿ_ℤ` along `S ⟶ Spec ℤ`. -/
private lemma isPullback_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsPullback (projectiveSpaceOver n S ↘ S)
      (pullback.snd (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  IsPullback.of_hasPullback _ _

/-- The Segre morphism over `S` is the base change of the Segre morphism over `ℤ`: the square
from `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` to `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^{nm+n+m}_ℤ` is a pullback. -/
private lemma isPullback_segreMorphism (n m : ℕ) (S : Scheme.{u}) :
    IsPullback
      (pullback.lift (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
        (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m S) (terminal.hom_ext _ _))
      (Faltings.segreMorphism n m S) (Segre.segreMorphism.{u} n m)
      (pullback.snd (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m)))) := by
  let ρ : pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ⟶
      pullback (terminal.from (projectiveSpaceAtUniverse.{u} n))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)) :=
    pullback.lift (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
      (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m S) (terminal.hom_ext _ _)
  -- `ℙⁿ_S ×_S ℙᵐ_S` is `S × (ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ)`.
  have hW := IsPullback.of_isPullback_four (ρ := ρ) (isPullback_projectiveSpaceOver n S)
    (isPullback_projectiveSpaceOver m S)
    (IsPullback.of_hasPullback (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from (projectiveSpaceAtUniverse.{u} m)))
    (IsPullback.of_hasPullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hs : IsPullback ρ
      (Faltings.segreMorphism n m S ≫ (projectiveSpaceOver (n * m + n + m) S ↘ S))
      (Segre.segreMorphism.{u} n m ≫
        terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))) (terminal.from S) := by
    rw [show Faltings.segreMorphism n m S ≫ (projectiveSpaceOver (n * m + n + m) S ↘ S) =
      pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S) from
        projectiveSpaceOver.liftAtUniverse_fst _ _ _]
    convert hW.flip using 1
    exact terminal.hom_ext _ _
  -- Paste with the defining square of `ℙ^{nm+n+m}_S`.
  exact .of_bot hs (projectiveSpaceOver.liftAtUniverse_toIntegralAtUniverse _ _ _).symm
    (isPullback_projectiveSpaceOver (n * m + n + m) S).flip

/-- The **Segre morphism** `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` is a closed immersion. -/
@[faltings "lem_ht_segre_closed_immersion"]
public theorem isClosedImmersion_segreMorphism (n m : ℕ) (S : Scheme.{u}) :
    IsClosedImmersion (segreMorphism n m S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (isPullback_segreMorphism n m S) (Segre.isClosedImmersion_segreMorphism.{u} n m)

end Faltings
