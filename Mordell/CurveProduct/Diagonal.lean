module

public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroDivisor

/-!
# The diagonal of a curve is an effective Cartier divisor

Let `C` be a smooth projective geometrically integral curve over a field `k`, and let
`X = C ×_k C`. Since `C` is separated, the diagonal `Δ_{C/k} : C ⟶ X` is a closed immersion;
its image `Δ ⊆ X` is the closed subscheme cut out by the kernel ideal sheaf of `Δ_{C/k}`.
Then `Δ` is an integral effective Cartier divisor on `X`, the canonical morphism from `C` onto
`Δ` is an isomorphism, and the ideal sheaf of `Δ` is the invertible sheaf `𝓞_X(-Δ)`.

The first projection `pr₁ : X ⟶ C` is a base change of `f`, so it is separated and smooth of
relative dimension one, and the diagonal `Δ_{C/k}` is a section of it. The triple
`(X, pr₁, Δ_{C/k})` is therefore a pointed family over `C`, whose zero divisor is the closed
subscheme `Δ`. A section of a separated morphism smooth of relative dimension one cuts out a
relative effective Cartier divisor, since `Δ ⟶ C` is an isomorphism, hence finite locally free
([Stacks, Tag 0B9D]); in particular `Δ` is an effective Cartier divisor on `X`. The diagonal is
a closed immersion, so it induces an isomorphism `C ≅ Δ`, and `Δ` is integral because `C` is.

## Main results

* `Faltings.isEffectiveCartierDivisor_ker_diagonal`: the closed subscheme
  `(pullback.diagonal f).ker` of `C ×_k C` is an integral effective Cartier divisor, and
  `(pullback.diagonal f).toImage : C ⟶ Δ` is an isomorphism.

## Implementation notes

The diagonal `Δ` is the closed subscheme `(pullback.diagonal f).ker.subscheme`, which is
Mathlib's scheme-theoretic image `(pullback.diagonal f).image`. Being an effective Cartier
divisor is `Stacks.Divisors.IsEffectiveCartierDivisor`: the ideal sheaf of `Δ` is an invertible
`𝓞_X`-module. That ideal sheaf is, by definition, `Stacks.Divisors.negativeTwist`, the sheaf
`𝓞_X(-Δ)`; so the clause "with ideal sheaf `𝓞_X(-Δ)`" holds by the definition of `𝓞_X(-Δ)`
and its invertibility is the effective Cartier condition. The isomorphism `Δ ≅ C` is pinned
as the canonical factorisation `Scheme.Hom.toImage` of the diagonal through its image.

The effective Cartier property is read off from the relative statement for the section
`Δ_{C/k}` of `pr₁`, rather than from the codimension-one criterion on the regular surface `X`
([Stacks, Tag 0BXH]): both give the same conclusion, and the relative route needs no
dimension count on `X`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 0BXH], [Stacks Project, Tag 0AG0], [Stacks Project, Tag 01WR]
* [Stacks Project, Tag 0B9D], [Stacks Project, Tag 062T]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- The image of the diagonal is integral: it is isomorphic to `C`. -/
private lemma isIntegral_ker_diagonal_subscheme {S C : Scheme.{u}} (f : C ⟶ S) [IsIntegral C]
    [IsSeparated f] : IsIntegral (pullback.diagonal f).ker.subscheme :=
  have : Nonempty (pullback.diagonal f).ker.subscheme :=
    ⟨(pullback.diagonal f).toImage (Nonempty.some inferInstance)⟩
  isIntegral_of_isOpenImmersion (inv (pullback.diagonal f).toImage)

/-- For a smooth projective geometrically integral curve `f : C ⟶ Spec k`, the diagonal
`Δ ⊆ C ×_k C`, the closed subscheme cut out by the kernel of `pullback.diagonal f`, is an
effective Cartier divisor (its ideal sheaf `𝓞_X(-Δ)` is invertible), it is integral, and the
diagonal induces an isomorphism `C ≅ Δ`. -/
@[faltings "lem_nt_divisors_c_times_c"]
theorem isEffectiveCartierDivisor_ker_diagonal (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] :
    Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal f).ker ∧
      IsIntegral (pullback.diagonal f).ker.subscheme ∧
      IsIso (pullback.diagonal f).toImage := by
  have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f f).flip inferInstance
  exact ⟨ModuliEllipticCurves.PointedFamily.isEffectiveCartierDivisor_zeroDivisor
    ⟨pullback f f, pullback.fst f f, pullback.diagonal f, pullback.diagonal_fst f⟩,
    isIntegral_ker_diagonal_subscheme f, inferInstance⟩

end Faltings
