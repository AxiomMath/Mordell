module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Images of proper schemes are closed

If `X` is proper over a base scheme `S` and `Y` is separated over `S`, then every `S`-morphism
`f : X ⟶ Y` has Zariski closed image. In particular, for a projective variety `X` over `\bar{ℚ}`
and a morphism `f : X → ℙᴺ` over `\bar{ℚ}`, the image `f(X)` is closed in `ℙᴺ`, since projective
varieties are proper and projective space is separated.

## Main results

* `Faltings.isClosed_range_of_isProper_of_isSeparated`: the range of an `S`-morphism from a
  proper `S`-scheme to a separated `S`-scheme is closed.

## Implementation notes

The statement is made over an arbitrary base `S`, for a proper source and a separated target;
the case of a projective variety over `\bar{ℚ}` mapping to projective space is the instance
`S = Spec \bar{ℚ}`, `Y = ℙᴺ`.

## References

* [Hartshorne, *Algebraic Geometry*, II.4.8 and II.4.9][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- The image of an `S`-morphism from a proper `S`-scheme to a separated `S`-scheme is closed:
the morphism is itself universally closed (Hartshorne II.4.8), hence a closed map. -/
public theorem isClosed_range_of_isProper_of_isSeparated {S X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : X ⟶ S) (q : Y ⟶ S) [IsProper p] [IsSeparated q] (h : f ≫ q = p) :
    IsClosed (Set.range f) := by
  subst h
  have : UniversallyClosed f := .of_comp_of_isSeparated f q
  exact f.isClosedMap.isClosed_range

/-- **Images of projective varieties are closed.** For a projective variety `X` over a field `k`
and a `k`-morphism `f : X ⟶ ℙᴺ_k`, the image of `f` is Zariski closed. -/
@[faltings "lem_ht_projective_image_closed"]
public theorem isClosed_range_of_isProjectiveVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjectiveVariety k p] {N : ℕ}
    (f : X ⟶ projectiveSpaceOver N (Spec (.of k)))
    (h : f ≫ (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) = p) :
    IsClosed (Set.range f) := by
  have : IsProper p := (inferInstance : IsProperVariety k p).toIsProper
  have : IsProper (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) :=
    isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_projectiveSpaceOver N _)
  exact isClosed_range_of_isProper_of_isSeparated f p _ h

end Faltings
