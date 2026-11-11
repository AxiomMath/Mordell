module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Basic

/-!
# The Segre product of two morphisms to projective spaces

Let `S` be a scheme and `X` a scheme with morphisms `f : X ⟶ ℙʳ_S` and `ψ : X ⟶ ℙᵐ_S` that
agree over `S`. Their Segre product is the composite
`f ⊗ ψ = s ∘ (f, ψ) : X ⟶ ℙʳ_S ×_S ℙᵐ_S ⟶ ℙ^{(r+1)(m+1)-1}_S`
of the pair `(f, ψ)` into the fibre product with the Segre morphism `s`. On points it is
`(f ⊗ ψ)(p) = f(p) ⊗ ψ(p)`, with coordinates `f(p)_i ψ(p)_j`.

## Main definitions

* `Faltings.segreProduct`: the Segre product `f ⊗ ψ` of two morphisms to projective spaces
  over `S`.

## Implementation notes

The source works with a projective variety `X` over `Q̄`, that is `S = Spec Q̄`. The composite
is formed for any base scheme `S` and any `S`-scheme `X`; that `X` is a projective variety plays
no role in its formation. The target `ℙ^{(r+1)(m+1)-1}_S` is written
`projectiveSpaceOver (r * m + r + m) S`, since `r * m + r + m = (r + 1)(m + 1) - 1`.

## References

* [Gao, *An Introduction to Diophantine Geometry*, proof of Prop. 5.1.3(iii)][gao2022]
* [Bombieri, *The Mordell conjecture revisited*, §2][bombieri1990]
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings

/-- The **Segre product** `f ⊗ ψ = s ∘ (f, ψ) : X ⟶ ℙ^{rm+r+m}_S` of morphisms `f : X ⟶ ℙʳ_S`
and `ψ : X ⟶ ℙᵐ_S` agreeing over `S`, where `(f, ψ) : X ⟶ ℙʳ_S ×_S ℙᵐ_S` and `s` is the Segre
morphism `Faltings.segreMorphism`. -/
@[expose, faltings "def_ht_segre_product_embedding"]
public noncomputable def segreProduct {S X : Scheme.{u}} {r m : ℕ}
    (f : X ⟶ projectiveSpaceOver r S) (ψ : X ⟶ projectiveSpaceOver m S)
    (h : f ≫ projectiveSpaceOver r S ↘ S = ψ ≫ projectiveSpaceOver m S ↘ S) :
    X ⟶ projectiveSpaceOver (r * m + r + m) S :=
  pullback.lift f ψ h ≫ segreMorphism r m S

end Faltings
