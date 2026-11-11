module
public import Mathlib
public import Mordell.Attr

/-!
# The ideals `J_{A,B}` of a completed local ring of a product

Let `X ×_T Y` be a fibre product of schemes and `p` a point of it, with images `z = pr₁ p` in `X`
and `w = pr₂ p` in `Y`. Write `𝔪_z`, `𝔪_w` for the maximal ideals of the local rings `𝒪_{X,z}`,
`𝒪_{Y,w}`, and `𝒪̂_p` for the completion of `𝒪_{X ×_T Y, p}` at its maximal ideal. For `A B : ℕ`
the ideal `J_{A,B} = 𝔪_z^{A+1} 𝒪̂_p + 𝔪_w^{B+1} 𝒪̂_p` of `𝒪̂_p` is the ideal of germs that vanish
to order more than `A` along the first factor or more than `B` along the second. When `X = Y = C`
is a curve over an algebraically closed field `T = Spec k̄` and `p = (z, w)` is a closed point,
`𝒪̂_p ≅ k̄⟦ς, ς'⟧` for uniformizers `ς`, `ς'` at `z`, `w`, and `J_{A,B} = (ς^{A+1}, ς'^{B+1})`.

## Main definitions

* `Faltings.completedStalkBiorderIdeal`: the ideal `J_{A,B}` of the completed local ring of
  `X ×_T Y` at `p`.

## Implementation notes

The ideal is defined for an arbitrary fibre product of schemes and an arbitrary point of it; the
source's setting is the product `C × C` of a curve with itself over `k̄`, at a `k̄`-point. The
completed local ring is `AdicCompletion` of the stalk at its maximal ideal, and the maximal ideals
of the factors are pushed forward along the stalk maps of the two projections, then along the
canonical map of the stalk to its completion.

## References

* [E. Bombieri, *The Mordell conjecture revisited*, §6][bombieri1990]
-/

public section

namespace Faltings

open AlgebraicGeometry CategoryTheory Limits

/-- The ideal `J_{A,B} = 𝔪_z^{A+1} 𝒪̂_p + 𝔪_w^{B+1} 𝒪̂_p` of the completed local ring `𝒪̂_p` of
the fibre product `X ×_T Y` at a point `p`, where `𝔪_z`, `𝔪_w` are the maximal ideals of `X` and
`Y` at the images `z`, `w` of `p`, extended to `𝒪̂_p` along the stalk maps of the two
projections. -/
@[expose, faltings "def_bvr_ideal_j"]
noncomputable def completedStalkBiorderIdeal {T X Y : Scheme} (f : X ⟶ T) (g : Y ⟶ T)
    (p : (pullback f g : Scheme)) (A B : ℕ) :
    Ideal (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk p))
      ((pullback f g).presheaf.stalk p)) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk (pullback.fst f g p)) ^ (A + 1)).map
      ((algebraMap _ _).comp ((pullback.fst f g).stalkMap p).hom) ⊔
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (pullback.snd f g p)) ^ (B + 1)).map
      ((algebraMap _ _).comp ((pullback.snd f g).stalkMap p).hom)

end Faltings
