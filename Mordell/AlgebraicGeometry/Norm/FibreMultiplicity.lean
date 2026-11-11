module
public import Mathlib
public import Mordell.Attr

/-!
# Fibre multiplicities

For a morphism of schemes `f : X ⟶ Y` and a point `x : X`, the *fibre multiplicity* of `f`
at `x` is the length of the local ring at `x` of the scheme-theoretic fibre `f⁻¹(f x)`,
as a module over itself. When `f = π_{ab} : W_{ab} → 𝔸¹ × 𝔸¹` and `x = q` lies over
`p`, this is the integer `e_q` of Bombieri's norm formula
`(Norm f)(p) = ∏_{q ∈ π_{ab}⁻¹(p)} f(q)^{e_q}`.

## Main definitions

* `Faltings.fibreMultiplicity f x`: the length of the local ring of `f.fiber (f x)` at
  `f.asFiber x`, valued in `ℕ∞`.

## Implementation notes

The source defines `e_q` only for the projection `π_{ab}` and a geometric point `p` of
`𝔸¹ × 𝔸¹`. The definition makes sense for any morphism and any point of the source,
so it is stated in that generality; `e_q` is `fibreMultiplicity π_{ab} q`. The length
is valued in `ℕ∞`, since a local ring need not have finite length. For a quasi-finite
morphism such as the finite `π_{ab}`, the fibre is a finite discrete scheme and the
length is finite.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9][bombieri1990]
-/

namespace Faltings

open AlgebraicGeometry in
/-- The *fibre multiplicity* of a morphism of schemes `f : X ⟶ Y` at a point `x : X`: the
length of the local ring at `x` of the scheme-theoretic fibre `f⁻¹(f x)`, as a module over
itself. -/
@[expose, faltings "def_bvr_fibre_multiplicity"]
public noncomputable def fibreMultiplicity {X Y : Scheme} (f : X ⟶ Y) (x : X) : ℕ∞ :=
  Module.length ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
    ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

end Faltings
