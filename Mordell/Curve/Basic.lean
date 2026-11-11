module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Smooth projective curves over a field

Let `k` be a field. A *curve* over `k` is a scheme `C` with a structure morphism
`f : C ⟶ Spec k` that is smooth, projective and geometrically integral, of dimension one.

## Main definitions

* `Faltings.IsSmoothProjectiveCurve`: the property of a structure morphism `f : C ⟶ Spec k`
  that makes `C` a smooth projective geometrically integral curve over `k`.

## Implementation notes

The structure morphism is an explicit argument, as for `AlgebraicGeometry.IsProjectiveVariety`.
The class is the conjunction of three library classes, inherited as parents:
`AlgebraicGeometry.IsProjectiveVariety` (a variety whose structure morphism is H-projective),
`AlgebraicGeometry.GeometricallyIntegral` and `AlgebraicGeometry.SmoothOfRelativeDimension 1`.
The dimension condition is carried by the relative dimension of the smooth morphism: for a
smooth morphism to the spectrum of a field with irreducible source, being of relative
dimension `1` is the same as being smooth with source of dimension `1`. The variety parent
adds nothing beyond the source's conditions, since a geometrically integral projective scheme
over `k` is integral, separated and of finite type over `k`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 0A23], [Stacks Project, Tag 04L1]
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- A scheme `C` with structure morphism `f : C ⟶ Spec k` over a field `k` is a
*(smooth projective) curve* when `f` is smooth of relative dimension one, `C` is a projective
variety over `k`, and `f` is geometrically integral. -/
@[faltings "def_nt_curve"]
public class IsSmoothProjectiveCurve (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) : Prop
    extends IsProjectiveVariety k f, GeometricallyIntegral f, SmoothOfRelativeDimension 1 f

end Faltings
