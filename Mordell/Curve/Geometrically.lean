module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Geometrically reduced curves

Let `K` be a field. A curve over `K` is an integral scheme `C` of dimension one together with a
separated morphism of finite type `f : C ⟶ Spec K`. It is *geometrically reduced* if for every
field extension `K'/K` the base change `C_{K'} = C ×_{Spec K} Spec K'` is reduced. Mathlib
records the second condition for an arbitrary morphism as `AlgebraicGeometry.GeometricallyReduced`:
a morphism `Spec K' ⟶ Spec K` is the same as a field extension `K'/K`, and the base change is
any pullback of `f` along it.

## Main definitions

* `Faltings.FunctionField.IsGeometricallyReducedCurve`: `f : C ⟶ Spec K` makes `C` a curve
  over `K` whose base changes to all field extensions of `K` are reduced.

## Implementation notes

"A curve over `K`" is Stacks' `AlgebraicGeometry.IsCurve K f` (Tag 0A23: a variety, i.e. integral,
separated, locally of finite type and quasi-compact over `K`, of dimension one), used directly;
geometric reducedness is Mathlib's
`AlgebraicGeometry.GeometricallyReduced f`. The class only conjoins the two, exactly as
`Faltings.FunctionField.IsGeometricallyIrreducibleCurve` does for irreducibility.

## References

* [Stacks, Tag 035U], [Stacks, Tag 020D], [Stacks, Tag 0A23]
-/

@[expose] public section

open AlgebraicGeometry

namespace Faltings.FunctionField

/-- A morphism `f : C ⟶ Spec K` exhibits `C` as a *geometrically reduced curve* over the
field `K`: `C` is a curve over `K` (integral of dimension one, `f` separated and of finite type),
and for every field extension `K'/K` the base change `C ×_{Spec K} Spec K'` is reduced. -/
@[faltings "def_ff_geometrically_reduced_curve"]
public class IsGeometricallyReducedCurve (K : Type*) [Field K] {C : Scheme}
    (f : C ⟶ Spec (.of K)) : Prop extends IsCurve K f, GeometricallyReduced f

end Faltings.FunctionField

end


/-!
# Geometrically irreducible curves

Let `K` be a field and `f : C ⟶ Spec K` a curve over `K`. The curve is *geometrically
irreducible* if for every field extension `K'/K` the base change `C_{K'} = C ×_{Spec K} Spec K'`
is irreducible. A morphism `Spec K' ⟶ Spec K` is the same as a field extension `K'/K`, and the
base change is any pullback of `f` along it, so this is Mathlib's
`AlgebraicGeometry.GeometricallyIrreducible f`.

## Main definitions

* `Faltings.FunctionField.IsGeometricallyIrreducibleCurve`: `f : C ⟶ Spec K` is a curve over `K`
  (`AlgebraicGeometry.IsCurve K f`) whose base changes to all field extensions of `K` are
  irreducible (`AlgebraicGeometry.GeometricallyIrreducible f`).

## Implementation notes

The class extends `AlgebraicGeometry.IsCurve K f` and
`AlgebraicGeometry.GeometricallyIrreducible f`, so either half is available by instance
inference, and an instance of the class is built from instances of the two halves.

## References

* [Stacks, Tag 0361], [Stacks, Tag 0A23]
-/

@[expose] section

open AlgebraicGeometry

namespace Faltings.FunctionField

/-- A morphism `f : C ⟶ Spec K` exhibits `C` as a *geometrically irreducible curve* over the
field `K`: `C` is a curve over `K`, and for every field extension `K'/K` the base change
`C ×_{Spec K} Spec K'` is irreducible. -/
@[faltings "def_ff_geometrically_irreducible_curve"]
public class IsGeometricallyIrreducibleCurve (K : Type*) [Field K] {C : Scheme}
    (f : C ⟶ Spec (.of K)) : Prop extends IsCurve K f, GeometricallyIrreducible f

end Faltings.FunctionField

end
