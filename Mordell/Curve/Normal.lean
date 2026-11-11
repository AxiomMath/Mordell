module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Smooth curves are normal

Let `K` be a perfect field and `f : C ⟶ Spec K` a smooth curve over `K`. Then `C` is a normal
scheme: every stalk `𝒪_{C,x}` is an integrally closed domain. At the generic point the stalk is
the function field `K(C)`, a field; at a closed point the stalk is a one-dimensional regular local
ring, hence a discrete valuation ring, hence integrally closed.

## Main results

* `Faltings.FunctionField.isNormal_of_smooth`: a smooth curve over a perfect field is normal.

## Implementation notes

A curve is `AlgebraicGeometry.IsCurve K f`, smoothness is `AlgebraicGeometry.Smooth f`, and
normality is `AlgebraicGeometry.IsNormal C` (every stalk is an integrally closed domain).

The proof does not split into the generic point and the closed points: a scheme smooth over a
field is regular, and a regular scheme is normal. Neither the curve hypothesis nor perfectness
of `K` is used.

## References

* [Stacks, Tag 033H], [Stacks, Tag 056S]
-/

public section

universe u

namespace Faltings.FunctionField

open AlgebraicGeometry

/-- A smooth curve `f : C ⟶ Spec K` over a perfect field `K` is a normal scheme. -/
@[faltings "lem_ff_smooth_curve_normal"]
theorem isNormal_of_smooth (K : Type u) [Field K] [PerfectField K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] :
    IsNormal C :=
  isNormal_of_isRegular C (isRegular_of_smooth_over_field f)

end Faltings.FunctionField

end
