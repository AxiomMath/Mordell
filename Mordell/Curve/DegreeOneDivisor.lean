module
public import Mordell.Curve.Basic

/-!
# Curves with a rational divisor of degree one

Let `k` be a field. A *curve with a rational divisor of degree one* over `k` is a pair `(C, P)`
of a smooth projective geometrically integral curve `C` over `k` and a divisor
`P = ∑ nₓ x` on `C`, a finite `ℤ`-combination of closed points of `C`, of degree
`deg P = ∑ nₓ [κ(x) : k] = 1`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor`: a curve over `k` together with a divisor of degree one.

## Implementation notes

The curve is bundled as a scheme `C`, its structure morphism `f : C ⟶ Spec k` and the class
`Faltings.IsSmoothProjectiveCurve k f`. A divisor is a finitely supported function from the
closed points of `C` to `ℤ`. The degree of a closed point `x` is the residue degree
`AlgebraicGeometry.Scheme.Hom.residueDegree f x = [κ(x) : κ(f x)]`, and `κ(f x)` is the residue
field of the unique point of `Spec k`, which is `k`; it is finite since `C` is of finite type
over `k` and `x` is closed.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- A *curve with a rational divisor of degree one* over a field `k`: a smooth projective
geometrically integral curve `C` over `k`, with structure morphism `f`, together with a divisor
`P`, a finite `ℤ`-combination of closed points of `C`, of degree
`∑ P x • [κ(x) : k] = 1`. -/
@[faltings "def_nt_curve_setup"]
public structure CurveWithDegreeOneDivisor (k : Type u) [Field k] where
  /-- The underlying scheme of the curve. -/
  C : Scheme.{u}
  /-- The structure morphism of the curve. -/
  f : C ⟶ Spec (.of k)
  /-- `C` is a smooth projective geometrically integral curve over `k`. -/
  [isSmoothProjectiveCurve : IsSmoothProjectiveCurve k f]
  /-- The divisor `P`, a finite `ℤ`-combination of closed points of `C`. -/
  P : {x : C // IsClosed ({x} : Set C)} →₀ ℤ
  /-- The divisor `P` has degree one: `∑ P x • [κ(x) : k] = 1`. -/
  degree_P : (P.sum fun x n => n * (f.residueDegree x.1 : ℤ)) = 1

attribute [instance] CurveWithDegreeOneDivisor.isSmoothProjectiveCurve

end Faltings
