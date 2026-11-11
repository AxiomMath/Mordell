module
public import Mordell.Curve.DegreeOneDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic

/-!
# Vojta divisors

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one. On
`X = C ×_k C` put `Δ' = Δ - P × C - C × P` and, for integers `d₁, d₂, d`,
`V(d₁, d₂, d) = d₁ (P × C) + d₂ (C × P) + d Δ'`, whose class in `Pic(X)` is
`Faltings.CurveWithDegreeOneDivisor.vojtaClass`. Following Bombieri, `V(d₁, d₂, d)` is a
*Vojta divisor* when `d₁, d₂, d` are positive and `g d² < d₁ d₂ < g² d²`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.IsVojtaDivisor X d₁ d₂ d`: the divisor
  `V(d₁, d₂, d)` on `C ×_k C`, of class `X.vojtaClass d₁ d₂ d`, is a Vojta divisor.

## Implementation notes

The divisor `V(d₁, d₂, d)` is recorded by its coefficients `d₁, d₂, d` together with the curve
`X = (C, P)`: its class is `X.vojtaClass d₁ d₂ d`, and the Vojta condition is a condition on
these coefficients and on the genus `AlgebraicGeometry.genus X.f = dim_k H¹(C, 𝒪_C)`, so the
definition depends only on `X` and the three integers. It is a structure, so its five conditions
are available as named projections.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3
-/

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The *Vojta condition* (Bombieri): for a curve `X = (C, P)` of genus `g` over `k`, the divisor
`V(d₁, d₂, d) = d₁ (P × C) + d₂ (C × P) + d Δ'` on `C ×_k C`, whose class is
`X.vojtaClass d₁ d₂ d`, is a *Vojta divisor* if `d₁, d₂, d` are positive integers with
`g d² < d₁ d₂ < g² d²`. -/
@[faltings "def_bv_vojta_divisor"]
public structure IsVojtaDivisor (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ) : Prop where
  /-- The coefficient `d₁` of `P × C` is positive. -/
  pos_d₁ : 0 < d₁
  /-- The coefficient `d₂` of `C × P` is positive. -/
  pos_d₂ : 0 < d₂
  /-- The coefficient `d` of `Δ'` is positive. -/
  pos_d : 0 < d
  /-- The lower Vojta inequality `g d² < d₁ d₂`. -/
  genus_mul_sq_lt : (AlgebraicGeometry.genus X.f : ℤ) * d ^ 2 < d₁ * d₂
  /-- The upper Vojta inequality `d₁ d₂ < g² d²`. -/
  lt_genus_sq_mul_sq : d₁ * d₂ < (AlgebraicGeometry.genus X.f : ℤ) ^ 2 * d ^ 2

end Faltings.CurveWithDegreeOneDivisor
