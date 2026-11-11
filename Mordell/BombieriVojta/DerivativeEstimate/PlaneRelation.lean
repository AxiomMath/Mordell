module
public import Mathlib
public import Mordell.Attr

/-!
# The plane relation between two functions

Let `F / k` be a field extension, `t ∈ F` transcendental over `k`, and `z ∈ F`. Identify
`k⟮t⟯` with the rational function field `k(Y)` by `t ↦ Y`, and let `μ ∈ k(Y)[X]` be the minimal
polynomial of `z` over `k⟮t⟯` read through this identification. Let `r ∈ k[Y]` be the monic least
common denominator of the coefficients of `μ`. The plane relation of `z` over `t` is
`g = r μ ∈ k[Y][X] = k[X, Y]`; it satisfies `g(z, t) = 0`.

In Bombieri's proof of the Mordell conjecture this is applied in the function field `k(C)` of a
curve with `t = ξ₁₀` and `z = ξ_{νj}`, giving the polynomials `g_{νj}`.

## Main definitions

* `Faltings.FunctionField.planeRelation`: the polynomial `g = r μ ∈ k[Y][X]`.

## Implementation notes

The outer variable of `k[X][X]` is `X` and the coefficients lie in `k[Y]`, the inner polynomial
ring. The least common denominator is `Finset.lcm` of the (monic) denominators `RatFunc.denom` of
the coefficients of `μ`; in `k[Y]` this `lcm` is normalized, hence monic. The coefficient of `X^i`
in `g` is `num(μᵢ) · (r / denom(μᵢ))`, the division being exact. If `z` is transcendental over
`k⟮t⟯`, then `μ = 0` and `g = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, pp. 627–628
-/

open Polynomial IntermediateField

namespace Faltings.FunctionField

open scoped Classical in
/-- The plane relation `g = r μ ∈ k[Y][X]` of `z` over a transcendental `t`: `μ` is the minimal
polynomial of `z` over `k⟮t⟯`, transported to `k(Y)[X]` by `t ↦ Y`, and `r ∈ k[Y]` is the monic
least common denominator of its coefficients. The outer variable is `X`, the coefficients are in
`k[Y]`. -/
@[expose, faltings "def_bvs_plane_relation"]
public noncomputable def planeRelation (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F]
    (t z : F) (ht : Transcendental k t) : k[X][X] :=
  let μ : (RatFunc k)[X] := (minpoly k⟮t⟯ z).map
    (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom
  let r : k[X] := μ.support.lcm fun i => (μ.coeff i).denom
  ∑ i ∈ μ.support, C ((μ.coeff i).num * (r / (μ.coeff i).denom)) * X ^ i

end Faltings.FunctionField
