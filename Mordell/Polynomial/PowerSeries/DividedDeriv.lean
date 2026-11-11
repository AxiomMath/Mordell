module
public import Mathlib
public import Mordell.Attr

/-!
# Divided derivatives of power series

Let `K` be a field of characteristic `0`. For a formal power series `f ∈ K⟦ς⟧` and `l ∈ ℕ`, the
`l`-th divided derivative of `f` is
`∂_l f = (1 / l!) (d/dς)^l f ∈ K⟦ς⟧`.
Its constant term `∂_l f (0) ∈ K` is `PowerSeries.constantCoeff (∂_l f)`.

## Main definitions

* `Faltings.PowerSeries.dividedDerivative`: the `K`-linear endomorphism `∂_l` of `K⟦X⟧`.

## Main results

* `Faltings.PowerSeries.constantCoeff_dividedDerivative`: `∂_l f (0)` is the coefficient of
  `X ^ l` in `f`.

## Implementation notes

`∂_l` is defined as the `K`-linear map `(l !)⁻¹ • D ^ l`, where `D` is Mathlib's formal
derivative `PowerSeries.derivative K` viewed as a linear endomorphism; linearity is thus part of
the data. The value `∂_l f (0)` is not given a separate name: it is
`PowerSeries.constantCoeff (dividedDerivative K l f)`, and `constantCoeff_dividedDerivative`
identifies it with the coefficient of `X ^ l` in `f`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

namespace Faltings.PowerSeries

open _root_.PowerSeries Nat in
/-- The `l`-th divided derivative `∂_l = (1 / l!) (d/dX)^l` on formal power series over a field
`K` of characteristic `0`, as a `K`-linear endomorphism of `K⟦X⟧`. -/
@[expose, faltings "def_bvs_divided_derivative"]
public noncomputable def dividedDerivative (K : Type*) [Field K] [CharZero K] (l : ℕ) :
    K⟦X⟧ →ₗ[K] K⟦X⟧ :=
  ((l ! : K)⁻¹) • (derivative (R := K)).toLinearMap ^ l

open _root_.PowerSeries in
/-- The constant coefficient of `∂_l f` is the `l`-th coefficient of `f`. -/
public theorem constantCoeff_dividedDerivative {K : Type*} [Field K] [CharZero K] (l : ℕ)
    (f : K⟦X⟧) : constantCoeff (dividedDerivative K l f) = coeff l f := by
  rw [← coeff_zero_eq_constantCoeff_apply, dividedDerivative, LinearMap.smul_apply,
    Module.End.pow_apply, coeff_smul]
  simp [coeff_iterate_derivative, Nat.factorial_ne_zero]

end Faltings.PowerSeries
