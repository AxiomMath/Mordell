module
public import Mordell.BombieriVojta.DerivativeEstimate.PlaneRelation

/-!
# The discriminant of a plane relation is non-zero

Let `F / k` be a field extension, `t ∈ F` transcendental over `k`, and `z ∈ F` separable over
`k⟮t⟯`. The plane relation `g = r μ ∈ k[Y][X]` of `z` over `t`
(`Faltings.FunctionField.planeRelation`) has degree `e ≥ 1` in `X`, and its discriminant
`D_g(Y) = Res_X(g, ∂g/∂X) ∈ k[Y]`, the Sylvester resultant with formal degrees `e` and `e - 1`, is
not the zero polynomial. Indeed `μ` is the minimal polynomial of `z`, of degree `e ≥ 1` and
separable, so `μ` and `dμ/dX` are coprime in `k(Y)[X]`; since `r ≠ 0`, the same holds for `g` and
`∂g/∂X`, and a resultant at formal degrees of which the first is exact vanishes only on a common
factor of positive degree.

In Bombieri's proof this is applied in the function field `k(C)` of a curve over a field of
characteristic `0`, with `t = ξ₁₀` and `z = ξ_{νj}`, giving the non-vanishing of `D_{g_{νj}}`.

## Main results

* `Faltings.FunctionField.one_le_natDegree_planeRelation_and_resultant_ne_zero`: `deg_X g ≥ 1`
  and `D_g ≠ 0`.

## Implementation notes

As in `Faltings.FunctionField.planeRelation`, the outer variable of `k[X][X]` is `X` and the
coefficients lie in `k[Y]`. The discriminant is written as Mathlib's `Polynomial.resultant` of `g`
and `Polynomial.derivative g` with formal degrees `g.natDegree` and `g.natDegree - 1`, the
convention of `Faltings.evalEval_derivative_ne_zero_of_eval_resultant_ne_zero`. The source works in
characteristic `0`, where every algebraic `z` is separable over `k⟮t⟯`; the statement asks only for
separability of `z`, which is what the argument uses.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, pp. 627–628
-/

open Polynomial IntermediateField

namespace Faltings.FunctionField

open scoped Classical in
/-- Over `k(Y)`, the plane relation `g` is `C r * μ`, where `μ` is the minimal polynomial of `z`
transported along `k⟮t⟯ ≃ k(Y)` and `r ≠ 0` is the lcm of the denominators of its coefficients. -/
private lemma map_planeRelation (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F]
    (t z : F) (ht : Transcendental k t) :
    let μ : (RatFunc k)[X] := (minpoly k⟮t⟯ z).map
      (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom
    let r : k[X] := μ.support.lcm fun i => (μ.coeff i).denom
    r ≠ 0 ∧ (planeRelation k t z ht).map (algebraMap k[X] (RatFunc k)) =
      C (algebraMap k[X] (RatFunc k) r) * μ := by
  intro μ r
  have hr : r ≠ 0 := by
    simp only [r, ne_eq, Finset.lcm_eq_zero_iff, not_exists, not_and]
    intro i _ h
    exact (RatFunc.denom_ne_zero _) h
  refine ⟨hr, ?_⟩
  unfold planeRelation
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  conv_rhs => rw [μ.as_sum_support_C_mul_X_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, ← C_mul]
  congr 2
  have hden : algebraMap k[X] (RatFunc k) (μ.coeff i).denom ≠ 0 := by
    simpa using RatFunc.denom_ne_zero (μ.coeff i)
  have hdiv : r / (μ.coeff i).denom * (μ.coeff i).denom = r := by
    obtain ⟨c, hc⟩ : (μ.coeff i).denom ∣ r := Finset.dvd_lcm hi
    rw [hc, mul_div_cancel_left₀ _ (RatFunc.denom_ne_zero _), mul_comm]
  have h1 : algebraMap k[X] (RatFunc k) (r / (μ.coeff i).denom) =
      algebraMap k[X] (RatFunc k) r / algebraMap k[X] (RatFunc k) (μ.coeff i).denom := by
    rw [eq_div_iff hden, ← map_mul, hdiv]
  rw [map_mul, h1]
  conv_rhs => rw [← RatFunc.num_div_denom (μ.coeff i)]
  field_simp
  exact mul_comm _ _

/-- A separable polynomial and its derivative have non-zero resultant at formal degrees
`deg p` and `deg p - 1`: the first degree is exact, so lowering the second to the true degree of
`p'` only multiplies the resultant by a power of the leading coefficient. -/
private lemma resultant_derivative_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p.Separable) :
    p.resultant (derivative p) p.natDegree (p.natDegree - 1) ≠ 0 := by
  rw [show p.natDegree - 1 = (derivative p).natDegree +
      (p.natDegree - 1 - (derivative p).natDegree) by have := natDegree_derivative_le p; omega,
    resultant_add_right_deg _ _ _ _ _ le_rfl]
  exact mul_ne_zero (pow_ne_zero _ (by simpa using hp.ne_zero)) (resultant_ne_zero _ _ hp)

/-- The plane relation `g = planeRelation k t z ht` of an element `z` separable over `k⟮t⟯` has
degree at least one in `X`, and its discriminant `Res_X(g, ∂g/∂X)`, with formal degrees
`deg_X g` and `deg_X g - 1`, is a non-zero element of `k[Y]`. -/
@[faltings "lem_bvs_plane_discriminant_nonzero"]
public theorem one_le_natDegree_planeRelation_and_resultant_ne_zero (k : Type*) [Field k]
    {F : Type*} [Field F] [Algebra k F] {t z : F} (ht : Transcendental k t)
    (hz : IsSeparable k⟮t⟯ z) :
    1 ≤ (planeRelation k t z ht).natDegree ∧
      (planeRelation k t z ht).resultant (derivative (planeRelation k t z ht))
        (planeRelation k t z ht).natDegree ((planeRelation k t z ht).natDegree - 1) ≠ 0 := by
  obtain ⟨hr, hmap⟩ := map_planeRelation k t z ht
  have hι : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective _ _
  have hc := (map_ne_zero_iff _ hι).mpr hr
  rw [← natDegree_map_eq_of_injective hι, ← map_ne_zero_iff _ hι, ← resultant_map_map,
    ← derivative_map]
  refine ⟨?_, resultant_derivative_ne_zero ?_⟩
  · rw [hmap, natDegree_C_mul hc, natDegree_map]
    exact minpoly.natDegree_pos hz.isIntegral
  · rw [hmap, Separable, derivative_C_mul]
    exact (isCoprime_mul_unit_left (isUnit_C.mpr hc.isUnit) _ _).mpr (Separable.map hz)

end Faltings.FunctionField
