module
public import Mathlib
public import Mordell.Attr

/-!
# A non-vanishing discriminant gives a simple root

Let `p` be a polynomial in two variables `X, Y` over a commutative ring `R`, viewed as a
polynomial in `X` with coefficients in `R[Y]`, of degree `e ≥ 1` in `X`. Its discriminant with
respect to `X` is the resultant `D_p(Y) = Res_X(p, ∂p/∂X) ∈ R[Y]`, taken with formal degrees `e`
and `e - 1`. If `p(ξ₀, 0) = 0` and `D_p(0) ≠ 0`, then `∂p/∂X (ξ₀, 0) ≠ 0`: specialising `Y = 0`
commutes with forming the resultant, and a common root of `p(X, 0)` and `∂p/∂X (X, 0)` forces
their resultant to vanish.

## Main results

* `Faltings.evalEval_derivative_ne_zero_of_eval_resultant_ne_zero`: under the hypotheses above,
  `∂p/∂X (ξ₀, 0) ≠ 0`.

## Implementation notes

A polynomial in `X, Y` is a term `p : R[X][X]` whose outer variable is `X` (the variable of the
resultant and of the derivative) and whose coefficients are polynomials in `Y`; so `p(ξ₀, 0)` is
`Polynomial.evalEval 0 ξ₀ p`, `∂p/∂X` is `Polynomial.derivative p` and `D_p` is
`Polynomial.resultant p (derivative p) p.natDegree (p.natDegree - 1)`. The statement holds over
any commutative ring, not only over a field.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings

open Polynomial

/-- A common root of `f` and `g` kills their resultant at any formal degrees `(m, n)` bounding
the degrees, not both zero: evaluate the Bézout identity `f * a + g * b = C (resultant f g m n)`
at the root. -/
private lemma resultant_eq_zero_of_eval_eq_zero {R : Type*} [CommRing R] {f g : R[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) {x : R}
    (hfx : f.eval x = 0) (hgx : g.eval x = 0) : f.resultant g m n = 0 := by
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  simpa [hfx, hgx] using (congrArg (eval x) hab).symm

/-- If `p ∈ R[Y][X]` has degree at least one in `X`, vanishes at `(ξ₀, 0)`, and its discriminant
`Res_X(p, ∂p/∂X)` (formal degrees `e`, `e - 1`) does not vanish at `Y = 0`, then `∂p/∂X` does not
vanish at `(ξ₀, 0)`: specialise `Y = 0` through `Polynomial.resultant_map_map`, and the
specialised `p` and `∂p/∂X` share the root `ξ₀`. -/
@[faltings "lem_bvs_simple_root"]
public theorem evalEval_derivative_ne_zero_of_eval_resultant_ne_zero {R : Type*} [CommRing R]
    {p : R[X][X]} (hdeg : 1 ≤ p.natDegree) {ξ₀ : R} (hroot : p.evalEval 0 ξ₀ = 0)
    (hD : (p.resultant (derivative p) p.natDegree (p.natDegree - 1)).eval 0 ≠ 0) :
    (derivative p).evalEval 0 ξ₀ ≠ 0 := by
  intro hder
  rw [← map_evalRingHom_eval] at hroot hder
  refine hD ?_
  rw [← coe_evalRingHom, ← resultant_map_map]
  exact resultant_eq_zero_of_eval_eq_zero natDegree_map_le
    (natDegree_map_le.trans (natDegree_derivative_le p)) (Or.inl (by omega)) hroot hder

end Faltings
