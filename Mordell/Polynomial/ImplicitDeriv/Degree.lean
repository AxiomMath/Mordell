module
public import Mordell.Polynomial.ImplicitDeriv.Basic
public import Mordell.Polynomial.ImplicitDeriv.Length

/-!
# The degree of the polynomials `q_l`

For `p ∈ K[X, Y]` of total degree `D ≥ 1`, Bombieri's polynomials
`q_l = Faltings.MvPolynomial.implicitDerivNumerator p l` satisfy `deg q_l ≤ (2l - 1)(D - 1)` for
all `l ≥ 1`. The proof is an induction on `l`: `q₁ = p_Y` has degree at most `D - 1`, and each of
the three terms of `q_{l+1}` has degree at most `deg q_l + 2(D - 1)`, since a partial derivative
does not raise the total degree and lowers that of `p` to at most `D - 1`.

## Main results

* `Faltings.MvPolynomial.totalDegree_implicitDerivNumerator_le`: `deg q_l ≤ (2l - 1)(D - 1)`.

## Implementation notes

Degrees are `MvPolynomial.totalDegree`, valued in `ℕ`; since `l ≥ 1` and `D ≥ 1`, the truncated
subtractions `2 * l - 1` and `D - 1` agree with the integer ones.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

/-- For `p ∈ K[X, Y]` of total degree `D ≥ 1`, the polynomial `q_l(p)` has total degree at most
`(2l - 1)(D - 1)` for every `l ≥ 1`. -/
@[faltings "lem_bvs_q_degree"]
public theorem totalDegree_implicitDerivNumerator_le {K : Type*} [Field K]
    (p : MvPolynomial (Fin 2) K) (hD : 1 ≤ p.totalDegree) {l : ℕ} (hl : 1 ≤ l) :
    (implicitDerivNumerator p l).totalDegree ≤ (2 * l - 1) * (p.totalDegree - 1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa [implicitDerivNumerator] using totalDegree_pderiv_le 1 p
  | succ l hl ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hl
    refine (totalDegree_implicitDerivNumerator_succ_succ_le p n).trans ?_
    rw [show 2 * (n + 1 + 1) - 1 = 2 * (n + 1) - 1 + 2 by omega, add_mul]
    omega

end Faltings.MvPolynomial
