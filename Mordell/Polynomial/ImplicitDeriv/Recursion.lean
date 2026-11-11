module
public import Mordell.Polynomial.ImplicitDeriv.Basic

/-!
# The polynomials `q_l` compute the derivatives of an implicit branch

Let `p ∈ K[X, Y]` and let `ξ ∈ K⟦ς⟧` be a power series with `p(ξ, ς) = 0` and
`p_X(ξ(0), 0) ≠ 0`. Then Bombieri's polynomials
`q_l = Faltings.MvPolynomial.implicitDerivNumerator p l` satisfy
`q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} (d/dς)^l ξ = 0` for every `l ≥ 1`. The proof is an induction on `l`.
Differentiating `p(ξ, ς) = 0` gives `p_X ξ' + p_Y = 0`, which is the case `l = 1`. For the
induction step, the error term `E_l = q_l(ξ, ς) + p_X^{2l-1} ξ^{(l)}` satisfies
`E_{l+1} = p_X² E_l' - (2l - 1) p_X p_X' E_l` modulo `p_X ξ' + p_Y`, so no division by `p_X` is
needed.

## Main results

* `Faltings.MvPolynomial.aeval_implicitDerivNumerator_add_pow_mul_iterate_derivative`:
  `q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} ξ^{(l)} = 0`.

## Implementation notes

`K[X, Y]` is `MvPolynomial (Fin 2) K` with `X = X 0`, `Y = X 1`; the evaluation `u(ξ, ς)` is
`MvPolynomial.aeval ![ξ, PowerSeries.X] u`, and `d/dς` is `PowerSeries.derivative`. The
exponent `2l - 1` is a truncated subtraction in `ℕ`, which is the integer one since `l ≥ 1`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

/-- Chain rule: `d/dς u(ξ, ς) = u_X(ξ, ς) ξ' + u_Y(ξ, ς)`. -/
private lemma derivative_aeval {K : Type*} [CommRing K] (ξ : PowerSeries K)
    (u : MvPolynomial (Fin 2) K) :
    PowerSeries.derivative (R := K) (aeval ![ξ, PowerSeries.X] u) =
      aeval ![ξ, PowerSeries.X] (pderiv 0 u) * PowerSeries.derivative (R := K) ξ +
        aeval ![ξ, PowerSeries.X] (pderiv 1 u) := by
  induction u using MvPolynomial.induction_on with
  | C a => simp
  | add u v hu hv => simp only [map_add, hu, hv]; ring
  | mul_X u i ih =>
    simp only [map_mul, Derivation.leibniz, ih, pderiv_X, aeval_X, smul_eq_mul, map_add]
    fin_cases i <;> simp <;> ring

/-- The recursion for the error term `E_l = q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} ξ^{(l)}`: along a curve
where `d/dς p(ξ, ς) = p_X ξ' + p_Y` vanishes,
`E_{l+1} = p_X² E_l' - (2l - 1) p_X (d/dς p_X) E_l`. -/
private lemma implicitDerivError_succ {K : Type*} [CommRing K] (p : MvPolynomial (Fin 2) K)
    (ξ : PowerSeries K)
    (hF : aeval ![ξ, PowerSeries.X] (pderiv 0 p) * PowerSeries.derivative (R := K) ξ +
      aeval ![ξ, PowerSeries.X] (pderiv 1 p) = 0) (n : ℕ) :
    aeval ![ξ, PowerSeries.X] (implicitDerivNumerator p (n + 1 + 1)) +
        aeval ![ξ, PowerSeries.X] (pderiv 0 p) ^ (2 * (n + 1 + 1) - 1) *
          (PowerSeries.derivative (R := K))^[n + 1 + 1] ξ =
      aeval ![ξ, PowerSeries.X] (pderiv 0 p) ^ 2 * PowerSeries.derivative (R := K)
          (aeval ![ξ, PowerSeries.X] (implicitDerivNumerator p (n + 1)) +
            aeval ![ξ, PowerSeries.X] (pderiv 0 p) ^ (2 * (n + 1) - 1) *
              (PowerSeries.derivative (R := K))^[n + 1] ξ) -
        (2 * n + 1 : ℕ) * aeval ![ξ, PowerSeries.X] (pderiv 0 p) *
          PowerSeries.derivative (R := K) (aeval ![ξ, PowerSeries.X] (pderiv 0 p)) *
          (aeval ![ξ, PowerSeries.X] (implicitDerivNumerator p (n + 1)) +
            aeval ![ξ, PowerSeries.X] (pderiv 0 p) ^ (2 * (n + 1) - 1) *
              (PowerSeries.derivative (R := K))^[n + 1] ξ) := by
  rw [show 2 * (n + 1 + 1) - 1 = 2 * n + 1 + 2 by omega,
    show 2 * (n + 1) - 1 = 2 * n + 1 by omega, implicitDerivNumerator,
    Function.iterate_succ_apply' _ (n + 1)]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_aeval, smul_eq_mul,
    nsmul_eq_mul, map_sub, map_mul, map_pow, map_natCast, Nat.add_sub_cancel]
  push_cast
  linear_combination
    (-(aeval ![ξ, PowerSeries.X] (pderiv 0 (implicitDerivNumerator p (n + 1)))) *
      aeval ![ξ, PowerSeries.X] (pderiv 0 p) + (2 * n + 1) *
      aeval ![ξ, PowerSeries.X] (implicitDerivNumerator p (n + 1)) *
      aeval ![ξ, PowerSeries.X] (pderiv 0 (pderiv 0 p))) * hF

/-- If `p ∈ K[X, Y]` and `ξ ∈ K⟦ς⟧` satisfy `p(ξ, ς) = 0` and `p_X(ξ(0), 0) ≠ 0`, then
`q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} (d/dς)^l ξ = 0` for every `l ≥ 1`, where
`q_l = implicitDerivNumerator p l`. -/
@[faltings "lem_bvs_q_recursion"]
public theorem aeval_implicitDerivNumerator_add_pow_mul_iterate_derivative {K : Type*} [Field K]
    [CharZero K] (p : MvPolynomial (Fin 2) K) (ξ : PowerSeries K)
    (hξ : aeval ![ξ, PowerSeries.X] p = 0)
    (hpX : eval ![PowerSeries.constantCoeff ξ, 0] (pderiv 0 p) ≠ 0) {l : ℕ} (hl : 1 ≤ l) :
    aeval ![ξ, PowerSeries.X] (implicitDerivNumerator p l) +
        aeval ![ξ, PowerSeries.X] (pderiv 0 p) ^ (2 * l - 1) *
          (PowerSeries.derivative (R := K))^[l] ξ = 0 := by
  have hF := derivative_aeval ξ p
  rw [hξ, map_zero, eq_comm] at hF
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  induction n with
  | zero => simpa [implicitDerivNumerator, add_comm] using hF
  | succ n ih => rw [implicitDerivError_succ p ξ hF, ih (by omega)]; simp

end Faltings.MvPolynomial
