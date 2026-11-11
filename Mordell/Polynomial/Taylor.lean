module
public import Mordell.Polynomial.IteratedPDeriv
public import Mordell.Attr

/-!
# Taylor expansion of a multivariate polynomial

Let `K` be a field of characteristic `0`, `Q ∈ K[ς₁, …, ςₘ]` and `x ∈ Kᵐ`. Translating the
variables by `x` gives `Q(x + τ) ∈ K[τ₁, …, τₘ]`, and its coefficient of `τ^I` is the value at `x`
of the divided derivative `∂_I Q = (1 / I!) ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₘ}/∂ςₘ^{iₘ} Q`. Equivalently
`Q(x + τ) = ∑_I ∂_I Q(x) τ^I`, a finite sum since `Q(x + τ)` is a polynomial.

## Main results

* `Faltings.MvPolynomial.coeff_aeval_C_add_X`: the coefficient of `τ^I` in `Q(x + τ)` is
  `(∏ μ, (I μ)!)⁻¹ * (∂^I Q)(x)`.

## Implementation notes

The expansion is stated coefficientwise: an identity of polynomials in `τ` is the same as the
identity of all their coefficients, and the finiteness of the sum is then automatic. The
translate `Q(x + τ)` is `MvPolynomial.aeval (fun μ => C (x μ) + X μ) Q`, and the iterated partial
derivative `∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₘ}/∂ςₘ^{iₘ}` is the product, in `Module.End K`, of the powers
`(MvPolynomial.pderiv μ) ^ (I μ)` taken in the order `μ = 0, …, m - 1`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial Nat

section

variable {K : Type*} [Field K] {m : ℕ}

/-- The constant coefficient of `∂^I P = (∏ μ, (pderiv μ) ^ (I μ)) P` is `I!` times the
coefficient of `X^I` in `P`. -/
private lemma coeff_zero_iteratedPDeriv (I : Fin m →₀ ℕ) (P : MvPolynomial (Fin m) K) :
    ((List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) :
      List (Module.End K (MvPolynomial (Fin m) K))).prod P).coeff 0 =
      P.coeff I * ∏ μ, ((I μ)! : K) := by
  simpa [Nat.descFactorial_self, Finsupp.univ_sum_single] using
    coeff_ofFn_prod id Function.injective_id ⇑I P 0

/-- Partial derivatives commute with translation of the variables. -/
private lemma pderiv_aeval_C_add_X (x : Fin m → K) (μ : Fin m) (Q : MvPolynomial (Fin m) K) :
    pderiv μ (aeval (fun ν => C (x ν) + X ν) Q) = aeval (fun ν => C (x ν) + X ν) (pderiv μ Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ν hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add]
    by_cases h : ν = μ
    · subst h; simp
    · simp [pderiv_X_of_ne h]

/-- The iterated partial derivative `∂^I` commutes with translation of the variables. -/
private lemma iteratedPDeriv_aeval_C_add_X (x : Fin m → K) (I : Fin m →₀ ℕ)
    (Q : MvPolynomial (Fin m) K) :
    (List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) :
      List (Module.End K (MvPolynomial (Fin m) K))).prod (aeval (fun ν => C (x ν) + X ν) Q) =
      aeval (fun ν => C (x ν) + X ν) ((List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) :
        List (Module.End K (MvPolynomial (Fin m) K))).prod Q) := by
  have : Commute (List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) :
      List (Module.End K (MvPolynomial (Fin m) K))).prod
      (aeval (fun ν => C (x ν) + X ν)).toLinearMap :=
    Commute.list_prod_left _ _ fun _ ha => by
      obtain ⟨μ, rfl⟩ := List.mem_ofFn.mp ha
      exact .pow_left (LinearMap.ext (pderiv_aeval_C_add_X x μ)) _
  exact LinearMap.congr_fun this.eq Q

/-- Evaluating the translate `R(x + τ)` at `τ = 0` gives `R(x)`. -/
private lemma eval_zero_aeval_C_add_X (x : Fin m → K) (R : MvPolynomial (Fin m) K) :
    eval 0 (aeval (fun ν => C (x ν) + X ν) R) = eval x R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ν hp =>
    simp only [map_mul, map_add, hp, aeval_X, eval_C, eval_X, Pi.zero_apply, add_zero]

end

/-- **Taylor expansion** of a multivariate polynomial over a field of characteristic `0`: the
coefficient of `τ^I` in `Q(x + τ)` is the divided derivative `∂_I Q` evaluated at `x`, i.e.
`(∏ μ, (I μ)!)⁻¹ * (∂^{I} Q)(x)`. -/
@[faltings "lem_bvr_taylor_expansion"]
public theorem coeff_aeval_C_add_X {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (Q : MvPolynomial (Fin m) K) (x : Fin m → K) (I : Fin m →₀ ℕ) :
    (aeval (fun μ => C (x μ) + X μ) Q).coeff I =
      (∏ μ, ((I μ)! : K))⁻¹ *
        eval x ((List.ofFn fun μ => (pderiv μ).toLinearMap ^ (I μ) : List (Module.End K _)).prod
          Q) := by
  rw [← eval_zero_aeval_C_add_X, ← iteratedPDeriv_aeval_C_add_X, eval_zero, constantCoeff_eq,
    coeff_zero_iteratedPDeriv, mul_left_comm,
    inv_mul_cancel₀ (by simp [Finset.prod_ne_zero_iff, Nat.factorial_ne_zero]), mul_one]

end Faltings.MvPolynomial
