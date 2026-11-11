module
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Coefficients of iterated partial derivatives

For a polynomial `P ∈ K[X₁, …, Xₘ]` the coefficient of `X^J` in `∂ᵏ/∂X_μᵏ P` is the coefficient
of `X^{J + k e_μ}` in `P` times the falling factorial `(J_μ + k)(J_μ + k - 1) ⋯ (J_μ + 1)`.
Iterating over distinct variables, the coefficient of `X^J` in
`∂^{k₁}/∂X_{g₁}^{k₁} ⋯ ∂^{kₙ}/∂X_{gₙ}^{kₙ} P` is the coefficient of `X^{J + ∑ᵢ kᵢ e_{gᵢ}}` in `P`
times `∏ᵢ (J_{gᵢ} + kᵢ)(J_{gᵢ} + kᵢ - 1) ⋯ (J_{gᵢ} + 1)`.

## Main results

* `Faltings.MvPolynomial.coeff_pderiv_pow`: the coefficients of `(pderiv μ) ^ k P`.
* `Faltings.MvPolynomial.coeff_ofFn_prod`: the coefficients of a product of powers of partial
  derivatives in distinct variables.

## Implementation notes

The iterated partial derivative is the product, in `Module.End K`, of the powers
`(MvPolynomial.pderiv (g i)) ^ (k i)` taken in the order `i = 0, …, n - 1`, and the falling
factorial is `Nat.descFactorial`.
-/

public section

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- The coefficient of `X^J` in `∂ᵏ/∂X_μᵏ P` is the coefficient of `X^{J + k e_μ}` in `P` times
the falling factorial `(J μ + k).descFactorial k`. -/
lemma coeff_pderiv_pow (μ : Fin m) (k : ℕ) (P : MvPolynomial (Fin m) K) (J : Fin m →₀ ℕ) :
    (((pderiv μ).toLinearMap ^ k : Module.End K _) P).coeff J =
      P.coeff (J + Finsupp.single μ k) * ((J μ + k).descFactorial k : K) := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Derivation.coeFn_coe, coeff_pderiv, add_assoc,
      ← Finsupp.single_add]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [show J μ + (k + 1) = (J μ + k) + 1 by omega, Nat.succ_descFactorial_succ]
    push_cast; ring

/-- The coefficients of a product of powers of partial derivatives in distinct variables: the
coefficient of `X^J` in `∏ᵢ (∂/∂X_{g i})^{k i} P` is the coefficient of `X^{J + ∑ᵢ k i • e_{g i}}`
in `P` times `∏ᵢ (J (g i) + k i).descFactorial (k i)`. -/
lemma coeff_ofFn_prod {n : ℕ} (g : Fin n → Fin m) (hg : Function.Injective g)
    (k : Fin n → ℕ) (P : MvPolynomial (Fin m) K) (J : Fin m →₀ ℕ) :
    ((List.ofFn fun i => (pderiv (g i)).toLinearMap ^ (k i) :
        List (Module.End K _)).prod P).coeff J =
      P.coeff (J + ∑ i, Finsupp.single (g i) (k i)) *
        ∏ i, ((J (g i) + k i).descFactorial (k i) : K) := by
  induction n generalizing J with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, coeff_pderiv_pow,
      ih (fun i => g i.succ) (hg.comp (Fin.succ_injective _)), Fin.sum_univ_succ,
      Fin.prod_univ_succ]
    have hJ (i : Fin n) : (J + Finsupp.single (g 0) (k 0)) (g i.succ) = J (g i.succ) := by
      simp [hg.ne (Fin.succ_ne_zero i).symm]
    simp only [hJ, add_assoc]
    ring

end Faltings.MvPolynomial

end
