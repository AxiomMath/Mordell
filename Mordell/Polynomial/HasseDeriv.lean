module
public import Mathlib
public import Mordell.Attr
public import Mordell.Polynomial.IteratedPDeriv

/-!
# Divided (Hasse) derivatives of multivariate polynomials

For a multi-index `I = (i_1, …, i_m)` the divided derivative
`∂_I = (1 / (i_1! ⋯ i_m!)) ∂^{i_1}/∂x_1^{i_1} ⋯ ∂^{i_m}/∂x_m^{i_m}`
acts on polynomials in `x_1, …, x_m`. On monomials it is
`∂_I x^J = (∏_μ (j_μ choose i_μ)) x^{J - I}`, which is zero unless `I ≤ J`
(a binomial coefficient `j choose i` with `i > j` vanishes).

## Main definitions

* `Faltings.MvPolynomial.hasseDeriv I`: the divided derivative `∂_I` as an `R`-linear
  endomorphism of `MvPolynomial σ R`, for a multi-index `I : σ →₀ ℕ`.

## Main results

* `Faltings.MvPolynomial.hasseDeriv_monomial`: the action of `∂_I` on a monomial.
* `Faltings.MvPolynomial.hasseDeriv_eq_inv_prod_factorial_smul`: in characteristic zero,
  `∂_I = (∏_μ (I μ)!)⁻¹ ∏_μ (∂/∂x_μ)^{I μ}`.

## Implementation notes

The source works over `\overline{ℚ}` with variables `x_1, …, x_m`. We define `∂_I` by its action
on monomials, `x^J ↦ (∏_μ (j_μ choose i_μ)) x^{J - I}`, over an arbitrary commutative semiring
`R` and an arbitrary index type `σ`, exactly as `Polynomial.hasseDeriv` does in one variable.
This needs no division, and over a field of characteristic zero it agrees with
`(1 / I!) ∏_μ (∂/∂x_μ)^{i_μ}`, the iterated `MvPolynomial.pderiv` divided by `∏_μ i_μ!`.
The product of binomial coefficients runs over `I.support`, the other factors being
`j choose 0 = 1`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006].
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- The divided (Hasse) derivative `∂_I` with multi-index `I : σ →₀ ℕ`. It is the `R`-linear
map on `MvPolynomial σ R` sending the monomial `x^J` to `(∏_μ (J μ choose I μ)) x^{J - I}`.
In characteristic zero this is `(1 / ∏_μ (I μ)!) ∏_μ (∂/∂x_μ)^{I μ}`. -/
@[expose, faltings "def_ht_divided_derivative"]
public noncomputable def hasseDeriv (I : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  Finsupp.lsum R (fun J : σ →₀ ℕ =>
      ((∏ μ ∈ I.support, (J μ).choose (I μ) : ℕ) : R) • monomial (J - I))
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The divided derivative on a monomial:
`∂_I (r x^J) = (∏_μ (J μ choose I μ)) r x^{J - I}`. -/
public theorem hasseDeriv_monomial (I J : σ →₀ ℕ) (r : R) :
    hasseDeriv I (monomial J r) =
      ((∏ μ ∈ I.support, (J μ).choose (I μ) : ℕ) : R) • monomial (J - I) r := by
  change Finsupp.lsum R _ (Finsupp.single J r) = _
  rw [Finsupp.lsum_single]
  rfl

/-- In characteristic zero the divided derivative is the iterated partial derivative divided by
`I! = ∏_μ (I μ)!`: `∂_I = (∏_μ (I μ)!)⁻¹ ∏_μ (∂/∂x_μ)^{I μ}`, the factors taken in the order
`μ = 0, …, m - 1`. -/
public theorem hasseDeriv_eq_inv_prod_factorial_smul {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (I : Fin m →₀ ℕ) :
    (hasseDeriv I : MvPolynomial (Fin m) K →ₗ[K] MvPolynomial (Fin m) K) =
      (∏ μ, ((I μ).factorial : K))⁻¹ •
        (List.ofFn fun μ => (pderiv μ).toLinearMap ^ I μ :
          List (Module.End K (MvPolynomial (Fin m) K))).prod := by
  refine LinearMap.ext fun P => ?_
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial b r =>
    rw [hasseDeriv_monomial, LinearMap.smul_apply]
    ext c
    have h := coeff_ofFn_prod (K := K) id Function.injective_id ⇑I (monomial b r) c
    simp only [id] at h
    rw [coeff_smul, coeff_smul, h, coeff_monomial, coeff_monomial, Finsupp.univ_sum_single]
    by_cases hb : b = c + I
    · subst hb
      have hfac : (∏ μ, ((I μ).factorial : K)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun μ _ => by exact_mod_cast Nat.factorial_ne_zero _
      have hsupp : ∏ μ ∈ I.support, (((c μ + I μ).choose (I μ) : ℕ) : K) =
          ∏ μ, (((c μ + I μ).choose (I μ) : ℕ) : K) :=
        Finset.prod_subset (Finset.subset_univ _) fun μ _ hμ => by
          rw [Finsupp.notMem_support_iff.mp hμ, Nat.choose_zero_right, Nat.cast_one]
      rw [ite_eq_left (add_tsub_cancel_right c I), ite_eq_left rfl]
      simp only [Finsupp.add_apply, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
        Nat.cast_prod, Finset.prod_mul_distrib, smul_eq_mul]
      rw [hsupp, mul_left_comm r, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul, mul_comm]
    · rw [ite_eq_right hb, zero_mul, smul_zero]
      split_ifs with h
      · have : ¬ ∀ μ, I μ ≤ b μ := by
          intro hle; apply hb; subst h; ext μ; simpa using (Nat.sub_add_cancel (hle μ)).symm
        push Not at this
        obtain ⟨μ, hμ⟩ := this
        have h0 : ∏ ν ∈ I.support, (b ν).choose (I ν) = 0 :=
          Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr (by omega)) (Nat.choose_eq_zero_of_lt hμ)
        rw [h0, Nat.cast_zero, zero_smul]
      · rw [smul_zero]

end Faltings.MvPolynomial
