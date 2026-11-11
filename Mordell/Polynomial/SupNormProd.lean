module
public import Mordell.Polynomial.CoeffNorm

/-!
# An upper bound for the coefficients of a product

Let `f_1, …, f_k` be nonzero polynomials in `t_1, …, t_n`, `f = f_1 ⋯ f_k`, and let
`d' = ∑_μ deg_{t_μ}(f_1 ⋯ f_{k-1})` be the sum of the partial degrees of the product of all
factors but one. Then `ℓ^∞(f) ≤ 2^{d'} ∏_j ℓ^∞(f_j)`. Each coefficient of `f` is a sum of
products of coefficients of the `f_j`; once the exponents taken from the first `k - 1` factors
are chosen the last is determined, and there are at most `∏_{j<k} ∏_μ (1 + deg_{t_μ} f_j)`
such choices, which is at most `2^{d'}` because `1 + a ≤ 2^a` and partial degrees are additive
over a ring without zero divisors.

## Main results

* `Faltings.MvPolynomial.supNorm_prod_le_two_pow_mul_prod_supNorm`: for nonzero `f_j`,
  `j ∈ s`, and `i ∈ s`, `ℓ^∞(∏_{j ∈ s} f_j) ≤ 2^{d'} ∏_{j ∈ s} ℓ^∞(f_j)`, where
  `d' = ∑_μ deg_{t_μ} (∏_{j ∈ s \ {i}} f_j)`.

## Implementation notes

The factors are indexed by a `Finset` of an arbitrary type, with a distinguished member `i`
playing the role of the last factor `f_k`; the variables are indexed by an arbitrary finite
type `σ`; the coefficients lie in a normed commutative ring without zero divisors. The source's
case is `R = ℂ`, `σ = Fin n`, `s = {1, …, k}`, `i = k`; for `k = 1` the product over
`s \ {i}` is `1` and `d' = 0`. The partial degree `deg_{t_μ}` is `MvPolynomial.degreeOf μ`, and
`ℓ^∞` is `Faltings.MvPolynomial.supNorm`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022], proof of Theorem 1.3.4.
-/

namespace Faltings

namespace MvPolynomial

section Helpers

variable {σ R : Type*} [Fintype σ] [SeminormedCommRing R]

/-- A polynomial has at most `∏_μ (deg_{t_μ} g + 1)` monomials. -/
private theorem card_support_le (g : _root_.MvPolynomial σ R) :
    g.support.card ≤ ∏ μ : σ, (g.degreeOf μ + 1) := by
  classical
  have hmaps : ∀ a ∈ g.support, (⇑a : σ → ℕ) ∈
      Fintype.piFinset (fun μ : σ => Finset.range (g.degreeOf μ + 1)) := fun a ha =>
    Fintype.mem_piFinset.2 fun μ =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (_root_.MvPolynomial.monomial_le_degreeOf μ ha))
  simpa [Fintype.card_piFinset] using
    Finset.card_le_card_of_injOn _ hmaps fun a _ b _ h => DFunLike.coe_injective h

private theorem prod_degreeOf_add_one_le_two_pow (g : _root_.MvPolynomial σ R) :
    ∏ μ : σ, (g.degreeOf μ + 1) ≤ 2 ^ (∑ μ : σ, g.degreeOf μ) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' fun μ _ => Nat.lt_two_pow_self

/-- Each coefficient of `g * h` is a sum over the support of `g` of products of a coefficient
of `g` and a coefficient of `h`. -/
private theorem supNorm_mul_le_card_support_mul (g h : _root_.MvPolynomial σ R) :
    supNorm (g * h) ≤ g.support.card * (supNorm g * supNorm h) := by
  have h0 : 0 ≤ supNorm g * supNorm h := mul_nonneg (supNorm_nonneg g) (supNorm_nonneg h)
  rw [supNorm_le_iff (mul_nonneg (Nat.cast_nonneg _) h0)]
  intro E
  conv_lhs => rw [g.as_sum, Finset.sum_mul, _root_.MvPolynomial.coeff_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [_root_.MvPolynomial.coeff_monomial_mul']
  split_ifs
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_coeff_le_supNorm _ _)
      (norm_coeff_le_supNorm _ _) (norm_nonneg _) (supNorm_nonneg _))
  · simpa using h0

private theorem supNorm_mul_le (g h : _root_.MvPolynomial σ R) :
    supNorm (g * h) ≤ (2 : ℝ) ^ (∑ μ : σ, g.degreeOf μ) * (supNorm g * supNorm h) :=
  (supNorm_mul_le_card_support_mul g h).trans <| mul_le_mul_of_nonneg_right
    (by exact_mod_cast (card_support_le g).trans (prod_degreeOf_add_one_le_two_pow g))
    (mul_nonneg (supNorm_nonneg g) (supNorm_nonneg h))

/-- Iterating `supNorm_mul_le` over the factors `f j`, `j ∈ t`, of `(∏_{j ∈ t} f_j) * h`. -/
private theorem supNorm_prod_mul_le {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (f : ι → _root_.MvPolynomial σ R) (h : _root_.MvPolynomial σ R) :
    supNorm ((∏ j ∈ t, f j) * h) ≤
      (2 : ℝ) ^ (∑ j ∈ t, ∑ μ : σ, (f j).degreeOf μ) *
        ((∏ j ∈ t, supNorm (f j)) * supNorm h) := by
  induction t using Finset.induction_on generalizing h with
  | empty => simp
  | insert a t ha ih =>
    have hp : 0 ≤ ∏ j ∈ t, supNorm (f j) := Finset.prod_nonneg fun j _ => supNorm_nonneg _
    rw [Finset.prod_insert ha, mul_comm (f a), mul_assoc, Finset.prod_insert ha,
      Finset.sum_insert ha, pow_add]
    refine (ih _).trans ?_
    calc _ ≤ (2 : ℝ) ^ (∑ j ∈ t, ∑ μ : σ, (f j).degreeOf μ) * ((∏ j ∈ t, supNorm (f j)) *
          ((2 : ℝ) ^ (∑ μ : σ, (f a).degreeOf μ) * (supNorm (f a) * supNorm h))) := by
          gcongr; exact supNorm_mul_le (f a) h
      _ = _ := by ring

end Helpers

/-- **Upper bound for the coefficients of a product.** For nonzero polynomials `f_j`, `j ∈ s`,
over a normed commutative ring without zero divisors, and any `i ∈ s`, with
`d' = ∑_μ deg_{t_μ} (∏_{j ∈ s \ {i}} f_j)`,
`ℓ^∞(∏_{j ∈ s} f_j) ≤ 2^{d'} ∏_{j ∈ s} ℓ^∞(f_j)`, where `ℓ^∞` is
`Faltings.MvPolynomial.supNorm`. -/
@[faltings "lem_ht_coefficient_product_upper"]
public theorem supNorm_prod_le_two_pow_mul_prod_supNorm {σ ι R : Type*} [Fintype σ]
    [DecidableEq ι] [NormedCommRing R] [NoZeroDivisors R]
    (s : Finset ι) (f : ι → _root_.MvPolynomial σ R) (hf : ∀ j ∈ s, f j ≠ 0)
    {i : ι} (hi : i ∈ s) :
    supNorm (∏ j ∈ s, f j) ≤
      (2 : ℝ) ^ (∑ μ : σ, (∏ j ∈ s.erase i, f j).degreeOf μ) * ∏ j ∈ s, supNorm (f j) := by
  have hdeg : ∑ μ : σ, (∏ j ∈ s.erase i, f j).degreeOf μ =
      ∑ j ∈ s.erase i, ∑ μ : σ, (f j).degreeOf μ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => _root_.MvPolynomial.degreeOf_prod_eq _ _
      fun j hj => hf j (Finset.mem_of_mem_erase hj)
  rw [← Finset.prod_erase_mul _ _ hi, ← Finset.prod_erase_mul _ _ hi, hdeg]
  exact supNorm_prod_mul_le _ f (f i)

end MvPolynomial

end Faltings
