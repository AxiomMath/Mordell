module
public import Mordell.Polynomial.PowerSeries.DividedDeriv

/-!
# The coefficient identity for a power-series solution of `p(X, Y) = 0`

Let `K` be a field of characteristic `0`, `p = ∑ p_{ij} X^i Y^j ∈ K[X, Y]` and `ξ ∈ K⟦ς⟧` with
`p(ξ, ς) = 0`. Comparing coefficients of `ς^l` (`l ≥ 1`) in `p(ξ, ς)` by the Cauchy product gives
`0 = p_X(ξ(0), 0) ∂_l ξ(0) + ∑_{i,j} p_{ij} ∑^* ∂_{l₀}(ς^j)(0) ∂_{l₁}ξ(0) ⋯ ∂_{l_i}ξ(0)`,
where `∑^*` runs over the tuples `(l₀, …, l_i)` with `l₀ + ⋯ + l_i = l` and `l_λ < l` for
`λ ≥ 1`. This is the recursion expressing `∂_l ξ(0)` through lower divided derivatives.

## Main results

* `Faltings.PowerSeries.constantCoeff_dividedDerivative_branch_identity`: the identity above.

## Implementation notes

The polynomial `p ∈ K[X, Y]` is an `MvPolynomial (Fin 2) K`, with `X = X 0` and `Y = X 1`;
`p(ξ, ς)` is `MvPolynomial.aeval ![ξ, PowerSeries.X] p`, the partial derivative `p_X` is
`MvPolynomial.pderiv 0 p`, and `p_{ij}` is the coefficient of the monomial
`single 0 i + single 1 j`.
The sum over `(i, j)` runs over the monomials `m` of the support of `p`, with `i = m 0`, `j = m 1`.
A tuple `(l₀, …, l_i)` is a function `Fin (i + 1) → ℕ`, taken from
`Finset.Nat.antidiagonalTuple (i + 1) l` (the tuples summing to `l`); the evaluation `f(0)` of a
power series is `PowerSeries.constantCoeff`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 5
-/

namespace Faltings.PowerSeries

open _root_.PowerSeries Finset

private theorem coeff_prod_antidiagonalTuple {R : Type*} [CommSemiring R] {n : ℕ}
    (f : Fin n → R⟦X⟧) (l : ℕ) :
    coeff l (∏ i, f i) = ∑ t ∈ Nat.antidiagonalTuple n l, ∏ i, coeff (t i) (f i) := by
  classical
  rw [coeff_prod]
  refine Finset.sum_nbij' (fun g => ⇑g) (fun t => Finsupp.equivFunOnFinite.symm t) (fun g hg => ?_)
    (fun t ht => ?_) (fun g _ => by simp) (fun t _ => by simp) fun g _ => rfl
  · simp only [mem_finsuppAntidiag, Nat.mem_antidiagonalTuple] at hg ⊢
    exact hg.1
  · simp only [mem_finsuppAntidiag, Nat.mem_antidiagonalTuple] at ht ⊢
    exact ⟨by simpa using ht, by simp⟩

private theorem filter_not_lt_eq_image (i l : ℕ) :
    (Nat.antidiagonalTuple (i + 1) l).filter (fun t => ¬ ∀ k : Fin i, t k.succ < l) =
      univ.image (fun k : Fin i => (Pi.single k.succ l : Fin (i + 1) → ℕ)) := by
  ext t
  simp only [mem_filter, Nat.mem_antidiagonalTuple, mem_image, mem_univ, true_and, not_forall,
    not_lt]
  constructor
  · rintro ⟨hs, k, hk⟩
    have hkl : t k.succ = l :=
      (hs ▸ single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)).antisymm hk
    have hrest : ∑ m ∈ univ.erase k.succ, t m = 0 := by
      have := add_sum_erase univ t (mem_univ k.succ)
      omega
    rw [sum_eq_zero_iff] at hrest
    refine ⟨k, funext fun m => ?_⟩
    by_cases hm : m = k.succ
    · simp [hm, hkl]
    · rw [Pi.single_eq_of_ne hm, hrest m (mem_erase.2 ⟨hm, mem_univ _⟩)]
  · rintro ⟨k, rfl⟩
    exact ⟨by simp, k, by simp⟩

/-- The tuples of `Nat.antidiagonalTuple (i + 1) l` with some `t k.succ = l` contribute
`[j = 0] i a₀^{i-1} aₗ` to the Cauchy-product coefficient of `ςˡ` in `ξ^i ς^j`. -/
private theorem sum_filter_not_lt {K : Type*} [Field K] (ξ : K⟦X⟧) (i j : ℕ) {l : ℕ}
    (hl : 1 ≤ l) :
    ∑ t ∈ (Nat.antidiagonalTuple (i + 1) l).filter (fun t => ¬ ∀ k : Fin i, t k.succ < l),
      (if t 0 = j then (1 : K) else 0) * ∏ k : Fin i, coeff (t k.succ) ξ =
      (if j = 0 then (i : K) * constantCoeff ξ ^ (i - 1) else 0) * coeff l ξ := by
  classical
  rw [filter_not_lt_eq_image, sum_image fun k₁ _ k₂ _ h => by
    simpa [Pi.single_apply, Nat.one_le_iff_ne_zero.1 hl] using congrFun h k₁.succ]
  simp [Pi.single_apply, apply_ite (coeff · ξ), prod_ite, filter_eq', filter_ne', card_erase_of_mem,
    Fin.succ_ne_zero, eq_comm (a := 0) (b := j)]
  split_ifs <;> ring

private theorem coeff_pow_mul_X_pow {K : Type*} [Field K] (ξ : K⟦X⟧) (i j l : ℕ) :
    coeff l (ξ ^ i * X ^ j) = ∑ t ∈ Nat.antidiagonalTuple (i + 1) l,
      (if t 0 = j then (1 : K) else 0) * ∏ k : Fin i, coeff (t k.succ) ξ := by
  have : ξ ^ i * X ^ j =
      ∏ k : Fin (i + 1), (Fin.cons (X ^ j) (fun _ : Fin i => ξ) : Fin (i + 1) → K⟦X⟧) k := by
    rw [Fin.prod_univ_succ]; simp [mul_comm]
  rw [this, coeff_prod_antidiagonalTuple]
  refine sum_congr rfl fun t _ => ?_
  rw [Fin.prod_univ_succ]
  simp [coeff_X_pow]

/-- For `l ≥ 1`, the coefficient of `ςˡ` in `ξ^i ς^j` splits into the term linear in `aₗ` and
the Cauchy-product terms in which every `l_λ` (`λ ≥ 1`) is `< l`. -/
private theorem coeff_pow_mul_X_pow_of_one_le {K : Type*} [Field K] (ξ : K⟦X⟧) (i j : ℕ) {l : ℕ}
    (hl : 1 ≤ l) :
    coeff l (ξ ^ i * X ^ j) =
      (if j = 0 then (i : K) * constantCoeff ξ ^ (i - 1) else 0) * coeff l ξ +
        ∑ t ∈ (Nat.antidiagonalTuple (i + 1) l).filter (fun t => ∀ k : Fin i, t k.succ < l),
          (if t 0 = j then (1 : K) else 0) * ∏ k : Fin i, coeff (t k.succ) ξ := by
  rw [coeff_pow_mul_X_pow, ← sum_filter_add_sum_filter_not _ (fun t => ∀ k : Fin i, t k.succ < l),
    sum_filter_not_lt ξ i j hl, add_comm]

private theorem eval_pderiv_zero {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) (a : K) :
    MvPolynomial.eval ![a, 0] (MvPolynomial.pderiv 0 p) =
      ∑ m ∈ p.support,
        p.coeff m * (if m 1 = 0 then (m 0 : K) * a ^ (m 0 - 1) else 0) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  refine sum_congr rfl fun m _ => ?_
  split_ifs with h <;> simp [h, mul_assoc]

private theorem coeff_aeval {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) (ξ : K⟦X⟧) (l : ℕ) :
    coeff l (MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p) =
      ∑ m ∈ p.support, p.coeff m * coeff l (ξ ^ m 0 * X ^ m 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  refine sum_congr rfl fun m _ => ?_
  simp

/-- If `ξ ∈ K⟦ς⟧` solves `p(ξ, ς) = 0` for `p ∈ K[X, Y]`, then for `l ≥ 1`,
`0 = p_X(ξ(0), 0) ∂_l ξ(0) + ∑_{i,j} p_{ij} ∑^* ∂_{l₀}(ς^j)(0) ∏_{λ ≥ 1} ∂_{l_λ} ξ(0)`, where `∑^*`
runs over `(l₀, …, l_i)` with `l₀ + ⋯ + l_i = l` and `l_λ < l` for `λ ≥ 1`. -/
@[faltings "lem_bvs_branch_coefficient_identity"]
public theorem constantCoeff_dividedDerivative_branch_identity {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 2) K) (ξ : K⟦X⟧)
    (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0) {l : ℕ} (hl : 1 ≤ l) :
    0 = MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p) *
          constantCoeff (dividedDerivative K l ξ) +
        ∑ m ∈ p.support, p.coeff m *
          ∑ t ∈ (Finset.Nat.antidiagonalTuple (m 0 + 1) l).filter
              (fun t => ∀ k : Fin (m 0), t k.succ < l),
            constantCoeff (dividedDerivative K (t 0) ((X : K⟦X⟧) ^ m 1)) *
              ∏ k : Fin (m 0), constantCoeff (dividedDerivative K (t k.succ) ξ) := by
  have h := congrArg (coeff l) hp
  simp only [coeff_aeval, map_zero, coeff_pow_mul_X_pow_of_one_le _ _ _ hl, mul_add,
    sum_add_distrib] at h
  simp only [constantCoeff_dividedDerivative, coeff_X_pow, eval_pderiv_zero, sum_mul, mul_assoc]
  exact h.symm

end Faltings.PowerSeries
