module
public import Mordell.Roth.Index.Mul

/-!
# The index of a sum

For fixed positive weights `r = (r₁, …, rₘ)` and a point `ς⁰ ∈ Kᵐ`, the index is
superadditive in the ultrametric sense: `ind(Q₁ + Q₂) ≥ min(ind Q₁, ind Q₂)`. This holds because
each divided derivative `∂_I` and evaluation at `ς⁰` are linear, so if
`∂_I (Q₁ + Q₂) (ς⁰) ≠ 0` then `∂_I Q₁ (ς⁰) ≠ 0` or `∂_I Q₂ (ς⁰) ≠ 0`. By induction a lower
bound on the index of every term of a finite sum bounds the index of the sum; together with the
additivity of the index on products, this bounds the index of a determinant by the sum of
column-wise lower bounds on its entries, through the Leibniz expansion.

## Main results

* `Faltings.MvPolynomial.le_index_add`: the index of `Q₁ + Q₂` is at least
  `min (ind Q₁) (ind Q₂)`.
* `Faltings.MvPolynomial.le_index_sum`: a common lower bound on the indices of the terms of a
  finite sum bounds the index of the sum.
* `Faltings.MvPolynomial.le_index_det`: column-wise lower bounds `c ν` on the indices of the
  entries of a square matrix give `∑ ν, c ν ≤ ind (det M)`.

## References

* [Bombieri, *The Mordell conjecture revisited*, §9, p. 634][bombieri1990]
-/

namespace Faltings.MvPolynomial

/-- If a sum is nonzero, one of its summands is. -/
private lemma ne_zero_or_ne_zero_of_add_ne_zero {M : Type*} [AddZeroClass M] {a b : M}
    (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  contrapose! h
  simp [h]

/-- The index of a sum is at least the minimum of the indices:
`min (ind Q₁) (ind Q₂) ≤ ind (Q₁ + Q₂)`, for the index with respect to fixed weights `r` at a
fixed point `ς₀`. -/
@[faltings "lem_bvr_index_sum"]
public theorem le_index_add {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+)
    (ς₀ : Fin m → K) (Q₁ Q₂ : MvPolynomial (Fin m) K) :
    min (index r ς₀ Q₁) (index r ς₀ Q₂) ≤ index r ς₀ (Q₁ + Q₂) := by
  refine le_iInf₂ fun I hI => ?_
  rw [map_add, smul_add, map_add] at hI
  obtain h | h := ne_zero_or_ne_zero_of_add_ne_zero hI
  · exact min_le_of_left_le (iInf₂_le I h)
  · exact min_le_of_right_le (iInf₂_le I h)

section

variable {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+) (ς₀ : Fin m → K)

/-- A common lower bound `c` on the indices of the terms of a finite sum is a lower bound on the
index of the sum. -/
public lemma le_index_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin m) K)
    {c : ENNReal} (h : ∀ i ∈ s, c ≤ index r ς₀ (f i)) : c ≤ index r ς₀ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [index_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans (le_index_add r ς₀ _ _)

/-- If the index of every entry in column `ν` of a square matrix is at least `c ν`, then the
index of its determinant is at least `∑ ν, c ν`: every term of the Leibniz expansion is a signed
product of one entry from each column. -/
public lemma le_index_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial (Fin m) K)) (c : ι → ENNReal)
    (h : ∀ μ ν, c ν ≤ index r ς₀ (M μ ν)) : ∑ ν, c ν ≤ index r ς₀ M.det := by
  rw [Matrix.det_apply]
  refine le_index_sum r ς₀ _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine le_trans ?_ (index_le_index_intCast_mul r ς₀ _ _)
  rw [index_prod]
  exact Finset.sum_le_sum fun ν _ => h (σ ν) ν

end

end Faltings.MvPolynomial
