module
public import Mordell.Height.Siegel.Basic

/-!
# Siegel's lemma with a lower bound for the solution space

Let `K` be a number field. There is a constant `c ≥ 0`, depending only on `K`, with the following
property. Let `A` be a `κ × ι` matrix over `K` (the rows are the coefficient vectors of linear
forms `L_i` in `N = #ι` variables), whose kernel in `K^ι` has dimension at least `S > 0`, and let
`H ≥ 0` bound the absolute height of every nonzero row. Then there is a nonzero `x ∈ K^ι` with
`A x = 0` and `h(x) ≤ (N / S) (H + log N + c)`.

This follows from Siegel's lemma in its rank form: if the rows span a space of dimension `r`, the
kernel has dimension `N - r ≥ S`, and the bound `r/(N-r) (H + log N) + c N/(N-r)` is at most
`N/S (H + log N + c)`.

## Main results

* `Faltings.exists_ne_zero_mulVec_eq_zero_logHeight_le`: Siegel's lemma for a solution space of
  dimension at least `S`.

## Implementation notes

The linear forms are the rows of a matrix `A : Matrix κ ι K`, and a linear form is identified
with its coefficient vector, so `h(L_i)` is the height of the row `A i`. The common solution space
is `LinearMap.ker A.mulVecLin`. The absolute height of a vector `v : ι → K` is
`Height.logHeight v / [K : ℚ]`. The constant `c` is chosen before the index types `ι` and `κ`,
so it is uniform in `N` and `M`. The lower bound `S` is allowed to be any positive real number.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8
-/

namespace Faltings

universe u v

open Module Matrix

/-- Rank–nullity for a matrix, with the rank read off the row span. -/
private lemma finrank_span_row_add_finrank_ker {K ι κ : Type*} [Field K] [Fintype ι]
    [Finite κ] (A : Matrix κ ι K) :
    finrank K (Submodule.span K (Set.range A)) + finrank K (LinearMap.ker A.mulVecLin) =
      Fintype.card ι := by
  rw [← Module.finrank_fintype_fun_eq_card K,
    ← LinearMap.finrank_range_add_finrank_ker A.mulVecLin]
  exact congrArg (· + _) A.rank_eq_finrank_span_row.symm

/-- The rank-form bound `r/(N-r) X + c N/(N-r)` is at most `N/S (X + c)` once `S ≤ N - r`. -/
private lemma div_sub_mul_add_le {N r S X c : ℝ} (hS : 0 < S) (hSr : S ≤ N - r) (hr : 0 ≤ r)
    (hX : 0 ≤ X) (hc : 0 ≤ c) : r / (N - r) * X + c * N / (N - r) ≤ N / S * (X + c) := by
  have hNr : 0 < N - r := hS.trans_le hSr
  calc r / (N - r) * X + c * N / (N - r) = r / (N - r) * X + c * (N / (N - r)) := by ring
    _ ≤ N / S * X + c * (N / S) := by
      gcongr <;> linarith
    _ = N / S * (X + c) := by ring

/-- **Siegel's lemma** with a lower bound on the solution space: for a number field `K` there is
`c ≥ 0` such that for every matrix `A : Matrix κ ι K` whose kernel has dimension at least `S > 0`
and whose nonzero rows have absolute height at most `H ≥ 0`, there is a nonzero `x` with
`A *ᵥ x = 0` and `h(x) ≤ (N / S) (H + log N + c)`, where `N = Fintype.card ι`. -/
@[faltings "lem_bvs_siegel_lemma_dimension"]
public theorem exists_ne_zero_mulVec_eq_zero_logHeight_le (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] (A : Matrix κ ι K)
      (S H : ℝ), 0 < S → S ≤ finrank K (LinearMap.ker A.mulVecLin) → 0 ≤ H →
      (∀ i, A i ≠ 0 → Height.logHeight (A i) / finrank ℚ K ≤ H) →
      ∃ x : ι → K, x ≠ 0 ∧ A *ᵥ x = 0 ∧
        Height.logHeight x / finrank ℚ K ≤
          (Fintype.card ι / S) * (H + Real.log (Fintype.card ι) + c) := by
  obtain ⟨c, hc, h⟩ := exists_ne_zero_dotProduct_eq_zero_logHeight_le.{u, v} K
  refine ⟨c, hc, fun {ι κ} _ _ A S H hS hSk hH hA => ?_⟩
  have hrank := finrank_span_row_add_finrank_ker A
  have hSr : S ≤ Fintype.card ι - finrank K (Submodule.span K (Set.range A)) := by
    rw [← hrank]; push_cast; linarith
  have hlt : finrank K (Submodule.span K (Set.range A)) < Fintype.card ι :=
    (Nat.cast_lt (α := ℝ)).mp (by linarith)
  obtain ⟨x, hx0, hx, hbound⟩ := h A H hlt hH hA
  exact ⟨x, hx0, funext hx, hbound.trans <|
    div_sub_mul_add_le hS hSr (by positivity) (add_nonneg hH (Real.log_natCast_nonneg _)) hc⟩

end Faltings
