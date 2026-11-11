module

public import Mordell.Height.Polynomial.Basic
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.Representative

/-!
# An upper bound for the height of a sum of polynomials

Let `P_1, …, P_r` be polynomials over an algebraic extension `K` of `ℚ` whose sum is nonzero.
Then `h(P_1 + ⋯ + P_r) ≤ h(P_1, …, P_r) + log r`. At each place every coefficient of the sum is
a sum of `r` coefficients of the `P_i`, so its absolute value is at most `r` (at the archimedean
places) or `1` (at the finite places) times the largest coefficient of the family; summing the
logarithms over the places gives the inequality of heights.

## Main results

* `Faltings.mvPolynomialHeight_sum_le`: for a finite family `P` with `∑ i, P i ≠ 0`,
  `h(∑ i, P i) ≤ h(P) + log (card ι)`.
* `Faltings.polynomialFamilyHeight_eq_sumLocalHeight`: the height of a family of polynomials is
  the sum of local heights of its coefficient vector over a number field containing the
  coefficients.

## Implementation notes

The source takes `K = ℚ̄`, the variables `x_1, …, x_m` and the summands indexed by
`{1, …, r}` with `r ≥ 1`; here `K / ℚ` is any algebraic extension, the variables are indexed by
an arbitrary type `σ` and the summands by an arbitrary finite type `ι`. The condition `r ≥ 1`
follows from the nonvanishing of the sum, and so does the hypothesis that the family is not all
zero, which `Faltings.polynomialFamilyHeight` needs. The height of the sum is
`Faltings.mvPolynomialHeight`, that of the family `Faltings.polynomialFamilyHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

private theorem normalizedAbv_zero {F : Type*} [Field F] [NumberField F] (w : NumberFieldPlace F) :
    w.normalizedAbv 0 = 0 := by
  rcases w with w | w <;>
    simp [Real.zero_rpow, Module.finrank_pos.ne', NumberField.InfinitePlace.mult_ne_zero]

/-- If `|x|_w ≤ |r|_w ^ ε_w · |y|_w` at every place `w` of a number field, for an integer
`r ≥ 1`, then `h(x) ≤ h(y) + log r` for the sums of local heights. -/
private theorem sumLocalHeight_le_add_log {F : Type*} [Field F] [NumberField F] {κ μ : Type*}
    [Finite κ] [Finite μ] {x : κ → F} {y : μ → F} (hx : x ≠ 0) (hy : y ≠ 0) {r : ℤ}
    (hr : 1 ≤ r) (h : ∀ w : NumberFieldPlace F,
      w.vectorAbv x ≤ w.normalizedAbv (r : F) ^ w.archimedeanIndicator * w.vectorAbv y) :
    sumLocalHeight x ≤ sumLocalHeight y + Real.log r := by
  have harch : (Function.support fun w : NumberFieldPlace F =>
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (r : F))).Finite := by
    refine (Set.finite_range (Sum.inr : NumberField.InfinitePlace F → NumberFieldPlace F)).subset ?_
    rintro (w | w) hw
    · simp at hw
    · exact ⟨w, rfl⟩
  rw [sumLocalHeight, sumLocalHeight,
    ← NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := F) hr, add_comm,
    ← finsum_add_distrib harch (NumberFieldPlace.finite_support_localHeight hy)]
  refine finsum_le_finsum' (NumberFieldPlace.finite_support_localHeight hx)
    ((harch.union (NumberFieldPlace.finite_support_localHeight hy)).subset (Function.support_add _ _))
    fun w => ?_
  have := w.normalizedAbv_pos (show (r : F) ≠ 0 by exact_mod_cast (show r ≠ 0 by omega))
  rw [NumberFieldPlace.localHeight, NumberFieldPlace.localHeight, ← Real.log_pow,
    ← Real.log_mul (by positivity) (w.vectorAbv_pos hy).ne']
  exact Real.log_le_log (w.vectorAbv_pos hx) (h w)

/-- The coefficient vector `(coeff_I P_i)_{(i, I)}` of a family of polynomials, not all zero, is
nonzero. -/
theorem coeffVector_ne_zero {K σ ι : Type*} [Field K] {P : ι → MvPolynomial σ K}
    (hP : ∃ i, P i ≠ 0) : (fun p : Σ i, (P i).support => (P p.1).coeff p.2.1) ≠ 0 := by
  obtain ⟨i, hi⟩ := hP
  obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hi
  exact Function.ne_iff.mpr ⟨⟨i, I, MvPolynomial.mem_support_iff.mpr hI⟩, hI⟩

/-- A vector `y` with entries in `F` whose image in `K` is the coefficient vector of a family of
polynomials, not all zero, is nonzero. -/
theorem coeffVector_ne_zero_of_algebraMap {K σ ι F : Type*} [Field K] [Field F] [Algebra F K]
    {P : ι → MvPolynomial σ K} (hP : ∃ i, P i ≠ 0) {y : (Σ i, (P i).support) → F}
    (hy : ∀ p, algebraMap F K (y p) = (P p.1).coeff p.2.1) : y ≠ 0 := fun h =>
  coeffVector_ne_zero hP (funext fun p => by simp [← hy p, h])

/-- The height `Faltings.polynomialFamilyHeight` of a family of polynomials over `K`, not all
zero, is the sum of local heights of its coefficient vector, computed in any number field `F`
over which `K` is an algebra and which contains the coefficients. -/
theorem polynomialFamilyHeight_eq_sumLocalHeight {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype ι] (P : ι → MvPolynomial σ K)
    (hP : ∃ i, P i ≠ 0) {F : Type*} [Field F] [NumberField F] [Algebra F K]
    (y : (Σ i, (P i).support) → F) (hy : ∀ p, algebraMap F K (y p) = (P p.1).coeff p.2.1) :
    polynomialFamilyHeight P hP = sumLocalHeight y := by
  have hcomp : algebraMap F K ∘ y = fun p => (P p.1).coeff p.2.1 := funext hy
  unfold polynomialFamilyHeight
  letI : LinearOrder (Σ i, (P i).support) := IsWellOrder.linearOrder WellOrderingRel
  exact weilHeight_eq_sumLocalHeight (hcomp ▸ coeffVector_ne_zero hP) (by simp_rw [hcomp])

/-- **Height of a sum of polynomials.** For a finite family `P` of polynomials over an algebraic
extension `K` of `ℚ` with nonzero sum, `h(∑ i, P i) ≤ h(P) + log (card ι)`, where the left side is
`Faltings.mvPolynomialHeight` and `h(P)` is `Faltings.polynomialFamilyHeight`. -/
@[faltings "lem_ht_height_of_sum"]
public theorem mvPolynomialHeight_sum_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype ι] (P : ι → MvPolynomial σ K)
    (hP : ∑ i, P i ≠ 0) :
    mvPolynomialHeight (∑ i, P i) hP ≤
      polynomialFamilyHeight P
          (let ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP; ⟨i, hi⟩) +
        Real.log (Fintype.card ι) := by
  classical
  let F := IntermediateField.adjoin ℚ
    (Set.range fun p : Σ i, (P i).support => (P p.1).coeff p.2.1)
  have hfin : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  letI : NumberField F :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  have hmem (i I) : (P i).coeff I ∈ F := by
    by_cases h : I ∈ (P i).support
    · exact IntermediateField.subset_adjoin ℚ _ ⟨⟨i, I, h⟩, rfl⟩
    · rw [MvPolynomial.notMem_support_iff.mp h]; exact zero_mem _
  let a (i : ι) (I : σ →₀ ℕ) : F := ⟨(P i).coeff I, hmem i I⟩
  let yfam : (Σ i, (P i).support) → F := fun p => a p.1 p.2.1
  let ysum : (Σ _ : Unit, (∑ i, P i).support) → F := fun p => ∑ i, a i p.2.1
  have hysum (p : Σ _ : Unit, (∑ i, P i).support) :
      algebraMap F K (ysum p) = (∑ i, P i).coeff p.2.1 := by
    simp [ysum, a, MvPolynomial.coeff_sum]
  have hfam : ∃ i, P i ≠ 0 := by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP; exact ⟨i, hi⟩
  have hsum0 := coeffVector_ne_zero_of_algebraMap (P := fun _ : Unit => ∑ i, P i) ⟨(), hP⟩ hysum
  haveI : Nonempty ι := hfam.nonempty
  rw [mvPolynomialHeight, polynomialFamilyHeight_eq_sumLocalHeight _ _ ysum hysum,
    polynomialFamilyHeight_eq_sumLocalHeight _ _ yfam fun _ => rfl, ← Int.cast_natCast]
  refine sumLocalHeight_le_add_log hsum0 (coeffVector_ne_zero_of_algebraMap hfam fun _ => rfl)
    (Nat.one_le_cast.2 Fintype.card_pos) fun w => ?_
  haveI : Nonempty (Σ _ : Unit, (∑ i, P i).support) := (Function.ne_iff.mp hsum0).nonempty
  refine ciSup_le fun p =>
    (NumberFieldPlace.normalizedAbv_sum_le w Finset.univ_nonempty (a · p.2.1)).trans ?_
  rw [Finset.card_univ, Int.cast_natCast]
  refine mul_le_mul_of_nonneg_left (Finset.sup'_le Finset.univ_nonempty _ fun i _ => ?_)
    (pow_nonneg (NumberFieldPlace.normalizedAbv_nonneg _ _) _)
  by_cases h : p.2.1 ∈ (P i).support
  · exact le_ciSup (f := fun q => w.normalizedAbv (yfam q)) (Set.finite_range _).bddAbove
      ⟨i, p.2.1, h⟩
  · rw [show a i p.2.1 = 0 from Subtype.ext (MvPolynomial.notMem_support_iff.mp h),
      normalizedAbv_zero]
    exact w.vectorAbv_nonneg yfam

end Faltings
