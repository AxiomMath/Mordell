module

public import Mathlib
public import Mordell.Attr
public import Mordell.Height.Polynomial.Basic
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Polynomial.Local.ProdUpper
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Weil.LocalHeight
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue
public import Mordell.Height.Polynomial.Sum

/-!
# An upper bound for the height of a vector of products of polynomials

Let `A` be a finite set and, for `a ∈ A` and `j` in a finite index set, let `P^{(a)}_j` be
polynomials in finitely many variables over an algebraic extension `K` of `ℚ`, such that for each
`j` the vector `(P^{(a)}_j)_{a ∈ A}` is not zero and the vector `(∏_j P^{(a)}_j)_{a ∈ A}` is not
zero. Fix one factor `j₀`. If `d` bounds the sum of the partial degrees of the partial product
`∏_{j ≠ j₀} P^{(a)}_j` for every `a` for which this partial product is nonzero, then
`h((∏_j P^{(a)}_j)_a) ≤ ∑_j h((P^{(a)}_j)_a) + d log 2`. At every place the coefficient norm of
`∏_j P^{(a)}_j` is at most `2^d` (archimedean places) or `1` (finite places) times the product of
the coefficient norms of the factors; take the maximum over `a` and sum over the places.

## Main results

* `Faltings.polynomialFamilyHeight_prod_le`: the bound
  `h((∏_j P a j)_a) ≤ ∑_j h((P a j)_a) + d log 2`.

## Implementation notes

The source takes `K = ℚ̄`, the variables `x_1, …, x_m` and the factors indexed by `{1, …, k}`,
with the partial degrees bounded for the product of the first `k - 1` factors. Here `K / ℚ` is
any algebraic extension, the variables form an arbitrary finite type `σ`, the factors an
arbitrary finite type `ι`, and the factor left out of the degree bound is an arbitrary `j₀ : ι`
(the source's choice is `j₀ = k`). The bound `d` is a real number; it is nonnegative under the
hypotheses. The partial degree `deg_{x_μ}` is `MvPolynomial.degreeOf μ`, and the heights are
`Faltings.polynomialFamilyHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
-/

@[expose] public section

namespace Faltings

open _root_.MvPolynomial

section Helpers

variable {F : Type*} [Field F] [NumberField F]

/-- `1 ≤ |2|_w ^ ε_w`. -/
private theorem one_le_normalizedAbv_two_pow (w : NumberFieldPlace F) :
    1 ≤ w.normalizedAbv 2 ^ w.archimedeanIndicator := by
  rcases w with w | w
  · simp
  · simpa using (NumberFieldPlace.normalizedAbv_natCast_inr w (w.comap (algebraMap ℚ F)) ⟨rfl⟩
      (r := 2) (by norm_num)).2

omit [NumberField F] in
/-- `Faltings.coeffVector_ne_zero_of_algebraMap` for a family given by models `Q a` over `F`. -/
private theorem coeffVector_ne_zero_of_map {K : Type*} [Field K] {σ A : Type*} [Algebra F K]
    (P : A → MvPolynomial σ K) (hP : ∃ a, P a ≠ 0) (Q : A → MvPolynomial σ F)
    (hQ : ∀ a, map (algebraMap F K) (Q a) = P a) :
    (fun p : Σ a, (P a).support => (Q p.1).coeff p.2.1) ≠ 0 :=
  coeffVector_ne_zero_of_algebraMap hP fun p => by rw [← coeff_map, hQ]

/-- `Faltings.polynomialFamilyHeight_eq_sumLocalHeight` for a family given by models `Q a`
over `F`. -/
private theorem polynomialFamilyHeight_eq_sumLocalHeight_of_map {K : Type*} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {σ A : Type*} [Fintype A] [Algebra F K]
    (P : A → MvPolynomial σ K) (hP : ∃ a, P a ≠ 0) (Q : A → MvPolynomial σ F)
    (hQ : ∀ a, map (algebraMap F K) (Q a) = P a) :
    polynomialFamilyHeight P hP =
      sumLocalHeight fun p : Σ a, (P a).support => (Q p.1).coeff p.2.1 :=
  polynomialFamilyHeight_eq_sumLocalHeight P hP _ fun p => by rw [← coeff_map, hQ]

/-- Every coefficient of a member of a family is bounded by the size of the coefficient vector
of the family. -/
private theorem mvPolynomialAbv_le_vectorAbv {K : Type*} [Field K] {σ A : Type*} [Finite A]
    [Algebra F K] (w : NumberFieldPlace F) (P : A → MvPolynomial σ K) (Q : A → MvPolynomial σ F)
    (hQ : ∀ a, map (algebraMap F K) (Q a) = P a) (a : A) :
    NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => Q a) ≤
      w.vectorAbv (fun p : Σ a, (P a).support => (Q p.1).coeff p.2.1) := by
  refine ciSup_le fun _ => ciSup_le fun I => ?_
  by_cases hI : I ∈ (P a).support
  · exact NumberFieldPlace.normalizedAbv_le_vectorAbv w
      (fun p : Σ a, (P a).support => (Q p.1).coeff p.2.1) ⟨a, I, hI⟩
  · have h0 : (Q a).coeff I = 0 := (algebraMap F K).injective <| by
      rw [← coeff_map, hQ, notMem_support_iff.mp hI, map_zero]
    rw [h0, NumberFieldPlace.normalizedAbv_zero]
    exact NumberFieldPlace.vectorAbv_nonneg w _

/-- The local bound: at a place `w` of `F`, the size of the coefficient vector of `(∏_j P a j)_a`
is at most `(|2|_w ^ ε_w) ^ d` times the product of the sizes of the coefficient vectors of the
`(P a j)_a`. -/
private theorem vectorAbv_coeffVector_prod_le {K : Type*} [Field K] {σ A ι : Type*} [Fintype σ]
    [Finite A] [Fintype ι] [DecidableEq ι] [Algebra F K] (w : NumberFieldPlace F)
    (P : A → ι → MvPolynomial σ K) (Q : A → ι → MvPolynomial σ F)
    (hQ : ∀ a j, map (algebraMap F K) (Q a j) = P a j) (j₀ : ι) (d : ℝ)
    (hd : ∀ a, ∏ j ∈ Finset.univ.erase j₀, P a j ≠ 0 →
      ((∑ μ : σ, (∏ j ∈ Finset.univ.erase j₀, P a j).degreeOf μ : ℕ) : ℝ) ≤ d) :
    w.vectorAbv (fun p : Σ a, (∏ j, P a j).support => (∏ j, Q p.1 j).coeff p.2.1) ≤
      (w.normalizedAbv 2 ^ w.archimedeanIndicator) ^ d *
        ∏ j, w.vectorAbv (fun p : Σ a, (P a j).support => (Q p.1 j).coeff p.2.1) := by
  have hinj := (algebraMap F K).injective
  have hQprod : ∀ a (s : Finset ι), map (algebraMap F K) (∏ j ∈ s, Q a j) = ∏ j ∈ s, P a j :=
    fun a s => by simp [map_prod, hQ]
  have hB := one_le_normalizedAbv_two_pow w
  refine Real.iSup_le (fun ⟨a, I, hI⟩ => ?_) (mul_nonneg (by positivity)
    (Finset.prod_nonneg fun j _ => NumberFieldPlace.vectorAbv_nonneg w _))
  have hPa : ∀ j ∈ Finset.univ, P a j ≠ 0 :=
    Finset.prod_ne_zero_iff.mp fun h => by simp [h] at hI
  have hQa : ∀ j ∈ Finset.univ, Q a j ≠ 0 := fun j hj h => hPa j hj (by rw [← hQ, h, map_zero])
  have hn : (Multiset.card (∏ j ∈ Finset.univ.erase j₀, Q a j).degrees : ℝ) ≤ d := by
    have := hd a (Finset.prod_ne_zero_iff.mpr fun j hj => hPa j (Finset.mem_of_mem_erase hj))
    rwa [← hQprod, ← card_degrees_eq_sum_degreeOf, degrees_map_of_injective _ hinj] at this
  obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv w
  calc w.normalizedAbv ((∏ j, Q a j).coeff I)
      ≤ NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => ∏ j, Q a j) :=
        NumberFieldPlace.normalizedAbv_coeff_le_mvPolynomialAbv _ _ _
    _ ≤ w.normalizedAbv ((2 : F) ^ Multiset.card (∏ j ∈ Finset.univ.erase j₀, Q a j).degrees) ^
          w.archimedeanIndicator *
            ∏ j, NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => Q a j) :=
        NumberFieldPlace.mvPolynomialAbv_prod_le w Finset.univ (Finset.mem_univ j₀) (Q a) hQa
    _ ≤ _ := by
      rw [← hv, map_pow, hv, ← pow_mul, mul_comm (Multiset.card _), pow_mul, ← Real.rpow_natCast]
      exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hB hn)
        (Finset.prod_le_prod₀ (fun j _ => w.mvPolynomialAbv_nonneg _) fun j _ =>
          mvPolynomialAbv_le_vectorAbv w (fun a => P a j) (fun a => Q a j) (fun a => hQ a j) a)
        (Finset.prod_nonneg fun j _ => w.mvPolynomialAbv_nonneg _) (by positivity)

/-- If at every place `|x|_w ≤ (|2|_w ^ ε_w) ^ d ∏_j |y_j|_w`, then
`S(x) ≤ ∑_j S(y_j) + d log 2`. -/
private theorem sumLocalHeight_le_of_vectorAbv_le {κ ι : Type*} [Finite κ] [Fintype ι]
    {κ' : ι → Type*} [∀ j, Finite (κ' j)] {x : κ → F} (hx : x ≠ 0) {y : ∀ j, κ' j → F}
    (hy : ∀ j, y j ≠ 0) (d : ℝ)
    (h : ∀ w : NumberFieldPlace F, w.vectorAbv x ≤
      (w.normalizedAbv 2 ^ w.archimedeanIndicator) ^ d * ∏ j, w.vectorAbv (y j)) :
    sumLocalHeight x ≤ ∑ j, sumLocalHeight (y j) + d * Real.log 2 := by
  have hloc : ∀ w : NumberFieldPlace F, w.localHeight x ≤ ∑ j, w.localHeight (y j) +
      d * ((w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv 2)) := fun w => by
    have hB := one_le_normalizedAbv_two_pow w
    have hM : ∀ j ∈ Finset.univ, w.vectorAbv (y j) ≠ 0 := fun j _ =>
      (NumberFieldPlace.vectorAbv_pos w (hy j)).ne'
    calc w.localHeight x ≤ Real.log (_ ^ d * ∏ j, w.vectorAbv (y j)) :=
          Real.log_le_log (NumberFieldPlace.vectorAbv_pos w hx) (h w)
      _ = _ := by
          rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr hM),
            Real.log_rpow (by positivity), Real.log_prod hM, Real.log_pow]
          simp only [NumberFieldPlace.localHeight]
          ring
  have hfj : ∀ j, (Function.support fun w : NumberFieldPlace F => w.localHeight (y j)).Finite :=
    fun j => NumberFieldPlace.finite_support_localHeight (hy j)
  have hf2 : (Function.support fun w : NumberFieldPlace F =>
      d * ((w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv 2))).Finite := by
    refine (Set.finite_range Sum.inr).subset ?_
    rintro (w | w) hw
    · simp at hw
    · exact ⟨w, rfl⟩
  have hfs : (Function.support fun w : NumberFieldPlace F => ∑ j, w.localHeight (y j)).Finite :=
    (Set.finite_iUnion hfj).subset fun w hw => by
      by_contra hw'
      simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hw'
      exact hw (by simp [hw'])
  have h2 := NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := F)
    (r := 2) (by norm_num)
  simp only [Int.cast_ofNat] at h2
  unfold sumLocalHeight
  calc ∑ᶠ w : NumberFieldPlace F, w.localHeight x
      ≤ ∑ᶠ w : NumberFieldPlace F, (∑ j, w.localHeight (y j) +
          d * ((w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv 2))) :=
        finsum_le_finsum' (NumberFieldPlace.finite_support_localHeight hx)
          ((hfs.union hf2).subset (Function.support_add _ _)) hloc
    _ = _ := by
        rw [finsum_add_distrib hfs hf2, finsum_sum_comm _ _ fun j _ => hfj j, ← mul_finsum, h2]

end Helpers

/-- **Height of a vector of products.** Let `P a j` be polynomials over an algebraic extension
`K` of `ℚ` in finitely many variables, for `a` in a finite type `A` and `j` in a finite type `ι`,
such that for each `j` the vector `(P a j)_a` is not zero and the vector `(∏_j P a j)_a` is not
zero. Let `j₀ : ι` and let `d` bound the sum `∑_μ deg_{x_μ}` of the partial degrees
`MvPolynomial.degreeOf` of `∏_{j ≠ j₀} P a j` whenever this product is nonzero. Then
`h((∏_j P a j)_a) ≤ ∑_j h((P a j)_a) + d log 2`, where `h` is
`Faltings.polynomialFamilyHeight`. -/
@[faltings "lem_ht_height_product_vectors"]
public theorem polynomialFamilyHeight_prod_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {σ A ι : Type*} [Fintype σ] [Fintype A] [Fintype ι]
    [DecidableEq ι] (P : A → ι → MvPolynomial σ K) (hP : ∀ j, ∃ a, P a j ≠ 0)
    (hprod : ∃ a, ∏ j, P a j ≠ 0) (j₀ : ι) (d : ℝ)
    (hd : ∀ a, ∏ j ∈ Finset.univ.erase j₀, P a j ≠ 0 →
      ((∑ μ : σ, (∏ j ∈ Finset.univ.erase j₀, P a j).degreeOf μ : ℕ) : ℝ) ≤ d) :
    polynomialFamilyHeight (fun a => ∏ j, P a j) hprod ≤
      ∑ j, polynomialFamilyHeight (fun a => P a j) (hP j) + d * Real.log 2 := by
  classical
  -- the number field `F` generated by the coefficients of the `P a j`
  let S : Set K := ⋃ a, ⋃ j, ((P a j).coeffs : Set K)
  let F := IntermediateField.adjoin ℚ S
  have : Finite S := (Set.finite_iUnion fun a => Set.finite_iUnion fun j =>
    (P a j).coeffs.finite_toSet).to_subtype
  have hfin : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin fun r _ =>
    (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  let : NumberField F := { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  have hlift : ∀ a j, ∃ q : MvPolynomial σ F, map (algebraMap F K) q = P a j := fun a j =>
    mem_range_map_iff_coeffs_subset.2 fun x hx =>
      ⟨⟨x, IntermediateField.subset_adjoin ℚ S (Set.mem_iUnion₂.2 ⟨a, j, hx⟩)⟩, rfl⟩
  choose Q hQ using hlift
  have hQprod : ∀ a, map (algebraMap F K) (∏ j, Q a j) = ∏ j, P a j := fun a => by
    simp [map_prod, hQ]
  rw [polynomialFamilyHeight_eq_sumLocalHeight_of_map _ hprod _ hQprod]
  simp_rw [polynomialFamilyHeight_eq_sumLocalHeight_of_map _ (hP _) (fun a => Q a _)
    (fun a => hQ a _)]
  exact sumLocalHeight_le_of_vectorAbv_le (coeffVector_ne_zero_of_map _ hprod _ hQprod)
    (fun j => coeffVector_ne_zero_of_map _ (hP j) _ fun a => hQ a j) d
    fun w => vectorAbv_coeffVector_prod_le w P Q hQ j₀ d hd

end Faltings
