module

public import Mordell.Height.Polynomial.Basic
public import Mordell.Height.Polynomial.Local.ProdLower
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Polynomial.Sum

/-!
# A lower bound for the height of a product of polynomials

Let `P_1, …, P_k` be nonzero polynomials in `x_1, …, x_m` over an algebraic extension `K` of
`ℚ`, let `P = P_1 ⋯ P_k`, and let `d = ∑_μ deg_{x_μ} P` be the sum of the partial degrees of
`P`. Then `∑_j h(P_j) - d log 2 ≤ h(P)`. This is Gelfond's inequality: at each place the
coefficient norm of a product is bounded below by the product of the coefficient norms of the
factors, up to a factor `2^{-d}` at the archimedean places, and summing over the places gives
the inequality of heights.

## Main results

* `Faltings.sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod`: for nonzero `P_j`,
  `∑_j h(P_j) - d log 2 ≤ h(∏_j P_j)`, where `d = ∑_μ deg_{x_μ} (∏_j P_j)`.

## Implementation notes

The source takes `K = ℚ̄`, the variables `x_1, …, x_m` and the factors indexed by
`{1, …, k}`; here `K / ℚ` is any algebraic extension, the variables are indexed by an arbitrary
finite type `σ` and the factors by an arbitrary finite type `ι`. The partial degree `deg_{x_μ}`
is `MvPolynomial.degreeOf μ`, and `h` is `Faltings.mvPolynomialHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022], Theorem 1.3.4.
-/

@[expose] public section

namespace Faltings

/-- The local size of a polynomial is the absolute value of the vector of its coefficients,
indexed by any finite type covering the support. -/
theorem mvPolynomialAbv_eq_vectorAbv {F : Type*} [Field F] [NumberField F] {σ ι : Type*}
    [Finite ι] [Nonempty ι] (w : NumberFieldPlace F) (Q : MvPolynomial σ F) (f : ι → σ →₀ ℕ)
    (hf : ∀ I ∈ Q.support, I ∈ Set.range f) :
    w.mvPolynomialAbv (fun _ : Unit => Q) = w.vectorAbv (fun i => Q.coeff (f i)) := by
  have hle : ∀ I, w.normalizedAbv (Q.coeff I) ≤ w.vectorAbv (fun i => Q.coeff (f i)) := by
    intro I
    by_cases hI : I ∈ Q.support
    · obtain ⟨i, rfl⟩ := hf I hI
      exact w.normalizedAbv_le_vectorAbv (fun i => Q.coeff (f i)) i
    · rw [MvPolynomial.notMem_support_iff.1 hI, NumberFieldPlace.normalizedAbv_zero]
      exact w.vectorAbv_nonneg _
  simp only [NumberFieldPlace.mvPolynomialAbv, ciSup_const]
  refine le_antisymm (ciSup_le hle) (ciSup_le fun i => ?_)
  exact le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ (f i)

private lemma mvPolynomialAbv_eq_vectorAbv_support {F : Type*} [Field F] [NumberField F]
    {σ : Type*} (w : NumberFieldPlace F) (Q : MvPolynomial σ F) (hQ : Q ≠ 0) :
    w.mvPolynomialAbv (fun _ : Unit => Q) =
      w.vectorAbv (fun p : Σ _ : Unit, Q.support => Q.coeff p.2.1) := by
  have : Nonempty (Σ _ : Unit, Q.support) := by
    obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hQ
    exact ⟨⟨(), I, MvPolynomial.mem_support_iff.2 hI⟩⟩
  exact mvPolynomialAbv_eq_vectorAbv w Q (fun p : Σ _ : Unit, Q.support => (p.2 : σ →₀ ℕ))
    fun I hI => ⟨⟨(), I, hI⟩, rfl⟩

/-- `Faltings.coeffVector_ne_zero` for the one-element family `(Q)`. -/
private lemma coeffVector_unit_ne_zero {F : Type*} [Field F] {σ : Type*} (Q : MvPolynomial σ F)
    (hQ : Q ≠ 0) : (fun p : Σ _ : Unit, Q.support => Q.coeff p.2.1) ≠ 0 :=
  coeffVector_ne_zero (P := fun _ : Unit => Q) ⟨(), hQ⟩

/-- A nonzero polynomial has positive local size at every place. -/
theorem mvPolynomialAbv_pos {F : Type*} [Field F] [NumberField F] {σ : Type*}
    (w : NumberFieldPlace F) (Q : MvPolynomial σ F) (hQ : Q ≠ 0) :
    0 < w.mvPolynomialAbv (fun _ : Unit => Q) := by
  rw [mvPolynomialAbv_eq_vectorAbv_support w Q hQ]
  exact w.vectorAbv_pos (coeffVector_unit_ne_zero Q hQ)

/-- The logarithm of the local size of a nonzero polynomial vanishes at all but finitely many
places. -/
theorem finite_support_log_mvPolynomialAbv {F : Type*} [Field F] [NumberField F]
    {σ : Type*} (Q : MvPolynomial σ F) (hQ : Q ≠ 0) :
    (Function.support fun w : NumberFieldPlace F =>
      Real.log (w.mvPolynomialAbv (fun _ : Unit => Q))).Finite := by
  have := NumberFieldPlace.finite_support_localHeight (coeffVector_unit_ne_zero Q hQ)
  simpa only [NumberFieldPlace.localHeight, ← mvPolynomialAbv_eq_vectorAbv_support _ Q hQ]
    using this

/-- The height of a polynomial over `K` with a model `Q'` over a number field `F ⊆ K` is the sum
over the places of `F` of the logarithms of the local sizes of `Q'`. -/
theorem mvPolynomialHeight_eq_finsum {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {σ : Type*} {F : Type*} [Field F] [NumberField F] [Algebra F K]
    (Q : MvPolynomial σ K) (hQ : Q ≠ 0) (Q' : MvPolynomial σ F)
    (hQ' : MvPolynomial.map (algebraMap F K) Q' = Q) :
    mvPolynomialHeight Q hQ =
      ∑ᶠ w : NumberFieldPlace F, Real.log (w.mvPolynomialAbv (fun _ : Unit => Q')) := by
  have hsupp : Q.support = Q'.support := by
    rw [← hQ', MvPolynomial.support_map_of_injective _ (algebraMap F K).injective]
  obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hQ
  have : Nonempty (Σ _ : Unit, Q.support) := ⟨⟨(), I, MvPolynomial.mem_support_iff.mpr hI⟩⟩
  rw [mvPolynomialHeight, polynomialFamilyHeight_eq_sumLocalHeight (fun _ : Unit => Q) ⟨(), hQ⟩
    (fun p => Q'.coeff p.2.1) fun p => by rw [← MvPolynomial.coeff_map, hQ']]
  refine finsum_congr fun w => ?_
  rw [NumberFieldPlace.localHeight,
    mvPolynomialAbv_eq_vectorAbv w Q' (fun p : Σ _ : Unit, Q.support => p.2.1)
      fun I hI => ⟨⟨(), I, hsupp ▸ hI⟩, rfl⟩]

/-- The local bound `Faltings.NumberFieldPlace.inv_pow_mul_prod_mvPolynomialAbv_le`, in logarithms:
`∑_j log |Q_j|_w - ε_w log |2^d|_w ≤ log |∏_j Q_j|_w`, where `d = ∑_μ deg_μ ∏_j Q_j`. -/
private lemma sum_log_mvPolynomialAbv_sub_le {F : Type*} [Field F] [NumberField F]
    {σ ι : Type*} [Fintype σ] [Fintype ι] (w : NumberFieldPlace F) (Q : ι → MvPolynomial σ F)
    (hQ : ∀ j, Q j ≠ 0) :
    ∑ j, Real.log (w.mvPolynomialAbv (fun _ : Unit => Q j)) -
        (w.archimedeanIndicator : ℝ) *
          Real.log (w.normalizedAbv ((2 : F) ^ ∑ μ : σ, (∏ j, Q j).degreeOf μ)) ≤
      Real.log (w.mvPolynomialAbv (fun _ : Unit => ∏ j, Q j)) := by
  have ha := w.normalizedAbv_pos (pow_ne_zero (∑ μ : σ, (∏ j, Q j).degreeOf μ) two_ne_zero)
  have hb : ∀ j ∈ Finset.univ, w.mvPolynomialAbv (fun _ : Unit => Q j) ≠ 0 :=
    fun j _ => (mvPolynomialAbv_pos w (Q j) (hQ j)).ne'
  have h := Real.log_le_log (mul_pos (pow_pos (inv_pos.2 ha) _)
      (Finset.prod_pos fun j _ => mvPolynomialAbv_pos w (Q j) (hQ j)))
    (NumberFieldPlace.inv_pow_mul_prod_mvPolynomialAbv_le w Finset.univ Q fun j _ => hQ j)
  rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.2 hb), Real.log_pow, Real.log_inv,
    Real.log_prod hb] at h
  linarith

/-- The archimedean term `ε_w log |r|_w` vanishes at every finite place. -/
private lemma finite_support_archimedeanIndicator_mul_log {F : Type*} [Field F] [NumberField F]
    (r : F) : (Function.support fun w : NumberFieldPlace F =>
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv r)).Finite := by
  refine (Set.finite_range (Sum.inr : NumberField.InfinitePlace F → NumberFieldPlace F)).subset ?_
  rintro (w | w) hw
  · simp [NumberFieldPlace.archimedeanIndicator_inl] at hw
  · exact ⟨w, rfl⟩

/-- **Gelfond's inequality.** For a finite family `P` of nonzero polynomials over an algebraic
extension `K` of `ℚ` in finitely many variables, with `d = ∑_μ deg_{x_μ} (∏_j P_j)` the sum of
the partial degrees `MvPolynomial.degreeOf` of the product,
`∑_j h(P_j) - d log 2 ≤ h(∏_j P_j)`, where `h` is `Faltings.mvPolynomialHeight`. -/
@[faltings "lem_ht_height_of_product"]
public theorem sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod {K : Type*} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ K) (hP : ∀ j, P j ≠ 0) :
    ∑ j, mvPolynomialHeight (P j) (hP j) -
        (∑ μ : σ, (∏ j, P j).degreeOf μ : ℕ) * Real.log 2 ≤
      mvPolynomialHeight (∏ j, P j) (Finset.prod_ne_zero_iff.mpr fun j _ => hP j) := by
  classical
  -- the number field generated by all coefficients
  let S : Set K := ⋃ j, ((P j).coeffs : Set K)
  have hS : Finite S := (Set.finite_iUnion fun j => (P j).coeffs.finite_toSet).to_subtype
  let F := IntermediateField.adjoin ℚ S
  have hfin : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  let : NumberField F :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  have hlift : ∀ j, ∃ Q : MvPolynomial σ F, MvPolynomial.map (algebraMap F K) Q = P j :=
    fun j => MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun r hr =>
      ⟨⟨r, IntermediateField.subset_adjoin ℚ S (Set.mem_iUnion.2 ⟨j, hr⟩)⟩, rfl⟩
  choose Q hQ using hlift
  have hQ0 : ∀ j, Q j ≠ 0 := fun j h => hP j (by rw [← hQ j, h, map_zero])
  have hQprod : MvPolynomial.map (algebraMap F K) (∏ j, Q j) = ∏ j, P j := by
    simp [map_prod, hQ]
  have hdeg : ∀ μ, (∏ j, P j).degreeOf μ = (∏ j, Q j).degreeOf μ := fun μ => by
    rw [← hQprod, MvPolynomial.degreeOf_def, MvPolynomial.degreeOf_def,
      MvPolynomial.degrees_map_of_injective _ (algebraMap F K).injective]
  simp only [hdeg]
  set d := ∑ μ : σ, (∏ j, Q j).degreeOf μ
  rw [mvPolynomialHeight_eq_finsum _ _ _ hQprod]
  simp only [fun j => mvPolynomialHeight_eq_finsum (P j) (hP j) (Q j) (hQ j)]
  -- `d log 2` as a sum over the places
  have h2 : (d : ℝ) * Real.log 2 = ∑ᶠ w : NumberFieldPlace F,
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv ((2 : F) ^ d)) := by
    have := NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := F)
      (r := 2 ^ d) (by exact_mod_cast Nat.one_le_two_pow)
    push_cast at this
    rw [this, Real.log_pow]
  have hQj := fun j => finite_support_log_mvPolynomialAbv _ (hQ0 j)
  have hsum := (Finset.univ.finite_toSet.biUnion fun j _ => hQj j).subset
    (Finset.support_sum _ _)
  have harch := finite_support_archimedeanIndicator_mul_log ((2 : F) ^ d)
  rw [h2, ← finsum_sum_comm _ _ fun j _ => hQj j, ← finsum_sub_distrib hsum harch]
  exact finsum_le_finsum' ((hsum.union harch).subset (Function.support_sub _ _))
    (finite_support_log_mvPolynomialAbv _ (Finset.prod_ne_zero_iff.2 fun j _ => hQ0 j))
    fun w => sum_log_mvPolynomialAbv_sub_le w Q hQ0

end Faltings

/-!
# Bombieri's form of Gelfond's inequality

Let `P_1, …, P_k` be nonzero polynomials over an algebraic extension `K` of `ℚ` in the
variables `x_1, …, x_m`, with partial degrees `deg_{x_μ} P_i ≤ D_i` for all `i` and `μ`. Then the
heights of the factors are bounded by the height of their product:
`∑_i h(P_i) ≤ h(P_1 ⋯ P_k) + m (D_1 + ⋯ + D_k)`.

## Main results

* `Faltings.sum_mvPolynomialHeight_le_mvPolynomialHeight_prod_add`: Bombieri's form of
  Gelfond's inequality.

## Implementation notes

The source works over `ℚ̄`, with variables `x_1, …, x_m` and factors indexed by `{1, …, k}`.
Here `K` is any algebraic extension of `ℚ`, the variables form an arbitrary finite type `σ`
(so `m = Fintype.card σ`), and the factors an arbitrary finite family indexed by `ι`. The height
is `Faltings.mvPolynomialHeight` and the partial degree is `MvPolynomial.degreeOf`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

/-- If every factor `P j` has partial degree at most `D j` in each variable, then the partial
degrees of `∏ j, P j` sum to at most `card σ * ∑ j, D j`. -/
private lemma sum_degreeOf_prod_le {R σ ι : Type*} [CommSemiring R] [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ R) (D : ι → ℕ) (hD : ∀ j μ, (P j).degreeOf μ ≤ D j) :
    ∑ μ : σ, (∏ j, P j).degreeOf μ ≤ Fintype.card σ * ∑ j, D j := by
  simpa using Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) =>
    (MvPolynomial.degreeOf_prod_le μ Finset.univ P).trans (Finset.sum_le_sum fun j _ => hD j μ)

/-- **Bombieri's form of Gelfond's inequality.** Let `P` be a finite family of nonzero
polynomials over an algebraic extension `K` of `ℚ` in finitely many variables `σ`, with
`MvPolynomial.degreeOf μ (P j) ≤ D j` for all `j` and `μ`. Then
`∑_j h(P_j) ≤ h(∏_j P_j) + |σ| ∑_j D_j`, where `h` is `Faltings.mvPolynomialHeight`.

This is `Faltings.sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod`, with the degree term
`d log 2` bounded by `|σ| ∑_j D_j` using `log 2 ≤ 1` and `sum_degreeOf_prod_le`. -/
@[faltings "lem_ht_gelfond_bombieri"]
public theorem sum_mvPolynomialHeight_le_mvPolynomialHeight_prod_add {K : Type*} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype σ] [Fintype ι]
    (P : ι → MvPolynomial σ K) (hP : ∀ j, P j ≠ 0) (D : ι → ℕ)
    (hD : ∀ j μ, (P j).degreeOf μ ≤ D j) :
    ∑ j, mvPolynomialHeight (P j) (hP j) ≤
      mvPolynomialHeight (∏ j, P j) (Finset.prod_ne_zero_iff.mpr fun j _ => hP j) +
        (Fintype.card σ * ∑ j, D j : ℕ) := by
  have hd : ((∑ μ : σ, (∏ j, P j).degreeOf μ : ℕ) : ℝ) ≤ (Fintype.card σ * ∑ j, D j : ℕ) := by
    exact_mod_cast sum_degreeOf_prod_le P D hD
  have hlog := mul_le_of_le_one_right (Nat.cast_nonneg' (∑ μ : σ, (∏ j, P j).degreeOf μ))
    (by linarith [Real.log_two_lt_d9] : Real.log 2 ≤ 1)
  linarith [sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod P hP]

end Faltings
