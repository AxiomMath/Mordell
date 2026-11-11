module

public import Mordell.Height.Polynomial.Local.Size
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue

/-!
# Gauss' lemma for the local size of polynomials

Let `K` be a number field and `w` a finite place of `K`. For polynomials
`P_1, …, P_k ∈ K[x_1, …, x_m]` the local size `|P|_w = max_I |a_I|_w` of
`Faltings.NumberFieldPlace.mvPolynomialAbv` is multiplicative:
`|P_1 ⋯ P_k|_w = ∏_j |P_j|_w`. This is Gauss' lemma: the normalized absolute value at a finite
place is non-archimedean, and the reduction of polynomials modulo the maximal ideal of the
valuation ring of `w` lands in a polynomial ring over a field, which is a domain.

## Main results

* `Faltings.NumberFieldPlace.mvPolynomialAbv_prod`: `|∏_{j ∈ s} P_j|_w = ∏_{j ∈ s} |P_j|_w` at a
  finite place `w`, for a nonempty finite family of polynomials.

## Implementation notes

The family of polynomials is indexed by a `Finset` of an arbitrary type and the variables by an
arbitrary type `σ`; the source's case is `s = {1, …, k}` and `σ = Fin m`. A single polynomial
`Q` has local size `Faltings.NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => Q)`.

The proof does not construct the residue field of `w`. For a non-archimedean absolute value `v`
on `K`, scale `P` and `Q` so that their coefficients lie in the closed unit ball
`O = {v ≤ 1}`, a subring of `K`, with some coefficient equal to `1`. The open unit ball
`𝔪 = {v < 1}` is a prime ideal of `O`, so `(O ⧸ 𝔪)[σ]` is a domain and the product of the
nonzero reductions of `P` and `Q` is nonzero: some coefficient of `P Q` has `v ≥ 1`. The
ultrametric inequality gives the reverse bound.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

namespace Faltings

open NumberField MvPolynomial

section NonarchimedeanGauss

variable {K : Type*} [Field K] {σ : Type*}

/-- The closed unit ball `{x | v x ≤ 1}` of a non-archimedean absolute value, as a subring. -/
private def unitBall (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) : Subring K where
  carrier := {x | v x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ ha (v.nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (hv a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/-- The open unit ball `{x | v x < 1}`, as an ideal of the closed unit ball. -/
private def openBall (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    Ideal (unitBall v hv) where
  carrier := {x | v x < 1}
  add_mem' {a b} ha hb := lt_of_le_of_lt (hv _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    show v ((c : K) * x) < 1
    rw [map_mul]
    exact (mul_le_of_le_one_left (v.nonneg _) c.2).trans_lt hx

private lemma isPrime_openBall (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    (openBall v hv).IsPrime := by
  refine Ideal.isPrime_iff.2 ⟨(Ideal.ne_top_iff_one _).2 fun h => ?_, fun {x y} hxy => ?_⟩
  · change v (1 : K) < 1 at h
    simp at h
  · change v ((x : K) * y) < 1 at hxy
    change v (x : K) < 1 ∨ v (y : K) < 1
    by_contra! h
    rw [map_mul] at hxy
    exact hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)

private lemma sum_le {ι : Type*} {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {s : Finset ι} {g : ι → K} {c : ℝ} (h : ∀ i ∈ s, v (g i) ≤ c) (hc : 0 ≤ c) :
    v (∑ i ∈ s, g i) ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hc
  · exact (hv.apply_sum_le_sup_of_isNonarchimedean hs).trans (Finset.sup'_le _ _ h)

private lemma exists_max_coeff (v : AbsoluteValue K ℝ) {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ I, P.coeff I ≠ 0 ∧ ∀ J, v (P.coeff J) ≤ v (P.coeff I) := by
  obtain ⟨I, hI, hmax⟩ := P.support.exists_max_image (fun I => v (P.coeff I))
    (Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hP))
  refine ⟨I, mem_support_iff.1 hI, fun J => ?_⟩
  by_cases hJ : J ∈ P.support
  · exact hmax J hJ
  · rw [notMem_support_iff.1 hJ, map_zero]
    exact v.nonneg _

private lemma iSup_eq_of_max {ι : Type*} [Nonempty ι] {f : ι → ℝ} {i : ι} (h : ∀ j, f j ≤ f i) :
    ⨆ j, f j = f i :=
  le_antisymm (ciSup_le h) (le_ciSup ⟨f i, Set.forall_mem_range.2 h⟩ i)

private lemma exists_one_le_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {P Q : MvPolynomial σ K} (hP : ∀ I, v (P.coeff I) ≤ 1) (hQ : ∀ I, v (Q.coeff I) ≤ 1)
    {I₀ J₀ : σ →₀ ℕ} (hI₀ : P.coeff I₀ = 1) (hJ₀ : Q.coeff J₀ = 1) :
    ∃ L, 1 ≤ v ((P * Q).coeff L) := by
  have lift : ∀ R : MvPolynomial σ K, (∀ I, v (R.coeff I) ≤ 1) →
      ∃ R' : MvPolynomial σ (unitBall v hv), map (unitBall v hv).subtype R' = R := by
    intro R hR
    refine mem_range_map_iff_coeffs_subset.2 fun x hx => ?_
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact ⟨⟨_, hR n⟩, rfl⟩
  obtain ⟨P', rfl⟩ := lift P hP
  obtain ⟨Q', rfl⟩ := lift Q hQ
  haveI := isPrime_openBall v hv
  have hne : ∀ (R' : MvPolynomial σ (unitBall v hv)) (I : σ →₀ ℕ),
      (map (unitBall v hv).subtype R').coeff I = 1 →
        map (Ideal.Quotient.mk (openBall v hv)) R' ≠ 0 := by
    intro R' I h h0
    have h1 : R'.coeff I = 1 := Subtype.ext (by rwa [coeff_map] at h)
    simpa [coeff_map, h1] using congrArg (fun p => p.coeff I) h0
  have hprod := mul_ne_zero (hne P' I₀ hI₀) (hne Q' J₀ hJ₀)
  rw [← map_mul] at hprod
  obtain ⟨L, hL⟩ := MvPolynomial.ne_zero_iff.1 hprod
  refine ⟨L, ?_⟩
  rw [coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem] at hL
  rw [← map_mul, coeff_map]
  exact not_lt.1 hL

/-- Dividing `P` by a coefficient of maximal size puts its coefficients in the unit ball. -/
private lemma coeff_C_inv_mul_le_one {v : AbsoluteValue K ℝ} {P : MvPolynomial σ K}
    {I₀ : σ →₀ ℕ} (hI₀ : ∀ I, v (P.coeff I) ≤ v (P.coeff I₀)) (I : σ →₀ ℕ) :
    v ((C (P.coeff I₀)⁻¹ * P).coeff I) ≤ 1 := by
  rcases eq_or_ne (P.coeff I₀) 0 with h | h
  · simp [h]
  · rw [coeff_C_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (v.pos h), mul_one]
    exact hI₀ I

/-- The lower bound in Gauss' lemma: the product of the largest coefficient sizes of `P` and `Q`
is attained or exceeded by some coefficient of `P * Q`. -/
private lemma exists_mul_le_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {P Q : MvPolynomial σ K} {I₀ J₀ : σ →₀ ℕ} (ha : P.coeff I₀ ≠ 0) (hb : Q.coeff J₀ ≠ 0)
    (hI₀ : ∀ I, v (P.coeff I) ≤ v (P.coeff I₀)) (hJ₀ : ∀ J, v (Q.coeff J) ≤ v (Q.coeff J₀)) :
    ∃ L, v (P.coeff I₀) * v (Q.coeff J₀) ≤ v ((P * Q).coeff L) := by
  obtain ⟨L, hL⟩ := exists_one_le_coeff_mul hv (coeff_C_inv_mul_le_one hI₀)
    (coeff_C_inv_mul_le_one hJ₀) (by rw [coeff_C_mul, inv_mul_cancel₀ ha])
    (by rw [coeff_C_mul, inv_mul_cancel₀ hb])
  refine ⟨L, ?_⟩
  rwa [mul_mul_mul_comm, ← C_mul, coeff_C_mul, map_mul, map_mul, map_inv₀, map_inv₀, ← mul_inv,
    inv_mul_eq_div, one_le_div (mul_pos (v.pos ha) (v.pos hb))] at hL

/-- Gauss' lemma for one non-archimedean absolute value and two polynomials. -/
private lemma iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (P Q : MvPolynomial σ K) :
    ⨆ I, v ((P * Q).coeff I) = (⨆ I, v (P.coeff I)) * ⨆ I, v (Q.coeff I) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  obtain ⟨I₀, ha, hI₀⟩ := exists_max_coeff v hP
  obtain ⟨J₀, hb, hJ₀⟩ := exists_max_coeff v hQ
  rw [iSup_eq_of_max hI₀, iSup_eq_of_max hJ₀]
  have hup : ∀ L, v ((P * Q).coeff L) ≤ v (P.coeff I₀) * v (Q.coeff J₀) := fun L => by
    classical
    rw [coeff_mul]
    exact sum_le hv (fun x _ => by
      rw [map_mul]
      exact mul_le_mul (hI₀ _) (hJ₀ _) (v.nonneg _) (v.nonneg _)) (by positivity)
  obtain ⟨L, hL⟩ := exists_mul_le_coeff_mul hv ha hb hI₀ hJ₀
  exact le_antisymm (ciSup_le hup) (hL.trans (le_ciSup ⟨_, Set.forall_mem_range.2 hup⟩ L))

end NonarchimedeanGauss

/-- **Gauss' lemma.** At a finite place `w` of a number field `K`, the local size
`Faltings.NumberFieldPlace.mvPolynomialAbv` of a product of polynomials is the product of their
local sizes: `|∏_{j ∈ s} P_j|_w = ∏_{j ∈ s} |P_j|_w`. -/
@[faltings "lem_ht_gauss_lemma"]
public theorem NumberFieldPlace.mvPolynomialAbv_prod {K : Type*} [Field K] [NumberField K] {σ ι : Type*}
    (w : FinitePlace K) (s : Finset ι) (hs : s.Nonempty) (P : ι → MvPolynomial σ K) :
    NumberFieldPlace.mvPolynomialAbv (.inl w) (fun _ : Unit => ∏ j ∈ s, P j) =
      ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv (.inl w) (fun _ : Unit => P j) := by
  obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv (.inl w : NumberFieldPlace K)
  have hna : IsNonarchimedean v := hv ▸ NumberFieldPlace.isNonarchimedean_normalizedAbv_inl w
  simp only [NumberFieldPlace.mvPolynomialAbv, ciSup_const, ← hv]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j t hj _ ih => rw [Finset.prod_cons, Finset.prod_cons, iSup_coeff_mul hna, ih]

end Faltings
