module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.LocalHeight

/-!
# The local size of a vector of polynomials

Let `K` be a number field, `v ∈ M_K`, and `P = (P_1, …, P_r)` with
`P_i = ∑_I a_{i,I} x^I ∈ K[x_1, …, x_m]`. The local size of `P` at `v` is
`|P|_v = max_{i,I} |a_{i,I}|_v`, the largest normalized absolute value
`Faltings.NumberFieldPlace.normalizedAbv` of a coefficient. For a single polynomial (`r = 1`) this
is `|P|_v = max_I |a_I|_v`.

## Main definitions

* `Faltings.NumberFieldPlace.mvPolynomialAbv w P`: the local size `|P|_w` of a family `P` of
  polynomials.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_coeff_le_mvPolynomialAbv`: `|a_I|_w ≤ |F|_w`.
* `Faltings.NumberFieldPlace.normalizedAbv_coeff_mul_prod_le`: for `F` homogeneous of degree `e`,
  `|a_I x^I|_w ≤ |a_I|_w |x|_w ^ e`.

## Implementation notes

The family is a function `P : ι → MvPolynomial σ K` on an arbitrary index type and the variables
form an arbitrary type `σ`; the source's case is `ι = Fin r`, `σ = Fin m`, and a single polynomial
`Q` is the family `fun _ : Unit => Q`. The maximum is written as the supremum
`⨆ i, ⨆ I, |coeff I (P i)|_w` over all exponents `I`, not only those in the support: the absent
coefficients are `0`, whose absolute value `0` does not exceed any other value, and each `P i` has
finitely many nonzero coefficients, so for finite nonempty `ι` this is the maximum of the source.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 5 and Sec. 9.
-/

@[expose] public section

namespace Faltings

/-- The local size `|P|_w = max_{i,I} |a_{i,I}|_w` at a place `w` of the number field `K` of a
family `P : ι → MvPolynomial σ K` of polynomials, where `a_{i,I}` is the coefficient of the
monomial `x^I` in `P i` and `|·|_w` is `Faltings.NumberFieldPlace.normalizedAbv`. It is the
supremum over all `i` and all exponents `I`, which is the maximum when `ι` is finite and nonempty.
-/
@[faltings "def_ht_polynomial_local_norm"]
public noncomputable def NumberFieldPlace.mvPolynomialAbv {K : Type*} [Field K] [NumberField K]
    {ι σ : Type*} (w : NumberFieldPlace K) (P : ι → MvPolynomial σ K) : ℝ :=
  ⨆ i, ⨆ I, w.normalizedAbv ((P i).coeff I)

/-- Over a finite type of variables, `Multiset.card p.degrees` is the sum of the partial
degrees of `p`. -/
theorem card_degrees_eq_sum_degreeOf {R τ : Type*} [CommSemiring R] [Fintype τ]
    (p : _root_.MvPolynomial τ R) : Multiset.card p.degrees = ∑ μ, p.degreeOf μ := by
  classical
  simp only [_root_.MvPolynomial.degreeOf_def]
  exact (Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a).symm

namespace NumberFieldPlace

open NumberField

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

/-- The local size `|P|_w` of a family of polynomials is nonnegative. -/
theorem mvPolynomialAbv_nonneg {ι : Type*} (w : NumberFieldPlace K)
    (P : ι → _root_.MvPolynomial σ K) : 0 ≤ w.mvPolynomialAbv P :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => normalizedAbv_nonneg _ _

/-- A coefficient's local absolute value is at most the local size `|F|_w`. -/
theorem normalizedAbv_coeff_le_mvPolynomialAbv (w : NumberFieldPlace K)
    (F : _root_.MvPolynomial σ K) (I : σ →₀ ℕ) :
    w.normalizedAbv (F.coeff I) ≤ w.mvPolynomialAbv (fun _ : Unit => F) := by
  rw [mvPolynomialAbv, ciSup_unique]
  refine le_ciSup (f := fun J => w.normalizedAbv (F.coeff J))
    ⟨∑ J ∈ F.support, w.normalizedAbv (F.coeff J), ?_⟩ I
  rintro _ ⟨J, rfl⟩
  by_cases hJ : J ∈ F.support
  · exact Finset.single_le_sum (f := fun J => w.normalizedAbv (F.coeff J))
      (fun _ _ => normalizedAbv_nonneg _ _) hJ
  · simp only [_root_.MvPolynomial.notMem_support_iff.1 hJ, normalizedAbv_zero]
    exact Finset.sum_nonneg fun _ _ => normalizedAbv_nonneg _ _

/-- `|m|_w ^ ε_w` is monotone in the natural number `m ≥ 1`. -/
theorem normalizedAbv_natCast_pow_le (w : NumberFieldPlace K) {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    w.normalizedAbv (m : K) ^ w.archimedeanIndicator ≤
      w.normalizedAbv (n : K) ^ w.archimedeanIndicator := by
  rcases w with w | w
  · simp
  · have h : LiesOver (.inr w : NumberFieldPlace K) (.inr (w.comap (algebraMap ℚ K))) := ⟨rfl⟩
    rw [archimedeanIndicator_inr, pow_one, pow_one, (normalizedAbv_natCast_inr w _ h hm).1,
      (normalizedAbv_natCast_inr w _ h (hm.trans hmn)).1]
    gcongr

/-- Each term of a homogeneous polynomial `F` of degree `e` evaluated at `x` satisfies
`|a_I x^I|_w ≤ |a_I|_w |x|_w ^ e`. -/
theorem normalizedAbv_coeff_mul_prod_le [Fintype σ] (w : NumberFieldPlace K) {e : ℕ}
    {F : _root_.MvPolynomial σ K} (hF : F.IsHomogeneous e) (x : σ → K) {I : σ →₀ ℕ}
    (hI : I ∈ F.support) :
    w.normalizedAbv (F.coeff I * ∏ i, x i ^ I i) ≤
      w.normalizedAbv (F.coeff I) * w.vectorAbv x ^ e := by
  obtain ⟨v, hv⟩ := w.exists_absoluteValue_coe_eq_normalizedAbv
  have he : e = ∑ i, I i := by
    rw [← hF (_root_.MvPolynomial.mem_support_iff.1 hI), Finsupp.weight_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    simp
  have hx : ∀ i, 0 ≤ w.normalizedAbv (x i) ^ I i := fun i =>
    pow_nonneg (normalizedAbv_nonneg _ _) _
  rw [← hv, map_mul, map_prod, he, ← Finset.prod_pow_eq_pow_sum]
  simp only [map_pow, hv]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => hx i) fun i _ =>
      pow_le_pow_left₀ (normalizedAbv_nonneg _ _) (w.normalizedAbv_le_vectorAbv x i) _)
    (normalizedAbv_nonneg _ _)

end NumberFieldPlace

end Faltings
