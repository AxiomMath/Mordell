module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mordell.Height.Polynomial.Local.GaussLemma
public import Mordell.Analysis.MahlerMeasure.Gelfond
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Polynomial.Local.ProdUpper

/-!
# A local lower bound for the size of a product of polynomials

Let `K` be a number field, `P_1, …, P_k ∈ K[x_1, …, x_m]` nonzero, `P = P_1 ⋯ P_k` and
`d = ∑_μ deg_{x_μ} P` the sum of the partial degrees of `P`. At every place `w ∈ M_K`,
`|2^d|_w^{-ε_w} ∏_j |P_j|_w ≤ |P|_w`, where `|·|_w` is the local size of a polynomial (the
largest normalized absolute value of a coefficient) and `ε_w` is the archimedean indicator.
At a finite place this is Gauss' lemma, with equality; at an infinite place it is Gelfond's
inequality transported along the embedding defining `w`.

## Main results

* `Faltings.NumberFieldPlace.inv_pow_mul_prod_mvPolynomialAbv_le`: the local lower bound
  `(|2^d|_w⁻¹) ^ ε_w * ∏_{j ∈ s} |P_j|_w ≤ |∏_{j ∈ s} P_j|_w`.

## Implementation notes

The family is `P : ι → MvPolynomial σ K` indexed by a `Finset` `s` of an arbitrary type, and the
variables form an arbitrary finite type `σ`; the source's case is `s = Finset.univ` in `Fin k`,
`σ = Fin m`. A single polynomial `Q` has local size `Faltings.NumberFieldPlace.mvPolynomialAbv w
(fun _ : Unit => Q)`. Since `ε_w ∈ ℕ`, the factor `|2^d|_w^{-ε_w}` is written as the natural
power `(|2^d|_w)⁻¹ ^ ε_w`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022], proof of Theorem 1.3.4.
-/

@[expose] public section

namespace Faltings

namespace NumberFieldPlace

open NumberField

/-- The local size of the constant polynomial `1` at a finite place is `1`. -/
private lemma mvPolynomialAbv_inl_one {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (w : FinitePlace K) :
    NumberFieldPlace.mvPolynomialAbv (.inl w) (fun _ : Unit => (1 : MvPolynomial σ K)) = 1 := by
  obtain ⟨v, hv⟩ :=
    NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv (.inl w : NumberFieldPlace K)
  simp only [NumberFieldPlace.mvPolynomialAbv, ciSup_const, ← hv]
  have hle : ∀ I, v ((1 : MvPolynomial σ K).coeff I) ≤ 1 := fun I => by
    classical
    rw [MvPolynomial.coeff_one]
    split_ifs <;> simp
  refine le_antisymm (ciSup_le hle) ?_
  calc (1 : ℝ) = v ((1 : MvPolynomial σ K).coeff 0) := by simp
    _ ≤ _ := le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ (0 : σ →₀ ℕ)

/-- Partial degrees are preserved by the coefficient map of an injective ring hom. -/
private lemma degreeOf_map_of_injective {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {f : R →+* S} (hf : Function.Injective f) (Q : MvPolynomial σ R) (μ : σ) :
    (MvPolynomial.map f Q).degreeOf μ = Q.degreeOf μ := by
  classical
  rw [MvPolynomial.degreeOf_def, MvPolynomial.degreeOf_def,
    MvPolynomial.degrees_map_of_injective _ hf]

/-- The bound at an infinite place `w`: Gelfond's inequality for the images `τ P_j` under the
embedding `τ` defining `w`, raised to the power `t = n_w / [K : ℚ]`. -/
private lemma inv_pow_mul_prod_mvPolynomialAbv_inr_le {K : Type*} [Field K] [NumberField K]
    {σ ι : Type*} [Fintype σ] (w : InfinitePlace K) (s : Finset ι) (P : ι → MvPolynomial σ K)
    (hP : ∀ j ∈ s, P j ≠ 0) :
    (NumberFieldPlace.normalizedAbv (.inr w) ((2 : K) ^ (∑ μ : σ, (∏ j ∈ s, P j).degreeOf μ)))⁻¹ *
      ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => P j) ≤
      NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => ∏ j ∈ s, P j) := by
  have h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace K)
      (.inr (w.comap (algebraMap ℚ K)) : NumberFieldPlace ℚ) := ⟨rfl⟩
  set τ := w.embedding
  obtain ⟨hmult, -, habs⟩ := NumberFieldPlace.localDegree_inr_eq_mult_and_normalizedAbv_inr_eq w τ
    w.mk_embedding _ h
  set t : ℝ := (NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K)
    (.inr (w.comap (algebraMap ℚ K)) : NumberFieldPlace ℚ) h : ℝ) / Module.finrank ℚ K with ht_def
  have ht : 0 < t := by
    rw [ht_def, hmult]
    have := w.mult_pos
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hG := Faltings.MvPolynomial.inv_two_pow_mul_prod_supNorm_le_supNorm_prod s
    (fun j => MvPolynomial.map τ (P j)) fun j hj =>
      (MvPolynomial.map_injective τ τ.injective).ne_iff' (map_zero _) |>.2 (hP j hj)
  simp only [← map_prod, degreeOf_map_of_injective τ.injective] at hG
  set d := ∑ μ : σ, (∏ j ∈ s, P j).degreeOf μ
  have h2 : NumberFieldPlace.normalizedAbv (.inr w) ((2 : K) ^ d) = ((2 : ℝ) ^ d) ^ t := by
    simpa using (NumberFieldPlace.normalizedAbv_natCast_inr w _ h (r := 2 ^ d) Nat.one_le_two_pow).1
  have hprod := Finset.prod_nonneg fun j (_ : j ∈ s) =>
    Faltings.MvPolynomial.supNorm_nonneg (MvPolynomial.map τ (P j))
  simp only [h2, mvPolynomialAbv_inr_eq w ht.le habs]
  rw [Real.finsetProd_rpow _ _ fun j _ => Faltings.MvPolynomial.supNorm_nonneg _,
    ← Real.inv_rpow (by positivity), ← Real.mul_rpow (by positivity) hprod, ← inv_pow]
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) hprod) hG ht.le

/-- For a number field `K`, a place `w`, and nonzero polynomials `P j ∈ K[σ]`, `j ∈ s`, with
`d = ∑_μ deg_{x_μ} (∏_{j ∈ s} P j)`, the local sizes satisfy
`(|2^d|_w)⁻¹ ^ ε_w * ∏_{j ∈ s} |P j|_w ≤ |∏_{j ∈ s} P j|_w`, where `|·|_w` is
`Faltings.NumberFieldPlace.normalizedAbv` on `K` and `Faltings.NumberFieldPlace.mvPolynomialAbv` on
polynomials, and `ε_w` is `Faltings.NumberFieldPlace.archimedeanIndicator`. -/
@[faltings "lem_ht_local_product"]
public theorem inv_pow_mul_prod_mvPolynomialAbv_le {K : Type*} [Field K] [NumberField K]
    {σ ι : Type*} [Fintype σ] (w : NumberFieldPlace K) (s : Finset ι) (P : ι → MvPolynomial σ K)
    (hP : ∀ j ∈ s, P j ≠ 0) :
    (w.normalizedAbv ((2 : K) ^ (∑ μ : σ, (∏ j ∈ s, P j).degreeOf μ)))⁻¹ ^
        w.archimedeanIndicator *
      ∏ j ∈ s, w.mvPolynomialAbv (fun _ : Unit => P j) ≤
      w.mvPolynomialAbv (fun _ : Unit => ∏ j ∈ s, P j) := by
  rcases w with w | w
  · rw [archimedeanIndicator_inl, pow_zero, one_mul]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [mvPolynomialAbv_inl_one]
    · exact (mvPolynomialAbv_prod w s hs P).ge
  · rw [archimedeanIndicator_inr, pow_one]
    exact inv_pow_mul_prod_mvPolynomialAbv_inr_le w s P hP

end NumberFieldPlace

end Faltings
