module
public import Mordell.Height.Affine.Basic
public import Mordell.BombieriVojta.SmallSection.BasisB

/-!
# Reduction of monomials to the basis `b_ν`

Let `k` be a number field, `k(C)` the function field of a curve `C` over `k` and `k(C × C)` that
of `C × C`, with the two projections `pr₁^*, pr₂^* : k(C) → k(C × C)`. Let `ξ₁, ξ₂ ∈ k(C)` satisfy
`ξ₂^N = A₀(ξ₁) + A₁(ξ₁) ξ₂ + ⋯ + A_{N-1}(ξ₁) ξ₂^{N-1}` with `A_i ∈ k[T]`, `deg A_i ≤ N - i`.
Then every monomial `ξ₁^{l₁} ξ₂^{l₂} ξ'₁^{l'₁} ξ'₂^{l'₂}` on `C × C` (unprimed functions pulled
back along `pr₁`, primed ones along `pr₂`) is a combination `∑_ν q_ν(ξ₁, ξ'₁) b_ν` of the
functions `b_ν = ξ₂^i ξ'₂^{i'}`, `ν = (i, i') ∈ {0, …, N - 1}²`, with polynomial coefficients
`q_ν ∈ k[T, T']` of degree at most `l₁ + l₂` in `T` and `l'₁ + l'₂` in `T'`, whose heights satisfy
`h(q_ν) ≤ h_aff(q_ν) ≤ (h_aff({A_i}) + log (2N + 2)) (l₁ + l₂ + l'₁ + l'₂)`.

## Main results

* `Faltings.BombieriSiegel.exists_monomial_eq_sum_aeval_mul_basisB`: the reduction, with the
  degree and height bounds.

## Implementation notes

Only the field structure is used, as in `Faltings.BombieriSiegel.basisB`: `k(C)` and `k(C × C)`
are arbitrary fields `K`, `L` over `k`, and the projections are arbitrary `k`-algebra maps
`pr₁ pr₂ : K →ₐ[k] L`. The relation for `ξ'₂` over `ξ'₁` is the image of the given one under
`pr₂`.

The polynomials `q_ν` lie in `MvPolynomial (Fin 2) k`, with `T = X 0` and `T' = X 1`; the partial
degrees are `MvPolynomial.degreeOf`. The projective height of `q` is
`h(q) = Finsupp.logHeight c / [k : ℚ]` for its coefficient vector `c = AddMonoidAlgebra.coeff q`,
and its affine height is `Faltings.affineLogHeight c`. The family
`{A_i}` is the coefficient vector `(i, m) ↦ coeff (A i) m` on `Fin N × ℕ`.

The proof writes `ξ₂ ^ e = ∑_{i < N} A^{(e)}_i(ξ₁) ξ₂ ^ i`, the coefficients being given by the
recursion `A^{(e+1)}_i = A^{(e)}_{i-1} + A^{(e)}_{N-1} A_i`; then `deg A^{(e)}_i ≤ e - i` and, at
every place `v`, each coefficient of `A^{(e)}_i` has size at most
`((2N + 2)^{κ_v} max(1, |{A_i}|_v))^e`. The polynomial
`q_ν = T^{l₁} A^{(l₂)}_i(T) T'^{l'₁} A^{(l'₂)}_{i'}(T')` reduces the monomial, and summing the
local bounds over the places gives the height bound.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 630
-/

open Polynomial Finset Real NumberField

namespace Faltings.BombieriSiegel

section Reduction

variable {k : Type*} [Field k]

/-- The coefficients `A^{(e)}_i` of `ξ₂ ^ e = ∑_{i ≤ n} A^{(e)}_i(ξ₁) ξ₂ ^ i`, for a relation of
degree `N = n + 1` with coefficients `A i`, given by the recursion
`A^{(e+1)}_i = A^{(e)}_{i-1} + A^{(e)}_n A_i`. -/
private noncomputable def powCoeff (A : ℕ → k[X]) (n : ℕ) : ℕ → ℕ → k[X]
  | 0, i => if i = 0 then 1 else 0
  | e + 1, 0 => powCoeff A n e n * A 0
  | e + 1, i + 1 => powCoeff A n e i + powCoeff A n e n * A (i + 1)

private lemma pow_eq_sum_powCoeff {K : Type*} [Field K] [Algebra k K] (A : ℕ → k[X]) (n : ℕ)
    (ξ₁ ξ₂ : K) (hrel : ξ₂ ^ (n + 1) = ∑ i ∈ range (n + 1), aeval ξ₁ (A i) * ξ₂ ^ i) (e : ℕ) :
    ξ₂ ^ e = ∑ i ∈ range (n + 1), aeval ξ₁ (powCoeff A n e i) * ξ₂ ^ i := by
  induction e with
  | zero => rw [sum_range_succ']; simp [powCoeff]
  | succ e ih =>
    rw [sum_range_succ']
    simp only [powCoeff, map_add, map_mul, add_mul, sum_add_distrib, pow_zero, mul_one]
    rw [sum_range_succ'] at hrel
    simp only [pow_zero, mul_one] at hrel
    have h : ∑ i ∈ range n, aeval ξ₁ (powCoeff A n e n) * aeval ξ₁ (A (i + 1)) * ξ₂ ^ (i + 1) +
        aeval ξ₁ (powCoeff A n e n) * aeval ξ₁ (A 0) =
          aeval ξ₁ (powCoeff A n e n) * ξ₂ ^ (n + 1) := by
      rw [hrel, mul_add, mul_sum]
      simp only [mul_assoc]
    rw [add_assoc, h, show ξ₂ ^ (e + 1) = ξ₂ * ξ₂ ^ e from pow_succ' _ _, ih, mul_sum,
      sum_range_succ]
    congr 1
    · exact sum_congr rfl fun i _ => by ring
    · ring

/-- A coefficient of `P * Q` with `deg Q ≤ D` is a sum of `D + 1` products of a coefficient of `Q`
and one of `P`. -/
private lemma coeff_mul_eq_sum_range (P Q : k[X]) {D : ℕ} (hQ : Q.natDegree ≤ D) (m : ℕ) :
    (P * Q).coeff m = ∑ j ∈ range (D + 1), Q.coeff j * (if j ≤ m then P.coeff (m - j) else 0) := by
  conv_lhs => rw [Q.as_sum_range' (D + 1) (Nat.lt_succ_of_le hQ)]
  rw [mul_sum, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, mul_comm P, mul_assoc, coeff_C_mul, coeff_mul_X_pow']

/-- The degree step of `coeff_powCoeff_eq_zero`: `deg (P Q) ≤ e + 1 - i` when `deg P ≤ e - n`
and `deg Q ≤ n + 1 - i`, with `Q = 0` for `i > n`. -/
private lemma coeff_mul_eq_zero_of_lt {P Q : k[X]} {e n i m : ℕ}
    (hP : ∀ a, e < a + n → P.coeff a = 0) (hQ : Q.natDegree ≤ n + 1 - i) (hQ0 : n < i → Q = 0)
    (h : e + 1 < m + i) : (P * Q).coeff m = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  by_cases ha : e < x.1 + n
  · rw [hP _ ha, zero_mul]
  by_cases hi : n < i
  · rw [hQ0 hi, coeff_zero, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), mul_zero]

/-- `deg A^{(e)}_i ≤ e - i`, in the form: the coefficient of `T ^ m` vanishes when `e < m + i`. -/
private lemma coeff_powCoeff_eq_zero (A : ℕ → k[X]) (n : ℕ)
    (hA : ∀ i, (A i).natDegree ≤ n + 1 - i) (hA0 : ∀ i, n < i → A i = 0) (e : ℕ) :
    ∀ i m, e < m + i → (powCoeff A n e i).coeff m = 0 := by
  induction e with
  | zero =>
    intro i m h
    rcases i with _ | i
    · simp only [powCoeff, ↓reduceIte, coeff_one, show m ≠ 0 by omega]
    · simp [powCoeff]
  | succ e ih =>
    intro i m h
    rcases i with _ | i
    · exact coeff_mul_eq_zero_of_lt (fun a ha => ih n a ha) (hA 0) (hA0 0) (by omega)
    · rw [powCoeff, coeff_add, ih i m (by omega),
        coeff_mul_eq_zero_of_lt (fun a ha => ih n a ha) (hA _) (hA0 _) (by omega), add_zero]

/-- The local size of the coefficients of `A^{(e)}_i`: at most `(c₂ c₁ α) ^ e`, where `α ≥ 1`
bounds the coefficients of the `A i`, `c₂` is the constant for sums of two terms and `c₁` that for
sums of `n + 2` terms. -/
private lemma abv_coeff_powCoeff_le (A : ℕ → k[X]) (n : ℕ) (hA : ∀ i, (A i).natDegree ≤ n + 1)
    (v : AbsoluteValue k ℝ) {α c₁ c₂ : ℝ} (hα : 1 ≤ α) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hAα : ∀ i m, v ((A i).coeff m) ≤ α)
    (h₂ : ∀ x y B, v x ≤ B → v y ≤ B → v (x + y) ≤ c₂ * B)
    (h₁ : ∀ (t : ℕ → k) B, (∀ j, v (t j) ≤ B) → v (∑ j ∈ range (n + 2), t j) ≤ c₁ * B)
    (e : ℕ) : ∀ i m, v ((powCoeff A n e i).coeff m) ≤ (c₂ * c₁ * α) ^ e := by
  induction e with
  | zero =>
    intro i m
    rcases i with _ | i
    · simp only [powCoeff, ↓reduceIte, coeff_one]
      split_ifs <;> simp
    · simp [powCoeff]
  | succ e ih =>
    intro i m
    have hβ : 0 ≤ (c₂ * c₁ * α) ^ e :=
      pow_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) _
    have hy : ∀ j, v ((powCoeff A n e n * A j).coeff m) ≤ c₁ * (α * (c₂ * c₁ * α) ^ e) := by
      intro j
      rw [coeff_mul_eq_sum_range _ _ (hA j)]
      refine h₁ _ _ fun l => ?_
      rw [map_mul]
      refine mul_le_mul (hAα j l) ?_ (v.nonneg _) (by linarith)
      split_ifs
      · exact ih n _
      · rw [map_zero]; exact hβ
    have hle : (c₂ * c₁ * α) ^ e ≤ c₁ * (α * (c₂ * c₁ * α) ^ e) := by
      rw [← mul_assoc]
      exact le_mul_of_one_le_left hβ (one_le_mul_of_one_le_of_one_le hc₁ hα)
    have hnn : 0 ≤ c₁ * (α * (c₂ * c₁ * α) ^ e) := hβ.trans hle
    rw [pow_succ, show (c₂ * c₁ * α) ^ e * (c₂ * c₁ * α) = c₂ * (c₁ * (α * (c₂ * c₁ * α) ^ e)) by
      ring]
    rcases i with _ | i
    · exact (hy 0).trans (le_mul_of_one_le_left hnn hc₂)
    · rw [powCoeff, coeff_add]
      exact h₂ _ _ _ ((ih i m).trans hle) (hy _)

/-- The coefficients of `p(T) r(T')` are the products of those of `p` and `r`. -/
private lemma coeff_aeval_X_mul_aeval_X (p r : k[X]) (m : Fin 2 →₀ ℕ) :
    (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) p *
        aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) r).coeff m =
      p.coeff (m 0) * r.coeff (m 1) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, add_mul, MvPolynomial.coeff_add, h₁, h₂, Polynomial.coeff_add, add_mul]
  | monomial a c =>
    induction r using Polynomial.induction_on' with
    | add r₁ r₂ h₁ h₂ =>
      rw [map_add, mul_add, MvPolynomial.coeff_add, h₁, h₂, Polynomial.coeff_add, mul_add]
    | monomial b d =>
      simp only [aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_X_pow_eq_monomial,
        MvPolynomial.monomial_mul_monomial, MvPolynomial.coeff_monomial,
        Polynomial.coeff_monomial]
      have key : Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b = m ↔ a = m 0 ∧ b = m 1 := by
        constructor
        · rintro rfl; simp
        · rintro ⟨rfl, rfl⟩; ext j; fin_cases j <;> simp
      simp only [key]
      by_cases ha : a = m 0 <;> by_cases hb : b = m 1 <;> simp [ha, hb]

/-- Multiplying by `X ^ l` shifts the coefficients, so it keeps a uniform bound on their sizes. -/
private lemma abv_coeff_X_pow_mul_le (v : AbsoluteValue k ℝ) (p : k[X]) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ d, v (p.coeff d) ≤ B) (l d : ℕ) : v ((X ^ l * p).coeff d) ≤ B := by
  rw [coeff_X_pow_mul']
  split_ifs
  exacts [h _, by simpa using hB]

/-- If the coefficients of `p` and `r` have size at most `β ^ e₁` and `β ^ e₂`, those of
`p(T) r(T')` have size at most `β ^ (e₁ + e₂)`. -/
private lemma iSup_abv_coeff_aeval_X_mul_aeval_X_le (v : AbsoluteValue k ℝ) (p r : k[X]) {β : ℝ}
    (hβ : 0 ≤ β) {e₁ e₂ : ℕ} (hp : ∀ d, v (p.coeff d) ≤ β ^ e₁) (hr : ∀ d, v (r.coeff d) ≤ β ^ e₂) :
    ⨆ m : (AddMonoidAlgebra.coeff (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) p *
        aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) r)).support,
      v (AddMonoidAlgebra.coeff (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) p *
        aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) r) m) ≤ β ^ (e₁ + e₂) := by
  refine Real.iSup_le (fun m => ?_) (pow_nonneg hβ _)
  change v (AddMonoidAlgebra.coeff _ _) ≤ _
  rw [coeff_aeval_X_mul_aeval_X, map_mul, pow_add]
  exact mul_le_mul (hp _) (hr _) (v.nonneg _) (pow_nonneg hβ _)

end Reduction

section Heights

variable {K : Type*} [Field K] [NumberField K] {α : Type*}

private lemma log_le_posLog (x : ℝ) : log x ≤ log⁺ x := by
  rw [posLog_apply]; exact le_max_right _ _

omit [NumberField K] in
private lemma le_iSup_support (f : α →₀ K) {φ : K → ℝ} (h0 : φ 0 = 0) (hφ : ∀ x, 0 ≤ φ x)
    (c : α) : φ (f c) ≤ ⨆ c : f.support, φ (f c) := by
  by_cases hc : c ∈ f.support
  · exact le_ciSup (f := fun c : f.support => φ (f c)) (Set.finite_range _).bddAbove ⟨c, hc⟩
  · rw [Finsupp.notMem_support_iff.mp hc, h0]
    exact Real.iSup_nonneg fun _ => hφ _

/-- Only finitely many finite places see a coefficient of `f` of size different from `1`. -/
private lemma finite_badPlaces (f : α →₀ K) :
    (⋃ c ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f c)).Finite :=
  f.support.finite_toSet.biUnion fun _ hc =>
    FinitePlace.hasFiniteMulSupport (Finsupp.mem_support_iff.mp hc)

private lemma iSup_finitePlace_eq_one (f : α →₀ K) (hf : f ≠ 0) {w : FinitePlace K}
    (hw : w ∉ ⋃ c ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f c)) :
    ⨆ c : f.support, w (f c) = 1 := by
  obtain ⟨c₀, hc₀⟩ := Finsupp.support_nonempty_iff.mpr hf
  have : Nonempty f.support := ⟨⟨c₀, hc₀⟩⟩
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hw
  have h : ∀ c : f.support, w (f c) = 1 := fun c => hw c c.2
  simp only [h, ciSup_const]

private lemma support_posLog_iSup_subset (f : α →₀ K) :
    Function.support (fun w : FinitePlace K => log⁺ (⨆ c : f.support, w (f c))) ⊆
      ⋃ c ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f c) := by
  intro w hw
  by_contra hU
  apply hw
  by_cases hf : f = 0
  · subst hf; simp
  · simp only [iSup_finitePlace_eq_one f hf hU, posLog_one]

private lemma sum_posLog_iSup_nonneg (f : α →₀ K) :
    0 ≤ (∑ v : InfinitePlace K, v.mult * log⁺ (⨆ c : f.support, v (f c))) +
      ∑ᶠ v : FinitePlace K, log⁺ (⨆ c : f.support, v (f c)) :=
  add_nonneg (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) posLog_nonneg)
    (finsum_nonneg fun _ => posLog_nonneg)

omit [NumberField K] in
/-- Over a nonzero `f`, the supremum of a size function vanishing at `0` over all indices is its
supremum over the support. -/
private lemma iSup_eq_iSup_support (f : α →₀ K) (hf : f ≠ 0) (φ : K → ℝ) (h0 : φ 0 = 0)
    (hφ : ∀ x, 0 ≤ φ x) : ⨆ i, φ (f i) = ⨆ c : f.support, φ (f c) := by
  obtain ⟨c₀, hc₀⟩ := Finsupp.support_nonempty_iff.mpr hf
  have : Nonempty f.support := ⟨⟨c₀, hc₀⟩⟩
  have : Nonempty α := ⟨c₀⟩
  refine le_antisymm (ciSup_le fun i => le_iSup_support f h0 hφ i) (ciSup_le fun c => ?_)
  exact le_ciSup (f := fun i => φ (f i))
    ⟨_, by rintro _ ⟨i, rfl⟩; exact le_iSup_support f h0 hφ i⟩ (c : α)

/-- `h(f) ≤ h_aff(f)`: the projective height is at most the affine height. -/
private lemma logHeight_div_le_affineLogHeight (f : α →₀ K) :
    Finsupp.logHeight f / Module.finrank ℚ K ≤ affineLogHeight f := by
  unfold affineLogHeight
  gcongr
  by_cases hf : f = 0
  · have h0 : (⇑f : α → K) = 0 := by rw [hf, Finsupp.coe_zero]
    rw [Finsupp.logHeight, show Height.mulHeight (⇑f) = 1 by rw [h0, Height.mulHeight_zero],
      log_one]
    exact sum_posLog_iSup_nonneg f
  obtain ⟨c₀, hc₀⟩ := Finsupp.support_nonempty_iff.mpr hf
  have hc₀' : f c₀ ≠ 0 := Finsupp.mem_support_iff.mp hc₀
  have hy : (⇑f : α → K) ≠ 0 := fun h => hc₀' (congrFun h c₀)
  have hinfeq : ∀ v : InfinitePlace K, ⨆ i, v (f i) = ⨆ c : f.support, v (f c) := fun v =>
    iSup_eq_iSup_support f hf v (map_zero v) (apply_nonneg v)
  have hfineq : ∀ v : FinitePlace K, ⨆ i, v (f i) = ⨆ c : f.support, v (f c) := fun v =>
    iSup_eq_iSup_support f hf v (map_zero v) (apply_nonneg v)
  have hinf : ∀ v : InfinitePlace K, 0 < ⨆ c : f.support, v (f c) := fun v =>
    (InfinitePlace.pos_iff.mpr hc₀').trans_le
      (le_ciSup (f := fun c : f.support => v (f c)) (Set.finite_range _).bddAbove ⟨c₀, hc₀⟩)
  have hfin : ∀ v : FinitePlace K, 0 < ⨆ c : f.support, v (f c) := fun v =>
    (FinitePlace.pos_iff.mpr hc₀').trans_le
      (le_ciSup (f := fun c : f.support => v (f c)) (Set.finite_range _).bddAbove ⟨c₀, hc₀⟩)
  have hU : ∀ w : FinitePlace K, w ∉ (finite_badPlaces f).toFinset →
      ⨆ c : f.support, w (f c) = 1 := fun w hw =>
    iSup_finitePlace_eq_one f hf (by simpa using hw)
  rw [Finsupp.logHeight, NumberField.mulHeight_eq hy]
  simp only [hinfeq, hfineq]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_badPlaces f).toFinset) _ ?_,
    finsum_eq_sum_of_support_subset (s := (finite_badPlaces f).toFinset) _ ?_,
    Real.log_mul (prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hinf v).ne')
      (prod_ne_zero_iff.mpr fun v _ => (hfin v).ne'),
    Real.log_prod (fun v _ => pow_ne_zero _ (hinf v).ne'), Real.log_prod (fun v _ => (hfin v).ne')]
  · refine add_le_add (sum_le_sum fun v _ => ?_) (sum_le_sum fun v _ => ?_)
    · rw [Real.log_pow]
      exact mul_le_mul_of_nonneg_left (log_le_posLog _) (Nat.cast_nonneg _)
    · exact log_le_posLog _
  · intro w hw
    by_contra h
    exact hw (by simp only [hU w h, posLog_one])
  · intro w hw
    by_contra h
    exact hw (hU w h)

/-- At a finite place the size of a sum is at most the largest size of a summand. -/
private lemma finitePlace_sum_range_le (w : FinitePlace K) (t : ℕ → K) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j, w (t j) ≤ B) (s : ℕ) : w (∑ j ∈ range s, t j) ≤ B := by
  induction s with
  | zero => simpa using hB
  | succ s ih => rw [sum_range_succ]; exact (FinitePlace.add_le w _ _).trans (max_le ih (h s))

/-- `log⁺ S ≤ L (log⁺ c + log⁺ s)` whenever `0 ≤ S ≤ (c max(1, s)) ^ L`. -/
private lemma posLog_le_of_le_pow {S c s : ℝ} {L : ℕ} (hS : 0 ≤ S) (h : S ≤ (c * max 1 s) ^ L) :
    log⁺ S ≤ L * (log⁺ c + log⁺ s) := by
  calc log⁺ S ≤ log⁺ ((c * max 1 s) ^ L) := posLog_le_posLog (by linarith) h
    _ = L * log⁺ (c * max 1 s) := posLog_pow _ _
    _ ≤ L * (log⁺ c + log⁺ s) := by
      gcongr
      refine posLog_mul.trans (add_le_add le_rfl ?_)
      rcases le_total 1 s with h1 | h1
      · rw [max_eq_right h1]
      · rw [max_eq_left h1, posLog_one]; exact posLog_nonneg

/-- The arithmetic of `affineLogHeight_le_of_forall_place`: from `Iq ≤ L (lc d + IA)`,
`Fq ≤ L FA` and `L ≤ M`, `(Iq + Fq) / d ≤ ((IA + FA) / d + lc) M`. -/
private lemma div_le_mul_of_le {Iq Fq IA FA d lc L M : ℝ} (hd : 0 < d) (hlc : 0 ≤ lc)
    (hIA : 0 ≤ IA + FA) (hLM : L ≤ M) (hI : Iq ≤ L * (lc * d + IA)) (hF : Fq ≤ L * FA) :
    (Iq + Fq) / d ≤ ((IA + FA) / d + lc) * M := by
  rw [div_le_iff₀ hd, show ((IA + FA) / d + lc) * M * d = (IA + FA + lc * d) * M by
    field_simp]
  nlinarith [mul_le_mul_of_nonneg_left hLM (add_nonneg hIA (mul_nonneg hlc hd.le))]

/-- Summing local bounds over the places: if `log⁺ |f|_w ≤ L (log c + log⁺ |F|_w)` at every
infinite place and `log⁺ |f|_w ≤ L log⁺ |F|_w` at every finite place, then
`h_aff(f) ≤ (h_aff(F) + log c) M` for every `M ≥ L`. -/
private lemma affineLogHeight_le_of_forall_place {β : Type*} (f : α →₀ K) (F : β →₀ K) {c : ℝ}
    (hc : 1 ≤ c) {L M : ℕ} (hLM : L ≤ M)
    (hinf : ∀ w : InfinitePlace K, log⁺ (⨆ m : f.support, w (f m)) ≤
      L * (Real.log c + log⁺ (⨆ x : F.support, w (F x))))
    (hfin : ∀ w : FinitePlace K, log⁺ (⨆ m : f.support, w (f m)) ≤
      L * log⁺ (⨆ x : F.support, w (F x))) :
    affineLogHeight f ≤ (affineLogHeight F + Real.log c) * M := by
  have hsum : (∑ w : InfinitePlace K, (w.mult : ℝ)) = Module.finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  unfold affineLogHeight
  refine div_le_mul_of_le (L := L) (by exact_mod_cast Module.finrank_pos) (Real.log_nonneg hc)
    (sum_posLog_iSup_nonneg F) (by exact_mod_cast hLM) ?_ ?_
  · calc _ ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) *
          (L * (Real.log c + log⁺ (⨆ x : F.support, w (F x)))) :=
          sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hinf w) (Nat.cast_nonneg _)
      _ = L * (Real.log c * ∑ w : InfinitePlace K, (w.mult : ℝ) +
            ∑ w : InfinitePlace K, (w.mult : ℝ) * log⁺ (⨆ x : F.support, w (F x))) := by
          rw [mul_sum, ← sum_add_distrib, mul_sum]
          exact sum_congr rfl fun w _ => by ring
      _ = _ := by rw [hsum]
  · have hU := (finite_badPlaces f).union (finite_badPlaces F)
    rw [mul_finsum, finsum_eq_sum_of_support_subset (s := hU.toFinset) _ ?_,
      finsum_eq_sum_of_support_subset (s := hU.toFinset) _ ?_]
    · exact sum_le_sum fun w _ => hfin w
    · rw [Set.Finite.coe_toFinset]
      exact (Function.support_mul_subset_right _ _).trans
        ((support_posLog_iSup_subset F).trans Set.subset_union_right)
    · rw [Set.Finite.coe_toFinset]
      exact (support_posLog_iSup_subset _).trans Set.subset_union_left

end Heights

/-- Let `ξ₁, ξ₂ ∈ K` satisfy `ξ₂^N = ∑_{i < N} A_i(ξ₁) ξ₂^i` with `A_i ∈ k[T]`, `deg A_i ≤ N - i`,
over a number field `k`, and let `pr₁, pr₂ : K →ₐ[k] L`. Then every monomial
`(pr₁ ξ₁)^{l₁} (pr₁ ξ₂)^{l₂} (pr₂ ξ₁)^{l'₁} (pr₂ ξ₂)^{l'₂}` equals
`∑_ν q_ν(pr₁ ξ₁, pr₂ ξ₁) · basisB pr₁ pr₂ ξ₂ ν` for polynomials `q_ν ∈ k[T, T']` with
`deg_T q_ν ≤ l₁ + l₂`, `deg_{T'} q_ν ≤ l'₁ + l'₂` and
`h(q_ν) ≤ h_aff(q_ν) ≤ (h_aff({A_i}) + log (2N + 2)) (l₁ + l₂ + l'₁ + l'₂)`. -/
@[faltings "lem_bvs_monomial_reduction"]
public theorem exists_monomial_eq_sum_aeval_mul_basisB {k K L : Type*} [Field k] [NumberField k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (ξ₁ ξ₂ : K) {N : ℕ}
    (A : Fin N → k[X]) (hA : ∀ i, (A i).natDegree ≤ N - i)
    (hrel : ξ₂ ^ N = ∑ i : Fin N, aeval ξ₁ (A i) * ξ₂ ^ (i : ℕ))
    (l₁ l₂ l₁' l₂' : ℕ) :
    ∃ q : Fin N × Fin N → MvPolynomial (Fin 2) k,
      pr₁ ξ₁ ^ l₁ * pr₁ ξ₂ ^ l₂ * pr₂ ξ₁ ^ l₁' * pr₂ ξ₂ ^ l₂' =
          ∑ ν, MvPolynomial.aeval ![pr₁ ξ₁, pr₂ ξ₁] (q ν) * basisB pr₁ pr₂ ξ₂ ν ∧
        ∀ ν, (q ν).degreeOf 0 ≤ l₁ + l₂ ∧ (q ν).degreeOf 1 ≤ l₁' + l₂' ∧
          Finsupp.logHeight (AddMonoidAlgebra.coeff (q ν)) / Module.finrank ℚ k ≤
            affineLogHeight (AddMonoidAlgebra.coeff (q ν)) ∧
          affineLogHeight (AddMonoidAlgebra.coeff (q ν)) ≤
            (affineLogHeight (Finsupp.uncurry
                (Finsupp.equivFunOnFinite.symm fun i => (A i).toFinsupp.coeff)) +
              Real.log (2 * N + 2)) * (l₁ + l₂ + l₁' + l₂' : ℕ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    rcases N with _ | n
    · simp at hrel
    · exact ⟨n, rfl⟩
  classical
  -- the coefficients `A_i`, indexed by `ℕ` and extended by zero
  set A' : ℕ → k[X] := fun i => if h : i < n + 1 then A ⟨i, h⟩ else 0
  have hA'deg : ∀ i, (A' i).natDegree ≤ n + 1 - i := fun i => by
    simp only [A']
    split_ifs with h
    · exact hA ⟨i, h⟩
    · simp
  have hA'0 : ∀ i, n < i → A' i = 0 := fun i hi => by
    simp only [A', show ¬i < n + 1 by omega, ↓reduceDIte]
  have hrel' : ξ₂ ^ (n + 1) = ∑ i ∈ range (n + 1), aeval ξ₁ (A' i) * ξ₂ ^ i := by
    rw [hrel, ← Fin.sum_univ_eq_sum_range (fun i => aeval ξ₁ (A' i) * ξ₂ ^ i)]
    refine sum_congr rfl fun i _ => ?_
    simp only [A', i.isLt, ↓reduceDIte, Fin.eta]
  have hpow := pow_eq_sum_powCoeff A' n ξ₁ ξ₂ hrel'
  -- `T ^ l A^{(e)}_i(T)`, and the polynomials `q_ν`
  let P : ℕ → ℕ → ℕ → k[X] := fun l e i => X ^ l * powCoeff A' n e i
  let q : Fin (n + 1) × Fin (n + 1) → MvPolynomial (Fin 2) k := fun ν =>
    aeval (MvPolynomial.X 0) (P l₁ l₂ ν.1) * aeval (MvPolynomial.X 1) (P l₁' l₂' ν.2)
  have hqc : ∀ ν m, (q ν).coeff m = (P l₁ l₂ ν.1).coeff (m 0) * (P l₁' l₂' ν.2).coeff (m 1) :=
    fun ν m => coeff_aeval_X_mul_aeval_X _ _ m
  have hP0 : ∀ l e i d, l + e < d → (P l e i).coeff d = 0 := by
    intro l e i d h
    simp only [P, coeff_X_pow_mul']
    split_ifs
    · exact coeff_powCoeff_eq_zero A' n hA'deg hA'0 e i (d - l) (by omega)
    · rfl
  have h1 : ∀ (f : K →ₐ[k] L) l e, f ξ₁ ^ l * f ξ₂ ^ e =
      ∑ i : Fin (n + 1), aeval (f ξ₁) (P l e i) * f ξ₂ ^ (i : ℕ) := by
    intro f l e
    rw [Fin.sum_univ_eq_sum_range (fun i => aeval (f ξ₁) (P l e i) * f ξ₂ ^ i), ← map_pow f ξ₂ e,
      hpow e, map_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [P, map_mul, map_pow, aeval_X, aeval_algHom_apply]
    ring
  have hq : ∀ ν, MvPolynomial.aeval ![pr₁ ξ₁, pr₂ ξ₁] (q ν) =
      aeval (pr₁ ξ₁) (P l₁ l₂ ν.1) * aeval (pr₂ ξ₁) (P l₁' l₂' ν.2) := by
    intro ν
    simp [q, ← aeval_algHom_apply]
  refine ⟨q, ?_, fun ν => ⟨?_, ?_, logHeight_div_le_affineLogHeight _, ?_⟩⟩
  · rw [show pr₁ ξ₁ ^ l₁ * pr₁ ξ₂ ^ l₂ * pr₂ ξ₁ ^ l₁' * pr₂ ξ₂ ^ l₂' =
        (pr₁ ξ₁ ^ l₁ * pr₁ ξ₂ ^ l₂) * (pr₂ ξ₁ ^ l₁' * pr₂ ξ₂ ^ l₂') by ring, h1 pr₁, h1 pr₂,
      sum_mul_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hq]
    simp only [basisB]
    ring
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    rw [MvPolynomial.mem_support_iff, hqc] at hm
    by_contra hc
    exact left_ne_zero_of_mul hm (hP0 _ _ _ _ (by omega))
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    rw [MvPolynomial.mem_support_iff, hqc] at hm
    by_contra hc
    exact right_ne_zero_of_mul hm (hP0 _ _ _ _ (by omega))
  · -- the height bound, place by place
    set F := Finsupp.uncurry (Finsupp.equivFunOnFinite.symm fun i => (A i).toFinsupp.coeff)
    have hAα : ∀ (v : AbsoluteValue k ℝ) i m,
        v ((A' i).coeff m) ≤ max 1 (⨆ x : F.support, v (F x)) := by
      intro v i m
      simp only [A']
      split_ifs with h
      · exact (le_iSup_support F (map_zero v) v.nonneg (⟨i, h⟩, m)).trans (le_max_right _ _)
      · rw [coeff_zero, map_zero]
        exact zero_le_one.trans (le_max_left _ _)
    have key : ∀ (v : AbsoluteValue k ℝ) (c₁ c₂ : ℝ), 1 ≤ c₁ → 1 ≤ c₂ →
        (∀ x y B, v x ≤ B → v y ≤ B → v (x + y) ≤ c₂ * B) →
        (∀ (t : ℕ → k) B, (∀ j, v (t j) ≤ B) → v (∑ j ∈ range (n + 2), t j) ≤ c₁ * B) →
        log⁺ (⨆ m : (AddMonoidAlgebra.coeff (q ν)).support, v (AddMonoidAlgebra.coeff (q ν) m)) ≤
          ((l₂ + l₂' : ℕ) : ℝ) * (log⁺ (c₂ * c₁) + log⁺ (⨆ x : F.support, v (F x))) := by
      intro v c₁ c₂ hc₁ hc₂ h₂ h₁
      have hβ : 0 ≤ c₂ * c₁ * max 1 (⨆ x : F.support, v (F x)) := by
        have := le_max_left 1 (⨆ x : F.support, v (F x)); positivity
      have hPv : ∀ l e i d, v ((P l e i).coeff d) ≤
          (c₂ * c₁ * max 1 (⨆ x : F.support, v (F x))) ^ e := fun l e i =>
        abv_coeff_X_pow_mul_le v _ (pow_nonneg hβ _)
          (abv_coeff_powCoeff_le A' n (fun i => (hA'deg i).trans (Nat.sub_le _ _)) v
            (le_max_left _ _) hc₁ hc₂ (hAα v) h₂ h₁ e i) l
      exact posLog_le_of_le_pow (Real.iSup_nonneg fun _ => v.nonneg _)
        (iSup_abv_coeff_aeval_X_mul_aeval_X_le v _ _ hβ (hPv _ _ _) (hPv _ _ _))
    have hlogc : log⁺ (2 * ((n : ℝ) + 2)) = Real.log (2 * ((n + 1 : ℕ) : ℝ) + 2) := by
      rw [posLog_eq_log (by
        rw [abs_of_pos (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      push_cast
      ring_nf
    refine affineLogHeight_le_of_forall_place _ F (L := l₂ + l₂') (by push_cast; linarith)
      (by omega) (fun w => ?_) (fun w => ?_)
    · rw [← hlogc]
      refine key w.1 ((n : ℝ) + 2) 2 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        one_le_two (fun x y B hx hy => ?_) (fun t B ht => ?_)
      · exact (w.1.add_le x y).trans (by linarith)
      · refine (w.1.sum_le _ _).trans ((sum_le_card_nsmul _ _ _ fun j _ => ht j).trans_eq ?_)
        rw [card_range, nsmul_eq_mul]
        push_cast
        ring
    · have := key w.1 1 1 le_rfl le_rfl
        (fun x y B hx hy => by
          rw [one_mul]; exact (FinitePlace.add_le w x y).trans (max_le hx hy))
        (fun t B ht => by
          rw [one_mul]
          exact finitePlace_sum_range_le w t ((w.1.nonneg _).trans (ht 0)) ht _)
      rwa [mul_one, posLog_one, zero_add] at this

end Faltings.BombieriSiegel
