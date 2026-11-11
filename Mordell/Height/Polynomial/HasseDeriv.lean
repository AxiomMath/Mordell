module

public import Mordell.Polynomial.HasseDeriv
public import Mordell.Height.Polynomial.Basic
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Polynomial.Sum

/-!
# The height of a family of divided derivatives

Let `(P_a)_{a ∈ A}` be a finite family of polynomials in `x_1, …, x_m` over an algebraic
extension `K` of `ℚ`, not all zero, with partial degrees `deg_{x_μ} P_a ≤ r_μ`, and let
`(I_a)_{a ∈ A}` be multi-indices such that the family of divided derivatives `(∂_{I_a} P_a)_a`
is not identically zero. Then
`h((∂_{I_a} P_a)_a) ≤ h((P_a)_a) + (r_1 + ⋯ + r_m) log 2`.
At a non-archimedean place the coefficients of `∂_I P` are integer multiples of those of `P`;
at an archimedean place they are multiplied by `∏_μ (j_μ choose i_μ) ≤ 2^{r_1 + ⋯ + r_m}`.

## Main results

* `Faltings.polynomialFamilyHeight_hasseDeriv_le`: the inequality above.

## Implementation notes

The source works over `ℚ̄` with variables `x_1, …, x_m`; here `K / ℚ` is any algebraic
extension and the variables are indexed by a finite type `σ`. The divided derivative is
`Faltings.MvPolynomial.hasseDeriv`, the partial degree is `MvPolynomial.degreeOf`, and the
height of a family is `Faltings.polynomialFamilyHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
-/

@[expose] public section

namespace Faltings

open _root_.MvPolynomial

/-- The coefficients of a divided derivative:
`coeff_K (∂_I P) = (∏_μ ((K + I)_μ choose I_μ)) coeff_{K + I} P`. -/
private theorem coeff_hasseDeriv {R σ : Type*} [CommSemiring R] (I K : σ →₀ ℕ)
    (P : _root_.MvPolynomial σ R) :
    (Faltings.MvPolynomial.hasseDeriv I P).coeff K =
      ((∏ μ ∈ I.support, ((K + I) μ).choose (I μ) : ℕ) : R) * P.coeff (K + I) := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, Faltings.MvPolynomial.hasseDeriv_monomial, coeff_sum, coeff_smul,
    coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single (K + I)]
  · simp
  · intro J _ hJ
    split_ifs with h
    · have : ∃ μ, J μ < I μ := by
        by_contra hc
        push Not at hc
        apply hJ
        rw [← h]
        ext μ
        simp [Nat.sub_add_cancel (hc μ)]
      obtain ⟨μ, hμ⟩ := this
      rw [Finset.prod_eq_zero (i := μ) (by simp; omega) (Nat.choose_eq_zero_of_lt hμ)]
      simp
    · simp
  · intro h
    simp [notMem_support_iff.mp h]

section Local

variable {F : Type*} [Field F] [NumberField F]

/-- An integer `1 ≤ b ≤ N` has `|b|_w ≤ |N|_w ^ ε_w`: at most `1` at a finite place, at most
`|N|_w` at an infinite place. -/
private theorem normalizedAbv_natCast_le (w : NumberFieldPlace F) {b N : ℕ} (hb : 1 ≤ b)
    (hbN : b ≤ N) :
    w.normalizedAbv (b : F) ≤ (w.normalizedAbv (N : F)) ^ w.archimedeanIndicator := by
  rcases w with w | w
  · simpa using NumberFieldPlace.normalizedAbv_inl_intCast_le_one w (r := (b : ℤ))
      (by exact_mod_cast hb)
  · have h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace F)
        (.inr Rat.infinitePlace : NumberFieldPlace ℚ) :=
      ⟨congrArg Subtype.val (Subsingleton.elim (w.comap (algebraMap ℚ F)) Rat.infinitePlace)⟩
    rw [NumberFieldPlace.archimedeanIndicator_inr, pow_one,
      (NumberFieldPlace.normalizedAbv_natCast_inr w _ h hb).1,
      (NumberFieldPlace.normalizedAbv_natCast_inr w _ h (hb.trans hbN)).1]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbN) (by positivity)

/-- The local estimate: if every coordinate of `u` is `b_k v_{j k}` with `1 ≤ b_k ≤ N`, then
`h_w(u) ≤ ε_w log |N|_w + h_w(v)`. -/
private theorem localHeight_le {κ τ : Type*} [Finite κ] [Finite τ] (w : NumberFieldPlace F)
    (u : κ → F) (v : τ → F) (j : κ → τ) (b : κ → ℕ) {N : ℕ} (hu : ∀ k, u k ≠ 0)
    (hk : Nonempty κ) (huv : ∀ k, u k = b k * v (j k)) (hbN : ∀ k, b k ≤ N) :
    w.localHeight u ≤
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (N : F)) + w.localHeight v := by
  have k₀ := hk.some
  have hb : ∀ k, 1 ≤ b k := fun k => Nat.one_le_iff_ne_zero.2 fun h =>
    hu k (by rw [huv k, h]; simp)
  have hv : ∀ k, v (j k) ≠ 0 := fun k h => hu k (by rw [huv k, h, mul_zero])
  have hN : 1 ≤ N := (hb k₀).trans (hbN k₀)
  set C := (w.normalizedAbv (N : F)) ^ w.archimedeanIndicator
  have hC : 0 < C := pow_pos (w.normalizedAbv_pos (by exact_mod_cast (by omega : N ≠ 0))) _
  have hbddv : BddAbove (Set.range fun i => w.normalizedAbv (v i)) :=
    (Set.finite_range _).bddAbove
  have hbddu : BddAbove (Set.range fun i => w.normalizedAbv (u i)) :=
    (Set.finite_range _).bddAbove
  have hupos : 0 < w.vectorAbv u :=
    (w.normalizedAbv_pos (hu k₀)).trans_le (le_ciSup hbddu k₀)
  have hvpos : 0 < w.vectorAbv v :=
    (w.normalizedAbv_pos (hv k₀)).trans_le (le_ciSup hbddv (j k₀))
  have hle : w.vectorAbv u ≤ C * w.vectorAbv v := by
    refine ciSup_le fun k => ?_
    rw [huv k, NumberFieldPlace.normalizedAbv_mul]
    exact mul_le_mul (normalizedAbv_natCast_le w (hb k) (hbN k)) (le_ciSup hbddv (j k))
      (NumberFieldPlace.normalizedAbv_nonneg _ _) hC.le
  have hlogC : Real.log C =
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (N : F)) := by
    rw [Real.log_pow]
  unfold NumberFieldPlace.localHeight
  calc Real.log (w.vectorAbv u) ≤ Real.log (C * w.vectorAbv v) := Real.log_le_log hupos hle
    _ = _ := by rw [Real.log_mul hC.ne' hvpos.ne', hlogC]

/-- The global estimate: if every coordinate of `u` is `b_k v_{j k}` with `1 ≤ b_k ≤ N`, then
`∑_w h_w(u) ≤ ∑_w h_w(v) + log N`. -/
private theorem sumLocalHeight_le {κ τ : Type*} [Finite κ] [Finite τ] (u : κ → F) (v : τ → F)
    (j : κ → τ) (b : κ → ℕ) {N : ℕ} (hu : ∀ k, u k ≠ 0) (hk : Nonempty κ)
    (huv : ∀ k, u k = b k * v (j k)) (hbN : ∀ k, b k ≤ N) :
    sumLocalHeight u ≤ sumLocalHeight v + Real.log N := by
  have hu0 : u ≠ 0 := fun h => hu hk.some (by rw [h]; rfl)
  have hv0 : v ≠ 0 := fun h => hu hk.some (by rw [huv, h, Pi.zero_apply, mul_zero])
  have hN : 1 ≤ (N : ℤ) := by
    have := hbN hk.some
    have : b hk.some ≠ 0 := fun h => hu hk.some (by rw [huv, h, Nat.cast_zero, zero_mul])
    omega
  set g : NumberFieldPlace F → ℝ := fun w =>
    (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (N : F))
  have hg : (Function.support g).Finite := by
    refine (Set.finite_range (Sum.inr : NumberField.InfinitePlace F → NumberFieldPlace F)).subset ?_
    rintro (w | w) hw
    · simp [g] at hw
    · exact ⟨w, rfl⟩
  have hgsum : ∑ᶠ w, g w = Real.log N := by
    simpa using
      NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := F) hN
  have hv := NumberFieldPlace.finite_support_localHeight hv0
  unfold sumLocalHeight
  calc ∑ᶠ w : NumberFieldPlace F, w.localHeight u ≤
        ∑ᶠ w : NumberFieldPlace F, (g w + w.localHeight v) :=
        finsum_le_finsum' (NumberFieldPlace.finite_support_localHeight hu0)
          ((hg.union hv).subset (Function.support_add _ _))
          fun w => localHeight_le w u v j b hu hk huv hbN
    _ = _ := by rw [finsum_add_distrib hg hv, hgsum, add_comm]

end Local

/-- The binomial factor of a coefficient of `∂_I P` is at most `2 ^ (∑_μ r_μ)` when
`deg_{x_μ} P ≤ r_μ` and `J` is in the support of `P`. -/
private theorem prod_choose_le_two_pow {R σ : Type*} [CommSemiring R] [Fintype σ]
    {P : _root_.MvPolynomial σ R} {r : σ → ℕ} (hr : ∀ μ, P.degreeOf μ ≤ r μ) (I : σ →₀ ℕ)
    {J : σ →₀ ℕ} (hJ : J ∈ P.support) :
    ∏ μ ∈ I.support, (J μ).choose (I μ) ≤ 2 ^ ∑ μ, r μ :=
  calc ∏ μ ∈ I.support, (J μ).choose (I μ) ≤ ∏ μ ∈ I.support, 2 ^ r μ :=
        Finset.prod_le_prod' fun μ _ => (Nat.choose_le_two_pow _ _).trans
          (Nat.pow_le_pow_right (by norm_num) ((le_degreeOf_of_mem_support μ hJ).trans (hr μ)))
    _ ≤ ∏ μ, 2 ^ r μ :=
        Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _)
          fun _ _ _ => Nat.one_le_two_pow
    _ = 2 ^ ∑ μ, r μ := Finset.prod_pow_eq_pow_sum _ _ _

/-- For a finite family `P` of polynomials over an algebraic extension `K` of `ℚ`, not all zero,
with partial degrees `(P a).degreeOf μ ≤ r μ`, and multi-indices `I a` such that the divided
derivatives `Faltings.MvPolynomial.hasseDeriv (I a) (P a)` are not all zero,
`h((∂_{I a} P a)_a) ≤ h((P a)_a) + (∑_μ r μ) log 2`, where `h` is
`Faltings.polynomialFamilyHeight`. -/
@[faltings "lem_ht_height_of_derivative"]
public theorem polynomialFamilyHeight_hasseDeriv_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype σ] [Fintype ι]
    (P : ι → _root_.MvPolynomial σ K) (hP : ∃ a, P a ≠ 0) (r : σ → ℕ)
    (hr : ∀ a μ, (P a).degreeOf μ ≤ r μ) (I : ι → σ →₀ ℕ)
    (hD : ∃ a, MvPolynomial.hasseDeriv (I a) (P a) ≠ 0) :
    polynomialFamilyHeight (fun a => MvPolynomial.hasseDeriv (I a) (P a)) hD ≤
      polynomialFamilyHeight P hP + (∑ μ, r μ : ℕ) * Real.log 2 := by
  classical
  set D : ι → _root_.MvPolynomial σ K := fun a => MvPolynomial.hasseDeriv (I a) (P a)
  -- the number field generated by the coefficients
  let F := IntermediateField.adjoin ℚ
    (Set.range fun p : (Σ a, (P a).support) => (P p.1).coeff p.2.1)
  have hfin : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let : NumberField F :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  let y : (Σ a, (P a).support) → F := fun p =>
    ⟨(P p.1).coeff p.2.1, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hmem : ∀ p : Σ a, (D a).support, p.2.1 + I p.1 ∈ (P p.1).support := by
    rintro ⟨a, J, hJ⟩
    have h := MvPolynomial.mem_support_iff.mp hJ
    rw [coeff_hasseDeriv] at h
    exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)
  let j : (Σ a, (D a).support) → (Σ a, (P a).support) := fun p => ⟨p.1, p.2.1 + I p.1, hmem p⟩
  let b : (Σ a, (D a).support) → ℕ := fun p =>
    ∏ μ ∈ (I p.1).support, ((p.2.1 + I p.1) μ).choose (I p.1 μ)
  let y' : (Σ a, (D a).support) → F := fun p => (b p : F) * y (j p)
  have hy' : ∀ p, algebraMap F K (y' p) = (D p.1).coeff p.2.1 := fun p => by
    rw [map_mul, map_natCast]
    exact (coeff_hasseDeriv _ _ _).symm
  have hne : Nonempty (Σ a, (D a).support) := by
    obtain ⟨a, ha⟩ := hD
    obtain ⟨J, hJ⟩ := MvPolynomial.ne_zero_iff.mp ha
    exact ⟨⟨a, J, MvPolynomial.mem_support_iff.mpr hJ⟩⟩
  rw [polynomialFamilyHeight_eq_sumLocalHeight D hD y' hy',
    polynomialFamilyHeight_eq_sumLocalHeight P hP y (fun _ => rfl)]
  refine (sumLocalHeight_le y' y j b
    (fun p h => MvPolynomial.mem_support_iff.mp p.2.2 (by rw [← hy', h, map_zero])) hne
    (fun _ => rfl) fun p => prod_choose_le_two_pow (hr p.1) (I p.1) (hmem p)).trans_eq ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end Faltings
