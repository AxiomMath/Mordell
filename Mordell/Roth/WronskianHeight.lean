module
public import Mordell.Roth.Wronskian.Product
public import Mordell.Height.Finsupp
public import Mordell.Polynomial.HasseDeriv

/-!
# Heights of the Wronskian factors in Roth's lemma

Let `m ≥ 2`, `0 < ε < 1/2` and `r₁, …, rₘ` positive integers with
`r_{μ+1} / r_μ ≤ ε^{2^{m-1}}`. Let `P ≠ 0` be a polynomial with algebraic coefficients and
degree at most `r_μ` in `ς_μ`, written as `P = ∑_{j=0}^s φ_j(ς₁, …, ς_{m-1}) ψ_j(ς_m)` with
`s ≤ r_m`, and let `I'₀, …, I'ₛ ∈ ℕ^{m-1}` be multi-indices with `|I'_μ| ≤ s` such that the
generalized Wronskian `U = Wr_{I'₀,…,I'ₛ}(φ₀, …, φₛ)` and the Wronskian
`V = Wr(ψ₀, …, ψₛ)` are nonzero. Then `h(U) + h(V) ≤ (s + 1)(h(P) + 2 r₁)`.

Here `h` of a polynomial is the absolute logarithmic height of its coefficient vector, a point
of projective space: `Finsupp.logHeight` of the coefficients divided by `[K : ℚ]`.

## Main results

* `Faltings.logHeight_generalizedWronskian_add_le`: the height bound.

## Implementation notes

The algebraic coefficients are taken in a number field `K` containing them; the heights are
normalised by `[K : ℚ]`, so they are absolute. The variables `ς₁, …, ςₘ` are `X 0, …, X n`
with `m = n + 1`, so `m ≥ 2` is `1 ≤ n`. A polynomial in `ς₁, …, ς_{m-1}` is an
`MvPolynomial (Fin n) K`, embedded by `rename Fin.castSucc`, and `ψ_j(ς_m)` is
`Polynomial.aeval (X (Fin.last n)) (ψ j)`, exactly as in
`Faltings.exists_sum_rename_mul_aeval_eq`. The one-variable Wronskian `V` is
`Faltings.generalizedWronskian` in one variable with the multi-indices `ν ↦ ν`, applied to the
`ψ_j` viewed in `MvPolynomial (Fin 1) K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 635
-/

namespace Faltings

open _root_.MvPolynomial Height Height.AdmissibleAbsValues

section IntegerTuples

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

private lemma finprod_le_one_of_le_one {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : ∏ᶠ a, f a ≤ 1 := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_le_one₀ (fun a _ => h0 a) (fun a _ => h1 a)
  · exact le_rfl

omit [Finite ι] in
/-- A tuple of integers of absolute value at most `M ≥ 1` has multiplicative height at most
`M ^ totalWeight K`. -/
private lemma mulHeight_intCast_le (z : ι → ℤ) {M : ℝ} (hM : 1 ≤ M)
    (hz : ∀ i, |(z i : ℝ)| ≤ M) :
    mulHeight (fun i => (z i : K)) ≤ M ^ totalWeight K := by
  by_cases h : (fun i => (z i : K)) = 0
  · rw [h, mulHeight_zero]
    exact one_le_pow₀ hM
  rw [mulHeight_eq h, ← mul_one (M ^ totalWeight K)]
  have : Nonempty ι := (Function.ne_iff.mp h).nonempty
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
    (le_trans zero_le_one (one_le_pow₀ hM))
  · rw [← Multiset.prod_replicate, totalWeight, ← Multiset.map_const']
    refine Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ => ciSup_le fun i => ?_
    calc v (z i : K) = v ((z i).natAbs : K) := by
            rcases Int.natAbs_eq (z i) with h | h
            · conv_lhs => rw [h]
              simp
            · conv_lhs => rw [h]
              simp
      _ ≤ (z i).natAbs := v.apply_nat_le_self _
      _ ≤ M := by rw [Nat.cast_natAbs]; push_cast; exact hz i
  · refine finprod_le_one_of_le_one (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      fun v => ciSup_le fun i => ?_
    exact IsNonarchimedean.apply_intCast_le_one (by simp) (by simp) (fun a => by simp)
      (isNonarchimedean _ v.prop)

private lemma logHeight_intCast_le (z : ι → ℤ) {M : ℝ} (hM : 1 ≤ M)
    (hz : ∀ i, |(z i : ℝ)| ≤ M) :
    logHeight (fun i => (z i : K)) ≤ totalWeight K * Real.log M := by
  rw [logHeight_eq_log_mulHeight, ← Real.log_pow]
  exact Real.log_le_log (mulHeight_pos _) (mulHeight_intCast_le z hM hz)

/-- The height of a finitely supported function is that of its restriction along an injection
whose range contains the support. -/
private lemma mulHeight_finsupp_eq_comp {α β : Type*} [Finite β] (x : α →₀ K) {e : β → α}
    (he : Function.Injective e) (hsupp : ∀ a ∈ x.support, a ∈ Set.range e) :
    mulHeight (⇑x) = mulHeight (fun i => x (e i)) := by
  rw [mulHeight_finsupp_eq, Finsupp.mulHeight,
    mulHeight_eq_mulHeight_restrict_support (fun i => x (e i))]
  let f : Function.support (fun i => x (e i)) → x.support :=
    fun i => ⟨e i, Finsupp.mem_support_iff.mpr i.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => Subtype.ext (he (congrArg Subtype.val h)), fun a => ?_⟩
    obtain ⟨i, hi⟩ := hsupp a a.2
    refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
    simpa [Function.mem_support, hi] using Finsupp.mem_support_iff.mp a.2
  rw [← mulHeight_comp_equiv (Equiv.ofBijective f hf)]
  rfl

omit [Finite ι] in
/-- The height of a polynomial is that of its coefficients on its support. -/
private lemma logHeight_coeff_eq (P : MvPolynomial ι K) :
    Finsupp.logHeight (AddMonoidAlgebra.coeff P) =
      logHeight (fun b : P.support => P.coeff (b : ι →₀ ℕ)) := by
  unfold Finsupp.logHeight
  rw [mulHeight_finsupp_eq, Finsupp.mulHeight, logHeight_eq_log_mulHeight]
  rfl

omit [AdmissibleAbsValues K] [Finite ι] in
private lemma coeff_support_ne_zero {P : MvPolynomial ι K} (hP : P ≠ 0) :
    (fun b : P.support => P.coeff (b : ι →₀ ℕ)) ≠ 0 := by
  obtain ⟨b, hb⟩ := support_nonempty.mpr hP
  exact Function.ne_iff.mpr ⟨⟨b, hb⟩, mem_support_iff.mp hb⟩

end IntegerTuples

section DividedDerivatives

variable {K : Type*} [Field K] {m : ℕ}

/-- The divided derivative `∂_J` of a monomial: `∂_J X^b = (∏ₖ binom(bₖ, Jₖ)) X^{b - J}`. -/
private lemma hasseDeriv_equivFunOnFinite_monomial (J : Fin m → ℕ) (b : Fin m →₀ ℕ) :
    Faltings.MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm J) (monomial b (1 : K)) =
      monomial (b - Finsupp.equivFunOnFinite.symm J) ((∏ k, (b k).choose (J k) : ℕ) : K) := by
  rw [Faltings.MvPolynomial.hasseDeriv_monomial, smul_monomial, smul_eq_mul, mul_one]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [Finset.prod_subset (f := fun k => (b k).choose (J k)) (Finset.subset_univ _)
    fun k _ hk => by
      have hk0 : J k = 0 := by simpa using Finsupp.notMem_support_iff.mp hk
      simp [hk0]]

end DividedDerivatives

section WronskianHeight

variable {K : Type*} [Field K] {N s : ℕ}

/-- The integer coefficient of `X^c` in `∑_σ sgn σ ∏_ν ∂_{J (σ ν) ν} X^{t ν}`. -/
private noncomputable def zcoef (J : Fin (s + 1) → Fin (s + 1) → Fin N → ℕ) (c : Fin N →₀ ℕ)
    (t : Fin (s + 1) → Fin N →₀ ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin (s + 1)), (Equiv.Perm.sign σ : ℤ) *
    (if ∑ ν, (t ν - Finsupp.equivFunOnFinite.symm (J (σ ν) ν)) = c then
      ((∏ ν, ∏ k, (t ν k).choose (J (σ ν) ν k) : ℕ) : ℤ) else 0)

private lemma coeff_sum_sign_prod_dd_monomial (J : Fin (s + 1) → Fin (s + 1) → Fin N → ℕ)
    (t : Fin (s + 1) → Fin N →₀ ℕ) (c : Fin N →₀ ℕ) :
    (∑ σ : Equiv.Perm (Fin (s + 1)),
      Equiv.Perm.sign σ • ∏ ν,
        MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J (σ ν) ν))
          (monomial (t ν) (1 : K))).coeff c =
      (zcoef J c t : K) := by
  simp only [hasseDeriv_equivFunOnFinite_monomial, ← monomial_sum_prod, coeff_sum, zcoef]
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul,
    ← map_intCast (C : K →+* MvPolynomial (Fin N) K), coeff_C_mul, coeff_monomial]

private lemma det_dd_eq_sum (J : Fin (s + 1) → Fin (s + 1) → Fin N → ℕ)
    (P : MvPolynomial (Fin N) K) :
    Matrix.det (Matrix.of fun μ ν =>
        MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J μ ν)) P) =
      ∑ t : Fin (s + 1) → P.support, (∏ ν, P.coeff (t ν : Fin N →₀ ℕ)) •
        ∑ σ : Equiv.Perm (Fin (s + 1)), Equiv.Perm.sign σ •
          ∏ ν, MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J (σ ν) ν))
            (monomial (t ν : Fin N →₀ ℕ) 1) := by
  have hexp : ∀ J' : Fin N → ℕ, MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm J') P =
      ∑ b : P.support, P.coeff (b : Fin N →₀ ℕ) •
        MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm J')
          (monomial (b : Fin N →₀ ℕ) (1 : K)) := by
    intro J'
    conv_lhs => rw [as_sum P]
    rw [← Finset.sum_coe_sort, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply, hexp, Finset.prod_univ_sum, Finset.prod_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_comm]

private lemma prod_choose_le (J : Fin (s + 1) → Fin N → ℕ) (r : Fin N → ℕ)
    (t : Fin (s + 1) → Fin N →₀ ℕ) (ht : ∀ ν k, t ν k ≤ r k) :
    ∏ ν, ∏ k, (t ν k).choose (J ν k) ≤ 2 ^ ((s + 1) * ∑ k, r k) := by
  calc ∏ ν, ∏ k, (t ν k).choose (J ν k) ≤ ∏ _ν : Fin (s + 1), ∏ k, 2 ^ r k := by
        refine Finset.prod_le_prod fun ν _ => Finset.prod_le_prod fun k _ => ?_
        exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (ht ν k))
    _ = 2 ^ ((s + 1) * ∑ k, r k) := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul, mul_comm]

private lemma abs_zcoef_le (J : Fin (s + 1) → Fin (s + 1) → Fin N → ℕ) (r : Fin N → ℕ)
    (c : Fin N →₀ ℕ) (t : Fin (s + 1) → Fin N →₀ ℕ) (ht : ∀ ν k, t ν k ≤ r k) :
    |(zcoef J c t : ℝ)| ≤ (s + 1).factorial * 2 ^ ((s + 1) * ∑ k, r k) := by
  rw [zcoef, Int.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hcard : ((s + 1).factorial : ℝ) =
      (Finset.univ : Finset (Equiv.Perm (Fin (s + 1)))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [Int.cast_mul, abs_mul]
  have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  split_ifs
  · push_cast
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast prod_choose_le (fun ν => J (σ ν) ν) r t ht
  · simp

private lemma card_support_le (P : MvPolynomial (Fin N) K) (r : Fin N → ℕ)
    (hr : ∀ b ∈ P.support, ∀ k, b k ≤ r k) :
    Fintype.card P.support ≤ 2 ^ ∑ k, r k := by
  let f : P.support → ((k : Fin N) → Fin (r k + 1)) :=
    fun b k => ⟨(b : Fin N →₀ ℕ) k, Nat.lt_succ_of_le (hr b b.2 k)⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext <| Finsupp.ext fun k => congrArg Fin.val (congrFun h k)
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod fun k _ => ?_
  rw [Fintype.card_fin]
  exact Nat.lt_two_pow_self

private lemma log_card_fun_support_le (P : MvPolynomial (Fin N) K) (r : Fin N → ℕ)
    (hr : ∀ b ∈ P.support, ∀ k, b k ≤ r k) :
    Real.log (Nat.card (Fin (s + 1) → P.support)) ≤ (s + 1) * (∑ k, r k) * Real.log 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow,
    mul_assoc]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases Nat.eq_zero_or_pos (Fintype.card P.support) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    positivity
  · have := Real.log_le_log (x := (Fintype.card P.support : ℝ)) (y := (2 : ℝ) ^ ∑ k, r k)
      (by exact_mod_cast hpos) (by exact_mod_cast card_support_le P r hr)
    rwa [Real.log_pow, Nat.cast_sum] at this

/-- **Height of a Wronskian-type determinant.** If the monomials of `P ≠ 0` have exponents at
most `r`, the determinant `det (∂_{J μ ν} P)` has height at most
`(s + 1) h(P) + [2 (s + 1) ρ log 2 + log ((s + 1)!)]` (per unit of total weight), `ρ = ∑ₖ rₖ`. -/
private theorem logHeight_det_dd_le [AdmissibleAbsValues K]
    (J : Fin (s + 1) → Fin (s + 1) → Fin N → ℕ) {P : MvPolynomial (Fin N) K} (hP : P ≠ 0)
    (r : Fin N → ℕ) (hr : ∀ b ∈ P.support, ∀ k, b k ≤ r k) :
    Finsupp.logHeight (AddMonoidAlgebra.coeff (Matrix.det (Matrix.of fun μ ν =>
        MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J μ ν)) P))) ≤
      (s + 1) * Finsupp.logHeight (AddMonoidAlgebra.coeff P) +
        totalWeight K * (2 * (s + 1) * (∑ k, r k) * Real.log 2 +
          Real.log (s + 1).factorial) := by
  set W := Matrix.det (Matrix.of fun μ ν =>
    MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J μ ν)) P) with hWdef
  let x : P.support → K := fun b => P.coeff (b : Fin N →₀ ℕ)
  let X : (Fin (s + 1) → P.support) → K := fun t => ∏ ν, x (t ν)
  let A : W.support × (Fin (s + 1) → P.support) → K :=
    fun jt => (zcoef J jt.1 (fun ν => (jt.2 ν : Fin N →₀ ℕ)) : K)
  have hW : (fun j : W.support => W.coeff (j : Fin N →₀ ℕ)) =
      fun j => ∑ t, A (j, t) * X t := by
    ext j
    refine (congrArg (fun q : MvPolynomial (Fin N) K => q.coeff (j : Fin N →₀ ℕ))
      (det_dd_eq_sum J P)).trans ?_
    rw [coeff_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [coeff_smul, coeff_sum_sign_prod_dd_monomial, smul_eq_mul, mul_comm]
  have hX : logHeight X = (s + 1) * logHeight x := by
    simpa [X] using logHeight_fun_prod_eq (ι := fun _ : Fin (s + 1) => P.support)
      (x := fun _ => x) fun _ => coeff_support_ne_zero hP
  have hA : logHeight A ≤ totalWeight K *
      Real.log ((s + 1).factorial * 2 ^ ((s + 1) * ∑ k, r k)) :=
    logHeight_intCast_le (fun jt : W.support × (Fin (s + 1) → P.support) =>
      zcoef J jt.1 (fun ν => (jt.2 ν : Fin N →₀ ℕ)))
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast (s + 1).factorial_pos)
        (one_le_pow₀ (by norm_num)))
      fun jt => by exact_mod_cast abs_zcoef_le J r jt.1 _ fun ν k => hr _ (jt.2 ν).2 k
  have key := logHeight_linearMap_apply_le A X
  rw [← hW, ← logHeight_coeff_eq] at key
  rw [logHeight_coeff_eq P, Real.log_mul (by positivity) (by positivity), Real.log_pow] at *
  have := mul_le_mul_of_nonneg_left (log_card_fun_support_le (s := s) P r hr)
    (Nat.cast_nonneg (totalWeight K) : (0 : ℝ) ≤ _)
  push_cast at hA this ⊢
  nlinarith

end WronskianHeight

section DisjointVariables

variable {K : Type*} [Field K] {n : ℕ}

/-- The exponent of `ς^a ς_m^b` for `a` in the first `n + 1` variables and `b` in the last. -/
private noncomputable def joinExp (a : Fin (n + 1) →₀ ℕ) (b : Fin 1 →₀ ℕ) : Fin (n + 2) →₀ ℕ :=
  a.mapDomain Fin.castSucc + b.mapDomain (fun _ => Fin.last (n + 1))

private lemma joinExp_apply_castSucc (a : Fin (n + 1) →₀ ℕ) (b : Fin 1 →₀ ℕ) (i : Fin (n + 1)) :
    joinExp a b i.castSucc = a i := by
  have h1 : i.castSucc ∉ Set.range (fun _ : Fin 1 => Fin.last (n + 1)) := by
    rintro ⟨_, h⟩
    exact (Fin.castSucc_lt_last i).ne' h
  rw [joinExp, Finsupp.add_apply,
    Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective _),
    Finsupp.mapDomain_of_notMem_range _ _ h1, add_zero]

private lemma joinExp_apply_last (a : Fin (n + 1) →₀ ℕ) (b : Fin 1 →₀ ℕ) :
    joinExp a b (Fin.last (n + 1)) = b 0 := by
  have h1 : Fin.last (n + 1) ∉ Set.range Fin.castSucc := by
    rintro ⟨i, h⟩
    exact (Fin.castSucc_lt_last i).ne h
  have h2 := Finsupp.mapDomain_apply_of_injective (f := fun _ : Fin 1 => Fin.last (n + 1))
    (fun x y _ => Subsingleton.elim x y) b 0
  rw [joinExp, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ h1, zero_add]
  exact h2

private lemma joinExp_injective :
    Function.Injective (fun ab : (Fin (n + 1) →₀ ℕ) × (Fin 1 →₀ ℕ) => joinExp ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  refine Prod.ext (Finsupp.ext fun i => ?_) (Finsupp.ext fun i => ?_)
  · simpa [joinExp_apply_castSucc] using congrArg (fun c => c i.castSucc) h
  · rw [Subsingleton.elim i 0]
    simpa [joinExp_apply_last] using congrArg (fun c => c (Fin.last (n + 1))) h

private lemma rename_mul_rename_eq_sum (U : MvPolynomial (Fin (n + 1)) K)
    (V : MvPolynomial (Fin 1) K) :
    rename Fin.castSucc U * rename (fun _ => Fin.last (n + 1)) V =
      ∑ a ∈ U.support, ∑ b ∈ V.support, monomial (joinExp a b) (U.coeff a * V.coeff b) := by
  conv_lhs => rw [as_sum U, as_sum V]
  simp only [map_sum, rename_monomial, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial,
    joinExp]
  exact Finset.sum_comm

private lemma coeff_rename_mul_rename (U : MvPolynomial (Fin (n + 1)) K)
    (V : MvPolynomial (Fin 1) K) (a : Fin (n + 1) →₀ ℕ) (b : Fin 1 →₀ ℕ) :
    (rename Fin.castSucc U * rename (fun _ => Fin.last (n + 1)) V).coeff (joinExp a b) =
      U.coeff a * V.coeff b := by
  classical
  rw [rename_mul_rename_eq_sum, coeff_sum]
  simp only [coeff_sum, coeff_monomial]
  have hinj := @joinExp_injective n
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      rw [ite_eq_right]
      intro h
      exact hb' (congrArg Prod.snd (hinj (a₁ := (a, b')) (a₂ := (a, b)) h))
    · intro hb
      rw [ite_eq_left rfl, notMem_support_iff.mp hb, mul_zero]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [ite_eq_right]
    intro h
    exact ha' (congrArg Prod.fst (hinj (a₁ := (a', b')) (a₂ := (a, b)) h))
  · intro ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    split_ifs
    · rw [notMem_support_iff.mp ha, zero_mul]
    · rfl

/-- **Heights of products in disjoint variables.** `h(U V) = h(U) + h(V)` when `U` involves only
the first `n + 1` variables and `V` only the last one. -/
private lemma logHeight_rename_mul_rename [AdmissibleAbsValues K]
    {U : MvPolynomial (Fin (n + 1)) K} (hU : U ≠ 0) {V : MvPolynomial (Fin 1) K} (hV : V ≠ 0) :
    Finsupp.logHeight (AddMonoidAlgebra.coeff
        (rename Fin.castSucc U * rename (fun _ => Fin.last (n + 1)) V)) =
      Finsupp.logHeight (AddMonoidAlgebra.coeff U) +
        Finsupp.logHeight (AddMonoidAlgebra.coeff V) := by
  set W := rename Fin.castSucc U * rename (fun _ => Fin.last (n + 1)) V with hWdef
  let e : U.support × V.support → (Fin (n + 2) →₀ ℕ) := fun ab => joinExp ab.1 ab.2
  have he : Function.Injective e := fun x y h => by
    have := joinExp_injective (n := n) (a₁ := ((x.1 : _), (x.2 : _)))
      (a₂ := ((y.1 : _), (y.2 : _))) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst this)) (Subtype.ext (congrArg Prod.snd this))
  have hsupp : ∀ c ∈ (AddMonoidAlgebra.coeff W).support, c ∈ Set.range e := by
    intro c hc
    have hc' : W.coeff c ≠ 0 := Finsupp.mem_support_iff.mp hc
    rw [hWdef, rename_mul_rename_eq_sum, coeff_sum] at hc'
    obtain ⟨a, ha, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc'
    rw [coeff_sum] at hc'
    obtain ⟨b, hb, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc'
    rw [coeff_monomial] at hc'
    split_ifs at hc' with h
    · exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), h⟩
    · exact absurd rfl hc'
  unfold Finsupp.logHeight
  rw [mulHeight_finsupp_eq_comp _ he hsupp, mulHeight_finsupp_eq, mulHeight_finsupp_eq,
    Finsupp.mulHeight, Finsupp.mulHeight,
    ← Real.log_mul (mulHeight_ne_zero _) (mulHeight_ne_zero _)]
  congr 1
  have h1 : (fun i => (AddMonoidAlgebra.coeff W) (e i)) =
      fun ab : U.support × V.support => U.coeff (ab.1 : Fin (n + 1) →₀ ℕ) *
        V.coeff (ab.2 : Fin 1 →₀ ℕ) :=
    funext fun ab => coeff_rename_mul_rename U V ab.1 ab.2
  rw [h1, mulHeight_fun_mul_eq (coeff_support_ne_zero hU) (coeff_support_ne_zero hV)]
  rfl

end DisjointVariables

section Numerics

/-- The numerical heart of the estimate: `(2 ρ + r_m) log 2 ≤ 2 r₁` with `ρ = r₁ + ⋯ + r_m`. -/
private lemma two_mul_sum_add_last_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 2) (r : Fin (n + 1) → ℕ) (hr : ∀ μ, 0 < r μ)
    (hratio : ∀ μ : Fin n, (r μ.succ : ℝ) / r μ.castSucc ≤ ε ^ (2 ^ n)) :
    (2 * ∑ k, (r k : ℝ) + r (Fin.last n)) * Real.log 2 ≤ 2 * r 0 := by
  set q := ε ^ (2 ^ n) with hq
  have hq0 : 0 ≤ q := by positivity
  have hstep : ∀ μ : Fin n, (r μ.succ : ℝ) ≤ q * r μ.castSucc := fun μ =>
    (div_le_iff₀ (by exact_mod_cast hr μ.castSucc)).mp (hratio μ)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hr0 : (0 : ℝ) ≤ r 0 := Nat.cast_nonneg _
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    have hq4 : q ≤ 1 / 4 := by
      rw [hq]
      have : ε ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hε.le hε'.le 2
      norm_num at this ⊢
      linarith
    have h1 := hstep 0
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at h1
    rw [Fin.sum_univ_two, show Fin.last 1 = 1 from rfl]
    have h1' : (r 1 : ℝ) ≤ r 0 / 4 := by nlinarith
    nlinarith
  · have hq16 : q ≤ 1 / 16 := by
      have h4 : 4 ≤ 2 ^ n :=
        (by norm_num : 4 = 2 ^ 2).trans_le (Nat.pow_le_pow_right two_pos hn2)
      have : ε ^ (2 ^ n) ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le (by linarith) h4
      have h' : ε ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ hε.le hε'.le 4
      rw [hq]; norm_num at h' ⊢; linarith
    have hgeom : ∀ k (hk : k < n + 1), (r ⟨k, hk⟩ : ℝ) ≤ q ^ k * r 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro hk
        have h := hstep ⟨k, by omega⟩
        have e1 : (Fin.succ ⟨k, by omega⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ := rfl
        have e2 : (Fin.castSucc ⟨k, by omega⟩ : Fin (n + 1)) = ⟨k, by omega⟩ := rfl
        rw [e1, e2] at h
        calc (r ⟨k + 1, hk⟩ : ℝ) ≤ q * r ⟨k, by omega⟩ := h
          _ ≤ q * (q ^ k * r 0) := mul_le_mul_of_nonneg_left (ih (by omega)) hq0
          _ = q ^ (k + 1) * r 0 := by ring
    have hsum : ∑ k, (r k : ℝ) ≤ 16 / 15 * r 0 := by
      calc ∑ k, (r k : ℝ) ≤ ∑ k : Fin (n + 1), q ^ (k : ℕ) * r 0 :=
            Finset.sum_le_sum fun k _ => hgeom k k.2
        _ = (∑ i ∈ Finset.range (n + 1), q ^ i) * r 0 := by
            rw [Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => q ^ i * (r 0 : ℝ))]
        _ ≤ (1 - q)⁻¹ * r 0 := by
            refine mul_le_mul_of_nonneg_right ?_ hr0
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1) hq0 (by linarith)
            rw [← Finset.range_eq_Ico, pow_zero] at this
            simpa [one_div] using this
        _ ≤ 16 / 15 * r 0 := by
            refine mul_le_mul_of_nonneg_right ?_ hr0
            rw [inv_le_iff_one_le_mul₀ (by linarith)]
            linarith
    have hlast : (r (Fin.last n) : ℝ) ≤ r 0 / 16 := by
      have hqn : q ^ n ≤ q := pow_le_of_le_one hq0 (by linarith) (by omega)
      calc (r (Fin.last n) : ℝ) ≤ q ^ n * r 0 := hgeom n (by omega)
        _ ≤ (1 / 16) * r 0 := mul_le_mul_of_nonneg_right (hqn.trans hq16) hr0
        _ = r 0 / 16 := by ring
    nlinarith

/-- `log ((s + 1)!) ≤ (s + 1) s log 2`. -/
private lemma log_factorial_succ_le (s : ℕ) :
    Real.log (s + 1).factorial ≤ (s + 1) * s * Real.log 2 := by
  have h : (s + 1).factorial ≤ 2 ^ (s * (s + 1)) := by
    calc (s + 1).factorial ≤ (s + 1) ^ (s + 1) := Nat.factorial_le_pow _
      _ ≤ (2 ^ s) ^ (s + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self _
      _ = 2 ^ (s * (s + 1)) := by rw [← pow_mul]
  calc Real.log (s + 1).factorial ≤ Real.log ((2 : ℝ) ^ (s * (s + 1))) :=
        Real.log_le_log (by exact_mod_cast (s + 1).factorial_pos) (by exact_mod_cast h)
    _ = (s + 1) * s * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- The constant of the estimate: `2 (s + 1) ρ log 2 + log ((s + 1)!) ≤ 2 (s + 1) r₁`, given
`s ≤ r_m` and `(2 ρ + r_m) log 2 ≤ 2 r₁`. -/
private lemma const_le {n s : ℕ} (r : Fin (n + 1) → ℕ) (hs : s ≤ r (Fin.last n))
    (hnum : (2 * ∑ k, (r k : ℝ) + r (Fin.last n)) * Real.log 2 ≤ 2 * r 0) :
    2 * (s + 1) * (∑ k, (r k : ℝ)) * Real.log 2 + Real.log (s + 1).factorial ≤
      (s + 1) * (2 * r 0) := by
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : (s + 1) * ((2 * ∑ k, (r k : ℝ) + s) * Real.log 2) ≤ (s + 1) * (2 * r 0) :=
    mul_le_mul_of_nonneg_left (le_trans (by gcongr) hnum) (by positivity)
  nlinarith [log_factorial_succ_le s]

end Numerics

/-- **Heights of the Wronskian factors.** Let `K` be a number field, `n ≥ 1`, `0 < ε < 1/2`,
and `r : Fin (n + 1) → ℕ` positive with `r_{μ+1} / r_μ ≤ ε^{2^n}`. Let
`P = ∑_{j ≤ s} φ_j(X 0, …, X (n-1)) ψ_j(X n) ≠ 0` with `deg_{X i} P ≤ r i` and `s ≤ r n`, and
let `I' : Fin (s + 1) → Fin n → ℕ` with `∑ₖ I' μ k ≤ s`. If `U = generalizedWronskian I' φ`
and the one-variable Wronskian `V` of the `ψ_j` are nonzero, then
`h(U) + h(V) ≤ (s + 1) (h(P) + 2 r 0)`, where `h` is `Finsupp.logHeight` of the coefficients
divided by `[K : ℚ]`. -/
@[faltings "lem_bvr_roth_height_wronskian"]
public theorem logHeight_generalizedWronskian_add_le {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) (r : Fin (n + 1) → ℕ)
    (hr : ∀ μ, 0 < r μ)
    (hratio : ∀ μ : Fin n, (r μ.succ : ℝ) / r μ.castSucc ≤ ε ^ (2 ^ n))
    {P : MvPolynomial (Fin (n + 1)) K} (hP : P ≠ 0) (hP_deg : ∀ i, P.degreeOf i ≤ r i)
    {s : ℕ} (hs : s ≤ r (Fin.last n)) (φ : Fin (s + 1) → MvPolynomial (Fin n) K)
    (ψ : Fin (s + 1) → Polynomial K)
    (hPeq : P = ∑ j, rename Fin.castSucc (φ j) * Polynomial.aeval (X (Fin.last n)) (ψ j))
    (I' : Fin (s + 1) → Fin n → ℕ) (hI : ∀ μ, ∑ k, I' μ k ≤ s)
    (hU : generalizedWronskian I' φ ≠ 0)
    (hV : generalizedWronskian (fun ν _ => (ν : ℕ))
      (fun j => Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) (ψ j)) ≠ 0) :
    Finsupp.logHeight (AddMonoidAlgebra.coeff (generalizedWronskian I' φ)) /
        Module.finrank ℚ K +
      Finsupp.logHeight (AddMonoidAlgebra.coeff (generalizedWronskian (fun ν _ => (ν : ℕ))
        (fun j => Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) (ψ j)))) /
        Module.finrank ℚ K ≤
      (s + 1) * (Finsupp.logHeight (AddMonoidAlgebra.coeff P) / Module.finrank ℚ K +
        2 * r 0) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set ψ' : Fin (s + 1) → MvPolynomial (Fin 1) K :=
    fun j => Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) (ψ j)
  have hPeq' : P = ∑ j, rename Fin.castSucc (φ j) * rename (fun _ => Fin.last (n + 1)) (ψ' j) := by
    rw [hPeq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Polynomial.aeval_algHom_apply, rename_X]
  have hsum := logHeight_rename_mul_rename hU hV
  rw [← rothWronskian_sum_mul_eq I' φ ψ', ← hPeq'] at hsum
  have hdet : rothWronskian I' P = Matrix.det (Matrix.of fun μ ν =>
      MvPolynomial.hasseDeriv
        (Finsupp.equivFunOnFinite.symm (Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ))) P) := by
    simp only [Faltings.MvPolynomial.hasseDeriv_eq_inv_prod_factorial_smul,
      Finsupp.equivFunOnFinite_symm_apply_apply, LinearMap.smul_apply]
    rfl
  have hbound := logHeight_det_dd_le (fun μ ν => Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ)) hP r
    (fun b hb k => (monomial_le_degreeOf k hb).trans (hP_deg k))
  rw [← hdet, hsum, NumberField.totalWeight_eq_finrank] at hbound
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have := mul_le_mul_of_nonneg_left
    (const_le r hs (two_mul_sum_add_last_mul_log_two_le hn hε hε' r hr hratio)) hd.le
  push_cast at hbound
  rw [← add_div, div_le_iff₀ hd, mul_add, add_mul, mul_div_assoc', div_mul_cancel₀ _ hd.ne']
  linarith

end Faltings
