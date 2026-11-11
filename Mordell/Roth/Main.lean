module
public import Mordell.Roth.Wronskian.NeZero
public import Mordell.Roth.Index.Mul
public import Mordell.Roth.Index.HasseDeriv
public import Mordell.Roth.Index.Range
public import Mordell.Roth.Index.Add
public import Mordell.Roth.ElementaryInequality
public import Mordell.Roth.SplitLastVariable
public import Mordell.Roth.WronskianHeight
public import Mordell.Roth.OneVariable
public import Mordell.Roth.Wronskian.Degree

/-!
# Roth's lemma

Let `K` be a number field and `P ∈ K[ς₁, …, ςₘ]` a nonzero polynomial with
`deg_{ς_μ} P ≤ r_μ` for positive integers `r₁, …, rₘ`. Let `ς⁰ ∈ Kᵐ` and
`Z = min_μ r_μ h(ς⁰_μ)`. If `ε > 0` satisfies `r_{μ+1} / r_μ ≤ ε^{2^{m-1}}` for
`μ = 1, …, m - 1` and `Z ≥ ε^{-2^{m-1}} (h(P) + 2 m r₁)`, then some divided derivative
`∂_{I*} P` does not vanish at `ς⁰`, for a multi-index `I* = (i*₁, …, i*ₘ)` of weight
`∑_μ i*_μ / r_μ ≤ 2 m ε`. In other words, the index of `P` at `ς⁰` with respect to
`(r₁, …, rₘ)` is at most `2 m ε`.

Here `h` is the absolute logarithmic Weil height: `h(x) = Height.logHeight₁ x / [K : ℚ]` for
`x ∈ K`, and `h(P)` is the height of the point of projective space whose homogeneous
coordinates are the coefficients of `P`, i.e. `Finsupp.logHeight` of the coefficient vector of
`P`, divided by `[K : ℚ]`. The divided derivative is
`∂_I = (i₁! ⋯ iₘ!)⁻¹ ∂^{i₁}/∂ς₁^{i₁} ⋯ ∂^{iₘ}/∂ςₘ^{iₘ}`.

The proof follows Bombieri and runs by induction on the number `m` of variables. It suffices to
bound the index `t = ind(P)` of `P` with respect to `(r₁, …, rₘ)` at `ς⁰` by `2 m ε`, since the
index is attained.
For `m = 1` this is Roth's lemma in one variable. For `m ≥ 2`, write
`P = ∑ⱼ φⱼ(ς₁, …, ς_{m-1}) ψⱼ(ςₘ)` with both families linearly independent, take a nonzero
generalized Wronskian `U` of the `φⱼ` and the Wronskian `V` of the `ψⱼ`, and compare a lower
bound for the index of `W = UV`, read off the determinant defining `W`, with the upper bound
coming from the induction hypothesis applied to `U` and from the one-variable lemma applied
to `V`.

## Main results

* `Faltings.exists_eval_dividedDeriv_ne_zero_of_roth`: Roth's lemma.

## Implementation notes

The source's "algebraic coefficients" and "algebraic point" are taken in a number field `K`
containing all of them; the heights are normalised by `[K : ℚ]`, so they are the absolute
heights and do not depend on `K`. The variables are `Fin m` with `m ≥ 1` (`[NeZero m]`), so
that `r₁ = r 0` makes sense. The condition `Z ≥ ε^{-2^{m-1}} (h(P) + 2 m r₁)` on the minimum
`Z` is written as the same lower bound for every `r_μ h(ς⁰_μ)`, which is equivalent. The
divided derivative is written as the scalar `(∏_μ i_μ!)⁻¹` times the composite, in
`Module.End K`, of the iterated partial derivatives `MvPolynomial.pderiv μ ^ i_μ` in the order
`μ = 0, …, m - 1`; these commute, so the order is immaterial.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, pp. 633–636
-/

open _root_.MvPolynomial
open scoped ENNReal

namespace Faltings

section OneVariable

variable {K : Type*} [Field K]

/-- The height of a one-variable polynomial does not depend on whether it is read in
`MvPolynomial (Fin 1) K` or in `K[X]`. -/
private lemma logHeight_uniqueAlgEquiv [Height.AdmissibleAbsValues K]
    (Q : MvPolynomial (Fin 1) K) :
    Finsupp.logHeight (uniqueAlgEquiv K (Fin 1) Q).toFinsupp.coeff =
      Finsupp.logHeight (AddMonoidAlgebra.coeff Q) := by
  let e : ℕ ≃ (Fin 1 →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (Equiv.funUnique (Fin 1) ℕ)).symm
  have he (n : ℕ) : e n = Finsupp.single 0 n :=
    Finsupp.ext fun i => by simp [e, Fin.fin_one_eq_zero i]
  have h : ⇑(uniqueAlgEquiv K (Fin 1) Q).toFinsupp.coeff = ⇑(AddMonoidAlgebra.coeff Q) ∘ e := by
    funext n
    simp only [Function.comp_apply, he]
    exact coeff_uniqueAlgEquiv (R := K) (σ := Fin 1) (P := Q) (n := n)
  unfold Finsupp.logHeight
  rw [h, Height.mulHeight_comp_equiv]

/-- Evaluation of a one-variable `MvPolynomial` is evaluation of the corresponding polynomial. -/
private lemma eval_uniqueAlgEquiv (ξ : K) (q : MvPolynomial (Fin 1) K) :
    Polynomial.eval ξ (uniqueAlgEquiv K (Fin 1) q) = eval (fun _ => ξ) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p n hp => rw [map_mul, Polynomial.eval_mul, hp]; simp

/-- The degree of the polynomial attached to `Q ∈ K[ς]` is its degree in `ς`. -/
private lemma natDegree_uniqueAlgEquiv_le {Q : MvPolynomial (Fin 1) K} {R : ℕ}
    (h : Q.degreeOf 0 ≤ R) : (uniqueAlgEquiv K (Fin 1) Q).natDegree ≤ R := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_
  rw [coeff_uniqueAlgEquiv (R := K) (σ := Fin 1)]
  by_contra hc
  have := monomial_le_degreeOf 0 (mem_support_iff.2 hc)
  simp at this
  omega

/-- **Roth's lemma in one variable**, for `Q ∈ K[ς]` written as an `MvPolynomial (Fin 1) K`:
some divided derivative of order `i ≤ ε R` does not vanish at `ξ`. -/
private lemma exists_dividedDeriv_ne_zero_one_var [NumberField K] {Q : MvPolynomial (Fin 1) K}
    (hQ : Q ≠ 0) {R : ℕ} (hdeg : Q.degreeOf 0 ≤ R) (ξ : K) {ε : ℝ} (hε : 0 < ε)
    (hheight : ε⁻¹ * (Finsupp.logHeight (AddMonoidAlgebra.coeff Q) / Module.finrank ℚ K + R) ≤
      R * (Height.logHeight₁ ξ / Module.finrank ℚ K)) :
    ∃ i : ℕ, eval (fun _ => ξ) (((i.factorial : K))⁻¹ • ((pderiv (0 : Fin 1)).toLinearMap ^ i) Q)
      ≠ 0 ∧ (i : ℝ) ≤ ε * R := by
  set p := uniqueAlgEquiv K (Fin 1) Q
  have hp : p ≠ 0 := fun h => hQ ((uniqueAlgEquiv K (Fin 1)).injective (h.trans (map_zero _).symm))
  have hex : ∃ i, (Polynomial.hasseDeriv i p).eval ξ ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.taylor_injective ξ
    ext n
    simp [Polynomial.taylor_coeff, h]
  classical
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rw [← eval_uniqueAlgEquiv, uniqueAlgEquiv_divided_pderiv]
    exact Nat.find_spec hex
  · refine le_mul_of_hasseDeriv_eval_ne_zero hp (natDegree_uniqueAlgEquiv_le hdeg)
      (fun j hj => ?_) (Nat.find_spec hex) hε ?_
    · simpa using Nat.find_min hex hj
    · rwa [logHeight_uniqueAlgEquiv]

end OneVariable

section Index

variable {K : Type*} [Field K] [CharZero K] {m : ℕ} (r : Fin m → ℕ+) (ς₀ : Fin m → K)

/-- With `L = ∏ μ, r μ`, the weight `∑ μ, I μ / r μ` is the natural number
`∑ μ, I μ * (L / r μ)` divided by `L`. -/
private lemma sum_div_eq_div (I : Fin m → ℕ) :
    ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) =
      ((∑ μ, I μ * ((∏ ν, (r ν : ℕ)) / r μ) : ℕ) : ℝ≥0∞) / ((∏ ν, (r ν : ℕ) : ℕ) : ℝ≥0∞) := by
  set L : ℕ := ∏ ν, (r ν : ℕ)
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ν _ => (r ν).ne_zero
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hdvd : (r μ : ℕ) ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_univ μ)
  have hw : ((r μ : ℕ) : ℝ≥0∞) * ((L / r μ : ℕ) : ℝ≥0∞) = (L : ℝ≥0∞) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  have hw0 : L / r μ ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) hdvd) (r μ).pos).ne'
  rw [← hw, Nat.cast_mul, ← div_eq_mul_inv,
    ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hw0) (ENNReal.natCast_ne_top _)]

/-- A finite index is attained: some multi-index realises the minimum. -/
private lemma exists_eval_ne_zero_sum_eq_index {Q : MvPolynomial (Fin m) K}
    (hQ : MvPolynomial.index r ς₀ Q < ⊤) :
    ∃ I : Fin m →₀ ℕ, eval ς₀ ((∏ μ, ((I μ).factorial : K))⁻¹ •
        (List.ofFn fun μ : Fin m => (pderiv μ).toLinearMap ^ I μ :
          List (Module.End K (MvPolynomial (Fin m) K))).prod Q) ≠ 0 ∧
      ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) = MvPolynomial.index r ς₀ Q := by
  classical
  set key : (Fin m →₀ ℕ) → ℕ := fun I => ∑ μ, I μ * ((∏ ν, (r ν : ℕ)) / r μ)
  have hex : ∃ k, ∃ I : Fin m →₀ ℕ, eval ς₀ ((∏ μ, ((I μ).factorial : K))⁻¹ •
        (List.ofFn fun μ : Fin m => (pderiv μ).toLinearMap ^ I μ :
          List (Module.End K (MvPolynomial (Fin m) K))).prod Q) ≠ 0 ∧ key I = k := by
    by_contra! h
    refine hQ.ne (iInf₂_eq_top.2 fun I hI => absurd rfl (h _ I hI))
  obtain ⟨I, hI, hk⟩ := Nat.find_spec hex
  refine ⟨I, hI, le_antisymm ?_ (iInf₂_le I hI)⟩
  refine le_iInf₂ fun J hJ => ?_
  rw [sum_div_eq_div, sum_div_eq_div]
  refine ENNReal.div_le_div_right ?_ _
  exact Nat.cast_le.2 (show key I ≤ key J from hk.trans_le (Nat.find_min' hex ⟨J, hJ, rfl⟩))

end Index

section Rename

variable {K : Type*} [Field K]

private lemma pderiv_pow_rename {σ τ : Type*} {f : σ → τ} (hf : Function.Injective f) (x : σ)
    (e : ℕ) (p : MvPolynomial σ K) :
    ((pderiv (f x)).toLinearMap ^ e : Module.End K (MvPolynomial τ K)) (rename f p) =
      rename f (((pderiv x).toLinearMap ^ e : Module.End K (MvPolynomial σ K)) p) := by
  induction e generalizing p with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
    exact congrArg _ (pderiv_rename hf x p)

private lemma ofFn_prod_pderiv_rename {σ τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    {N : ℕ} (g : Fin N → σ) (e : Fin N → ℕ) (p : MvPolynomial σ K) :
    (List.ofFn fun k => (pderiv (f (g k))).toLinearMap ^ e k :
        List (Module.End K (MvPolynomial τ K))).prod (rename f p) =
      rename f ((List.ofFn fun k => (pderiv (g k)).toLinearMap ^ e k :
        List (Module.End K (MvPolynomial σ K))).prod p) := by
  induction N generalizing p with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ih (fun k => g k.succ)
      (fun k => e k.succ), pderiv_pow_rename hf, List.ofFn_succ, List.prod_cons,
      Module.End.mul_apply]

/-- The divided derivative `∂_{(J, 0)}` of a polynomial not involving the last variable. -/
private lemma dividedDeriv_snoc_zero_rename_castSucc {n : ℕ} (J : Fin (n + 1) → ℕ)
    (U : MvPolynomial (Fin (n + 1)) K) :
    (∏ k, ((Fin.snoc (α := fun _ => ℕ) J 0 k).factorial : K))⁻¹ •
        (List.ofFn fun k => (pderiv k).toLinearMap ^ Fin.snoc (α := fun _ => ℕ) J 0 k :
          List (Module.End K (MvPolynomial (Fin (n + 2)) K))).prod (rename Fin.castSucc U) =
      rename Fin.castSucc ((∏ k, ((J k).factorial : K))⁻¹ •
        (List.ofFn fun k => (pderiv k).toLinearMap ^ J k :
          List (Module.End K (MvPolynomial (Fin (n + 1)) K))).prod U) := by
  rw [List.ofFn_succ', List.prod_concat, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, pow_zero, mul_one, Nat.factorial_zero,
    Nat.cast_one]
  rw [map_smul]
  congr 1
  exact ofFn_prod_pderiv_rename (Fin.castSucc_injective _) id J U

/-- The divided derivative `∂_{(0, i)}` of a polynomial in the last variable only. -/
private lemma dividedDeriv_snoc_rename_last {n : ℕ} (i : ℕ) (V : MvPolynomial (Fin 1) K) :
    (∏ k, ((Fin.snoc (α := fun _ => ℕ) (0 : Fin (n + 1) → ℕ) i k).factorial : K))⁻¹ •
        (List.ofFn fun k => (pderiv k).toLinearMap ^ Fin.snoc (α := fun _ => ℕ)
          (0 : Fin (n + 1) → ℕ) i k :
          List (Module.End K (MvPolynomial (Fin (n + 2)) K))).prod
          (rename (fun _ => Fin.last (n + 1)) V) =
      rename (fun _ => Fin.last (n + 1)) (((i.factorial : K))⁻¹ •
        ((pderiv (0 : Fin 1)).toLinearMap ^ i : Module.End K (MvPolynomial (Fin 1) K)) V) := by
  rw [List.ofFn_succ', List.prod_concat, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, pow_zero, Nat.factorial_zero,
    Nat.cast_one, List.ofFn_const, List.prod_replicate, one_pow, Finset.prod_const_one, one_mul]
  rw [map_smul]
  congr 1
  exact pderiv_pow_rename (f := fun _ : Fin 1 => Fin.last (n + 1))
    (fun a b _ => Subsingleton.elim a b) 0 i V

end Rename

section Main

variable {K : Type*} [Field K]

/-- The weight `∑ μ, i_μ / r_μ` in `ℝ≥0∞` is the real weight. -/
private lemma sum_div_eq_ofReal {m : ℕ} (r : Fin m → ℕ+) (I : Fin m → ℕ) :
    ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) =
      ENNReal.ofReal (∑ μ, (I μ : ℝ) / ((r μ : ℕ) : ℝ)) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun μ _ => by positivity]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast (r μ).pos), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

private lemma index_le_of_eval_ne_zero [CharZero K] {m : ℕ} (r : Fin m → ℕ+)
    (ς₀ : Fin m → K) {Q : MvPolynomial (Fin m) K} (I : Fin m → ℕ)
    (h : eval ς₀ ((∏ μ, ((I μ).factorial : K))⁻¹ •
        (List.ofFn fun μ : Fin m => (pderiv μ).toLinearMap ^ I μ :
          List (Module.End K (MvPolynomial (Fin m) K))).prod Q) ≠ 0) :
    MvPolynomial.index r ς₀ Q ≤ ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) :=
  iInf₂_le (Finsupp.equivFunOnFinite.symm I) h

private lemma index_le_index_dividedDeriv_add [CharZero K] {m : ℕ} (r : Fin m → ℕ+)
    (ς₀ : Fin m → K) (Q : MvPolynomial (Fin m) K) (I : Fin m → ℕ) :
    MvPolynomial.index r ς₀ Q ≤ MvPolynomial.index r ς₀
        ((∏ μ, ((I μ).factorial : K))⁻¹ •
        (List.ofFn fun μ : Fin m => (pderiv μ).toLinearMap ^ I μ :
          List (Module.End K (MvPolynomial (Fin m) K))).prod Q) +
      ∑ μ, ((I μ : ℝ≥0∞) / (r μ : ℝ≥0∞)) :=
  MvPolynomial.index_le_index_hasseDeriv_add r ς₀ Q (Finsupp.equivFunOnFinite.symm I)

private lemma uniqueAlgEquiv_aeval_X (p : Polynomial K) :
    uniqueAlgEquiv K (Fin 1) (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a => simp [← Polynomial.C_mul_X_pow_eq_monomial]

private lemma aeval_X_zero_injective :
    Function.Injective (Polynomial.aeval (R := K) (X 0 : MvPolynomial (Fin 1) K)) :=
  Function.LeftInverse.injective (uniqueAlgEquiv_aeval_X (K := K))

private lemma degreeOf_aeval_X_le (p : Polynomial K) :
    (Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) p).degreeOf 0 ≤ p.natDegree := by
  rw [degreeOf_le_iff]
  intro d hd
  have h := coeff_uniqueAlgEquiv (R := K) (σ := Fin 1)
    (P := Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) p) (d 0)
  rw [uniqueAlgEquiv_aeval_X, show (Finsupp.single default (d 0) : Fin 1 →₀ ℕ) = d from
    (Finsupp.unique_single d).symm] at h
  exact Polynomial.le_natDegree_of_ne_zero (h ▸ mem_support_iff.1 hd)

/-- The closing comparison of Roth's lemma: if `0 ≤ t ≤ M` with `1 ≤ M` and
`min (t / 2) (t ^ 2 / 2) ≤ 2 M ε²`, then `t ≤ 2 M ε`. -/
private lemma le_two_mul_of_min_le {t M ε : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) (hM : 1 ≤ M)
    (hε : 0 ≤ ε) (h : min (t / 2) (t ^ 2 / 2) ≤ 2 * M * ε ^ 2) : t ≤ 2 * M * ε := by
  refine (pow_le_pow_iff_left₀ ht (by positivity) two_ne_zero).1 ?_
  rcases min_choice (t / 2) (t ^ 2 / 2) with h' | h' <;> rw [h'] at h <;>
    nlinarith [mul_le_mul_of_nonneg_left htM ht,
      mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ M * ε ^ 2)]

/-- If `(s + 1) a ≤ ∑ ν, max (b ν) 0` and `0 ≤ δ`, then
`(s + 1) (a - δ) ≤ ∑ ν, max (b ν - δ) 0`. -/
private lemma mul_sub_le_sum_max_sub {s : ℕ} {a δ : ℝ} (hδ : 0 ≤ δ) {b : Fin (s + 1) → ℝ}
    (h : ((s : ℝ) + 1) * a ≤ ∑ ν, max (b ν) 0) :
    ((s : ℝ) + 1) * (a - δ) ≤ ∑ ν, max (b ν - δ) 0 := by
  have h2 (ν : Fin (s + 1)) : max (b ν) 0 - δ ≤ max (b ν - δ) 0 := by
    rcases le_total 0 (b ν) with hb | hb
    · rw [max_eq_left hb]
      exact le_max_left _ _
    · rw [max_eq_right hb]
      linarith [le_max_right (b ν - δ) 0]
  calc ((s : ℝ) + 1) * (a - δ) = (s + 1) * a - ∑ _ν : Fin (s + 1), δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ ν, max (b ν) 0 - ∑ _ν : Fin (s + 1), δ := by gcongr
    _ = ∑ ν, (max (b ν) 0 - δ) := by rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun ν _ => h2 ν

/-- Roth's lemma for polynomials in `n + 1` variables. -/
private def RothStatement (K : Type*) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ (P : MvPolynomial (Fin (n + 1)) K), P ≠ 0 → ∀ (r : Fin (n + 1) → ℕ), (∀ μ, 0 < r μ) →
    (∀ μ, P.degreeOf μ ≤ r μ) → ∀ (ς₀ : Fin (n + 1) → K) {ε : ℝ}, 0 < ε →
    (∀ (μ : Fin (n + 1)) (hμ : μ.val + 1 < n + 1),
      (r ⟨μ.val + 1, hμ⟩ : ℝ) / r μ ≤ ε ^ (2 ^ (n + 1 - 1))) →
    (∀ μ, (ε ^ (2 ^ (n + 1 - 1)))⁻¹ *
        (Finsupp.logHeight (AddMonoidAlgebra.coeff P) / Module.finrank ℚ K +
          2 * ((n + 1 : ℕ) : ℝ) * r 0) ≤
      r μ * (Height.logHeight₁ (ς₀ μ) / Module.finrank ℚ K)) →
    ∃ I : Fin (n + 1) → ℕ,
      eval ς₀ ((∏ μ, ((I μ).factorial : K))⁻¹ •
          (List.ofFn fun μ => (pderiv μ).toLinearMap ^ I μ :
            List (Module.End K (MvPolynomial (Fin (n + 1)) K))).prod P) ≠ 0 ∧
        ∑ μ, (I μ : ℝ) / r μ ≤ 2 * ((n + 1 : ℕ) : ℝ) * ε

private lemma roth_base [NumberField K] : RothStatement K 0 := by
  intro P hP r hr hdeg ς₀ ε hε _ hZ
  have hd : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  have hP0 := div_nonneg (zero_le_finsuppLogHeight (AddMonoidAlgebra.coeff P)) hd
  have hr0 : (0 : ℝ) < r 0 := by exact_mod_cast hr 0
  obtain ⟨i, hi, hiε⟩ := exists_dividedDeriv_ne_zero_one_var hP (hdeg 0) (ς₀ 0) hε (by
    have := hZ 0
    simp only [Nat.zero_add, Nat.sub_self, pow_zero, pow_one, Nat.cast_one, mul_one] at this
    refine le_trans ?_ this
    gcongr
    linarith)
  have hς : ς₀ = fun _ => ς₀ 0 := funext fun μ => by rw [Fin.fin_one_eq_zero μ]
  refine ⟨fun _ => i, ?_, ?_⟩
  · rw [hς]
    simpa [List.ofFn_succ, Fin.prod_univ_one] using hi
  · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, div_le_iff₀ hr0]
    push_cast
    nlinarith

private lemma roth_step [NumberField K] (n : ℕ) (ih : RothStatement K n) :
    RothStatement K (n + 1) := by
  intro P hP r hr hdeg ς₀ ε hε hratio hZ
  simp only [Nat.add_sub_cancel] at hratio hZ
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  set hPh := Finsupp.logHeight (AddMonoidAlgebra.coeff P) / Module.finrank ℚ K with hPh_def
  have hPh0 : 0 ≤ hPh := div_nonneg (zero_le_finsuppLogHeight _) hd.le
  set r' : Fin (n + 1 + 1) → ℕ+ := fun μ => ⟨r μ, hr μ⟩ with hr'_def
  -- the index of `P`, attained by `I₀`
  have hind : MvPolynomial.index r' ς₀ P ≤ ((n + 1 + 1 : ℕ) : ℝ≥0∞) :=
    MvPolynomial.index_le_of_degreeOf_le r' ς₀ hP hdeg
  obtain ⟨I₀, hI₀, hw⟩ := exists_eval_ne_zero_sum_eq_index r' ς₀
    (hind.trans_lt (ENNReal.natCast_lt_top _))
  refine ⟨⇑I₀, hI₀, ?_⟩
  set t := ∑ μ, (I₀ μ : ℝ) / r μ with ht_def
  have ht0 : 0 ≤ t := by positivity
  have htE : MvPolynomial.index r' ς₀ P = ENNReal.ofReal t := by
    rw [← hw, sum_div_eq_ofReal]
    rfl
  have htm : t ≤ n + 2 := by
    have := htE ▸ hind
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    push_cast at this
    linarith
  push_cast
  rcases le_or_gt (1 / 2) ε with hε2 | hε2
  · nlinarith
  -- Reduction (A): from now on `ε < 1 / 2`
  set N := 2 ^ (n + 1) with hN
  have hN2 : 2 ≤ N := by
    rw [hN, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hεN : ε ^ N ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le (by linarith) hN2
  have hεN0 : 0 < ε ^ N := by positivity
  have hεN1 : ε ^ N ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have hrpos : ∀ μ, (0 : ℝ) < r μ := fun μ => by exact_mod_cast hr μ
  have hratio' : ∀ μ : Fin (n + 1), (r μ.succ : ℝ) / r μ.castSucc ≤ ε ^ N := fun μ =>
    hratio μ.castSucc (by simp only [Fin.val_castSucc]; omega)
  have hanti : Antitone r := Fin.antitone_iff_succ_le.2 fun μ => by
    have h1 := hratio' μ
    rw [div_le_iff₀ (hrpos _)] at h1
    exact_mod_cast (show (r μ.succ : ℝ) ≤ r μ.castSucc by nlinarith [hrpos μ.castSucc])
  -- the decomposition `P = ∑ φⱼ ψⱼ` and the Wronskians `U`, `V`
  obtain ⟨s, φ, ψ, hs, hφ, hψ, hφdeg, hψdeg, hPeq⟩ :=
    exists_sum_rename_mul_aeval_eq (n := n + 1) (by omega) r hP hdeg
  obtain ⟨I', hI'sum, hU⟩ := exists_generalizedWronskian_ne_zero hφ
  set ψ' : Fin (s + 1) → MvPolynomial (Fin 1) K :=
    fun j => Polynomial.aeval (X 0 : MvPolynomial (Fin 1) K) (ψ j) with hψ'_def
  have hψ' : LinearIndependent K ψ' :=
    hψ.map' (Polynomial.aeval (R := K) (X 0 : MvPolynomial (Fin 1) K)).toLinearMap
      (LinearMap.ker_eq_bot.2 aeval_X_zero_injective)
  have hV := (generalizedWronskian_ne_zero_iff_linearIndependent ψ').2 hψ'
  have hI : ∀ μ, ∑ k, I' μ k ≤ s := fun μ => (hI'sum μ).trans (Nat.lt_succ_iff.1 μ.isLt)
  have hheights := logHeight_generalizedWronskian_add_le (n := n + 1) (by omega) hε
    (by linarith) r hr hratio' hP hdeg hs φ ψ hPeq I' hI hU hV
  set U := generalizedWronskian I' φ with hU_def
  set V := generalizedWronskian (fun ν _ => (ν : ℕ)) ψ' with hV_def
  set hU' := Finsupp.logHeight (AddMonoidAlgebra.coeff U) / Module.finrank ℚ K with hU'_def
  set hV' := Finsupp.logHeight (AddMonoidAlgebra.coeff V) / Module.finrank ℚ K with hV'_def
  have hU0 : 0 ≤ hU' := div_nonneg (zero_le_finsuppLogHeight _) hd.le
  have hV0 : 0 ≤ hV' := div_nonneg (zero_le_finsuppLogHeight _) hd.le
  have hW : rothWronskian I' P =
      rename Fin.castSucc U * rename (fun _ => Fin.last (n + 1)) V := by
    have hPeq' : P = ∑ j, rename Fin.castSucc (φ j) *
        rename (fun _ => Fin.last (n + 1)) (ψ' j) := by
      rw [hPeq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hψ'_def, ← Polynomial.aeval_algHom_apply, rename_X]
    rw [hPeq']
    exact rothWronskian_sum_mul_eq I' φ ψ'
  set r0 : ℝ := ((r 0 : ℕ) : ℝ) with hr0_def
  set rl : ℝ := ((r (Fin.last (n + 1)) : ℕ) : ℝ) with hrl_def
  set rn : ℝ := ((r (Fin.last n).castSucc : ℕ) : ℝ) with hrn_def
  have hr0pos : 0 < r0 := hrpos 0
  have hrlpos : 0 < rl := hrpos _
  have hrnpos : 0 < rn := hrpos _
  have hrl_le : rl ≤ r0 := by
    rw [hrl_def, hr0_def]; exact_mod_cast hanti (Fin.zero_le _)
  -- (a) the induction hypothesis for `U`
  have hratioU : ∀ (μ : Fin (n + 1)) (hμ : μ.val + 1 < n + 1),
      (((fun μ : Fin (n + 1) => (s + 1) * r μ.castSucc) ⟨μ.val + 1, hμ⟩ : ℕ) : ℝ) /
        (((fun μ : Fin (n + 1) => (s + 1) * r μ.castSucc) μ : ℕ) : ℝ) ≤
        (ε ^ 2) ^ (2 ^ (n + 1 - 1)) := by
    intro μ hμ
    have h1 := hratio μ.castSucc (by simp; omega)
    rw [Nat.add_sub_cancel, ← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by ring]
    push_cast
    rw [mul_div_mul_left _ _ (by positivity)]
    exact h1
  have hZU : ∀ μ : Fin (n + 1), ((ε ^ 2) ^ (2 ^ (n + 1 - 1)))⁻¹ *
      (Finsupp.logHeight (AddMonoidAlgebra.coeff U) / Module.finrank ℚ K +
        2 * ((n + 1 : ℕ) : ℝ) *
          (((fun μ : Fin (n + 1) => (s + 1) * r μ.castSucc) 0 : ℕ) : ℝ)) ≤
      (((fun μ : Fin (n + 1) => (s + 1) * r μ.castSucc) μ : ℕ) : ℝ) *
        (Height.logHeight₁ ((ς₀ ∘ Fin.castSucc) μ) / Module.finrank ℚ K) := by
    intro μ
    have h1 := hZ μ.castSucc
    rw [Nat.add_sub_cancel, ← pow_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by ring]
    simp only [Fin.castSucc_zero, Function.comp_apply]
    push_cast
    push_cast at h1
    have hUle : hU' ≤ (s + 1) * (hPh + 2 * r0) := by linarith
    have hεinv : 0 ≤ (ε ^ N)⁻¹ := by positivity
    calc (ε ^ N)⁻¹ * (hU' + 2 * (n + 1) * ((s + 1) * r0))
        ≤ (ε ^ N)⁻¹ * ((s + 1) * (hPh + 2 * (n + 1 + 1) * r0)) := by
          gcongr
          nlinarith
      _ = (s + 1) * ((ε ^ N)⁻¹ * (hPh + 2 * (n + 1 + 1) * r0)) := by ring
      _ ≤ (s + 1) * (r μ.castSucc * (Height.logHeight₁ (ς₀ μ.castSucc) /
            Module.finrank ℚ K)) := by gcongr
      _ = _ := by ring
  obtain ⟨IU, hIU, hIUw⟩ := ih U hU (fun μ => (s + 1) * r μ.castSucc)
    (fun μ => Nat.mul_pos (Nat.succ_pos s) (hr _))
    (fun μ => degreeOf_generalizedWronskian_le I' φ μ (fun j => hφdeg j μ))
    (ς₀ ∘ Fin.castSucc) (ε := ε ^ 2) (by positivity) hratioU hZU
  -- (b) the one-variable lemma for `V`
  have hVdeg : V.degreeOf 0 ≤ (s + 1) * r (Fin.last (n + 1)) :=
    degreeOf_generalizedWronskian_le _ ψ' 0
      (fun j => (degreeOf_aeval_X_le (ψ j)).trans (hψdeg j))
  have hZV : (ε ^ N)⁻¹ * (Finsupp.logHeight (AddMonoidAlgebra.coeff V) / Module.finrank ℚ K +
      (((s + 1) * r (Fin.last (n + 1)) : ℕ) : ℝ)) ≤
      (((s + 1) * r (Fin.last (n + 1)) : ℕ) : ℝ) *
        (Height.logHeight₁ (ς₀ (Fin.last (n + 1))) / Module.finrank ℚ K) := by
    have h1 := hZ (Fin.last (n + 1))
    push_cast
    push_cast at h1
    have hVle : hV' ≤ (s + 1) * (hPh + 2 * r0) := by linarith
    have hεinv : 0 ≤ (ε ^ N)⁻¹ := by positivity
    calc (ε ^ N)⁻¹ * (hV' + (s + 1) * rl)
        ≤ (ε ^ N)⁻¹ * ((s + 1) * (hPh + 2 * (n + 1 + 1) * r0)) := by
          gcongr
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith [mul_le_mul_of_nonneg_left hrl_le (by positivity : (0 : ℝ) ≤ s + 1),
            mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ s + 1) this) hr0pos.le]
      _ = (s + 1) * ((ε ^ N)⁻¹ * (hPh + 2 * (n + 1 + 1) * r0)) := by ring
      _ ≤ (s + 1) * (rl * (Height.logHeight₁ (ς₀ (Fin.last (n + 1))) /
            Module.finrank ℚ K)) := by gcongr
      _ = _ := by ring
  obtain ⟨iV, hiV, hiVε⟩ := exists_dividedDeriv_ne_zero_one_var hV hVdeg
    (ς₀ (Fin.last (n + 1))) hεN0 hZV
  -- upper bound for the index of `W`
  have hupper : MvPolynomial.index r' ς₀ (rothWronskian I' P) ≤
      ENNReal.ofReal (∑ μ : Fin (n + 1), (IU μ : ℝ) / r μ.castSucc + iV / rl) := by
    rw [hW, MvPolynomial.index_mul]
    have h1 := index_le_of_eval_ne_zero r' ς₀ (Q := rename Fin.castSucc U)
      (Fin.snoc (α := fun _ => ℕ) IU 0) (by
        rw [dividedDeriv_snoc_zero_rename_castSucc, eval_rename]
        exact hIU)
    have h2 := index_le_of_eval_ne_zero r' ς₀ (Q := rename (fun _ => Fin.last (n + 1)) V)
      (Fin.snoc (α := fun _ => ℕ) (0 : Fin (n + 1) → ℕ) iV) (by
        rw [dividedDeriv_snoc_rename_last, eval_rename]
        exact hiV)
    rw [sum_div_eq_ofReal] at h1 h2
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    refine (add_le_add h1 h2).trans_eq ?_
    congr 2
    · rw [Fin.sum_univ_castSucc]
      simp [r']
    · rw [Fin.sum_univ_castSucc]
      simp [r', rl]
  -- lower bound for the index of the entries `∂_{(I'_μ, ν)} P`
  set δ := rl / rn with hδ_def
  have hδ0 : 0 ≤ δ := by positivity
  have hentry : ∀ μ ν : Fin (s + 1), ENNReal.ofReal (t - (ν : ℕ) / rl - δ) ≤
      MvPolynomial.index r' ς₀
        ((∏ k, (((Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ)) k).factorial : K))⁻¹ •
          (List.ofFn fun k => (pderiv k).toLinearMap ^
            (Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ)) k :
            List (Module.End K (MvPolynomial (Fin (n + 1 + 1)) K))).prod P) := by
    intro μ ν
    have h := index_le_index_dividedDeriv_add r' ς₀ P (Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ))
    rw [htE, sum_div_eq_ofReal] at h
    have hw : ∑ k, ((Fin.snoc (α := fun _ => ℕ) (I' μ) (ν : ℕ) k : ℕ) : ℝ) /
        ((r' k : ℕ) : ℝ) ≤ δ + (ν : ℕ) / rl := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      refine add_le_add ?_ le_rfl
      have hrn_le : ∀ k : Fin (n + 1), rn ≤ r k.castSucc := fun k => by
        rw [hrn_def]
        exact_mod_cast hanti (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last k))
      calc ∑ k : Fin (n + 1), (I' μ k : ℝ) / ((r' k.castSucc : ℕ) : ℝ)
          ≤ ∑ k : Fin (n + 1), (I' μ k : ℝ) / rn :=
            Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_left (by positivity) hrnpos
              (hrn_le k)
        _ = ((∑ k, I' μ k : ℕ) : ℝ) / rn := by rw [← Finset.sum_div]; push_cast; rfl
        _ ≤ δ := by
          rw [hδ_def]
          gcongr
          rw [hrl_def]
          exact_mod_cast (hI μ).trans hs
    calc ENNReal.ofReal (t - (ν : ℕ) / rl - δ) = ENNReal.ofReal (t - (δ + (ν : ℕ) / rl)) := by
          ring_nf
      _ = ENNReal.ofReal t - ENNReal.ofReal (δ + (ν : ℕ) / rl) :=
          ENNReal.ofReal_sub _ (by positivity)
      _ ≤ _ := by
        rw [tsub_le_iff_right]
        exact h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hw))
  -- lower bound for the index of `W`, from the expansion of the determinant
  have hlower : ENNReal.ofReal ((s + 1) * (min (t / 2) (t ^ 2 / 2) - δ)) ≤
      MvPolynomial.index r' ς₀ (rothWronskian I' P) := by
    have hsum : ((s : ℝ) + 1) * (min (t / 2) (t ^ 2 / 2) - δ) ≤
        ∑ ν : Fin (s + 1), max (t - (ν : ℕ) / rl - δ) 0 := by
      have h0 := mul_min_le_sum_range_max_sub_div (r := r (Fin.last (n + 1)))
        (hr _) hs ht0
      rw [← Fin.sum_univ_eq_sum_range] at h0
      exact mul_sub_le_sum_max_sub hδ0 h0
    refine (ENNReal.ofReal_le_ofReal hsum).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => le_max_right _ _)]
    refine MvPolynomial.le_index_det r' ς₀ _ _ fun μ ν => ?_
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_le (hentry μ ν) zero_le
  -- comparison
  have hA : ∑ μ : Fin (n + 1), (IU μ : ℝ) / r μ.castSucc + iV / rl ≤
      (s + 1) * (2 * (n + 1) * ε ^ 2 + ε ^ N) := by
    have e1 : ∑ μ : Fin (n + 1), (IU μ : ℝ) / r μ.castSucc =
        (s + 1) * ∑ μ, (IU μ : ℝ) / (((s + 1) * r μ.castSucc : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have := hrpos μ.castSucc
      push_cast
      field_simp
    have e2 : (iV : ℝ) / rl ≤ (s + 1) * ε ^ N := by
      rw [div_le_iff₀ hrlpos]
      push_cast at hiVε
      linarith
    have h3 := mul_le_mul_of_nonneg_left hIUw (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1)
    rw [e1]
    push_cast at h3 ⊢
    linarith
  have hfinal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
    (hlower.trans (hupper.trans (ENNReal.ofReal_le_ofReal hA)))
  have hδ : δ ≤ ε ^ N := hratio (Fin.last n).castSucc (by simp)
  have hmin : min (t / 2) (t ^ 2 / 2) ≤ 2 * (n + 1 + 1) * ε ^ 2 := by
    have := le_of_mul_le_mul_left hfinal (by positivity)
    linarith
  exact le_two_mul_of_min_le ht0 (by linarith) (by linarith) hε.le hmin

end Main

/-- **Roth's lemma.** Let `P ∈ K[ς₁, …, ςₘ]` be a nonzero polynomial over a number field `K`
with `deg_{ς_μ} P ≤ r_μ`, `r_μ > 0`, and let `ς⁰ ∈ Kᵐ`. If `ε > 0`,
`r_{μ+1} / r_μ ≤ ε^{2^{m-1}}` for all `μ`, and
`r_μ h(ς⁰_μ) ≥ ε^{-2^{m-1}} (h(P) + 2 m r₁)` for all `μ`, then there is a multi-index `I`
with `∂_I P(ς⁰) ≠ 0` and `∑_μ i_μ / r_μ ≤ 2 m ε`. Heights are absolute logarithmic heights:
`h(x) = Height.logHeight₁ x / [K : ℚ]`, and `h(P)` is `Finsupp.logHeight` of the coefficients
of `P` divided by `[K : ℚ]`. -/
@[faltings "thm_bvr_roth_lemma"]
public theorem exists_eval_dividedDeriv_ne_zero_of_roth {K : Type*} [Field K] [NumberField K]
    {m : ℕ} [NeZero m] (P : MvPolynomial (Fin m) K) (hP : P ≠ 0) (r : Fin m → ℕ)
    (hr : ∀ μ, 0 < r μ) (hdeg : ∀ μ, P.degreeOf μ ≤ r μ) (ς₀ : Fin m → K) {ε : ℝ}
    (hε : 0 < ε)
    (hratio : ∀ (μ : Fin m) (hμ : μ.val + 1 < m),
      (r ⟨μ.val + 1, hμ⟩ : ℝ) / r μ ≤ ε ^ (2 ^ (m - 1)))
    (hZ : ∀ μ, (ε ^ (2 ^ (m - 1)))⁻¹ *
        (Finsupp.logHeight (AddMonoidAlgebra.coeff P) / Module.finrank ℚ K + 2 * m * r 0) ≤
      r μ * (Height.logHeight₁ (ς₀ μ) / Module.finrank ℚ K)) :
    ∃ I : Fin m → ℕ,
      eval ς₀ ((∏ μ, ((I μ).factorial : K))⁻¹ •
          (List.ofFn fun μ => (pderiv μ).toLinearMap ^ I μ : List (Module.End K _)).prod P) ≠ 0 ∧
        ∑ μ, (I μ : ℝ) / r μ ≤ 2 * m * ε := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne m)).symm⟩
  have key : ∀ n, RothStatement K n := fun n => by
    induction n with
    | zero => exact roth_base
    | succ n ih => exact roth_step n ih
  exact key n P hP r hr hdeg ς₀ hε hratio hZ

end Faltings
