module
public import Mathlib
public import Mordell.Attr

/-!
# Splitting off the last variable of a polynomial

Let `P ≠ 0` be a polynomial in the variables `X 0, …, X n` over a number field `K`, of degree at
most `r i` in `X i`. Then `P = ∑_{j ≤ s} φ_j(X 0, …, X (n-1)) · ψ_j(X n)` with `s ≤ r n`, where the
`φ_j` are `K`-linearly independent polynomials in the first `n` variables with the same partial
degree bounds, and the `ψ_j` are `K`-linearly independent one-variable polynomials of degree at
most `r n`. This is the decomposition used to factor the Wronskian in Roth's lemma.

## Main results

* `Faltings.exists_sum_rename_mul_aeval_eq`: the decomposition.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][Bombieri1990], Sec. 8.
-/

namespace Faltings

open MvPolynomial

/-- A nonzero finite family of vectors has a linearly independent subfamily, indexed by some
`Fin (s + 1)` with `s + 1` at most the size of the family, spanning every member of the family. -/
private theorem exists_fin_linearIndependent_comp {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (v : Fin (N + 1) → V) (hv : v ≠ 0) :
    ∃ (s : ℕ) (σ : Fin (s + 1) → Fin (N + 1)), s ≤ N ∧ LinearIndependent K (v ∘ σ) ∧
      ∀ e, ∃ c : Fin (s + 1) → K, ∑ j, c j • v (σ j) = v e := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hne : Fintype.card κ ≠ 0 := by
    intro h0
    have : IsEmpty κ := Fintype.card_eq_zero_iff.mp h0
    apply hv
    funext e
    have : v e ∈ Submodule.span K (Set.range (v ∘ a)) := hspan ▸ Submodule.subset_span ⟨e, rfl⟩
    rwa [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hne
  let f : κ ≃ Fin (s + 1) := (Fintype.equivFin κ).trans (finCongr hs)
  refine ⟨s, a ∘ f.symm, ?_, hli.comp f.symm f.symm.injective, fun e => ?_⟩
  · have := Fintype.card_le_of_injective a ha
    simp only [Fintype.card_fin] at this
    omega
  · have : v e ∈ Submodule.span K (Set.range ((v ∘ a) ∘ f.symm)) := by
      rw [EquivLike.range_comp, hspan]
      exact Submodule.subset_span ⟨e, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun K).mp this

/-- `finSuccEquiv` sends a polynomial in `X 1, …, X n` (renamed along `Fin.succ`) to a constant. -/
private theorem finSuccEquiv_rename_succ {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) : finSuccEquiv R n (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, finSuccEquiv_X_succ]

/-- A polynomial in `X 0, …, X n` is `∑_{e ≤ d} P_e(X 0, …, X (n-1)) · (X n) ^ e`, where `d` is its
degree in `X n` and each `P_e` has degree in `X i` at most that of the polynomial. -/
private theorem exists_eq_sum_rename_mul_X_last_pow {R : Type*} [CommSemiring R] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) :
    ∃ v : Fin (P.degreeOf (Fin.last n) + 1) → MvPolynomial (Fin n) R,
      (∀ e i, (v e).degreeOf i ≤ P.degreeOf i.castSucc) ∧
      P = ∑ e, rename Fin.castSucc (v e) * X (Fin.last n) ^ (e : ℕ) := by
  have hrot : ∀ i : Fin n, finRotate (n + 1) i.castSucc = i.succ := fun i => by
    simp [Fin.coeSucc_eq_succ]
  set P' := rename (finRotate (n + 1)) P with hP'
  set Q := finSuccEquiv R n P' with hQ
  have hdeg : Q.natDegree = P.degreeOf (Fin.last n) := by
    rw [hQ, natDegree_finSuccEquiv, hP', ← finRotate_last,
      degreeOf_rename_of_injective (finRotate (n + 1)).injective]
  refine ⟨fun e => Q.coeff e, fun e i => ?_, ?_⟩
  · refine (degreeOf_coeff_finSuccEquiv P' i e).trans (le_of_eq ?_)
    rw [hP', ← hrot, degreeOf_rename_of_injective (finRotate (n + 1)).injective]
  · have hP'sum : P' = ∑ e : Fin (P.degreeOf (Fin.last n) + 1),
        rename Fin.succ (Q.coeff e) * X 0 ^ (e : ℕ) := by
      apply (finSuccEquiv R n).injective
      rw [← hQ]
      simp only [map_sum, map_mul, map_pow, finSuccEquiv_rename_succ, finSuccEquiv_X_zero,
        Polynomial.C_mul_X_pow_eq_monomial]
      rw [Fin.sum_univ_eq_sum_range (fun e => Polynomial.monomial e (Q.coeff e))
        (P.degreeOf (Fin.last n) + 1)]
      exact Polynomial.as_sum_range' Q _ (by omega)
    have hP : P = rename (finRotate (n + 1)).symm P' := by
      rw [hP', rename_rename]; simp
    refine hP.trans ?_
    rw [hP'sum, map_sum]
    have h1 : ⇑(finRotate (n + 1)).symm ∘ Fin.succ = Fin.castSucc := by
      funext i
      exact (Equiv.symm_apply_eq _).mpr (hrot i).symm
    have h2 : (finRotate (n + 1)).symm 0 = Fin.last n := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    simp only [map_mul, map_pow, rename_X, rename_rename, h1, h2]

/-- If `w` is linearly independent and `∑ j, c j • w j = w k`, then `c` is the `k`-th unit
vector. -/
private theorem eq_single_of_sum_smul_eq {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] {w : ι → V} (hw : LinearIndependent K w) {c : ι → K} {k : ι}
    (hc : ∑ j, c j • w j = w k) (j : ι) : c j = if j = k then 1 else 0 := by
  refine sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hw (fun j => c j - if j = k then 1 else 0)
    ?_ j)
  simp [sub_smul, Finset.sum_sub_distrib, ite_smul, hc]

/-- A nonzero polynomial `P` in `n + 1` variables over a number field `K`, of degree at most `r i`
in `X i`, is `∑_{j ≤ s} φ_j · ψ_j(X n)` with `s ≤ r n`, where the `φ_j` are linearly independent
polynomials in the first `n` variables of degree at most `r i` in `X i`, and the `ψ_j` are linearly
independent one-variable polynomials of degree at most `r n`. -/
@[faltings "lem_bvr_roth_decomposition"]
public theorem exists_sum_rename_mul_aeval_eq {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (hn : 1 ≤ n) (r : Fin (n + 1) → ℕ) {P : MvPolynomial (Fin (n + 1)) K} (hP : P ≠ 0)
    (hP_deg : ∀ i, P.degreeOf i ≤ r i) :
    ∃ (s : ℕ) (φ : Fin (s + 1) → MvPolynomial (Fin n) K) (ψ : Fin (s + 1) → Polynomial K),
      s ≤ r (Fin.last n) ∧ LinearIndependent K φ ∧ LinearIndependent K ψ ∧
      (∀ j i, (φ j).degreeOf i ≤ r i.castSucc) ∧
      (∀ j, (ψ j).natDegree ≤ r (Fin.last n)) ∧
      P = ∑ j, rename Fin.castSucc (φ j) * Polynomial.aeval (X (Fin.last n)) (ψ j) := by
  obtain ⟨v, hv_deg, hPv⟩ := exists_eq_sum_rename_mul_X_last_pow P
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hP (hPv.trans (by simp))
  obtain ⟨s, σ, hs, hli, hc⟩ := exists_fin_linearIndependent_comp (K := K) v hv0
  choose a ha using hc
  have hδ : ∀ k j, a (σ k) j = if j = k then 1 else 0 := fun k =>
    eq_single_of_sum_smul_eq hli (ha (σ k))
  refine ⟨s, v ∘ σ, fun j => ∑ e : Fin _, Polynomial.monomial (e : ℕ) (a e j), hs.trans (hP_deg _),
    hli, Fintype.linearIndependent_iff.mpr fun g hg k => ?_,
    fun j i => (hv_deg _ _).trans (hP_deg _), fun j => ?_, ?_⟩
  · simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj, hδ] using
      congrArg (Polynomial.coeff · (σ k : ℕ)) hg
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e _ =>
      (Polynomial.natDegree_monomial_le _).trans ((Fin.is_le e).trans (hP_deg _))
  · refine hPv.trans ?_
    calc _ = ∑ e, ∑ j, a e j • (rename Fin.castSucc (v (σ j)) * X (Fin.last n) ^ (e : ℕ)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← ha e, map_sum, Finset.sum_mul]
          simp
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [map_sum, Polynomial.aeval_monomial, Finset.mul_sum, Algebra.smul_def]
          exact Finset.sum_congr rfl fun e _ => mul_left_comm _ _ _

end Faltings
