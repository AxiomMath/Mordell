module
public import Mordell.Polynomial.PowerSeries.BranchIdentity
public import Mordell.Polynomial.SimpleRoot

/-!
# The local Eisenstein bound at a non-archimedean place

Let `K` be a field of characteristic `0`, `p ∈ K[X, Y]` with `e = deg_X p ≥ 1`, and let
`D_p(Y) = Res_X(p, ∂p/∂X) ∈ K[Y]` be its discriminant with respect to `X` (Sylvester resultant
with formal degrees `e` and `e - 1`). Let `ξ ∈ K⟦ς⟧` with `p(ξ(ς), ς) = 0` and `D_p(0) ≠ 0`, and
let `|·|_v` be a non-archimedean absolute value on `K` with `|ξ(0)|_v ≤ 1`. Writing `|p|_v` for the
maximum of `|c|_v` over the coefficients `c` of `p`, for every `l ≥ 1`
`|∂_l ξ(0)|_v ≤ (|p|_v / |p_X(ξ(0), 0)|_v) ^ (2l - 1)`.
This is the finite-place half of Eisenstein's theorem in the form of Bombieri's Lemma 5.

## Main results

* `Faltings.PowerSeries.abv_constantCoeff_dividedDerivative_le`: the bound above.
* `Faltings.finSuccEquiv_pderiv_zero`: `MvPolynomial.finSuccEquiv` turns `∂/∂X₀` into the
  derivative in the outer variable.
* `Faltings.PowerSeries.eval_pderiv_zero_ne_zero`: if `D_p(0) ≠ 0`, every root `x` of `p(X, 0)`
  has `p_X(x, 0) ≠ 0`.

## Implementation notes

The polynomial `p` is an `MvPolynomial (Fin 2) K` with `X = X 0`, `Y = X 1`; `p(ξ, ς)` is
`MvPolynomial.aeval ![ξ, PowerSeries.X] p` and `p_X` is `MvPolynomial.pderiv 0 p`. The discriminant
is computed on `MvPolynomial.finSuccEquiv K 1 p`, the polynomial `p` viewed in `X` over
`K[Y] = MvPolynomial (Fin 1) K`, as `Polynomial.resultant` of it and its derivative with formal
degrees `e = MvPolynomial.degreeOf 0 p` and `e - 1`; `D_p(0)` is its evaluation at `0`.

The source states the bound at a finite place `v` of a number field, with Bombieri's normalised
`|·|_v`. Both sides are homogeneous of degree one in `|·|_v` (the right side is a power of a
ratio), so replacing `|·|_v` by a positive real power of it does not change the inequality, and
the bound holds for every non-archimedean absolute value on a field of characteristic `0`; this is
the form stated. The finite places of a number field, with Mathlib's or Bombieri's normalisation,
are instances.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 5
-/

namespace Faltings.PowerSeries

open _root_.PowerSeries Finset

/-- The partial derivative in the first variable corresponds to the derivative in the outer
variable under `MvPolynomial.finSuccEquiv`. -/
public theorem _root_.Faltings.finSuccEquiv_pderiv_zero {R : Type*} [CommRing R] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.pderiv 0 f) =
      Polynomial.derivative (MvPolynomial.finSuccEquiv R n f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.pderiv_C, map_zero, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
      Polynomial.algebraMap_apply, Polynomial.derivative_C]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul,
      Polynomial.derivative_mul, hf]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero, mul_comm, add_comm]
    · simp [MvPolynomial.finSuccEquiv_X_succ, mul_comm]

/-- The identification `K[Y] = MvPolynomial (Fin 1) K → K[X]`. -/
private noncomputable abbrev toPoly (K : Type*) [CommRing K] :
    MvPolynomial (Fin 1) K →ₐ[K] Polynomial K :=
  (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toAlgHom

private lemma toPoly_injective (K : Type*) [CommRing K] : Function.Injective (toPoly K) :=
  (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective

private lemma evalRingHom_comp_toPoly (K : Type*) [CommRing K] :
    (Polynomial.evalRingHom 0).comp (toPoly K).toRingHom = MvPolynomial.eval 0 := by
  ext <;> simp

private lemma evalEval_map_toPoly {K : Type*} [CommRing K] (x : MvPolynomial (Fin 2) K) (a : K) :
    ((MvPolynomial.finSuccEquiv K 1 x).map (toPoly K).toRingHom).evalEval 0 a =
      MvPolynomial.eval ![a, 0] x := by
  rw [← Polynomial.map_evalRingHom_eval, Polynomial.map_map, evalRingHom_comp_toPoly]
  have : (![a, 0] : Fin 2 → K) = Fin.cons a (0 : Fin 1 → K) := by
    ext i
    fin_cases i <;> rfl
  rw [this, MvPolynomial.eval_eq_eval_mv_eval']

/-- If the natural numbers `f i` (`i ∈ s`) are all `< l` and sum to at most `l`, then
`∑ (2 f i - 1) ≤ 2 l - 2` (truncated subtraction). -/
private lemma sum_two_mul_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) {l : ℕ}
    (hsum : ∑ i ∈ s, f i ≤ l) (hlt : ∀ i ∈ s, f i < l) :
    ∑ i ∈ s, (2 * f i - 1) ≤ 2 * l - 2 := by
  have key : ∑ i ∈ s, (2 * f i - 1) + #{i ∈ s | f i ≠ 0} = 2 * ∑ i ∈ s, f i := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h <;> omega
  have hfilt : ∑ i ∈ s, f i = ∑ i ∈ s with f i ≠ 0, f i := (Finset.sum_filter_ne_zero s).symm
  rcases Nat.lt_or_ge #{i ∈ s | f i ≠ 0} 2 with hN | hN
  · rcases Nat.lt_succ_iff.mp hN |>.lt_or_eq with hN | hN
    · have h0 : #{i ∈ s | f i ≠ 0} = 0 := by omega
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hfilt
      omega
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hN
      have hjs : j ∈ s := (Finset.mem_filter.mp (hj ▸ Finset.mem_singleton_self j)).1
      rw [hj, Finset.sum_singleton] at hfilt
      have := hlt j hjs
      omega
  · omega

/-- `p_X(a, 0)` as a sum over the support of `p`: only monomials free of `Y` contribute. -/
private theorem eval_pderiv_zero_eq_sum {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K)
    (a : K) :
    MvPolynomial.eval ![a, 0] (MvPolynomial.pderiv 0 p) =
      ∑ m ∈ p.support,
        p.coeff m * (if m 1 = 0 then (m 0 : K) * a ^ (m 0 - 1) else 0) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  refine sum_congr rfl fun m _ => ?_
  split_ifs with h <;> simp [h, mul_assoc]

/-- The constant term of a power-series root `ξ` of `p(X, Y)` is a root of `p(X, 0)`. -/
private lemma eval_constantCoeff_eq_zero {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K)
    (ξ : K⟦X⟧) (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0) :
    MvPolynomial.eval ![constantCoeff ξ, 0] p = 0 := by
  have h := congrArg (constantCoeff (R := K)) hp
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.hom_eval₂] at h
  refine Eq.trans ?_ h
  change MvPolynomial.eval₂ (RingHom.id K) _ p = _
  congr 1
  funext i
  fin_cases i <;> simp

/-- If `D_p(0) ≠ 0`, then every root `x` of `p(X, 0)` is simple: `p_X(x, 0) ≠ 0`. -/
public theorem eval_pderiv_zero_ne_zero {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K)
    (hdeg : 1 ≤ p.degreeOf 0) {x : K} (hx : MvPolynomial.eval ![x, 0] p = 0)
    (hD : MvPolynomial.eval 0
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K 1 p)
        (Polynomial.derivative (MvPolynomial.finSuccEquiv K 1 p))
        (p.degreeOf 0) (p.degreeOf 0 - 1)) ≠ 0) :
    MvPolynomial.eval ![x, 0] (MvPolynomial.pderiv 0 p) ≠ 0 := by
  set q := (MvPolynomial.finSuccEquiv K 1 p).map (toPoly K).toRingHom with hq
  have hqdeg : q.natDegree = p.degreeOf 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective (toPoly_injective K),
      MvPolynomial.natDegree_finSuccEquiv]
  have := Faltings.evalEval_derivative_ne_zero_of_eval_resultant_ne_zero (p := q) (by omega)
    (by rwa [hq, evalEval_map_toPoly]) ?_
  · rwa [hq, Polynomial.derivative_map, ← finSuccEquiv_pderiv_zero, evalEval_map_toPoly] at this
  · rwa [hqdeg, hq, Polynomial.derivative_map, Polynomial.resultant_map_map,
      ← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, evalRingHom_comp_toPoly]

/-- For a non-archimedean `v` and `|x|_v ≤ 1`, `|p_X(x, 0)|_v` is bounded by any bound `B` of the
coefficients of `p`. -/
private lemma abv_eval_pderiv_zero_le {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K)
    {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) {x : K} (hx : v x ≤ 1) {B : ℝ}
    (hB : 0 ≤ B) (hcoef : ∀ m ∈ p.support, v (p.coeff m) ≤ B) :
    v (MvPolynomial.eval ![x, 0] (MvPolynomial.pderiv 0 p)) ≤ B := by
  rw [eval_pderiv_zero_eq_sum]
  refine hv.apply_sum_le.trans (Real.iSup_le (Subtype.forall.2 fun m hm => ?_) hB)
  rw [map_mul]
  refine (mul_le_mul (hcoef m hm) ?_ (v.nonneg _) hB).trans (mul_one B).le
  split_ifs
  · rw [map_mul, map_pow]
    exact (mul_le_mul (IsNonarchimedean.apply_natCast_le_one (by simp) (by simp) hv)
      (pow_le_one₀ (v.nonneg _) hx) (by positivity) zero_le_one).trans_eq (one_mul 1)
  · simp

/-- The recursion behind Eisenstein's bound: if `a = p_X(ξ(0), 0)` and every coefficient of `p`
has `|·|_v ≤ R |a|_v` with `R ≥ 1`, then `|∂_n ξ(0)|_v ≤ R ^ (2n - 1)` for every `n`. It is
proved by strong induction on `n` from the coefficient identity
`constantCoeff_dividedDerivative_branch_identity`. -/
private lemma abv_constantCoeff_dividedDerivative_le_pow {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 2) K) (ξ : K⟦X⟧) (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0)
    {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (hξ : v (constantCoeff ξ) ≤ 1)
    (ha : MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p) ≠ 0)
    {R : ℝ} (hR : 1 ≤ R) (hcoef : ∀ m ∈ p.support, v (p.coeff m) ≤
      R * v (MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p))) (n : ℕ) :
    v (constantCoeff (dividedDerivative K n ξ)) ≤ R ^ (2 * n - 1) := by
  set a := MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p)
  have hva : 0 < v a := v.pos ha
  have hP0 : 0 ≤ R * v a := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [constantCoeff_dividedDerivative] using hξ
  have hid := constantCoeff_dividedDerivative_branch_identity p ξ hp hn
  have hmain : v a * v (constantCoeff (dividedDerivative K n ξ)) ≤
      R * v a * R ^ (2 * n - 2) := by
    rw [← map_mul, eq_neg_of_add_eq_zero_left hid.symm, AbsoluteValue.map_neg]
    refine hv.apply_sum_le.trans (Real.iSup_le (Subtype.forall.2 fun m hm => ?_) (by positivity))
    dsimp only
    rw [map_mul]
    refine mul_le_mul (hcoef m hm) ?_ (v.nonneg _) hP0
    refine hv.apply_sum_le.trans (Real.iSup_le (Subtype.forall.2 fun t ht => ?_) (by positivity))
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at ht
    rw [map_mul, map_prod]
    have h1 : v (constantCoeff (dividedDerivative K (t 0) ((X : K⟦X⟧) ^ m 1))) ≤ 1 := by
      rw [constantCoeff_dividedDerivative, coeff_X_pow]
      split_ifs <;> simp
    calc _ ≤ 1 * ∏ k : Fin (m 0), R ^ (2 * t k.succ - 1) :=
          mul_le_mul h1 (Finset.prod_le_prod₀ (fun _ _ => v.nonneg _)
            fun k _ => ih _ (ht.2 k)) (Finset.prod_nonneg fun _ _ => v.nonneg _) zero_le_one
      _ = R ^ (∑ k : Fin (m 0), (2 * t k.succ - 1)) := by
          rw [one_mul, Finset.prod_pow_eq_pow_sum]
      _ ≤ R ^ (2 * n - 2) := pow_le_pow_right₀ hR
          (sum_two_mul_sub_one_le _ _ (by omega) fun k _ => ht.2 k)
  refine le_of_mul_le_mul_left (hmain.trans_eq ?_) hva
  rw [show 2 * n - 1 = 2 * n - 2 + 1 by omega, pow_succ]
  ring

/-- **Local Eisenstein bound at a non-archimedean place.** Let `K` be a field of characteristic
`0`, `p ∈ K[X, Y]` with `deg_X p ≥ 1` whose discriminant `D_p = Res_X(p, p_X)` does not vanish at
`Y = 0`, and `ξ ∈ K⟦ς⟧` with `p(ξ, ς) = 0`. If `|·|_v` is a non-archimedean absolute value on `K`
with `|ξ(0)|_v ≤ 1`, then `|∂_l ξ(0)|_v ≤ (|p|_v / |p_X(ξ(0), 0)|_v) ^ (2l - 1)` for every `l ≥ 1`,
where `|p|_v` is the maximum of `|·|_v` on the coefficients of `p`. -/
@[faltings "lem_bvs_eisenstein_finite"]
public theorem abv_constantCoeff_dividedDerivative_le {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 2) K) (hdeg : 1 ≤ p.degreeOf 0) (ξ : K⟦X⟧)
    (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0)
    (hD : MvPolynomial.eval 0
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K 1 p)
        (Polynomial.derivative (MvPolynomial.finSuccEquiv K 1 p))
        (p.degreeOf 0) (p.degreeOf 0 - 1)) ≠ 0)
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (hξ : v (constantCoeff ξ) ≤ 1)
    {l : ℕ} (hl : 1 ≤ l) :
    v (constantCoeff (dividedDerivative K l ξ)) ≤
      ((⨆ m : p.support, v (p.coeff m)) /
        v (MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p))) ^ (2 * l - 1) := by
  have ha := eval_pderiv_zero_ne_zero p hdeg (eval_constantCoeff_eq_zero p ξ hp) hD
  have hcoef : ∀ m ∈ p.support, v (p.coeff m) ≤ ⨆ m : p.support, v (p.coeff m) := fun m hm =>
    le_ciSup (f := fun m : p.support => v (p.coeff m)) (Set.finite_range _).bddAbove ⟨m, hm⟩
  refine abv_constantCoeff_dividedDerivative_le_pow p ξ hp hv hξ ha
    ((one_le_div (v.pos ha)).mpr (abv_eval_pderiv_zero_le p hv hξ
      (Real.iSup_nonneg fun _ => v.nonneg _) hcoef))
    (fun m hm => (hcoef m hm).trans_eq (div_mul_cancel₀ _ (v.pos ha).ne').symm) l

end Faltings.PowerSeries
