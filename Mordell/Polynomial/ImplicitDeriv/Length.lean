module
public import Mordell.Polynomial.Length
public import Mordell.Polynomial.ImplicitDeriv.Basic

/-!
# The length of the polynomials `q_l`

For `p ∈ R[X, Y]` of total degree `D ≥ 1`, the polynomials `q_l = q_l(p)` satisfy
`𝓛(q_l) ≤ 8^{l-1} (l-1)! D^{3l-2} 𝓛(p)^{2l-1}` for every `l ≥ 1`, where `𝓛` is the length
(the sum of the norms of the coefficients). The proof is an induction on `l` using that `𝓛` is
subadditive and submultiplicative and that `𝓛(u_X), 𝓛(u_Y) ≤ deg u · 𝓛(u)`.

## Main results

* `Faltings.MvPolynomial.length_implicitDerivNumerator_le`: the bound on `𝓛(q_l)`.

## Implementation notes

The source works over `ℂ`. The argument only uses that the norm is submultiplicative, that
`‖n • a‖ ≤ n ‖a‖`, and that `‖1‖ = 1` (to bound the integer coefficients `2l - 1` of the
recursion), so the statement is made over any normed commutative ring with `‖1‖ = 1`;
`ℂ` is the instance used downstream. The degree `D` is `p.totalDegree`.

Since `deg q_l ≤ (2l - 1)(D - 1)`, each term of the recursion for `q_{l+1}` is bounded by a
multiple of `D³ 𝓛(p)² 𝓛(q_l)`, giving `𝓛(q_{l+1}) ≤ 4(2l - 1) D³ 𝓛(p)² 𝓛(q_l)`. The induction is
run directly on the closed-form bound, using `4(2l - 1) ≤ 8l`; this absorbs the source's product
estimate `∏_{t=1}^{l-1} (2t - 1) ≤ 2^{l-1} (l-1)!` step by step. The degree bound on `q_l` is
needed over a commutative ring rather than a field, so it is reproved here.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 5
-/

namespace Faltings.MvPolynomial

open _root_.MvPolynomial

section Degree

/-- A partial derivative lowers the total degree by at least one. -/
public lemma totalDegree_pderiv_le {R σ : Type*} [CommSemiring R] (i : σ)
    (p : MvPolynomial σ R) : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  rcases eq_or_ne (s i) 0 with h | h
  · simp [h]
  refine (totalDegree_monomial_le _ _).trans ?_
  have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
  have := le_totalDegree hs
  rw [← tsub_add_cancel_of_le hle, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl] at this
  exact Nat.le_sub_one_of_lt this

/-- A product has total degree at most the sum of bounds for its factors. -/
public lemma totalDegree_mul_le_add {R σ : Type*} [CommSemiring R] {a b : MvPolynomial σ R}
    {m n : ℕ} (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ n) : (a * b).totalDegree ≤ m + n :=
  (totalDegree_mul a b).trans (add_le_add ha hb)

/-- A difference has total degree at most a common bound for its terms. -/
public lemma totalDegree_sub_le_of_le {R σ : Type*} [CommRing R] {a b : MvPolynomial σ R}
    {m : ℕ} (ha : a.totalDegree ≤ m) (hb : b.totalDegree ≤ m) : (a - b).totalDegree ≤ m :=
  (totalDegree_sub a b).trans (max_le ha hb)

/-- One step of the recursion for `q_l` raises the total degree by at most `2 (deg p - 1)`. -/
public lemma totalDegree_implicitDerivNumerator_succ_succ_le {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 2) R) (n : ℕ) :
    (implicitDerivNumerator p (n + 2)).totalDegree ≤
      (implicitDerivNumerator p (n + 1)).totalDegree + 2 * (p.totalDegree - 1) := by
  set E := p.totalDegree - 1
  have hp0 : (pderiv 0 p).totalDegree ≤ E := totalDegree_pderiv_le 0 p
  have hp1 : (pderiv 1 p).totalDegree ≤ E := totalDegree_pderiv_le 1 p
  have hp0' (i : Fin 2) : (pderiv i (pderiv 0 p)).totalDegree ≤ E :=
    (totalDegree_pderiv_le i _).trans ((Nat.sub_le _ _).trans hp0)
  have hq (i : Fin 2) : (pderiv i (implicitDerivNumerator p (n + 1))).totalDegree ≤
      (implicitDerivNumerator p (n + 1)).totalDegree :=
    (totalDegree_pderiv_le i _).trans (Nat.sub_le _ _)
  have hc : ((2 * n + 1 : ℕ) : MvPolynomial (Fin 2) R).totalDegree ≤ 0 := by
    rw [← map_natCast C, totalDegree_C]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_sub_le_of_le ?_ ?_) ?_)
  · exact totalDegree_mul_le_add (hq 1) ((totalDegree_pow _ 2).trans (by omega))
  · exact (totalDegree_mul_le_add (totalDegree_mul_le_add (hq 0) hp0) hp1).trans_eq (by omega)
  · refine (totalDegree_mul_le_add (totalDegree_mul_le_add hc le_rfl) (totalDegree_sub_le_of_le
      (totalDegree_mul_le_add (hp0' 0) hp1) (totalDegree_mul_le_add (hp0' 1) hp0))).trans_eq ?_
    omega

/-- `deg q_l ≤ (2l - 1)(D - 1)` over any commutative ring (`totalDegree_implicitDerivNumerator_le`
is the same bound over a field). -/
private lemma totalDegree_implicitDerivNumerator_le_of_commRing {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 2) R) {l : ℕ} (hl : 1 ≤ l) :
    (implicitDerivNumerator p l).totalDegree ≤ (2 * l - 1) * (p.totalDegree - 1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa [implicitDerivNumerator] using totalDegree_pderiv_le 1 p
  | succ l hl ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hl
    refine (totalDegree_implicitDerivNumerator_succ_succ_le p n).trans ?_
    rw [show 2 * (n + 1 + 1) - 1 = 2 * (n + 1) - 1 + 2 by omega, add_mul]
    omega

end Degree

section Length

variable {σ R : Type*} [SeminormedCommRing R]

private lemma length_nonneg (u : MvPolynomial σ R) : 0 ≤ length u :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The length may be computed as a sum over any finite set containing the support. -/
private lemma length_eq_sum_of_subset {u : MvPolynomial σ R} {t : Finset (σ →₀ ℕ)}
    (h : u.support ⊆ t) : length u = ∑ m ∈ t, ‖u.coeff m‖ :=
  Finset.sum_subset h fun m _ hm => by simp [notMem_support_iff.1 hm]

private lemma length_zero : length (0 : MvPolynomial σ R) = 0 := by simp [length]

/-- The length is subadditive. -/
private lemma length_add_le (a b : MvPolynomial σ R) :
    length (a + b) ≤ length a + length b := by
  classical
  rw [length_eq_sum_of_subset (support_add (p := a) (q := b)),
    length_eq_sum_of_subset (Finset.subset_union_left : a.support ⊆ a.support ∪ b.support),
    length_eq_sum_of_subset (Finset.subset_union_right : b.support ⊆ a.support ∪ b.support),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by rw [_root_.MvPolynomial.coeff_add]; exact norm_add_le _ _

/-- `𝓛(a - b) ≤ 𝓛(a) + 𝓛(b)`. -/
private lemma length_sub_le (a b : MvPolynomial σ R) :
    length (a - b) ≤ length a + length b := by
  simpa [sub_eq_add_neg, length, support_neg] using length_add_le a (-b)

private lemma length_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    length (∑ i ∈ s, f i) ≤ ∑ i ∈ s, length (f i) :=
  Finset.le_sum_of_subadditive length length_zero.le length_add_le s f

/-- `𝓛(c Xˢ) ≤ ‖c‖`. -/
private lemma length_monomial_le (s : σ →₀ ℕ) (c : R) : length (monomial s c) ≤ ‖c‖ := by
  classical
  simp [length_eq_sum_of_subset support_monomial_subset]

/-- The length is submultiplicative. -/
private lemma length_mul_le (a b : MvPolynomial σ R) : length (a * b) ≤ length a * length b := by
  classical
  have hab : length a * length b =
      ∑ x ∈ a.support, ∑ y ∈ b.support, ‖a.coeff x‖ * ‖b.coeff y‖ := by
    rw [length, length, Finset.sum_mul_sum]
  rw [hab]
  conv_lhs => rw [a.as_sum, b.as_sum, Finset.sum_mul_sum]
  refine (length_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (length_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [monomial_mul_monomial]
  exact (length_monomial_le _ _).trans (norm_mul_le _ _)

/-- `𝓛(n) ≤ n` for a natural number `n` when `‖1‖ = 1`. -/
private lemma length_natCast_le [NormOneClass R] (n : ℕ) :
    length (n : MvPolynomial σ R) ≤ n := by
  rw [← map_natCast C, C_apply]
  exact (length_monomial_le _ _).trans ((Nat.norm_cast_le n).trans (by simp))

/-- `𝓛(∂ᵢ u) ≤ deg u · 𝓛(u)`. -/
private lemma length_pderiv_le [NormOneClass R] (i : σ) (u : MvPolynomial σ R) :
    length (pderiv i u) ≤ u.totalDegree * length u := by
  classical
  have hu : (u.totalDegree : ℝ) * length u =
      ∑ s ∈ u.support, (u.totalDegree : ℝ) * ‖u.coeff s‖ := by
    rw [length, Finset.mul_sum]
  rw [hu]
  conv_lhs => rw [u.as_sum]
  rw [map_sum]
  refine (length_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [pderiv_monomial]
  refine (length_monomial_le _ _).trans ((norm_mul_le _ _).trans ?_)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ((Nat.norm_cast_le _).trans ?_) (norm_nonneg _)
  rw [norm_one, mul_one]
  exact_mod_cast (Finsupp.le_degree i s).trans (le_totalDegree hs)

/-- `𝓛(∂ᵢ u) ≤ d · L` from `deg u ≤ d` and `𝓛(u) ≤ L`. -/
private lemma length_pderiv_le_of_le [NormOneClass R] (i : σ) {u : MvPolynomial σ R} {d : ℕ}
    {L : ℝ} (hd : u.totalDegree ≤ d) (hL : length u ≤ L) : length (pderiv i u) ≤ d * L :=
  (length_pderiv_le i u).trans
    (mul_le_mul (by exact_mod_cast hd) hL (length_nonneg u) (Nat.cast_nonneg _))

/-- `𝓛(a b) ≤ A B` from `𝓛(a) ≤ A` and `𝓛(b) ≤ B`. -/
private lemma length_mul_le_of_le {a b : MvPolynomial σ R} {A B : ℝ} (ha : length a ≤ A)
    (hb : length b ≤ B) : length (a * b) ≤ A * B :=
  (length_mul_le a b).trans (mul_le_mul ha hb (length_nonneg b) ((length_nonneg a).trans ha))

end Length

/-- One step of the recursion: `𝓛(q_{l+1}) ≤ 4(2l - 1) D³ 𝓛(p)² 𝓛(q_l)`, here with `l = n + 1`. -/
private lemma length_implicitDerivNumerator_succ_succ_le {R : Type*} [NormedCommRing R]
    [NormOneClass R] (p : MvPolynomial (Fin 2) R) (n : ℕ) :
    length (implicitDerivNumerator p (n + 2)) ≤
      4 * (2 * n + 1) * (p.totalDegree : ℝ) ^ 3 * length p ^ 2 *
        length (implicitDerivNumerator p (n + 1)) := by
  set q := implicitDerivNumerator p (n + 1)
  set D : ℝ := (p.totalDegree : ℝ)
  have hp (i : Fin 2) : length (pderiv i p) ≤ D * length p := length_pderiv_le i p
  have hpp (i : Fin 2) : length (pderiv i (pderiv 0 p)) ≤ D * (D * length p) :=
    length_pderiv_le_of_le i ((totalDegree_pderiv_le 0 p).trans (Nat.sub_le _ _)) (hp 0)
  have hq (i : Fin 2) : length (pderiv i q) ≤ ((2 * n + 1) * p.totalDegree : ℕ) * length q :=
    length_pderiv_le_of_le i ((totalDegree_implicitDerivNumerator_le_of_commRing p n.succ_pos).trans
      (Nat.mul_le_mul (by omega) (Nat.sub_le _ _))) le_rfl
  rw [implicitDerivNumerator, pow_two]
  refine (length_add_le _ _).trans <| (add_le_add ((length_sub_le _ _).trans <| add_le_add
    (length_mul_le_of_le (hq 1) (length_mul_le_of_le (hp 0) (hp 0)))
    (length_mul_le_of_le (length_mul_le_of_le (hq 0) (hp 0)) (hp 1)))
    (length_mul_le_of_le (length_mul_le_of_le (length_natCast_le _) le_rfl)
      ((length_sub_le _ _).trans (add_le_add (length_mul_le_of_le (hpp 0) (hp 1))
        (length_mul_le_of_le (hpp 1) (hp 0)))))).trans_eq ?_
  push_cast
  ring

/-- For `p ∈ R[X, Y]` of total degree `D ≥ 1` and `l ≥ 1`, the polynomial `q_l(p)` has length
`𝓛(q_l) ≤ 8^{l-1} (l-1)! D^{3l-2} 𝓛(p)^{2l-1}`. -/
@[faltings "lem_bvs_q_length_bound"]
public theorem length_implicitDerivNumerator_le {R : Type*} [NormedCommRing R] [NormOneClass R]
    (p : MvPolynomial (Fin 2) R) (hp : 1 ≤ p.totalDegree) {l : ℕ} (hl : 1 ≤ l) :
    length (implicitDerivNumerator p l) ≤
      8 ^ (l - 1) * ((l - 1).factorial : ℝ) * (p.totalDegree : ℝ) ^ (3 * l - 2) *
        length p ^ (2 * l - 1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa [implicitDerivNumerator] using length_pderiv_le 1 p
  | succ l hl ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hl
    rw [show 3 * (n + 1) - 2 = 3 * n + 1 by omega, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      Nat.add_sub_cancel] at ih
    rw [show 3 * (n + 1 + 1) - 2 = 3 * n + 4 by omega,
      show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega, Nat.add_sub_cancel, Nat.factorial_succ]
    have := length_nonneg (implicitDerivNumerator p (n + 1))
    calc _ ≤ _ := length_implicitDerivNumerator_succ_succ_le p n
      _ ≤ 8 * (n + 1) * (p.totalDegree : ℝ) ^ 3 * length p ^ 2 *
          (8 ^ n * n.factorial * (p.totalDegree : ℝ) ^ (3 * n + 1) * length p ^ (2 * n + 1)) := by
        gcongr ?_ * _ * _ * ?_
        linarith
      _ = _ := by push_cast; ring

end Faltings.MvPolynomial
