module
public import Mordell.Polynomial.Eisenstein.Finite
public import Mordell.Polynomial.ImplicitDeriv.Length
public import Mordell.Polynomial.ImplicitDeriv.Recursion
public import Mordell.Polynomial.SimpleRoot

/-!
# The local Eisenstein bound at an infinite place

Let `K` be a number field and `p ∈ K[X, Y]` with `deg_X p ≥ 1`, whose discriminant
`D_p(Y) = Res_X(p, ∂p/∂X)` (formal degrees `deg_X p` and `deg_X p - 1`) does not vanish at `Y = 0`.
Let `ξ ∈ K⟦ς⟧` be a power series with `p(ξ, ς) = 0`, and let `v` be an infinite place of `K` with
`|ξ(0)|_v ≤ 1`, for Bombieri's normalised absolute value `|·|_v`. Then for every `l ≥ 1` the
`l`-th divided derivative of `ξ` at `0` satisfies
`|∂_l ξ(0)|_v ≤ |2 deg p|_v ^ (7l) · (|p|_v / |p_X(ξ(0), 0)|_v) ^ (2l - 1)`,
where `deg p` is the total degree and `|p|_v` the largest `|·|_v` of a coefficient of `p`.

## Main results

* `Faltings.PowerSeries.normalizedAbs_constantCoeff_dividedDerivative_le_of_isInfinite`: the
  bound above.

## Implementation notes

`K[X, Y]` is `MvPolynomial (Fin 2) K`, with `X = X 0` and `Y = X 1`; `p_X` is
`MvPolynomial.pderiv 0 p`, `deg_X p` is `MvPolynomial.degreeOf 0 p` and `deg p` is
`MvPolynomial.totalDegree p`. The discriminant is computed on the image of `p` in
`(MvPolynomial (Fin 1) K)[X]` under `MvPolynomial.finSuccEquiv` (outer variable `X`, coefficients
polynomials in `Y`) as `Polynomial.resultant q (derivative q) e (e - 1)` with `e = q.natDegree`
(which equals `degreeOf 0 p`), and `D_p(0)` is its evaluation at `Y = 0`.

Bombieri's normalised absolute value at the infinite place `w` is `|x|_v = w x ^ (n_w / [K : ℚ])`
with `n_w = w.mult`, written out in the statement; so `|2 deg p|_v = (2 deg p) ^ κ_v` with
`κ_v = Faltings.NumberField.localWeight`. The size `|p|_v` is the supremum over the support of `p`.
The value `∂_l ξ(0)` is `PowerSeries.constantCoeff (Faltings.PowerSeries.dividedDerivative K l ξ)`.
The printed exponent `5l` of the source is replaced by `7l`: the length (sum of absolute values of
coefficients) of Bombieri's auxiliary polynomials `q_l` grows by a factor `4 (2l - 1) D ^ 3` per
step, which yields `72 ^ l D ^ (7l) ≤ (2D) ^ (7l)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 5
-/

namespace Faltings.PowerSeries

open _root_.PowerSeries _root_.NumberField Module Faltings.MvPolynomial

/-- The constant term of `u(ξ, ς)` is `u(ξ(0), 0)`. -/
private lemma constantCoeff_aeval {K : Type*} [Field K] (u : _root_.MvPolynomial (Fin 2) K)
    (ξ : K⟦X⟧) :
    constantCoeff (_root_.MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] u) =
      _root_.MvPolynomial.eval ![constantCoeff ξ, 0] u := by
  rw [_root_.MvPolynomial.aeval_def, _root_.MvPolynomial.hom_eval₂]
  change _root_.MvPolynomial.eval₂ (RingHom.id K) _ u = _
  congr 1
  funext i
  fin_cases i <;> simp

/-- Base change along a ring hom commutes with forming the polynomials `q_l`. -/
private lemma map_implicitDerivNumerator {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : _root_.MvPolynomial (Fin 2) R) : ∀ l : ℕ,
    _root_.MvPolynomial.map f (implicitDerivNumerator p l) =
      implicitDerivNumerator (_root_.MvPolynomial.map f p) l
  | 0 => by simp [implicitDerivNumerator]
  | 1 => by simp [implicitDerivNumerator, _root_.MvPolynomial.pderiv_map]
  | n + 2 => by
    rw [implicitDerivNumerator, implicitDerivNumerator, ← map_implicitDerivNumerator f p (n + 1)]
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, _root_.MvPolynomial.pderiv_map]

/-- A polynomial evaluated at a point of the closed unit polydisc is bounded by its length. -/
private lemma norm_eval_le_length {σ : Type*} [Finite σ] (u : _root_.MvPolynomial σ ℂ)
    (x : σ → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) : ‖_root_.MvPolynomial.eval x u‖ ≤ length u := by
  cases nonempty_fintype σ
  rw [_root_.MvPolynomial.eval_eq', Faltings.MvPolynomial.length]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_prod]
  exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i))

/-- A polynomial in two variables of total degree `D` has at most `(D + 1)²` monomials. -/
private lemma card_support_le {R : Type*} [CommSemiring R] (p : _root_.MvPolynomial (Fin 2) R) :
    p.support.card ≤ (p.totalDegree + 1) ^ 2 := by
  have h := Finset.card_le_card_of_injOn (fun m : Fin 2 →₀ ℕ => (m 0, m 1))
    (s := p.support) (t := Finset.range (p.totalDegree + 1) ×ˢ Finset.range (p.totalDegree + 1))
    (fun m hm => by
      have := _root_.MvPolynomial.le_totalDegree hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
      omega)
    (fun m _ m' _ h => by
      simp only [Prod.mk.injEq] at h
      ext i; fin_cases i <;> simp [h.1, h.2])
  simpa [sq] using h

/-- The numerical heart of the bound: from `𝓛(q_l) ≤ 8^{l-1}(l-1)! D^{3l-2} L^{2l-1}` and
`L ≤ 4 D² B`, `𝓛(q_l) / (l! A^{2l-1}) ≤ (2D)^{7l} (B / A)^{2l-1}` (here `l = n + 1`). -/
private lemma key_estimate {Q L D B A : ℝ} (n : ℕ) (hD : 1 ≤ D) (hL : 0 ≤ L) (hA : 0 < A)
    (hQ : Q ≤ 8 ^ n * (n.factorial : ℝ) * D ^ (3 * n + 1) * L ^ (2 * n + 1))
    (hLB : L ≤ 4 * D ^ 2 * B) :
    Q / ((n + 1).factorial * A ^ (2 * n + 1)) ≤
      (2 * D) ^ (7 * (n + 1)) * (B / A) ^ (2 * n + 1) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hf' : (n.factorial : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_le n.le_succ
  have hD2 : 0 < 4 * D ^ 2 := by positivity
  have hB : 0 ≤ B := le_of_mul_le_mul_left (by linarith : 4 * D ^ 2 * 0 ≤ 4 * D ^ 2 * B) hD2
  have hAp : 0 < A ^ (2 * n + 1) := pow_pos hA _
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc Q ≤ 8 ^ n * (n.factorial : ℝ) * D ^ (3 * n + 1) * (4 * D ^ 2 * B) ^ (2 * n + 1) :=
        hQ.trans (by gcongr)
    _ = (2 ^ (7 * n + 2) * D ^ (7 * n + 3)) * B ^ (2 * n + 1) * n.factorial := by
        rw [mul_pow, mul_pow, show (8 : ℝ) ^ n = 2 ^ (3 * n) by rw [pow_mul]; norm_num,
          show (4 : ℝ) ^ (2 * n + 1) = 2 ^ (4 * n + 2) by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
        ring
    _ ≤ (2 ^ (7 * n + 7) * D ^ (7 * n + 7)) * B ^ (2 * n + 1) * (n + 1).factorial := by
        gcongr
        all_goals first | exact hD | norm_num
    _ = (2 * D) ^ (7 * (n + 1)) * (B ^ (2 * n + 1) / A ^ (2 * n + 1)) *
          ((n + 1).factorial * A ^ (2 * n + 1)) := by
        field_simp
        ring

/-- At the constant term, the recursion `q_l(ξ, ς) + p_X(ξ, ς)^{2l-1} ξ^{(l)} = 0` solves for
`∂_l ξ(0)` (here `l = n + 1`). -/
private lemma constantCoeff_dividedDerivative_eq {K : Type*} [Field K] [CharZero K]
    (p : _root_.MvPolynomial (Fin 2) K) {ξ : K⟦X⟧}
    (hp : _root_.MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0)
    (ha : _root_.MvPolynomial.eval ![constantCoeff ξ, 0] (_root_.MvPolynomial.pderiv 0 p) ≠ 0)
    (n : ℕ) :
    constantCoeff (dividedDerivative K (n + 1) ξ) =
      -_root_.MvPolynomial.eval ![constantCoeff ξ, 0] (implicitDerivNumerator p (n + 1)) /
        ((n + 1).factorial * _root_.MvPolynomial.eval ![constantCoeff ξ, 0]
          (_root_.MvPolynomial.pderiv 0 p) ^ (2 * n + 1)) := by
  have hrec := congrArg constantCoeff
    (aeval_implicitDerivNumerator_add_pow_mul_iterate_derivative p ξ hp ha (Nat.le_add_left 1 n))
  rw [map_add, map_mul, map_pow, constantCoeff_aeval, constantCoeff_aeval, map_zero,
    show 2 * (n + 1) - 1 = 2 * n + 1 by omega, constantCoeff_iterate_derivative] at hrec
  have hf : ((n + 1).factorial : K) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
  rw [constantCoeff_dividedDerivative, eq_div_iff (mul_ne_zero hf (pow_ne_zero _ ha))]
  linear_combination hrec

/-- A polynomial in two variables of total degree `D ≥ 1` whose coefficients have norm at most
`B` has length at most `4 D² B`. -/
private lemma length_le_of_norm_coeff_le {R : Type*} [NormedCommRing R]
    (u : _root_.MvPolynomial (Fin 2) R) (hD : 1 ≤ u.totalDegree) {B : ℝ}
    (hB : ∀ m ∈ u.support, ‖u.coeff m‖ ≤ B) :
    length u ≤ 4 * (u.totalDegree : ℝ) ^ 2 * B := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at hD
  obtain ⟨m, hm⟩ := _root_.MvPolynomial.support_nonempty.2 hu
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB m hm)
  have hD' : (1 : ℝ) ≤ u.totalDegree := by exact_mod_cast hD
  calc length u ≤ ∑ _m ∈ u.support, B := Finset.sum_le_sum hB
    _ = u.support.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((u.totalDegree : ℝ) + 1) ^ 2 * B := by gcongr; exact_mod_cast card_support_le u
    _ ≤ 4 * (u.totalDegree : ℝ) ^ 2 * B := by gcongr; nlinarith

/-- The Eisenstein bound at a complex embedding `σ`: if `|σ ξ(0)| ≤ 1` and the coefficients of
`σ p` have absolute value at most `B`, then
`|σ ∂_l ξ(0)| ≤ (2D)^{7l} (B / |σ p_X(ξ(0), 0)|)^{2l-1}` (here `l = n + 1`). -/
private lemma norm_constantCoeff_dividedDerivative_le {K : Type*} [Field K] [CharZero K]
    (σ : K →+* ℂ) (p : _root_.MvPolynomial (Fin 2) K) (hD : 1 ≤ p.totalDegree) {ξ : K⟦X⟧}
    (hp : _root_.MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0)
    (ha : _root_.MvPolynomial.eval ![constantCoeff ξ, 0] (_root_.MvPolynomial.pderiv 0 p) ≠ 0)
    (hξ : ‖σ (constantCoeff ξ)‖ ≤ 1) {B : ℝ} (hB : ∀ m ∈ p.support, ‖σ (p.coeff m)‖ ≤ B)
    (n : ℕ) :
    ‖σ (constantCoeff (dividedDerivative K (n + 1) ξ))‖ ≤
      (2 * p.totalDegree) ^ (7 * (n + 1)) * (B / ‖σ (_root_.MvPolynomial.eval
        ![constantCoeff ξ, 0] (_root_.MvPolynomial.pderiv 0 p))‖) ^ (2 * n + 1) := by
  set P := _root_.MvPolynomial.map σ p
  have hsupp : P.support = p.support := _root_.MvPolynomial.support_map_of_injective p σ.injective
  have hdegP : P.totalDegree = p.totalDegree := by
    simp only [_root_.MvPolynomial.totalDegree, hsupp]
  have hQ : ‖σ (_root_.MvPolynomial.eval ![constantCoeff ξ, 0] (implicitDerivNumerator p (n + 1)))‖
      ≤ 8 ^ n * (n.factorial : ℝ) * (p.totalDegree : ℝ) ^ (3 * n + 1) * length P ^ (2 * n + 1) := by
    rw [_root_.MvPolynomial.map_eval, map_implicitDerivNumerator]
    refine (norm_eval_le_length _ _ fun i => by fin_cases i <;> simp [hξ]).trans ?_
    simpa [hdegP, show 3 * (n + 1) - 2 = 3 * n + 1 by omega,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega] using
      length_implicitDerivNumerator_le P (hdegP ▸ hD) (Nat.le_add_left 1 n)
  have hLB := length_le_of_norm_coeff_le P (hdegP ▸ hD) (B := B) fun m hm => by
    rw [hsupp] at hm; rw [_root_.MvPolynomial.coeff_map]; exact hB m hm
  rw [constantCoeff_dividedDerivative_eq p hp ha, map_div₀, map_neg, norm_div, norm_neg, map_mul,
    map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
  exact key_estimate n (by exact_mod_cast hD) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) hQ (hdegP ▸ hLB)

/-- Local Eisenstein bound at an infinite place `w` of a number field `K`: if `p ∈ K[X, Y]` has
`deg_X p ≥ 1` and `Res_X(p, p_X)(0) ≠ 0`, `ξ ∈ K⟦ς⟧` satisfies `p(ξ, ς) = 0` and `|ξ(0)|_w ≤ 1`,
then `|∂_l ξ(0)|_w ≤ |2 deg p|_w ^ (7l) (|p|_w / |p_X(ξ(0), 0)|_w) ^ (2l - 1)` for `l ≥ 1`, where
`|x|_w = w x ^ (w.mult / [K : ℚ])` and `|p|_w` is the largest `|·|_w` of a coefficient of `p`. -/
@[faltings "lem_bvs_eisenstein_infinite"]
public theorem normalizedAbs_constantCoeff_dividedDerivative_le_of_isInfinite
    {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (p : MvPolynomial (Fin 2) K) (hdeg : 1 ≤ p.degreeOf 0)
    (hD : let q := MvPolynomial.finSuccEquiv K 1 p
      MvPolynomial.eval 0 (q.resultant (Polynomial.derivative q) q.natDegree (q.natDegree - 1)) ≠ 0)
    (ξ : K⟦X⟧) (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0) {l : ℕ} (hl : 1 ≤ l) :
    let absV : K → ℝ := fun x => w x ^ ((w.mult : ℝ) / finrank ℚ K)
    absV (constantCoeff ξ) ≤ 1 →
    absV (constantCoeff (dividedDerivative K l ξ)) ≤
      absV (2 * p.totalDegree : K) ^ (7 * l) *
        ((⨆ m : p.support, absV (p.coeff m)) /
          absV (MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p))) ^
            (2 * l - 1) := by
  intro absV hξ
  set σ : K →+* ℂ := w.embedding
  set κ : ℝ := (w.mult : ℝ) / finrank ℚ K
  have hκ : 0 < κ := div_pos (by exact_mod_cast InfinitePlace.mult_pos)
    (by exact_mod_cast Module.finrank_pos)
  have habs (x : K) : absV x = ‖σ x‖ ^ κ := by
    change w x ^ κ = ‖w.embedding x‖ ^ κ
    rw [InfinitePlace.norm_embedding_eq]
  have ha := eval_pderiv_zero_ne_zero p hdeg (by rw [← constantCoeff_aeval, hp, map_zero])
    (by simpa only [_root_.MvPolynomial.natDegree_finSuccEquiv] using hD)
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image p.support (fun m => ‖σ (p.coeff m)‖)
    (MvPolynomial.support_nonempty.2 (by rintro rfl; simp at hdeg))
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  have hmain := norm_constantCoeff_dividedDerivative_le σ p
    (hdeg.trans (MvPolynomial.degreeOf_le_totalDegree p 0)) hp ha
    (le_of_not_gt fun h => (Real.one_lt_rpow h hκ).not_ge (habs _ ▸ hξ)) hmax n
  have hBS : ‖σ (p.coeff m₀)‖ ^ κ ≤ ⨆ m : p.support, absV (p.coeff m) := by
    rw [← habs]
    exact le_ciSup (f := fun m : p.support => absV (p.coeff m)) (Set.finite_range _).bddAbove
      ⟨m₀, hm₀⟩
  set A := ‖σ (MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p))‖
  have hA : 0 < A := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have h2D : absV (2 * p.totalDegree : K) = (2 * p.totalDegree) ^ κ := by
    rw [habs, map_mul, map_natCast, map_ofNat, norm_mul, Complex.norm_natCast]
    norm_num
  rw [habs, h2D, habs, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  calc _ ≤ ((2 * p.totalDegree) ^ (7 * (n + 1)) * (‖σ (p.coeff m₀)‖ / A) ^ (2 * n + 1)) ^ κ :=
        Real.rpow_le_rpow (norm_nonneg _) hmain hκ.le
    _ = (((2 : ℝ) * p.totalDegree) ^ κ) ^ (7 * (n + 1)) *
          (‖σ (p.coeff m₀)‖ ^ κ / A ^ κ) ^ (2 * n + 1) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_pow_comm (by positivity),
          ← Real.rpow_pow_comm (by positivity), Real.div_rpow (norm_nonneg _) hA.le]
    _ ≤ _ := by gcongr

end Faltings.PowerSeries
