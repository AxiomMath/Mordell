module
public import Mordell.Polynomial.MonomialCard
public import Mordell.Height.Affine.LocalSize.Sum

/-!
# The local size of a value of a polynomial

Let `K` be a number field, `v` a place of `K`, and for a polynomial `f` over `K` let `|f|_v` be
the maximum of Bombieri's normalised absolute values `|c|_v` of its coefficients. If `f` has
degree at most `e_t` in the variable `X_t` for every `t`, then for every point `a` one has
`|f(a)|_v ≤ (#f) ^ κ_v · |f|_v · ∏_t max(1, |a_t|_v) ^ e_t`,
where `#f` is the number of monomials of `f` (`Faltings.MvPolynomial.monomialCount`) and `κ_v`
is the local weight of `v` (`Faltings.NumberField.localWeight`). Indeed `f(a)` is a sum of `#f`
terms `c · a^i` with `i_t ≤ e_t`, each of normalised absolute value at most
`|f|_v ∏_t max(1, |a_t|_v) ^ e_t`.

## Main definitions

* `Faltings.NumberField.normalizedAbs`: Bombieri's normalised absolute value `|·|_v`, as a
  monoid-with-zero hom.

## Main results

* `Faltings.NumberField.normalizedAbs_eval_le`: the bound on `|f(a)|_v`.

## Implementation notes

The variables are indexed by an arbitrary finite type `σ` (the source's `{1, …, r}`), and the
degree bound in `X_t` is `MvPolynomial.degreeOf t f ≤ e t`. A place of `K` is a term of
`InfinitePlace K ⊕ FinitePlace K`; Bombieri's normalised absolute value is
`‖x‖_w ^ (n_w / [K : ℚ])` at an infinite place `w` (with `n_w = w.mult`) and
`‖x‖_w ^ (1 / [K : ℚ])` at a finite place `w`, the conventions of `Faltings.affineLogHeight`.
The size `|f|_v` is the supremum over the support of `f`, which is `0` for `f = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 7 and 8
-/

namespace Faltings.NumberField

open _root_.NumberField Module Finset

variable {K : Type*} [Field K] [NumberField K]

/-- Bombieri's normalised absolute value `|·|_v` at a place `v` of `K`, as a monoid-with-zero
hom: `‖x‖_w ^ (n_w / [K : ℚ])` at an infinite place `w` and `‖x‖_w ^ (1 / [K : ℚ])` at a finite
place `w`. -/
@[expose] public noncomputable def normalizedAbs (v : InfinitePlace K ⊕ FinitePlace K) :
    K →*₀ ℝ where
  toFun x := Sum.elim (fun w : InfinitePlace K => w x ^ ((w.mult : ℝ) / finrank ℚ K))
    (fun w : FinitePlace K => w x ^ ((1 : ℝ) / finrank ℚ K)) v
  map_zero' := by
    have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    rcases v with w | w
    · simpa using Real.zero_rpow (by have := w.mult_pos; positivity)
    · simpa using Real.zero_rpow (one_div_pos.mpr hd).ne'
  map_one' := by rcases v with w | w <;> simp
  map_mul' x y := by
    rcases v with w | w <;> simp [Real.mul_rpow (apply_nonneg _ _) (apply_nonneg _ _)]

/-- At an infinite place `w`, `|x|_w = w x ^ (n_w / [K : ℚ])` with `n_w = w.mult`. -/
@[simp]
public lemma normalizedAbs_inl (w : InfinitePlace K) (x : K) :
    normalizedAbs (.inl w) x = w x ^ ((w.mult : ℝ) / finrank ℚ K) :=
  rfl

/-- At a finite place `w`, `|x|_w = w x ^ (1 / [K : ℚ])`. -/
@[simp]
public lemma normalizedAbs_inr (w : FinitePlace K) (x : K) :
    normalizedAbs (.inr w) x = w x ^ ((1 : ℝ) / finrank ℚ K) :=
  rfl

/-- Bombieri's normalised absolute value is nonnegative. -/
public lemma normalizedAbs_nonneg (v : InfinitePlace K ⊕ FinitePlace K) (x : K) :
    0 ≤ normalizedAbs v x := by
  rcases v with w | w <;> exact Real.rpow_nonneg (apply_nonneg _ _) _

/-- The scalar case of `iSup_normalizedAbs_sum_le`: if `|x t|_v ≤ A` for every `t ∈ s`, `s ≠ ∅`,
then `|∑_{t ∈ s} x t|_v ≤ #s ^ κ_v · A`. -/
private lemma normalizedAbs_sum_le (v : InfinitePlace K ⊕ FinitePlace K) {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (x : ι → K) {A : ℝ}
    (hx : ∀ t ∈ s, normalizedAbs v (x t) ≤ A) :
    normalizedAbs v (∑ t ∈ s, x t) ≤ (#s : ℝ) ^ localWeight K v * A := by
  have key := iSup_normalizedAbs_sum_le v hs fun t => Finsupp.single () (x t)
  rw [← Finsupp.single_finsetSum] at key
  change (⨆ c : _, normalizedAbs v _) ≤ _ * ⨆ t : s, ⨆ c : _, normalizedAbs v _ at key
  have hA : 0 ≤ A := (normalizedAbs_nonneg v _).trans (hx _ hs.choose_spec)
  refine le_trans ?_ (key.trans (mul_le_mul_of_nonneg_left
    (Real.iSup_le (fun t => Real.iSup_le (fun c => by simpa using hx t t.2) hA) hA)
    (by positivity)))
  by_cases h0 : ∑ t ∈ s, x t = 0
  · rw [h0, map_zero]
    exact Real.iSup_nonneg fun _ => normalizedAbs_nonneg v _
  · exact le_trans (by simp) (le_ciSup (Set.finite_range _).bddAbove ⟨(), by simp [h0]⟩)

/-- A term `c_m a^m` of `f(a)` has `|c_m a^m|_v ≤ |f|_v · ∏_t max(1, |a_t|_v) ^ e_t` when
`deg_t f ≤ e_t` for every variable `t`. -/
private lemma normalizedAbs_term_le (v : InfinitePlace K ⊕ FinitePlace K) {σ : Type*}
    [Fintype σ] {f : _root_.MvPolynomial σ K} {e : σ → ℕ} (he : ∀ t, f.degreeOf t ≤ e t)
    (a : σ → K) {m : σ →₀ ℕ} (hm : m ∈ f.support) :
    normalizedAbs v (f.coeff m * ∏ t, a t ^ m t) ≤
      (⨆ m : f.support, normalizedAbs v (f.coeff m)) *
        ∏ t, max 1 (normalizedAbs v (a t)) ^ e t := by
  simp only [map_mul, map_prod, map_pow]
  have h0 := normalizedAbs_nonneg v
  refine mul_le_mul (le_ciSup (f := fun m : f.support => normalizedAbs v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hm⟩)
    (prod_le_prod₀ (fun _ _ => pow_nonneg (h0 _) _) fun t _ => ?_)
    (prod_nonneg fun _ _ => pow_nonneg (h0 _) _) (Real.iSup_nonneg fun _ => h0 _)
  calc normalizedAbs v (a t) ^ m t ≤ max 1 (normalizedAbs v (a t)) ^ m t :=
        pow_le_pow_left₀ (h0 _) (le_max_right _ _) _
    _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _)
        ((_root_.MvPolynomial.monomial_le_degreeOf t hm).trans (he t))

/-- For a polynomial `f` over a number field `K` of degree at most `e t` in each variable `X_t`,
a point `a`, and a place `v` of `K`,
`|f(a)|_v ≤ (#f) ^ κ_v |f|_v ∏_t max(1, |a_t|_v) ^ e_t`, where `|·|_v` is Bombieri's normalised
absolute value, `|f|_v` the maximum over the coefficients of `f`, `#f = monomialCount f` and
`κ_v = localWeight K v`. -/
@[faltings "lem_bvs_local_size_value"]
public theorem normalizedAbs_eval_le {K : Type*} [Field K] [NumberField K] {σ : Type*}
    [Fintype σ] (v : InfinitePlace K ⊕ FinitePlace K) (f : _root_.MvPolynomial σ K)
    (e : σ → ℕ) (he : ∀ t, f.degreeOf t ≤ e t) (a : σ → K) :
    let absv : K → ℝ := fun x =>
      Sum.elim (fun w : InfinitePlace K => w x ^ ((w.mult : ℝ) / finrank ℚ K))
        (fun w : FinitePlace K => w x ^ ((1 : ℝ) / finrank ℚ K)) v
    absv (_root_.MvPolynomial.eval a f) ≤
      (Faltings.MvPolynomial.monomialCount f : ℝ) ^ localWeight K v *
        (⨆ m : f.support, absv (f.coeff m)) * ∏ t, max 1 (absv (a t)) ^ e t := by
  intro absv
  change normalizedAbs v _ ≤ _ * (⨆ m : f.support, normalizedAbs v _) *
    ∏ t, max 1 (normalizedAbs v (a t)) ^ e t
  rcases f.support.eq_empty_or_nonempty with hf | hf
  · simp [_root_.MvPolynomial.support_eq_empty.mp hf]
  rw [_root_.MvPolynomial.eval_eq', mul_assoc]
  exact normalizedAbs_sum_le v hf _ fun m hm => normalizedAbs_term_le v he a hm

end Faltings.NumberField
