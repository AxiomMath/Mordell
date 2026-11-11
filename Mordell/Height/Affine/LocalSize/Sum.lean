module
public import Mordell.NumberField.LocalWeight

/-!
# The local size of a sum of polynomials

Let `K` be a number field, `v` a place of `K` and `|·|_v` Bombieri's normalised absolute value
on `K`. For a polynomial (or any coefficient vector) `f` over `K`, `|f|_v` is the maximum of
`|c|_v` over the coefficients `c` of `f`. If `f_1, …, f_M` (`M ≥ 1`) are such coefficient
vectors, then
`|f_1 + ⋯ + f_M|_v ≤ M ^ κ_v · max_t |f_t|_v`,
where `κ_v` is the local weight of `v` (`Faltings.NumberField.localWeight`). At a finite place
`κ_v = 0` and this is the ultrametric inequality; at an infinite place it follows from
`|M|_v = M ^ κ_v` and the triangle inequality, applied coefficientwise.

## Main results

* `Faltings.NumberField.iSup_normalizedAbs_sum_le`: the local size of a sum of `M ≥ 1`
  coefficient vectors is at most `M ^ κ_v` times the largest local size of a summand.

## Implementation notes

A coefficient vector is a finitely supported function `f : α →₀ K`. A polynomial
`MvPolynomial σ K` in any number of variables is `(σ →₀ ℕ) →₀ K`, so the statement for
polynomials is the case `α = σ →₀ ℕ`. The size `|f|_v` is the supremum of `|f c|_v` over the
support of `f`, which is `0` for `f = 0`.

A place is a term of `InfinitePlace K ⊕ FinitePlace K`. Bombieri's normalised absolute value is
`‖x‖_w ^ (n_w / [K : ℚ])` at an infinite place `w` (with `n_w = w.mult`) and
`‖x‖_w ^ (1 / [K : ℚ])` at a finite place `w`, where `‖x‖_w` is Mathlib's absolute value at `w`
(`|σ x|` for an embedding `σ`, resp. `N(𝔭) ^ (-v_𝔭(x))`); it is written out in the statement.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 7 and 8
-/

namespace Faltings.NumberField

open _root_.NumberField Module Finset

/-- At an infinite place `w`, the triangle inequality gives
`w (∑ t ∈ s, x t) ^ e ≤ #s ^ e * A` whenever every `w (x t) ^ e` is at most `A`. -/
private lemma infinitePlace_rpow_sum_le {K ι : Type*} [Field K] (w : InfinitePlace K)
    {s : Finset ι} (hs : s.Nonempty) (x : ι → K) {e A : ℝ} (he : 0 ≤ e)
    (hx : ∀ t ∈ s, w (x t) ^ e ≤ A) :
    w (∑ t ∈ s, x t) ^ e ≤ (#s : ℝ) ^ e * A := by
  obtain ⟨t₀, ht₀, hmax⟩ := s.exists_max_image (fun t => w (x t)) hs
  calc w (∑ t ∈ s, x t) ^ e ≤ ((#s : ℝ) * w (x t₀)) ^ e := by
        gcongr
        exact (w.1.sum_le _ _).trans <| (sum_le_card_nsmul _ _ _ hmax).trans_eq (nsmul_eq_mul _ _)
    _ = (#s : ℝ) ^ e * w (x t₀) ^ e := Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (#s : ℝ) ^ e * A := by gcongr; exact hx t₀ ht₀

/-- At a finite place `w`, the ultrametric inequality gives `w (∑ t ∈ s, x t) ^ e ≤ A`
whenever every `w (x t) ^ e` is at most `A`. -/
private lemma finitePlace_rpow_sum_le {K ι : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) {s : Finset ι} (hs : s.Nonempty) (x : ι → K) {e A : ℝ} (he : 0 ≤ e)
    (hx : ∀ t ∈ s, w (x t) ^ e ≤ A) :
    w (∑ t ∈ s, x t) ^ e ≤ A := by
  obtain ⟨t₀, ht₀, heq⟩ := exists_mem_eq_sup' hs (fun t => w (x t))
  refine le_trans ?_ (hx t₀ ht₀)
  gcongr
  exact heq ▸ IsNonarchimedean.apply_sum_le_sup
    (fun a b => FinitePlace.add_le w a b) hs

/-- A coefficient of `g` has size at most the size of `g`, for a nonnegative size function
vanishing at `0`. -/
private lemma le_iSup_support {α K : Type*} [Zero K] (g : α →₀ K) {φ : K → ℝ}
    (h0 : φ 0 = 0) (hφ : ∀ x, 0 ≤ φ x) (c : α) :
    φ (g c) ≤ ⨆ c : g.support, φ (g c) := by
  by_cases hc : c ∈ g.support
  · exact le_ciSup (f := fun c : g.support => φ (g c)) (Set.finite_range _).bddAbove ⟨c, hc⟩
  · rw [Finsupp.notMem_support_iff.mp hc, h0]
    exact Real.iSup_nonneg fun _ => hφ _

/-- For a place `v` of a number field `K` and coefficient vectors `f t` (`t ∈ s`, `s ≠ ∅`) over
`K`, the local size `|∑_t f t|_v` (the largest normalised `|c|_v` over the coefficients `c`) is
at most `(#s) ^ κ_v` times `max_t |f t|_v`, where `κ_v = localWeight K v`. -/
@[faltings "lem_bvs_local_size_sum"]
public theorem iSup_normalizedAbs_sum_le {K : Type*} [Field K] [NumberField K] {α ι : Type*}
    (v : InfinitePlace K ⊕ FinitePlace K) {s : Finset ι} (hs : s.Nonempty) (f : ι → α →₀ K) :
    let absV : K → ℝ := fun x =>
      Sum.elim (fun w : InfinitePlace K => w x ^ ((w.mult : ℝ) / finrank ℚ K))
        (fun w : FinitePlace K => w x ^ ((1 : ℝ) / finrank ℚ K)) v
    (⨆ c : (∑ t ∈ s, f t).support, absV ((∑ t ∈ s, f t) c)) ≤
      (#s : ℝ) ^ localWeight K v * ⨆ t : s, ⨆ c : (f t).support, absV (f t c) := by
  intro absV
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have habs0 : ∀ x, 0 ≤ absV x := by
    rcases v with w | w <;> exact fun x => Real.rpow_nonneg (by positivity) _
  have habs_zero : absV 0 = 0 := by
    rcases v with w | w
    · simpa [absV] using Real.zero_rpow (by have := w.mult_pos; positivity)
    · simpa [absV] using Real.zero_rpow (one_div_pos.mpr hd).ne'
  have hA : ∀ t ∈ s, ∀ c, absV (f t c) ≤ ⨆ t : s, ⨆ c : (f t).support, absV (f t c) :=
    fun t ht c => (le_iSup_support (f t) habs_zero habs0 c).trans <|
      le_ciSup (f := fun t : s => ⨆ c : (f t).support, absV (f t c))
        (Set.finite_range _).bddAbove ⟨t, ht⟩
  refine Real.iSup_le (fun c => ?_) (mul_nonneg (Real.rpow_nonneg (by positivity) _) <|
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => habs0 _)
  rw [Finsupp.finsetSum_apply]
  rcases v with w | w
  · exact infinitePlace_rpow_sum_le w hs _ (by positivity) fun t ht => hA t ht c
  · rw [localWeight, Real.rpow_zero, one_mul]
    exact finitePlace_rpow_sum_le w hs _ (by positivity) fun t ht => hA t ht c

end Faltings.NumberField
