module
public import Mathlib
public import Mordell.Attr

/-!
# The height of an integral vector

Let `K` be a number field and `x = (x_l)_{l ∈ ι}` a nonzero vector of algebraic integers of `K`.
Then the (absolute, projective) height of `x` is at most `log max_l house (x_l)`: at a finite
place every `|x_l|_v ≤ 1`, and at an infinite place `|x_l|_v` is a conjugate of `x_l`, bounded by
its house.

## Main results

* `Faltings.logHeight_div_finrank_le_log_iSup_house`: `h(x) ≤ log max_l house (x_l)`.

## Implementation notes

The absolute height of `x : ι → K` is `Height.logHeight x / [K : ℚ]`: on a number field
`Height.logHeight` is `∑_{v | ∞} n_v log max_l ‖x_l‖_v + ∑ᶠ_{v ∤ ∞} log max_l ‖x_l‖_v`, and
dividing by the degree gives the normalisation in which the local weights sum to one. The
maximum over the coordinates is the supremum `⨆ l, house (x_l)` over the finite index type.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8
-/

namespace Faltings

open NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- A `finprod` of reals in `[0, 1]` is at most one. -/
private lemma finprod_le_one_of_le_one {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : ∏ᶠ a, f a ≤ 1 := by
  by_cases hf : (Function.mulSupport f).Finite
  · rw [finprod_eq_prod f hf]
    exact Finset.prod_le_one₀ (fun a _ ↦ h0 a) (fun a _ ↦ h1 a)
  · rw [finprod_of_infinite_mulSupport hf]

/-- At an infinite place, every coordinate of an integral vector is bounded by the largest
house of the coordinates. -/
private lemma infinitePlace_le_iSup_house (x : ι → 𝓞 K) (w : InfinitePlace K) (i : ι) :
    w (x i : K) ≤ ⨆ l, house (x l : K) :=
  ((InfinitePlace.le_iff_le _ _).mpr (fun φ ↦ norm_embedding_le_house _ φ) w).trans
    (le_ciSup (f := fun l ↦ house (x l : K)) (Finite.bddAbove_range _) i)

/-- The multiplicative height of a nonzero integral vector is at most the `[K : ℚ]`-th power of
the largest house of its coordinates: the finite places contribute at most `1`, and each
infinite place `w` at most `(max_l house x_l) ^ n_w`. -/
private lemma mulHeight_le_iSup_house_pow (x : ι → 𝓞 K) (hx : (fun l ↦ (x l : K)) ≠ 0) :
    Height.mulHeight (fun l ↦ (x l : K)) ≤ (⨆ l, house (x l : K)) ^ Module.finrank ℚ K := by
  obtain ⟨l₀, -⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨l₀⟩
  have hw (w : InfinitePlace K) : 0 ≤ ⨆ i, w (x i : K) :=
    le_ciSup_of_le (Finite.bddAbove_range _) l₀ (by positivity)
  have hv (v : FinitePlace K) : 0 ≤ ⨆ i, v (x i : K) :=
    le_ciSup_of_le (Finite.bddAbove_range _) l₀ (by positivity)
  have hwH (w : InfinitePlace K) : ⨆ i, w (x i : K) ≤ ⨆ l, house (x l : K) :=
    ciSup_le (infinitePlace_le_iSup_house x w)
  rw [NumberField.mulHeight_eq hx, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine (mul_le_mul (Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (hw w) _)
      fun w _ ↦ pow_le_pow_left₀ (hw w) (hwH w) _)
    (finprod_le_one_of_le_one hv fun v ↦ ciSup_le fun i ↦
      FinitePlace.norm_embedding_eq v (x i) ▸ FinitePlace.norm_le_one K v.maximalIdeal (x i))
    (finprod_nonneg hv) (Finset.prod_nonneg fun w _ ↦ pow_nonneg ((hw w).trans (hwH w)) _))
    |>.trans_eq (mul_one _)

/-- For a nonzero vector `x` of algebraic integers of a number field `K`, the absolute height
`Height.logHeight x / [K : ℚ]` is at most `log max_l house (x_l)`. -/
@[faltings "lem_bvs_height_integral_vector"]
public theorem logHeight_div_finrank_le_log_iSup_house {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Finite ι] (x : ι → 𝓞 K) (hx : x ≠ 0) :
    Height.logHeight (fun l ↦ (x l : K)) / Module.finrank ℚ K ≤
      Real.log (⨆ l, house (x l : K)) := by
  have hx' : (fun l ↦ (x l : K)) ≠ 0 := fun h ↦ hx (funext fun l ↦ by simpa using congrFun h l)
  rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos), Height.logHeight_eq_log_mulHeight,
    mul_comm, ← Real.log_pow]
  exact Real.log_le_log (Height.mulHeight_pos _) (mulHeight_le_iSup_house_pow x hx')

end Faltings
