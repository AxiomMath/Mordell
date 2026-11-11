module

public import Mordell.Height.Weil.Basic
public import Mordell.Height.Weil.Representative

/-!
# The affine height as a sum of local terms

Let `ξ = (ξ_1, …, ξ_n) ∈ ℚ̄ⁿ` and let `F` be a number field containing `ξ_1, …, ξ_n`. Then the
height of `ξ` is the sum over the places of `F` of the positive parts of the local logarithmic
sizes of `ξ`:
`h(ξ) = ∑_{v ∈ M_F} log⁺ max_j |ξ_j|_v`.
For `n = 1` this is `h(α) = ∑_{v ∈ M_F} log⁺ |α|_v`.

## Main results

* `Faltings.affineWeilHeight_eq_finsum_posLog`: `h(ξ) = ∑ᶠ v, log⁺ |ξ|_v` for `ξ` with
  coordinates in a number field `F ⊆ K`.

## Implementation notes

The ambient field is an arbitrary algebraic extension `K / ℚ`, as for `Faltings.affineWeilHeight`;
`K = AlgebraicClosure ℚ` gives `ℚ̄ⁿ`. The number field `F` "containing the coordinates" is any
number field with a ring map `algebraMap F K`, and the point is `algebraMap F K ∘ ξ` for
`ξ : Fin n → F`. The quantity `max_j |ξ_j|_v` is `Faltings.NumberFieldPlace.vectorAbv`, and the sum
over the places `Faltings.NumberFieldPlace F` is a `finsum`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

section Helpers

variable {F : Type*} [Field F] [NumberField F]

/-- `|(1, ξ)|_w = max 1 |ξ|_w`. -/
private theorem vectorAbv_cons_one (w : NumberFieldPlace F) {n : ℕ} (ξ : Fin n → F) :
    w.vectorAbv (Fin.cons 1 ξ : Fin (n + 1) → F) = max 1 (w.vectorAbv ξ) := by
  have hbdd : BddAbove (Set.range fun j => w.normalizedAbv ((Fin.cons 1 ξ : Fin (n + 1) → F) j)) :=
    (Set.finite_range _).bddAbove
  apply le_antisymm
  · refine Real.iSup_le (fun j => ?_) (zero_le_one.trans (le_max_left _ _))
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · exact le_max_of_le_right <|
        le_ciSup (f := fun i => w.normalizedAbv (ξ i)) (Set.finite_range _).bddAbove i
  · refine max_le ?_ ?_
    · simpa [NumberFieldPlace.vectorAbv] using le_ciSup hbdd 0
    · exact Real.iSup_le (fun i => by simpa [NumberFieldPlace.vectorAbv] using le_ciSup hbdd i.succ)
        (w.vectorAbv_nonneg _)

end Helpers

/-- The height `Faltings.affineWeilHeight ξ = h(1 : ξ_1 : … : ξ_n)` of a point with coordinates
in a number field `F ⊆ K` is the sum over the places `v` of `F` of
`log⁺ |ξ|_v = log⁺ max_j |ξ_j|_v`, with `|ξ|_v` the vector absolute value
`Faltings.NumberFieldPlace.vectorAbv`. The proof writes `h(1 : ξ)` as a sum of local heights
(`Faltings.weilHeight_eq_sumLocalHeight`) and uses `|(1, ξ)|_v = max 1 |ξ|_v`. -/
@[faltings "lem_ht_height_elementary_numbers"]
public theorem affineWeilHeight_eq_finsum_posLog {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {F : Type*} [Field F] [NumberField F] [Algebra F K] {n : ℕ}
    (ξ : Fin n → F) :
    affineWeilHeight (algebraMap F K ∘ ξ) = ∑ᶠ v : NumberFieldPlace F, Real.posLog (v.vectorAbv ξ) := by
  have hc : (algebraMap F K ∘ (Fin.cons 1 ξ : Fin (n + 1) → F)) =
      (Fin.cons 1 (algebraMap F K ∘ ξ) : Fin (n + 1) → K) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have hy : algebraMap F K ∘ (Fin.cons 1 ξ : Fin (n + 1) → F) ≠ 0 := by
    rw [hc]; exact fun h => one_ne_zero (congr_fun h 0)
  unfold affineWeilHeight
  rw [weilHeight_eq_sumLocalHeight hy (by simp_rw [hc]), sumLocalHeight]
  refine finsum_congr fun w => ?_
  rw [NumberFieldPlace.localHeight, vectorAbv_cons_one,
    Real.posLog_eq_log_max_one (w.vectorAbv_nonneg ξ)]

end Faltings
