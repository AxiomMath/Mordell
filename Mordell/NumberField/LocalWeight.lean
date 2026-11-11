module
public import Mathlib
public import Mordell.Attr

/-!
# Local weights of the places of a number field

Let `K` be a number field. Its set of places `M_K` is the disjoint union of the infinite places
(Mathlib's `NumberField.InfinitePlace K`) and the finite places (`NumberField.FinitePlace K`).
The local weight of a place `v` is `κ_v = [K_v : ℝ] / [K : ℚ]` if `v` is infinite and `κ_v = 0`
if `v` is finite. With Bombieri's normalised absolute values one has `|M|_v = M ^ κ_v` for every
positive integer `M` and every place `v`.

## Main definitions

* `Faltings.NumberField.localWeight`: the local weight `κ_v` of a place `v` of `K`.

## Implementation notes

A place of `K` is a term of `InfinitePlace K ⊕ FinitePlace K`. For an infinite place `w` the local
degree `[K_w : ℝ]` is `w.mult` (it is `1` if `w` is real and `2` if `w` is complex), so the weight
is `w.mult / finrank ℚ K`. The weight is real-valued because it is used as a real exponent.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
-/

namespace Faltings.NumberField

open _root_.NumberField Module

/-- The local weight `κ_v` of a place `v` of a number field `K`: `[K_v : ℝ] / [K : ℚ]` at an
infinite place `v` and `0` at a finite place. -/
@[expose, faltings "def_bvs_local_weight"]
public noncomputable def localWeight (K : Type*) [Field K] [NumberField K] :
    InfinitePlace K ⊕ FinitePlace K → ℝ
  | .inl w => (w.mult : ℝ) / finrank ℚ K
  | .inr _ => 0

end Faltings.NumberField


/-!
# The local weights of a number field sum to one

Let `K` be a number field. The local weights `κ_v` of its places
(`Faltings.NumberField.localWeight`) sum to `1`: the finite places have weight `0`, and
`∑_{w | ∞} [K_w : ℝ] = [K : ℚ]`.

## Main results

* `Faltings.NumberField.finsum_localWeight`: `∑ᶠ v, κ_v = 1`.

## Implementation notes

There are infinitely many places, so the sum is a `finsum`; its support is contained in the
(finite) set of infinite places.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
-/

namespace Faltings.NumberField

open _root_.NumberField

/-- The local weights of the places of a number field sum to one: the finite places have
weight `0`, and the infinite ones sum to `∑_w [K_w : ℝ] / [K : ℚ] = 1`
(`NumberField.InfinitePlace.sum_mult_eq`). -/
@[faltings "lem_bvs_local_weights_sum"]
public theorem finsum_localWeight (K : Type*) [Field K] [NumberField K] :
    ∑ᶠ v, localWeight K v = 1 := by
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.map .inl) _
    (by rintro (w | v) h <;> simp_all [localWeight])]
  simp only [Finset.sum_map, Function.Embedding.inl_apply, localWeight, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (by exact_mod_cast Module.finrank_pos.ne')]
  exact_mod_cast InfinitePlace.sum_mult_eq

end Faltings.NumberField
