module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mathlib
public import Mordell.Attr

/-!
# The absolute value of a vector at a place

Let `K` be a number field and `w ∈ M_K`. For a vector `x = (x_0, …, x_n) ∈ K^{n+1}` put
`|x|_w = max_j |x_j|_w`, where `|·|_w` is Bombieri's normalized absolute value
`Faltings.NumberFieldPlace.normalizedAbv`.

## Main definitions

* `Faltings.NumberFieldPlace.vectorAbv w x`: the absolute value `|x|_w = max_j |x_j|_w` of a
  vector `x`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_le_vectorAbv`: `|x_i|_w ≤ |x|_w` for a finite index
  type.
* `Faltings.NumberFieldPlace.vectorAbv_pos`: `0 < |x|_w` for a nonzero vector `x` on a finite
  index type.

## Implementation notes

The vector is a function `x : ι → K` on an arbitrary index type, not only `Fin (n + 1)`: the
same quantity is used for coefficient vectors of polynomials, indexed by monomials. The maximum
is written as the supremum `⨆ j, |x_j|_w` in `ℝ`, which is the maximum for a finite nonempty
index type; for an empty index type it is `0`, and every value is nonnegative.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Def. 1.2.1.
-/

@[expose] public section

namespace Faltings

/-- The absolute value `|x|_w = max_j |x_j|_w` of a vector `x : ι → K` at a place `w` of the
number field `K`, with `|·|_w` the normalized absolute value
`Faltings.NumberFieldPlace.normalizedAbv`. It is written as a supremum over `ι`, which is the
maximum when `ι` is finite and nonempty. -/
@[faltings "def_ht_vector_absolute_value"]
public noncomputable def NumberFieldPlace.vectorAbv {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (w : NumberFieldPlace K) (x : ι → K) : ℝ :=
  ⨆ j, w.normalizedAbv (x j)

namespace NumberFieldPlace

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- The normalized absolute value of a nonzero element is positive. -/
public theorem normalizedAbv_pos (w : NumberFieldPlace K) {a : K} (ha : a ≠ 0) :
    0 < w.normalizedAbv a := by
  rcases w with w | w
  · exact Real.rpow_pos_of_pos (w.pos_iff.2 ha) _
  · exact Real.rpow_pos_of_pos (pow_pos (w.pos_iff.2 ha) _) _

/-- The absolute value of a vector is nonnegative. -/
public theorem vectorAbv_nonneg (w : NumberFieldPlace K) (x : ι → K) : 0 ≤ w.vectorAbv x :=
  Real.iSup_nonneg fun _ => normalizedAbv_nonneg _ _

/-- Each coordinate satisfies `|x_i|_w ≤ |x|_w`. -/
public theorem normalizedAbv_le_vectorAbv [Finite ι] (w : NumberFieldPlace K) (x : ι → K) (i : ι) :
    w.normalizedAbv (x i) ≤ w.vectorAbv x :=
  le_ciSup (f := fun j => w.normalizedAbv (x j)) (Set.finite_range _).bddAbove i

/-- A nonzero vector has positive absolute value. -/
public theorem vectorAbv_pos [Finite ι] (w : NumberFieldPlace K) {x : ι → K} (hx : x ≠ 0) :
    0 < w.vectorAbv x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact (w.normalizedAbv_pos hi).trans_le (w.normalizedAbv_le_vectorAbv x i)

end NumberFieldPlace

end Faltings

/-!
# Local heights

Let `K` be a number field, `w ∈ M_K` and `x = (x_0, …, x_n) ∈ K^{n+1} \ {0}`. The local height
of `x` at `w` is `h_w(x) = log |x|_w = max_j log |x_j|_w`, where `|x|_w = max_j |x_j|_w` is
`Faltings.NumberFieldPlace.vectorAbv`.

## Main definitions

* `Faltings.NumberFieldPlace.localHeight w x`: the local height `h_w(x) = log |x|_w`.

## Implementation notes

The definition is total: it is `Real.log (w.vectorAbv x)` for every `x : ι → K`. For `x ≠ 0`
with `ι` finite this is the local height of the source, and it equals `max_j log |x_j|_w` over
the nonzero coordinates. For `x = 0` it takes the value `Real.log 0 = 0`; results about local
heights carry the hypothesis `x ≠ 0`. As for `Faltings.NumberFieldPlace.vectorAbv`, the index type
is an arbitrary `ι` rather than `Fin (n + 1)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Def. 1.2.1.
-/

@[expose] public section

namespace Faltings

open NumberField in
/-- The local height `h_w(x) = log |x|_w` of a vector `x : ι → K` at a place `w` of the number
field `K`, where `|x|_w = max_j |x_j|_w` is `Faltings.NumberFieldPlace.vectorAbv`. For `x ≠ 0` and
`ι` finite it is `max_j log |x_j|_w` over the nonzero coordinates; at `x = 0` it is `0`. -/
@[faltings "def_ht_local_height"]
public noncomputable def NumberFieldPlace.localHeight {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (w : NumberFieldPlace K) (x : ι → K) : ℝ :=
  Real.log (w.vectorAbv x)

end Faltings

/-!
# The sum of the local heights

Let `K` be a number field and `x ∈ K^{n+1} \ {0}`. The sum of the local heights of `x` is
`S_K(x) = ∑_{w ∈ M_K} h_w(x)`, where `h_w(x) = log |x|_w` is
`Faltings.NumberFieldPlace.localHeight`. Only finitely many terms are nonzero
(`Faltings.NumberFieldPlace.finite_support_localHeight`), so the sum is a real number.

## Main definitions

* `Faltings.sumLocalHeight x`: the sum `S_K(x) = ∑_{w ∈ M_K} h_w(x)`.

## Implementation notes

The sum over the infinite set `M_K = Faltings.NumberFieldPlace K` is a `finsum`. It agrees with
the honest sum whenever the support is finite, which is the case for `x ≠ 0` with finitely many
coordinates; the definition is total, and results about it carry the hypothesis `x ≠ 0`. As for
`Faltings.NumberFieldPlace.localHeight`, the index type is an arbitrary `ι` rather than
`Fin (n + 1)`.

Mathlib's `Height.logHeight x` is the height relative to `K`; it equals `[K : ℚ] • S_K(x)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Def. 1.2.1.
-/

@[expose] public section

namespace Faltings

/-- The sum `S_K(x) = ∑_{w ∈ M_K} h_w(x)` of the local heights
`Faltings.NumberFieldPlace.localHeight` of a vector `x : ι → K` over all places of the number
field `K`, as a `finsum`. For `x ≠ 0` with `ι` finite only finitely many terms are nonzero. -/
@[faltings "def_ht_height_sum"]
public noncomputable def sumLocalHeight {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (x : ι → K) : ℝ :=
  ∑ᶠ w : NumberFieldPlace K, w.localHeight x

end Faltings

/-!
# Local heights vanish at almost all places

Let `K` be a number field and `x ∈ K^{n+1} \ {0}`. Then the local height `h_w(x)` vanishes for
all but finitely many places `w ∈ M_K`: outside the finitely many places where some nonzero
coordinate of `x` is not a unit, every nonzero coordinate has `|x_j|_w = 1`, so `|x|_w = 1`.

## Main results

* `Faltings.NumberFieldPlace.finite_support_localHeight`: for `x ≠ 0` with finitely many
  coordinates, the function `w ↦ h_w(x)` on `Faltings.NumberFieldPlace K` has finite support.

## Implementation notes

The vector is indexed by an arbitrary finite type `ι` in place of `Fin (n + 1)`, as for
`Faltings.NumberFieldPlace.localHeight`. "For all but finitely many `w`" is stated as finiteness of
`Function.support`, the form used by `finsum`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Def. 1.2.1.
-/

@[expose] public section

namespace Faltings

open NumberField

/-- If every nonzero coordinate of a nonzero vector `x` has `|x_j|_w = 1`, then `|x|_w = 1`. -/
private lemma NumberFieldPlace.vectorAbv_eq_one {K : Type*} [Field K] [NumberField K] {ι : Type*}
    [Finite ι] {w : NumberFieldPlace K} {x : ι → K} (hx : x ≠ 0)
    (h : ∀ j, x j ≠ 0 → w.normalizedAbv (x j) = 1) : w.vectorAbv x = 1 := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨j₀⟩
  refine le_antisymm (ciSup_le fun j => ?_) ((h j₀ hj₀).symm.le.trans
    (le_ciSup (f := fun j => w.normalizedAbv (x j)) (Set.finite_range _).bddAbove j₀))
  by_cases hj : x j = 0
  · rcases w with w | w <;>
      simp [hj, Real.zero_rpow, Module.finrank_pos.ne', InfinitePlace.mult_ne_zero]
  · exact (h j hj).le

/-- For a nonzero vector `x : ι → K` with finitely many coordinates over a number field `K`, the
local height `Faltings.NumberFieldPlace.localHeight w x` is zero for all but finitely many places
`w`. -/
@[faltings "lem_ht_local_height_finite_support"]
public theorem NumberFieldPlace.finite_support_localHeight {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (Function.support fun w : NumberFieldPlace K => w.localHeight x).Finite := by
  have hS : (⋃ j ∈ {j | x j ≠ 0}, Function.mulSupport fun w : FinitePlace K => w (x j)).Finite :=
    (Set.toFinite _).biUnion fun j hj => FinitePlace.hasFiniteMulSupport hj
  refine ((hS.image Sum.inl).union (Set.finite_range Sum.inr)).subset ?_
  rintro (w | w) hw
  · refine Or.inl ⟨w, ?_, rfl⟩
    by_contra hwS
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hwS
    exact hw (by simp [NumberFieldPlace.localHeight,
      NumberFieldPlace.vectorAbv_eq_one hx fun j hj => by
        rw [NumberFieldPlace.normalizedAbv_inl, hwS j hj, Real.one_rpow]])
  · exact Or.inr ⟨w, rfl⟩

end Faltings
