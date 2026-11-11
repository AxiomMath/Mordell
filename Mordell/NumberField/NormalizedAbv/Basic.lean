module

public import Mordell.NumberField.Place.Basic

/-!
# Bombieri's normalized absolute values

Let `K` be a number field of degree `D = [K : ℚ]` and let `w ∈ M_K` lie over `p ∈ M_ℚ`. For
`x ∈ K` the normalized absolute value is `|x|_w = |N_{K_w/ℚ_p}(x)|_p ^ (1/D)`. For `K = ℚ` these
are the usual `p`-adic and euclidean absolute values.

The quantity `|N_{K_w/ℚ_p}(x)|_p` is the module of multiplication by `x` on `K_w`, which is
Mathlib's normalization of the absolute value at `w`:

* for a finite place `w` with prime `𝔭`, it is `N(𝔭) ^ (-ord_𝔭 x)`, the value of the
  `NumberField.FinitePlace` `w` at `x` (normalized by `Ideal.absNorm`);
* for an infinite place `w` defined by `σ : K → ℂ`, it is `|σ x| ^ n_w`, where `n_w` is
  `NumberField.InfinitePlace.mult w` (`1` if `w` is real, `2` if `w` is complex), since
  `N_{ℝ/ℝ}(σ x) = σ x` and `N_{ℂ/ℝ}(σ x) = |σ x|²`.

So `|x|_w` is the `D`-th root of these.

## Main definitions

* `Faltings.NumberFieldPlace.normalizedAbv w x`: Bombieri's normalized absolute value `|x|_w`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_inl`, `Faltings.NumberFieldPlace.normalizedAbv_inr`:
  the defining formulas.
* `Faltings.NumberFieldPlace.normalizedAbv_zero`, `Faltings.NumberFieldPlace.normalizedAbv_one`:
  `|0|_w = 0` and `|1|_w = 1`.
* `Faltings.NumberFieldPlace.normalizedAbv_nonneg`: `0 ≤ |x|_w`.

## Implementation notes

The definition is by cases on `w`, through Mathlib's absolute values at the finite and infinite
places, whose values are `|N_{K_w/ℚ_p}(x)|_p` as recalled above; the place `p` of `ℚ` below `w`
is determined by `w` and does not appear as an argument. That the definition agrees with the
local norm, and the explicit formulas `N(𝔭) ^ (-ord_𝔭 x / D)` and `|σ x| ^ (n_w / D)`, are
separate results.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

open NumberField

/-- Bombieri's normalized absolute value `|x|_w = |N_{K_w/ℚ_p}(x)|_p ^ (1/[K:ℚ])` at a place
`w` of the number field `K`. At a finite place it is `w x ^ (1/[K:ℚ])`, with `w x` Mathlib's
`NumberField.FinitePlace` value; at an infinite place it is `(w x ^ n_w) ^ (1/[K:ℚ])`, with
`n_w = NumberField.InfinitePlace.mult w`. -/
@[faltings "def_ht_absolute_values_normalized"]
noncomputable def NumberFieldPlace.normalizedAbv {K : Type*} [Field K] [NumberField K] :
    NumberFieldPlace K → K → ℝ
  | .inl w, x => w x ^ (Module.finrank ℚ K : ℝ)⁻¹
  | .inr w, x => (w x ^ w.mult) ^ (Module.finrank ℚ K : ℝ)⁻¹

namespace NumberFieldPlace

variable {K : Type*} [Field K] [NumberField K]

/-- At a finite place, `|x|_w = w x ^ (1/[K:ℚ])`. -/
@[simp]
theorem normalizedAbv_inl (w : FinitePlace K) (x : K) :
    normalizedAbv (.inl w) x = w x ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
  rfl

/-- At an infinite place, `|x|_w = (w x ^ n_w) ^ (1/[K:ℚ])`. -/
@[simp]
theorem normalizedAbv_inr (w : InfinitePlace K) (x : K) :
    normalizedAbv (.inr w) x = (w x ^ w.mult) ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
  rfl

/-- `|0|_w = 0`. -/
@[simp]
theorem normalizedAbv_zero (w : NumberFieldPlace K) : normalizedAbv w 0 = 0 := by
  cases w <;> simp [Module.finrank_pos.ne']

/-- `|1|_w = 1`. -/
@[simp]
theorem normalizedAbv_one (w : NumberFieldPlace K) : normalizedAbv w 1 = 1 := by
  cases w <;> simp

/-- `|x|_w ≥ 0`. -/
theorem normalizedAbv_nonneg (w : NumberFieldPlace K) (x : K) : 0 ≤ normalizedAbv w x := by
  cases w <;> simp only [normalizedAbv_inl, normalizedAbv_inr] <;> positivity

end NumberFieldPlace

end Faltings

/-!
# The archimedean indicator of a place

For a number field `K` and a place `w ∈ M_K`, the archimedean indicator is `ε_w = 1` if `w` is
infinite and `ε_w = 0` if `w` is finite. It enters the generalised triangle inequality
`|a₁ + ⋯ + a_r|_w ≤ |r|_w ^ ε_w · maxᵢ |aᵢ|_w`, which is the ultrametric inequality at a finite
place and the usual triangle inequality at an infinite one.

## Main definitions

* `Faltings.NumberFieldPlace.archimedeanIndicator w`: the indicator `ε_w ∈ {0, 1}` of a place `w`.

## Main results

* `Faltings.NumberFieldPlace.archimedeanIndicator_inl`,
  `Faltings.NumberFieldPlace.archimedeanIndicator_inr`: the values `0` at a finite place and `1`
  at an infinite one.
* `Faltings.NumberFieldPlace.archimedeanIndicator_le_one`: `ε_w ≤ 1`.

## Implementation notes

The indicator takes values in `ℕ`, so that `|r|_w ^ ε_w` is a natural-number power and
`ε_w * log |r|_w` is obtained by the cast `ℕ → ℝ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 6.
* [Z. Gao, *Heights*][gao2022], Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

/-- The archimedean indicator `ε_w` of a place `w` of a number field `K`: `1` if `w` is an
infinite place and `0` if `w` is a finite place. -/
@[faltings "def_ht_archimedean_indicator"]
def NumberFieldPlace.archimedeanIndicator {K : Type*} [Field K] [NumberField K]
    (w : NumberFieldPlace K) : ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1) w

namespace NumberFieldPlace

variable {K : Type*} [Field K] [NumberField K]

/-- `ε_w = 0` at a finite place. -/
@[simp]
theorem archimedeanIndicator_inl (v : NumberField.FinitePlace K) :
    archimedeanIndicator (Sum.inl v : NumberFieldPlace K) = 0 :=
  rfl

/-- `ε_w = 1` at an infinite place. -/
@[simp]
theorem archimedeanIndicator_inr (v : NumberField.InfinitePlace K) :
    archimedeanIndicator (Sum.inr v : NumberFieldPlace K) = 1 :=
  rfl

/-- `ε_w ≤ 1`. -/
theorem archimedeanIndicator_le_one (w : NumberFieldPlace K) : archimedeanIndicator w ≤ 1 := by
  cases w <;> simp

end NumberFieldPlace

end Faltings
