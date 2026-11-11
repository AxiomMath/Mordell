module

public import Mathlib
public import Mordell.Attr

/-!
# Tate's limit

Let `S` be a set, `φ : S → S` a map, `α > 1` a real number and `f : S → ℝ`. The *Tate limit*
of `f` is the partial function
`f̂ x = lim_{n → ∞} α⁻ⁿ f (φⁿ x)`,
defined exactly at those `x ∈ S` for which this limit exists. Under the hypothesis that
`f ∘ φ - α f` is bounded, the limit exists everywhere, is within a bounded distance of `f`, and
satisfies `f̂ ∘ φ = α f̂`; this is the construction of canonical (Néron–Tate) heights.

## Main definitions

* `Faltings.tateLimit`: the partial function `x ↦ lim_{n → ∞} α⁻ⁿ f (φ^[n] x)`, as an element
  of `S →. ℝ` whose domain is the set of `x` at which the sequence converges.

## Implementation notes

The definition is a `PFun`: its domain at `x` is the proposition that
`n ↦ (α ^ n)⁻¹ * f (φ^[n] x)` tends to some real number along `Filter.atTop`, and its value
there is `limUnder Filter.atTop` of that sequence, so that `Filter.Tendsto.limUnder_eq`
computes it from any convergence statement.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [Wu] Theorem 2.3 (quasi-homogeneous functions).
-/

@[expose] public section

namespace Faltings

open Filter Topology in
/-- The *Tate limit* of `f : S → ℝ` along `φ : S → S` with ratio `α > 1`: the partial function
`x ↦ lim_{n → ∞} α⁻ⁿ f (φ^[n] x)`, defined exactly at those `x` for which the limit exists. -/
@[faltings "def_nt_tate_limit_function"]
noncomputable def tateLimit {S : Type*} (φ : S → S) (α : ℝ) (_hα : 1 < α) (f : S → ℝ) :
    S →. ℝ := fun x =>
  ⟨∃ L : ℝ, Tendsto (fun n : ℕ => (α ^ n)⁻¹ * f (φ^[n] x)) atTop (𝓝 L),
    fun _ => limUnder atTop (fun n : ℕ => (α ^ n)⁻¹ * f (φ^[n] x))⟩

end Faltings


/-!
# Existence of Tate's limit

Let `S` be a set, `φ : S → S`, `α > 1` real and `f : S → ℝ` such that
`|f (φ x) - α f x| ≤ M` for all `x`. Then the sequence `α⁻ⁿ f (φⁿ x)` converges for every
`x ∈ S`: consecutive terms differ by at most `M α⁻ⁿ⁻¹`, a summable bound, so the sequence is
Cauchy. In other words, the partial function `Faltings.tateLimit φ α hα f` is defined everywhere.

## Main results

* `Faltings.tateLimit_dom`: under the bound `|f (φ x) - α f x| ≤ M`, every `x` lies in the
  domain of `Faltings.tateLimit φ α hα f`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [Wu] Theorem 2.3 (quasi-homogeneous functions).
-/

@[expose] public section

namespace Faltings

open Filter Topology

/-- Consecutive terms of `n ↦ α⁻ⁿ f (φⁿ x)` differ by at most `M α⁻¹ (α⁻¹)ⁿ` when
`|f ∘ φ - α f| ≤ M`: the difference is `α⁻ⁿ⁻¹ (α f y - f (φ y))` with `y = φⁿ x`. -/
private lemma dist_inv_pow_mul_iterate_succ_le {S : Type*} (φ : S → S) {α : ℝ} (hα : 0 < α)
    (f : S → ℝ) {M : ℝ} (hM : ∀ x, |f (φ x) - α * f x| ≤ M) (x : S) (n : ℕ) :
    dist ((α ^ n)⁻¹ * f (φ^[n] x)) ((α ^ (n + 1))⁻¹ * f (φ^[n + 1] x)) ≤
      M * α⁻¹ * α⁻¹ ^ n := by
  have key : (α ^ n)⁻¹ * f (φ^[n] x) - (α ^ (n + 1))⁻¹ * f (φ^[n + 1] x) =
      -((α ^ n)⁻¹ * α⁻¹ * (f (φ (φ^[n] x)) - α * f (φ^[n] x))) := by
    rw [Function.iterate_succ_apply']
    field_simp
    ring
  rw [Real.dist_eq, key, abs_neg, abs_mul, abs_of_pos (by positivity), inv_pow]
  nlinarith [hM (φ^[n] x), show 0 < (α ^ n)⁻¹ * α⁻¹ by positivity]

/-- **Existence of Tate's limit.** If `|f (φ x) - α f x| ≤ M` for all `x`, then the limit
`lim_{n → ∞} α⁻ⁿ f (φ^[n] x)` exists for every `x`, i.e. `x` lies in the domain of
`Faltings.tateLimit φ α hα f`. -/
@[faltings "lem_nt_tate_limit"]
theorem tateLimit_dom {S : Type*} (φ : S → S) (α : ℝ) (hα : 1 < α) (f : S → ℝ) (M : ℝ)
    (hM : ∀ x, |f (φ x) - α * f x| ≤ M) (x : S) :
    x ∈ (tateLimit φ α hα f).Dom :=
  cauchySeq_tendsto_of_complete <| cauchySeq_of_le_geometric α⁻¹ _ (inv_lt_one_of_one_lt₀ hα)
    (dist_inv_pow_mul_iterate_succ_le φ (by linarith) f hM x)

end Faltings


/-!
# Tate's limit is close to `f`

Let `φ : S → S`, `α > 1` and `f : S → ℝ` with `|f (φ x) - α f x| ≤ M` for all `x`. Then the
Tate limit `f̂ x = lim_{n → ∞} α⁻ⁿ f (φ^[n] x)` exists at every `x` and satisfies
`|f̂ x - f x| ≤ M / (α - 1)`: consecutive terms of the sequence differ by at most `M α⁻ⁿ⁻¹`,
and summing this geometric bound from the term `f x` at `n = 0` gives `M α⁻¹ / (1 - α⁻¹)`.

## Main results

* `Faltings.abs_tateLimit_sub_le`: at every `x` the Tate limit `Faltings.tateLimit φ α hα f`
  has a value `y`, and `|y - f x| ≤ M / (α - 1)`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [Wu] Theorem 2.3.
-/

namespace Faltings

/-- If `|f (φ x) - α * f x| ≤ M` for all `x`, then the Tate limit of `f` along `φ` with ratio
`α > 1` is defined at every `x`, and its value differs from `f x` by at most `M / (α - 1)`. -/
@[faltings "lem_nt_tate_limit_bound"]
public theorem abs_tateLimit_sub_le {S : Type*} (φ : S → S) {α : ℝ} (hα : 1 < α) (f : S → ℝ)
    {M : ℝ} (hM : ∀ x, |f (φ x) - α * f x| ≤ M) (x : S) :
    ∃ y ∈ tateLimit φ α hα f x, |y - f x| ≤ M / (α - 1) := by
  obtain ⟨L, hL⟩ := tateLimit_dom φ α hα f M hM x
  refine ⟨L, ⟨⟨L, hL⟩, hL.limUnder_eq⟩, ?_⟩
  have h := dist_le_of_le_geometric_of_tendsto₀ α⁻¹ (M * α⁻¹) (inv_lt_one_of_one_lt₀ hα)
    (dist_inv_pow_mul_iterate_succ_le φ (by linarith) f hM x) hL
  rw [pow_zero, inv_one, one_mul, Function.iterate_zero_apply, dist_comm, Real.dist_eq] at h
  convert h using 1
  field_simp [show α - 1 ≠ 0 by linarith]

end Faltings


/-!
# The functional equation of Tate's limit

Let `S` be a set, `φ : S → S`, `α > 1` and `f : S → ℝ` with `|f (φ x) - α f x| ≤ M` for all
`x`. The Tate limit `f̂ = Faltings.tateLimit φ α hα f` then satisfies `f̂ (φ x) = α f̂ x`:
if `α⁻ⁿ f (φⁿ x) → L`, then `α⁻ⁿ f (φⁿ (φ x)) = α · α⁻⁽ⁿ⁺¹⁾ f (φⁿ⁺¹ x) → α L`, and the limit
exists at every point by `Faltings.tateLimit_dom`.

## Main results

* `Faltings.tateLimit_apply_comp`:
  `tateLimit φ α hα f (φ x) = (tateLimit φ α hα f x).map (α * ·)`.

## Implementation notes

Since `Faltings.tateLimit` is a partial function, the equation is stated as an equality in
`Part ℝ`: it says both that `φ x` lies in the domain exactly when `x` does, and that the values
then agree up to the factor `α`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [Wu] Theorem 2.3.
-/

@[expose] public section

namespace Faltings

open Filter Topology

/-- The Tate limit at `x` is `L` as soon as `α⁻ⁿ f (φⁿ x) → L`. -/
private lemma tateLimit_eq_some_of_tendsto {S : Type*} {φ : S → S} {α : ℝ} {hα : 1 < α}
    {f : S → ℝ} {x : S} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (α ^ n)⁻¹ * f (φ^[n] x)) atTop (𝓝 L)) :
    tateLimit φ α hα f x = Part.some L :=
  Part.eq_some_iff.2 ⟨⟨L, h⟩, h.limUnder_eq⟩

/-- Shifting the starting point by `φ` multiplies the limit of `α⁻ⁿ f (φⁿ x)` by `α`. -/
private lemma tendsto_inv_pow_mul_iterate_apply {S : Type*} {φ : S → S} {α : ℝ} (hα : α ≠ 0)
    {f : S → ℝ} {x : S} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (α ^ n)⁻¹ * f (φ^[n] x)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (α ^ n)⁻¹ * f (φ^[n] (φ x))) atTop (𝓝 (α * L)) :=
  (((tendsto_add_atTop_iff_nat 1).2 h).const_mul α).congr fun n => by
    rw [← Function.iterate_succ_apply, pow_succ]
    field_simp

/-- **Functional equation of Tate's limit.** If `|f (φ x) - α f x| ≤ M` for all `x`, then the
Tate limit `f̂ = tateLimit φ α hα f` satisfies `f̂ (φ x) = α f̂ x`. This is stated as an equality
of partial values: `f̂ (φ x) = (f̂ x).map (α * ·)`. -/
@[faltings "lem_nt_tate_limit_functional"]
theorem tateLimit_apply_comp {S : Type*} (φ : S → S) (α : ℝ) (hα : 1 < α) (f : S → ℝ)
    (M : ℝ) (hM : ∀ x, |f (φ x) - α * f x| ≤ M) (x : S) :
    tateLimit φ α hα f (φ x) = (tateLimit φ α hα f x).map (α * ·) := by
  obtain ⟨L, hL⟩ := tateLimit_dom φ α hα f M hM x
  rw [tateLimit_eq_some_of_tendsto (tendsto_inv_pow_mul_iterate_apply (by positivity) hL),
    tateLimit_eq_some_of_tendsto hL, Part.map_some]

end Faltings
