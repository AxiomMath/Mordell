module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mathlib
public import Mordell.Attr
public import Mordell.NumberField.Place.LocalDegree

/-!
# Normalized absolute values at a finite place

Let `K` be a number field of degree `D = [K : ℚ]` and `w` a finite place of `K`, with prime
`𝔭 = NumberField.FinitePlace.maximalIdeal w` of `𝓞 K`. For `x ∈ Kˣ`, Bombieri's normalized
absolute value is `|x|_w = N(𝔭) ^ (-ord_𝔭(x) / D)`, where
`N(𝔭) = Ideal.absNorm 𝔭 = #(𝓞 K ⧸ 𝔭)` and `ord_𝔭(x)` is the exponent of `𝔭` in the
factorization of the principal fractional ideal `(x)`, i.e.
`FractionalIdeal.count K 𝔭 (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_inl_eq_absNorm_rpow`: the explicit formula.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

open NumberField nonZeroDivisors IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace NumberFieldPlace

/-- The `v`-adic valuation of a nonzero `x` is `exp (-count K v (x))`. -/
private lemma valuation_eq_exp_neg_count {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
    {x : K} (hx : x ≠ 0) :
    v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  have hn : n ≠ 0 := by rintro rfl; simp at hx
  have hI : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) d)⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx) hI,
    valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), ← WithZero.exp_sub, neg_sub,
    neg_sub_neg]

/-- A finite place of a number field takes the value `N(𝔭) ^ (-ord_𝔭 x)` at a nonzero `x`. -/
private lemma finitePlace_apply_eq_absNorm_zpow {K : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) {x : K} (hx : x ≠ 0) :
    w x = (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
      (-FractionalIdeal.count K w.maximalIdeal (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding',
    valuation_eq_exp_neg_count _ hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  rfl

/-- At a finite place `w` of a number field `K`, with prime `𝔭 = w.maximalIdeal`, Bombieri's
normalized absolute value of `x ≠ 0` is `N(𝔭) ^ (-ord_𝔭(x) / [K : ℚ])`, where `N(𝔭)` is
`Ideal.absNorm 𝔭` and `ord_𝔭(x)` is the multiplicity of `𝔭` in the fractional ideal `(x)`. -/
@[faltings "lem_ht_abs_finite_explicit"]
theorem normalizedAbv_inl_eq_absNorm_rpow {K : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) {x : K} (hx : x ≠ 0) :
    normalizedAbv (.inl w : NumberFieldPlace K) x =
      (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
        (-(FractionalIdeal.count K w.maximalIdeal
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℝ) / Module.finrank ℚ K) := by
  rw [normalizedAbv_inl, finitePlace_apply_eq_absNorm_zpow w hx, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _), div_eq_mul_inv]
  push_cast
  rfl

end NumberFieldPlace

end Faltings

/-!
# Normalized absolute values at an infinite place

Let `K` be a number field of degree `D = [K : ℚ]` and `w` an infinite place of `K` defined by an
embedding `σ : K → ℂ`. The local degree `n_w = [K_w : ℝ]` of `w` over the infinite place of `ℚ`
is `NumberField.InfinitePlace.mult w`, so it is `1` or `2`, and Bombieri's normalized absolute
value is `|x|_w = |σ x| ^ (n_w / D)`.

## Main results

* `Faltings.NumberFieldPlace.localDegree_inr_eq_mult_and_normalizedAbv_inr_eq`:
  `n_w = mult w ∈ {1, 2}` and `|x|_w = ‖σ x‖ ^ (n_w / D)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

namespace NumberFieldPlace

open NumberField

/-- At an infinite place `w` of a number field `K` defined by an embedding `σ : K →+* ℂ`, the
local degree `n_w` of `w` over the infinite place `v` of `ℚ` is
`NumberField.InfinitePlace.mult w`, hence `1` or `2`, and the normalized absolute value is
`|x|_w = ‖σ x‖ ^ (n_w / [K : ℚ])`. -/
@[faltings "lem_ht_abs_infinite_explicit"]
theorem localDegree_inr_eq_mult_and_normalizedAbv_inr_eq {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) (σ : K →+* ℂ) (hσ : InfinitePlace.mk σ = w) (v : InfinitePlace ℚ)
    (h : w.LiesOver v) :
    let n_w :=
      NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace ℚ) h
    n_w = w.mult ∧ n_w ∈ ({1, 2} : Set ℕ) ∧
      ∀ x : K, normalizedAbv (.inr w) x = ‖σ x‖ ^ ((n_w : ℝ) / Module.finrank ℚ K) := by
  intro n_w
  have hn : n_w = w.mult := by
    have hv : v.mult = 1 := by
      simp [Subsingleton.elim v Rat.infinitePlace, InfinitePlace.mult, Rat.isReal_infinitePlace]
    exact (one_mul _).symm.trans (hv ▸ InfinitePlace.mult_mul_finrank v w)
  refine ⟨hn, ?_, fun x => ?_⟩
  · rw [hn, InfinitePlace.mult]
    split_ifs <;> simp
  · rw [normalizedAbv_inr, hn, ← hσ, InfinitePlace.apply, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _), div_eq_mul_inv]

end NumberFieldPlace

end Faltings
