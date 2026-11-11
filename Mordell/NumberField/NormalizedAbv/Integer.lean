module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mordell.NumberField.NormalizedAbv.Explicit
public import Mordell.NumberField.Place.LocalDegreeSum

/-!
# Integers at finite places

Let `K` be a number field and `w` a finite place of `K`. Every rational integer `r ≥ 1` has
Bombieri's normalized absolute value `|r|_w = Faltings.NumberFieldPlace.normalizedAbv w r` at most
`1`: `r` lies in the ring of integers, so its valuation at the prime of `w` is non-negative.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_inl_intCast_le_one`: `|r|_w ≤ 1` for an integer `r ≥ 1`
  and a finite place `w`.

## References

* [Z. Gao, *Heights*][gao2022], Example 1.1.11.
* [E. Bombieri, W. Gubler, *Heights in Diophantine geometry*][bombieri2006], 1.3.6–1.3.8.
-/

@[expose] public section

namespace Faltings

open NumberField

namespace NumberFieldPlace

/-- At a finite place `w` of a number field `K`, every integer `r ≥ 1` satisfies `|r|_w ≤ 1` for
Bombieri's normalized absolute value `Faltings.NumberFieldPlace.normalizedAbv`: `r` is an algebraic
integer, and an algebraic integer has absolute value at most `1` at every finite place. -/
@[faltings "lem_ht_integer_abs_finite"]
theorem normalizedAbv_inl_intCast_le_one {K : Type*} [Field K] [NumberField K]
    (w : FinitePlace K) {r : ℤ} (hr : 1 ≤ r) :
    normalizedAbv (.inl w : NumberFieldPlace K) (r : K) ≤ 1 := by
  rw [normalizedAbv_inl, ← w.norm_embedding_eq]
  refine Real.rpow_le_one (norm_nonneg _) ?_ (by positivity)
  simpa using FinitePlace.norm_le_one K w.maximalIdeal (r : 𝓞 K)

end NumberFieldPlace

end Faltings

/-!
# Normalized absolute values of integers at infinite places

Let `K` be a number field of degree `D = [K : ℚ]` and `w` an infinite place of `K`, lying over
the infinite place `∞` of `ℚ`, with local degree `n_w = [K_w : ℝ]`. For an integer `r ≥ 1`
the normalized absolute value of `r` at `w` is `|r|_w = r ^ (n_w / D)`, and in particular
`|r|_w ≥ 1`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_natCast_inr`: `|r|_w = r ^ (n_w / D)` and `1 ≤ |r|_w`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Example 1.1.11, Notation 1.1.12.
-/

@[expose] public section

namespace Faltings

open NumberField

/-- For an infinite place `w` of a number field `K`, lying over the infinite place `v` of `ℚ`, and
a natural number `r ≥ 1`, the normalized absolute value is `|r|_w = r ^ (n_w / [K : ℚ])`, where
`n_w = [K_w : ℚ_v]` is `Faltings.NumberFieldPlace.localDegree`; in particular `1 ≤ |r|_w`. -/
@[faltings "lem_ht_integer_abs_infinite"]
theorem NumberFieldPlace.normalizedAbv_natCast_inr {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) (v : InfinitePlace ℚ)
    (h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace ℚ)) {r : ℕ} (hr : 1 ≤ r) :
    NumberFieldPlace.normalizedAbv (.inr w : NumberFieldPlace K) (r : K) =
        (r : ℝ) ^ ((NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace ℚ) h : ℝ) /
          Module.finrank ℚ K) ∧
      1 ≤ NumberFieldPlace.normalizedAbv (.inr w : NumberFieldPlace K) (r : K) := by
  -- `σ r = r` for the embedding `σ` defining `w`, so `|r|_w = ‖σ r‖ ^ (n_w / D) = r ^ (n_w / D)`
  have heq := (NumberFieldPlace.localDegree_inr_eq_mult_and_normalizedAbv_inr_eq w w.embedding
    w.mk_embedding v h).2.2 (r : K)
  rw [map_natCast, Complex.norm_natCast] at heq
  exact ⟨heq, heq ▸ Real.one_le_rpow (by exact_mod_cast hr) (by positivity)⟩

end Faltings

/-!
# The archimedean sum of `log |r|_w`

For a number field `K` and an integer `r ≥ 1`, weighting `log |r|_w` by the archimedean
indicator `ε_w` and summing over all places `w ∈ M_K` gives `log r`: only the infinite places
contribute, and there `∑_{w ∣ ∞} (n_w / [K : ℚ]) log r = log r` since `∑_{w ∣ ∞} n_w = [K : ℚ]`.

## Main results

* `Faltings.NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast`:
  `∑_{w ∈ M_K} ε_w log |r|_w = log r`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

open NumberField

namespace NumberFieldPlace

/-- For a number field `K` and an integer `r ≥ 1`, the sum over all places `w` of `K` of
`ε_w · log |r|_w` equals `log r`, where `ε_w = Faltings.NumberFieldPlace.archimedeanIndicator w`
and `|·|_w = Faltings.NumberFieldPlace.normalizedAbv w`.

The summand vanishes off the places over the infinite place `∞` of `ℚ`; at `w ∣ ∞` it is
`(n_w / [K : ℚ]) log r` by `Faltings.NumberFieldPlace.normalizedAbv_natCast_inr`, and
`∑_{w ∣ ∞} n_w = [K : ℚ]` is `Faltings.NumberFieldPlace.finsum_localDegree_eq_finrank`. -/
@[faltings "lem_ht_normalized_absolute_values_explicit"]
theorem finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast {K : Type*} [Field K]
    [NumberField K] {r : ℤ} (hr : 1 ≤ r) :
    ∑ᶠ w : NumberFieldPlace K, (archimedeanIndicator w : ℝ) * Real.log (normalizedAbv w (r : K)) =
      Real.log r := by
  set v : NumberFieldPlace ℚ := .inr Rat.infinitePlace
  set f : NumberFieldPlace K → ℝ := fun w =>
    (archimedeanIndicator w : ℝ) * Real.log (normalizedAbv w (r : K))
  have hsupp : Function.support f ⊆ {w | w.LiesOver v} := by
    rintro (w | w) hw
    · simp [f] at hw
    · exact ⟨congrArg Subtype.val
        (Subsingleton.elim (w.comap (algebraMap ℚ K)) Rat.infinitePlace)⟩
  have h1 : ∑ᶠ w : NumberFieldPlace K, f w = ∑ᶠ s : {w : NumberFieldPlace K // w.LiesOver v}, f s.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun w => ?_
    by_cases hw : w.LiesOver v
    · rw [finsum_eq_single _ hw (fun h' hne => (hne rfl).elim)]
    · haveI : IsEmpty (w.LiesOver v) := ⟨hw⟩
      rw [finsum_of_isEmpty, Function.notMem_support.1 fun h' => hw (hsupp h')]
  have h2 : ∀ s : {w : NumberFieldPlace K // w.LiesOver v},
      f s.1 = (s.1.localDegree v s.2 : ℝ) * (Real.log r / Module.finrank ℚ K) := by
    rintro ⟨w | w, h⟩
    · exact h.elim
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
      have hn : 1 ≤ n := by omega
      have := (normalizedAbv_natCast_inr w Rat.infinitePlace h (r := n) hn).1
      simp only [f, archimedeanIndicator_inr, Nat.cast_one, one_mul, Int.cast_natCast, this]
      rw [Real.log_rpow (by exact_mod_cast hn)]
      ring
  have hD := finsum_localDegree_eq_finrank (K := K) v
  have hfin : (Function.support fun s : {w : NumberFieldPlace K // w.LiesOver v} =>
      s.1.localDegree v s.2).Finite := by
    by_contra hinf
    rw [finsum_of_infinite_support hinf] at hD
    exact Module.finrank_pos.ne' hD.symm
  have hcast := map_finsum (Nat.castAddMonoidHom ℝ) hfin
  simp only [Nat.coe_castAddMonoidHom] at hcast
  rw [h1, finsum_congr h2, ← finsum_mul, ← hcast, hD, mul_div_left_comm,
    div_self (by exact_mod_cast Module.finrank_pos.ne'), mul_one]

end NumberFieldPlace

end Faltings
