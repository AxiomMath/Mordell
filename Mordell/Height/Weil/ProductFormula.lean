module

public import Mordell.Height.Weil.LocalHeight
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue

/-!
# The sum of the local heights is independent of the representative

Let `K` be a number field, `x ∈ K^{n+1} \ {0}` and `λ ∈ Kˣ`. Then `S_K(λx) = S_K(x)`: by
multiplicativity `h_w(λx) = log |λ|_w + h_w(x)`, and `∑_w log |λ|_w = 0` by the product formula.
Hence `S_K` descends to projective space.

## Main results

* `Faltings.finsum_log_normalizedAbv`: the product formula in additive form,
  `∑_w log |c|_w = 0` for `c ≠ 0`, with its finiteness side condition
  `Faltings.finite_support_log_normalizedAbv`.
* `Faltings.sumLocalHeight_smul`: `S_K(λ • x) = S_K(x)` for `λ ≠ 0` and `x ≠ 0`.

## Implementation notes

The vector is indexed by an arbitrary finite type `ι` instead of `Fin (n + 1)`, and the scalar
is given as `c : K` with `c ≠ 0` rather than as a unit.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Lemma 1.2.3.
-/

@[expose] public section

namespace Faltings

open NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/-- `h_w(c x) = log |c|_w + h_w(x)`. -/
private lemma localHeight_smul {ι : Type*} [Finite ι] (w : NumberFieldPlace K) {x : ι → K}
    (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    w.localHeight (c • x) = Real.log (w.normalizedAbv c) + w.localHeight x := by
  have hpos : 0 < w.vectorAbv x := w.vectorAbv_pos hx
  have : w.vectorAbv (c • x) = w.normalizedAbv c * w.vectorAbv x := by
    simp only [NumberFieldPlace.vectorAbv, Pi.smul_apply, smul_eq_mul,
      NumberFieldPlace.normalizedAbv_mul]
    exact (Real.mul_iSup_of_nonneg (NumberFieldPlace.normalizedAbv_nonneg w c) _).symm
  rw [NumberFieldPlace.localHeight, NumberFieldPlace.localHeight, this,
    Real.log_mul (w.normalizedAbv_pos hc).ne' hpos.ne']

/-- A `finsum` over a sum type with finite support splits into the two summands. -/
private lemma finsum_sum_elim {α β M : Type*} [AddCommMonoid M] {f : α ⊕ β → M}
    (hf : (Function.support f).Finite) :
    ∑ᶠ i, f i = ∑ᶠ a, f (.inl a) + ∑ᶠ b, f (.inr b) := by
  rw [← finsum_mem_univ, ← Set.range_inl_union_range_inr,
    finsum_mem_union' Set.isCompl_range_inl_range_inr.disjoint (hf.inter_of_right _)
      (hf.inter_of_right _), finsum_mem_range Sum.inl_injective,
    finsum_mem_range Sum.inr_injective]

/-- `log |c|_w = 0` for all but finitely many places `w`, when `c ≠ 0`. -/
theorem finite_support_log_normalizedAbv {c : K} (hc : c ≠ 0) :
    (Function.support fun w : NumberFieldPlace K => Real.log (w.normalizedAbv c)).Finite := by
  refine (((FinitePlace.hasFiniteMulSupport hc).image Sum.inl).union
    (Set.finite_range Sum.inr)).subset ?_
  rintro (w | w) hw
  · refine Or.inl ⟨w, ?_, rfl⟩
    by_contra hwS
    simp only [Function.mem_mulSupport, not_not] at hwS
    exact hw (by simp [hwS])
  · exact Or.inr ⟨w, rfl⟩

/-- The product formula, in additive form: `∑_w log |c|_w = 0` for `c ≠ 0`. -/
theorem finsum_log_normalizedAbv {c : K} (hc : c ≠ 0) :
    ∑ᶠ w : NumberFieldPlace K, Real.log (w.normalizedAbv c) = 0 := by
  have hfin : ∀ w : FinitePlace K, 0 < w c := fun w => FinitePlace.pos_iff.2 hc
  have hinf : ∀ w : InfinitePlace K, 0 < w c := fun w => InfinitePlace.pos_iff.2 hc
  rw [finsum_sum_elim (finite_support_log_normalizedAbv hc)]
  simp only [NumberFieldPlace.normalizedAbv_inl, NumberFieldPlace.normalizedAbv_inr]
  simp_rw [Real.log_rpow (hfin _), Real.log_rpow (pow_pos (hinf _) _)]
  rw [← mul_finsum, ← mul_finsum, ← mul_add, ← Real.log_finprod hfin, finsum_eq_sum_of_fintype,
    ← Real.log_prod fun w _ => (pow_pos (hinf w) _).ne', ← Real.log_mul,
    mul_comm (∏ᶠ w : FinitePlace K, w c), prod_abs_eq_one hc, Real.log_one, mul_zero]
  · exact (finprod_induction (0 < ·) one_pos (fun _ _ => mul_pos) hfin).ne'
  · exact (Finset.prod_pos fun w _ => pow_pos (hinf w) _).ne'

end

/-- The sum of the local heights `Faltings.sumLocalHeight` of a nonzero vector `x : ι → K` over a
number field `K` is unchanged by scaling `x` by a nonzero `c : K`. -/
@[faltings "lem_ht_height_independent"]
public theorem sumLocalHeight_smul {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
    {x : ι → K} (hx : x ≠ 0) {c : K} (hc : c ≠ 0) :
    sumLocalHeight (c • x) = sumLocalHeight x := by
  simp_rw [sumLocalHeight, localHeight_smul _ hx hc]
  rw [finsum_add_distrib (finite_support_log_normalizedAbv hc)
    (NumberFieldPlace.finite_support_localHeight hx), finsum_log_normalizedAbv hc, zero_add]

end Faltings
