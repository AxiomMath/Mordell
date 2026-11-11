module
public import Mathlib

/-!
# Heights of finitely supported families

For a finitely supported family `x : α →₀ K`, Mathlib's `Finsupp.mulHeight x` is the height of
the restriction of `x` to its support. This file identifies it with the tuple height
`Height.mulHeight ⇑x` of `x` over its whole, possibly infinite, index type, and records that
these heights are at least `1`.

## Main results

* `Faltings.mulHeight_finsupp_eq`: `Height.mulHeight ⇑x = Finsupp.mulHeight x`.
* `Faltings.one_le_finsuppMulHeight`: `1 ≤ Finsupp.mulHeight x`.
* `Faltings.zero_le_finsuppLogHeight`: `0 ≤ Finsupp.logHeight x`.

## Implementation notes

`Finsupp.logHeight x` unfolds to `Real.log (Height.mulHeight ⇑x)`, a height over the index type
`α`, which need not be finite; `Faltings.mulHeight_finsupp_eq` moves it to the finite support.
-/

namespace Faltings

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α : Type*}

/-- The height of a finitely supported family is at least `1`. -/
public lemma one_le_finsuppMulHeight (x : α →₀ K) : 1 ≤ Finsupp.mulHeight x :=
  one_le_mulHeight (fun j : x.support => x j)

/-- The tuple height of a finitely supported family over its whole (possibly infinite) index
type is the height of its restriction to the support, `Finsupp.mulHeight`. -/
public lemma mulHeight_finsupp_eq (x : α →₀ K) : mulHeight ⇑x = Finsupp.mulHeight x := by
  by_cases hx : (⇑x) = 0
  · have : (fun i : x.support => x i) = 0 := funext fun i => by simp [hx]
    rw [Finsupp.mulHeight, this, hx, mulHeight_zero, mulHeight_zero]
  have hx' : (fun i : x.support => x i) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Function.ne_iff.mpr ⟨⟨i, Finsupp.mem_support_iff.mpr hi⟩, hi⟩
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x i) = ⨆ i : x.support, v (x i) := by
    have : Nonempty x.support := (Function.ne_iff.mp hx').nonempty
    have : Nonempty α := (Function.ne_iff.mp hx).nonempty
    have hle (i : α) : v (x i) ≤ ⨆ i : x.support, v (x i) := by
      by_cases hi : i ∈ x.support
      · exact le_ciSup (f := fun j : x.support => v (x j)) (Set.finite_range _).bddAbove ⟨i, hi⟩
      · rw [Finsupp.notMem_support_iff.mp hi, map_zero]
        exact Real.iSup_nonneg_of_nonnegHomClass v _
    exact le_antisymm (ciSup_le hle)
      (ciSup_le fun i => le_ciSup (f := fun i => v (x i)) ⟨_, Set.forall_mem_range.2 hle⟩ i.1)
  rw [Finsupp.mulHeight, mulHeight_eq hx, mulHeight_eq hx']
  simp only [H]

/-- `Finsupp.logHeight` is nonnegative. -/
public lemma zero_le_finsuppLogHeight (x : α →₀ K) : 0 ≤ Finsupp.logHeight x :=
  Real.log_nonneg (mulHeight_finsupp_eq x ▸ one_le_finsuppMulHeight x)

end Faltings
