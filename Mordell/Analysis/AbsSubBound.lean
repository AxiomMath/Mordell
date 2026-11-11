module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.GCongr

/-!
# Propagating absolute-value bounds through a scaling

If `a` is within `C` of `r * b` and `b'` is within `C'` of `b`, then `a` is within `C + r * C'`
of `r * b'`, for `r ≥ 0`. This is the bookkeeping step when a height is compared with a scaled
height up to a bounded error.

## Main results

* `Faltings.abs_sub_mul_le_add_mul`: the bound `|a - r * b'| ≤ C + r * C'`.
-/

@[expose] public section

namespace Faltings

/-- If `a` is within `C` of `r * b` and `b'` is within `C'` of `b`, then `a` is within
`C + r * C'` of `r * b'`, for `r ≥ 0`. -/
lemma abs_sub_mul_le_add_mul {a b b' r C C' : ℝ} (hr : 0 ≤ r)
    (h : |a - r * b| ≤ C) (h' : |b' - b| ≤ C') : |a - r * b'| ≤ C + r * C' := by
  calc |a - r * b'| ≤ |a - r * b| + |r * b - r * b'| := abs_sub_le _ _ _
    _ ≤ C + r * C' := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hr, abs_sub_comm b]
      gcongr

end Faltings
