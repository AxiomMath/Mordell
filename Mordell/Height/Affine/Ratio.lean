module
public import Mathlib
public import Mordell.Attr

/-!
# The height of a ratio of coordinates

Let `x = (x_i)_{i ∈ ι}` be a vector of elements of a field `K` with a family of admissible
absolute values (for instance a number field), and suppose `x_j ≠ 0`. Then the height of the
ratio `x_ν / x_j` is at most the height of `x`, for every index `ν`: the ratio has the height
of the point `(x_ν : x_j)` of `ℙ¹`, whose coordinates are a sub-vector of those of `x`.

## Main results

* `Faltings.logHeight₁_div_le_logHeight`: `h(x_ν / x_j) ≤ h(x)`.

## Implementation notes

The point of projective space is given by a representative `x : ι → K` with `x_j ≠ 0`; since
`Height.logHeight` is invariant under scaling by a nonzero constant
(`Height.logHeight_smul_eq_logHeight`), this is the same as the statement for the point
`Projectivization.mk K x _`, whose height is `Projectivization.logHeight`. The field is any field
with `Height.AdmissibleAbsValues`, which contains the case of a number field `K ⊆ k̄`; the
normalisation of the absolute values scales both sides by the same positive factor.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, p. 628
-/

namespace Faltings

open Height

/-- For a vector `x` of coordinates with `x j ≠ 0`, the height of the ratio `x ν / x j` is at
most the height of `x`: it is the height of `(x ν : x j)`, a sub-vector of `x`. -/
@[faltings "lem_bvs_ratio_height"]
public theorem logHeight₁_div_le_logHeight {K : Type*} [Field K] [AdmissibleAbsValues K]
    {ι : Type*} [Finite ι] (x : ι → K) {j : ι} (hj : x j ≠ 0) (ν : ι) :
    logHeight₁ (x ν / x j) ≤ logHeight x := by
  rw [logHeight₁_div_eq_logHeight]
  convert logHeight_comp_le ![ν, j] x using 2
  ext i; fin_cases i <;> rfl

end Faltings
