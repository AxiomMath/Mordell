module

public import Mathlib
public import Mordell.Attr

/-!
# A quadratic function is half its polar form on the diagonal

Let `M` be an abelian group and `q : M → N` a function satisfying the parallelogram law
`q (x + y) + q (x - y) = 2 q x + 2 q y`. Taking `x = y = 0` gives `q 0 = 0` (when `N` has no
`2`-torsion), and taking `y = x` gives `q (2 x) = 4 q x`. Hence the polar form satisfies
`QuadraticMap.polar q x x = q (2 x) - 2 q x = 2 q x`, that is `q x = ½ · polar q x x` when
`N = ℝ`. This is the analogue, for functions satisfying the parallelogram law, of Mathlib's
`QuadraticMap.polar_self`.

## Main results

* `Faltings.polar_self_of_add_add_sub_eq`: `QuadraticMap.polar q x x = 2 • q x`.

## Implementation notes

The codomain is a torsion-free additive commutative group `N` rather than `ℝ`, and the
conclusion is written without division, as `polar q x x = 2 • q x`, in the shape of
`QuadraticMap.polar_self`. For `N = ℝ` this is equivalent to `q x = ½ · polar q x x`.
Torsion-freeness is what makes `q 0 = 0` follow from the law: on `N = ZMod 2` the constant
function `1` satisfies the law but `polar 1 x x = 1 ≠ 0 = 2 • 1`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*.
-/

@[expose] public section

namespace Faltings

/-- The parallelogram law at `x = y = 0` reads `2 • q 0 = 4 • q 0`, so `q 0 = 0` when the
codomain is torsion-free. -/
private lemma map_zero_of_add_add_sub_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [IsAddTorsionFree N] {q : M → N}
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) : q 0 = 0 := by
  have h00 := h 0 0
  rw [add_zero, sub_zero, ← two_nsmul, left_eq_add] at h00
  exact (nsmul_eq_zero_iff_right two_ne_zero).1 h00

/-- A function satisfying the parallelogram law `q (x + y) + q (x - y) = 2 q x + 2 q y`,
with values in a torsion-free abelian group, is half its polar form on the diagonal:
`QuadraticMap.polar q x x = 2 • q x`. -/
@[faltings "lem_nt_polar_form_diagonal"]
theorem polar_self_of_add_add_sub_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [IsAddTorsionFree N] {q : M → N}
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) (x : M) :
    QuadraticMap.polar q x x = 2 • q x := by
  have hx := h x x
  rw [sub_self, map_zero_of_add_add_sub_eq h, add_zero] at hx
  rw [QuadraticMap.polar, hx]
  abel

end Faltings
