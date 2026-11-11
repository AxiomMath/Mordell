module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Tactic.Abel
public import Mordell.Attr
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The linear parallelogram law

Let `M` be an abelian group and `f : M → N` a map to a torsion-free abelian group with
`f 0 = 0` and `f (x + y) + f (x - y) = 2 • f x` for all `x y`. Then `f` is additive: putting
`x = 0` gives `f (-y) = -f y`, and adding the identity to the one with `x` and `y` exchanged gives
`2 • f (x + y) = 2 • f x + 2 • f y`, which can be halved since `N` has no `2`-torsion.

## Main results

* `Faltings.map_add_of_add_add_sub_eq_two_nsmul`: a map vanishing at `0` and satisfying the
  linear parallelogram law is additive.

## Implementation notes

The source states the result for real-valued `f`; it is stated here for any torsion-free abelian
codomain `N` (`IsAddTorsionFree N`), which covers `ℝ`. Some condition on `N` is needed: for
`M = N = ZMod 2` every map vanishing at `0` satisfies the law. The normalisation `f 0 = 0` is
needed as well, since every constant map satisfies the law.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
-/

@[expose] public section

namespace Faltings

/-- A map vanishing at `0` and satisfying the linear parallelogram law is odd: put `x = 0`. -/
private lemma map_neg_of_add_add_sub_eq_two_nsmul {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] {f : M → N} (h0 : f 0 = 0)
    (h : ∀ x y, f (x + y) + f (x - y) = 2 • f x) (z : M) : f (-z) = -f z :=
  eq_neg_of_add_eq_zero_right <| by simpa [h0] using h 0 z

/-- A map `f` from an abelian group to a torsion-free abelian group with `f 0 = 0` and
`f (x + y) + f (x - y) = 2 • f x` for all `x y` is additive. -/
@[faltings "lem_nt_parallelogram_additive"]
theorem map_add_of_add_add_sub_eq_two_nsmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [IsAddTorsionFree N] {f : M → N} (h0 : f 0 = 0)
    (h : ∀ x y, f (x + y) + f (x - y) = 2 • f x) (x y : M) :
    f (x + y) = f x + f y := by
  have h2 := h y x
  rw [add_comm y x, ← neg_sub x y, map_neg_of_add_add_sub_eq_two_nsmul h0 h] at h2
  refine eq_of_nsmul_eq_nsmul_of_addCommute two_ne_zero (AddCommute.all _ _) ?_
  change 2 • f (x + y) = 2 • (f x + f y)
  rw [nsmul_add, ← h x y, ← h2]
  abel

end Faltings


/-!
# The parallelogram law, quadratic case

Let `M` be an abelian group and `q : M → N` a map to a torsion-free abelian group satisfying the
parallelogram law `q (x + y) + q (x - y) = 2 • q x + 2 • q y`. Then the polar form
`QuadraticMap.polar q x y = q (x + y) - q x - q y` is symmetric and additive in each variable.

## Main results

* `Faltings.polar_comm_and_add_of_add_add_sub_eq_two_nsmul`: the polar form of a map satisfying
  the parallelogram law is symmetric and biadditive.

## Implementation notes

The source takes `q` real-valued; the statement is given for any torsion-free abelian codomain
`N` (`IsAddTorsionFree N`), which covers `ℝ`, where `2 • a = 2 * a`. Some condition on `N` is
needed: for `M = N = ZMod 2` every map satisfies the law, and its polar form need not be
biadditive. Biadditivity is stated as additivity in the left and in the right variable, the form
of `QuadraticMap.polar_add_left` and `QuadraticMap.polar_add_right`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
-/

@[expose] public section

namespace Faltings

section

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {q : M → N}

/-- A map to a torsion-free group satisfying the parallelogram law vanishes at `0`. -/
private lemma map_zero_of_parallelogram [IsAddTorsionFree N]
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) : q 0 = 0 :=
  eq_of_nsmul_eq_nsmul_of_addCommute two_ne_zero (AddCommute.all _ _) <| by
    simpa [two_nsmul] using h 0 0

/-- The parallelogram law for `q` gives the linear-case relation for `polar q · z`. -/
private lemma polar_add_add_polar_sub
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) (z x y : M) :
    QuadraticMap.polar q (x + y) z + QuadraticMap.polar q (x - y) z =
      2 • QuadraticMap.polar q x z := by
  have h1 := h (x + z) y
  have h2 := h x y
  rw [show x + z + y = x + y + z by abel, show x + z - y = x - y + z by abel] at h1
  simp only [QuadraticMap.polar, nsmul_sub, two_nsmul] at *
  rw [← sub_eq_zero]
  calc _ = (q (x + y + z) + q (x - y + z)) - (q (x + y) + q (x - y)) - (q z + q z)
        - (q (x + z) + q (x + z)) + (q x + q x) + (q z + q z) := by abel
    _ = 0 := by rw [h1, h2]; abel

/-- The polar form of a map satisfying the parallelogram law is additive on the left. -/
private lemma polar_add_left_of_parallelogram [IsAddTorsionFree N]
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) (x x' z : M) :
    QuadraticMap.polar q (x + x') z =
      QuadraticMap.polar q x z + QuadraticMap.polar q x' z :=
  map_add_of_add_add_sub_eq_two_nsmul (f := (QuadraticMap.polar q · z))
    (by simp [QuadraticMap.polar, map_zero_of_parallelogram h]) (polar_add_add_polar_sub h z) x x'

end

/-- If `q : M → N`, with `N` torsion-free, satisfies the parallelogram law
`q (x + y) + q (x - y) = 2 • q x + 2 • q y`, then its polar form `QuadraticMap.polar q` is
symmetric and additive in each variable. -/
@[faltings "lem_nt_parallelogram_quadratic"]
theorem polar_comm_and_add_of_add_add_sub_eq_two_nsmul {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [IsAddTorsionFree N] {q : M → N}
    (h : ∀ x y, q (x + y) + q (x - y) = 2 • q x + 2 • q y) :
    (∀ x y, QuadraticMap.polar q x y = QuadraticMap.polar q y x) ∧
    (∀ x x' y, QuadraticMap.polar q (x + x') y =
      QuadraticMap.polar q x y + QuadraticMap.polar q x' y) ∧
    (∀ x y y', QuadraticMap.polar q x (y + y') =
      QuadraticMap.polar q x y + QuadraticMap.polar q x y') :=
  ⟨QuadraticMap.polar_comm _, polar_add_left_of_parallelogram h, fun x y y' => by
    simp only [QuadraticMap.polar_comm _ x, polar_add_left_of_parallelogram h]⟩

end Faltings
