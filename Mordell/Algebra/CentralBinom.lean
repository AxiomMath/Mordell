module
public import Mathlib
public import Mordell.Attr

/-!
# A central binomial estimate

For every natural number `D`, the middle binomial coefficient `D.choose (D / 2)` satisfies
`D.choose (D / 2) * √(D + 1) ≤ 2 ^ D`. This sharpens the trivial bound
`Nat.choose_le_two_pow` by the factor `√(D + 1)`. It follows from the inequality
`(2 * n).choose n ≤ 4 ^ n / √(3 * n + 1)`, proved by induction on `n`, treating the cases
`D = 2 * n` and `D = 2 * n + 1` separately.

## Main results

* `Faltings.choose_div_two_mul_sqrt_succ_le_two_pow`:
  `D.choose (D / 2) * √(D + 1) ≤ 2 ^ D`.

## References

* [S. Gao, *Lecture notes on the Mordell conjecture*][gao2022], proof of Lemma 1.3.6.
-/

namespace Faltings

/-- Squared form of `(2 * n).choose n ≤ 4 ^ n / √(3 * n + 1)`, by induction on `n` through
`(n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n`. -/
private theorem centralBinom_sq_mul_le (n : ℕ) :
    n.centralBinom ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := congrArg (· ^ 2) (Nat.succ_mul_centralBinom_succ n)
    simp only [mul_pow] at hrec
    refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < (n + 1) ^ 2)
    calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (3 * (n + 1) + 1))
        = 4 * (2 * n + 1) ^ 2 * (3 * n + 4) * n.centralBinom ^ 2 := by
          rw [← mul_assoc, hrec]; ring
      _ ≤ 16 * (n + 1) ^ 2 * (3 * n + 1) * n.centralBinom ^ 2 :=
          Nat.mul_le_mul_right _ (by ring_nf; omega)
      _ = 16 * (n + 1) ^ 2 * (n.centralBinom ^ 2 * (3 * n + 1)) := by ring
      _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring

/-- Squared form of `D.choose (D / 2) * √(D + 1) ≤ 2 ^ D`; the odd case uses
`centralBinom (n + 1) = 2 * (2 * n + 1).choose n`. -/
private theorem choose_div_two_sq_mul_le (D : ℕ) : D.choose (D / 2) ^ 2 * (D + 1) ≤ 4 ^ D := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' D
  · rw [Nat.mul_div_cancel_left n two_pos, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    exact (Nat.mul_le_mul_left _ (by omega)).trans (centralBinom_sq_mul_le n)
  · have hc : (n + 1).centralBinom = 2 * (2 * n + 1).choose n := by
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.mul_succ, Nat.choose_succ_succ,
        ← Nat.choose_symm_half]
      ring
    have h := centralBinom_sq_mul_le (n + 1)
    rw [hc, pow_succ 16 n] at h
    rw [show 4 ^ (2 * n + 1) = 4 * 16 ^ n by rw [pow_succ, pow_mul]; ring,
      show (2 * n + 1) / 2 = n by omega]
    nlinarith

/-- For every natural number `D`, `D.choose (D / 2) * √(D + 1) ≤ 2 ^ D`. -/
@[faltings "lem_ht_central_binomial"]
public theorem choose_div_two_mul_sqrt_succ_le_two_pow (D : ℕ) :
    (D.choose (D / 2) : ℝ) * Real.sqrt (D + 1) ≤ 2 ^ D := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm D 2, pow_mul]
  exact_mod_cast choose_div_two_sq_mul_le D

end Faltings


/-!
# Central binomial coefficients are supermultiplicative

For natural numbers `a` and `b`, the middle binomial coefficients satisfy
`(a choose ⌊a/2⌋) * (b choose ⌊b/2⌋) ≤ (a + b) choose ⌊(a + b)/2⌋`.
Here `n choose ⌊n/2⌋` is the largest coefficient in row `n` of Pascal's triangle, for every `n`,
odd or even. (Mathlib's `Nat.centralBinom n` is the even-row case `(2 * n).choose n`.)

## Main results

* `Faltings.choose_div_two_mul_choose_div_two_le`: the middle binomial coefficients are
  supermultiplicative.

## References

* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006]
-/

namespace Faltings

/-- One term of Vandermonde's identity
`(a + b).choose k = ∑_{i + j = k} a.choose i * b.choose j` is at most the sum. -/
private theorem choose_mul_choose_le_add_choose (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun _ _ => Nat.zero_le _) (Finset.HasAntidiagonal.mem_antidiagonal (a := (i, j)).mpr rfl)

/-- The middle binomial coefficients `n.choose (n / 2)` are supermultiplicative:
`a.choose (a / 2) * b.choose (b / 2) ≤ (a + b).choose ((a + b) / 2)`. -/
@[faltings "lem_ht_central_binomial_supermultiplicative"]
public theorem choose_div_two_mul_choose_div_two_le (a b : ℕ) :
    a.choose (a / 2) * b.choose (b / 2) ≤ (a + b).choose ((a + b) / 2) :=
  (choose_mul_choose_le_add_choose a b _ _).trans (Nat.choose_le_middle _ _)

end Faltings
