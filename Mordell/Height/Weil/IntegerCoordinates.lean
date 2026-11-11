module

public import Mordell.Height.Weil.Representative

/-!
# Height of a point with coprime integer coordinates

If a point `x = (x_0 : ⋯ : x_n)` of projective space over an algebraic extension of `ℚ` has
coordinates `x_j ∈ ℤ` with `gcd(x_0, …, x_n) = 1`, then its absolute logarithmic Weil height is
`h(x) = log max_j |x_j|`: at every prime `p` the local term `max_j log |x_j|_p` vanishes, since the
`x_j` are integers not all divisible by `p`, and the archimedean place contributes
`log max_j |x_j|`.

## Main results

* `Faltings.weilHeight_eq_log_max_abs_of_gcd_eq_one`: for `x : ι → ℤ` with
  `Finset.univ.gcd x = 1`, `Faltings.weilHeight [x] = Real.log (⨆ i, |x i|)`.

## References

* [Z. Gao, *Heights*][gao2022], formula (1.2.1).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization
open NumberField

namespace Faltings

/-- If `x : ι → ℤ` has coprime entries, `Finset.univ.gcd x = 1`, then the absolute logarithmic
Weil height of the point `[x] ∈ ℙ K (ι → K)`, for `K / ℚ` algebraic, is `log max_i |x i|`.
The height is computed over `ℚ`, where it is Mathlib's logarithmic height
`Height.logHeight`, given by `Rat.logHeight_eq_max_abs_of_gcd_eq_one`. -/
@[faltings "lem_ht_height_integer_coords"]
theorem weilHeight_eq_log_max_abs_of_gcd_eq_one {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι] [LinearOrder ι] (x : ι → ℤ)
    (hx : Finset.univ.gcd x = 1) (hx₀ : (fun i => (x i : K)) ≠ 0) :
    weilHeight (Projectivization.mk K (fun i => (x i : K)) hx₀) = Real.log ↑(⨆ i, |x i|) := by
  have : Nonempty ι := not_isEmpty_iff.1 fun h => hx₀ (funext h.elim)
  have hy : algebraMap ℚ K ∘ (fun i => (x i : ℚ)) ≠ 0 := by simpa [Function.comp_def] using hx₀
  have ha : (fun i => (x i : ℚ)) ≠ 0 := fun h => hy (by rw [h]; ext; simp)
  rw [weilHeight_eq_sumLocalHeight hy (by congr 1; simp [Function.comp_def]),
    BombieriVojta.HeightLowerBound.sumLocalHeight_eq_logHeight ha, Module.finrank_self,
    Nat.cast_one, div_one]
  exact Rat.logHeight_eq_max_abs_of_gcd_eq_one hx

end Faltings
