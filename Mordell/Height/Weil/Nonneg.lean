module

public import Mordell.Height.Weil.PointField
public import Mordell.Height.Weil.Representative

/-!
# Nonnegativity of the Weil height on projective space

The absolute logarithmic Weil height of a point of projective space over an algebraic
extension of `ℚ` is nonnegative: normalizing a coordinate to `1`, every local term
`max_j log |x̃_j|_v` is at least `log 1 = 0`.

## Main results

* `Faltings.weilHeight_nonneg`: `0 ≤ Faltings.weilHeight x`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- The local height of a vector with a coordinate equal to `1` is nonnegative. -/
private theorem localHeight_nonneg_of_eq_one {F : Type*} [Field F] [NumberField F]
    {ι : Type*} [Finite ι] (w : NumberFieldPlace F) {v : ι → F} {j : ι} (hj : v j = 1) :
    0 ≤ w.localHeight v :=
  Real.log_nonneg <| le_ciSup_of_le (Set.finite_range _).bddAbove j (by cases w <;> simp [hj])

/-- The absolute logarithmic Weil height `Faltings.weilHeight x` of a point `x` of
`ℙ K (ι → K)`, for `K / ℚ` algebraic, is nonnegative: computing it from a representative with a
coordinate equal to `1`, every local height is nonnegative. -/
@[faltings "lem_ht_height_nonneg"]
theorem weilHeight_nonneg {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {ι : Type*} [Fintype ι] [LinearOrder ι] (x : ℙ K (ι → K)) : 0 ≤ weilHeight x := by
  have hfin : FiniteDimensional ℚ (pointField ℚ x) := by
    have : Finite {r : K | ∃ i j, x.rep j ≠ 0 ∧ r = x.rep i / x.rep j} :=
      ((Set.finite_range fun p : ι × ι => x.rep p.1 / x.rep p.2).subset
        (by rintro r ⟨i, j, -, rfl⟩; exact ⟨(i, j), rfl⟩)).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  letI : NumberField (pointField ℚ x) :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  obtain ⟨v, j, hv, hj, hx⟩ := exists_coords_fieldOfDefinition_eq_one ℚ x
  rw [weilHeight_eq_sumLocalHeight (F := pointField ℚ x) hv hx]
  exact finsum_nonneg fun w => localHeight_nonneg_of_eq_one w hj

end Faltings
