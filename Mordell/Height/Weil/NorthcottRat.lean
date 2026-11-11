module

public import Mordell.Height.Weil.IntegerCoordinates

/-!
# Northcott's theorem over `ℚ`

For every real `B`, there are only finitely many points `x` of the projective space `ℙⁿ(ℚ)`
whose absolute logarithmic Weil height `h(x)` is at most `B`. Writing `x` with coprime integer
coordinates, `h(x) ≤ B` bounds every coordinate by `e^B`, which leaves finitely many choices.

## Main results

* `Faltings.finite_setOf_weilHeight_le_rat`: for a finite linearly ordered index type `ι` and
  any `B : ℝ`, the set `{x : ℙ ℚ (ι → ℚ) | Faltings.weilHeight x ≤ B}` is finite.

## Implementation notes

The coordinates are indexed by an arbitrary finite linearly ordered type `ι`; `ι = Fin (n + 1)`
is `ℙⁿ(ℚ)`. The bound `B` is any real number: for `B < 0` the statement is still true (the
height is nonnegative, so the set is empty) and no sign condition is needed. Compare
`NumberField.finite_setOfPred_logHeight₁_le`, the case of the affine line over a fixed number
field.

## References

* [Z. Gao, *Heights*][gao2022], proof of Thm. 1.2.5.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- Every point of `ℙ ℚ (ι → ℚ)` has a representative with coprime integer coordinates. -/
private lemma exists_primitive_rep {ι : Type*} [Fintype ι] (x : ℙ ℚ (ι → ℚ)) :
    ∃ (u : ι → ℤ) (hu : (fun i => (u i : ℚ)) ≠ 0),
      Finset.univ.gcd u = 1 ∧ x = Projectivization.mk ℚ (fun i => (u i : ℚ)) hu := by
  classical
  have : Nonempty ι := not_isEmpty_iff.1 fun h => x.rep_nonzero (funext h.elim)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x.rep
  choose w hw using hb
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hw' : (fun i => (w i : ℚ)) = ((b : ℤ) : ℚ) • x.rep := funext fun i => by
    simpa [zsmul_eq_mul] using hw i
  obtain ⟨u, hu, hgcd⟩ := Finset.extract_gcd w Finset.univ_nonempty
  have hg0 : ((Finset.univ.gcd w : ℤ) : ℚ) ≠ 0 := by
    refine Int.cast_ne_zero.2 fun h => smul_ne_zero hb0 x.rep_nonzero ?_
    rw [← hw']; funext i; simp [Finset.gcd_eq_zero_iff.1 h i (Finset.mem_univ i)]
  have hu' : (fun i => (u i : ℚ)) = (((b : ℤ) : ℚ) / Finset.univ.gcd w) • x.rep := by
    rw [div_eq_inv_mul, mul_smul, ← hw']; funext i
    simp [hu i (Finset.mem_univ i), hg0]
  have hu0 : (fun i => (u i : ℚ)) ≠ 0 := hu' ▸ smul_ne_zero (div_ne_zero hb0 hg0) x.rep_nonzero
  refine ⟨u, hu0, hgcd, ?_⟩
  conv_lhs => rw [← x.mk_rep]
  exact ((Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).2 ⟨_, hu'.symm⟩).symm

/-- A point with coprime integer coordinates `u` and height at most `B` has
`|u i| ≤ ⌊exp B⌋` for every `i`. -/
private lemma abs_le_floor_exp_of_weilHeight_le {ι : Type*} [Fintype ι] [LinearOrder ι]
    {B : ℝ} (u : ι → ℤ) (hgcd : Finset.univ.gcd u = 1) (hu : (fun i => (u i : ℚ)) ≠ 0)
    (hB : weilHeight (Projectivization.mk ℚ (fun i => (u i : ℚ)) hu) ≤ B) (i : ι) :
    |u i| ≤ ⌊Real.exp B⌋ := by
  rw [weilHeight_eq_log_max_abs_of_gcd_eq_one u hgcd hu] at hB
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra! h; exact hu (funext fun i => by simp [h i])
  have hbdd : BddAbove (Set.range fun i => |u i|) := (Set.finite_range _).bddAbove
  have hpos : (0 : ℝ) < ↑(⨆ i, |u i|) := by
    exact_mod_cast (abs_pos.2 hj).trans_le (le_ciSup hbdd j)
  exact Int.le_floor.2 <| (Int.cast_le.2 (le_ciSup hbdd i)).trans
    ((Real.log_le_iff_le_exp hpos).1 hB)

/-- **Northcott's theorem over `ℚ`**: for every `B : ℝ` there are only finitely many points
`x` of the projective space `ℙ ℚ (ι → ℚ)` with `Faltings.weilHeight x ≤ B`. -/
@[faltings "lem_ht_northcott_rational"]
public theorem finite_setOf_weilHeight_le_rat {ι : Type*} [Fintype ι] [LinearOrder ι] (B : ℝ) :
    {x : ℙ ℚ (ι → ℚ) | weilHeight x ≤ B}.Finite := by
  classical
  have hs : {u : ι → ℤ | (∀ i, |u i| ≤ ⌊Real.exp B⌋) ∧ (fun i => (u i : ℚ)) ≠ 0}.Finite :=
    (Fintype.piFinset fun _ => Finset.Icc (-⌊Real.exp B⌋) ⌊Real.exp B⌋).finite_toSet.subset
      fun u hu => by
        simpa only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le] using hu.1
  refine (hs.dependent_image fun u hu => Projectivization.mk ℚ _ hu.2).subset ?_
  rintro x (hx : weilHeight x ≤ B)
  obtain ⟨u, hu, hgcd, rfl⟩ := exists_primitive_rep x
  exact ⟨u, ⟨abs_le_floor_exp_of_weilHeight_le u hgcd hu hx, hu⟩, rfl⟩

end Faltings
