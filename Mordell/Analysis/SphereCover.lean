module
public import Mathlib
public import Mordell.Attr

/-!
# Covering the unit sphere by caps of small angular diameter

In a real inner product space `E` of finite dimension `ρ ≥ 1`, the unit sphere can be covered
by at most `7 ^ ρ` subsets of itself, any two points of one of which have inner product
greater than `3 / 4`. One takes the open balls of radius `1 / 3` about a maximal `1 / 3`-separated
family of points of the sphere; a volume comparison bounds the number of balls by `7 ^ ρ`.

## Main results

* `Faltings.exists_sphere_cover_inner_gt`: the covering of the unit sphere by at most `7 ^ ρ`
  caps on which the inner product exceeds `3 / 4`.

## Implementation notes

The Euclidean space `ℝ^ρ` is an arbitrary finite-dimensional real inner product space `E`
with `Module.finrank ℝ E = ρ`, so that the result applies directly to
`(A(K) / tors) ⊗ ℝ` with the Néron–Tate inner product, without choosing an isometry with
`EuclideanSpace ℝ (Fin ρ)`. The caps are indexed by `Fin M`.

## References

* [Bombieri, *The Mordell conjecture revisited*][bombieri1990], §10, p. 639
-/

open Module Metric MeasureTheory
open scoped RealInnerProductSpace

namespace Faltings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite `1 / 3`-separated subset of the unit sphere has at most `7 ^ ρ` points. -/
private theorem card_le_of_separated [FiniteDimensional ℝ E] (T : Finset E)
    (hT : (T : Set E) ⊆ sphere 0 1) (hsep : (T : Set E).Pairwise fun c c' => 1 / 3 ≤ dist c c') :
    T.card ≤ 7 ^ finrank ℝ E := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  have hle : μ (⋃ c ∈ T, ball c (1 / 6 : ℝ)) ≤ μ (ball (0 : E) (7 / 6)) := by
    refine measure_mono <| Set.iUnion₂_subset fun c hc => ball_subset_ball' ?_
    linarith [mem_sphere.1 (hT hc)]
  rw [measure_biUnion_finset (fun c hc c' hc' hne => ball_disjoint_ball (by
      linarith [hsep hc hc' hne])) fun c _ => measurableSet_ball] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 1 / 6),
    Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 7 / 6), Finset.sum_const,
    nsmul_eq_mul] at hle
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ one_pos).ne'
    measure_ball_lt_top.ne, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), show (7 / 6 : ℝ) = 7 * (1 / 6) by norm_num,
    mul_pow] at hle
  exact_mod_cast le_of_mul_le_mul_right hle (by positivity)

/-- The unit sphere is covered by the balls of radius `1 / 3` about at most `7 ^ ρ` of its
points: a `1 / 3`-separated family of maximal cardinality is such a family. -/
private theorem exists_finset_sphere_subset_biUnion_ball [FiniteDimensional ℝ E] :
    ∃ T : Finset E, T.card ≤ 7 ^ finrank ℝ E ∧ (T : Set E) ⊆ sphere 0 1 ∧
      sphere (0 : E) 1 ⊆ ⋃ c ∈ T, ball c (1 / 3) := by
  classical
  let P : ℕ → Prop := fun n => ∃ T : Finset E, T.card = n ∧ (T : Set E) ⊆ sphere 0 1 ∧
    (T : Set E).Pairwise fun c c' => 1 / 3 ≤ dist c c'
  obtain ⟨T, hTn, hTS, hTsep⟩ : P (Nat.findGreatest P (7 ^ finrank ℝ E)) :=
    Nat.findGreatest_spec (Nat.zero_le _) ⟨∅, by simp⟩
  refine ⟨T, hTn ▸ Nat.findGreatest_le _, hTS, fun x hx => ?_⟩
  by_contra! hfar
  simp only [Set.mem_iUnion, mem_ball, not_exists, not_lt] at hfar
  have hxT : x ∉ T := fun h => by linarith [hfar x h, dist_self x]
  have hcard : (insert x T).card = Nat.findGreatest P (7 ^ finrank ℝ E) + 1 := by
    rw [Finset.card_insert_of_notMem hxT, hTn]
  have hS : ((insert x T : Finset E) : Set E) ⊆ sphere 0 1 := by
    simpa using Set.insert_subset hx hTS
  have hsep : ((insert x T : Finset E) : Set E).Pairwise fun c c' => 1 / 3 ≤ dist c c' := by
    rw [Finset.coe_insert]
    exact Set.pairwise_insert.2 ⟨hTsep, fun c hc _ => ⟨hfar c hc, dist_comm x c ▸ hfar c hc⟩⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hcard ▸ card_le_of_separated _ hS hsep)
    ⟨_, hcard, hS, hsep⟩

/-- Two unit vectors at distance less than `2 / 3` have inner product greater than `3 / 4`. -/
private theorem inner_gt_of_dist_lt {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : dist x y < 2 / 3) : (3 / 4 : ℝ) < ⟪x, y⟫ := by
  have := norm_sub_sq_real x y
  rw [hx, hy, ← dist_eq_norm] at this
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- The unit sphere of a real inner product space of finite dimension `ρ ≥ 1` is covered by
`M ≤ 7 ^ ρ` subsets `C i` of itself such that `3 / 4 < ⟪x, y⟫` whenever `x` and `y` lie in the
same `C i`. -/
@[faltings "lem_bvr_spherical_caps"]
public theorem exists_sphere_cover_inner_gt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (hρ : 1 ≤ finrank ℝ E) :
    ∃ (M : ℕ) (C : Fin M → Set E), M ≤ 7 ^ finrank ℝ E ∧
      (∀ i, C i ⊆ sphere (0 : E) 1) ∧ sphere (0 : E) 1 ⊆ ⋃ i, C i ∧
      ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, (3 / 4 : ℝ) < ⟪x, y⟫ := by
  obtain ⟨T, hT, -, hcov⟩ := exists_finset_sphere_subset_biUnion_ball (E := E)
  refine ⟨T.card, fun i => sphere 0 1 ∩ ball (T.equivFin.symm i) (1 / 3), hT,
    fun i => Set.inter_subset_left, fun x hx => ?_, fun i x hx y hy => ?_⟩
  · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion.2 ⟨T.equivFin ⟨c, hc⟩, hx, by simpa using hxc⟩
  · refine inner_gt_of_dist_lt (by simpa using hx.1) (by simpa using hy.1) ?_
    linarith [dist_triangle_right x y (T.equivFin.symm i : E), mem_ball.1 hx.2, mem_ball.1 hy.2]

end Faltings
