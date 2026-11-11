module

public import Mordell.Height.Weil.PointField
public import Mordell.Height.Weil.SubVector
public import Mordell.Height.Weil.MinimalPolynomial
public import Mordell.Height.Weil.NorthcottRat

/-!
# Northcott's theorem

For every bound `B` on the absolute logarithmic Weil height and every bound `D` on the degree
`[ℚ(x) : ℚ]`, only finitely many points `x` of projective space over an algebraic extension of
`ℚ` satisfy both bounds.

First the algebraic numbers of bounded height and degree form a finite set: the coefficient
point of the minimal polynomial has bounded height, so Northcott's theorem over `ℚ` leaves
finitely many minimal polynomials. Then every coordinate of a representative of a point of
bounded height and degree, normalized to have a coordinate equal to `1`, is such an algebraic
number.

## Main results

* `Faltings.finite_setOf_weilHeight_le_of_degreeOfPoint_le`: the set
  `{x | h(x) ≤ B ∧ [ℚ(x) : ℚ] ≤ D}` is finite.

## Implementation notes

The points live in `ℙ K (ι → K)` for an arbitrary algebraic extension `K / ℚ` and a finite,
linearly ordered index type `ι`, the setting of `Faltings.weilHeight`; `K = AlgebraicClosure ℚ`
and `ι = Fin (n + 1)` give `ℙⁿ(ℚ̄)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- For every `C`, only finitely many affine points `ξ ∈ ℚⁿ` have `affineWeilHeight ξ ≤ C`. -/
private theorem finite_setOf_affineWeilHeight_le_rat (n : ℕ) (C : ℝ) :
    {ξ : Fin n → ℚ | affineWeilHeight ξ ≤ C}.Finite := by
  have hne : ∀ ξ : Fin n → ℚ, (Fin.cons 1 ξ : Fin (n + 1) → ℚ) ≠ 0 :=
    fun ξ h => one_ne_zero (congr_fun h 0)
  refine Set.Finite.of_finite_image (f := fun ξ => Projectivization.mk ℚ _ (hne ξ))
    ((finite_setOf_weilHeight_le_rat C).subset ?_) ?_
  · rintro _ ⟨ξ, hξ, rfl⟩
    exact hξ
  · intro ξ _ ξ' _ h
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).1 h
    have h1 : c = 1 := by simpa using congr_fun hc 0
    funext r
    exact (by simpa [h1] using congr_fun hc r.succ : ξ' r = ξ r).symm

/-- The coefficient vector `(s_1, …, s_d)`, `s_r = (-1)^r · p_{d-r}`, of a polynomial `p`. -/
private noncomputable def coeffVector (d : ℕ) (p : Polynomial ℚ) : Fin d → ℚ :=
  fun r => (-1) ^ ((r : ℕ) + 1) * p.coeff (d - ((r : ℕ) + 1))

/-- A monic polynomial of degree `d` is determined by its coefficient vector. -/
private theorem coeffVector_injOn (d : ℕ) :
    {p : Polynomial ℚ | p.Monic ∧ p.natDegree = d}.InjOn (coeffVector d) := by
  rintro p ⟨hp, hpd⟩ q ⟨hq, hqd⟩ h
  ext m
  rcases lt_trichotomy m d with hm | rfl | hm
  · have := congr_fun h ⟨d - 1 - m, by omega⟩
    simp only [coeffVector] at this
    have hm' : d - (d - 1 - m + 1) = m := by omega
    rw [hm'] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this
  · rw [← hpd, hp.coeff_natDegree, hpd, ← hqd, hq.coeff_natDegree]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hpd ▸ hm),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hqd ▸ hm)]

/-- For every `B` and `D`, only finitely many `α ∈ K` have `h(α) ≤ B` and degree at most `D`. -/
private theorem finite_setOf_affineWeilHeight_le_natDegree_le {K : Type*} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] (B : ℝ) (D : ℕ) :
    {α : K | affineWeilHeight ![α] ≤ B ∧ (minpoly ℚ α).natDegree ≤ D}.Finite := by
  classical
  refine (Set.finite_le_nat D).biUnion (t := fun d =>
    {α : K | affineWeilHeight ![α] ≤ B ∧ (minpoly ℚ α).natDegree = d}) (fun d _ => ?_)
    |>.subset fun α hα => Set.mem_biUnion hα.2 ⟨hα.1, rfl⟩
  set P := minpoly ℚ '' {α : K | affineWeilHeight ![α] ≤ B ∧ (minpoly ℚ α).natDegree = d}
  have hP : P.Finite := by
    refine Set.Finite.of_finite_image ((finite_setOf_affineWeilHeight_le_rat d
      (d * B + d * Real.log 2)).subset ?_) ((coeffVector_injOn d).mono ?_)
    · rintro _ ⟨_, ⟨α, ⟨hαB, rfl⟩, rfl⟩, rfl⟩
      refine (affineWeilHeight_minpoly_coeff_le α).trans ?_
      gcongr
    · rintro _ ⟨α, ⟨-, hαd⟩, rfl⟩
      exact ⟨minpoly.monic (Algebra.IsAlgebraic.isAlgebraic α).isIntegral, hαd⟩
  refine (hP.biUnion fun p _ => (p.aroots K).toFinset.finite_toSet).subset ?_
  intro α hα
  have hi : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  refine Set.mem_biUnion ⟨α, hα, rfl⟩ ?_
  simp [minpoly.ne_zero hi]

/-- A coordinate `v i` of a representative `v` with `v j = 1` has height `h(v i) ≤ h(v)`:
`(1 : v i)` is the sub-vector `(v j, v i)` of `v`. -/
private theorem affineWeilHeight_le_weilHeight_of_eq_one {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι] [LinearOrder ι] (v : ι → K) (hv : v ≠ 0)
    {j : ι} (hj : v j = 1) (i : ι) :
    affineWeilHeight ![v i] ≤ weilHeight (Projectivization.mk K v hv) := by
  have heq : v ∘ ![j, i] = Fin.cons 1 ![v i] := by ext k; fin_cases k <;> simp [hj]
  have hf : v ∘ ![j, i] ≠ 0 := heq ▸ fun h => one_ne_zero (congr_fun h 0)
  simpa only [affineWeilHeight, heq] using weilHeight_mk_comp_le v ![j, i] hf

/-- An element `α` of the field of definition `ℚ(x)` has degree at most `[ℚ(x) : ℚ]`. -/
private theorem natDegree_minpoly_le_degreeOfPoint {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Finite ι] (x : ℙ K (ι → K)) {α : K}
    (hα : α ∈ pointField ℚ x) : (minpoly ℚ α).natDegree ≤ degreeOfPoint ℚ x := by
  have : Finite {r : K | ∃ i j, x.rep j ≠ 0 ∧ r = x.rep i / x.rep j} :=
    ((Set.finite_range fun p : ι × ι => x.rep p.1 / x.rep p.2).subset
      (by rintro r ⟨i, j, -, rfl⟩; exact ⟨(i, j), rfl⟩)).to_subtype
  have : FiniteDimensional ℚ (pointField ℚ x) :=
    IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  rw [← IntermediateField.adjoin.finrank (Algebra.IsAlgebraic.isAlgebraic α).isIntegral]
  exact IntermediateField.finrank_le_of_le_right (IntermediateField.adjoin_simple_le_iff.mpr hα)

/-- **Northcott's theorem**: for `B ≥ 0` and `D ≥ 1`, there are only finitely many points `x` of
`ℙ K (ι → K)`, `K / ℚ` algebraic, with `Faltings.weilHeight x ≤ B` and
`Faltings.degreeOfPoint ℚ x ≤ D`. -/
@[faltings "thm_ht_northcott"]
theorem finite_setOf_weilHeight_le_of_degreeOfPoint_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι] [LinearOrder ι] {B : ℝ} (hB : 0 ≤ B)
    {D : ℕ} (hD : 1 ≤ D) :
    {x : ℙ K (ι → K) | weilHeight x ≤ B ∧ degreeOfPoint ℚ x ≤ D}.Finite := by
  set A := {α : K | affineWeilHeight ![α] ≤ B ∧ (minpoly ℚ α).natDegree ≤ D}
  have hT : {w : {w : ι → K // w ≠ 0} | ∀ i, w.1 i ∈ A}.Finite :=
    ((Set.Finite.pi fun _ => finite_setOf_affineWeilHeight_le_natDegree_le B D).preimage
      Subtype.val_injective.injOn).subset fun w hw i _ => hw i
  refine (hT.image (Projectivization.mk' K)).subset ?_
  rintro x ⟨hxB, hxD⟩
  obtain ⟨v, j, hv, hvj, hx⟩ := exists_coords_fieldOfDefinition_eq_one ℚ x
  refine ⟨⟨_, hv⟩, fun i => ⟨?_, (natDegree_minpoly_le_degreeOfPoint x (v i).2).trans hxD⟩, hx⟩
  exact (affineWeilHeight_le_weilHeight_of_eq_one (fun k => (v k : K)) hv (j := j)
    (by simp [hvj]) i).trans (hx.symm ▸ hxB)

end Faltings
