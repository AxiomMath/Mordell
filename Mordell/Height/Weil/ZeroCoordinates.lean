module

public import Mordell.Height.Weil.Representative

/-!
# Zero coordinates do not change the Weil height

Let `x = (v_i)_{i ∈ ι}` be a point of projective space over an algebraic extension `K` of `ℚ`,
and let `x'` be obtained from these homogeneous coordinates by inserting coordinates equal to
`0`: along an injective map of index sets `e : ι → ι'`, the coordinate of `x'` at `e i` is `v_i`
and every coordinate outside the range of `e` is `0`. Then `h(x') = h(x)`.

## Main results

* `Faltings.weilHeight_mk_extend_zero`: for an injective `e : ι → ι'` and a nonzero
  `v : ι → K`, the point with coordinates `Function.extend e v 0` has the same height
  `Faltings.weilHeight` as the point with coordinates `v`.

## Implementation notes

Inserting zero coordinates is `Function.extend e v 0` for an injective `e : ι → ι'`. The
statement allows any injective `e`, not only an order-preserving one, so it also covers a
permutation of the coordinates followed by an insertion of zeros. The case `ι = Fin (n + 1)`,
`ι' = Fin (n' + 1)`, `K = AlgebraicClosure ℚ` is the classical statement for `ℙⁿ(ℚ̄)` and
`ℙ^{n'}(ℚ̄)`. Compare `Height.mulHeight_sumElim_zero_eq`, the relative multiplicative height over
a fixed number field.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

open Function

/-- Extending a nonnegative real family by zero along an injection does not change its
supremum. This is `iSup_extend_bot` for `ℝ`, which is not a complete lattice. -/
private theorem iSup_extend_zero {ι ι' : Type*} [Finite ι] {e : ι → ι'} (he : Injective e)
    {f : ι → ℝ} (hf : 0 ≤ f) : ⨆ j, extend e f 0 j = ⨆ i, f i := by
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hle (j : ι') : extend e f 0 j ≤ ⨆ i, f i := by
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simpa [he.extend_apply] using le_ciSup hb i
    · simpa [extend_apply' _ _ _ hj] using Real.iSup_nonneg hf
  have hnn (j : ι') : 0 ≤ extend e f 0 j := by
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simpa [he.extend_apply] using hf i
    · simp [extend_apply' _ _ _ hj]
  refine le_antisymm (Real.iSup_le hle (Real.iSup_nonneg hf))
    (Real.iSup_le (fun i => ?_) (Real.iSup_nonneg hnn))
  simpa [he.extend_apply] using le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ (e i)

/-- The vector absolute value is unchanged by inserting zero coordinates. -/
private theorem vectorAbv_extend_zero {K : Type*} [Field K] [NumberField K] {ι ι' : Type*}
    [Finite ι] {e : ι → ι'} (he : Injective e) (y : ι → K) (w : NumberFieldPlace K) :
    w.vectorAbv (extend e y 0) = w.vectorAbv y := by
  have h0 : w.normalizedAbv ∘ (0 : ι' → K) = 0 := funext fun _ => w.normalizedAbv_zero
  simp only [NumberFieldPlace.vectorAbv, apply_extend w.normalizedAbv, h0]
  exact iSup_extend_zero he fun i => NumberFieldPlace.normalizedAbv_nonneg w (y i)

/-- Inserting zero coordinates does not change the Weil height: if `e : ι → ι'` is injective and
`v : ι → K` is nonzero, the point of `ℙ K (ι' → K)` with coordinates `Function.extend e v 0`
(equal to `v i` at `e i` and to `0` off the range of `e`) has the same height
`Faltings.weilHeight` as the point of `ℙ K (ι → K)` with coordinates `v`. -/
@[faltings "lem_ht_height_zero_coordinates"]
public theorem weilHeight_mk_extend_zero {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι ι' : Type*} [Fintype ι] [LinearOrder ι] [Fintype ι']
    [LinearOrder ι'] {e : ι → ι'} (he : Function.Injective e) (v : ι → K) (hv : v ≠ 0) :
    weilHeight (Projectivization.mk K (Function.extend e v 0)
        (fun h => hv (funext fun i => by simpa [he.extend_apply] using congrFun h (e i)))) =
      weilHeight (Projectivization.mk K v hv) := by
  set F := IntermediateField.adjoin ℚ (Set.range v)
  have hfin : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  let : NumberField F :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  let y : ι → F := fun i => ⟨v i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  have hyv : algebraMap F K ∘ y = v := rfl
  have hyv' : algebraMap F K ∘ extend e y 0 = extend e v 0 := by
    ext j
    simp [apply_extend (algebraMap F K), comp_def, y]
    rfl
  have hy' : algebraMap F K ∘ extend e y 0 ≠ 0 := by
    rw [hyv']
    exact fun h => hv (funext fun i => by simpa [he.extend_apply] using congrFun h (e i))
  rw [weilHeight_eq_sumLocalHeight (y := y) (hyv ▸ hv) (by simp only [hyv]),
    weilHeight_eq_sumLocalHeight hy' (by simp only [hyv'])]
  simp only [sumLocalHeight, NumberFieldPlace.localHeight, vectorAbv_extend_zero he]

end Faltings
