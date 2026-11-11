module

public import Mordell.Height.Weil.Basic
public import Mordell.Height.Weil.Representative

/-!
# The height of the inverse of an algebraic number

For a nonzero algebraic number `α` the height of `α⁻¹` equals the height of `α`:
`h(α⁻¹) = h(α)`, where `h(α) = h(1 : α)` is the affine height. Indeed `(1 : α⁻¹) = (α : 1)` in
`ℙ¹`, and the Weil height is symmetric in the coordinates.

## Main results

* `Faltings.affineWeilHeight_inv`: `h(α⁻¹) = h(α)` for `α ≠ 0`.

## Implementation notes

The number `α` lies in an arbitrary algebraic extension `K / ℚ`, as for
`Faltings.affineWeilHeight`; `K = AlgebraicClosure ℚ` gives `α ∈ ℚ̄`. The height of `α` is
`Faltings.affineWeilHeight ![α]`. Both heights are computed over the number field `F = ℚ(α)`
by `Faltings.weilHeight_eq_sumLocalHeight`, from the representatives `(α : 1)` and `(1 : α)`.
This is the analogue of `Height.logHeight₁_inv`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

/-- The sum of local heights of a pair does not depend on the order of the coordinates. -/
private lemma sumLocalHeight_swap {F : Type*} [Field F] [NumberField F] (a b : F) :
    sumLocalHeight ![a, b] = sumLocalHeight ![b, a] := by
  unfold sumLocalHeight NumberFieldPlace.localHeight NumberFieldPlace.vectorAbv
  congr 1; funext w; congr 1
  rw [← (Equiv.swap (0 : Fin 2) 1).iSup_comp]
  congr 1; funext j; fin_cases j <;> rfl

open IntermediateField in
/-- The height of the inverse of a nonzero algebraic number equals its height:
`h(α⁻¹) = h(α)`, with `h(α) = Faltings.affineWeilHeight ![α] = h(1 : α)`. -/
@[faltings "lem_ht_height_inverse"]
public theorem affineWeilHeight_inv {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {α : K} (hα : α ≠ 0) :
    affineWeilHeight ![α⁻¹] = affineWeilHeight ![α] := by
  have hfin : FiniteDimensional ℚ ℚ⟮α⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  letI : NumberField ℚ⟮α⟯ :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  set a := AdjoinSimple.gen ℚ α
  unfold affineWeilHeight
  rw [weilHeight_eq_sumLocalHeight (y := ![a, 1]) (fun h => by simpa using congr_fun h 1),
    weilHeight_eq_sumLocalHeight (y := ![1, a]) (fun h => by simpa using congr_fun h 0) ?_,
    sumLocalHeight_swap]
  · congr 1; funext j; fin_cases j <;> rfl
  · refine (Projectivization.mk_eq_mk_iff' _ _ _ _ _).2 ⟨α, funext fun j => ?_⟩
    fin_cases j <;> simp [a, hα]

end Faltings
