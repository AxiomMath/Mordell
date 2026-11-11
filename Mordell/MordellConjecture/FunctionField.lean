module

public import Mathlib
public import Mordell.Attr
public import Mordell.FunctionField.Place.Basic
public import Mordell.FunctionField.Genus
public import Mordell.MordellConjecture.Curve
public import Mordell.FunctionField.Place.Constants
public import Mordell.FunctionField.SmoothProjectiveModel
public import Mordell.Curve.AdelicGenus
public import Mordell.FunctionField.RationalPlaces
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison

/-!
# Faltings' theorem (the Mordell conjecture)

Let `K` be a number field and `F/K` an algebraic function field of one variable of genus at
least two. Then `F/K` has only finitely many places of degree one, i.e. places `v` whose residue
field `κ(v)` is one-dimensional over `K`. Equivalently, a smooth projective curve of genus at
least two over a number field has only finitely many rational points.

## Main results

* `Faltings.finite_setOf_place_isDegreeOne`: if `2 ≤ Faltings.genus K F`, the set of places of
  degree one of `F/K` is finite.

## Implementation notes

An algebraic function field of one variable over `K` is encoded, as in Mathlib, by
`FunctionField K F` together with a chosen `RatFunc K`-algebra structure on `F` compatible with
the `K`-algebra structure; these are exactly the data of a finite extension of `K(x)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009]
-/

@[expose] public section

namespace Faltings

/-- **Faltings' theorem** (the Mordell conjecture): an algebraic function field of one variable
of genus at least two over a number field has only finitely many places of degree one. -/
@[faltings "thm_main"]
public theorem finite_setOf_place_isDegreeOne {K F : Type*} [Field K] [NumberField K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (h : 2 ≤ genus K F) :
    {v : Place K F | v.IsDegreeOne}.Finite :=
      by
  by_cases hK : algebraicClosure K F = ⊥
  · obtain ⟨M⟩ := FunctionField.nonempty_smoothProjectiveModel K F hK
    haveI := M.isCurve
    haveI := M.isProjectiveVariety
    haveI := M.smooth
    haveI := M.geometricallyIntegral
    obtain ⟨e, -⟩ := FunctionField.exists_equiv_isDegreeOne_section K F M
    have := (finite_setOf_comp_eq_id_of_two_le_genus K M.f
      ((FunctionField.SmoothProjectiveModel.genus_f_eq_genus K F M).symm ▸ h)).to_subtype
    exact Set.finite_coe_iff.mp (e.finite_iff.mpr this)
  · convert Set.finite_empty
    ext v
    simpa [Place.IsDegreeOne] using Place.rank_residueField_ne_one hK v

end Faltings

end
