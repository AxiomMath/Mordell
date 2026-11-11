module

public import Mordell.FunctionField.Place.Constants
public import Mordell.FunctionField.Place.Basic
public import Mordell.FunctionField.SemilocalRing
public import Mordell.FunctionField.Place.OverZero

/-!
# An element of a function field has finitely many poles

Let `F/K` be an algebraic function field of one variable and `x ∈ F`. Then `x` lies in the ring
`𝒪_v` of all but finitely many places `v` of `F/K`: the set of places at which `x` has a pole is
finite.

If `x` is algebraic over `K` it lies in every place. Otherwise `x⁻¹` is transcendental, and the
poles of `x` are among the zeros of `x⁻¹`, which correspond to the finitely many maximal ideals of
the semilocal ring `S_{x⁻¹}`.

## Main results

* `Faltings.Place.finite_setOf_notMem`: `{v : Place K F | x ∉ v.toSubalgebra}.Finite`.

## Implementation notes

The function field is Mathlib's `FunctionField K F` (that is, `FiniteDimensional (RatFunc K) F`),
with `IsScalarTower K (RatFunc K) F` expressing that `K → K(X) → F` is the structure map of `F`.
The ring `𝒪_v` of a place `v` is `v.toSubalgebra`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Corollary 1.3.4
-/

public section

namespace Faltings

open FunctionField

/-- The poles of `x` are zeros of `x⁻¹`: a place not containing `x` has `x⁻¹` in its maximal
ideal. -/
private lemma Place.inv_mem_maximalIdeal_of_notMem {K F : Type*} [CommSemiring K] [Field F]
    [Algebra K F] {v : Place K F} {x : F} (hv : x ∉ v.toSubalgebra) :
    x⁻¹ ∈ v.maximalIdeal :=
  (v.toValuationSubring.mem_nonunits_iff_or.trans
    (or_iff_right (inv_ne_zero <| by rintro rfl; exact hv (zero_mem _)))).mpr
    (by rwa [inv_inv])

/-- An element `x` of an algebraic function field `F/K` has only finitely many poles: the set of
places `v` of `F/K` with `x ∉ 𝒪_v` is finite. -/
@[faltings "thm_faltings_finitely_many_poles"]
theorem Place.finite_setOf_notMem {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] (x : F) :
    {v : Place K F | x ∉ v.toSubalgebra}.Finite := by
  by_cases hx : IsAlgebraic K x
  · -- constants lie in every place, so `x` has no pole
    exact Set.finite_empty.subset fun v hv =>
      hv (v.algebraicClosure_le (mem_algebraicClosure_iff.mpr hx))
  · -- otherwise the poles of `x` are among the zeros of the transcendental `x⁻¹`
    have hz : Transcendental K x⁻¹ := fun h => hx (by simpa using h.inv)
    obtain ⟨e, -⟩ := exists_equiv_maximalSpectrum_semilocalRing hz
    have := finite_maximalSpectrum_semilocalRing hz
    exact (Set.finite_range fun 𝔫 => (e 𝔫).1).subset fun v hv =>
      ⟨e.symm ⟨v, Place.inv_mem_maximalIdeal_of_notMem hv⟩, by simp⟩

end Faltings

end
