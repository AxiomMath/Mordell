module

public import Mordell.FunctionField.Place.Basic

/-!
# Constants lie in every place

Let `F/K` be an algebraic function field of one variable and `v` a place of `F/K`. Every element
of `F` algebraic over `K` lies in the ring `𝒪_v`: the field of constants
`K̃ = algebraicClosure K F` is contained in `𝒪_v`. An element algebraic over the field `K` is
integral over `K`, hence over `𝒪_v ⊇ K`, and `𝒪_v` is integrally closed in `F`.

## Main results

* `Faltings.Place.algebraicClosure_le`: `algebraicClosure K F ≤ 𝒪_v` as `K`-subalgebras of `F`.

## Implementation notes

The function field structure is Mathlib's: `F` is an algebra over `RatFunc K` compatible with
`K → F` and finite dimensional over it (`FunctionField K F`).

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Theorem 1.1.5(c)
-/

public section

namespace Faltings

/-- Every element of `F` algebraic over `K` lies in the ring `𝒪_v` of a place `v` of `F/K`: the
field of constants `algebraicClosure K F` of a function field `F/K` is contained in `𝒪_v`.

An algebraic element is integral over `K`; mapping its monic polynomial along `K → 𝒪_v` shows it
is integral over `𝒪_v`, and `𝒪_v` is integrally closed in `F` (Mathlib's instance for a valuation
subring). -/
@[faltings "lem_ff_constants_in_place"]
theorem Place.algebraicClosure_le {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (v : Place K F) : (algebraicClosure K F).toSubalgebra ≤ v.toSubalgebra := by
  intro z hz
  obtain ⟨p, hp, hpz⟩ := (mem_algebraicClosure_iff.mp hz).isIntegral
  let f : K →+* v.toValuationSubring :=
    (algebraMap K F).codRestrict v.toValuationSubring.toSubring v.toSubalgebra.algebraMap_mem
  obtain ⟨y, rfl⟩ := (inferInstance : IsIntegrallyClosedIn v.toValuationSubring F).isIntegral_iff.mp
    ⟨p.map f, hp.map f, by rwa [Polynomial.eval₂_map]⟩
  exact y.2

end Faltings

end


/-!
# Constants are units at every place

Let `F/K` be an algebraic function field and `v` a place of `F/K`. The field of constants
`K̃ = algebraicClosure K F` meets the maximal ideal `𝔪_v` of `v` only in `0`: a nonzero constant
`z` has its inverse in `K̃ ⊆ 𝒪_v`, so `z` is a unit of `𝒪_v`.

## Main results

* `Faltings.Place.algebraicClosure_inter_maximalIdeal`: `K̃ ∩ 𝔪_v = {0}` as subsets of `F`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Theorem 1.1.5(c)
-/

public section

namespace Faltings

/-- The field of constants `algebraicClosure K F` of a function field `F/K` meets the maximal
ideal `𝔪_v` of a place `v` only in `0`.

A nonzero constant `z` has `z⁻¹ ∈ K̃ ⊆ 𝒪_v` (`Place.algebraicClosure_le`), so `z ∉ 𝔪_v`
(`ValuationSubring.mem_nonunits_iff_or`, the case `z = 0` excluded). -/
@[faltings "lem_ff_constants_units"]
theorem Place.algebraicClosure_inter_maximalIdeal {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (v : Place K F) :
    (algebraicClosure K F : Set F) ∩ (v.maximalIdeal : Set F) = {0} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨zero_mem _, zero_mem _⟩, fun z ⟨hK, hm⟩ => ?_⟩
  by_contra hz
  exact (v.toValuationSubring.mem_nonunits_iff_or.trans (or_iff_right hz)).mp hm
    (v.algebraicClosure_le ((algebraicClosure K F).inv_mem hK))

end Faltings

end


/-!
# No places of degree one when the constant field is bigger

Let `F/K` be an algebraic function field of one variable whose field of constants
`K̃ = algebraicClosure K F` is strictly larger than `K`. Then no place `v` of `F/K` has residue
field `κ(v)` of rank one over `K`: the field `K̃` lies in `𝒪_v` and maps injectively into `κ(v)`,
so `rank_K κ(v) ≥ rank_K K̃ ≥ 2`.

## Main results

* `Faltings.Place.rank_residueField_ne_one`: if `algebraicClosure K F ≠ ⊥`, then
  `Module.rank K v.ResidueField ≠ 1` for every place `v` of `F/K`.

## Implementation notes

The function field structure is Mathlib's: `F` is an algebra over `RatFunc K` compatible with
`K → F` and finite dimensional over it (`FunctionField K F`). The field of constants is Mathlib's
`algebraicClosure K F`, and `K̃ ≠ K` is `algebraicClosure K F ≠ ⊥`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Section 1.1
-/

public section

namespace Faltings

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]

/-- The field of constants embeds `K`-linearly into the residue field of every place:
`K̃ ⊆ 𝒪_v → κ(v)`, well defined since `K̃ ⊆ 𝒪_v` (`Place.algebraicClosure_le`). -/
private noncomputable def algebraicClosureToResidueField (v : Place K F) :
    algebraicClosure K F →ₐ[K] v.ResidueField where
  toRingHom := (IsLocalRing.residue v.toValuationSubring).comp <|
    (algebraicClosure K F).val.toRingHom.codRestrict v.toValuationSubring.toSubring
      fun x => v.algebraicClosure_le x.2
  commutes' _ := rfl

/-- The field of constants has `K`-dimension at most that of the residue field of any place. -/
private theorem rank_algebraicClosure_le_rank_residueField (v : Place K F) :
    Module.rank K (algebraicClosure K F) ≤ Module.rank K v.ResidueField :=
  LinearMap.rank_le_of_injective (algebraicClosureToResidueField v).toLinearMap
    (algebraicClosureToResidueField v).toRingHom.injective

/-- If the field of constants `algebraicClosure K F` of a function field `F/K` is strictly larger
than `K`, then no place `v` of `F/K` has residue field of rank one over `K`.

The field of constants embeds `K`-linearly into `κ(v)`, so rank one for `κ(v)` would force
`rank_K K̃ ≤ 1`, i.e. `K̃ = K`. -/
@[faltings "lem_ff_no_rational_points_if_constants_bigger"]
theorem Place.rank_residueField_ne_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (h : algebraicClosure K F ≠ ⊥) (v : Place K F) :
    Module.rank K v.ResidueField ≠ 1 := fun h1 =>
  h <| IntermediateField.rank_eq_one_iff.mp <|
    le_antisymm (h1 ▸ rank_algebraicClosure_le_rank_residueField v) <|
      Module.one_le_rank_iff.mpr ⟨Algebra.linearMap K _, (algebraMap K _).injective⟩

end Faltings

end
