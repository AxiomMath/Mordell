module

public import Mathlib
public import Mordell.Attr

/-!
# Places of a function field

Let `F` be a field and `K` a commutative semiring with `F` a `K`-algebra (in the application, `F/K`
is an algebraic function field of one variable). A *place* of `F/K` is a subring `𝒪 ⊆ F` which
contains the image of `K`, is a valuation subring of `F` (for every `z ∈ F`, `z ∈ 𝒪` or
`z⁻¹ ∈ 𝒪`), and is different from `F`. We bundle it as a structure carrying a `K`-subalgebra and a
valuation subring of `F` with the same carrier, together with properness.

## Main definitions

* `Faltings.Place K F`: the type of places of `F/K`, the set `ℙ_F` of the source.

## Implementation notes

Stichtenoth also requires `K ⊊ 𝒪`; for a function field this is automatic (an element of `F`
transcendental over `K` or its inverse lies in `𝒪`), so it is omitted, as in the target statement.
The definition needs neither that `K` is a field nor that `F/K` is a function field, so it is
stated for a commutative semiring `K` and an arbitrary `K`-algebra `F` which is a field.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009],
  Definitions 1.1.4, 1.1.8
-/

namespace Faltings

public section

/-- A *place* of `F/K`: a `K`-subalgebra of `F` which is a valuation subring of `F` (for every
`z : F`, `z` or `z⁻¹` lies in it) and is not all of `F`. The type `Place K F` is the set `ℙ_F` of
places of `F/K`; for `v : Place K F` the ring `𝒪_v` is its carrier. -/
@[faltings "def_ff_place", ext]
structure Place (K F : Type*) [CommSemiring K] [Field F] [Algebra K F]
    extends Subalgebra K F, ValuationSubring F where
  /-- A place is a proper subring of `F`. -/
  ne_top : toSubalgebra ≠ ⊤

end

end Faltings

/-!
# The maximal ideal of a place

For a place `v` of `F/K` with valuation ring `𝒪_v ⊆ F`, the set `𝔪_v = 𝒪_v \ 𝒪_vˣ` of nonunits of
`𝒪_v` is the unique maximal ideal of the local ring `𝒪_v`. It is regarded, as in the source, as a
subset of `F`: it is the non-unital subring `ValuationSubring.nonunits` of `F`, whose elements are
the `a : F` with `v.toValuationSubring.valuation a < 1`.

## Main definitions

* `Faltings.Place.maximalIdeal v`: the set `𝔪_v ⊆ F` of nonunits of `𝒪_v`.

## Implementation notes

The definition is the Mathlib object `ValuationSubring.nonunits` of the valuation subring
underlying `v`, so it is an `abbrev`; its API (`ValuationSubring.mem_nonunits_iff`,
`ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal`, relating it to
`IsLocalRing.maximalIdeal` of `𝒪_v`) applies directly.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.1.8
-/

namespace Faltings

@[expose] public section

/-- The maximal ideal `𝔪_v = 𝒪_v \ 𝒪_vˣ` of a place `v` of `F/K`: the set of nonunits of the
valuation ring `𝒪_v`, as a non-unital subring of `F`. -/
@[faltings "def_ff_place_maximal_ideal"]
abbrev Place.maximalIdeal {K F : Type*} [CommSemiring K] [Field F] [Algebra K F]
    (v : Place K F) : NonUnitalSubring F :=
  v.toValuationSubring.nonunits

end

end Faltings

/-!
# The residue field of a place

For a place `v` of `F/K` with valuation ring `𝒪_v ⊆ F` and maximal ideal `𝔪_v`, the residue field
of `v` is the quotient `κ(v) = 𝒪_v / 𝔪_v`. Since `𝒪_v` is a local ring whose maximal ideal is
`𝔪_v`, this is the residue field `IsLocalRing.ResidueField 𝒪_v` of the local ring `𝒪_v`. It is a
`K`-algebra through the composite `K → 𝒪_v → κ(v)` of the structure map of `𝒪_v` as a
`K`-subalgebra of `F` and the residue map.

## Main definitions

* `Faltings.Place.ResidueField v`: the residue field `κ(v) = 𝒪_v / 𝔪_v` of a place `v`.
* `Faltings.Place.instAlgebraResidueField`: the `K`-algebra structure on `κ(v)` given by
  `K → 𝒪_v → κ(v)`.

## Implementation notes

The quotient `𝒪_v / 𝔪_v` is taken as the residue field of the local ring `𝒪_v`, i.e. the quotient
by `IsLocalRing.maximalIdeal 𝒪_v`; the elements of this ideal are exactly those of
`Faltings.Place.maximalIdeal v` (`ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal`).
The type is an `abbrev`, so the field structure and the API of `IsLocalRing.ResidueField` apply.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.1.14
-/

namespace Faltings

@[expose] public section

/-- The residue field `κ(v) = 𝒪_v / 𝔪_v` of a place `v` of `F/K`: the residue field of the local
ring `𝒪_v`. -/
@[faltings "def_ff_residue_field"]
abbrev Place.ResidueField {K F : Type*} [CommSemiring K] [Field F] [Algebra K F]
    (v : Place K F) : Type _ :=
  IsLocalRing.ResidueField v.toValuationSubring

/-- The residue field `κ(v)` of a place `v` of `F/K` is a `K`-algebra via `K → 𝒪_v → κ(v)`. -/
@[faltings "def_ff_residue_field"]
noncomputable instance Place.instAlgebraResidueField {K F : Type*} [CommSemiring K] [Field F]
    [Algebra K F] (v : Place K F) : Algebra K v.ResidueField :=
  ((IsLocalRing.residue v.toValuationSubring).comp
    ((algebraMap K F).codRestrict v.toValuationSubring
      v.toSubalgebra.algebraMap_mem)).toAlgebra

end

end Faltings

/-!
# Places of degree one

A place `v` of `F/K` is a *place of degree one* (a *rational place*) if its residue field
`κ(v)`, a `K`-algebra through `K → 𝒪_v → κ(v)`, has rank one over `K`; equivalently, the
structure map `K → κ(v)` is onto when `K` is a field.

## Main definitions

* `Faltings.Place.IsDegreeOne v`: the place `v` has degree one, `rank_K κ(v) = 1`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.1.14
-/

namespace Faltings

@[expose] public section

/-- A place `v` of `F/K` is a *place of degree one* (a *rational place*) if its residue field
`κ(v)` has rank one over `K`. -/
@[faltings "def_ff_degree_one_place"]
def Place.IsDegreeOne {K F : Type*} [CommSemiring K] [Field F] [Algebra K F]
    (v : Place K F) : Prop :=
  Module.rank K v.ResidueField = 1

end

end Faltings
