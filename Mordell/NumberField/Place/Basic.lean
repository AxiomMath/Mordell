module

public import Mathlib
public import Mordell.Attr

/-!
# Places of a number field

The set `M_K` of places of a number field `K` is the disjoint union of its finite places and its
infinite (archimedean) places.

* A finite place is a `NumberField.FinitePlace K`; these are in bijection with the nonzero prime
  ideals of `𝓞 K` via `NumberField.FinitePlace.equivHeightOneSpectrum`, and the completion of `K`
  at the finite place `w` is the `𝔭_w`-adic completion
  `(NumberField.FinitePlace.maximalIdeal w).adicCompletion K`, with `K → K_w` the map
  `NumberField.FinitePlace.embedding`.
* An infinite place is a `NumberField.InfinitePlace K`, i.e. an embedding `K → ℂ` up to complex
  conjugation; its completion is `NumberField.InfinitePlace.Completion`, which is `ℝ` for a real
  place (`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`) and `ℂ` for a complex one
  (`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`).

For `K = ℚ` the finite places correspond to the primes `p`, with completions `ℚ_p`.

## Main definitions

* `Faltings.NumberFieldPlace K`: the set `M_K` of places of `K`, as
  `FinitePlace K ⊕ InfinitePlace K`.

## Implementation notes

A place is a finite place or an infinite place, so `M_K` is the sum type. The completions are
Mathlib's at each summand and are not repackaged as a single family over
`Faltings.NumberFieldPlace K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Def. 1.1.4, Example 1.1.11.
-/

@[expose] public section

namespace Faltings

open NumberField

/-- The set `M_K` of places of a number field `K`: a place is either a finite place
(`Sum.inl`, a `NumberField.FinitePlace K`) or an infinite place (`Sum.inr`, a
`NumberField.InfinitePlace K`). -/
@[faltings "def_ht_places_number_field"]
abbrev NumberFieldPlace (K : Type*) [Field K] [NumberField K] : Type _ :=
  FinitePlace K ⊕ InfinitePlace K

end Faltings
