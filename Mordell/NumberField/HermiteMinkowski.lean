module

public import Mordell.NumberField.UnramifiedOutside

/-!
# The Hermite–Minkowski finiteness theorem for extensions unramified outside `S`

Let `k` be a number field, `S` a finite set of finite places of `k` and `N ≥ 1` a natural number.
Inside any field extension `K / k` there are only finitely many intermediate fields `L` with
`[L : k] ≤ N` that are unramified outside `S`. This follows from the bound on the discriminant of
such fields together with Hermite's theorem that there are only finitely many number fields of
bounded discriminant inside a given field.

## Main results

* `Faltings.finite_setOf_finrank_le_isUnramifiedOutside`: the intermediate fields of `K / k` of
  degree at most `N` over `k` that are unramified outside `S` form a finite set.

## Implementation notes

The ambient field `K` is an arbitrary extension of `k`; the algebraic closure `k̄` is one instance.
The degree bound `[L : k] ≤ N` carries the finiteness of `L / k`, so it is written as
`∃ _ : FiniteDimensional k L, Module.finrank k L ≤ N ∧ …`, the instance being needed to state
`Faltings.IsUnramifiedOutside`.

## References

* J. S. Milne, *Algebraic Number Theory*, Theorem 8.42
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.5
-/

@[expose] public section

open NumberField IsDedekindDomain

namespace Faltings

/-- **Hermite–Minkowski.** For a number field `k`, a finite set `S` of finite places of `k` and
`N ≥ 1`, only finitely many intermediate fields `L` of a field extension `K / k` have
`[L : k] ≤ N` and are unramified outside `S`.

Restricting scalars to `ℚ` is injective on intermediate fields, and the discriminant bound
`Faltings.exists_discr_le_of_isUnramifiedOutside` puts every such `L` among the finitely many
number fields in `K` of bounded discriminant (`NumberField.finite_of_discr_bdd`). -/
@[faltings "thm_mw_hermite_minkowski"]
theorem finite_setOf_finrank_le_isUnramifiedOutside (k K : Type*) [Field k] [NumberField k]
    [Field K] [Algebra k K] (S : Finset (HeightOneSpectrum (𝓞 k))) (N : ℕ)
    (hN : 1 ≤ N) :
    {L : IntermediateField k K |
      ∃ _ : FiniteDimensional k L, Module.finrank k L ≤ N ∧ IsUnramifiedOutside k L S}.Finite := by
  obtain ⟨B, -, hB⟩ := exists_discr_le_of_isUnramifiedOutside k S N hN
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  refine Set.Finite.of_finite_image ?_ (IntermediateField.restrictScalars_injective ℚ).injOn
  refine ((finite_of_discr_bdd (A := K) B).image Subtype.val).subset ?_
  rintro _ ⟨L, ⟨_, hdeg, hun⟩, rfl⟩
  exact ⟨⟨L.restrictScalars ℚ, (Module.Finite.trans k L : FiniteDimensional ℚ L)⟩,
    hB L hdeg hun, rfl⟩

end Faltings
