module

public import Mordell.NumberField.Place.Basic

/-!
# Places lying over a place

Let `k ⊆ K` be number fields, `v ∈ M_k` and `w ∈ M_K`. The place `w` *lies over* `v`, written
`w ∣ v`, if either both are finite and the prime `𝔭_w` of `𝓞 K` contracts to the prime `𝔭_v`
of `𝓞 k`, i.e. `𝔭_w ∩ 𝓞 k = 𝔭_v`, or both are infinite and an embedding `K → ℂ` defining `w`
restricts to an embedding `k → ℂ` defining `v`. Taking `k = ℚ` this defines `w ∣ p` for
`p ∈ M_ℚ`.

When `w ∣ v`, the map `k → K → K_w` extends by continuity to an embedding `k_v → K_w`, through
which `K_w` is a finite extension of `k_v`.

## Main definitions

* `Faltings.NumberFieldPlace.LiesOver w v`: the place `w` of `K` lies over the place `v` of `k`.

## Main results

* `Faltings.NumberFieldPlace.liesOver_inl_inl`, `Faltings.NumberFieldPlace.liesOver_inr_inr`: the
  two cases of `Faltings.NumberFieldPlace.LiesOver`, as Mathlib's `Ideal.LiesOver` and
  `InfinitePlace.LiesOver`.
* `Faltings.NumberFieldPlace.not_liesOver_inl_inr`,
  `Faltings.NumberFieldPlace.not_liesOver_inr_inl`: a finite place never lies over an infinite
  place, nor conversely.
* `Faltings.NumberFieldPlace.liesOverInlEquiv`: the places of `K` over a finite place `v` of `k`
  are the primes of `𝓞 K` over `𝔭_v`; in particular there are finitely many
  (`Faltings.NumberFieldPlace.finite_liesOver_inl`,
  `Faltings.NumberFieldPlace.finite_finitePlace_liesOver_inl`,
  `Faltings.NumberFieldPlace.finite_heightOneSpectrum_liesOver`).
* `Faltings.NumberFieldPlace.finitePlaceLiesOverEquiv`,
  `Faltings.NumberFieldPlace.infinitePlaceLiesOverEquiv`: the places of `K` over a finite
  (infinite) place of `k` are finite (infinite) places.

## Implementation notes

The finite case is Mathlib's `Ideal.LiesOver` for the primes `FinitePlace.maximalIdeal w` and
`FinitePlace.maximalIdeal v`, along `𝓞 k → 𝓞 K`; it says `𝔭_v = 𝔭_w.under (𝓞 k)`. The infinite
case is Mathlib's `NumberField.InfinitePlace.LiesOver`, which says that `w` restricts to `v` on
`k`; this is the same as asking that some (equivalently every) embedding defining `w` restricts
to an embedding defining `v`.

The finite case is not phrased through the absolute values: the normalized absolute value of a
finite place `w` restricts to `|·|_v ^ (e f)` on `k`, not to `|·|_v`.

For infinite places the embedding of completions `k_v → K_w` is Mathlib's
`NumberField.LiesOver.completionMap`; for finite places it is the map of adic completions
induced by `𝓞 k → 𝓞 K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Sec. 1.1.
-/

@[expose] public section

namespace Faltings

open NumberField

/-- The place `w` of the number field `K` *lies over* the place `v` of the subfield `k`,
written `w ∣ v`: both are finite and `𝔭_w ∩ 𝓞 k = 𝔭_v` (`Ideal.LiesOver`), or both are
infinite and `w` restricts to `v` on `k` (`NumberField.InfinitePlace.LiesOver`). -/
@[faltings "def_ht_place_lies_over"]
def NumberFieldPlace.LiesOver {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] : NumberFieldPlace K → NumberFieldPlace k → Prop
  | .inl w, .inl v =>
    (FinitePlace.maximalIdeal w).asIdeal.LiesOver (FinitePlace.maximalIdeal v).asIdeal
  | .inr w, .inr v => w.LiesOver v
  | _, _ => False

namespace NumberFieldPlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- A finite place `w` lies over a finite place `v` iff `𝔭_w` lies over `𝔭_v`. -/
@[simp]
theorem liesOver_inl_inl (w : FinitePlace K) (v : FinitePlace k) :
    LiesOver (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k) ↔
      (FinitePlace.maximalIdeal w).asIdeal.LiesOver (FinitePlace.maximalIdeal v).asIdeal :=
  .rfl

/-- An infinite place `w` lies over an infinite place `v` iff `w` restricts to `v`. -/
@[simp]
theorem liesOver_inr_inr (w : InfinitePlace K) (v : InfinitePlace k) :
    LiesOver (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace k) ↔ w.LiesOver v :=
  .rfl

/-- A finite place never lies over an infinite place. -/
@[simp]
theorem not_liesOver_inl_inr (w : FinitePlace K) (v : InfinitePlace k) :
    ¬LiesOver (.inl w : NumberFieldPlace K) (.inr v : NumberFieldPlace k) :=
  id

/-- An infinite place never lies over a finite place. -/
@[simp]
theorem not_liesOver_inr_inl (w : InfinitePlace K) (v : FinitePlace k) :
    ¬LiesOver (.inr w : NumberFieldPlace K) (.inl v : NumberFieldPlace k) :=
  id

/-- The places of `K` over a finite place `v` of `k` are the primes of `𝓞 K` over `𝔭_v`: a
place `w ∣ v` is necessarily finite, and goes to its prime `𝔭_w`. -/
noncomputable def liesOverInlEquiv (v : FinitePlace k) :
    {w : NumberFieldPlace K // w.LiesOver (.inl v)} ≃
      (FinitePlace.maximalIdeal v).asIdeal.primesOver (𝓞 K) where
  toFun
    | ⟨.inl w, h⟩ => ⟨(FinitePlace.maximalIdeal w).asIdeal, (FinitePlace.maximalIdeal w).isPrime, h⟩
    | ⟨.inr _, h⟩ => h.elim
  invFun P :=
    haveI := P.2.2
    ⟨.inl (FinitePlace.mk ⟨P.1, P.2.1,
      Ideal.ne_bot_of_liesOver_of_ne_bot (FinitePlace.maximalIdeal v).ne_bot P.1⟩), by
      simpa [FinitePlace.maximalIdeal_mk] using P.2.2⟩
  left_inv := by
    rintro ⟨w | w, h⟩
    · exact Subtype.ext (congrArg Sum.inl (FinitePlace.mk_maximalIdeal w))
    · exact h.elim
  right_inv P := by simp [FinitePlace.maximalIdeal_mk]

/-- `liesOverInlEquiv` sends a finite place `w ∣ v` to its prime `𝔭_w`. -/
@[simp]
theorem coe_liesOverInlEquiv_inl (v : FinitePlace k) (w : FinitePlace K)
    (h : LiesOver (.inl w : NumberFieldPlace K) (.inl v)) :
    (liesOverInlEquiv v ⟨.inl w, h⟩ : Ideal (𝓞 K)) = (FinitePlace.maximalIdeal w).asIdeal :=
  rfl

/-- Only finitely many places of `K` lie over a finite place of `k`. -/
instance finite_liesOver_inl (v : FinitePlace k) :
    Finite {w : NumberFieldPlace K // w.LiesOver (.inl v)} :=
  .of_equiv _ (liesOverInlEquiv v).symm

/-- Only finitely many primes of `𝓞 K` lie over a prime `p` of `𝓞 k`. -/
instance finite_heightOneSpectrum_liesOver (p : IsDedekindDomain.HeightOneSpectrum (𝓞 k)) :
    Finite {P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver p.asIdeal} :=
  .of_injective (fun P => (⟨P.1.asIdeal, P.1.isPrime, P.2⟩ : p.asIdeal.primesOver (𝓞 K)))
    fun _ _ h => Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h))

/-- The finite places of `K` over a finite place `v` of `k`, as places of `K` over `v`. -/
def finitePlaceLiesOverEquiv (v : FinitePlace k) :
    {w : FinitePlace K // LiesOver (.inl w : NumberFieldPlace K) (.inl v)} ≃
      {w : NumberFieldPlace K // w.LiesOver (.inl v)} where
  toFun w := ⟨.inl w.1, w.2⟩
  invFun
    | ⟨.inl w, h⟩ => ⟨w, h⟩
    | ⟨.inr _, h⟩ => h.elim
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w | w, h⟩
    · rfl
    · exact h.elim

/-- `finitePlaceLiesOverEquiv` sends a finite place `w` to the place `Sum.inl w`. -/
@[simp]
theorem coe_finitePlaceLiesOverEquiv (v : FinitePlace k)
    (w : {w : FinitePlace K // LiesOver (.inl w : NumberFieldPlace K) (.inl v)}) :
    (finitePlaceLiesOverEquiv v w : NumberFieldPlace K) = .inl w.1 :=
  rfl

/-- Only finitely many finite places of `K` lie over a finite place of `k`. -/
instance finite_finitePlace_liesOver_inl (v : FinitePlace k) :
    Finite {w : FinitePlace K // LiesOver (.inl w : NumberFieldPlace K) (.inl v)} :=
  .of_equiv _ (finitePlaceLiesOverEquiv v).symm

/-- The infinite places of `K` over an infinite place `v` of `k`, as places of `K` over `v`. -/
def infinitePlaceLiesOverEquiv (v : InfinitePlace k) :
    {w : InfinitePlace K // w.LiesOver v} ≃ {w : NumberFieldPlace K // w.LiesOver (.inr v)} where
  toFun w := ⟨.inr w.1, w.2⟩
  invFun
    | ⟨.inr w, h⟩ => ⟨w, h⟩
    | ⟨.inl _, h⟩ => h.elim
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w | w, h⟩
    · exact h.elim
    · rfl

/-- `infinitePlaceLiesOverEquiv` sends an infinite place `w` to the place `Sum.inr w`. -/
@[simp]
theorem coe_infinitePlaceLiesOverEquiv (v : InfinitePlace k)
    (w : {w : InfinitePlace K // w.LiesOver v}) :
    (infinitePlaceLiesOverEquiv v w : NumberFieldPlace K) = .inr w.1 :=
  rfl

end NumberFieldPlace

end Faltings

/-!
# Every place lies over exactly one place of a subfield

Let `k ⊆ K` be number fields. Every place `w` of `K` lies over exactly one place `v` of `k`:
for a finite place, `v` is the place of the prime `𝔭_w ∩ 𝓞 k`; for an infinite place, `v` is
the restriction of `w` to `k`.

## Main results

* `Faltings.NumberFieldPlace.existsUnique_liesOver`: for every `w : NumberFieldPlace K` there is a
  unique `v : NumberFieldPlace k` with `w.LiesOver v`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Sec. 1.1.
-/

@[expose] public section

namespace Faltings

open NumberField IsDedekindDomain

/-- A finite place `w` of `K` lies over exactly one finite place of `k`: the one whose prime is
`𝔭_w ∩ 𝓞 k`. -/
private theorem existsUnique_finitePlace_liesOver {k K : Type*} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] (w : FinitePlace K) :
    ∃! v : FinitePlace k,
      (FinitePlace.maximalIdeal w).asIdeal.LiesOver (FinitePlace.maximalIdeal v).asIdeal := by
  refine ⟨FinitePlace.mk ((FinitePlace.maximalIdeal w).under (𝓞 k)), ?_, fun v h ↦ ?_⟩
  · beta_reduce
    rw [FinitePlace.maximalIdeal_mk]
    exact ⟨rfl⟩
  · rw [← FinitePlace.maximalIdeal_inj, FinitePlace.maximalIdeal_mk]
    exact HeightOneSpectrum.ext h.over

/-- An infinite place `w` of `K` lies over exactly one infinite place of `k`: its restriction. -/
private theorem existsUnique_infinitePlace_liesOver {k K : Type*} [Field k] [Field K]
    [Algebra k K] (w : InfinitePlace K) : ∃! v : InfinitePlace k, w.LiesOver v :=
  ⟨w.comap (algebraMap k K), ⟨rfl⟩, fun v _ ↦ (InfinitePlace.LiesOver.comap_eq w v).symm⟩

/-- Every place `w` of a number field `K` lies over exactly one place `v` of a number subfield
`k ⊆ K`. -/
@[faltings "lem_ht_place_lies_over_unique"]
theorem NumberFieldPlace.existsUnique_liesOver {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (w : NumberFieldPlace K) :
    ∃! v : NumberFieldPlace k, w.LiesOver v := by
  rcases w with w | w
  · obtain ⟨v, hv, huniq⟩ := existsUnique_finitePlace_liesOver (k := k) w
    refine ⟨.inl v, hv, ?_⟩
    rintro (v' | v') h
    exacts [congrArg _ (huniq v' h), h.elim]
  · obtain ⟨v, hv, huniq⟩ := existsUnique_infinitePlace_liesOver (k := k) w
    refine ⟨.inr v, hv, ?_⟩
    rintro (v' | v') h
    exacts [h.elim, congrArg _ (huniq v' h)]

end Faltings
