module

public import Mordell.FunctionField.LocalRingAtZero
public import StacksFrontier.RingTheory.KrullAkizuki.IntermediateRingNoetherian

/-!
# The semilocal ring over the zero of a transcendental element

Let `F/K` be a field extension and let `z ∈ F` be transcendental over `K`, with local ring
`R_z = Faltings.FunctionField.localRingAtZero hz ⊆ F` at the zero of `z`. The ring `S_z` is the
integral closure of `R_z` in `F`: the set of elements of `F` that are integral over `R_z`.
When `F/K` is a function field, `S_z` is a semilocal Dedekind domain whose maximal ideals
correspond to the zeros of `z`.

## Main definitions

* `Faltings.FunctionField.semilocalRing`: the `R_z`-subalgebra `S_z` of `F`.

## Implementation notes

`S_z` is Mathlib's `integralClosure` of `R_z` in `F`, an `R_z`-subalgebra of `F` (so the
inclusion `R_z → S_z` is its structure map); it is an `abbrev`, so all of Mathlib's API on
`integralClosure` applies directly. It carries the chapter's standing hypothesis that `F/K` is
a function field (`[Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]`),
as `localRingAtZero` does.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. Proposition 1.1.6
  and the proof of Theorem 3.2.6
-/

@[expose] public section

namespace Faltings.FunctionField

/-- The integral closure `S_z` of the local ring `R_z = localRingAtZero hz` in `F`, for `z ∈ F`
transcendental over `K`: the elements of `F` integral over `R_z`, as an `R_z`-subalgebra of `F`. -/
@[faltings "def_ff_semilocal_ring"]
abbrev semilocalRing {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] {z : F}
    (hz : Transcendental K z) : Subalgebra (localRingAtZero hz) F :=
  integralClosure (localRingAtZero hz) F

end Faltings.FunctionField

end

/-!
# Common denominators for the semilocal ring over the zero of a transcendental element

Let `F/K` be a function field and `z ∈ F` transcendental over `K`, with local ring
`R_z = Faltings.FunctionField.localRingAtZero hz` at the zero of `z` and its integral closure
`S_z = Faltings.FunctionField.semilocalRing hz` in `F`. Every `a ∈ F` is a quotient `s / r` with
`s ∈ S_z` and `0 ≠ r ∈ R_z`: since `F/K(z)` is finite, `a` satisfies a monic equation over
`K(z) = Frac R_z`, and multiplying `a` by a common denominator `r` of its coefficients makes
`r a` integral over `R_z`.

## Main results

* `Faltings.FunctionField.exists_mem_semilocalRing_eq_div`: every `a ∈ F` is `s / r` with
  `s ∈ S_z` and `r ∈ R_z` nonzero.

## Implementation notes

This is the instance for `R_z ⊆ F` of the general fact that an element algebraic over the
fraction field of a domain `R` has a nonzero multiple from `R` that is integral over `R`
(cf. Mathlib's `exists_integral_multiple`).

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. Proposition 1.1.6
  and the proof of Theorem 3.2.6
-/

public section

namespace Faltings.FunctionField

open IntermediateField

/-- Every element of a function field `F/K` is algebraic over the local ring `R_z` at the zero
of a transcendental `z`: it is algebraic over `K(z)`, the fraction field of `R_z`. -/
private lemma isAlgebraic_localRingAtZero {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) (a : F) : IsAlgebraic (localRingAtZero hz) a := by
  have := FunctionField.finiteDimensional_of_adjoin_transcendental hz
  obtain ⟨-, -, hle, _⟩ := isDiscreteValuationRing_localRingAtZero hz
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (localRingAtZero hz) K⟮z⟯ F := .of_algebraMap_eq fun _ => rfl
  exact (IsFractionRing.isAlgebraic_iff _ K⟮z⟯ F).mpr (Algebra.IsAlgebraic.isAlgebraic a)

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, every `a ∈ F` can be
written `a = s / r` with `s` in the semilocal ring `semilocalRing hz` and `r` a nonzero element
of the local ring `localRingAtZero hz`. -/
@[faltings "lem_ff_semilocal_fraction"]
theorem exists_mem_semilocalRing_eq_div {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) (a : F) :
    ∃ s ∈ semilocalRing hz, ∃ r ∈ localRingAtZero hz, r ≠ 0 ∧ a = s / r := by
  obtain ⟨y, hy, hint⟩ := (isAlgebraic_localRingAtZero hz a).exists_integral_multiple
  have hy' : (y : F) ≠ 0 := by simpa using hy
  exact ⟨y • a, hint, y, y.2, hy', (mul_div_cancel_left₀ a hy').symm⟩

end Faltings.FunctionField

end

/-!
# The semilocal ring over the zero of a transcendental element is Noetherian

Let `F/K` be a function field and `z ∈ F` transcendental over `K`, with local ring
`R_z = Faltings.FunctionField.localRingAtZero hz` at the zero of `z` and its integral closure
`S_z = Faltings.FunctionField.semilocalRing hz` in `F`. Then `S_z` is a Noetherian domain.
It is a domain as a subring of the field `F`; it is Noetherian by the Krull–Akizuki theorem,
since `R_z` is a discrete valuation ring with fraction field `K(z)` and `F/K(z)` is finite.

## Main results

* `Faltings.FunctionField.isNoetherianRing_semilocalRing`: `S_z` is a domain and a Noetherian
  ring.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. the proof of
  Theorem 3.2.6
-/

public section

namespace Faltings.FunctionField

open IntermediateField

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, the semilocal ring
`semilocalRing hz` (the integral closure of `localRingAtZero hz` in `F`) is a Noetherian
domain. -/
@[faltings "lem_ff_semilocal_noetherian"]
theorem isNoetherianRing_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    IsDomain (semilocalRing hz) ∧ IsNoetherianRing (semilocalRing hz) := by
  refine ⟨inferInstance, ?_⟩
  have : FiniteDimensional K⟮z⟯ F := FunctionField.finiteDimensional_of_adjoin_transcendental hz
  obtain ⟨_, -, hle, _⟩ := isDiscreteValuationRing_localRingAtZero hz
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower (localRingAtZero hz) K⟮z⟯ F := .of_algebraMap_eq' rfl
  exact krull_akizuki (localRingAtZero hz) K⟮z⟯ F
    (IsDiscreteValuationRing.ringKrullDim_eq_one _) (semilocalRing hz).toSubring
    (by rintro _ ⟨r, rfl⟩; exact isIntegral_algebraMap)

end Faltings.FunctionField

end

/-!
# The semilocal ring over the zero of a transcendental element has dimension one

Let `F/K` be a function field and `z ∈ F` transcendental over `K`, with local ring
`R_z = Faltings.FunctionField.localRingAtZero hz` and its integral closure
`S_z = Faltings.FunctionField.semilocalRing hz` in `F`. Then the Krull dimension of `S_z` is
one: `S_z` is integral over the discrete valuation ring `R_z`, so it has dimension at most one,
and it is not a field because a domain integral over a non-field is not a field.

## Main results

* `Faltings.FunctionField.ringKrullDim_semilocalRing`: `ringKrullDim S_z = 1`.

## References

* [The Stacks project][stacks-project], Tag 00OK
-/

public section

namespace Faltings.FunctionField

/-- A domain of dimension at most one that is not a field has Krull dimension exactly one. -/
private lemma ringKrullDim_eq_one_of_not_isField {R : Type*} [CommRing R] [IsDomain R]
    [Ring.DimensionLEOne R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  refine le_antisymm (Ring.krullDimLE_iff.mp inferInstance) ?_
  by_contra h1
  have : Ring.KrullDimLE 0 R :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast Order.le_of_lt_succ (not_le.mp h1))
  exact h Ring.KrullDimLE.isField_of_isDomain

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, the semilocal ring
`semilocalRing hz` (the integral closure of `localRingAtZero hz` in `F`) has Krull dimension
one. -/
@[faltings "lem_ff_semilocal_dim_one"]
theorem ringKrullDim_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    ringKrullDim (semilocalRing hz) = 1 := by
  have := (isDiscreteValuationRing_localRingAtZero hz).1
  have : Ring.DimensionLEOne (semilocalRing hz) :=
    Ring.DimensionLEOne.of_isIntegral (R := localRingAtZero hz) _
  have hinj : Function.Injective (algebraMap (localRingAtZero hz) (semilocalRing hz)) :=
    fun _ _ h => Subtype.ext congr($h.1)
  exact ringKrullDim_eq_one_of_not_isField fun h =>
    IsDiscreteValuationRing.not_isField _ (isField_of_isIntegral_of_isField hinj h)

end Faltings.FunctionField

end

/-!
# The semilocal ring `S_z` is normal

Let `F/K` be a function field and let `z ∈ F` be transcendental over `K`. The integral closure
`S_z = Faltings.FunctionField.semilocalRing hz` of the local ring `R_z` in `F` is a normal
domain whose fraction field is `F`: every element of `F` is a quotient of elements of `S_z`,
and an element of `F` integral over `S_z` is integral over `R_z` by transitivity, hence lies
in `S_z`.

## Main results

* `Faltings.FunctionField.isFractionRing_semilocalRing`: `F` is the fraction field of `S_z`,
  and `S_z` is integrally closed.

## Implementation notes

"Normal domain with fraction field `F`" is stated as `IsFractionRing S_z F` together with
`IsIntegrallyClosed S_z`; that `S_z` is a domain is an instance (it is a subring of a field).

## References

* [Stacks Project, Tag 00GN](https://stacks.math.columbia.edu/tag/00GN)
-/

public section

namespace Faltings.FunctionField

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, then `F` is the
fraction field of the semilocal ring `semilocalRing hz`, and `semilocalRing hz` is integrally
closed (a normal domain). -/
@[faltings "lem_ff_semilocal_normal"]
theorem isFractionRing_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    IsFractionRing (semilocalRing hz) F ∧ IsIntegrallyClosed (semilocalRing hz) := by
  have : IsFractionRing (semilocalRing hz) F := .of_field _ _ fun a => by
    obtain ⟨s, hs, r, hr, -, rfl⟩ := exists_mem_semilocalRing_eq_div hz a
    exact ⟨⟨s, hs⟩, ⟨r, (semilocalRing hz).algebraMap_mem ⟨r, hr⟩⟩, rfl⟩
  exact ⟨this, (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mpr inferInstance⟩

end Faltings.FunctionField

end

/-!
# Maximal ideals of the semilocal ring over a zero of `z` contain `z`

Let `F/K` be a function field and `z ∈ F` transcendental over `K`. The semilocal ring
`S_z = Faltings.FunctionField.semilocalRing hz` is the integral closure in `F` of the local ring
`R_z = Faltings.FunctionField.localRingAtZero hz`. Since `S_z` is integral over `R_z`, every
maximal ideal of `S_z` contracts to the maximal ideal `z R_z` of `R_z`; in particular it contains
`z`.

## Main results

* `Faltings.FunctionField.exists_mem_of_isMaximal_semilocalRing`: `z ∈ S_z`, and `z` lies in
  every maximal ideal of `S_z`.

## References

* [The Stacks Project, Tag 00GR][stacks-project]
-/

public section

namespace Faltings.FunctionField

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, then `z` lies in the
semilocal ring `semilocalRing hz` and in every maximal ideal of it. -/
@[faltings "lem_ff_semilocal_max_contains_z"]
theorem exists_mem_of_isMaximal_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) (M : Ideal (semilocalRing hz)) [M.IsMaximal] :
    ∃ h : z ∈ semilocalRing hz, (⟨z, h⟩ : semilocalRing hz) ∈ M := by
  obtain ⟨_, ⟨hzR, hmax⟩, -⟩ := isDiscreteValuationRing_localRingAtZero hz
  refine ⟨(algebraMap (localRingAtZero hz) (semilocalRing hz) ⟨z, hzR⟩).2, ?_⟩
  show algebraMap (localRingAtZero hz) (semilocalRing hz) ⟨z, hzR⟩ ∈ M
  -- `M ∩ R_z` is maximal since `S_z` is integral over `R_z`, so it is the maximal ideal `z R_z`
  rw [← Ideal.mem_comap,
    IsLocalRing.eq_maximalIdeal (show (M.comap (algebraMap (localRingAtZero hz)
      (semilocalRing hz))).IsMaximal from Ideal.isMaximal_under_of_isIntegral_of_isMaximal M),
    ← IsLocalRing.eq_maximalIdeal hmax]
  exact Ideal.subset_span rfl

end Faltings.FunctionField

end

/-!
# Nonzero primes of the semilocal ring over the zero of a transcendental element are maximal

Let `F/K` be a function field and `z ∈ F` transcendental over `K`, with local ring
`R_z = Faltings.FunctionField.localRingAtZero hz` and its integral closure
`S_z = Faltings.FunctionField.semilocalRing hz` in `F`. Then every nonzero prime ideal of `S_z`
is maximal: `S_z` is integral over the discrete valuation ring `R_z`, and dimension at most one
ascends along integral extensions.

## Main results

* `Faltings.FunctionField.dimensionLEOne_semilocalRing`: `S_z` satisfies
  `Ring.DimensionLEOne`, i.e. every nonzero prime ideal of `S_z` is maximal.

## Implementation notes

The conclusion is stated as Mathlib's class `Ring.DimensionLEOne`, whose one field
`Ring.DimensionLEOne.maximalOfPrime` is literally the assertion that every nonzero prime ideal is
maximal; `Ideal.IsPrime.isMaximal` then gives the statement for a given prime.

## References

* [The Stacks project][stacks-project], Tag 00OK
-/

public section

namespace Faltings.FunctionField

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, every nonzero prime
ideal of `semilocalRing hz` (the integral closure of `localRingAtZero hz` in `F`) is maximal:
`semilocalRing hz` is integral over the discrete valuation ring `localRingAtZero hz`. -/
@[faltings "lem_ff_semilocal_prime_maximal"]
theorem dimensionLEOne_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    Ring.DimensionLEOne (semilocalRing hz) :=
  have := (isDiscreteValuationRing_localRingAtZero hz).1
  Ring.DimensionLEOne.of_isIntegral (R := localRingAtZero hz) _

end Faltings.FunctionField

end

/-!
# The ring `S_z` is semilocal

Let `F/K` be a function field and `z ∈ F` transcendental over `K`. The ring
`S_z = Faltings.FunctionField.semilocalRing hz`, the integral closure in `F` of the local ring
`R_z = Faltings.FunctionField.localRingAtZero hz`, has only finitely many maximal ideals: they are
exactly the primes containing `z S_z`, i.e. the minimal primes of the Noetherian ring
`S_z / z S_z`.

## Main results

* `Faltings.FunctionField.finite_maximalSpectrum_semilocalRing`: the maximal spectrum of `S_z` is
  finite.

## Implementation notes

"Finitely many maximal ideals" is stated as `Finite (MaximalSpectrum S_z)`, Mathlib's type of
maximal ideals; it is equivalent to finiteness of `{M : Ideal S_z | M.IsMaximal}`.

## References

* [The Stacks Project, Tag 00FR][stacks-project]
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. Theorem 3.2.6
-/

public section

namespace Faltings.FunctionField

/-- In a Noetherian ring of dimension at most one, if a nonzero element `x` lies in every maximal
ideal, then there are only finitely many maximal ideals: each one is a minimal prime over `(x)`,
since every prime between `(x)` and it is nonzero, hence maximal. -/
private lemma finite_maximalSpectrum_of_mem_all {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] {x : R} (hx : x ≠ 0) (hmem : ∀ M : Ideal R, M.IsMaximal → x ∈ M) :
    Finite (MaximalSpectrum R) := by
  have : Finite (Ideal.span {x}).minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R _).to_subtype
  refine Finite.of_injective (fun M => (⟨M.asIdeal, ?_⟩ : (Ideal.span {x}).minimalPrimes))
    fun M N h => MaximalSpectrum.ext congr($h.1)
  have hxM := (Ideal.span_singleton_le_iff_mem _).2 (hmem _ M.isMaximal)
  refine ⟨⟨M.isMaximal.isPrime, hxM⟩, fun P ⟨hP, hxP⟩ hPM => ?_⟩
  have hP0 : P ≠ ⊥ := fun hb => hx (by simpa [hb] using hxP (Ideal.mem_span_singleton_self x))
  exact ((hP.isMaximal hP0).eq_of_le M.isMaximal.ne_top hPM).ge

/-- If `F/K` is a function field and `z ∈ F` is transcendental over `K`, then the semilocal ring
`semilocalRing hz` has only finitely many maximal ideals. -/
@[faltings "lem_ff_semilocal_finitely_many_max"]
theorem finite_maximalSpectrum_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    Finite (MaximalSpectrum (semilocalRing hz)) := by
  have := (isNoetherianRing_semilocalRing hz).2
  have := dimensionLEOne_semilocalRing hz
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (semilocalRing hz)
  obtain ⟨hzS, -⟩ := exists_mem_of_isMaximal_semilocalRing hz M₀
  exact finite_maximalSpectrum_of_mem_all (x := ⟨z, hzS⟩) (fun h => hz.ne_zero congr($h.1))
    fun M _ => (exists_mem_of_isMaximal_semilocalRing hz M).2

end Faltings.FunctionField

end

/-!
# Localizations of the semilocal ring at its maximal ideals are discrete valuation rings

Let `F/K` be a function field, `z ∈ F` transcendental over `K`, and
`S_z = Faltings.FunctionField.semilocalRing hz` the integral closure in `F` of the local ring
`R_z = Faltings.FunctionField.localRingAtZero hz` at the zero of `z`. For every maximal ideal
`𝔫` of `S_z`, the localization `(S_z)_𝔫`, viewed inside `F`, is a discrete valuation ring
whose fraction field is `F`.

## Main results

* `Faltings.FunctionField.isDiscreteValuationRing_localization_semilocalRing`: any
  localization `Sₙ` of `semilocalRing hz` at a maximal ideal `𝔫`, carrying an `Sₙ`-algebra
  structure on `F` compatible with `semilocalRing hz ⊆ F`, is a discrete valuation ring and
  `F` is a fraction field of `Sₙ`.

## Implementation notes

The localization is taken abstractly, as any `Sₙ` with `IsLocalization.AtPrime Sₙ 𝔫`, in the
style of `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`. The inclusion
`(S_z)_𝔫 ⊆ F` is the `Sₙ`-algebra structure on `F` subject to `IsScalarTower`, which by the
universal property of localization pins it to the canonical extension of `S_z ⊆ F`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. the proof of
  Theorem 3.2.6
-/

public section

namespace Faltings.FunctionField

/-- The semilocal ring `S_z` is a Dedekind domain: it is Noetherian, integrally closed, and of
Krull dimension one. -/
private lemma isDedekindDomain_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) : IsDedekindDomain (semilocalRing hz) := by
  have := (isNoetherianRing_semilocalRing hz).2
  have := (isFractionRing_semilocalRing hz).2
  have : Ring.KrullDimLE 1 (semilocalRing hz) :=
    Ring.krullDimLE_iff.mpr (ringKrullDim_semilocalRing hz).le
  have : Ring.DimensionLEOne (semilocalRing hz) :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  exact { }

/-- A maximal ideal of `S_z` is nonzero, since it contains the nonzero element `z`. -/
private lemma ne_bot_of_isMaximal_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsMaximal] :
    𝔫 ≠ ⊥ := by
  obtain ⟨_, hzn⟩ := exists_mem_of_isMaximal_semilocalRing hz 𝔫
  rintro rfl
  exact hz.ne_zero congr($((Ideal.mem_bot).mp hzn).1)

/-- If `F/K` is a function field, `z ∈ F` is transcendental over `K` and `𝔫` is a maximal ideal
of `semilocalRing hz`, then the localization `Sₙ` of `semilocalRing hz` at `𝔫`, with its
induced embedding in `F`, is a discrete valuation ring with fraction field `F`. -/
@[faltings "lem_ff_semilocal_ring"]
theorem isDiscreteValuationRing_localization_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsMaximal]
    (Sₙ : Type*) [CommRing Sₙ] [IsDomain Sₙ] [Algebra (semilocalRing hz) Sₙ]
    [IsLocalization.AtPrime Sₙ 𝔫] [Algebra Sₙ F] [IsScalarTower (semilocalRing hz) Sₙ F] :
    IsDiscreteValuationRing Sₙ ∧ IsFractionRing Sₙ F :=
  have := isDedekindDomain_semilocalRing hz
  have := (isFractionRing_semilocalRing hz).1
  ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _
      (ne_bot_of_isMaximal_semilocalRing hz 𝔫) Sₙ,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔫.primeCompl Sₙ F⟩

end Faltings.FunctionField

end
