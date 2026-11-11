module

public import Mathlib
public import Mordell.Attr
public import Mordell.NumberField.DifferentBound

/-!
# Extensions unramified outside a finite set of places

Let `k` be a number field and `S` a finite set of finite places of `k`, i.e. of nonzero primes of
`𝓞 k`. A finite extension `L / k` is *unramified outside `S`* if every nonzero prime `𝔓` of `𝓞 L`
lying over a prime `𝔭 ∉ S` of `𝓞 k` has ramification index `e(𝔓 | 𝔭) = 1`.

## Main definitions

* `Faltings.IsUnramifiedOutside`: `L / k` is unramified outside the finite set `S` of finite
  places.

## Implementation notes

The finite places of `k` are the elements of `IsDedekindDomain.HeightOneSpectrum (𝓞 k)`, and `S`
is a `Finset` of them. The prime `𝔓 ∩ 𝓞 k` is expressed through `Ideal.LiesOver`, and the
ramification index is `Ideal.ramificationIdx`. The extension is not required to sit inside a
fixed algebraic closure `k̄`: an intermediate field of `k̄ / k` is an instance of the definition.
Since residue fields of number fields are finite, hence perfect, the condition at a prime `𝔭` is
equivalent to `Algebra.IsUnramifiedIn (𝓞 L) 𝔭` by
`Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one`.

## References

* J. S. Milne, *Algebraic Number Theory*, Theorem 8.42
-/

@[expose] public section

namespace Faltings

open NumberField IsDedekindDomain in
/-- A finite extension `L / k` of a number field `k` is *unramified outside* a finite set `S` of
finite places of `k` if every nonzero prime `𝔓` of `𝓞 L` lying over a prime `𝔭 ∉ S` of `𝓞 k`
has ramification index `e(𝔓 | 𝔭) = 1`. -/
@[faltings "def_mw_unramified_outside"]
def IsUnramifiedOutside (k L : Type*) [Field k] [NumberField k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (S : Finset (HeightOneSpectrum (𝓞 k))) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → ∀ w : HeightOneSpectrum (𝓞 L),
    w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 k) = 1

end Faltings

/-!
# A uniform discriminant bound for extensions unramified outside `S`

Let `k` be a number field, `S` a finite set of finite places of `k` and `N ≥ 1` a natural number.
There is a bound `B` such that every finite extension `L / k` of degree `[L : k] ≤ N` which is
unramified outside `S` has `|d_L| ≤ B`. This is the step from which the Hermite–Minkowski
theorem (finitely many such `L`) follows by Hermite's finiteness theorem
`NumberField.finite_of_discr_bdd`.

The proof follows Neukirch. Put `n₀ = N [k : ℚ]` and `M = |d_k| · ∏_{𝔭 ∈ S} N 𝔭`. Every
prime `𝔓` of `𝓞 L` dividing the different `𝔇_L` lies over a rational prime `p ∣ M`: a prime
with `e(𝔓 | p) = 1` does not divide `𝔇_L` by Hensel's bound
`Faltings.count_normalizedFactors_differentIdeal_le`, while `e(𝔓 | p) > 1` forces either
`e(𝔓 | 𝔭) > 1`, so `𝔭 ∈ S`, or `e(𝔭 | p) > 1`, so `p ∣ d_k`. Hensel's bound and
`v_p(e) ≤ e ≤ [L : ℚ] ≤ n₀` give `ord_𝔓 𝔇_L ≤ (n₀ + 1) e(𝔓 | p) = ord_𝔓 (p ^ (n₀ + 1))`, so
`𝔇_L ∣ M ^ (n₀ + 1)` and `|d_L| = N(𝔇_L) ≤ N(M ^ (n₀ + 1)) ≤ M ^ ((n₀ + 1) n₀)`.

## Main results

* `Faltings.exists_discr_le_of_isUnramifiedOutside`: the uniform bound on `|d_L|`.

## Implementation notes

The source multiplies the local bounds over the primes above each `p`, using
`∑_{𝔓 ∣ p} e f = [L : ℚ]`; here the same local bounds are packaged as the divisibility
`𝔇_L ∣ M ^ (n₀ + 1)`, whose norm is computed directly.

The extension `L` is an arbitrary field with a finite `k`-algebra structure, not necessarily a
subfield of a fixed algebraic closure of `k`; intermediate fields of `k̄ / k` are instances. Such
an `L` is a number field by `NumberField.of_module_finite`, which supplies the instance under
which `NumberField.discr L` is formed. The degree bound is `Module.finrank k L ≤ N`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, Theorem 2.13
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.5
-/

@[expose] public section

open NumberField IsDedekindDomain UniqueFactorizationMonoid Ideal

namespace Faltings

/-- The ramification index of a nonzero prime of `𝓞 L` over `ℤ` is at most `[L : ℚ]`. -/
private lemma ramificationIdx_le_finrank (L : Type*) [Field L] [NumberField L] (p : ℕ)
    [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.ramificationIdx ℤ ≤ Module.finrank ℚ L := by
  classical
  let q : (span {(p : ℤ)}).primesOver (𝓞 L) := ⟨P, inferInstance, inferInstance⟩
  have : Fintype ((span {(p : ℤ)}).primesOver (𝓞 L)) := Fintype.ofFinite _
  rw [← RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank (span {(p : ℤ)}) (𝓞 L)]
  calc P.ramificationIdx ℤ ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
        Nat.le_mul_of_pos_right _ (inertiaDeg_pos ..)
    _ ≤ _ := Finset.single_le_sum (f := fun q : (span {(p : ℤ)}).primesOver (𝓞 L) =>
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)

/-- A prime `𝔓` of `𝓞 L` over `p` that is ramified over `ℤ` lies over a prime of `S` or over a
prime `p` dividing `d_k`; in either case `p` divides `|d_k| · ∏_{𝔭 ∈ S} N 𝔭`. -/
private lemma dvd_of_ramificationIdx_ne_one (k : Type*) [Field k] [NumberField k]
    (S : Finset (HeightOneSpectrum (𝓞 k))) (L : Type*) [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] (hS : IsUnramifiedOutside k L S) (p : ℕ) [hp : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (hP : P ≠ ⊥)
    (he : P.ramificationIdx ℤ ≠ 1) :
    p ∣ (discr k).natAbs * ∏ v ∈ S, absNorm v.asIdeal := by
  set 𝔭 : Ideal (𝓞 k) := P.under (𝓞 k)
  have h𝔭 : 𝔭 ≠ ⊥ := fun h => hP (eq_bot_of_comap_eq_bot h)
  have : 𝔭.LiesOver (span {(p : ℤ)}) := LiesOver.tower_bot P 𝔭 _
  let v : HeightOneSpectrum (𝓞 k) := ⟨𝔭, inferInstance, h𝔭⟩
  by_cases hv : v ∈ S
  · refine Dvd.dvd.mul_left ((dvd_pow_self p (inertiaDeg_pos 𝔭 ℤ).ne').trans ?_) _
    have h := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 k) => absNorm v.asIdeal) hv
    rw [pow_inertiaDeg p 𝔭]
    exact h
  · have h1 : P.ramificationIdx (𝓞 k) = 1 :=
      hS v hv ⟨P, inferInstance, hP⟩ (inferInstanceAs (P.LiesOver 𝔭))
    refine Dvd.dvd.mul_right ?_ _
    by_contra hd
    rw [← Int.natCast_dvd] at hd
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have hun := (not_dvd_discr_iff_forall_liesOver k (𝓞 k) hpz).mp hd 𝔭
      (IsPrime.isMaximal inferInstance h𝔭) inferInstance
    have h2 : 𝔭.ramificationIdx ℤ = 1 := ramificationIdx_eq_one 𝔭 ℤ
    exact he (by rw [ramificationIdx_tower 𝔭 P, h1, h2])

/-- `|d_k| · ∏_{𝔭 ∈ S} N 𝔭` is nonzero. -/
private lemma discr_natAbs_mul_prod_absNorm_ne_zero (k : Type*) [Field k] [NumberField k]
    (S : Finset (HeightOneSpectrum (𝓞 k))) :
    (discr k).natAbs * ∏ v ∈ S, absNorm v.asIdeal ≠ 0 :=
  mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero k))
    (Finset.prod_ne_zero_iff.mpr fun v _ => absNorm_eq_zero_iff.not.mpr v.ne_bot)

/-- Hensel's bound `ord_𝔓 𝔇_L ≤ e · v_p(e) + e - 1`, with `e = e(𝔓 | p)` the ramification index
over `ℤ`. -/
private lemma count_differentIdeal_le (L : Type*) [Field L] [NumberField L] (p : ℕ)
    [hp : Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Multiset.count P (normalizedFactors (differentIdeal ℤ (𝓞 L))) ≤
      P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + P.ramificationIdx ℤ - 1 := by
  have hp0 : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.out.ne_zero
  simpa only [ramificationIdx'_eq_ramificationIdx _ _ hp0] using
    count_normalizedFactors_differentIdeal_le L p P

/-- A prime of `𝓞 L` unramified over `ℤ` does not divide the different. -/
private lemma notMem_normalizedFactors_differentIdeal (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (he : P.ramificationIdx ℤ = 1) : P ∉ normalizedFactors (differentIdeal ℤ (𝓞 L)) := by
  simpa [he] using count_differentIdeal_le L p P

/-- The local bound `ord_𝔓 𝔇_L ≤ ([L : ℚ] + 1) · e(𝔓 | p)`. -/
private lemma count_differentIdeal_le_mul (L : Type*) [Field L] [NumberField L] (p : ℕ)
    [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Multiset.count P (normalizedFactors (differentIdeal ℤ (𝓞 L))) ≤
      (Module.finrank ℚ L + 1) * P.ramificationIdx ℤ := by
  have hv : padicValNat p (P.ramificationIdx ℤ) ≤ Module.finrank ℚ L :=
    (Nat.padicValNat_le_self _).trans (ramificationIdx_le_finrank L p P)
  calc _ ≤ _ := count_differentIdeal_le L p P
    _ ≤ P.ramificationIdx ℤ * Module.finrank ℚ L + P.ramificationIdx ℤ := by
      grw [Nat.sub_le, hv]
    _ = _ := by ring

/-- If `p ∣ m ≠ 0`, a prime `𝔓` of `𝓞 L` over `p` occurs in `m 𝓞 L` at least `e(𝔓 | p)` times. -/
private lemma ramificationIdx_le_count_span_natCast (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [hp : Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    {m : ℕ} (hm : m ≠ 0) (hpm : p ∣ m) :
    P.ramificationIdx ℤ ≤ Multiset.count P (normalizedFactors (span {(m : 𝓞 L)})) := by
  have hmap : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 L)) = span {(p : 𝓞 L)} := by
    simp [Ideal.map_span]
  have hpL : span {(p : 𝓞 L)} ≠ ⊥ := by simpa using hp.out.ne_zero
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ (hmap ▸ hpL), hmap]
  refine Multiset.count_le_of_le P ((dvd_iff_normalizedFactors_le_normalizedFactors hpL
    (by simpa using hm)).mp ?_)
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact Nat.cast_dvd_cast hpm

/-- If `L / k` is unramified outside `S` and `[L : ℚ] ≤ n₀`, then the different of `L` divides
`M ^ (n₀ + 1)`, where `M = |d_k| · ∏_{𝔭 ∈ S} N 𝔭`. -/
private lemma differentIdeal_dvd (k : Type*) [Field k] [NumberField k]
    (S : Finset (HeightOneSpectrum (𝓞 k))) (L : Type*) [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] (hS : IsUnramifiedOutside k L S) (n₀ : ℕ)
    (hn : Module.finrank ℚ L ≤ n₀) :
    differentIdeal ℤ (𝓞 L) ∣
      span {((((discr k).natAbs * ∏ v ∈ S, absNorm v.asIdeal) ^ (n₀ + 1) : ℕ) : 𝓞 L)} := by
  classical
  have hM := discr_natAbs_mul_prod_absNorm_ne_zero k S
  rw [Nat.cast_pow, ← span_singleton_pow,
    dvd_iff_normalizedFactors_le_normalizedFactors differentIdeal_ne_bot
      (pow_ne_zero _ (by rwa [Ne, zero_eq_bot, span_singleton_eq_bot, Nat.cast_eq_zero])),
    normalizedFactors_pow, Multiset.le_iff_count]
  intro P
  by_cases hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 L))
  swap
  · simp [Multiset.count_eq_zero.mpr hmem]
  have hPp := prime_of_normalized_factor P hmem
  have : P.IsPrime := isPrime_of_prime hPp
  have : NeZero P := ⟨hPp.ne_zero⟩
  set p := absNorm (under ℤ P)
  have : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
  have he : P.ramificationIdx ℤ ≠ 1 := fun he =>
    notMem_normalizedFactors_differentIdeal L p P he hmem
  rw [Multiset.count_nsmul]
  calc _ ≤ (Module.finrank ℚ L + 1) * P.ramificationIdx ℤ := count_differentIdeal_le_mul L p P
    _ ≤ (n₀ + 1) * _ := by gcongr
    _ ≤ _ := Nat.mul_le_mul_left _ (ramificationIdx_le_count_span_natCast L p P hM
        (dvd_of_ramificationIdx_ne_one k S L hS p P hPp.ne_zero he))

/-- The norm of the principal ideal generated by a natural number `m` in `𝓞 L` is `m ^ [L : ℚ]`. -/
private lemma absNorm_span_natCast (L : Type*) [Field L] [NumberField L] (m : ℕ) :
    absNorm (span {(m : 𝓞 L)}) = m ^ Module.finrank ℚ L := by
  have h : span {(m : 𝓞 L)} = (span {(m : ℤ)}).map (algebraMap ℤ (𝓞 L)) := by
    simp [Ideal.map_span]
  rw [h, absNorm_algebraMap, ← RingOfIntegers.rank]
  simp [Ideal.absNorm_span_singleton]

/-- If the different of `L` divides `m 𝓞 L` with `m ≠ 0` and `[L : ℚ] ≤ n`, then
`|d_L| ≤ m ^ n`. -/
private lemma natAbs_discr_le_of_differentIdeal_dvd (L : Type*) [Field L] [NumberField L]
    {m n : ℕ} (hm : m ≠ 0) (hn : Module.finrank ℚ L ≤ n)
    (h : differentIdeal ℤ (𝓞 L) ∣ span {(m : 𝓞 L)}) : (discr L).natAbs ≤ m ^ n := by
  rw [← absNorm_differentIdeal L (𝓞 L)]
  calc _ ≤ absNorm (span {(m : 𝓞 L)}) := Nat.le_of_dvd
        (by rw [absNorm_span_natCast]; positivity) (absNorm_dvd_absNorm_of_le (dvd_iff_le.mp h))
    _ ≤ m ^ n := (absNorm_span_natCast L m).trans_le (Nat.pow_le_pow_right (by omega) hn)

/-- **Uniform discriminant bound.** For a number field `k`, a finite set `S` of finite places of
`k` and `N ≥ 1`, there is `B > 0` such that every finite extension `L / k` with
`[L : k] ≤ N` that is unramified outside `S` has `|d_L| ≤ B`; one may take
`B = M ^ ((n₀ + 1) n₀)` with `n₀ = N [k : ℚ]` and `M = |d_k| · ∏_{𝔭 ∈ S} N 𝔭`. -/
@[faltings "lem_mw_discriminant_bound"]
theorem exists_discr_le_of_isUnramifiedOutside (k : Type*) [Field k] [NumberField k]
    (S : Finset (HeightOneSpectrum (𝓞 k))) (N : ℕ) (hN : 1 ≤ N) :
    ∃ B : ℕ, 0 < B ∧ ∀ (L : Type*) [Field L] [Algebra k L] [FiniteDimensional k L],
      Module.finrank k L ≤ N → IsUnramifiedOutside k L S →
        haveI : NumberField L := NumberField.of_module_finite k L
        |discr L| ≤ B := by
  have hM := pow_ne_zero (N * Module.finrank ℚ k + 1) (discr_natAbs_mul_prod_absNorm_ne_zero k S)
  refine ⟨_, pow_pos (Nat.pos_of_ne_zero hM) (N * Module.finrank ℚ k), fun L _ _ _ hL hS => ?_⟩
  let : NumberField L := NumberField.of_module_finite k L
  have hn : Module.finrank ℚ L ≤ N * Module.finrank ℚ k := by
    rw [← Module.finrank_mul_finrank ℚ k L, mul_comm]
    exact Nat.mul_le_mul_right _ hL
  rw [Int.abs_eq_natAbs]
  exact_mod_cast natAbs_discr_le_of_differentIdeal_dvd L hM hn (differentIdeal_dvd k S L hS _ hn)

end Faltings
