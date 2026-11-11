module

public import Mordell.BombieriVojta.Norm.ReducedRepresentation
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycleSupplement
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.Curve.Topology
public import Mordell.AlgebraicGeometry.NormalScheme.Order
public import Mordell.AlgebraicGeometry.NormalScheme.Integrality

/-!
# The zeros of the numerators `U_i`

Let `C` be a smooth proper geometrically integral curve of genus `g ≥ 2` over a field `k`, with a
divisor `P` of degree one, and let `X = C ×_k C` with projections `pr₁, pr₂` and diagonal `Δ`. Let
`B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` be very ample, `s ≥ 1`, let `y₀, …, yₘ` be a basis of
`H⁰(X, 𝒪(B))` giving the embedding `φ_B : X → ℙᵐ`, with divisors of zeros `Dᵢ`, and put
`ηᵢ = yᵢ / y₀`. Fix `N ≥ 2g + 1`, `n = N - g`, and a generic basis `x₀, …, xₙ` of
`H⁰(C, 𝒪(N P))` giving `φ_{NP} : C → ℙⁿ`, and assume the coordinates `y` generic for the
projections `π_{ab} = (ξ_a, ξ'_b) : X → ℙ¹ × ℙ¹`. For `1 ≤ a, b ≤ n` write
`Norm ηᵢ = Uᵢ / Vᵢ` in lowest terms in `R = k[ξ_a, ξ'_b]`.

Then for `i ≠ 0` and a point `p` of `𝔸¹ × 𝔸¹` with coordinates algebraic over `k`, `Uᵢ(p) = 0`
exactly when `yᵢ` vanishes at some point of `π_{ab}⁻¹(p)`. Indeed
`div (Uᵢ / Vᵢ) = π_* Dᵢ - π_* D₀`, and since `π_* Dᵢ` and `π_* D₀` have no common component
(genericity) while `Uᵢ` and `Vᵢ` are coprime, the affine zero divisor of `Uᵢ` is `π_* Dᵢ`, whose
support is `π(Dᵢ)`.

## Main results

* `Faltings.aeval_num_eq_zero_iff_of_isReducedNormRepresentation`: `U i` vanishes at `p` if and
  only if the zero divisor of `y i` passes through a point of `X` lying over `p`.
* `Faltings.exists_prime_dvd_mem`: in a factorial domain, a nonzero element of a prime ideal has
  a prime factor in it.
* `Faltings.exists_prime_comap_eq_span`: under an integral extension of a normal factorial domain
  `A`, a height-one prime lies over a principal prime of `A`.
* `Faltings.exists_mul_eq_or_inv`: the localization of a factorial domain at a principal prime is
  a valuation ring.

## Implementation notes

The data and hypotheses are those of `Faltings.degreeOf_num_eq_of_isReducedNormRepresentation`,
written in the same way: divisors through the order of vanishing `AlgebraicGeometry.Scheme.ord`
at codimension-one points, a section `y` of `𝒪(B)` as a rational function with
`div y + B ≥ 0` and divisor of zeros `div y + B`, and genericity on `X` over `k` through the
subfields `k(ξ_{a'}, ξ'_{b'})` of `k(X)`.

A point `p : Fin 2 → Ω` of `𝔸²`, for a field `Ω` algebraic over `k` (in the source `Ω = k̄`),
determines the maximal ideal `ker (aeval p)` of `R`. A point `q` of `X` lies over `p` when every
`r ∈ R` with `r(p) = 0` gives a rational function `r(ξ_a, ξ'_b)` vanishing at `q`. On the normal
scheme `X`, a rational function `h` vanishes at `q` when `h = 0`, or `ord_w h ≥ 0` at every
codimension-one `w` specialising to `q` and `ord_w h > 0` at one of them. The zero divisor `Dᵢ`
passes through `q` when it has a component through `q`. A `k̄`-point of `X` over `p` at which `yᵢ`
vanishes maps to such a scheme point `q`, and every such `q` is the image of a `k̄`-point over a
conjugate of `p`, hence (replacing the embedding of `κ(q)`) over `p`; so the two formulations
agree.

The proof works on the affine open `W = pr₁⁻¹ C₀ ∩ pr₂⁻¹ C₀` of `X`, where `C₀ = φ⁻¹ D₊(T₀)` is
the chart of `C` on which `ξ_a` is regular. Every point at which `ξ_a` is regular lies in `C₀`,
so `W` contains every point of `X` lying over `𝔸²`. By the valuative criterion on the proper
curve `C`, the ring `Γ(C₀)` is integral over `k[ξ_a]`. Since `Γ(W)` is the tensor product of two
copies of `Γ(C₀)` over `k`, the ring `B = Γ(W)` is a finite extension of `A = k[ξ_a, ξ'_b]`; it is
a Noetherian normal domain with fraction field `k(X)`.

On `B` the statement becomes commutative algebra. If `Uᵢ(p) = 0`, a prime factor `π` of `Uᵢ`
vanishing at `p` gives a height-one prime of `B` over `(π)` at which `ηᵢ` has a zero. Otherwise,
by algebraic Hartogs, `ηᵢ⁻¹` would be integral over `A_(π)`, and coprimality of `Uᵢ` and `Vᵢ`
would fail. Going up then gives the point over `p`. Conversely, if `Dᵢ` has a component `w`
through a point over `p`, then `w` lies over a principal prime `(π) ⊆ 𝔪_p` (by going down). By
the genericity hypothesis, no component of `D₀` lies over `(π)`. So `ηᵢ` is integral over `A_(π)`
and lies in the prime of `w`, its norm lies in `(π)`, and `π` divides `Uᵢ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order

universe u

section CommAlg

open IntermediateField

variable {A B K L : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]

omit [IsDomain A] in
/-- In a factorial domain, a nonzero element of a prime ideal has a prime factor in it. -/
public theorem exists_prime_dvd_mem [UniqueFactorizationMonoid A] {P : Ideal A} [hP : P.IsPrime]
    {x : A} (hx : x ≠ 0) (hxP : x ∈ P) : ∃ π : A, Prime π ∧ π ∣ x ∧ π ∈ P := by
  revert hx hxP
  refine UniqueFactorizationMonoid.induction_on_prime x (fun h => absurd rfl h) ?_ ?_
  · intro x hu _ hxP
    exact absurd (P.eq_top_of_isUnit_mem hxP hu) hP.ne_top
  · intro a π ha hπ ih _ hxP
    rcases hP.mem_or_mem hxP with h | h
    · exact ⟨π, hπ, dvd_mul_right _ _, h⟩
    · obtain ⟨π', h1, h2, h3⟩ := ih ha h
      exact ⟨π', h1, dvd_mul_of_dvd_right h2 _, h3⟩

/-- In a factorial domain, a nonzero prime ideal contained in the ideal generated by a prime `π`
is that ideal. -/
private theorem eq_span_of_le_span [UniqueFactorizationMonoid A] {π : A} (hπ : Prime π)
    {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) (hle : Q ≤ Ideal.span {π}) : Q = Ideal.span {π} := by
  refine le_antisymm hle ?_
  obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  obtain ⟨π', hπ', -, hπ'Q⟩ := exists_prime_dvd_mem hy0 hyQ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hle hπ'Q)
  have hu : IsUnit c := (hπ'.irreducible.isUnit_or_isUnit hc.symm).resolve_right hπ.not_isUnit
  rw [Ideal.span_singleton_le_iff_mem]
  have : π = ↑hu.unit⁻¹ * π' := by
    rw [← hc, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this]
  exact Q.mul_mem_left _ hπ'Q

/-- **Algebraic Hartogs over a height-one prime.** Let `B` be a Noetherian normal domain integral
over a factorial domain `A`, and `π` a prime of `A`. An element `h` of `Frac B` lying in `B_P` for
every height-one prime `P` of `B` over `(π)` lies in the localization of `B` at `A ∖ (π)`. -/
private theorem exists_mul_eq_of_forall_height_one [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [UniqueFactorizationMonoid A]
    (hinj : Function.Injective (algebraMap A B)) {π : A} (hπ : Prime π) {h : L}
    (hh : ∀ P : Ideal B, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A B) = Ideal.span {π} →
      ∃ a s : B, s ∉ P ∧ h * algebraMap B L s = algebraMap B L a) :
    ∃ (b : B) (t : A), t ∉ Ideal.span {π} ∧ h * algebraMap A L t = algebraMap B L b := by
  set z : Ideal A := Ideal.span {π}
  have hz : z.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  set M := Algebra.algebraMapSubmonoid B z.primeCompl
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht ?_
    rw [← map_zero (algebraMap A B)] at h0
    rw [hinj h0]
    exact z.zero_mem
  let Bz := Localization M
  have : IsDomain Bz := IsLocalization.isDomain_of_le_nonZeroDivisors (S := Bz) hM
  have : IsNoetherianRing Bz := IsLocalization.isNoetherianRing M Bz inferInstance
  have : IsIntegrallyClosed Bz := isIntegrallyClosed_of_isLocalization Bz M hM
  have hunit : ∀ m : M, IsUnit (algebraMap B L m) := fun m =>
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr
      (nonZeroDivisors.ne_zero (hM m.2)) |>.isUnit
  let : Algebra Bz L := (IsLocalization.lift (M := M) (S := Bz) hunit).toAlgebra
  have : IsScalarTower B Bz L := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq (M := M) (S := Bz) hunit b).symm
  have : IsFractionRing Bz L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Bz L
  obtain ⟨r, hr⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    (R := Bz) L (z := h) fun q hq => by
      set P := q.asIdeal.comap (algebraMap B Bz)
      have : P.IsPrime := Ideal.IsPrime.comap _
      have hPh : P.height = 1 := (IsLocalization.height_under M q.asIdeal).trans hq
      have hPz : P.comap (algebraMap A B) = z := by
        refine eq_span_of_le_span hπ ?_ ?_
        · intro h0
          exact Ideal.ne_bot_of_height_eq_one hPh (Ideal.eq_bot_of_comap_eq_bot h0)
        · intro a ha
          by_contra haz
          have hu : IsUnit (algebraMap B Bz (algebraMap A B a)) :=
            IsLocalization.map_units Bz (⟨algebraMap A B a, a, haz, rfl⟩ : M)
          exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
      obtain ⟨a, s, hs, has⟩ := hh P inferInstance hPh hPz
      refine ⟨algebraMap B Bz a, algebraMap B Bz s, hs, ?_⟩
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective M r
  obtain ⟨t, ht, hmt⟩ := m.2
  refine ⟨b, t, ht, ?_⟩
  have hspec := congrArg (algebraMap Bz L) (IsLocalization.mk'_spec Bz b m)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hmt,
    ← IsScalarTower.algebraMap_apply] at hspec
  rwa [← hr]

omit [IsDomain A] [IsDomain B] [IsFractionRing B L] in
/-- The norm of an element of `B` integral over the normal domain `A` comes from `A`. -/
private theorem exists_algebraMap_eq_norm [IsIntegrallyClosed A] [Algebra.IsIntegral A B]
    (b : B) : ∃ a : A, algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
  have hb : IsIntegral A (algebraMap B L b) :=
    (Algebra.IsIntegral.isIntegral b).map (IsScalarTower.toAlgHom A B L)
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hb)

omit [IsFractionRing B L] in
/-- The norm of an element of a prime `P` of `B` comes from an element of `P ∩ A`. -/
private theorem exists_mem_algebraMap_eq_norm [IsIntegrallyClosed A] [Algebra.IsIntegral A B]
    [FiniteDimensional K L] {P : Ideal B} [P.IsPrime] {b : B} (hb : b ∈ P) :
    ∃ a ∈ P.comap (algebraMap A B), algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
  set y := algebraMap B L b
  have hbi : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  set p := minpoly A b
  have hK : minpoly K y = p.map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hbi
  have hyK : IsIntegral K y :=
    ((hbi.map (IsScalarTower.toAlgHom A B L)).tower_top (A := K))
  have hgen : Algebra.norm K (IntermediateField.AdjoinSimple.gen K y) =
      (-1) ^ (minpoly K y).natDegree * (minpoly K y).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hyK)
    simpa [IntermediateField.adjoin.powerBasis, IntermediateField.minpoly_gen] using this
  have hc0 : p.coeff 0 ∈ P.comap (algebraMap A B) := by
    have h0 : Polynomial.aeval b p = 0 := minpoly.aeval A b
    have h2 := congrArg (Polynomial.aeval b) (Polynomial.X_mul_divX_add p)
    rw [h0, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
    rw [Ideal.mem_comap, eq_neg_of_add_eq_zero_right h2]
    exact P.neg_mem (P.mul_mem_right _ hb)
  have he : 0 < Module.finrank K⟮y⟯ L := Module.finrank_pos
  refine ⟨((-1) ^ p.natDegree * p.coeff 0) ^ Module.finrank K⟮y⟯ L,
    Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hc0) _ he, ?_⟩
  rw [Algebra.norm_eq_norm_adjoin K y, hgen, hK, Polynomial.coeff_map,
    (minpoly.monic hbi).natDegree_map]
  simp [p]

/-- Under an integral extension `A ⊆ B` with `A` factorial and normal, a height-one prime of `B`
lies over a principal prime `(π)` of `A`. -/
public theorem exists_prime_comap_eq_span [IsNoetherianRing A] [Algebra.IsIntegral A B]
    [UniqueFactorizationMonoid A] [IsIntegrallyClosed A] [FaithfulSMul A B] [IsNoetherianRing B]
    {P : Ideal B} [P.IsPrime] (hP : P.height = 1) :
    ∃ π : A, Prime π ∧ P.comap (algebraMap A B) = Ideal.span {π} := by
  set z := P.comap (algebraMap A B) with hzdef
  have : z.IsPrime := Ideal.IsPrime.comap _
  have hz0 : z ≠ ⊥ := fun h0 =>
    Ideal.ne_bot_of_height_eq_one hP (Ideal.eq_bot_of_comap_eq_bot h0)
  have : P.LiesOver z := ⟨rfl⟩
  have hzh : z.height ≤ 1 := by
    rw [← hP, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown z P]
    exact le_self_add
  obtain ⟨π, hπz, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hz0
  refine ⟨π, hπ, ?_⟩
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  refine (lt_or_eq_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hπz)).elim (fun hlt => ?_)
    Eq.symm
  exfalso
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (⊥ : Ideal A) < Ideal.span {π} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  rw [Ideal.height_bot] at h3
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (Ideal.span {π}).height + 1 := by gcongr
      _ ≤ z.height := h1
      _ ≤ 1 := hzh
  exact absurd this (by norm_num)

/-- The localization of a factorial domain at a principal prime `(π)` is a valuation ring: every
element `κ` of the fraction field lies in it, or has inverse in `π A_(π)`. -/
public theorem exists_mul_eq_or_inv [UniqueFactorizationMonoid A] {π : A} (hπ : Prime π)
    (κ : K) :
    (∃ a s : A, s ∉ Ideal.span {π} ∧ κ * algebraMap A K s = algebraMap A K a) ∨
      ∃ a s : A, a ∈ Ideal.span {π} ∧ s ∉ Ideal.span {π} ∧
        κ⁻¹ * algebraMap A K s = algebraMap A K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) κ
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hπK : algebraMap A K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπ.ne_zero
  have h1 : (1 : A) ∉ Ideal.span {π} := fun h =>
    hπ.not_isUnit (isUnit_of_dvd_one (Ideal.mem_span_singleton.mp h))
  by_cases ha0 : a = 0
  · exact Or.inl ⟨0, 1, h1, by simp [ha0]⟩
  obtain ⟨m, a', ha', rfl⟩ := WfDvdMonoid.max_power_factor ha0 hπ.irreducible
  obtain ⟨n, s', hs', rfl⟩ := WfDvdMonoid.max_power_factor hs0 hπ.irreducible
  have hs'0 : algebraMap A K s' ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ?_
    rintro rfl
    exact hs' (dvd_zero π)
  have ha'0 : algebraMap A K a' ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ?_
    rintro rfl
    exact ha' (dvd_zero π)
  rcases le_or_gt n m with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    left
    refine ⟨π ^ d * a', s', fun h' => hs' (Ideal.mem_span_singleton.mp h'), ?_⟩
    simp only [map_mul, map_pow]
    field_simp
    ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
    right
    have hd : d ≠ 0 := by omega
    refine ⟨π ^ d * s', a', ?_, fun h' => ha' (Ideal.mem_span_singleton.mp h'), ?_⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) _
        (Nat.pos_of_ne_zero hd))
    · simp only [map_mul, map_pow, inv_div]
      field_simp
      ring

/-- **Forward direction, algebraically.** If `N(η) = U / V` with `U, V` coprime and `U ∈ 𝔪`, then
some height-one prime `P` of `B` with `P ∩ A ⊆ 𝔪` has `η⁻¹ ∉ B_P`. -/
private theorem exists_height_one_of_mem [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [UniqueFactorizationMonoid A] [IsIntegrallyClosed A]
    (hinj : Function.Injective (algebraMap A B)) {U V : A} (hUV : IsRelPrime U V) (hV : V ≠ 0)
    {η : L} (hη : η ≠ 0)
    (hN : Algebra.norm K η = algebraMap A K U / algebraMap A K V) {𝔪 : Ideal A} [𝔪.IsPrime]
    (hU : U ∈ 𝔪) :
    ∃ P : Ideal B, P.IsPrime ∧ P.height = 1 ∧ P.comap (algebraMap A B) ≤ 𝔪 ∧
      ¬ ∃ a s : B, s ∉ P ∧ η⁻¹ * algebraMap B L s = algebraMap B L a := by
  have hVK : algebraMap A K V ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hV
  have hU0 : U ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hN
    by_cases hfin : FiniteDimensional K L
    · exact hη (Algebra.norm_eq_zero_iff.mp hN)
    · rw [Algebra.norm_eq_one_of_not_module_finite hfin] at hN
      exact one_ne_zero hN
  have hUK : algebraMap A K U ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hU0
  obtain ⟨π, hπ, hπU, hπ𝔪⟩ := exists_prime_dvd_mem hU0 hU
  by_contra hcon
  push Not at hcon
  obtain ⟨b, t, ht, hbt⟩ := exists_mul_eq_of_forall_height_one (L := L) hinj hπ
    (h := η⁻¹) fun P hP hP1 hPz => by
      have hle : P.comap (algebraMap A B) ≤ 𝔪 := by
        rwa [hPz, Ideal.span_singleton_le_iff_mem]
      exact hcon P hP hP1 hle
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_norm (A := A) (K := K) (L := L) b
  have hinv : Algebra.norm K η⁻¹ = (Algebra.norm K η)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hη, map_one])
  have hnorm := congrArg (Algebra.norm K) hbt
  rw [map_mul, ← ha, IsScalarTower.algebraMap_apply A K L, Algebra.norm_algebraMap, hinv,
    hN, inv_div] at hnorm
  have hA : V * t ^ Module.finrank K L = U * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, map_mul, map_pow, ← hnorm]
    field_simp
  have hπV : π ∣ V := by
    have : π ∣ V * t ^ Module.finrank K L := hA ▸ dvd_mul_of_dvd_left hπU a
    rcases hπ.dvd_or_dvd this with h | h
    · exact h
    · exact absurd (Ideal.mem_span_singleton.mpr (hπ.dvd_of_dvd_pow h)) ht
  exact hπ.not_isUnit (hUV hπU hπV)

/-- **Backward direction, algebraically.** Let `P` be a height-one prime of `B` with `η ∈ P B_P`,
such that `η ∈ B_{P'}` for every height-one prime `P'` with `P' ∩ A = P ∩ A`. If
`N(η) = U / V`, then `U ∈ P ∩ A`. -/
private theorem mem_comap_of_height_one [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [UniqueFactorizationMonoid A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [FaithfulSMul A B] [FiniteDimensional K L] {U V : A} (hV : V ≠ 0)
    {η : L}
    (hN : Algebra.norm K η = algebraMap A K U / algebraMap A K V) {P : Ideal B} [P.IsPrime]
    (hP : P.height = 1)
    (hηP : ∃ c t : B, c ∈ P ∧ t ∉ P ∧ η * algebraMap B L t = algebraMap B L c)
    (hall : ∀ P' : Ideal B, P'.IsPrime → P'.height = 1 →
      P'.comap (algebraMap A B) = P.comap (algebraMap A B) →
      ∃ a s : B, s ∉ P' ∧ η * algebraMap B L s = algebraMap B L a) :
    U ∈ P.comap (algebraMap A B) := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  obtain ⟨π, hπ, hzπ⟩ := exists_prime_comap_eq_span (A := A) hP
  set z := P.comap (algebraMap A B) with hzdef
  have : z.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨b, t, ht, hbt⟩ := exists_mul_eq_of_forall_height_one (L := L) hinj hπ (h := η)
    fun P' hP' hP'1 hP'z => hall P' hP' hP'1 (hP'z.trans hzπ.symm)
  rw [← hzπ] at ht
  obtain ⟨c, t', hc, ht', hct⟩ := hηP
  have hbP : b ∈ P := by
    have h1 : b * t' = c * algebraMap A B t := by
      apply IsFractionRing.injective B L
      rw [map_mul, map_mul, ← hbt, ← hct, ← IsScalarTower.algebraMap_apply]
      ring
    have h2 : b * t' ∈ P := h1 ▸ P.mul_mem_right _ hc
    exact (Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_right ht'
  obtain ⟨a, haz, ha⟩ := exists_mem_algebraMap_eq_norm (A := A) (K := K) (L := L) hbP
  have hnorm := congrArg (Algebra.norm K) hbt
  rw [map_mul, ← ha, IsScalarTower.algebraMap_apply A K L, Algebra.norm_algebraMap, hN] at hnorm
  have hVK : algebraMap A K V ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hV
  have hA : U * t ^ Module.finrank K L = V * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, map_mul, map_pow, ← hnorm]
    field_simp
  have hmem : U * t ^ Module.finrank K L ∈ z := hA ▸ z.mul_mem_left _ haz
  rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
  · exact h
  · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h) ht

end CommAlg

set_option linter.unusedVariables false in
attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical BombieriSiegel in
/-- **The zeros of the numerators `Uᵢ`** (Bombieri). In the setting of
`Faltings.degreeOf_num_eq_of_isReducedNormRepresentation` (a curve `C` of genus `≥ 2`,
`X = C ×_k C`, the basis `y` of `H⁰(X, 𝒪(B))` generic for the projections and the generic
basis `x` of `H⁰(C, 𝒪(N P))`), let `a, b ≠ 0` and let `(U, V)` be a family of reduced
representations of the norms of `ηᵢ = y i / y 0` from `k(X)` to `k(ξ_a, ξ'_b)`. Then for
`i ≠ 0` and `p : Fin 2 → Ω` with `Ω` algebraic over `k`, `U i` vanishes at `p` if and only if
the zero divisor `Dᵢ = div (f i) + B` passes through a point `q` of `X` lying over `p` under
`π_{ab}`. -/
@[faltings "lem_bvr_norm_eta_zeros"]
public theorem aeval_num_eq_zero_iff_of_isReducedNormRepresentation (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ AlgebraicGeometry.genus f)
    -- the divisor `P₁` of degree one on `C`
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * AlgebraicGeometry.genus f + 1 ≤ N)
    {n : ℕ} (hn : n = N - AlgebraicGeometry.genus f) (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    -- (N): the basis `x` is generic
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (hG3 : SatisfiesG3 k f x)
    -- the product `X = C ×_k C` with its projections and diagonal
    {X : Scheme.{u}} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) [IsIntegral X]
    [IsLocallyNoetherian X] (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    -- the embedding `φ_{NP}` given by `x`
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k C.functionField] (hkC : ‹Algebra k C.functionField› = functionFieldAlgebra k f)
    [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB) {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (B : X → ℤ) (hB : ∀ w : X, B w =
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hD : ∀ i (w : X), 0 ≤ X.ord (y i) w + B w)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : X.functionField, (∀ w : X, 0 ≤ X.ord h w + B w) →
      h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ w : X, Order.coheight w = 1 → ∃ i, X.ord (y i) w + B w = 0)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k))) [IsClosedImmersion φB]
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of X.functionField)).inv.hom))
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w' : X,
      0 < X.ord (y i) w + B w → 0 < X.ord (y 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i j : Fin (m + 1),
      i.val = 1 → j.val = 2 → ∀ w w' : X, 0 < X.ord (y i) w + B w →
      0 < X.ord (y j) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w : X,
      0 < X.ord (y i) w + B w →
      0 ≤ X.ord (ι₁ (x a' / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b' / x 0)) w)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ q : X,
        (∀ r ∈ 𝔪,
          (∀ w, w ⤳ q → Order.coheight w = 1 →
            0 ≤ X.ord (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) ∧
          (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r = 0 ∨
            ∃ w, w ⤳ q ∧ Order.coheight w = 1 ∧
              0 < X.ord (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w)) →
        ∀ w, w ⤳ q → Order.coheight w = 1 → X.ord (y i) w + B w = 0)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    {K : Type u} [Field K] [Algebra (MvPolynomial (Fin 2) k) K]
    [IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => y i / y 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0)
    {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] (p : Fin 2 → Ω) :
    MvPolynomial.aeval p (U i) = 0 ↔ ∃ q : X,
      (∀ r : MvPolynomial (Fin 2) k, MvPolynomial.aeval p r = 0 →
        (∀ w, w ⤳ q → Order.coheight w = 1 →
          0 ≤ X.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) w) ∧
        (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r = 0 ∨
          ∃ w, w ⤳ q ∧ Order.coheight w = 1 ∧
            0 < X.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) w)) ∧
      ∃ w, w ⤳ q ∧ Order.coheight w = 1 ∧ 0 < X.ord (y i) w + B w := by
  classical
  subst hkC
  let : Algebra k C.functionField := functionFieldAlgebra k f
  have hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  set f₀ := f with hf₀
  have : IsProper f₀ := (instIsProperVarietyOfIsProjectiveVariety k f₀).toIsProper
  have : IsNormal C := isNormal_of_smooth_over_field f₀
  -- the divisor `E = N P₁`, the basis `x` in `L(E)`, and (G1) at codimension-one points
  set E : C → ℤ := ⇑((N : ℤ) • P₁) with hEdef
  have hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z :=
    ord_add_nonneg_of_span_eq f (isClosed_of_mem_support_smul hP₁cl _) hli hspan
  have hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0 := by
    intro a ha z hz
    have h := hG1 a ha z (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f
      fun h => FunctionField.coheight_genericPoint_ne_one C (h ▸ hz))
    have h0 := hxE 0 z
    have ha' := hxE a z
    rw [hEdef] at h0 ha' ⊢
    omega
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hX.flip inferInstance
  have : Smooth pr₂ := MorphismProperty.of_isPullback (P := @Smooth) hX inferInstance
  have : LocallyOfFiniteType pr₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX.flip inferInstance
  have : IsNormal X := isNormal_of_smooth_over_field (pr₁ ≫ f₀)
  have hx0 : ∀ j, x j ≠ 0 := hli.ne_zero
  -- the chart `C₀ = φ⁻¹ D₊(T₀)` of `C`, containing the generic point
  obtain ⟨hη₀, hξ₀⟩ := BombieriRoth.exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  set C₀ : C.Opens := φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)) with hC₀def
  have hC₀ne : Nonempty C₀ := ⟨⟨_, hη₀⟩⟩
  have hC₀ : IsAffineOpen C₀ :=
    (ProjectiveSpace.isAffineOpen_standardOpen n (Spec (.of k)) 0).preimage φNP
  have hchart : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ c : C,
      x a' / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₀ :=
    fun a' ha' c hc => mem_preimage_basicOpen_of_mem_range f₀ E x hx0 hxE φNP hφNPx
      (hNG1 a' ha') hc
  have hint : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ s : Γ(C, C₀), C.germToFunctionField C₀ s ∈
      integralClosure (Algebra.adjoin k {x a' / x 0}) C.functionField :=
    fun a' ha' => germToFunctionField_mem_integralClosure f₀ hkC _ C₀ (hchart a' ha')
  -- the sections `ξ_j = x j / x 0` over `C₀`
  set sec : Fin (n + 1) → Γ(C, C₀) := fun j => φNP.app _
    ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
          (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X _ j)))) with hsecdef
  have hsec : ∀ j, C.germToFunctionField C₀ (sec j) = x j / x 0 := hξ₀
  -- the affine open `W = π_{ab}⁻¹(𝔸²)` of `X` and its ring of sections `Γ(X, W)`
  set W : X.Opens := pr₁ ⁻¹ᵁ C₀ ⊓ pr₂ ⁻¹ᵁ C₀ with hWdef
  have hC₀top : C₀ ≤ f₀ ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  have hW : IsAffineOpen W :=
    isAffineOpen_of_isPullback hX (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top hC₀top hWdef
  have hWne : Nonempty W := by
    obtain ⟨c, hc⟩ : (C₀ : Set C).Nonempty := ⟨_, hη₀⟩
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := f₀) c c rfl
    refine ⟨⟨hX.isoPullback.inv z, ?_, ?_⟩⟩
    · change pr₁ (hX.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_fst, hz1]
      exact hc
    · change pr₂ (hX.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_snd, hz2]
      exact hc
  have : Nonempty (pr₁ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.1⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.2⟩⟩
  have : IsDomain Γ(X, W) := IsIntegral.component_integral W
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : IsIntegrallyClosed Γ(X, W) :=
    (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨W, hW⟩ inferInstance
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  have hBL : ∀ b : Γ(X, W), algebraMap Γ(X, W) X.functionField b = X.germToFunctionField W b :=
    fun _ => rfl
  have : Nonempty (⊤ : X.Opens) := ⟨⟨hWne.some.1, trivial⟩⟩
  -- germs of restricted sections
  have hgermLE : ∀ {V : X.Opens} [Nonempty V] (h : W ≤ V) (t : Γ(X, V)),
      X.germToFunctionField W (X.presheaf.map (homOfLE h).op t) = X.germToFunctionField V t :=
    fun h t => X.presheaf.germ_res_apply (homOfLE h) _ _ t
  -- the constants
  set κ : k →+* Γ(X, W) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (pr₁ ≫ f₀).appLE ⊤ W (fun _ _ => trivial)).hom with hκdef
  have hκ : ∀ c, algebraMap Γ(X, W) X.functionField (κ c) = algebraMap k X.functionField c := by
    intro c
    rw [hkX c, hBL]
    exact hgermLE le_top _
  -- the generators `ξ_a`, `ξ'_b` of `Γ(X, W)` over `k`
  have hpr₁ : ∀ s : Γ(C, C₀),
      algebraMap Γ(X, W) X.functionField (pr₁.appLE C₀ W inf_le_left s) =
        ι₁ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₁ C₀ s, hBL]
    exact hgermLE inf_le_left _
  have hpr₂ : ∀ s : Γ(C, C₀),
      algebraMap Γ(X, W) X.functionField (pr₂.appLE C₀ W inf_le_right s) =
        ι₂ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₂ C₀ s, hBL]
    exact hgermLE inf_le_right _
  set ta := pr₁.appLE C₀ W inf_le_left (sec a)
  set tb := pr₂.appLE C₀ W inf_le_right (sec b)
  let : Algebra (MvPolynomial (Fin 2) k) Γ(X, W) := (MvPolynomial.eval₂Hom κ ![ta, tb]).toAlgebra
  have hRBa : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 0) = ta :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBb : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 1) = tb :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBc : ∀ c, algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.C c) = κ c :=
    fun c => MvPolynomial.eval₂Hom_C _ _ _
  have hRBL : algebraMap (MvPolynomial (Fin 2) k) X.functionField =
      (algebraMap Γ(X, W) X.functionField).comp (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
        algebraMap Γ(X, W) X.functionField
          (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.C c))
      rw [hRBc, hRL₀, hκ]
    · fin_cases j
      · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
          algebraMap Γ(X, W) X.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 0))
        rw [hRBa, hRLa, hpr₁, hsec]
      · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
          algebraMap Γ(X, W) X.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 1))
        rw [hRBb, hRLb, hpr₂, hsec]
  have : IsScalarTower (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [hRBL]; rfl
  have hRL_inj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k) X.functionField) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 2) k) K X.functionField]
    exact (algebraMap K X.functionField).injective.comp
      (IsFractionRing.injective (MvPolynomial (Fin 2) k) K)
  have hRB_inj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) := by
    intro r r' h
    apply hRL_inj
    rw [hRBL, RingHom.comp_apply, RingHom.comp_apply, h]
  have : FaithfulSMul (MvPolynomial (Fin 2) k) Γ(X, W) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin 2) k) Γ(X, W)).mpr hRB_inj
  -- `Γ(X, W)` is integral over `(MvPolynomial (Fin 2) k)`
  have hintOf : ∀ (ι' : C.functionField →ₐ[k] X.functionField) (a' : Fin (n + 1)), a' ≠ 0 →
      ∀ j : Fin 2, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X j) =
        ι' (x a' / x 0) → ∀ t : Γ(C, C₀) → Γ(X, W),
      (∀ s, algebraMap Γ(X, W) X.functionField (t s) = ι' (C.germToFunctionField C₀ s)) →
      ∀ s, IsIntegral (MvPolynomial (Fin 2) k) (t s) := by
    intro ι' a' ha' j hj t ht s
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField)
      (IsFractionRing.injective Γ(X, W) X.functionField)).mp ?_
    change IsIntegral _ (algebraMap Γ(X, W) X.functionField (t s))
    rw [ht]
    exact isIntegral_map_of_mem_integralClosure ι' _ ⟨_, hj⟩ (fun c => ⟨_, hRL₀ c⟩)
      (hint a' ha' s)
  have : Algebra.IsIntegral (MvPolynomial (Fin 2) k) Γ(X, W) := ⟨fun y => mem_of_isPushout
    (isPushout_appLE_of_isPullback_inter hX (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top
      hC₀top hWdef inf_le_left inf_le_right)
    (integralClosure (MvPolynomial (Fin 2) k) Γ(X, W)).toSubring
    (hintOf ι₁ a ha 0 hRLa _ hpr₁) (hintOf ι₂ b hb 1 hRLb _ hpr₂) y⟩
  -- `Γ(X, W)` is finite over `(MvPolynomial (Fin 2) k)`, so `X.functionField` is finite over `K`
  let : Algebra k Γ(X, W) := κ.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin 2) k) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun c => (hRBc c).symm
  have : Algebra.FiniteType k Γ(X, W) := by
    have h1 := (pr₁ ≫ f₀).finiteType_appLE (isAffineOpen_top (Spec (.of k))) hW
      (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ fun y =>
        ⟨(Scheme.ΓSpecIso (.of k)).hom y, by simp⟩
    exact h1.comp h2
  have : Algebra.FiniteType (MvPolynomial (Fin 2) k) Γ(X, W) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 2) k) Γ(X, W)
  have : Module.Finite (MvPolynomial (Fin 2) k) Γ(X, W) := Algebra.IsIntegral.finite
  have : FiniteDimensional K X.functionField :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin 2) k) Γ(X, W) (Rₚ := K)
      (Sₚ := X.functionField) (nonZeroDivisors (MvPolynomial (Fin 2) k))
  -- the maximal ideal of `p`
  set 𝔪 : Ideal (MvPolynomial (Fin 2) k) :=
    RingHom.ker (MvPolynomial.aeval p : (MvPolynomial (Fin 2) k) →ₐ[k] Ω) with h𝔪def
  have h𝔪 : 𝔪.IsMaximal := isMaximal_ker_aeval p
  -- the norm of `η = y i / y 0`
  set η : X.functionField := y i / y 0 with hηdef
  have hη0 : η ≠ 0 := div_ne_zero (hy i) (hy 0)
  have hN : Algebra.norm K η =
      algebraMap (MvPolynomial (Fin 2) k) K (U i) / algebraMap (MvPolynomial (Fin 2) k) K (V i) :=
    hU.algebraNorm_eq_div i
  have hAL : ∀ r : (MvPolynomial (Fin 2) k),
      MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r =
        algebraMap (MvPolynomial (Fin 2) k) X.functionField r := by
    intro r
    have : (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] :
        (MvPolynomial (Fin 2) k) →ₐ[k] X.functionField).toRingHom =
          algebraMap (MvPolynomial (Fin 2) k) X.functionField := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [hRL₀]
      · fin_cases j
        · simp [hRLa]
        · simp [hRLb]
    exact congr($this r)
  constructor
  · -- `U i (p) = 0`: a height-one prime of `B` where `η` has a pole lies under a point over `p`
    intro hUp
    have hU𝔪 : U i ∈ 𝔪 := hUp
    obtain ⟨P, hPp, hP1, hP𝔪, hPη⟩ := exists_height_one_of_mem (A := MvPolynomial (Fin 2) k)
      (B := Γ(X, W)) (K := K) (L := X.functionField) hRB_inj (hU.isRelPrime i) (hU.ne_zero i)
      hη0 hN hU𝔪
    obtain ⟨Q, hPQ, hQp, hQ𝔪⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔪 P hP𝔪
    obtain ⟨w, hwW, hwP⟩ := exists_primeIdealOf_eq hW ⟨P, hPp⟩
    obtain ⟨q, hqW, hqQ⟩ := exists_primeIdealOf_eq hW ⟨Q, hQp⟩
    have hwq : w ⤳ q := (specializes_iff_primeIdealOf_le hW hwW hqW).mpr (by
      rw [hwP, hqQ]; exact hPQ)
    have hw1 : coheight w = 1 := by
      rw [coheight_eq_height_primeIdealOf hW hwW, hwP]; exact hP1
    refine ⟨q, fun r hr => ?_, w, hwq, hw1, ?_⟩
    · rw [hAL r]
      have hrQ : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r ∈ Q := by
        rw [← Ideal.mem_comap, ← Ideal.under_def, hQ𝔪]
        exact hr
      obtain ⟨t, ht, htr⟩ := (mem_maximalIdeal_stalk_iff hW hqW
        (algebraMap (MvPolynomial (Fin 2) k) X.functionField r)).mpr
        ⟨algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r, 1, by rw [hqQ]; exact hrQ,
          by rw [hqQ]; exact fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h),
          by rw [map_one, mul_one, hRBL]; rfl⟩
      exact (exists_mem_maximalIdeal_iff_ord q _).mpr ⟨t, ht, htr⟩
    · have hnot : η⁻¹ ∉ Set.range (algebraMap (X.presheaf.stalk w) X.functionField) := by
        rw [mem_range_stalk_iff hW hwW, hwP]
        exact hPη
      have hneg : X.ord η⁻¹ w < 0 := by
        by_contra hc
        push Not at hc
        exact hnot ((ord_nonneg_iff hw1 (inv_ne_zero hη0)).mp hc)
      rw [hηdef, inv_div, ord_div (hy 0) (hy i)] at hneg
      have := hD 0 w
      omega
  · -- a point `q` over `p` with `Dᵢ` through it: `U i` vanishes at the image of a component
    rintro ⟨q, hq, w, hwq, hw1, hwD⟩
    -- the constants in the local rings
    have hconst : ∀ y : X, (algebraMap (X.presheaf.stalk y) X.functionField).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (pr₁ ≫ f₀).appTop ≫
          X.presheaf.germ ⊤ y trivial).hom = algebraMap k X.functionField := by
      intro y
      ext c
      rw [hkX c]
      exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := ⊤) (x := y) trivial _
    -- `ξ_a` and `ξ'_b` are regular at `q`, hence `q` lies in `W`
    have hreg := mem_range_stalk_of_forall_aeval _ hconst p _ q fun r hr => (hq r hr).1
    have hqW : q ∈ W :=
      ⟨hchart a ha _ (mem_range_stalk_of_map_mem_range f₀ pr₁ ι₁.toRingHom hι₁ q (hreg 0)),
        hchart b hb _ (mem_range_stalk_of_map_mem_range f₀ pr₂ ι₂.toRingHom hι₂ q (hreg 1))⟩
    -- the prime `Q` of `q` lies over `𝔪`
    set Q := (hW.primeIdealOf ⟨q, hqW⟩).asIdeal with hQdef
    have h𝔪Q : 𝔪 ≤ Q.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) := by
      intro r hr
      have hvan := hq r hr
      rw [hAL r] at hvan
      obtain ⟨a', s', ha', hs', has'⟩ := (mem_maximalIdeal_stalk_iff hW hqW _).mp
        ((exists_mem_maximalIdeal_iff_ord q _).mp hvan)
      have hrs : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r * s' = a' := by
        apply IsFractionRing.injective Γ(X, W) X.functionField
        rwa [map_mul, ← RingHom.comp_apply, ← hRBL]
      have hmem' : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r * s' ∈ Q := hrs ▸ ha'
      exact (Ideal.IsPrime.mem_or_mem inferInstance hmem').resolve_right hs'
    have hQ𝔪 : Q.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) = 𝔪 :=
      (h𝔪.eq_of_le (Ideal.IsPrime.comap _).ne_top h𝔪Q).symm
    -- the prime `P` of `w`, of height one, under `Q`
    have hwW : w ∈ W := hwq.mem_open W.isOpen hqW
    set P := (hW.primeIdealOf ⟨w, hwW⟩).asIdeal with hPdef
    have hP1 : P.height = 1 := by rw [← coheight_eq_height_primeIdealOf hW hwW]; exact hw1
    have hPQ : P ≤ Q := (specializes_iff_primeIdealOf_le hW hwW hqW).mp hwq
    obtain ⟨π, hπ, hzπ⟩ := exists_prime_comap_eq_span (A := MvPolynomial (Fin 2) k)
      (B := Γ(X, W)) hP1
    -- `D₀` does not pass through `w`, so `η` vanishes at `w`
    have hw0 : X.ord (y 0) w + B w = 0 := by
      by_contra h
      have hpos : 0 < X.ord (y 0) w + B w := lt_of_le_of_ne (hD 0 w) (Ne.symm h)
      obtain ⟨r, -, hr1, hr2⟩ := hBG1 a b ha hb i hi w w hwD hpos
      omega
    have hηP : ∃ c t : Γ(X, W), c ∈ P ∧ t ∉ P ∧
        η * algebraMap Γ(X, W) X.functionField t = algebraMap Γ(X, W) X.functionField c := by
      have hpos : 0 < X.ord η w := by
        rw [hηdef, ord_div (hy i) (hy 0)]
        omega
      exact (mem_maximalIdeal_stalk_iff hW hwW η).mp ((ord_pos_iff hw1 hη0).mp hpos)
    -- the subfield `k(ξ_a, ξ'_b)` is the image of `K`
    have hadj : ∀ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
        ∃ κ' : K, algebraMap K X.functionField κ' = r := by
      let S : IntermediateField k X.functionField :=
        (algebraMap K X.functionField).fieldRange.toIntermediateField fun c =>
          ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.C c), by
            rw [← IsScalarTower.algebraMap_apply, hRL₀]⟩
      have hle : IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)} ≤ S := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ (rfl | rfl)
        · exact ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0), by
            rw [← IsScalarTower.algebraMap_apply, hRLa]⟩
        · exact ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 1), by
            rw [← IsScalarTower.algebraMap_apply, hRLb]⟩
      exact fun _ hr => hle hr
    -- every height-one prime over `P ∩ A` misses `D₀`, so `η` is regular there
    have hall : ∀ P' : Ideal Γ(X, W), P'.IsPrime → P'.height = 1 →
        P'.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) =
          P.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) →
        ∃ a' s' : Γ(X, W), s' ∉ P' ∧
          η * algebraMap Γ(X, W) X.functionField s' = algebraMap Γ(X, W) X.functionField a' := by
      intro P' hP' hP'1 hP'z
      obtain ⟨w', hw'W, hw'P⟩ := exists_primeIdealOf_eq hW ⟨P', hP'⟩
      have hw'1 : coheight w' = 1 := by
        rw [coheight_eq_height_primeIdealOf hW hw'W, hw'P]; exact hP'1
      have hw'0 : X.ord (y 0) w' + B w' = 0 := by
        by_contra h
        have hpos : 0 < X.ord (y 0) w' + B w' := lt_of_le_of_ne (hD 0 w') (Ne.symm h)
        obtain ⟨r, hrK, hr1, hr2⟩ := hBG1 a b ha hb i hi w w' hwD hpos
        obtain ⟨κ', rfl⟩ := hadj r hrK
        have hr0 : algebraMap K X.functionField κ' ≠ 0 := fun h0 => by
          rw [h0] at hr2
          simp at hr2
        rcases exists_mul_eq_or_inv (K := K) hπ κ' with ⟨a₁, s₁, hs₁, h₁⟩ | ⟨a₁, s₁, ha₁, hs₁, h₁⟩
        · have hs₁P' : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) s₁ ∉ P' := fun h =>
            hs₁ (by rw [← hzπ, ← hP'z]; exact h)
          have hmem : algebraMap K X.functionField κ' ∈
              Set.range (algebraMap (X.presheaf.stalk w') X.functionField) := by
            refine (mem_range_stalk_iff hW hw'W _).mpr ⟨algebraMap _ Γ(X, W) a₁,
              algebraMap _ Γ(X, W) s₁, by rw [hw'P]; exact hs₁P', ?_⟩
            have h₂ := congrArg (algebraMap K X.functionField) h₁
            rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
              hRBL, RingHom.comp_apply, RingHom.comp_apply] at h₂
            exact h₂
          have := (ord_nonneg_iff hw'1 hr0).mpr hmem
          omega
        · have hs₁P : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) s₁ ∉ P := fun h =>
            hs₁ (by rw [← hzπ]; exact h)
          have ha₁P : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) a₁ ∈ P := by
            rwa [← hzπ] at ha₁
          have hmem : ∃ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w),
              algebraMap (X.presheaf.stalk w) X.functionField t =
                (algebraMap K X.functionField κ')⁻¹ := by
            refine (mem_maximalIdeal_stalk_iff hW hwW _).mpr ⟨algebraMap _ Γ(X, W) a₁,
              algebraMap _ Γ(X, W) s₁, ha₁P, hs₁P, ?_⟩
            have h₂ := congrArg (algebraMap K X.functionField) h₁
            rw [map_mul, map_inv₀, ← IsScalarTower.algebraMap_apply,
              ← IsScalarTower.algebraMap_apply, hRBL, RingHom.comp_apply,
              RingHom.comp_apply] at h₂
            exact h₂
          have hpos := (ord_pos_iff hw1 (inv_ne_zero hr0)).mpr hmem
          rw [Stacks.Chow.ord_inv_eq_neg' hr0 (inv_ne_zero hr0) (mul_inv_cancel₀ hr0)] at hpos
          omega
      have hnn : 0 ≤ X.ord η w' := by
        rw [hηdef, ord_div (hy i) (hy 0)]
        have := hD i w'
        omega
      have := (ord_nonneg_iff hw'1 hη0).mp hnn
      rwa [mem_range_stalk_iff hW hw'W, hw'P] at this
    have hUP := mem_comap_of_height_one (A := MvPolynomial (Fin 2) k) (B := Γ(X, W)) (K := K)
      (L := X.functionField) (hU.ne_zero i) hN hP1 hηP hall
    exact (hQ𝔪 ▸ Ideal.comap_mono hPQ hUP : U i ∈ 𝔪)

end Faltings
