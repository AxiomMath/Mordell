module

public import Mordell.FunctionField.Place.Basic
public import Mordell.FunctionField.SemilocalRing

/-!
# The places at which a transcendental element vanishes

Let `F/K` be a function field and `z ∈ F` transcendental over `K`, with semilocal ring
`S_z = Faltings.FunctionField.semilocalRing hz ⊆ F`. For a maximal ideal `𝔫` of `S_z`, the
localization `(S_z)_𝔫`, viewed inside `F` as `{a / b : a, b ∈ S_z, b ∉ 𝔫}`, is a place of `F/K`
at which `z` vanishes, and every place `v` with `z ∈ 𝔪_v` arises in this way from exactly one `𝔫`.

## Main results

* `Faltings.FunctionField.exists_equiv_maximalSpectrum_semilocalRing`: an equivalence between the
  maximal spectrum of `S_z` and the places `v` of `F/K` with `z ∈ v.maximalIdeal`, sending `𝔫` to
  the place whose valuation ring is `(S_z)_𝔫 ⊆ F`.

## Implementation notes

The localization `(S_z)_𝔫` is described as the subset `{a / b : a, b ∈ S_z, b ∉ 𝔫}` of `F`, the
image of `Localization.AtPrime 𝔫` under the canonical map to the fraction field `F`; a place is
determined by its carrier, so this characterisation pins the equivalence.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], cf. Theorems 3.2.6
  and 3.2.7
* [The Stacks Project, Tag 00I9][stacks-project]
-/

public section

/- Instance search for `Algebra (semilocalRing hz) (locSub hz 𝔫)` otherwise tries
`NormedAlgebra.toAlgebra` on the subrings of `F` and enumerates every seminorm on `F` before
failing: it is switched off in this file. -/
attribute [-instance] NormedAlgebra.toAlgebra

namespace Faltings.FunctionField

open Polynomial

/-- In a valuation subring, a nonzero `x` is a nonunit iff `x⁻¹ ∉ A`. -/
private lemma mem_nonunits_iff_inv_not_mem {F : Type*} [Field F] (A : ValuationSubring F)
    {x : F} (hx : x ≠ 0) : x ∈ A.nonunits ↔ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff, ← A.valuation_le_one_iff, not_le,
    Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

/-- A nonunit of a valuation subring lies in it. -/
private lemma mem_of_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F) {x : F}
    (hx : x ∈ A.nonunits) : x ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff] at hx
  exact (A.valuation_le_one_iff x).mp hx.le

/-- The nonunits of a valuation subring absorb multiplication by its elements. -/
private lemma mul_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F) {x y : F}
    (hx : x ∈ A) (hy : y ∈ A.nonunits) : x * y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hy ⊢
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff x).mpr hx)) hy

/-- The inverse of a unit of a valuation subring lies in it. -/
private lemma inv_mem_of_not_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F)
    {x : F} (hx : x ∈ A) (hxn : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  have hx0 : x ≠ 0 := fun h => hxn (h ▸ zero_mem A.nonunits)
  by_contra h
  exact hxn ((mem_nonunits_iff_inv_not_mem A hx0).mpr h)

/-- A quotient `a / b` of elements of a valuation subring, `b` a unit, lies in it. -/
private lemma div_mem_of_not_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F)
    {a b : F} (ha : a ∈ A) (hb : b ∈ A) (hbn : b ∉ A.nonunits) : a / b ∈ A := by
  rw [div_eq_mul_inv]
  exact mul_mem ha (inv_mem_of_not_mem_nonunits A hb hbn)

/-- A quotient `a / b` of a nonunit by a unit of a valuation subring is a nonunit. -/
private lemma div_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F)
    {a b : F} (ha : a ∈ A.nonunits) (hb : b ∈ A) (hbn : b ∉ A.nonunits) : a / b ∈ A.nonunits := by
  rw [div_eq_mul_inv, mul_comm]
  exact mul_mem_nonunits A (inv_mem_of_not_mem_nonunits A hb hbn) ha

section

variable {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z)

/-- The localization `(S_z)_𝔫 ⊆ F` at a prime `𝔫`, as an `S_z`-subalgebra of `F`. -/
private noncomputable def locSub (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsPrime] :
    Subalgebra (semilocalRing hz) F :=
  haveI := (isFractionRing_semilocalRing hz).1
  Localization.subalgebra.ofField F 𝔫.primeCompl 𝔫.primeCompl_le_nonZeroDivisors

private lemma mem_locSub (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsPrime] (x : F) :
    x ∈ locSub hz 𝔫 ↔ ∃ a b : semilocalRing hz, b ∉ 𝔫 ∧ x = (a : F) / (b : F) := by
  show (∃ (a s : semilocalRing hz) (_ : s ∈ 𝔫.primeCompl), x = _ * _⁻¹) ↔ _
  simp only [Ideal.mem_primeCompl_iff, div_eq_mul_inv, exists_prop]
  rfl

/-- For `𝔫` maximal, `(S_z)_𝔫` is a valuation ring of `F`: it is a discrete valuation ring with
fraction field `F`. -/
private lemma mem_or_inv_mem_locSub (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsMaximal] (x : F) :
    x ∈ locSub hz 𝔫 ∨ x⁻¹ ∈ locSub hz 𝔫 := by
  haveI := (isFractionRing_semilocalRing hz).1
  haveI : IsLocalization.AtPrime (locSub hz 𝔫) 𝔫 := by
    unfold locSub; infer_instance
  have := isDiscreteValuationRing_localization_semilocalRing hz 𝔫 (locSub hz 𝔫)
  haveI := this.1
  haveI := this.2
  rcases (ValuationRing.iff_isInteger_or_isInteger (locSub hz 𝔫) F).mp inferInstance x with
    ⟨⟨y, hy⟩, h⟩ | ⟨⟨y, hy⟩, h⟩
  · left; rw [← h]; exact hy
  · right; rw [← h]; exact hy

/-- If `s ∈ 𝔫` is nonzero, then `s⁻¹ ∉ (S_z)_𝔫`. -/
private lemma inv_not_mem_locSub (𝔫 : Ideal (semilocalRing hz)) [𝔫.IsPrime]
    {s : semilocalRing hz} (hs : s ∈ 𝔫) (hs0 : (s : F) ≠ 0) : (s : F)⁻¹ ∉ locSub hz 𝔫 := by
  rw [mem_locSub]
  rintro ⟨a, b, hb, h⟩
  have hb0 : (b : F) ≠ 0 := fun h0 => hb (by
    rw [show b = 0 from Subtype.ext h0]; exact 𝔫.zero_mem)
  apply hb
  rw [show b = a * s from Subtype.ext (by
    rw [eq_div_iff hb0] at h
    simp only [MulMemClass.coe_mul]
    field_simp at h ⊢
    linear_combination h)]
  exact 𝔫.mul_mem_left a hs

/-- The place `(S_z)_𝔫` of `F/K` attached to a maximal ideal `𝔫` of `S_z`. -/
private noncomputable def placeOf (𝔫 : MaximalSpectrum (semilocalRing hz)) : Place K F :=
  haveI := 𝔫.isMaximal
  { (locSub hz 𝔫.asIdeal).toSubring with
    algebraMap_mem' := fun k => (locSub hz 𝔫.asIdeal).algebraMap_mem
      ⟨_, (semilocalRing hz).algebraMap_mem ⟨_, (localRingAtZero hz).algebraMap_mem k⟩⟩
    mem_or_inv_mem' := mem_or_inv_mem_locSub hz 𝔫.asIdeal
    ne_top := fun h => by
      obtain ⟨hzS, hzn⟩ := exists_mem_of_isMaximal_semilocalRing hz 𝔫.asIdeal
      refine inv_not_mem_locSub hz 𝔫.asIdeal hzn hz.ne_zero ?_
      have : z⁻¹ ∈ (⊤ : Subalgebra K F) := Algebra.mem_top
      rw [← h] at this
      exact this }

private lemma mem_placeOf_iff (𝔫 : MaximalSpectrum (semilocalRing hz)) (x : F) :
    x ∈ (placeOf hz 𝔫).toValuationSubring ↔ x ∈ locSub hz 𝔫.asIdeal :=
  Iff.rfl

/-- `𝔫` is recovered from `(S_z)_𝔫` as the elements of `S_z` lying in its maximal ideal. -/
private lemma mem_maximalIdeal_placeOf_iff (𝔫 : MaximalSpectrum (semilocalRing hz))
    (s : semilocalRing hz) : (s : F) ∈ (placeOf hz 𝔫).maximalIdeal ↔ s ∈ 𝔫.asIdeal := by
  haveI := 𝔫.isMaximal
  by_cases hs0 : (s : F) = 0
  · rw [show s = 0 from Subtype.ext hs0]
    simp only [ZeroMemClass.coe_zero, zero_mem, Submodule.zero_mem]
  rw [Place.maximalIdeal, mem_nonunits_iff_inv_not_mem _ hs0, mem_placeOf_iff]
  refine ⟨fun h => ?_, fun h => inv_not_mem_locSub hz 𝔫.asIdeal h hs0⟩
  by_contra hs
  exact h ((mem_locSub hz _ _).mpr ⟨1, s, hs, by simp⟩)

private lemma z_mem_maximalIdeal_placeOf (𝔫 : MaximalSpectrum (semilocalRing hz)) :
    z ∈ (placeOf hz 𝔫).maximalIdeal := by
  haveI := 𝔫.isMaximal
  obtain ⟨hzS, hzn⟩ := exists_mem_of_isMaximal_semilocalRing hz 𝔫.asIdeal
  exact (mem_maximalIdeal_placeOf_iff hz 𝔫 ⟨z, hzS⟩).mpr hzn

private lemma placeOf_injective : Function.Injective (placeOf hz) := by
  intro 𝔫 𝔫' h
  ext s
  rw [← mem_maximalIdeal_placeOf_iff, h, mem_maximalIdeal_placeOf_iff]

/-- A polynomial in `z` lies in every valuation subring containing `z`. -/
private lemma aeval_mem (v : Place K F) (hzv : z ∈ v.toValuationSubring) (p : K[X]) :
    aeval z p ∈ v.toValuationSubring := by
  rw [← Polynomial.aeval_subalgebra_coe p v.toSubalgebra ⟨z, hzv⟩]
  exact (aeval (⟨z, hzv⟩ : v.toSubalgebra) p).2

/-- If `z ∈ 𝔪_v` and `g(0) ≠ 0`, then `g(z)` is a unit of `𝒪_v`: it is `g(0) + z h(z)`, a unit
plus an element of `𝔪_v`. -/
private lemma aeval_not_mem_nonunits (v : Place K F) (hv : z ∈ v.maximalIdeal) {g : K[X]}
    (hg : g.coeff 0 ≠ 0) : aeval z g ∉ v.toValuationSubring.nonunits := by
  obtain ⟨h, hh⟩ := X_dvd_sub_C (p := g)
  have heq : aeval z g = algebraMap K F (g.coeff 0) + z * aeval z h := by
    rw [sub_eq_iff_eq_add] at hh
    rw [hh]
    simp [add_comm]
  have hc : algebraMap K F (g.coeff 0) ∉ v.toValuationSubring.nonunits := fun hn => by
    rw [mem_nonunits_iff_inv_not_mem _ (by simpa using hg)] at hn
    exact hn (by rw [← map_inv₀]; exact v.algebraMap_mem _)
  have hm : z * aeval z h ∈ v.toValuationSubring.nonunits := by
    rw [mul_comm]
    exact mul_mem_nonunits _ (aeval_mem v (mem_of_mem_nonunits _ hv) h) hv
  rw [ValuationSubring.mem_nonunits_iff] at hc hm ⊢
  rw [heq, Valuation.map_add_eq_of_lt_left _ (hm.trans_le (not_lt.mp hc))]
  exact hc

/-- A place `v` with `z ∈ 𝔪_v` contains `R_z`. -/
private lemma mem_of_mem_localRingAtZero (v : Place K F) (hv : z ∈ v.maximalIdeal) {x : F}
    (hx : x ∈ localRingAtZero hz) : x ∈ v.toValuationSubring := by
  obtain ⟨f, g, hg, rfl⟩ := hx
  exact div_mem_of_not_mem_nonunits _ (aeval_mem v (mem_of_mem_nonunits _ hv) f)
    (aeval_mem v (mem_of_mem_nonunits _ hv) g) (aeval_not_mem_nonunits v hv hg)

/-- A place `v` with `z ∈ 𝔪_v` contains `S_z`, since `𝒪_v` is integrally closed in `F`. -/
private lemma mem_of_mem_semilocalRing (v : Place K F) (hv : z ∈ v.maximalIdeal) {x : F}
    (hx : x ∈ semilocalRing hz) : x ∈ v.toValuationSubring := by
  letI : Algebra (localRingAtZero hz) v.toValuationSubring :=
    ((algebraMap (localRingAtZero hz) F).codRestrict _
      (fun y => mem_of_mem_localRingAtZero hz v hv y.2)).toAlgebra
  haveI : IsScalarTower (localRingAtZero hz) v.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsIntegrallyClosedIn v.toValuationSubring F := inferInstance
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := v.toValuationSubring)).mp
    (IsIntegral.tower_top (A := v.toValuationSubring) hx)
  exact hy ▸ y.2

/-- The prime `𝔪_v ∩ S_z` of `S_z`, for a place `v` with `z ∈ 𝔪_v`. -/
private noncomputable def idealOf (v : Place K F) (hv : z ∈ v.maximalIdeal) :
    Ideal (semilocalRing hz) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap
    ((algebraMap (semilocalRing hz) F).codRestrict _
      (fun y => mem_of_mem_semilocalRing hz v hv y.2))

private lemma mem_idealOf (v : Place K F) (hv : z ∈ v.maximalIdeal) (s : semilocalRing hz) :
    s ∈ idealOf hz v hv ↔ (s : F) ∈ v.maximalIdeal := by
  rw [idealOf, Ideal.mem_comap, Place.maximalIdeal,
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩

/-- `𝔪_v ∩ S_z` is a nonzero prime, hence maximal. -/
private lemma idealOf_isMaximal (v : Place K F) (hv : z ∈ v.maximalIdeal) :
    (idealOf hz v hv).IsMaximal := by
  have hzS : z ∈ semilocalRing hz := (semilocalRing hz).algebraMap_mem
    ⟨z, (isDiscreteValuationRing_localRingAtZero hz).2.1.1⟩
  haveI := dimensionLEOne_semilocalRing hz
  refine Ideal.IsPrime.isMaximal (by unfold idealOf; infer_instance) fun h => hz.ne_zero ?_
  have h1 := (mem_idealOf hz v hv ⟨z, hzS⟩).mpr hv
  rw [h, Ideal.mem_bot] at h1
  exact congr($h1.1)

/-- The place `v` dominates `(S_z)_𝔫` for `𝔫 = 𝔪_v ∩ S_z`, so the two valuation subrings
agree. -/
private lemma placeOf_idealOf (v : Place K F) (hv : z ∈ v.maximalIdeal) :
    placeOf hz ⟨idealOf hz v hv, idealOf_isMaximal hz v hv⟩ = v := by
  set 𝔫 : MaximalSpectrum (semilocalRing hz) := ⟨idealOf hz v hv, idealOf_isMaximal hz v hv⟩
  haveI := 𝔫.isMaximal
  have hS (s : semilocalRing hz) := mem_of_mem_semilocalRing hz v hv s.2
  have hu (b : semilocalRing hz) (hb : b ∉ 𝔫.asIdeal) : (b : F) ∉ v.toValuationSubring.nonunits :=
    mt (mem_idealOf hz v hv b).mpr hb
  have hle : (placeOf hz 𝔫).toValuationSubring ≤ v.toValuationSubring := by
    intro x hx
    obtain ⟨a, b, hb, rfl⟩ := (mem_locSub hz _ x).mp hx
    exact div_mem_of_not_mem_nonunits _ (hS a) (hS b) (hu b hb)
  have hnu : (placeOf hz 𝔫).toValuationSubring.nonunits ≤ v.toValuationSubring.nonunits := by
    intro x hx
    obtain ⟨a, b, hb, rfl⟩ := (mem_locSub hz _ _).mp (mem_of_mem_nonunits _ hx)
    by_cases hx0 : (a : F) / b = 0
    · exact hx0 ▸ zero_mem _
    refine div_mem_nonunits _ ((mem_idealOf hz v hv a).mp (not_not.mp fun ha => ?_))
      (hS b) (hu b hb)
    exact (mem_nonunits_iff_inv_not_mem _ hx0).mp hx
      ((mem_locSub hz _ _).mpr ⟨b, a, ha, inv_div _ _⟩)
  exact Place.ext congr(($(le_antisymm hle (ValuationSubring.nonunits_le_nonunits.mp hnu)) :
    Set F))

end

/-- Let `F/K` be a function field and `z ∈ F` transcendental over `K`. There is an equivalence
between the maximal ideals `𝔫` of `S_z = semilocalRing hz` and the places `v` of `F/K` with
`z ∈ v.maximalIdeal`, sending `𝔫` to the place whose valuation ring is the localization
`(S_z)_𝔫 = {a / b : a, b ∈ S_z, b ∉ 𝔫} ⊆ F`. -/
@[faltings "prop_ff_places_over_zero"]
theorem exists_equiv_maximalSpectrum_semilocalRing {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {z : F} (hz : Transcendental K z) :
    ∃ e : MaximalSpectrum (semilocalRing hz) ≃ {v : Place K F // z ∈ v.maximalIdeal},
      ∀ (𝔫 : MaximalSpectrum (semilocalRing hz)) (x : F),
        x ∈ (e 𝔫).1.toSubalgebra ↔
          ∃ a b : semilocalRing hz, b ∉ 𝔫.asIdeal ∧ x = (a : F) / (b : F) := by
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨placeOf hz 𝔫, z_mem_maximalIdeal_placeOf hz 𝔫⟩)
    ⟨fun _ _ h => placeOf_injective hz (congrArg Subtype.val h),
      fun ⟨v, hv⟩ => ⟨_, Subtype.ext (placeOf_idealOf hz v hv)⟩⟩,
    fun 𝔫 x => ?_⟩
  haveI := 𝔫.isMaximal
  exact mem_locSub hz 𝔫.asIdeal x

end Faltings.FunctionField

end
