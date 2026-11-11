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

/-!
# Orders of vanishing and local rings on normal schemes

For an integral locally Noetherian normal scheme: `0 ≤ ord_w h ↔ h ∈ 𝒪_w`, `0 < ord_w h ↔ h ∈ 𝔪_w`,
descriptions of local rings and maximal ideals on affine opens, algebraic Hartogs and Krull's
principal ideal theorem at a point, the centre of a valuation, germs on standard opens of `Proj`,
and `ord` of a quotient. Also: a scheme smooth over a field is normal.
-/

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order

universe u

/-- A scheme smooth over a field is normal. -/
public theorem isNormal_of_smooth_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] : IsNormal X :=
  isNormal_of_isRegular X (isRegular_of_smooth_over_field f)

section Ord

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- In a discrete valuation ring, every height-one prime is the maximal ideal, so an element of
the fraction field of valuation at most one lies in the ring. -/
public theorem mem_range_of_valuation_le_one {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {h : K}
    (hv : (IsDiscreteValuationRing.maximalIdeal R).valuation K h ≤ 1) :
    h ∈ Set.range (algebraMap R K) := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K h fun v => ?_
  have : v = IsDiscreteValuationRing.maximalIdeal R := by
    ext1
    exact (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance |>.2.unique
      ⟨v.ne_bot, v.isPrime⟩ ⟨(IsDiscreteValuationRing.maximalIdeal R).ne_bot,
        (IsDiscreteValuationRing.maximalIdeal R).isPrime⟩
  rwa [this]

/-- At a codimension-one point `w` of a normal scheme, a nonzero rational function has
nonnegative order exactly when it lies in the local ring. -/
public theorem ord_nonneg_iff {w : X} (hw : coheight w = 1) {h : X.functionField}
    (h0 : h ≠ 0) :
    0 ≤ X.ord h w ↔ h ∈ Set.range (algebraMap (X.presheaf.stalk w) X.functionField) := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hw
  have hord : Scheme.ordHom w hw = Ring.ordFrac (X.presheaf.stalk w) := rfl
  rw [Scheme.le_ord_iff hw h0, hord, Ring.ordFrac_eq_valuation_inv]
  have hv0 : 0 < (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk w)).valuation
      X.functionField h := by
    rwa [zero_lt_iff, Ne, Valuation.zero_iff]
  rw [show ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1
      from rfl,
    one_le_inv₀ hv0]
  refine ⟨mem_range_of_valuation_le_one, ?_⟩
  rintro ⟨s, rfl⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

/-- At a codimension-one point `w` of a normal scheme, the image of a unit of the local ring has
order zero. -/
public theorem ord_algebraMap_of_isUnit {w : X} (hw : coheight w = 1)
    {s : X.presheaf.stalk w} (hs : IsUnit s) :
    X.ord (algebraMap (X.presheaf.stalk w) X.functionField s) w = 0 := by
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hw
  have hs0 : algebraMap (X.presheaf.stalk w) X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs.ne_zero
  rw [Scheme.ord_eq_iff hw hs0]
  exact Ring.ordFrac_of_isUnit (K := X.functionField) hs

/-- At a codimension-one point `w` of a normal scheme, a nonzero rational function has
positive order exactly when it lies in the maximal ideal of the local ring. -/
public theorem ord_pos_iff {w : X} (hw : coheight w = 1) {h : X.functionField}
    (h0 : h ≠ 0) :
    0 < X.ord h w ↔ ∃ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w),
      algebraMap (X.presheaf.stalk w) X.functionField s = h := by
  constructor
  · intro hpos
    obtain ⟨s, rfl⟩ := (ord_nonneg_iff hw h0).mp hpos.le
    refine ⟨s, ?_, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hs => hpos.ne' (ord_algebraMap_of_isUnit hw hs)
  · rintro ⟨s, hs, rfl⟩
    refine lt_of_le_of_ne ((ord_nonneg_iff hw h0).mpr ⟨s, rfl⟩) fun h1 => ?_
    obtain ⟨a, ha, has⟩ :=
      Stacks.AlgebraicGeometry.UnitsNormalProper.exists_isUnit_of_ord_eq_zero hw h0 h1.symm
    rw [IsFractionRing.injective _ _ has] at ha
    exact (IsLocalRing.mem_maximalIdeal _).mp hs ha

end Ord

section Affine

variable {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]

include hU

/-- On an affine open `U`, a rational function lies in the local ring at `x ∈ U` exactly when it
is a fraction of sections over `U` whose denominator does not vanish at `x`. -/
public theorem mem_range_stalk_iff {x : X} (hx : x ∈ U) (h : X.functionField) :
    h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) ↔
      ∃ a s : Γ(X, U), s ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
        h * X.germToFunctionField U s = X.germToFunctionField U a := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hcomp : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk x) X.functionField
      (algebraMap Γ(X, U) (X.presheaf.stalk x) a) = X.germToFunctionField U a :=
    fun a => Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx a
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl t
    refine ⟨a, s, s.2, ?_⟩
    rw [← hcomp, ← hcomp, ← map_mul, IsLocalization.mk'_spec]
  · rintro ⟨a, s, hs, has⟩
    refine ⟨IsLocalization.mk' (X.presheaf.stalk x) a
      (⟨s, hs⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl), ?_⟩
    have hs0 : X.germToFunctionField U s ≠ 0 := fun h0 =>
      hs ((map_eq_zero_iff _ (X.germToFunctionField_injective U)).mp h0 ▸ zero_mem _)
    apply mul_right_cancel₀ hs0
    rw [has, ← hcomp, ← hcomp, ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec (X.presheaf.stalk x) a
      (⟨s, hs⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

/-- On an affine open `U`, a rational function lies in the maximal ideal of the local ring at
`x ∈ U` exactly when it is a fraction of sections over `U` whose numerator vanishes at `x` and
whose denominator does not. -/
public theorem mem_maximalIdeal_stalk_iff {x : X} (hx : x ∈ U) (h : X.functionField) :
    (∃ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      algebraMap (X.presheaf.stalk x) X.functionField t = h) ↔
      ∃ a s : Γ(X, U), a ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
        s ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
        h * X.germToFunctionField U s = X.germToFunctionField U a := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hcomp : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk x) X.functionField
      (algebraMap Γ(X, U) (X.presheaf.stalk x) a) = X.germToFunctionField U a :=
    fun a => Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx a
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl t
    refine ⟨a, s, (IsLocalization.AtPrime.mk'_mem_maximal_iff _ _ _ _).mp ht, s.2, ?_⟩
    rw [← hcomp, ← hcomp, ← map_mul, IsLocalization.mk'_spec]
  · rintro ⟨a, s, ha, hs, has⟩
    refine ⟨IsLocalization.mk' (X.presheaf.stalk x) a
      (⟨s, hs⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl),
      (IsLocalization.AtPrime.mk'_mem_maximal_iff _ _ _ _).mpr ha, ?_⟩
    have hs0 : X.germToFunctionField U s ≠ 0 := fun h0 =>
      hs ((map_eq_zero_iff _ (X.germToFunctionField_injective U)).mp h0 ▸ zero_mem _)
    apply mul_right_cancel₀ hs0
    rw [has, ← hcomp, ← hcomp, ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec (X.presheaf.stalk x) a
      (⟨s, hs⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

omit [IsIntegral X] [Nonempty U] in
/-- Every prime of the sections over an affine open `U` is the prime of a point of `U`. -/
public theorem exists_primeIdealOf_eq (P : PrimeSpectrum Γ(X, U)) :
    ∃ (x : X) (hx : x ∈ U), hU.primeIdealOf ⟨x, hx⟩ = P := by
  have hx : hU.fromSpec P ∈ U := by
    change hU.fromSpec P ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨P, rfl⟩
  exact ⟨_, hx, hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hx⟩)⟩

omit [IsIntegral X] [Nonempty U] in
/-- On an affine open, specialization of points is inclusion of their primes. -/
public theorem specializes_iff_primeIdealOf_le {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    x ⤳ y ↔ hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨y, hy⟩ := by
  have ex : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have ey : hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  conv_lhs => rw [← ex, ← ey]
  exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes _ _).symm

omit [IsIntegral X] [Nonempty U] in
/-- On an affine open, the codimension of a point is the height of its prime. -/
public theorem coheight_eq_height_primeIdealOf {x : X} (hx : x ∈ U) :
    coheight x = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  have ex : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  conv_lhs => rw [← ex]
  exact (coheight_eq_of_isOpenImmersion hU.fromSpec).trans (idealHeight_eq_coheight _ _).symm

end Affine

section Local

variable {X : Scheme.{u}} [IsIntegral X]

/-- Generization of local rings is compatible with the inclusions into the function field. -/
public theorem algebraMap_stalkSpecializes {w q : X} (h : w ⤳ q) (t : X.presheaf.stalk q) :
    algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.stalkSpecializes h t) =
      algebraMap (X.presheaf.stalk q) X.functionField t := by
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- An element of the local ring at `q` lies in the local ring at every generization of `q`. -/
public theorem mem_range_stalk_of_specializes {w q : X} (h : w ⤳ q) {g : X.functionField}
    (hg : g ∈ Set.range (algebraMap (X.presheaf.stalk q) X.functionField)) :
    g ∈ Set.range (algebraMap (X.presheaf.stalk w) X.functionField) := by
  obtain ⟨t, rfl⟩ := hg
  exact ⟨_, algebraMap_stalkSpecializes h t⟩

variable [IsLocallyNoetherian X] [IsNormal X]

/-- **Algebraic Hartogs at a point.** On a normal scheme, a rational function of nonnegative order
at every codimension-one generization of `q` lies in the local ring at `q`. -/
public theorem mem_range_stalk_of_forall_ord_nonneg (q : X) {h : X.functionField}
    (hh : ∀ w : X, w ⤳ q → coheight w = 1 → 0 ≤ X.ord h w) :
    h ∈ Set.range (algebraMap (X.presheaf.stalk q) X.functionField) := by
  by_cases h0 : h = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := q) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨q, hqU⟩⟩
  let := X.presheaf.algebra_section_stalk ⟨q, hqU⟩
  have := hU.isLocalization_stalk ⟨q, hqU⟩
  have : IsIntegrallyClosed (X.presheaf.stalk q) := IsNormal.stalk_normal q
  have hcomp : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk q) X.functionField
      (algebraMap Γ(X, U) (X.presheaf.stalk q) a) = X.germToFunctionField U a :=
    fun a => Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hqU a
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    (R := X.presheaf.stalk q) X.functionField (z := h) fun Q hQ => ?_
  set P := Q.asIdeal.comap (algebraMap Γ(X, U) (X.presheaf.stalk q))
  have : P.IsPrime := Ideal.IsPrime.comap _
  have hP1 : P.height = 1 :=
    (IsLocalization.height_under (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl Q.asIdeal).trans hQ
  have hPy : P ≤ (hU.primeIdealOf ⟨q, hqU⟩).asIdeal := by
    intro a ha
    by_contra hay
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk q) a) :=
      IsLocalization.map_units (X.presheaf.stalk q)
        (⟨a, hay⟩ : (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl)
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  obtain ⟨w, hwU, hwP⟩ := exists_primeIdealOf_eq hU ⟨P, inferInstance⟩
  have hwq : w ⤳ q := (specializes_iff_primeIdealOf_le hU hwU hqU).mpr (by rwa [hwP])
  have hw1 : coheight w = 1 := by
    rwa [coheight_eq_height_primeIdealOf hU hwU, hwP]
  obtain ⟨a, s, hs, has⟩ :=
    (mem_range_stalk_iff hU hwU h).mp ((ord_nonneg_iff hw1 h0).mp (hh w hwq hw1))
  rw [hwP] at hs
  refine ⟨algebraMap _ _ a, algebraMap _ _ s, hs, ?_⟩
  rwa [hcomp, hcomp]

/-- **Krull's principal ideal theorem at a point.** On a normal scheme, a nonzero nonunit of the
local ring at `q` vanishes at some codimension-one generization of `q`. -/
public theorem exists_ord_pos_of_mem_maximalIdeal (q : X) {t : X.presheaf.stalk q}
    (ht0 : t ≠ 0) (ht : t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q)) :
    ∃ w : X, w ⤳ q ∧ coheight w = 1 ∧
      0 < X.ord (algebraMap (X.presheaf.stalk q) X.functionField t) w := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := q) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨q, hqU⟩⟩
  let := X.presheaf.algebra_section_stalk ⟨q, hqU⟩
  have := hU.isLocalization_stalk ⟨q, hqU⟩
  have hcomp : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk q) X.functionField
      (algebraMap Γ(X, U) (X.presheaf.stalk q) a) = X.germToFunctionField U a :=
    fun a => Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hqU a
  obtain ⟨𝔭, h𝔭, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  have := h𝔭.isPrime
  have ht𝔭 : t ∈ 𝔭 := h𝔭.1.2 (Ideal.mem_span_singleton_self t)
  have h𝔭1 : 𝔭.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔭) ?_
    rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact ht0 ht𝔭
  set P := 𝔭.comap (algebraMap Γ(X, U) (X.presheaf.stalk q))
  have : P.IsPrime := Ideal.IsPrime.comap _
  have hP1 : P.height = 1 :=
    (IsLocalization.height_under (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl 𝔭).trans h𝔭1
  have hPy : P ≤ (hU.primeIdealOf ⟨q, hqU⟩).asIdeal := by
    intro a ha
    by_contra hay
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk q) a) :=
      IsLocalization.map_units (X.presheaf.stalk q)
        (⟨a, hay⟩ : (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl)
    exact h𝔭.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  obtain ⟨w, hwU, hwP⟩ := exists_primeIdealOf_eq hU ⟨P, inferInstance⟩
  have hwq : w ⤳ q := (specializes_iff_primeIdealOf_le hU hwU hqU).mpr (by rwa [hwP])
  have hw1 : coheight w = 1 := by
    rwa [coheight_eq_height_primeIdealOf hU hwU, hwP]
  refine ⟨w, hwq, hw1, ?_⟩
  have htK : algebraMap (X.presheaf.stalk q) X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht0
  rw [ord_pos_iff hw1 htK, mem_maximalIdeal_stalk_iff hU hwU, hwP]
  obtain ⟨⟨a, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.primeCompl t
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk q) a s
  refine ⟨a, s, ?_, fun hsP => s.2 (hPy hsP), ?_⟩
  · change algebraMap Γ(X, U) (X.presheaf.stalk q) a ∈ 𝔭
    rw [← hspec]
    exact 𝔭.mul_mem_right _ ht𝔭
  · rw [← hcomp, ← hcomp, ← map_mul, hspec]

/-- **Vanishing at a point, by orders.** On a normal scheme, a rational function `h` lies in the
maximal ideal of the local ring at `q` exactly when it has nonnegative order at every
codimension-one generization of `q` and is zero or has positive order at one of them. -/
public theorem exists_mem_maximalIdeal_iff_ord (q : X) (h : X.functionField) :
    ((∀ w, w ⤳ q → coheight w = 1 → 0 ≤ X.ord h w) ∧
      (h = 0 ∨ ∃ w, w ⤳ q ∧ coheight w = 1 ∧ 0 < X.ord h w)) ↔
      ∃ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q),
        algebraMap (X.presheaf.stalk q) X.functionField t = h := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨t, rfl⟩ := mem_range_stalk_of_forall_ord_nonneg q h1
    refine ⟨t, ?_, rfl⟩
    rcases h2 with h0 | ⟨w, hwq, hw1, hpos⟩
    · rw [IsFractionRing.injective _ X.functionField (h0.trans (map_zero _).symm)]
      exact zero_mem _
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [← algebraMap_stalkSpecializes hwq, ord_algebraMap_of_isUnit hw1 (hu.map _)] at hpos
      exact lt_irrefl _ hpos
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun w hwq hw1 => ?_, ?_⟩
    · by_cases h0 : algebraMap (X.presheaf.stalk q) X.functionField t = 0
      · simp [h0]
      · exact (ord_nonneg_iff hw1 h0).mpr (mem_range_stalk_of_specializes hwq ⟨t, rfl⟩)
    · by_cases ht0 : t = 0
      · exact Or.inl (by rw [ht0, map_zero])
      · exact Or.inr (exists_ord_pos_of_mem_maximalIdeal q ht0 ht)

end Local

section Centre

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (V : ValuationSubring X.functionField)
  (hV : ∀ c : k, X.presheaf.germ ⊤ (genericPoint X) trivial
    (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) ∈ V)

/-- The valuative square attached to a valuation subring `V` of the function field containing the
constants. -/
public noncomputable def valuativeCommSqOf : ValuativeCommSq f where
  R := V
  K := X.functionField
  i₁ := X.fromSpecStalk (genericPoint X)
  i₂ := Spec.map (CommRingCat.ofHom ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom).codRestrict V.toSubring hV))
  commSq := ⟨by
    rw [FunctionField.fromSpecStalk_comp_eq_SpecMap, ← Spec.map_comp]
    rfl⟩

include hV in
/-- **Centre of a valuation.** For `f : X ⟶ Spec k` universally closed and `V` a valuation subring
of `k(X)` containing the constants, some point `x` of `X` has `𝒪_{X,x}` dominated by `V`. -/
public theorem exists_isLocalHom_stalk [UniversallyClosed f] :
    ∃ (x : X) (ρ : X.presheaf.stalk x →+* V), IsLocalHom ρ ∧
      ∀ s, (ρ s : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField s := by
  let S := valuativeCommSqOf f V hV
  obtain ⟨l⟩ := ((UniversallyClosed.eq_valuativeCriterion.le _ _ f inferInstance).1 S).exists_lift
  set x := l.l (IsLocalRing.closedPoint (CommRingCat.of V))
  have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have : IsLocalRing (CommRingCat.of V) := inferInstanceAs (IsLocalRing V)
  refine ⟨x, (Scheme.stalkClosedPointTo l.l).hom, Scheme.isLocalHom_stalkClosedPointTo _,
    fun s => ?_⟩
  exact congr($(FunctionField.stalkClosedPointTo_comp_eq_stalkSpecializes
    (CommRingCat.ofHom (algebraMap V X.functionField)) l.l l.fac_left hηx).hom s)

end Centre

section Proj

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The germ at `y ∈ D₊(f)` of the section `x / fᵐ` is a unit exactly when `x ∉ y`. -/
public theorem isUnit_germ_awayToSection_iff {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (m : ℕ) (x : A)
    (hx : x ∈ 𝒜 (m • d)) (y : AlgebraicGeometry.Proj 𝒜) (hy : y ∈ Proj.basicOpen 𝒜 f) :
    IsUnit ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hy
      (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf m x hx))) ↔ x ∉ y.asHomogeneousIdeal := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have e := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f y hy).hom
    (Away.mk 𝒜 hf m x hx))
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hy
    (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf m x hx)) = _ at e
  rw [e, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  change IsUnit ((Proj.stalkIso' 𝒜 y).symm _) ↔ _
  rw [isUnit_map_iff, ← isUnit_iff_isUnit_val]
  change IsUnit (Localization.mk x ⟨f ^ m, _⟩ : Localization.AtPrime _) ↔ _
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

/-- On `D₊(f) ∩ D₊(g)` for `f, g` of degree one, the germs of the sections `g / f` and `f / g`
are inverse. -/
public theorem germ_mul_germ_awayToSection {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hf' : f ∈ 𝒜 (1 • 1)) (hg' : g ∈ 𝒜 (1 • 1)) (y : AlgebraicGeometry.Proj 𝒜)
    (hyf : y ∈ Proj.basicOpen 𝒜 f) (hyg : y ∈ Proj.basicOpen 𝒜 g) :
    (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hyf
        (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 g hg')) *
      (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
        (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')) = 1 := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have e₁ := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f y hyf).hom
    (Away.mk 𝒜 hf 1 g hg'))
  have e₂ := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 g y hyg).hom
    (Away.mk 𝒜 hg 1 f hf'))
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hyf
    (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 g hg')) = _ at e₁
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
    (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')) = _ at e₂
  rw [e₁, e₂, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  change (Proj.stalkIso' 𝒜 y).symm _ * (Proj.stalkIso' 𝒜 y).symm _ = 1
  rw [← map_mul, RingEquiv.symm_apply_eq, map_one]
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_one]
  change (Localization.mk g ⟨f ^ 1, _⟩ : Localization.AtPrime _) * Localization.mk f ⟨g ^ 1, _⟩ = 1
  rw [Localization.mk_mul, ← Localization.mk_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [mul_comm]⟩

end Proj

/-- The order of vanishing of a quotient. -/
public theorem ord_div {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {g h : X.functionField} (hg : g ≠ 0) (hh : h ≠ 0) (w : X) :
    X.ord (g / h) w = X.ord g w - X.ord h w := by
  rw [div_eq_mul_inv, Scheme.ord_mul hg (inv_ne_zero hh), Stacks.Chow.ord_inv_functionField hh]
  ring

end Faltings
