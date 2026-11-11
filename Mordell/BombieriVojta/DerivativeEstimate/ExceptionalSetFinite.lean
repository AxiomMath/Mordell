module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.BombieriVojta.DerivativeEstimate.PlaneRelationDiscriminant
public import Mordell.Curve.GenericUniformizer
public import Mordell.AlgebraicGeometry.RationalPoint
public import Mordell.Curve.Normal
public import Mordell.Curve.FunctionField
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma5
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma6
public import Mordell.BombieriVojta.Norm.NumeratorZeros
public import StacksFrontier.AlgebraicGeometry.Curves.ModelBaseChange
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral

/-!
# The exceptional set `Z` is finite

Let `C` be a smooth projective geometrically integral curve over a field `k` of characteristic
zero, `D` a divisor on `C` and `x₀, …, xₙ` sections of `𝒪(D)` (rational functions in `L(D)`)
that are linearly independent over `k`, with `ξ_{νj} = x_ν / x_j`. The exceptional set
`Faltings.BombieriSiegel.exceptionalSet` of Bombieri's Lemma 6 is finite: the zeros of `x₀` are
finitely many; the points where some `ξ_{a0} - ξ_{a0}(z)` fails to be a uniformizer are finitely
many since `ξ_{a0}` is non-constant
(`Faltings.FunctionField.finite_setOf_maximalIdeal_ne_span_sub`);
and each discriminant `D_{g_{νj}}` is a non-zero polynomial
(`Faltings.FunctionField.one_le_natDegree_planeRelation_and_resultant_ne_zero`), with finitely
many roots, each taken by the non-constant `ξ₁₀` at finitely many points.

## Main results

* `Faltings.BombieriSiegel.exceptionalSet_finite`: the exceptional set `Z` is finite.
* `Faltings.BombieriSiegel.exists_finite_forall_notMem_exceptionalSet`: outside a finite set of
  `k̄`-points, no point is exceptional on any model `C_K` over a finite extension `K ⊆ k̄` over
  which it is defined.

## Implementation notes

Points are `k`-points of `C`, as in `Faltings.BombieriSiegel.exceptionalSet`; the source's
`C(k̄)` is the case of the base change of `C` to `k̄`. Only the linear independence of
`x₀, …, xₙ` is assumed, not that they form a basis of `L(D)`: it makes every `ξ_{a0}` with
`a ≠ 0` non-constant, which is all the argument needs.

Every clause is reduced to one fact: a function `ξ ≠ a` takes the value `a` at finitely many
`k`-points. At such a point `(ξ - a)²` is regular with value `0` and is not a local parameter,
so these points lie in the finite set of
`Faltings.FunctionField.finite_setOf_maximalIdeal_ne_span_sub` (or `(ξ - a)²` is constant and
the set is empty). Since the local rings at `k`-points are valuation rings, the poles of `ξ` are
the zeros of `ξ⁻¹`, and a zero of positive order is a zero of the germ.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 6, with the
  Errata-Corrige (1991); Section 10
-/

open Faltings.FunctionField (algebraMap_const)
open Faltings.Lemma6EstimateForDerivatives (algebraMap_stalkMap_eq_functionFieldMap'
  functionFieldMap_comp_apply')
open Stacks.HQuasiProjectiveDimensionOne
  (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one)

open AlgebraicGeometry CategoryTheory Limits IsLocalRing Polynomial IntermediateField

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriSiegel

/-- A constant of the local ring at a point lies in its maximal ideal only if it is zero. -/
private lemma eq_zero_of_const_mem_maximalIdeal {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (x : C) {b : k}
    (hb : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.germ ⊤ x trivial).hom b ∈
      maximalIdeal (C.presheaf.stalk x)) : b = 0 := by
  by_contra hb0
  exact (mem_maximalIdeal _).mp hb ((isUnit_iff_ne_zero.mpr hb0).map _)

/-- In a local ring, an element of the maximal ideal whose square generates it is zero. -/
private lemma eq_zero_of_maximalIdeal_eq_span_sq {R : Type*} [CommRing R] [IsLocalRing R]
    {t : R} (ht : t ∈ maximalIdeal R) (h : maximalIdeal R = Ideal.span {t ^ 2}) : t = 0 := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h ▸ ht)
  have hu : IsUnit (1 - r * t) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left _ r ht)
  exact (hu.mul_left_eq_zero).mp (by linear_combination -hr)

/-- A function `ξ ≠ a` takes the value `a` at finitely many `k`-points. -/
private lemma finite_setOf_sub_const_mem (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (ξ : C.functionField) (a : k)
    (hξ : letI := functionFieldAlgebra k f; ξ ≠ algebraMap k C.functionField a) :
    {z : Spec (.of k) ⟶ C | z ≫ f = 𝟙 _ ∧
      ∃ g : C.presheaf.stalk (z (closedPoint k)), algebraMap _ C.functionField g = ξ ∧
        g - ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            C.presheaf.germ ⊤ (z (closedPoint k)) trivial).hom a ∈
          maximalIdeal (C.presheaf.stalk (z (closedPoint k)))}.Finite := by
  let := functionFieldAlgebra k f
  by_cases hς : (ξ - algebraMap k _ a) ^ 2 ∈ Set.range (algebraMap k C.functionField)
  · -- then `ξ - a` vanishes nowhere
    obtain ⟨b, hb⟩ := hς
    refine Set.finite_empty.subset ?_
    rintro z ⟨-, g, hg, hga⟩
    set c := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (z (closedPoint k)) trivial).hom
    have hc : ∀ b, algebraMap _ C.functionField (c b) = algebraMap k _ b :=
      algebraMap_const f _
    have hinj : Function.Injective
        (algebraMap (C.presheaf.stalk (z (closedPoint k))) C.functionField) :=
      IsFractionRing.injective _ _
    have hsq : (g - c a) ^ 2 = c b :=
      hinj (by rw [RingHom.map_pow, RingHom.map_sub, hg, hc, hc, hb])
    have hb0 : b = 0 := eq_zero_of_const_mem_maximalIdeal f (z (closedPoint k))
      (hsq ▸ Ideal.pow_mem_of_mem _ hga 2 two_pos)
    rw [hb0, map_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hsq
    exact hξ (by rw [← hg, hsq, hc])
  · refine (Faltings.FunctionField.finite_setOf_maximalIdeal_ne_span_sub k f _ hς).subset ?_
    rintro z ⟨hz, g, hg, hga⟩
    set c := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      C.presheaf.germ ⊤ (z (closedPoint k)) trivial).hom
    have hc : ∀ b, algebraMap _ C.functionField (c b) = algebraMap k _ b :=
      algebraMap_const f _
    refine ⟨hz, (g - c a) ^ 2, by rw [RingHom.map_pow, RingHom.map_sub, hg, hc], fun b hb => ?_⟩
    have hmem : (g - c a) ^ 2 - c b ∈ maximalIdeal _ := hb ▸ Ideal.mem_span_singleton_self _
    have hb0 : b = 0 := eq_zero_of_const_mem_maximalIdeal f (z (closedPoint k)) <|
      sub_sub_cancel ((g - c a) ^ 2) (c b) ▸ sub_mem (Ideal.pow_mem_of_mem _ hga 2 two_pos) hmem
    rw [hb0, map_zero, sub_zero] at hb
    exact hξ (by rw [← hg, sub_eq_zero.mp (eq_zero_of_maximalIdeal_eq_span_sq hga hb), hc])

/-- The image of a `k`-point is a closed point. -/
private lemma isClosed_singleton_apply_closedPoint {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSeparated f] (z : Spec (.of k) ⟶ C) (hz : z ≫ f = 𝟙 _) :
    IsClosed ({z (closedPoint k)} : Set C) := by
  have : IsClosedImmersion (z ≫ f) := hz ▸ inferInstance
  have : IsClosedImmersion z := IsClosedImmersion.of_comp z f
  convert z.isClosedEmbedding.isClosed_range using 1
  ext q
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨q, rfl⟩; exact congrArg z (Subsingleton.elim q _)

/-- The local ring of a normal curve at a closed point is a valuation ring. -/
private lemma valuationRing_stalk {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsNormal C] {x : C} (hx : IsClosed {x}) :
    ValuationRing (C.presheaf.stalk x) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim := ringKrullDim_stalk_eq_one_of_isCurve k f hx
  have : IsIntegrallyClosed (C.presheaf.stalk x) := IsNormal.stalk_normal x
  have hnf : ¬ IsField (C.presheaf.stalk x) := fun hR => by
    let := hR.toField
    exact one_ne_zero (hdim.symm.trans (ringKrullDim_eq_zero_of_field _))
  have hle : Ring.KrullDimLE 1 (C.presheaf.stalk x) := by rw [Ring.krullDimLE_iff, hdim]; rfl
  have : IsDedekindDomain (C.presheaf.stalk x) :=
    { maximalOfPrime := Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hle _ }
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 3 2).mp this

/-- A non-zero function is regular at all but finitely many `k`-points. -/
private lemma finite_setOf_not_regular (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (ξ : C.functionField) (hξ : ξ ≠ 0) :
    {z : Spec (.of k) ⟶ C | z ≫ f = 𝟙 _ ∧
      ¬ ∃ g : C.presheaf.stalk (z (closedPoint k)),
        algebraMap _ C.functionField g = ξ}.Finite := by
  let := functionFieldAlgebra k f
  have := Faltings.FunctionField.isNormal_of_smooth k f
  refine (finite_setOf_sub_const_mem k f ξ⁻¹ 0 (by simpa using hξ)).subset ?_
  rintro z ⟨hz, hreg⟩
  have := valuationRing_stalk f (isClosed_singleton_apply_closedPoint f z hz)
  rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk (z (closedPoint k))) ξ with
    ⟨g, hg⟩ | ⟨h, hh⟩
  · exact absurd ⟨g, hg⟩ hreg
  · refine ⟨hz, h, hh, ?_⟩
    rw [RingHom.map_zero, sub_zero, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hreg
    refine ⟨↑hu.unit⁻¹, ?_⟩
    have h1 := congrArg (algebraMap _ C.functionField) hu.unit.inv_mul
    rw [RingHom.map_mul, RingHom.map_one, IsUnit.unit_spec, hh] at h1
    exact (mul_inv_eq_one₀ hξ).mp h1

/-- A non-zero function vanishes at finitely many `k`-points. -/
private lemma finite_setOf_ord_pos (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (ξ : C.functionField) (hξ : ξ ≠ 0) :
    {z : Spec (.of k) ⟶ C | z ≫ f = 𝟙 _ ∧ 0 < C.ord ξ (z (closedPoint k))}.Finite := by
  let := functionFieldAlgebra k f
  have := Faltings.FunctionField.isNormal_of_smooth k f
  refine (finite_setOf_sub_const_mem k f ξ 0 (by rw [map_zero]; exact hξ)).subset ?_
  rintro z ⟨hz, hord⟩
  have hp : Order.coheight (z (closedPoint k)) = 1 := by
    by_contra h
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hord
    exact lt_irrefl _ hord
  have := valuationRing_stalk f (isClosed_singleton_apply_closedPoint f z hz)
  have : Ring.KrullDimLE 1 (C.presheaf.stalk (z (closedPoint k))) :=
    krullDimLE_of_coheight_le hp.le
  rcases ValuationRing.isInteger_or_isInteger (C.presheaf.stalk (z (closedPoint k))) ξ with
    ⟨g, hg⟩ | ⟨h, hh⟩
  · refine ⟨hz, g, hg, ?_⟩
    rw [RingHom.map_zero, sub_zero, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : C.ord ξ (z (closedPoint k)) = 0 := by
      rw [Scheme.ord_eq_iff hp hξ, ← hg]
      exact Ring.ordFrac_of_isUnit hu
    omega
  · exfalso
    have h0 : h ≠ 0 := by
      rintro rfl
      rw [RingHom.map_zero] at hh
      exact inv_ne_zero hξ hh.symm
    have h1 : 0 ≤ C.ord ξ⁻¹ (z (closedPoint k)) := by
      rw [Scheme.le_ord_iff hp (inv_ne_zero hξ), ← hh]
      exact Ring.ordFrac_ge_one_of_ne_zero h0
    have h2 : C.ord ξ (z (closedPoint k)) + C.ord ξ⁻¹ (z (closedPoint k)) = 0 := by
      rw [← Scheme.ord_mul hξ (inv_ne_zero hξ), mul_inv_cancel₀ hξ,
        Scheme.ord_eq_iff hp one_ne_zero, map_one]
      rfl
    omega

/-- A non-constant function `ξ` is a local parameter `ξ - ξ(z)` at all but finitely many
`k`-points. -/
private lemma finite_setOf_notUniformizer (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (ξ : C.functionField)
    (hξ : letI := functionFieldAlgebra k f; ξ ∉ Set.range (algebraMap k C.functionField)) :
    {z : Spec (.of k) ⟶ C | z ≫ f = 𝟙 _ ∧
      ∀ g : C.presheaf.stalk (z (closedPoint k)), algebraMap _ C.functionField g = ξ →
        ∀ a : k, maximalIdeal (C.presheaf.stalk (z (closedPoint k))) ≠
          Ideal.span {g - ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            C.presheaf.germ ⊤ (z (closedPoint k)) trivial).hom a}}.Finite := by
  let := functionFieldAlgebra k f
  have hξ0 : ξ ≠ 0 := fun h => hξ ⟨0, by rw [RingHom.map_zero, h]⟩
  refine ((Faltings.FunctionField.finite_setOf_maximalIdeal_ne_span_sub k f ξ hξ).union
    (finite_setOf_not_regular k f ξ hξ0)).subset ?_
  rintro z ⟨hz, h⟩
  by_cases hreg : ∃ g : C.presheaf.stalk (z (closedPoint k)), algebraMap _ C.functionField g = ξ
  · obtain ⟨g, hg⟩ := hreg
    exact .inl ⟨hz, g, hg, h g hg⟩
  · exact .inr ⟨hz, hreg⟩

/-- Every function on a curve over a field of characteristic zero is separable over the
subfield generated by a transcendental function. -/
public lemma isSeparable_adjoin_transcendental (k : Type u) [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] {t : C.functionField}
    (ht : letI := functionFieldAlgebra k f; Transcendental k t) (ξ : C.functionField) :
    letI := functionFieldAlgebra k f; IsSeparable k⟮t⟯ ξ := by
  let := functionFieldAlgebra k f
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    ((algebraicIndependent_unique_type_iff (ι := Unit)).mpr
      ht).isTranscendenceBasis_of_lift_trdeg_le_of_finite
        (by rw [Faltings.trdeg_functionField_eq_one k f]; simp)
  have halg := hb.isAlgebraic_field
  rw [Set.range_const] at halg
  have : Algebra.IsSeparable k⟮t⟯ C.functionField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.IsSeparable.isSeparable _ _

/-- The **exceptional set** `Z` of Bombieri's Lemma 6 is finite: for a smooth projective
geometrically integral curve `C` over a field `k` of characteristic zero, a divisor `D` and
`k`-linearly independent rational functions `x₀, …, xₙ` with `x₁ / x₀` transcendental over `k`,
`Faltings.BombieriSiegel.exceptionalSet k f D x ht` is a finite set of `k`-points of `C`. -/
@[faltings "lem_bvs_exceptional_set_finite"]
public theorem exceptionalSet_finite (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (x : Fin (n + 1) → C.functionField)
    (hx : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (ht : letI := functionFieldAlgebra k f; Transcendental k (x 1 / x 0)) :
    (exceptionalSet k f D x ht).Finite := by
  classical
  let := functionFieldAlgebra k f
  have h10 : x 1 / x 0 ∉ Set.range (algebraMap k C.functionField) := fun ⟨b, hb⟩ =>
    ht (hb ▸ isAlgebraic_algebraMap b)
  let R : Fin (n + 1) → Fin (n + 1) → k[X] := fun ν j =>
    let G := Faltings.FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) ht
    G.resultant (derivative G) G.natDegree (G.natDegree - 1)
  have hR : ∀ ν j, R ν j ≠ 0 := fun ν j =>
    (Faltings.FunctionField.one_le_natDegree_planeRelation_and_resultant_ne_zero k ht
      (isSeparable_adjoin_transcendental k f ht _)).2
  have hD : {z : Spec (.of k) ⟶ C | z ≫ f = 𝟙 _ ∧ z (closedPoint k) ∈ D.support}.Finite :=
    Set.Finite.of_finite_image (D.support.finite_toSet.subset (by
      rintro _ ⟨z, hz, rfl⟩; exact hz.2))
      ((Faltings.FunctionField.bijOn_rank_residueField_eq_one k f).injOn.mono fun z hz => hz.1)
  refine (((hD.union (finite_setOf_ord_pos k f (x 0) (hx.ne_zero 0))).union
    ((finite_setOf_notUniformizer k f _ h10).union
      (Set.finite_iUnion fun a : {a : Fin (n + 1) // a ≠ 0} =>
        finite_setOf_notUniformizer k f _ (div_notMem_range_algebraMap hx a.2)))).union
    (Set.finite_iUnion fun ν => Set.finite_iUnion fun j =>
      (R ν j).roots.toFinset.finite_toSet.biUnion fun a _ =>
        finite_setOf_sub_const_mem k f (x 1 / x 0) a fun h => h10 ⟨a, h.symm⟩)).subset ?_
  rintro z ⟨hz, h⟩
  rcases h with h1 | ⟨-, h2⟩ | ⟨-, ν, j, -, -, -, g, hg, a, hga, hRa⟩ | ⟨-, a, ha, h4⟩
  · by_cases hDp : D (z (closedPoint k)) = 0
    · exact .inl (.inl (.inr ⟨hz, by rw [hDp] at h1; simpa using h1⟩))
    · exact .inl (.inl (.inl ⟨hz, Finsupp.mem_support_iff.mpr hDp⟩))
  · exact .inl (.inr (.inl ⟨hz, h2⟩))
  · refine .inr (Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨j, Set.mem_biUnion
      (x := a) ?_ ⟨hz, g, hg, hga⟩⟩⟩)
    simpa [Polynomial.mem_roots (hR ν j), R] using hRa
  · exact .inl (.inr (.inr (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hz, h4⟩)))

/-! ### Points defined over an intermediate field

A `K`-point `z_K` of a model `C_K` of `C` over a field `K ⊆ k̄` gives the `k̄`-point `z̄` of
`C_{k̄}`. The stalk map `𝒪_{C_K, z_K} → 𝒪_{C_{k̄}, z̄}` is a local homomorphism compatible with the
function fields and the constants; through it each clause of `exceptionalSet` at `z_K` gives
the corresponding condition at `z̄`. -/

section BaseChange

/-- A local homomorphism out of a valuation ring reflects generators of the maximal ideal. -/
private lemma maximalIdeal_eq_span_of_map {R S : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {h : R}
    (hh : h ∈ maximalIdeal R) (hS : maximalIdeal S = Ideal.span {φ h}) (h0 : φ h ≠ 0) :
    maximalIdeal R = Ideal.span {h} := by
  refine le_antisymm (fun m hm => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hh)
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond h m
  · exact Ideal.mem_span_singleton'.2 ⟨c, by rw [mul_comm, hc]⟩
  · by_cases hcu : IsUnit c
    · refine Ideal.mem_span_singleton'.2 ⟨↑hcu.unit⁻¹, ?_⟩
      rw [← hc, mul_comm m, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    · exfalso
      have hc' : φ c ∈ maximalIdeal S := map_nonunit φ c ((mem_maximalIdeal _).2 hcu)
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hS ▸ map_nonunit φ m hm)
      have hu : IsUnit (1 - s * φ c) :=
        isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left _ s hc')
      refine h0 ((hu.mul_left_eq_zero).1 ?_)
      have : φ h = φ m * φ c := by rw [← map_mul, hc]
      calc φ h * (1 - s * φ c) = φ h - s * φ h * φ c := by ring
        _ = 0 := by rw [hs, ← this, sub_self]

variable {K L : Type u} [Field K] [Field L] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of K))
  (fY : Y ⟶ Spec (.of L)) (σ : K →+* L) (ρ : Y ⟶ X)

/-- The stalk map of a morphism over `Spec L ⟶ Spec K` carries the constants to the
constants. -/
private lemma stalkMap_const (hsq : ρ ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom σ)) (y : Y)
    (a : K) :
    ρ.stalkMap y (((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop ≫
        X.presheaf.germ ⊤ (ρ y) trivial).hom a) =
      ((Scheme.ΓSpecIso (.of L)).inv ≫ fY.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom (σ a) := by
  have key : (Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop ≫ ρ.appTop =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ fY.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h := Scheme.Hom.germ_stalkMap_apply ρ ⊤ y trivial
    (fX.appTop ((Scheme.ΓSpecIso (.of K)).inv.hom a))
  exact h.trans congr((Y.presheaf.germ ⊤ y trivial).hom ($(key).hom a))

variable [IsIntegral X] [IsIntegral Y] [IsDominant ρ]

/-- If `ξ` takes the value `a` at `ρ y`, then its pull-back takes the value `σ a` at `y`. -/
private lemma exists_germ_sub_const_mem_of_map
    (hsq : ρ ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom σ)) (y : Y) {q : X} (hq : ρ y = q)
    (ξ : X.functionField) (a : K)
    (h : ∃ g : X.presheaf.stalk q, algebraMap _ X.functionField g = ξ ∧
      g - ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop ≫
        X.presheaf.germ ⊤ q trivial).hom a ∈ maximalIdeal (X.presheaf.stalk q)) :
    ∃ g : Y.presheaf.stalk y, algebraMap _ Y.functionField g = functionFieldMap ρ ξ ∧
      g - ((Scheme.ΓSpecIso (.of L)).inv ≫ fY.appTop ≫
        Y.presheaf.germ ⊤ y trivial).hom (σ a) ∈ maximalIdeal (Y.presheaf.stalk y) := by
  subst hq
  obtain ⟨g, hg, hga⟩ := h
  refine ⟨ρ.stalkMap y g, by rw [algebraMap_stalkMap_eq_functionFieldMap' ρ y g, hg], ?_⟩
  rw [← stalkMap_const fX fY σ ρ hsq y a, ← map_sub]
  exact map_nonunit (ρ.stalkMap y).hom _ hga

/-- If `ξ - ξ(ρ y)` is not a local parameter at a rational point `ρ y` with valuation-ring local
ring, then `ρ^* ξ - ρ^* ξ(y)` is not a local parameter at `y`, provided `ρ^* ξ` is not a
constant. -/
private lemma notUniformizer_of_map [IsCurve K fX] [IsCurve L fY]
    (hsq : ρ ≫ fX = fY ≫ Spec.map (CommRingCat.ofHom σ)) (y : Y) {q : X} (hq : ρ y = q)
    [ValuationRing (X.presheaf.stalk q)]
    (hres : ∀ g : X.presheaf.stalk q, ∃ a : K, g - ((Scheme.ΓSpecIso (.of K)).inv ≫
      fX.appTop ≫ X.presheaf.germ ⊤ q trivial).hom a ∈ maximalIdeal _)
    (ξ : X.functionField)
    (hξ : letI := functionFieldAlgebra L fY;
      functionFieldMap ρ ξ ∉ Set.range (algebraMap L Y.functionField))
    (h : ∀ g : X.presheaf.stalk q, algebraMap _ X.functionField g = ξ →
      ∀ a : K, maximalIdeal (X.presheaf.stalk q) ≠ Ideal.span {g -
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop ≫ X.presheaf.germ ⊤ q trivial).hom a}) :
    ∀ g : Y.presheaf.stalk y, algebraMap _ Y.functionField g = functionFieldMap ρ ξ →
      ∀ b : L, maximalIdeal (Y.presheaf.stalk y) ≠ Ideal.span {g -
        ((Scheme.ΓSpecIso (.of L)).inv ≫ fY.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom b} := by
  subst hq
  let := functionFieldAlgebra L fY
  set φ := (ρ.stalkMap y).hom
  set cX := ((Scheme.ΓSpecIso (.of K)).inv ≫ fX.appTop ≫ X.presheaf.germ ⊤ (ρ y) trivial).hom
  set cY := ((Scheme.ΓSpecIso (.of L)).inv ≫ fY.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom
  have hinj : Function.Injective (algebraMap (Y.presheaf.stalk y) Y.functionField) :=
    IsFractionRing.injective _ _
  have hφ : ∀ g, algebraMap _ Y.functionField (φ g) =
      functionFieldMap ρ (algebraMap _ X.functionField g) :=
    algebraMap_stalkMap_eq_functionFieldMap' ρ y
  have hξ0 : functionFieldMap ρ ξ ≠ 0 := fun h0 => hξ ⟨0, by rw [map_zero, h0]⟩
  intro g' hg' b hb
  -- `ξ` is regular at `ρ y`
  obtain ⟨g, hg⟩ : ∃ g, algebraMap _ X.functionField g = ξ := by
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk (ρ y)) ξ with
      ⟨g, hg⟩ | ⟨t, ht⟩
    · exact ⟨g, hg⟩
    by_cases hu : IsUnit t
    · refine ⟨↑hu.unit⁻¹, ?_⟩
      have h1 := congrArg (algebraMap _ X.functionField) hu.unit.inv_mul
      rw [map_mul, map_one, IsUnit.unit_spec, ht] at h1
      have hξ' : ξ ≠ 0 := fun h0 => hξ0 (by rw [h0, map_zero])
      exact (mul_inv_eq_one₀ hξ').mp h1
    · exfalso
      have hmem : φ t ∈ maximalIdeal _ := map_nonunit φ t ((mem_maximalIdeal _).2 hu)
      have h1 : algebraMap _ Y.functionField (g' * φ t) = 1 := by
        rw [map_mul, hφ, ht, map_inv₀, hg', mul_inv_cancel₀ hξ0]
      rw [← map_one (algebraMap (Y.presheaf.stalk y) Y.functionField)] at h1
      exact (mem_maximalIdeal _).1 hmem
        ⟨⟨φ t, g', by rw [mul_comm]; exact hinj h1, hinj h1⟩, rfl⟩
  obtain ⟨a, ha⟩ := hres g
  have hφg : φ g = g' := hinj (by rw [hφ, hg, hg'])
  have hmem : g' - cY (σ a) ∈ maximalIdeal _ := by
    rw [← hφg, ← stalkMap_const fX fY σ ρ hsq y a, ← map_sub]
    exact map_nonunit φ _ ha
  have hb' : g' - cY b ∈ maximalIdeal _ := hb ▸ Ideal.mem_span_singleton_self _
  have hba : b - σ a = 0 := eq_zero_of_const_mem_maximalIdeal fY y (show cY (b - σ a) ∈ _ by
    rw [map_sub, ← sub_sub_sub_cancel_left (cY (σ a)) (cY b) g']
    exact sub_mem hmem hb')
  rw [sub_eq_zero.mp hba] at hb
  refine h g hg a (maximalIdeal_eq_span_of_map φ ha ?_ ?_)
  · rw [map_sub, hφg, stalkMap_const fX fY σ ρ hsq y a]
    exact hb
  · rw [map_sub, hφg, stalkMap_const fX fY σ ρ hsq y a]
    intro h0
    apply hξ
    refine ⟨σ a, ?_⟩
    have := congrArg (algebraMap (Y.presheaf.stalk y) Y.functionField) h0
    rw [map_sub, map_zero, hg', algebraMap_const fY y (σ a), sub_eq_zero] at this
    exact this.symm

/-- At a `K`-point every germ differs from a constant by an element of the maximal ideal. -/
private lemma exists_sub_constants_mem_maximalIdeal {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] (z : Spec (.of K) ⟶ X) [z.IsOver (Spec (.of K))]
    (g : X.presheaf.stalk (z (closedPoint K))) :
    ∃ a : K, g - BombieriVojta.constants z a ∈ maximalIdeal _ := by
  refine ⟨(Scheme.stalkClosedPointTo z).hom g, (mem_maximalIdeal _).2 fun hu => ?_⟩
  have h0 : (Scheme.stalkClosedPointTo z).hom
      (g - BombieriVojta.constants z ((Scheme.stalkClosedPointTo z).hom g)) = 0 := by
    rw [map_sub, BombieriVojta.stalkClosedPointTo_constants, sub_self]
  exact (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero h0

open scoped TensorProduct in
/-- **Linear disjointness from finite stages.** If `F ⊗[k] E` is a domain for every finite
subextension `E` of an algebraic extension `L / k`, then a `k`-linearly independent family of
`F` stays linearly independent over `L` inside any field `F'` containing `F` and `L`: the
coefficients of a relation lie in a finite subextension. -/
private lemma linearIndependent_algHom_of_isDomain_tensor {k L F F' : Type*} [Field k] [Field L]
    [Algebra k L] [Algebra.IsAlgebraic k L] [Field F] [Algebra k F] [Field F'] [Algebra L F']
    [Algebra k F'] [IsScalarTower k L F'] (β : F →ₐ[k] F')
    (hdom : ∀ E : IntermediateField k L, FiniteDimensional k E → IsDomain (F ⊗[k] E))
    {ι : Type*} [Finite ι] {x : ι → F} (hx : LinearIndependent k x) :
    LinearIndependent L (fun i => β (x i)) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  set E := IntermediateField.adjoin k (Set.range c)
  have hE : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  have := hdom E hE
  let : Algebra E F' := ((algebraMap L F').comp E.val.toRingHom).toAlgebra
  have : @IsScalarTower k E F' Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun a => (IsScalarTower.algebraMap_apply k L F' a)
  set b := Module.finBasis k E
  set c' : ι → E := fun i => ⟨c i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hcoe : ∀ i, c i = ∑ r, algebraMap k L (b.repr (c' i) r) * (b r : L) := by
    intro i
    have h := congrArg (fun e : E => (e : L)) (b.sum_repr (c' i))
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    change ((c' i : E) : L) = _
    rw [← h]
    exact Finset.sum_congr rfl fun r _ => Algebra.smul_def _ _
  have h0 : ∀ r, ∑ i, algebraMap k F (b.repr (c' i) r) * x i = 0 := by
    refine eq_zero_of_sum_algebraMap_mul_eq_zero β b _ ?_
    calc ∑ r, algebraMap E F' (b r) * β (∑ i, algebraMap k F (b.repr (c' i) r) * x i)
        = ∑ r, ∑ i, algebraMap L F' (algebraMap k L (b.repr (c' i) r) * (b r : L)) *
            β (x i) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, AlgHom.commutes, map_mul, IsScalarTower.algebraMap_apply k L F']
          change algebraMap L F' (b r : L) * _ = _
          ring
      _ = ∑ i, algebraMap L F' (c i) * β (x i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoe i, map_sum, Finset.sum_mul]
      _ = 0 := by simpa only [Algebra.smul_def] using hc
  have hr : ∀ r, b.repr (c' i) r = 0 := fun r =>
    Fintype.linearIndependent_iff.1 hx (fun i => b.repr (c' i) r)
      (by simpa only [Algebra.smul_def] using h0 r) i
  have : c' i = 0 := by
    rw [← b.sum_repr (c' i)]
    simp [hr]
  exact congrArg Subtype.val this

end BaseChange

/-- **Exceptional points over all fields of definition lie in a finite set.** Let `C` be a smooth
projective geometrically integral curve over a field `k` of characteristic zero, `D` a divisor on
`C` and `x₀, …, xₙ` rational functions linearly independent over `k`, and let `k̄` be an algebraic
closure of `k`. There is a finite set `Z` of `k̄`-points of `C` such that for every `z ∉ Z`, every
finite extension `ι : K → k̄` of `k`, every model `C_K = C ×_k K` of `C` over `K` (with
`ξ₁₀ = x₁ / x₀` transcendental over `K`) and every `K`-point `z_K` of `C_K` lying under `z`, the
point `z_K` is not in `Faltings.BombieriSiegel.exceptionalSet` of `C_K`, `D_K = π^* D` and the
`π^* xᵢ`.

The set `Z` is the image of finitely many `k̄`-points of `C_{k̄}`, given by the finiteness lemmas
behind `exceptionalSet_finite` over `k̄`: through the stalk map `𝒪_{C_K, z_K} → 𝒪_{C_{k̄}, z̄}`
each clause of `exceptionalSet` at `z_K` gives the corresponding condition at `z̄`, the plane
relations over `K` being the images of those over `k`. -/
public theorem exists_finite_forall_notMem_exceptionalSet (k : Type u) [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (x : Fin (n + 1) → C.functionField)
    (hx : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    ∃ Z : Set (Spec (.of kbar) ⟶ C), Z.Finite ∧ ∀ z ∉ Z,
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] (ι : K →ₐ[k] kbar)
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ C)
        (hπ : IsPullback π fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π]
        (hξ₁₀ : letI := functionFieldAlgebra K fK;
          Transcendental K (functionFieldMap π (x 1) / functionFieldMap π (x 0)))
        (DK : CK →₀ ℤ) (hDK : ∀ Q, DK Q = D (π Q)) (zK : Spec (.of K) ⟶ CK)
        (hzK : zK ≫ fK = 𝟙 _)
        (hz : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ zK ≫ π = z),
        zK ∉ exceptionalSet K fK DK (fun i => functionFieldMap π (x i)) hξ₁₀ := by
  classical
  let := functionFieldAlgebra k f
  by_cases htk : Transcendental k (x 1 / x 0)
  swap
  · refine ⟨∅, Set.finite_empty, fun z _ K _ _ _ ι CK fK π hπ _ _ _ _ hξ₁₀ => ?_⟩
    exfalso
    let : Algebra K CK.functionField := functionFieldAlgebra K fK
    let : Algebra k CK.functionField :=
      ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
    have : IsScalarTower k K CK.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let β : C.functionField →ₐ[k] CK.functionField := { functionFieldMap π with
      commutes' := fun a => functionFieldMap_algebraMap_of_comp_eq f fK π hπ.w a }
    apply hξ₁₀
    have h := ((not_not.1 htk).algHom β).tower_top K
    rwa [show β (x 1 / x 0) = functionFieldMap π (x 1) / functionFieldMap π (x 0) from
      map_div₀ (functionFieldMap π) _ _] at h
  -- the base change `C_{k̄}` and its instances
  set gb := Spec.map (CommRingCat.ofHom (algebraMap k kbar)) with hgb
  set fb : pullback f gb ⟶ Spec (.of kbar) := pullback.snd f gb
  set pr : pullback f gb ⟶ C := pullback.fst f gb
  have : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  have : IsCurve kbar fb := isCurve_pullback_snd_of_smooth k kbar f
  have : IsProper f := inferInstance
  have : IsProjectiveVariety kbar fb := (isProjectiveVariety_iff_isProjectiveMorphism kbar _).2
    (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one _
      (IsCurve.topologicalKrullDim_eq_one (k := kbar) (f := fb)).le)
  have : IsLocallyNoetherian (pullback f gb) := LocallyOfFiniteType.isLocallyNoetherian fb
  have : IsIntegral (pullback f gb) := inferInstance
  have : Flat gb := by
    rw [hgb, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have : Flat pr := inferInstance
  have : IsDominant pr := Stacks.Chow.isDominant_of_flat pr
  have : IsIntegralHom gb := IsIntegralHom.SpecMap_iff.2
    (algebraMap_isIntegral_iff.2 inferInstance)
  have : UniversallyClosed pr := inferInstance
  have hdom : ∀ E : IntermediateField k kbar, FiniteDimensional k E →
      IsDomain (TensorProduct k C.functionField E) :=
    fun E _ => isDomain_functionField_tensor k f E
  let xb : Fin (n + 1) → (pullback f gb).functionField := fun i => functionFieldMap pr (x i)
  let := functionFieldAlgebra kbar fb
  have hxb : LinearIndependent kbar xb := by
    let : Algebra k (pullback f gb).functionField :=
      ((algebraMap kbar (pullback f gb).functionField).comp (algebraMap k kbar)).toAlgebra
    have : IsScalarTower k kbar (pullback f gb).functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact linearIndependent_algHom_of_isDomain_tensor
      { functionFieldMap pr with
        commutes' := fun a => functionFieldMap_algebraMap_of_comp_eq f fb pr pullback.condition a }
      hdom hx
  -- the discriminants of the plane relations over `k`
  let R : Fin (n + 1) → Fin (n + 1) → k[X] := fun ν j =>
    let G := Faltings.FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) htk
    G.resultant (derivative G) G.natDegree (G.natDegree - 1)
  have hR : ∀ ν j, R ν j ≠ 0 := fun ν j =>
    (Faltings.FunctionField.one_le_natDegree_planeRelation_and_resultant_ne_zero k htk
      (isSeparable_adjoin_transcendental k f htk _)).2
  -- a function vanishing at each closed point of the support of `D`
  have hloc : ∀ y : C, ∃ h : C.functionField, IsClosed ({y} : Set C) →
      h ≠ 0 ∧ ∃ s ∈ maximalIdeal (C.presheaf.stalk y), algebraMap _ C.functionField s = h := by
    intro y
    by_cases hy : IsClosed ({y} : Set C)
    · have := Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one f y
        (coheight_eq_one_of_isCurve k f hy)
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk y)
      refine ⟨algebraMap _ C.functionField t, fun _ => ⟨?_, t, ?_, rfl⟩⟩
      · exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ht.ne_zero
      · exact (mem_maximalIdeal _).2 ht.not_isUnit
    · exact ⟨0, fun h => absurd h hy⟩
  choose hD hhD using hloc
  -- the finite set of `k̄`-points of `C_{k̄}`
  let cb : (z : Spec (.of kbar) ⟶ pullback f gb) → kbar →+*
      (pullback f gb).presheaf.stalk (z (closedPoint kbar)) := fun z =>
    ((Scheme.ΓSpecIso (.of kbar)).inv ≫ fb.appTop ≫
      (pullback f gb).presheaf.germ ⊤ (z (closedPoint kbar)) trivial).hom
  let T : (pullback f gb).functionField → kbar → Set (Spec (.of kbar) ⟶ pullback f gb) :=
    fun ξ b => {z | z ≫ fb = 𝟙 _ ∧ ∃ g : (pullback f gb).presheaf.stalk (z (closedPoint kbar)),
      algebraMap _ (pullback f gb).functionField g = ξ ∧ g - cb z b ∈ maximalIdeal _}
  let NU : (pullback f gb).functionField → Set (Spec (.of kbar) ⟶ pullback f gb) :=
    fun ξ => {z | z ≫ fb = 𝟙 _ ∧
      ∀ g : (pullback f gb).presheaf.stalk (z (closedPoint kbar)),
        algebraMap _ (pullback f gb).functionField g = ξ →
          ∀ b : kbar, maximalIdeal _ ≠ Ideal.span {g - cb z b}}
  let S : Set (Spec (.of kbar) ⟶ pullback f gb) :=
    T (xb 0) 0 ∪ (⋃ y ∈ (D.support : Set C) ∩ {y | IsClosed ({y} : Set C)},
      T (functionFieldMap pr (hD y)) 0) ∪
    (NU (xb 1 / xb 0) ∪ ⋃ a : {a : Fin (n + 1) // a ≠ 0}, NU (xb a / xb 0)) ∪
    ⋃ ν, ⋃ j, ⋃ b ∈ ((R ν j).map (algebraMap k kbar)).roots.toFinset, T (xb 1 / xb 0) b
  have h10ne : (1 : Fin (n + 1)) ≠ 0 := fun h => htk (by
    rw [h, div_self (hx.ne_zero 0)]; exact isAlgebraic_one)
  have h10 : xb 1 / xb 0 ∉ Set.range (algebraMap kbar (pullback f gb).functionField) :=
    div_notMem_range_algebraMap hxb h10ne
  have hS : S.Finite := by
    refine (((finite_setOf_sub_const_mem kbar fb _ 0 ?_).union
      (((D.support.finite_toSet.inter_of_left _)).biUnion fun y hy =>
        finite_setOf_sub_const_mem kbar fb _ 0 ?_)).union
      ((finite_setOf_notUniformizer kbar fb _ h10).union (Set.finite_iUnion fun a =>
        finite_setOf_notUniformizer kbar fb _ (div_notMem_range_algebraMap hxb a.2)))).union
      (Set.finite_iUnion fun ν => Set.finite_iUnion fun j =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun b _ =>
          finite_setOf_sub_const_mem kbar fb _ b fun h => h10 ⟨b, h.symm⟩)
    · simpa using hxb.ne_zero 0
    · rw [map_zero]
      exact (map_ne_zero_iff _ (functionFieldMap pr).injective).2 ((hhD y hy.2).1)
  refine ⟨(· ≫ pr) '' S, hS.image _, ?_⟩
  intro z hzZ K _ _ _ ι CK fK π hπ _ _ _ _ hξ₁₀ DK hDK zK hzK hz hmem
  apply hzZ
  set sι := Spec.map (CommRingCat.ofHom (ι : K →+* kbar))
  have hsK : sι ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = gb := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgb]
    congr 2
    ext a
    exact ι.commutes a
  have hzf : z ≫ f = 𝟙 _ ≫ gb := by
    rw [← hz, Category.assoc, Category.assoc, hπ.w, ← Category.assoc zK, hzK, Category.id_comp,
      Category.id_comp, hsK]
  set zb : Spec (.of kbar) ⟶ pullback f gb := pullback.lift z (𝟙 _) hzf
  have hzb : zb ≫ fb = 𝟙 _ := pullback.lift_snd _ _ _
  refine ⟨zb, ?_, pullback.lift_fst _ _ _⟩
  -- the comparison morphism `C_{k̄} ⟶ C_K`
  set ρ : pullback f gb ⟶ CK := hπ.lift pr (fb ≫ sι)
    (by rw [Category.assoc, hsK]; exact pullback.condition)
  have hρπ : ρ ≫ π = pr := hπ.lift_fst _ _ _
  have hρf : ρ ≫ fK = fb ≫ sι := hπ.lift_snd _ _ _
  have hsq : IsPullback ρ fb fK sι :=
    IsPullback.of_right (by rw [hρπ, hsK]; exact IsPullback.of_hasPullback f gb) hρf hπ
  have : Flat sι := by
    let := (ι : K →+* kbar).toAlgebra
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have : Flat ρ := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : IsDominant ρ := Stacks.Chow.isDominant_of_flat ρ
  have hzbρ : zb ≫ ρ = sι ≫ zK := hπ.hom_ext
    (by rw [Category.assoc, hρπ, pullback.lift_fst, Category.assoc, hz])
    (by rw [Category.assoc, hρf, ← Category.assoc, hzb, Category.id_comp, Category.assoc, hzK,
      Category.comp_id])
  set p := zb (closedPoint kbar)
  have hpt : ρ p = zK (closedPoint K) := by
    have : ρ p = zK (sι (closedPoint kbar)) := congr($(hzbρ) (closedPoint kbar))
    exact this.trans (congrArg (⇑zK) (Subsingleton.elim _ _))
  have hπp : π (zK (closedPoint K)) = pr p := by
    rw [← hpt]; exact congr($(hρπ) p)
  -- local facts at `z_K`
  have : Smooth fK := MorphismProperty.of_isPullback hπ ‹Smooth f›
  have : IsSeparated fK := MorphismProperty.of_isPullback hπ inferInstance
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : IsNormal CK := Faltings.FunctionField.isNormal_of_smooth K fK
  have : ValuationRing (CK.presheaf.stalk (zK (closedPoint K))) :=
    valuationRing_stalk fK (isClosed_singleton_apply_closedPoint fK zK hzK)
  let : CK.Over (Spec (.of K)) := ⟨fK⟩
  have : zK.IsOver (Spec (.of K)) := ⟨by
    rw [show (Spec (.of K) ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K K))
      from rfl, Algebra.algebraMap_self]
    exact hzK.trans (Spec.map_id _).symm⟩
  have hres := exists_sub_constants_mem_maximalIdeal zK
  have hxρ : ∀ i j, functionFieldMap ρ (functionFieldMap π (x i) / functionFieldMap π (x j)) =
      xb i / xb j := fun i j => by
    rw [map_div₀, functionFieldMap_comp_apply' ρ π hρπ, functionFieldMap_comp_apply' ρ π hρπ]
  obtain ⟨-, h⟩ := hmem
  rcases h with h1 | ⟨-, h2⟩ | ⟨-, ν, j, -, -, -, g, hg, a, hga, hRa⟩ | ⟨-, a, ha, h4⟩
  · rw [hDK, hπp] at h1
    by_cases hD0 : D (pr p) = 0
    · rw [hD0, add_zero] at h1
      have hco : Order.coheight (zK (closedPoint K)) = 1 := by
        by_contra hc
        rw [Scheme.ord_eq_zero_of_coheight_neq_one hc] at h1
        exact lt_irrefl _ h1
      have hx0 : functionFieldMap π (x 0) ≠ 0 :=
        (map_ne_zero_iff _ (functionFieldMap π).injective).2 (hx.ne_zero 0)
      obtain ⟨s, hs, hsx⟩ := (Faltings.ord_pos_iff hco hx0).1 h1
      have := exists_germ_sub_const_mem_of_map fK fb ι ρ hρf p hpt _ 0 ⟨s, hsx, by simpa using hs⟩
      rw [map_zero, functionFieldMap_comp_apply' ρ π hρπ] at this
      exact Or.inl (Or.inl (Or.inl ⟨hzb, this⟩))
    · have hy : pr p ∈ (D.support : Set C) := Finsupp.mem_support_iff.2 hD0
      have hycl : IsClosed ({pr p} : Set C) := by
        have := pr.isClosedMap _ (isClosed_singleton_apply_closedPoint fb zb hzb)
        rwa [Set.image_singleton] at this
      obtain ⟨-, s, hs, hsx⟩ := hhD (pr p) hycl
      have := exists_germ_sub_const_mem_of_map f fb (algebraMap k kbar) pr pullback.condition p rfl
        (hD (pr p)) 0 ⟨s, hsx, by simpa using hs⟩
      rw [map_zero] at this
      exact Or.inl (Or.inl (Or.inr (Set.mem_biUnion (x := pr p) ⟨hy, hycl⟩ ⟨hzb, this⟩)))
  · have := notUniformizer_of_map fK fb ι ρ hρf p hpt hres _ (by rw [hxρ]; exact h10) h2
    rw [hxρ] at this
    exact Or.inl (Or.inr (Or.inl ⟨hzb, this⟩))
  · have hT := exists_germ_sub_const_mem_of_map fK fb ι ρ hρf p hpt _ a ⟨g, hg, hga⟩
    rw [hxρ] at hT
    -- the plane relation over `K` is the image of the one over `k`
    let : Algebra K CK.functionField := functionFieldAlgebra K fK
    let : Algebra k CK.functionField :=
      ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
    have : IsScalarTower k K CK.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let β : C.functionField →ₐ[k] CK.functionField := { functionFieldMap π with
      commutes' := fun a => functionFieldMap_algebraMap_of_comp_eq f fK π hπ.w a }
    have := isDomain_functionField_tensor k f K
    have hLD := fun g hg => eq_zero_of_sum_algebraMap_mul_eq_zero β (Module.finBasis k K) g hg
    have hint : IsIntegral k⟮x 1 / x 0⟯ (x ν / x j) := by
      have hnot : x 1 / x 0 ∉ Set.range (algebraMap k C.functionField) := by
        rintro ⟨b, hb⟩; exact htk (hb ▸ isAlgebraic_algebraMap b)
      have hfin := (Faltings.FunctionField.finrank_adjoin_eq_finsum_ord k f (x 1 / x 0) hnot).1
      exact @IsIntegral.of_finite _ _ _ _ _ hfin _
    have hG : ∀ (t w : CK.functionField) (ht : Transcendental K t), t = β (x 1 / x 0) →
        w = β (x ν / x j) → Faltings.FunctionField.planeRelation K t w ht =
          (Faltings.FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) htk).map
            (Polynomial.mapRingHom (algebraMap k K)) := by
      rintro _ _ ht rfl rfl
      exact planeRelation_map_of_linearDisjoint (Module.finBasis k K) β hLD _ _ htk ht hint
    rw [hG _ _ hξ₁₀ (map_div₀ (functionFieldMap π) _ _).symm
      (map_div₀ (functionFieldMap π) _ _).symm] at hRa
    have hφ : Function.Injective (Polynomial.mapRingHom (algebraMap k K)) :=
      Polynomial.map_injective _ (algebraMap k K).injective
    dsimp only at hRa
    rw [Polynomial.natDegree_map_eq_of_injective hφ, Polynomial.derivative_map,
      Polynomial.resultant_map_map, Polynomial.coe_mapRingHom] at hRa
    have hroot : ι a ∈ ((R ν j).map (algebraMap k kbar)).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero (hR ν j)),
        Polynomial.IsRoot, show (R ν j).map (algebraMap k kbar) =
          ((R ν j).map (algebraMap k K)).map (ι : K →+* kbar) by
            rw [Polynomial.map_map, AlgHom.comp_algebraMap]]
      exact (Polynomial.eval_map_apply (f := (ι : K →+* kbar)) a).trans
        ((congrArg ι hRa).trans (map_zero _))
    exact Or.inr (Set.mem_iUnion.2 ⟨ν, Set.mem_iUnion.2 ⟨j, Set.mem_biUnion hroot ⟨hzb, hT⟩⟩⟩)
  · have := notUniformizer_of_map fK fb ι ρ hρf p hpt hres _
      (by rw [hxρ]; exact div_notMem_range_algebraMap hxb ha) h4
    rw [hxρ] at this
    exact Or.inl (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨⟨a, ha⟩, hzb, this⟩)))

end Faltings.BombieriSiegel
