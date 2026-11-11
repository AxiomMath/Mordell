module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# The divisor of a norm

Let `f : X ⟶ Y` be a proper morphism of integral schemes locally of finite type over a field `K`,
such that the function field `K(X)` is a finite extension of `K(Y)` through the map induced by
`f`. For a non-zero rational function `r` on `X`, the push-forward of its principal divisor is the
principal divisor of its norm: `f_* div(r) = div(N_{K(X)/K(Y)} r)`. Pointwise, at a point `y` of
`Y` of codimension one,
`ord_y (N r) = ∑_{x ↦ y, codim x = 1} [κ(x) : κ(y)] · ord_x r`.

## Main results

* `Faltings.ord_norm_eq_finsum_mapCoeff_mul_ord`: the order of vanishing of the norm of `r` at a
  point `y` of `Y` is the push-forward, in the sense of `AlgebraicGeometry.AlgebraicCycle.map`
  with codimension weights, of the orders of vanishing of `r`.

## Implementation notes

Mathlib has no cycle `div r` of a rational function, so the statement is written pointwise, in the
form of `Function.locallyFinsupp.map_apply`: the right-hand side is the value at `y` of the
push-forward `AlgebraicCycle.map f Order.coheight Order.coheight` of the function
`x ↦ Scheme.ord r x`. At points of codimension other than one both sides vanish.

The field extension `K(Y) → K(X)` is taken as an `Algebra` instance, characterised by its
compatibility with the germs of `f` on sections; such a compatible map exists exactly when `f`
is dominant.

## References

* [W. Fulton, *Intersection Theory*, Prop. 1.4(b)][fulton1998]
* [E. Bombieri, *The Mordell conjecture revisited*, §9][bombieri1990]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Faltings

/-- A morphism of integral schemes through which some field homomorphism `K(Y) → K(X)` is
compatible with the germs of sections is dominant. -/
private lemma isDominant_of_algebraMap_germ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Algebra Y.functionField X.functionField]
    (hf : ∀ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)),
      algebraMap Y.functionField X.functionField (Y.germToFunctionField U s) =
        X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)) :
    IsDominant f := by
  refine ⟨dense_iff_inter_open.mpr fun W hW hWne ↦ ⟨f.base (genericPoint X), ?_, ⟨_, rfl⟩⟩⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hy0U, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base (genericPoint X))) isOpen_univ
  have hηW : genericPoint Y ∈ W :=
    (genericPoint_spec Y).mem_open_set_iff hW |>.mpr (by simpa using hWne)
  have hηU : genericPoint Y ∈ U :=
    (genericPoint_spec Y).mem_open_set_iff U.isOpen |>.mpr ⟨_, Set.mem_univ _, hy0U⟩
  obtain ⟨s, hsW, hηs⟩ := hU.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨genericPoint Y, hηW⟩ hηU
  have : Nonempty U := ⟨⟨_, hy0U⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, hy0U⟩⟩
  have hs := hf U s
  have hunit : IsUnit (Y.germToFunctionField U s) := (Y.mem_basicOpen s _ hηU).mp hηs
  have hne : X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) ≠ 0 := by
    rw [← hs]
    exact (map_ne_zero _).mpr hunit.ne_zero
  have hX : genericPoint X ∈ X.basicOpen (f.app U s) :=
    (X.mem_basicOpen _ _ hy0U).mpr (isUnit_iff_ne_zero.mpr hne)
  rw [← Scheme.preimage_basicOpen] at hX
  exact hsW hX

/-- The field homomorphism `K(Y) → K(X)` compatible with germs is `dominantFunctionFieldMap`. -/
private lemma algebraMap_eq_dominantFunctionFieldMap {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] [Algebra Y.functionField X.functionField]
    (hf : ∀ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)),
      algebraMap Y.functionField X.functionField (Y.germToFunctionField U s) =
        X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)) :
    algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hgen : f.base (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant f
  have hηX : genericPoint X ∈ f ⁻¹ᵁ U := by
    change f.base (genericPoint X) ∈ U
    rw [hgen]
    exact hηU
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hηX⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(Y, U)) (RingHom.ext fun s ↦ ?_)
  change algebraMap Y.functionField X.functionField ((Y.germToFunctionField U).hom s) =
    dominantFunctionFieldMap f ((Y.germToFunctionField U).hom s)
  rw [hf U s, dominantFunctionFieldMap_germToFunctionField_of_mem f (genericPoint X) U
    (hgen ▸ hηU) (f ⁻¹ᵁ U) hηX le_rfl s, Scheme.Hom.appLE_eq_app]

/-- A dominant morphism with finite function-field extension has residue transcendence degree
zero at the generic point. -/
private lemma residueTrdeg_genericPoint_eq_zero {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] [Algebra Y.functionField X.functionField]
    [Module.Finite Y.functionField X.functionField]
    (halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f) :
    Stacks.Chow.residueTrdeg f (genericPoint X) = 0 := by
  unfold Stacks.Chow.residueTrdeg
  letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have hφ : functionFieldMap f = algebraMap Y.functionField X.functionField := by
    rw [halg]
    exact (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f _ (map_genericPoint_of_isDominant f))).symm
  have hc := residueFieldMap_comp_genericResidueEquivOfDominant f
  rw [Algebra.trdeg_eq_of_ringEquiv (genericResidueEquivOfDominant f).symm
    (genericResidueEquiv X).symm fun a ↦ ?_]
  · exact trdeg_eq_zero
  · have h := congr($hc ((genericResidueEquivOfDominant f).symm a))
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, hφ] at h
    rw [RingHom.algebraMap_toAlgebra, h, RingEquiv.symm_apply_apply]

/-- Over a field, a dominant morphism of integral schemes with finite function-field extension
preserves the delta-dimension: that of `X` is the relative dimension of `Y` at its generic point.
-/
private lemma schemeDeltaDimension_eq_of_finite {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [LocallyOfFiniteType f] [IsDominant f]
    [Algebra Y.functionField X.functionField] [Module.Finite Y.functionField X.functionField]
    (halg : algebraMap Y.functionField X.functionField = dominantFunctionFieldMap f) :
    Stacks.Chow.schemeDeltaDimension (Stacks.Chow.fieldChowSituation K) (X ↘ Spec (.of K)) =
      WithBotTop.coe (Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation K).dimensionFunction (Y ↘ Spec (.of K))
        (genericPoint Y)) := by
  rw [Stacks.Chow.schemeDeltaDimension_eq_genericPoint, ← comp_over f (Spec (.of K)),
    Stacks.Chow.relativeDimension_comp_eq_add_trdeg, residueTrdeg_genericPoint_eq_zero f halg,
    map_genericPoint_of_isDominant f]
  simp

/-- **Divisor of a norm** (Fulton, Prop. 1.4(b)). Let `f : X ⟶ Y` be a proper morphism of
integral schemes locally of finite type over a field `K`, with `K(X)` finite over `K(Y)` through
the map induced by `f`. Then for a non-zero rational function `r` on `X`, the order of vanishing
of `Algebra.norm K(Y) r` at any point `y` equals `∑ᶠ x ∈ f ⁻¹' {y}, ord_x r * mapCoeff f x`. In
other words, `div (N r)` is the push-forward `AlgebraicCycle.map f coheight coheight (div r)`. -/
@[faltings "lem_bvr_norm_divisor"]
public theorem ord_norm_eq_finsum_mapCoeff_mul_ord {K : Type*} [Field K] {X Y : Scheme}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [LocallyOfFiniteType (Y ↘ Spec (.of K))]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsProper f]
    [Algebra Y.functionField X.functionField] [Module.Finite Y.functionField X.functionField]
    (hf : ∀ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)),
      algebraMap Y.functionField X.functionField (Y.germToFunctionField U s) =
        X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s))
    {r : X.functionField} (hr : r ≠ 0) (y : Y) :
    Y.ord (Algebra.norm Y.functionField r) y =
      ∑ᶠ x ∈ f.base ⁻¹' {y},
        X.ord r x * (AlgebraicCycle.mapCoeff f coheight coheight x : ℤ) := by
  classical
  have : IsDominant f := isDominant_of_algebraMap_germ f hf
  have halg := algebraMap_eq_dominantFunctionFieldMap f hf
  have hp := comp_over f (Spec (.of K))
  have hnX := schemeDeltaDimension_eq_of_finite (K := K) f halg
  have hnY := Stacks.Chow.schemeDeltaDimension_eq_genericPoint (Stacks.Chow.fieldChowSituation K)
    (Y ↘ Spec (.of K))
  by_cases hy : coheight y = 1
  · have hfib : ∀ x : X, f.base x = y → coheight x = 1 := fun x hx ↦
      (Stacks.Chow.relativeDimension_eq_sub_one_iff_coheight_eq_one _ _ hnX x).mp
        (Stacks.Chow.relativeDimension_eq_sub_one_of_mem_fibre _ _ _ hnX hnY f hp hy hx)
    obtain ⟨V, hyV, hfin⟩ :=
      Stacks.Chow.exists_isFinite_morphismRestrict_of_coheight_eq_one _ _ _ hnX hnY f hp y hy
    rw [← Stacks.Chow.finsum_ord_mul_residueDegree_of_coheight_eq_one f halg r hr y hy hfib
      V hyV hfin]
    refine finsum_mem_congr rfl fun x (hx : f.base x = y) ↦ ?_
    simp [AlgebraicCycle.mapCoeff, hfib x hx, hx, hy]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hy, eq_comm]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x (hx : f.base x = y) ↦ ?_
    by_cases hxc : coheight x = 1
    · simp [AlgebraicCycle.mapCoeff, hxc, hx, Ne.symm hy]
    · simp [Scheme.ord_eq_zero_of_coheight_neq_one hxc]

end Faltings

end
