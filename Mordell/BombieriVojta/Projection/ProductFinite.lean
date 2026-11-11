module
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.BombieriVojta.Projection.Finite
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSections
public import Mordell.BombieriVojta.Projection.ProductAffine

/-!
# The product projections `π_{ab}` are finite

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P₁` a divisor of degree one supported on closed points (the source's `P`), `N ≥ 2g + 1`,
and `x₀, …, xₙ` a `k`-basis of the Riemann–Roch space `L(N P₁)` inside the function field
`k(C)`. For `a, b ∈ {1, …, n}` let
`π_{ab} = π_a × π_b : C ×_k C ⤏ ℙ¹_k ×_k ℙ¹_k`. If the basis satisfies (G1), each of `π_a` and
`π_b` is induced by a finite morphism `φ_a, φ_b : C ⟶ ℙ¹_k`, and the product
`φ_a ×_k φ_b : C ×_k C ⟶ ℙ¹_k ×_k ℙ¹_k` is finite, finiteness being stable under base change and
composition. Its rational map is `π_{ab}`: both are determined by their restriction to the
generic point of `C ×_k C`, and there the components of `φ_a ×_k φ_b` are the points
`(pr₁^* x₀ : pr₁^* x_a)` and `(pr₂^* x₀ : pr₂^* x_b)` that define `π_{ab}`, by naturality of the
morphism to projective space attached to a family of sections.

## Main results

* `Faltings.BombieriVojta.exists_isFinite_toRationalMap_eq_productProjectionToProjectiveLine`:
  under (G1), for all `a, b ∈ {1, …, n}` the rational map `π_{ab}` is induced by a finite
  morphism `C ×_k C ⟶ ℙ¹_k ×_k ℙ¹_k`.

## Implementation notes

"`π_{ab}` is a finite morphism" is stated as: there is a morphism
`φ : C ×_k C ⟶ ℙ¹_k ×_k ℙ¹_k` with `IsFinite φ` whose rational map `φ.toRationalMap` is
`Faltings.BombieriVojta.productProjectionToProjectiveLine`, exactly as
`Faltings.BombieriVojta.exists_isFinite_toRationalMap_eq_projectionToProjectiveLine` states it
for `π_a`. Here `C ×_k C` is `pullback f f` and `ℙ¹_k ×_k ℙ¹_k` is the fibre product of
`projectiveSpaceOver 1 (Spec k)` with itself over `Spec k`. The indices `a, b ∈ {1, …, n}` are
`a b : Fin n`, used as `a.succ`, `b.succ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings.BombieriVojta

open Faltings.BombieriSiegel

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `P₁` a divisor of degree one on closed points, `N ≥ 2g + 1`, and `x₀, …, xₙ` a
`k`-basis of `L(N P₁)` satisfying (G1). Then for all `a, b ∈ {1, …, n}` the product projection
`π_{ab} = π_a × π_b : C ×_k C ⤏ ℙ¹_k ×_k ℙ¹_k` is induced by a finite morphism
`C ×_k C ⟶ ℙ¹_k ×_k ℙ¹_k`, namely `φ_a ×_k φ_b` for the finite morphisms `φ_a, φ_b`
inducing `π_a, π_b`. -/
@[faltings "lem_bvs_product_projection_finite"]
public theorem exists_isFinite_toRationalMap_eq_productProjectionToProjectiveLine (k : Type u)
    [Field k] [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (a b : Fin n) :
    ∃ φ : pullback f f ⟶ pullback (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)),
      IsFinite φ ∧
        φ.toRationalMap =
          productProjectionToProjectiveLine k f hg P₁ hP₁cl hP₁ N hN x hli hspan a b := by
  have hDcl := isClosed_of_mem_support_smul hP₁cl (N : ℤ)
  have hD := finsum_smul_mul_residueDegree f hP₁ (N : ℤ)
  obtain ⟨φa, hφa, hra⟩ := exists_isFinite_toRationalMap_eq_projectionToProjectiveLine k f hg _
    hDcl N hN hD x hli hspan hG1 a
  obtain ⟨φb, hφb, hrb⟩ := exists_isFinite_toRationalMap_eq_projectionToProjectiveLine k f hg _
    hDcl N hN hD x hli hspan hG1 b
  have hoa := comp_structureMap_of_toRationalMap_eq (hD := hD) (hspan := hspan) hra
  have hob := comp_structureMap_of_toRationalMap_eq (hD := hD) (hspan := hspan) hrb
  refine ⟨pullback.map f f _ _ φa φb (𝟙 _) (by simp [hoa]) (by simp [hob]),
    MorphismProperty.pullbackMap (P := @IsFinite) hφa hφb hoa.symm hob.symm, ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [productProjectionToProjectiveLine, Scheme.RationalMap.fromFunctionField_ofFunctionField,
    Scheme.RationalMap.fromFunctionField_toRationalMap]
  simp only [Scheme.PartialMap.fromFunctionField,
    Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]
  -- `simp only [pullback.lift_fst]` cannot rewrite here: the motive is ill-typed.
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ?_).trans (pullback.lift_fst _ _ _).symm
    refine (congrArg _ (pullback.lift_fst _ _ _)).trans ?_
    exact fromSpecStalk_comp_comp_eq_toProjectiveSpaceOver f _ φa _ _ _
      (fromSpecStalk_comp_of_toRationalMap_eq (hD := hD) (hspan := hspan) hra) _
  · refine ((Category.assoc _ _ _).trans ?_).trans (pullback.lift_snd _ _ _).symm
    refine (congrArg _ (pullback.lift_snd _ _ _)).trans ?_
    rw [pullback.condition]
    exact fromSpecStalk_comp_comp_eq_toProjectiveSpaceOver f _ φb _ _ _
      (fromSpecStalk_comp_of_toRationalMap_eq (hD := hD) (hspan := hspan) hrb) _

end Faltings.BombieriVojta
