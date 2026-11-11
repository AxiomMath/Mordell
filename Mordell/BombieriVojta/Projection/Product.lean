module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Projection.Basic
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap

/-!
# The product projections `π_{ab} : C × C ⇢ ℙ¹ × ℙ¹`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P₁` a divisor of degree one supported on closed points (the source's `P`), `N ≥ 2g + 1`, and
`x_0, …, x_n` a `k`-basis of `L(N P₁)` inside `k(C)`. For `a ∈ {1, …, n}` the projection
`π_a = (x_0 : x_a) : C ⇢ ℙ¹_k` is `Faltings.BombieriVojta.projectionToProjectiveLine`. For
`a, b ∈ {1, …, n}`, the product projection is `π_{ab} = π_a × π_b : C ×_k C ⇢ ℙ¹_k ×_k ℙ¹_k`,
`(x, x') ↦ (x_0 : x_a ; x'_0 : x'_b)`.

## Main definitions

* `Faltings.BombieriVojta.productProjectionToProjectiveLine`: the rational map `π_{ab}` over `k`.

## Implementation notes

Because `C` is geometrically integral over `k`, `C ×_k C` is integral, and a `k`-rational map out
of it is determined by its restriction to `Spec k(C ×_k C)`
(`AlgebraicGeometry.Scheme.RationalMap.ofFunctionField`). Write `x_ν` for `pr₁^* x_ν` and
`x'_ν` for `pr₂^* x_ν` in `k(C ×_k C)`, where `pr_i^*` is `AlgebraicGeometry.functionFieldMap` of
the projection. The projections are dominant because they are base changes of the surjective map
`C → Spec k`. The `k(C ×_k C)`-point of `ℙ¹_k ×_k ℙ¹_k` is the pair of points
`(x_0 : x_a)` and `(x'_0 : x'_b)`, each built by
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver` exactly as for `π_a`. So the two
components of `π_{ab}` are `π_a ∘ pr₁` and `π_b ∘ pr₂`. `ℙ¹_k ×_k ℙ¹_k` is the fibre product
of `ℙ¹_k = projectiveSpaceOver 1 (Spec k)` with itself over `Spec k`. The indices
`a, b ∈ {1, …, n}` are `a b : Fin n`, used as `a.succ` and `b.succ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 8, pp. 629–630
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings.BombieriVojta

/-- The product projection `π_{ab} = π_a × π_b : C ×_k C ⤏ ℙ¹_k ×_k ℙ¹_k`,
`(x, x') ↦ (x_0 : x_a ; x'_0 : x'_b)`, for `a, b ∈ {1, …, n}` (here `a.succ`, `b.succ` with
`a b : Fin n`). It is a rational map over `k` built from the same curve data as
`Faltings.BombieriVojta.projectionToProjectiveLine`. Its restriction to `Spec k(C ×_k C)` is the
pair of points `(pr₁^* x_0 : pr₁^* x_a)` and `(pr₂^* x_0 : pr₂^* x_b)`, so its components are
`π_a ∘ pr₁` and `π_b ∘ pr₂`. -/
@[faltings "def_bvs_product_projection", expose]
public noncomputable def productProjectionToProjectiveLine (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (_hg : 2 ≤ genus f)
    (P₁ : C →₀ ℤ) (_hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (_hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (_hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (_hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (a b : Fin n) :
    pullback f f ⤏ pullback (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
  letI := functionFieldAlgebra k f
  let s : Spec (pullback f f).functionField ⟶ Spec (.of k) :=
    (pullback f f).fromSpecStalk _ ≫ pullback.fst f f ≫ f
  let pt (pr : pullback f f ⟶ C) [IsDominant pr] (c : Fin n) :
      Spec (pullback f f).functionField ⟶ projectiveSpaceOver 1 (Spec (.of k)) :=
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
      (fun i => (Scheme.ΓSpecIso (.of (pullback f f).functionField)).inv
        (![functionFieldMap pr (x 0), functionFieldMap pr (x c.succ)] i))
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
        ((Ne.isUnit ((map_ne_zero _).2 (hli.ne_zero 0))).map
          (Scheme.ΓSpecIso (.of (pullback f f).functionField)).inv.hom))
      s
  Scheme.RationalMap.ofFunctionField (pullback.fst f f ≫ f)
    (pullback.fst (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) ≫
        (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)))
    (pullback.lift (pt (pullback.fst f f) a) (pt (pullback.snd f f) b)
      ((Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst _ _ _).trans
        (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst _ _ _).symm))
    ((pullback.lift_fst_assoc _ _ _ _).trans
      (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst _ _ _))

end Faltings.BombieriVojta
