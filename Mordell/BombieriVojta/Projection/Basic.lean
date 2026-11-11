module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# The projections `π_a : C ⇢ ℙ¹`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `D` a divisor of degree `N ≥ 2g + 1` supported on closed points (the source's `NP`, with `P`
of degree one), and `x₀, …, xₙ` a `k`-basis of the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))`
inside the function field `k(C)`: these are the coordinates of `φ_D : C → ℙⁿ`.
For `a ∈ {1, …, n}`, `π_a : C ⇢ ℙ¹_k` is the rational map
`(x_0 : x_a)` over `k`. On `ℙ¹_k`, with homogeneous coordinates `(X_0 : X_1)`, the point
`∞ = (0 : 1)` is `X_0 = 0`, and `𝔸¹ = {X_0 ≠ 0}` has the affine coordinate `X_1 / X_0`. Its
pull-back by `π_a` is `ξ_a = x_a / x_0`, since `(x_0 : x_a) = (1 : ξ_a)`.

## Main definitions

* `Faltings.BombieriVojta.projectionToProjectiveLine`: the projection `π_a = (x_0 : x_a)`, as a
  `k`-rational map `C ⤏ ℙ¹_k`.

## Main results

* `Faltings.BombieriVojta.projectionToProjectiveLine_fromFunctionField`: the restriction of `π_a`
  to `Spec k(C)` is the point `(x_0 : x_a)`.
* `Faltings.BombieriVojta.isOver_projectionToProjectiveLine`: `π_a` is a rational map over `k`.

## Implementation notes

`ℙ¹_k` is `AlgebraicGeometry.projectiveSpaceOver 1 (Spec k)`, the base change of
`Proj ℤ[T_0, T_1]` to `k`, with homogeneous coordinates `T_0, T_1`; so `∞` is the zero locus of
`T_0` and `𝔸¹` its basic open. A rational map from an integral `k`-scheme `C` to a `k`-scheme
locally of finite type is determined by its restriction to `Spec k(C)`
(`AlgebraicGeometry.Scheme.RationalMap.ofFunctionField`). The `k(C)`-point is the morphism
`Spec k(C) → ℙ¹_k` attached to the global sections `x_0, x_a` of `Spec k(C)`
(`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver`), which span the unit ideal because
`x_0 ≠ 0`, by linear independence of the basis.

As in `Faltings.BombieriSiegel.finrank_adjoin_div_eq`, sections of `𝒪(D)` are rational
functions: `D` is a `C →₀ ℤ`, `L(D)` is `{g | g = 0 ∨ ∀ Q closed, 0 ≤ ord_Q g + D(Q)}` (the form
of `Faltings.BombieriSiegel.IsGenericBasis.span_eq`), and `k(C)` is a `k`-algebra through
`AlgebraicGeometry.functionFieldAlgebra k f`. The index `a ∈ {1, …, n}` is `a : Fin n`, used as
`a.succ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 8, p. 629; Sec. 9, p. 632
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings.BombieriVojta

/-- The projection `π_a = (x_0 : x_a) : C ⤏ ℙ¹_k` for `a ∈ {1, …, n}` (here `a.succ` with
`a : Fin n`), a rational map over `k`, where `C` is a smooth projective geometrically integral
curve of genus `≥ 2` over the number field `k`, `D` a divisor of degree `N ≥ 2g + 1` on closed
points, and `x_0, …, x_n` a `k`-basis of `L(D)` in `k(C)`. Its restriction to `Spec k(C)` is the
point `(x_0 : x_a)`; it lies in `𝔸¹ = {T_0 ≠ 0}`, where the affine coordinate `T_1 / T_0` pulls
back to `ξ_a = x_a / x_0`. -/
@[faltings "def_bvs_projection", expose]
public noncomputable def projectionToProjectiveLine (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (_hg : 2 ≤ genus f)
    (D : C →₀ ℤ) (_hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (_hN : 2 * genus f + 1 ≤ N) (_hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (_hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (a : Fin n) : C ⤏ projectiveSpaceOver 1 (Spec (.of k)) :=
  haveI := isProper_projectiveSpaceOver 1 (Spec (.of k))
  letI := functionFieldAlgebra k f
  Scheme.RationalMap.ofFunctionField f (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
      (fun i => (Scheme.ΓSpecIso (.of C.functionField)).inv (![x 0, x a.succ] i))
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
        ((Ne.isUnit (hli.ne_zero 0)).map (Scheme.ΓSpecIso (.of C.functionField)).inv.hom))
      (C.fromSpecStalk _ ≫ f))
    (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst _ _ _)

/-- The restriction of `π_a` to `Spec k(C)` is the point `(x_0 : x_a)` of `ℙ¹_k`, the morphism
attached to the sections `x_0, x_a` of `Spec k(C)`. -/
public theorem projectionToProjectiveLine_fromFunctionField (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (a : Fin n) :
    (projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a).fromFunctionField =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of C.functionField)).inv (![x 0, x a.succ] i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (letI := functionFieldAlgebra k f; hli.ne_zero 0)).map
            (Scheme.ΓSpecIso (.of C.functionField)).inv.hom))
        (C.fromSpecStalk _ ≫ f) :=
  haveI := isProper_projectiveSpaceOver 1 (Spec (.of k))
  Scheme.RationalMap.fromFunctionField_ofFunctionField _ _ _ _

/-- `π_a` is a rational map over `k`, where `C` is a `k`-scheme through `f`. -/
public theorem isOver_projectionToProjectiveLine (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (a : Fin n) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    (projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a).IsOver (Spec (.of k)) :=
  letI : C.Over (Spec (.of k)) := ⟨f⟩
  haveI := isProper_projectiveSpaceOver 1 (Spec (.of k))
  Scheme.RationalMap.isOver_iff.mpr
    (Scheme.RationalMap.equivFunctionField f (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
      ⟨_, Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst _ _ _⟩).2

end Faltings.BombieriVojta
