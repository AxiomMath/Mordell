module

public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
public import Mordell.CurveProduct.Diagonal

/-!
# The product of two curves is a surface

Let `k` be a field and let `C`, `D` be smooth projective geometrically integral curves over `k`.
The fibre product `C ×_k D`, with its structure morphism to `Spec k`, is a smooth projective
geometrically integral surface over `k`: it is a projective variety, geometrically integral,
and smooth of relative dimension `1 + 1 = 2`. The case `D = C` gives the surface `C ×_k C`.

## Main results

* `Faltings.IsSmoothProjectiveCurve.surface_pullback`: for curves `f : C ⟶ Spec k` and
  `g : D ⟶ Spec k`, the morphism `pullback.fst f g ≫ f : pullback f g ⟶ Spec k` is a
  projective variety, geometrically integral and smooth of relative dimension `2`.

## Implementation notes

A surface over `k` is expressed, as elsewhere in this library, by the three classes
`AlgebraicGeometry.IsProjectiveVariety k`, `AlgebraicGeometry.GeometricallyIntegral` and
`AlgebraicGeometry.SmoothOfRelativeDimension 2` on the structure morphism; the dimension two
is carried by the relative dimension. The structure morphism of the fibre product is
`pullback.fst f g ≫ f`, which equals `pullback.snd f g ≫ g` by `pullback.condition`.
The statement is given for two possibly different curves; the self-product is `g = f`.

Each property is stable under base change and composition: projectivity by [Stacks, Tag 01WF]
and [Stacks, Tag 01WE], geometric integrality of a product over a field by
`AlgebraicGeometry.Cube.geometricallyIntegral_fst_comp`, and smoothness of relative dimension
`1 + 1 = 2` by `AlgebraicGeometry.smoothOfRelativeDimension_comp`. Integrality of the product,
needed for it to be a variety, follows from geometric integrality over the one-point base
`Spec k`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- The fibre product over a field `k` of two smooth projective geometrically integral curves is
a smooth projective geometrically integral surface over `k`. -/
@[faltings "lem_nt_c_times_c_surface"]
theorem IsSmoothProjectiveCurve.surface_pullback (k : Type u) [Field k] {C D : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (g : D ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve k g] :
    IsProjectiveVariety k (pullback.fst f g ≫ f) ∧
      GeometricallyIntegral (pullback.fst f g ≫ f) ∧
      SmoothOfRelativeDimension 2 (pullback.fst f g ≫ f) := by
  have : GeometricallyIntegral (pullback.fst f g ≫ f) := Cube.geometricallyIntegral_fst_comp f g
  have : IsIntegral (pullback f g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst f g ≫ f)
  have hproj : IsProjectiveMorphism (pullback.fst f g ≫ f) := by
    rw [pullback.condition]
    exact (IsProjectiveVariety.isProjective (f := f)).baseChange g |>.comp
      (IsProjectiveVariety.isProjective (f := g))
  have : SmoothOfRelativeDimension 1 (pullback.fst f g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f g).flip inferInstance
  exact ⟨(isProjectiveVariety_iff k _).mpr ⟨IsVariety.mk, hproj⟩, ‹_›,
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ f⟩

end Faltings
