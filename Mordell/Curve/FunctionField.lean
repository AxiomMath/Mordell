module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne

/-!
# The function field of a curve has transcendence degree one

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K`. The
function field `C.functionField`, the stalk of `C` at its generic point, is a `K`-algebra through
`K ≅ Γ(Spec K, ⊤) ⟶ Γ(C, ⊤) ⟶ C.functionField`. Its transcendence degree over `K` is one.

## Main results

* `Faltings.trdeg_functionField_eq_one`: `Algebra.trdeg K C.functionField = 1` for a curve `C`
  over `K`.

## Implementation notes

A curve is `AlgebraicGeometry.IsCurve K f`: an integral scheme, separated and of finite type over
`Spec K`, of topological Krull dimension one. The `K`-algebra structure on the function field
is the one induced by `f` on global sections followed by the germ at the generic point.

The statement is `AlgebraicGeometry.trdeg_functionField_eq_one`, whose `K`-algebra structure
`AlgebraicGeometry.functionFieldAlgebra` is the one written out here.

## References

* [Stacks, Tag 0A21]
-/

public section

namespace Faltings

open AlgebraicGeometry CategoryTheory

universe u

/-- The function field of a curve `C` over a field `K` has transcendence degree `1` over `K`,
for the `K`-algebra structure induced by the structure morphism `f : C ⟶ Spec K`. -/
@[faltings "lem_ff_curve_function_field_trdeg"]
theorem trdeg_functionField_eq_one (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
    Algebra.trdeg K C.functionField = 1 :=
  AlgebraicGeometry.trdeg_functionField_eq_one K f

end Faltings

end


/-!
# Rational functions on a curve are regular on a nonempty open

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K`. The
function field `C.functionField` is the stalk of `C` at its generic point `η`, that is the colimit
of `Γ(C, U)` over the open sets `U ∋ η`. Every nonempty open set contains `η`, so every rational
function `g ∈ K(C)` is the image of a section `s ∈ Γ(C, U)` under the germ map
`C.germToFunctionField U` for some nonempty open `U ⊆ C`.

## Main results

* `Faltings.FunctionField.exists_germToFunctionField_eq`: every element of the function field of a
  curve is the germ of a section over some nonempty open set.

## Implementation notes

A curve is `AlgebraicGeometry.IsCurve K f`. "The germ of a section in `Γ(U, 𝒪_C)`" is the image
under `AlgebraicGeometry.Scheme.germToFunctionField U`, the germ map at the generic point.

## References

* [Stacks, Tag 0A21]
-/

public section

universe u

open AlgebraicGeometry

namespace Faltings.FunctionField

/-- Every rational function `g` on a curve `C` over a field `K` is the germ of a section of `𝒪_C`
over some nonempty open subset `U ⊆ C`. -/
@[faltings "lem_ff_curve_rational_function_regular"]
theorem exists_germToFunctionField_eq (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] (g : C.functionField) :
    ∃ (U : C.Opens) (hU : Nonempty U) (s : Γ(C, U)),
      C.germToFunctionField U (h := hU) s = g := by
  obtain ⟨U, hη, s, hs⟩ := C.presheaf.exists_germ_eq (x := genericPoint C) g
  exact ⟨U, ⟨⟨_, hη⟩⟩, s, hs⟩

end Faltings.FunctionField

end
