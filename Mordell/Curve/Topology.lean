module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Curves are Noetherian spaces

Let `K` be a field and `C` a curve over `K` (`AlgebraicGeometry.IsCurve`): an integral scheme of
dimension one with a separated morphism of finite type `C ⟶ Spec K`. Since `C` is of finite type
over the Noetherian scheme `Spec K`, it is a Noetherian scheme, so its underlying topological space
is Noetherian.

## Main results

* `Faltings.FunctionField.noetherianSpace_of_isCurve`: the underlying space of a curve over a
  field is a Noetherian topological space.

## References

* [Stacks, Tag 01T6]
-/

public section

open AlgebraicGeometry

universe u

namespace Faltings.FunctionField

/-- The underlying topological space of a curve over a field `K` is Noetherian: `C` is locally
Noetherian, being locally of finite type over `Spec K`, and quasi-compact over the quasi-compact
`Spec K`, hence a Noetherian scheme. -/
@[faltings "lem_ff_curve_noetherian"]
theorem noetherianSpace_of_isCurve (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] : TopologicalSpace.NoetherianSpace C :=
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := ⟨⟩
  inferInstance

end Faltings.FunctionField

end


/-!
# Non-generic points of a curve are closed

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K`. The
underlying space of `C` is irreducible and sober, with generic point `genericPoint C`. Since `C`
has topological Krull dimension one, the closure of a point `x ≠ genericPoint C` is an irreducible
closed proper subset that contains no smaller one, so it is `{x}`, and `x` is a closed point.

## Main results

* `Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint`: on a curve over a field, every
  point other than the generic point is closed.

## References

* [Stacks, Tag 0A23]
-/

public section

universe u

namespace Faltings.FunctionField

open AlgebraicGeometry TopologicalSpace

/-- In an irreducible T₀ space of topological Krull dimension at most one, a point whose closure
is not the whole space is closed: its closure is an irreducible closed set which, not being the
top one, must be minimal, so every point of it is inseparable from the given point. -/
private lemma isClosed_singleton_of_topologicalKrullDim_le_one {X : Type*} [TopologicalSpace X]
    [T0Space X] [IrreducibleSpace X] (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : closure ({x} : Set X) ≠ Set.univ) : IsClosed ({x} : Set X) := by
  let pt : X → IrreducibleCloseds X := fun y =>
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  rcases Order.krullDim_le_one_iff.mp hX (pt x) with hmin | hmax
  · refine closure_subset_iff_isClosed.mp fun y hy => ?_
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    exact ((specializes_iff_closure_subset.mpr
      (hmin (b := pt y) (specializes_iff_closure_subset.mp hxy))).antisymm hxy).eq
  · exact absurd (Set.eq_univ_of_univ_subset
      (hmax (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩)
        (Set.subset_univ _))) hx

/-- On a curve `C` over a field `K`, every point other than the generic point is closed. -/
@[faltings "lem_ff_curve_points"]
theorem isClosed_singleton_of_ne_genericPoint (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] {x : C} (hx : x ≠ genericPoint C) :
    IsClosed ({x} : Set C) :=
  isClosed_singleton_of_topologicalKrullDim_le_one
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    fun h => hx (IsGenericPoint.eq (h.trans Set.top_eq_univ.symm) (genericPoint_spec _))

end Faltings.FunctionField

end


/-!
# Proper closed subsets of a curve are finite

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K`. The
underlying space of `C` is Noetherian and of dimension one, with a unique generic point whose
closure is all of `C`. Hence a closed subset `Z ≠ C` has finitely many irreducible components,
none of them `C`, and each of them is a closed point. So `Z` is a finite set of closed points.

## Main results

* `Faltings.FunctionField.finite_and_subset_closedPoints_of_isClosed_of_ne_univ`: a closed subset
  `Z ≠ univ` of a curve is finite and consists of closed points.

## Implementation notes

A curve is `AlgebraicGeometry.IsCurve K f`. "A set of closed points" is `Z ⊆ closedPoints C`,
with `closedPoints C = {x | IsClosed {x}}`.

## References

* [Stacks, Tag 0A21], [Stacks, Tag 0A23]
-/

public section

universe u

namespace Faltings.FunctionField

open AlgebraicGeometry TopologicalSpace

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite:
it is a finite union of irreducible closed sets, each the closure of a point, hence a point. -/
private lemma finite_of_isClosed_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ x ∈ Z, IsClosed ({x} : Set X)) : Z.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  rw [← hy.def, (h y (Set.mem_sUnion_of_mem hy.mem ht)).closure_eq]
  exact Set.finite_singleton y

/-- A proper closed subset of an irreducible scheme misses the generic point. -/
private lemma genericPoint_notMem_of_isClosed_of_ne_univ {C : Scheme.{u}} [IrreducibleSpace C]
    {Z : Set C} (hZ : IsClosed Z) (hZ' : Z ≠ Set.univ) : genericPoint C ∉ Z := fun h =>
  hZ' <| Set.eq_univ_of_univ_subset <| (genericPoint_spec C).def ▸
    hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 h)

/-- A closed subset `Z ≠ univ` of a curve `C` over a field `K` is a finite set of closed points. -/
@[faltings "lem_ff_curve_closed_finite"]
theorem finite_and_subset_closedPoints_of_isClosed_of_ne_univ (K : Type u) [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] {Z : Set C} (hZ : IsClosed Z)
    (hZ' : Z ≠ Set.univ) :
    Z.Finite ∧ Z ⊆ closedPoints C := by
  have := noetherianSpace_of_isCurve K f
  have hcl (x) (hx : x ∈ Z) : IsClosed ({x} : Set C) :=
    isClosed_singleton_of_ne_genericPoint K f fun h =>
      genericPoint_notMem_of_isClosed_of_ne_univ hZ hZ' (h ▸ hx)
  exact ⟨finite_of_isClosed_of_forall_isClosed_singleton hZ hcl, hcl⟩

end Faltings.FunctionField

end
