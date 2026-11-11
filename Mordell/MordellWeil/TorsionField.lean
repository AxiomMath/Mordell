module

public import Mordell.AlgebraicGeometry.GeometricPoint.FieldOfDefinition
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import Mordell.AlgebraicGeometry.GeometricPoint.Galois
public import Mordell.MordellWeil.Kummer.PointDegree
public import Mordell.MordellWeil.TorsionLifting

/-!
# The field of `m`-torsion of an abelian variety

Let `k` be a number field, `k̄` an algebraic closure of `k` and `A` an abelian variety over `k`,
that is a proper, geometrically integral group scheme over `k`. The points
`A(k̄) = Hom_k(Spec k̄, A)` form a group under the group law of `A`. For `m ≥ 1`, the field of
`m`-torsion `k(A[m]) ⊆ k̄` is the compositum of the fields of definition `k(T)` of the points
`T ∈ A(k̄)` with `m T = 0`.

## Main definitions

* `Faltings.torsionField`: the field `k(A[m])`, as an `IntermediateField k k̄`.

## Implementation notes

An abelian variety over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral. The group structure
on `A(k̄)` is `CategoryTheory.Hom.group`, written multiplicatively, so `A(k̄)[m]` is the set of
`T` with `T ^ m = 1`. The compositum is the supremum in `IntermediateField k k̄` of the fields
`Faltings.fieldOfDefinition T`, where `A.left` is regarded as a `k`-scheme through `A.hom`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- The field of `m`-torsion `k(A[m]) ⊆ k̄` of an abelian variety `A` over a number field `k`:
the compositum of the fields of definition `k(T)` of the points `T ∈ A(k̄)` with `m T = 0`. -/
@[faltings "def_mw_torsion_field"]
noncomputable def torsionField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (_hm : 1 ≤ m) : IntermediateField k kbar :=
  letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  ⨆ (T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) (_ : T ^ m = 1),
    fieldOfDefinition (k := k) T.left (Over.w T)

end Faltings


/-!
# The field of `m`-torsion is finite Galois

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k` and
`m ≥ 1`. The field of `m`-torsion `k(A[m]) ⊆ k̄`, the compositum of the fields of definition of
the points of `A(k̄)[m]`, is a finite Galois extension of `k`: it is finite because `A(k̄)[m]` is
finite and each field of definition is finite over `k`, and it is normal because `Gal(k̄/k)`
permutes `A(k̄)[m]`; it is separable since `k` has characteristic zero.

## Main results

* `Faltings.finiteDimensional_and_isGalois_torsionField`: `k(A[m])/k` is finite and Galois.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory Limits
open scoped MonObj

namespace Faltings

section TorsionField

variable (k : Type u) [Field k] [NumberField k]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
  [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)

/-- `k(A[m])` is finite over `k`: a compositum of finitely many finite extensions. -/
private lemma finiteDimensional_torsionField :
    FiniteDimensional k (torsionField k kbar A m hm) := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  have : Finite {T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A //
      T ^ m = 1} := (finite_setOf_pow_eq_one (L := kbar) A hm).to_subtype
  have : ∀ T : {T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A //
      T ^ m = 1}, FiniteDimensional k (fieldOfDefinition (k := k) T.1.left (Over.w T.1)) :=
    fun T => finiteDimensional_fieldOfDefinition _ _
  rw [torsionField, iSup_subtype']
  exact IntermediateField.finiteDimensional_iSup_of_finite

/-- `k(A[m])` is normal over `k`: `Gal(k̄/k)` permutes `A(k̄)[m]` and conjugates fields of
definition. -/
private lemma normal_torsionField : Normal k (torsionField k kbar A m hm) := by
  have : Normal k kbar := IsAlgClosure.normal k kbar
  refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ => ?_
  obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
  rw [IntermediateField.map_le_iff_le_comap, torsionField]
  refine iSup₂_le fun T hT => ?_
  rw [← IntermediateField.map_le_iff_le_comap,
    ← fieldOfDefinition_galoisActionPoint (k := k) (K := kbar) A σ T]
  refine le_iSup₂_of_le (f := fun T _ => _) (galoisActionPoint k kbar A σ T) ?_ le_rfl
  rw [← he, ← map_pow, hT, map_one]

end TorsionField

/-- The field of `m`-torsion `k(A[m])` of an abelian variety `A` over a number field `k` is a
finite Galois extension of `k`. -/
@[faltings "lem_mw_torsion_field"]
theorem finiteDimensional_and_isGalois_torsionField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m) :
    FiniteDimensional k (torsionField k kbar A m hm) ∧
      IsGalois k (torsionField k kbar A m hm) :=
  have := normal_torsionField k kbar A m hm
  ⟨finiteDimensional_torsionField k kbar A m hm, ⟨⟩⟩

end Faltings


/-!
# The `m`-torsion is rational over the field of `m`-torsion

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k`,
`m ≥ 1` and `L = k(A[m]) ⊆ k̄` the field of `m`-torsion. Every point `T ∈ A(k̄)` with `m T = 0`
comes from an `L`-point: it is the image of some `P ∈ A(L)` under the map `A(L) → A(k̄)` induced
by the inclusion `L ⊆ k̄`. Indeed the field of definition of `T` is contained in `L` by
definition of `L`.

## Main results

* `Faltings.mem_range_of_pow_eq_one_torsionField`: every `T : A(k̄)` with `T ^ m = 1` lies in
  the image of `A(k(A[m])) → A(k̄)`.

## Implementation notes

Points are morphisms in `Over (Spec k)`; the group law on `A(k̄)` is `CategoryTheory.Hom.group`,
written multiplicatively, so `A(k̄)[m]` is `{T | T ^ m = 1}`. The map `A(L) → A(k̄)` is
precomposition with `Spec (L ⊆ k̄)`, regarded as a morphism over `Spec k`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- Every `m`-torsion point `T ∈ A(k̄)` of an abelian variety `A` over a number field `k` comes
from a point of `A` over the field of `m`-torsion `L = k(A[m])`: it lies in the image of
`A(L) → A(k̄)`. -/
@[faltings "lem_mw_torsion_field_contains_torsion"]
theorem mem_range_of_pow_eq_one_torsionField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) (hT : T ^ m = 1) :
    T ∈ Set.range fun P : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap k (torsionField k kbar A m hm)))) ⟶ A =>
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap k (torsionField k kbar A m hm)))))
        (Spec.map (CommRingCat.ofHom (algebraMap (torsionField k kbar A m hm) kbar)))
        (by
          change Spec.map _ ≫ Spec.map _ = Spec.map _
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) ≫ P := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  obtain ⟨P, hP, hPT⟩ := (exists_spec_map_comp_eq_iff_fieldOfDefinition_le (k := k) T.left
    (Over.w T) _).2 (le_iSup₂_of_le (f := fun (T : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k kbar))) ⟶ A) (_ : T ^ m = 1) => fieldOfDefinition (k := k) T.left (Over.w T))
      T hT le_rfl)
  exact ⟨Over.homMk P hP, Over.OverMorphism.ext hPT⟩

end Faltings
