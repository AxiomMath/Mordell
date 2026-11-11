module

public import Mordell.AlgebraicGeometry.GeometricPoint.FieldOfDefinition
public import Mordell.AlgebraicGeometry.GeometricPoint.Galois

/-!
# The Kummer field of an abelian variety

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k` and
`m ≥ 1`, and assume that the `m`-torsion `A(k̄)[m]` is contained in `A(k)`, that is, every
`T ∈ A(k̄)` with `m T = 0` comes from a `k`-rational point. The Kummer field
`k(m⁻¹ A(k)) ⊆ k̄` is the compositum of the fields of definition `k(Q)` of the points
`Q ∈ A(k̄)` with `m Q ∈ A(k)`.

## Main definitions

* `Faltings.kummerField`: the field `k(m⁻¹ A(k))`, as an `IntermediateField k k̄`.

## Implementation notes

An abelian variety over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral. The points
`A(k̄)` are the morphisms `Over.mk (Spec (k → k̄)) ⟶ A`, a group under `CategoryTheory.Hom.group`,
written multiplicatively, so `m Q` is `Q ^ m` and `0` is `1`. The `k`-points `A(k)` are the
morphisms `Over.mk (𝟙 (Spec k)) ⟶ A`, and `A(k) → A(k̄)` is precomposition with the morphism
`Spec k̄ ⟶ Spec k` over `Spec k`. The compositum is the supremum in `IntermediateField k k̄` of
the fields `Faltings.fieldOfDefinition Q`, where `A.left` is a `k`-scheme through `A.hom`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3, Definition 3.2
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- The Kummer field `k(m⁻¹ A(k)) ⊆ k̄` of an abelian variety `A` over a number field `k`, for
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`: the compositum of the fields of definition `k(Q)` of the points
`Q ∈ A(k̄)` with `m Q ∈ A(k)`. -/
@[faltings "def_mw_kummer_field"]
noncomputable def kummerField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (_hm : 1 ≤ m)
    (_htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T) :
    IntermediateField k kbar :=
  letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  ⨆ (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (_ : ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m),
    fieldOfDefinition (k := k) Q.left (Over.w Q)

end Faltings


/-!
# The Kummer field is Galois

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k` and
`m ≥ 1`, and assume that the `m`-torsion `A(k̄)[m]` is contained in `A(k)`. Then the Kummer field
`M = k(m⁻¹ A(k)) ⊆ k̄` is a Galois extension of `k`, possibly of infinite degree. For
`σ ∈ Gal(k̄/k)` and `Q ∈ A(k̄)` with `m Q ∈ A(k)`, one has `m (σ Q) = σ (m Q) = m Q ∈ A(k)` and
`σ (k(Q)) = k(σ Q)`, so `σ` permutes the fields generating `M` and `σ M = M`; as `k` has
characteristic zero, `M / k` is normal and separable.

## Main results

* `Faltings.isGalois_kummerField`: `k(m⁻¹ A(k)) / k` is Galois.

## Implementation notes

`IsGalois` in Mathlib asks for separability and normality only, with no finiteness, so it covers
the possibly infinite extension `k(m⁻¹ A(k)) / k`. The setup (abelian varieties, points, the
torsion hypothesis) is that of `Faltings.kummerField`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- Let `A` be an abelian variety over a number field `k` and `m ≥ 1` with `A(k̄)[m] ⊆ A(k)`.
Then the Kummer field `k(m⁻¹ A(k))`, `Faltings.kummerField`, is a (possibly infinite) Galois
extension of `k`. -/
@[faltings "lem_mw_kummer_field_galois"]
theorem isGalois_kummerField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T) :
    IsGalois k (kummerField k kbar A m hm htors) := by
  have : Normal k kbar := IsAlgClosure.normal k kbar
  have : Normal k (kummerField k kbar A m hm htors) := by
    refine (IntermediateField.normal_iff_forall_map_le').2 fun σ => ?_
    obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
    refine IntermediateField.map_le_iff_le_comap.2 <| iSup₂_le fun Q ⟨P, hP⟩ => ?_
    rw [← IntermediateField.map_le_iff_le_comap,
      ← fieldOfDefinition_galoisActionPoint (k := k) (K := kbar) A σ Q]
    refine le_iSup₂_of_le (galoisActionPoint k kbar A σ Q) ⟨P, ?_⟩ le_rfl
    rw [← he, ← map_pow, he, ← hP, galoisActionPoint_homMk_comp]
  exact ⟨⟩

end Faltings
