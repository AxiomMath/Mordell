module

public import Mordell.AlgebraicGeometry.GeometricPoint.Galois
public import Mordell.AlgebraicGeometry.GeometricPoint.FieldOfDefinition
public import Mordell.MordellWeil.Kummer.Pairing
public import Mordell.AlgebraicGeometry.GroupScheme.Points

/-!
# The field of definition of a Kummer point is finite Galois

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k` and
`m ≥ 1`, and assume that the `m`-torsion `A(k̄)[m]` is contained in `A(k)`. If `Q ∈ A(k̄)` has
`m Q ∈ A(k)`, then the field of definition `k(Q) ⊆ k̄` is a finite Galois extension of `k`: it is
finite since `A` is of finite type over `k`, and for `σ ∈ Gal(k̄/k)` the point `σ Q - Q` is
`m`-torsion, hence `k`-rational, so `σ Q ∈ A(k(Q))` and `σ(k(Q)) = k(σ Q) ⊆ k(Q)`.

## Main results

* `Faltings.finiteDimensional_and_isGalois_fieldOfDefinition_of_pow_mem`: `k(Q)/k` is finite
  and Galois.

## Implementation notes

An abelian variety over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral. The points `A(k̄)` are
the morphisms `Over.mk (Spec (k → k̄)) ⟶ A`, a group under `CategoryTheory.Hom.group`, written
multiplicatively, so `m Q` is `Q ^ m`. The `k`-points `A(k)` are the morphisms
`Over.mk (𝟙 (Spec k)) ⟶ A`, and `A(k) → A(k̄)` is precomposition with the morphism
`Spec k̄ ⟶ Spec k` over `Spec k`. The field `k(Q)` is `Faltings.fieldOfDefinition Q.left`,
where `A.left` is a `k`-scheme through `A.hom`. This is the setup of `Faltings.kummerField`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3, Proposition 3.1
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

section

variable {k kbar : Type u} [Field k] [NumberField k] [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]

/-- A point of `A(k̄)` lies in the subgroup `A(L)` exactly when its field of definition is
contained in `L`. -/
private lemma mem_iff_fieldOfDefinition_le {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    [LocallyOfFiniteType A.hom] {L : IntermediateField k kbar}
    {H : Subgroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)}
    (hH : (H : Set _) = Set.range
      fun P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))
          (Spec.map (CommRingCat.ofHom (algebraMap L kbar)))
          (by
            simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              ← IsScalarTower.algebraMap_eq]) ≫ P)
    (R : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    R ∈ H ↔ fieldOfDefinition (k := k) R.left (Over.w R) ≤ L := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  rw [← SetLike.mem_coe, hH]
  refine Iff.trans ?_
    (exists_spec_map_comp_eq_iff_fieldOfDefinition_le (k := k) R.left (Over.w R) L)
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.left, Over.w P, rfl⟩
  · rintro ⟨P, h1, h2⟩
    exact ⟨Over.homMk P h1, Over.OverMorphism.ext h2⟩

omit [NumberField k] [IsAlgClosure k kbar] in
/-- The image of a `k`-point lies in the subgroup `A(L)` of `A(k̄)`. -/
private lemma homMk_comp_mem {A : Over (Spec (CommRingCat.of k))} [GrpObj A]
    {L : IntermediateField k kbar}
    {H : Subgroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)}
    (hH : (H : Set _) = Set.range
      fun P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))
          (Spec.map (CommRingCat.ofHom (algebraMap L kbar)))
          (by
            simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              ← IsScalarTower.algebraMap_eq]) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) :
    Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P ∈ H := by
  rw [← SetLike.mem_coe, hH]
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ P.left)
    (by rw [Category.assoc, Over.w P]; simp), ?_⟩
  ext1
  simp only [Over.comp_left, Over.homMk_left, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- If `A(k̄)[m] ⊆ A(k)` and `m Q ∈ A(k)`, then every Galois conjugate `σ Q` is defined over
`k(Q)`: `σ Q - Q` is `m`-torsion, hence `k`-rational. -/
private lemma fieldOfDefinition_galoisActionPoint_le (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A)
    (hP : Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m)
    (σ : kbar ≃ₐ[k] kbar) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    fieldOfDefinition (k := k) (galoisActionPoint k kbar A σ Q).left
        (Over.w (galoisActionPoint k kbar A σ Q)) ≤
      fieldOfDefinition (k := k) Q.left (Over.w Q) := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  obtain ⟨H, hH⟩ := exists_subgroup_coe_eq_range_points
    (fieldOfDefinition (k := k) Q.left (Over.w Q)) A
  obtain ⟨P', hP'⟩ := htors _ (kummerPairing_pow_eq_one k kbar A m hm htors P σ)
  have := H.mul_mem (hP' ▸ homMk_comp_mem hH P') ((mem_iff_fieldOfDefinition_le hH Q).2 le_rfl)
  rw [kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hP.symm, inv_mul_cancel_right] at this
  exact (mem_iff_fieldOfDefinition_le hH _).1 this

end

/-- Let `A` be an abelian variety over a number field `k` with `A(k̄)[m] ⊆ A(k)`. If
`Q ∈ A(k̄)` satisfies `m Q ∈ A(k)`, then its field of definition `k(Q)` is a finite Galois
extension of `k`. -/
@[faltings "lem_mw_kummer_point_field_galois"]
theorem finiteDimensional_and_isGalois_fieldOfDefinition_of_pow_mem (k : Type u) [Field k]
    [NumberField k] (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (hQ : ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    FiniteDimensional k (fieldOfDefinition (k := k) Q.left (Over.w Q)) ∧
      IsGalois k (fieldOfDefinition (k := k) Q.left (Over.w Q)) :=
      by
  obtain ⟨P, hP⟩ := hQ
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  have := finiteDimensional_fieldOfDefinition (k := k) Q.left (Over.w Q)
  have : Normal k (fieldOfDefinition (k := k) Q.left (Over.w Q)) :=
    (IntermediateField.normal_iff_forall_map_le').2 fun σ =>
      (fieldOfDefinition_galoisActionPoint A σ Q).symm.trans_le
        (fieldOfDefinition_galoisActionPoint_le A m hm htors Q P hP σ)
  exact ⟨‹_›, { }⟩

end Faltings
