module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.GeometricPoint.FieldOfDefinition

/-!
# The Galois action on geometric points

Let `k` be a number field, `k̄` an algebraic closure of `k` and `G_k = Gal(k̄/k)`. For a scheme `X`
locally of finite type over `k`, a `k̄`-point of `X` is a morphism `Q : Spec k̄ ⟶ X` over `Spec k`.
An automorphism `σ ∈ G_k` acts on such points by precomposition with `Spec σ`:
`σ Q = Q ∘ Spec(σ)`, which is again a morphism over `Spec k` because `σ` fixes `k`.

## Main definitions

* `Faltings.galoisActionPoint`: the point `σ Q = Q ∘ Spec(σ)` of `X(k̄)`.

## Main results

* `Faltings.galoisActionPoint_mul`, `Faltings.galoisActionPoint_one`: this is an action of
  `Gal(k̄/k)`, that is `σ (τ Q) = (σ τ) Q` and `1 Q = Q`.
* `Faltings.galoisActionPoint_homMk_comp`: `σ` fixes the image in `X(k̄)` of a point of `X(k)`.

## Implementation notes

A scheme over `k` is an object of `Over (Spec k)`, and `X(k̄)` is the type of morphisms in
`Over (Spec k)` from `Spec k̄` (with its structure morphism `Spec` of the algebra map) to `X`.
In the composition order of Mathlib, `Q ∘ Spec(σ)` is written `Spec.map σ ≫ Q`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Faltings

/-- The Galois action on `k̄`-points: for `σ ∈ Gal(k̄/k)` and `Q ∈ X(k̄)`, the point
`σ Q = Q ∘ Spec(σ) ∈ X(k̄)`. -/
@[faltings "def_mw_galois_action_points"]
noncomputable def galoisActionPoint (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (σ : kbar ≃ₐ[k] kbar)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X :=
  Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
    (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
    (Spec.map (CommRingCat.ofHom (σ : kbar →+* kbar))) (by
      simp only [Over.mk_left, Over.mk_hom, ← Spec.map_comp]
      congr 1
      ext x
      simp) ≫ Q

section

variable {k : Type u} [Field k] [NumberField k]
    {kbar : Type u} [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]

/-- The Galois action on `k̄`-points is an action: `σ (τ Q) = (σ τ) Q`. -/
lemma galoisActionPoint_mul (σ τ : kbar ≃ₐ[k] kbar)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X) :
    galoisActionPoint k kbar X σ (galoisActionPoint k kbar X τ Q) =
      galoisActionPoint k kbar X (σ * τ) Q := by
  simp only [galoisActionPoint, ← Category.assoc]
  congr 1
  ext1
  simp only [Over.comp_left, Over.homMk_left, ← Spec.map_comp]
  rfl

/-- The identity of `Gal(k̄/k)` acts trivially on `k̄`-points. -/
lemma galoisActionPoint_one
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X) :
    galoisActionPoint k kbar X 1 Q = Q := by
  simp only [galoisActionPoint]
  convert Category.id_comp Q
  ext1
  exact Spec.map_id _

end

/-- Every `σ ∈ Gal(k̄/k)` fixes the image in `X(k̄)` of a point `R ∈ X(k)`, the image being
`R ∘ Spec(k̄ → k)`. -/
lemma galoisActionPoint_homMk_comp (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (σ : kbar ≃ₐ[k] kbar) (R : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    galoisActionPoint k kbar X σ
        (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ R) =
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ R := by
  ext1
  simp only [galoisActionPoint, Over.comp_left, Over.homMk_left, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext x
  simp

end Faltings

/-!
# The field of definition of a conjugate point

Let `k` be a number field, `k̄` an algebraic closure of `k`, and `X` a scheme locally of finite
type over `k`. For a `k̄`-point `Q` of `X` and `σ ∈ Gal(k̄/k)`, the conjugate point
`σ Q = Q ∘ Spec(σ)` has field of definition `k(σ Q) = σ(k(Q))`: if `x ∈ X` is the image of `Q`
and `ι : κ(x) → k̄` the induced embedding, then `σ Q` has the same image `x` and induces `σ ∘ ι`.

## Main results

* `Faltings.fieldOfDefinition_galoisActionPoint`: `k(σ Q) = σ(k(Q))`.

## Implementation notes

`Faltings.galoisActionPoint` is stated for `X` an object of `Over (Spec k)` and points the
morphisms in `Over (Spec k)`, while `Faltings.fieldOfDefinition` takes a scheme with an
`AlgebraicGeometry.Scheme.Over` instance and a morphism `Spec k̄ ⟶ X` with the equation
saying it lies over `k`. Here `X.left` is given the `Over` instance `X.hom`, and a point `Q`
contributes `Q.left` together with `Over.w Q`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Faltings

/-- The field of definition of a Galois conjugate point is the conjugate field:
`k(σ Q) = σ(k(Q))`. -/
@[faltings "lem_mw_field_of_definition_conjugate"]
theorem fieldOfDefinition_galoisActionPoint {k K : Type u} [Field k] [NumberField k] [Field K]
    [Algebra k K] [IsAlgClosure k K] (X : Over (Spec (CommRingCat.of k)))
    [hX : LocallyOfFiniteType X.hom] (σ : K ≃ₐ[k] K)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ X) :
    letI : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
    haveI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) := hX
    fieldOfDefinition (k := k) (galoisActionPoint k K X σ Q).left
        (Over.w (galoisActionPoint k K X σ Q)) =
      (fieldOfDefinition (k := k) Q.left (Over.w Q)).map (σ : K →ₐ[k] K) :=
  IntermediateField.toSubfield_injective <|
    (congrArg (fun p => p.2.hom.fieldRange)
      (specToEquivOfField_specMap_comp (CommRingCat.ofHom (σ : K →+* K)) Q.left)).trans
      (RingHom.map_fieldRange _ _).symm

end Faltings

/-!
# Galois automorphisms fixing a geometric point

Let `k` be a number field, `k̄` an algebraic closure and `X` a scheme locally of finite type
over `k`. An automorphism `σ ∈ Gal(k̄/k)` fixes a point `Q ∈ X(k̄)` (for the action
`σ Q = Q ∘ Spec σ`) if and only if `σ` restricts to the identity on the field of definition
`k(Q) ⊆ k̄` of `Q`.

## Main results

* `Faltings.galoisActionPoint_eq_self_iff`: `σ Q = Q ↔ ∀ x ∈ k(Q), σ x = x`.

## Implementation notes

The point `Q` is a morphism in `Over (Spec k)`; its underlying morphism of schemes
`Q.left : Spec k̄ ⟶ X.left` lies over `Spec k` by `Over.w Q`, and the field of definition is
`Faltings.fieldOfDefinition` of `Q.left`, with `X.left` a `k`-scheme through `X.hom`.

The statement holds for any field `K` and any ring endomorphism `τ` of `K`: a `K`-point
`Q : Spec K ⟶ X` satisfies `Spec τ ≫ Q = Q` if and only if `τ` fixes the image of the
residue-field embedding of `Q`. The theorem is this fact applied to `Q.left` and `σ`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Faltings

/-- A `K`-point `Q : Spec K ⟶ X`, with residue-field embedding `ι : κ(x) → K`, is fixed by
precomposition with `Spec τ` for an endomorphism `τ` of `K` if and only if `τ` is the identity
on the image of `ι`. -/
private lemma spec_map_comp_eq_self_iff {K : Type u} [Field K] {X : Scheme.{u}}
    (Q : Spec (.of K) ⟶ X) (τ : K →+* K) :
    Spec.map (CommRingCat.ofHom τ) ≫ Q = Q ↔
      ∀ y ∈ (Scheme.SpecToEquivOfField K X Q).2.hom.fieldRange, τ y = y := by
  set e := Scheme.SpecToEquivOfField K X
  obtain ⟨⟨x, ι⟩, rfl⟩ := e.symm.surjective Q
  rw [← e.injective.eq_iff, specToEquivOfField_specMap_comp, e.apply_symm_apply]
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, RingHom.mem_fieldRange,
    forall_exists_index, forall_apply_eq_imp_iff, CommRingCat.hom_ext_iff, RingHom.ext_iff]
  rfl

/-- An automorphism `σ ∈ Gal(k̄/k)` fixes a `k̄`-point `Q` of a `k`-scheme `X` locally of finite
type if and only if `σ` is the identity on the field of definition `k(Q)` of `Q`. -/
@[faltings "lem_mw_galois_fixes_point_iff"]
theorem galoisActionPoint_eq_self_iff {k : Type u} [Field k] [NumberField k]
    {kbar : Type u} [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (σ : kbar ≃ₐ[k] kbar)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X) :
    letI : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
    haveI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType X.hom)
    galoisActionPoint k kbar X σ Q = Q ↔
      ∀ x ∈ fieldOfDefinition (k := k) (K := kbar) Q.left (Over.w Q), σ x = x :=
  Over.OverMorphism.ext_iff.trans (spec_map_comp_eq_self_iff Q.left (σ : kbar →+* kbar))

end Faltings

/-!
# Galois descent for points

Let `X` be a scheme locally of finite type over a number field `k`, let `k̄` be an algebraic
closure of `k` and let `k ⊆ K ⊆ k̄` be an intermediate field. A `k̄`-point `Q` of `X` is fixed by
every `σ ∈ Gal(k̄/K)` under the action `Faltings.galoisActionPoint` exactly when it comes from a
`K`-point, i.e. lies in the image of the map `X(K) → X(k̄)` given by precomposition with
`Spec (K ⊆ k̄)`.

## Main results

* `Faltings.setOf_forall_galoisActionPoint_eq_eq_range`: the `Gal(k̄/K)`-fixed points of `X(k̄)`
  are the image of `X(K)`.

## Implementation notes

Points are morphisms in `Over (Spec k)`, as for `Faltings.galoisActionPoint`. An element
`σ : k̄ ≃ₐ[K] k̄` of `Gal(k̄/K)` acts through its restriction of scalars `σ.restrictScalars k`
to an element of `Gal(k̄/k)`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Faltings

/-- Galois descent for subfields of an algebraic closure in characteristic zero: an
intermediate field `L` of `k̄ / k` is fixed pointwise by `Gal(k̄/K)` if and only if `L ≤ K`. -/
private lemma forall_algEquiv_fixes_iff_le {k kbar : Type u} [Field k] [CharZero k] [Field kbar]
    [Algebra k kbar] [IsAlgClosure k kbar] (K L : IntermediateField k kbar) :
    (∀ σ : kbar ≃ₐ[K] kbar, ∀ x ∈ L, σ x = x) ↔ L ≤ K := by
  refine ⟨fun h x hx => ?_, fun h σ x hx => σ.commutes ⟨x, h hx⟩⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Normal K kbar := haveI := IsAlgClosure.normal k kbar; IntermediateField.normal k kbar K
  haveI : IsGalois K kbar := ⟨⟩
  obtain ⟨y, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) x).2 (h · x hx)
  exact y.2

/-- Galois descent for points: for an intermediate field `k ⊆ K ⊆ k̄`, the `k̄`-points of `X`
fixed by every `σ ∈ Gal(k̄/K)` are exactly the image of `X(K) → X(k̄)`. -/
@[faltings "lem_mw_galois_invariant_points"]
theorem setOf_forall_galoisActionPoint_eq_eq_range (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (K : IntermediateField k kbar) :
    {Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X |
        ∀ σ : kbar ≃ₐ[K] kbar, galoisActionPoint k kbar X (σ.restrictScalars k) Q = Q} =
      Set.range fun P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ X =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))
          (by
            change Spec.map _ ≫ Spec.map _ = Spec.map _
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) ≫ P := by
  letI : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
  haveI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  ext Q
  simp_rw [Set.mem_setOf_eq, galoisActionPoint_eq_self_iff, AlgEquiv.restrictScalars_apply]
  rw [forall_algEquiv_fixes_iff_le,
    ← exists_spec_map_comp_eq_iff_fieldOfDefinition_le (k := k) Q.left (Over.w Q), Set.mem_range]
  constructor
  · rintro ⟨P, hP, hPQ⟩
    exact ⟨Over.homMk P hP, Over.OverMorphism.ext hPQ⟩
  · rintro ⟨P, rfl⟩
    exact ⟨P.left, Over.w P, rfl⟩

end Faltings

/-!
# The Galois action on the points of a group scheme is by group automorphisms

Let `k` be a number field, `k̄` an algebraic closure of `k` and `A` a group scheme over `k`. The
points `A(k̄) = Hom_k(Spec k̄, A)` form a group under the group law of `A`, acting by
postcomposition, while `σ ∈ Gal(k̄/k)` acts by precomposition with `Spec σ`
(`Faltings.galoisActionPoint`). The two commute, so `P ↦ σ P` is a group homomorphism, and it is
bijective with inverse `P ↦ σ⁻¹ P`.

## Main results

* `Faltings.exists_mulEquiv_coe_eq_galoisActionPoint`: for `σ ∈ Gal(k̄/k)`, the map
  `galoisActionPoint k k̄ A σ` is the underlying map of a group automorphism of `A(k̄)`.

## Implementation notes

A group scheme over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure, and the group structure on `A(k̄)` is `CategoryTheory.Hom.group`, written
multiplicatively.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- For a group scheme `A` over a number field `k` and `σ ∈ Gal(k̄/k)`, the Galois action
`P ↦ σ P` on `A(k̄)` is a group automorphism of `A(k̄)`: it is multiplicative because
precomposition commutes with the pointwise group law, and its inverse is the action of `σ⁻¹`. -/
@[faltings "lem_mw_galois_action_additive"]
theorem exists_mulEquiv_coe_eq_galoisActionPoint (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [LocallyOfFiniteType A.hom]
    (σ : kbar ≃ₐ[k] kbar) :
    ∃ e : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) ≃*
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A),
      ⇑e = galoisActionPoint k kbar A σ :=
  ⟨{ toFun := galoisActionPoint k kbar A σ
     invFun := galoisActionPoint k kbar A σ⁻¹
     left_inv Q := by simp [galoisActionPoint_mul, galoisActionPoint_one]
     right_inv Q := by simp [galoisActionPoint_mul, galoisActionPoint_one]
     map_mul' _ _ := MonObj.comp_mul _ _ _ }, rfl⟩

end Faltings
