module

public import Mathlib
public import Mordell.Attr
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Points of a group scheme over an intermediate field form a subgroup

Let `k` be a number field, `k̄` an algebraic closure of `k` and `k ⊆ K ⊆ k̄` an intermediate
field. For a group scheme `A` over `k` (a group object in schemes over `Spec k`), the sets of
points `A(K) = Hom_k(Spec K, A)` and `A(k̄) = Hom_k(Spec k̄, A)` are groups under the group law
of `A`, and composition with `Spec k̄ → Spec K` maps `A(K)` into `A(k̄)`. The image of this map
is a subgroup of `A(k̄)`.

## Main results

* `Faltings.exists_subgroup_coe_eq_range_points`: the image of `A(K) → A(k̄)` is the carrier of
  a subgroup of `A(k̄)`.

## Implementation notes

A scheme over `k` is an object of `Over (Spec k)`, a group scheme over `k` is such an object
with a `CategoryTheory.GrpObj` structure, and the group structure on points is
`CategoryTheory.Hom.group`. The point `Spec k̄ → Spec K` over `Spec k` is `Spec` of the inclusion
`K → k̄`, which lies over `Spec k` by `IsScalarTower`.

## References

* [Stacks, Tag 01J6], [Stacks, Tag 03RO]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- In a cartesian monoidal category, for a group object `G` and a morphism `f : X ⟶ Y`, the
image of precomposition `(Y ⟶ G) → (X ⟶ G)` with `f` is a subgroup of `X ⟶ G`: it is the range
of the monoid hom `P ↦ f ≫ P`. -/
private theorem exists_subgroup_coe_eq_range_comp {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {X Y G : C} [GrpObj G] (f : X ⟶ Y) :
    ∃ H : Subgroup (X ⟶ G), (H : Set _) = Set.range fun P : Y ⟶ G => f ≫ P :=
  ⟨(MonoidHom.mk' (fun P : Y ⟶ G => f ≫ P) fun P Q => MonObj.comp_mul f P Q).range, by
    ext; simp⟩

/-- For a group scheme `A` over a number field `k`, an algebraic closure `k̄` of `k` and an
intermediate field `k ⊆ K ⊆ k̄`, the image of the map `A(K) → A(k̄)` given by composition with
`Spec k̄ → Spec K` is a subgroup of `A(k̄)`. -/
@[faltings "lem_mw_points_subgroup"]
theorem exists_subgroup_coe_eq_range_points
    {k kbar : Type u} [Field k] [NumberField k] [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (K : IntermediateField k kbar)
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] :
    ∃ H : Subgroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A),
      (H : Set _) = Set.range
        fun P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A =>
          Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
            (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))
            (by
              simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]) ≫ P :=
  exists_subgroup_coe_eq_range_comp _

end Faltings

/-!
# Points of a base change

Let `A` be a group scheme over a field `F`, viewed as a group object in `Over (Spec F)`, let `K/F`
be a field extension and `K'/K` a further extension. The base change `A_K = A ×_F Spec K` is the
image of `A` under `Over.pullback (Spec F ← Spec K)`, again a group object, and its `K'`-points are
the morphisms `Spec K' ⟶ A_K` over `Spec K`. By the universal property of the fibre product,
postcomposition with the first projection `A_K ⟶ A` identifies these with the morphisms
`Spec K' ⟶ A` over `Spec F`; this identification is a group isomorphism `A_K(K') ≃* A(K')` and
commutes with precomposition by `Spec σ` for every `σ ∈ Aut(K'/K)`.

## Main results

* `Faltings.exists_mulEquiv_points_pullback`: the group isomorphism `A_K(K') ≃* A(K')` given by
  postcomposition with `pullback.fst`, compatible with the action of `K' ≃ₐ[K] K'`.

## Implementation notes

A point `P ∈ A(K')` is a morphism `Over.mk (Spec.map (algebraMap F K')) ⟶ A` in `Over (Spec F)`,
with its group structure the one Mathlib puts on morphisms into a group object; the group
structure of the base change is the one Mathlib transports along the pullback,
`CategoryTheory.Over.grpObjMkPullbackSnd`. The action of
`σ ∈ Aut(K'/K)` by precomposition is stated on underlying morphisms of schemes: a point `Q` is the
transform of `P` by `σ` when `Q.left = Spec.map σ ≫ P.left`.

## References

* [Stacks, Tag 01J6], [Stacks, Tag 03RO]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj

namespace Faltings

section Points

variable {X Y T : Scheme.{u}}
  (g : Y ⟶ X) (A : Over X) [GrpObj A] {s : T ⟶ Y} {t : T ⟶ X}

/-- The group structure on the base change `A ×_X Y` transported along the pullback. -/
private noncomputable abbrev pullbackGrpObj : GrpObj ((Over.pullback g).obj A) :=
  @Over.grpObjMkPullbackSnd _ _ _ _ _ _ A.hom _ ‹GrpObj A›

attribute [local instance] pullbackGrpObj

/-- For `s ≫ g = t`, a `T`-point of `A` over `X` gives a `T`-point of `A ×_X Y` over `Y`,
by base change along `g` and the section `T ⟶ T ×_X Y` induced by `s`. -/
private noncomputable def pointsToPullback (h : s ≫ g = t) :
    (Over.mk t ⟶ A) →* (Over.mk s ⟶ (Over.pullback g).obj A) :=
  let j : Over.mk s ⟶ (Over.pullback g).obj (Over.mk t) :=
    Over.homMk (pullback.lift (𝟙 _) s (by simpa using h.symm)) (pullback.lift_snd _ _ _)
  { toFun := fun Q => j ≫ (Over.pullback g).map Q
    map_one' := by rw [Functor.map_one, MonObj.comp_one]; rfl
    map_mul' := fun Q₁ Q₂ => by rw [Functor.map_mul, MonObj.comp_mul]; rfl }

private lemma pointsToPullback_left_fst (h : s ≫ g = t) (Q : Over.mk t ⟶ A) :
    (pointsToPullback g A h Q).left ≫ pullback.fst A.hom g = Q.left := by
  simp [pointsToPullback]

/-- The universal property of the fibre product: `pointsToPullback` is bijective, with inverse
postcomposition by `pullback.fst`. -/
private lemma pointsToPullback_bijective (h : s ≫ g = t) :
    Function.Bijective (pointsToPullback g A h) := by
  refine ⟨fun Q₁ Q₂ hQ => ?_, fun P => ⟨Over.homMk (P.left ≫ pullback.fst A.hom g) ?_, ?_⟩⟩
  · ext
    rw [← pointsToPullback_left_fst g A h Q₁, ← pointsToPullback_left_fst g A h Q₂, hQ]
  · have hP : P.left ≫ pullback.snd A.hom g = s := Over.w P
    simp [pullback.condition, reassoc_of% hP, h]
  · ext
    apply pullback.hom_ext
    · rw [pointsToPullback_left_fst]; rfl
    · exact (Over.w (pointsToPullback g A h _)).trans (Over.w P).symm

/-- The group isomorphism `A_Y(T) ≃* A(T)`, postcomposition with `pullback.fst`. -/
private noncomputable def pointsPullbackMulEquiv (h : s ≫ g = t) :
    (Over.mk s ⟶ (Over.pullback g).obj A) ≃* (Over.mk t ⟶ A) :=
  (MulEquiv.ofBijective _ (pointsToPullback_bijective g A h)).symm

private lemma pointsPullbackMulEquiv_left (h : s ≫ g = t)
    (P : Over.mk s ⟶ (Over.pullback g).obj A) :
    (pointsPullbackMulEquiv g A h P).left = P.left ≫ pullback.fst A.hom g := by
  obtain ⟨Q, rfl⟩ := (pointsToPullback_bijective g A h).2 P
  rw [pointsPullbackMulEquiv, ← MulEquiv.ofBijective_apply _ (pointsToPullback_bijective g A h) Q,
    MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply, pointsToPullback_left_fst]

end Points

/-- For a group scheme `A` over a field `F` and field extensions `K'/K/F`, postcomposition with the
projection `A ×_F Spec K ⟶ A` is a group isomorphism from the `K'`-points of the base change
`(Over.pullback (Spec.map (algebraMap F K))).obj A` (morphisms over `Spec K`) to the `K'`-points of
`A` (morphisms over `Spec F`), and it commutes with precomposition by `Spec σ` for
`σ : K' ≃ₐ[K] K'`. -/
@[faltings "lem_mw_base_change_points"]
theorem exists_mulEquiv_points_pullback (F K K' : Type u) [Field F] [Field K] [Field K']
    [Algebra F K] [Algebra K K'] [Algebra F K'] [IsScalarTower F K K']
    (A : Over (Spec (CommRingCat.of F))) [GrpObj A] :
    letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj A) :=
      @Over.grpObjMkPullbackSnd _ _ _ _ _ _ A.hom _ ‹GrpObj A›
    ∃ e : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj A) ≃*
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F K'))) ⟶ A),
      (∀ P, (e P).left =
        P.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap F K)))) ∧
      ∀ (σ : K' ≃ₐ[K] K') (P Q), Q.left = Spec.map (CommRingCat.ofHom (σ : K' →+* K')) ≫ P.left →
        (e Q).left = Spec.map (CommRingCat.ofHom (σ : K' →+* K')) ≫ (e P).left := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F K)) =
        Spec.map (CommRingCat.ofHom (algebraMap F K')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨pointsPullbackMulEquiv _ A h, pointsPullbackMulEquiv_left _ A h, fun σ P Q hPQ => ?_⟩
  rw [pointsPullbackMulEquiv_left, pointsPullbackMulEquiv_left, hPQ, Category.assoc]

end Faltings
