module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# Points of a group scheme as sections of its base change

For a morphism `φ : S' ⟶ S` and a group object `A` over `S`, an `S'`-point of `A` is the same as a
section of the base change `A ×_S S' ⟶ S'`: `GroupScheme.toBaseChange` and `fromBaseChange` are
inverse bijections, and `toBaseChange` is multiplicative (`GroupScheme.toBaseChangeHom`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

namespace GroupScheme

section Points

variable {S S' : Scheme.{u}} (φ : S' ⟶ S) (A : Over S)

/-- A point `x : S' ⟶ A` over `S` as the section `(x, 1)` of the base change `A ×_S S' ⟶ S'`. -/
noncomputable def toBaseChange (x : Over.mk φ ⟶ A) :
    Over.mk (𝟙 S') ⟶ (Over.pullback φ).obj A :=
  Over.homMk (pullback.lift x.left (𝟙 _) (by simp)) (pullback.lift_snd _ _ _)

/-- The section `(x, 1)` followed by the projection `A ×_S S' ⟶ A` is `x`. -/
@[simp]
lemma toBaseChange_left_fst (x : Over.mk φ ⟶ A) :
    (toBaseChange φ A x).left ≫ pullback.fst _ _ = x.left :=
  pullback.lift_fst _ _ _

/-- A point of `A` is determined by its section `(x, 1)` of the base change. -/
lemma toBaseChange_injective : Function.Injective (toBaseChange φ A) := fun x y h ↦ by
  ext
  rw [← toBaseChange_left_fst, h, toBaseChange_left_fst]

variable [GrpObj A]

/-- A section of the base change `A ×_S S' ⟶ S'` as a point `S' ⟶ A` over `S`, through
`AlgebraicGeometry.GroupScheme.pointsMulEquiv`: the section followed by the projection
`A ×_S S' ⟶ A`. -/
noncomputable def fromBaseChange :
    (Over.mk (𝟙 S') ⟶ (Over.pullback φ).obj A) →* (Over.mk φ ⟶ A) where
  toFun a := (Over.homMk (𝟙 S') (by simp) : Over.mk φ ⟶ (Over.map φ).obj (Over.mk (𝟙 S'))) ≫
    AlgebraicGeometry.GroupScheme.pointsMulEquiv φ A _ a
  map_one' := by simp
  map_mul' a b := by simp [MonObj.comp_mul]

/-- The point attached to a section `a` of the base change is `a` followed by the projection
`A ×_S S' ⟶ A`. -/
@[simp]
lemma fromBaseChange_left (a : Over.mk (𝟙 S') ⟶ (Over.pullback φ).obj A) :
    (fromBaseChange φ A a).left = a.left ≫ pullback.fst _ _ := by
  simp [fromBaseChange]

/-- `fromBaseChange` is a left inverse of `toBaseChange`. -/
@[simp]
lemma fromBaseChange_toBaseChange (x : Over.mk φ ⟶ A) :
    fromBaseChange φ A (toBaseChange φ A x) = x := by
  ext
  simp

/-- `toBaseChange` is a left inverse of `fromBaseChange`. -/
@[simp]
lemma toBaseChange_fromBaseChange (a : Over.mk (𝟙 S') ⟶ (Over.pullback φ).obj A) :
    toBaseChange φ A (fromBaseChange φ A a) = a := by
  ext
  refine pullback.hom_ext (by simp) ?_
  simp only [toBaseChange, Over.homMk_left, pullback.lift_snd]
  exact (Over.w a).symm

/-- A section of `A ×_S S' ⟶ S'` is determined by its first projection. -/
lemma fromBaseChange_injective : Function.Injective (fromBaseChange φ A) :=
  Function.LeftInverse.injective (toBaseChange_fromBaseChange φ A)

/-- Every point `S' ⟶ A` over `S` comes from a section of the base change. -/
lemma fromBaseChange_surjective : Function.Surjective (fromBaseChange φ A) :=
  Function.RightInverse.surjective (fromBaseChange_toBaseChange φ A)

/-- The map `x ↦ (x, 1)` from the points of `A` to the sections of its base change is
multiplicative, being inverse to the homomorphism `fromBaseChange`. -/
lemma toBaseChange_mul (x y : Over.mk φ ⟶ A) :
    toBaseChange φ A (x * y) = toBaseChange φ A x * toBaseChange φ A y :=
  fromBaseChange_injective φ A (by simp)

/-- The map `x ↦ (x, 1)` from the points of `A` to the sections of its base change, as a group
homomorphism. -/
noncomputable def toBaseChangeHom :
    (Over.mk φ ⟶ A) →* (Over.mk (𝟙 S') ⟶ (Over.pullback φ).obj A) :=
  MonoidHom.mk' (toBaseChange φ A) (toBaseChange_mul φ A)

@[simp]
lemma toBaseChangeHom_apply (x : Over.mk φ ⟶ A) : toBaseChangeHom φ A x = toBaseChange φ A x :=
  rfl

end Points

end GroupScheme

end Faltings
