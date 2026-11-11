module
public import Mordell.Jacobian.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.GroupSchemeCriterion

/-!
# `ι` on the points of a Jacobian

Let `(J, ι)` be a Jacobian of a curve `C` over a field `k`. For every `k`-scheme `T` the map
`ι(T) : P⁰_C(T) ⟶ J(T)` is a homomorphism (`Faltings.Jacobian.map_add`), with the group law of
`J(T) = Hom_k(T, J)` written multiplicatively. This file records the consequences used for
computing with points: `ι(0) = 1`, `ι(-x) = ι(x)⁻¹`, `ι(x - y) = ι(x) ι(y)⁻¹`, and `ι` of a
finite sum is the product. The points of `J` with values in a field extension `K ⊇ k` are the
morphisms from `AlgebraicGeometry.fieldExtensionPoint k K`.

## Main results

* `Faltings.Jacobian.ι_app_zero`, `Faltings.Jacobian.ι_app_neg`, `Faltings.Jacobian.ι_app_sub`:
  `ι(T)` preserves the unit, inverses and quotients.
* `Faltings.Jacobian.ι_app_list_sum`, `Faltings.Jacobian.ι_app_sum`: `ι(T)` sends sums to
  products.
* `Faltings.comp_list_prod`: precomposition distributes over products in a `Hom`-monoid.
* `Faltings.sumMap`: the summation morphism `Yⁿ ⟶ M`, `(Q₁, …, Qₙ) ↦ j(Q₁) ⋯ j(Qₙ)`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped MonObj

universe u

namespace Faltings

/-- Precomposition distributes over products of lists in a `Hom`-monoid. -/
public lemma comp_list_prod {C : Type*} [Category C] [CartesianMonoidalCategory C] {Y Y' M : C}
    [MonObj M] (f : Y' ⟶ Y) (l : List (Y ⟶ M)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => exact MonObj.comp_one f
  | cons a l ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

/-- The summation morphism `Yⁿ ⟶ M`, `(Q₁, …, Qₙ) ↦ j(Q₁) ⋯ j(Qₙ)`, for a morphism `j : Y ⟶ M`
to a monoid object. -/
@[expose] public noncomputable abbrev sumMap {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Y M : C} [MonObj M] [HasFiniteProducts C] (n : ℕ) (j : Y ⟶ M) :
    ∏ᶜ (fun _ : Fin n => Y) ⟶ M :=
  (List.ofFn fun i : Fin n => Pi.π (fun _ : Fin n => Y) i ≫ j).prod

namespace Jacobian

variable {k : Type u} [Field k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
  [IsSmoothProjectiveCurve k f] (A : Jacobian k f) (T : Over (Spec (.of k)))

/-- `ι(T)` sends `0` to `1`. -/
public lemma ι_app_zero : (show T ⟶ A.J from A.ι.app (op T) 0) = 1 := by
  have h := A.map_add (op T) 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/-- `ι(T)` sends `-x` to `ι(x)⁻¹`. -/
public lemma ι_app_neg (x : (relativePicZeroFunctor k f).obj (op T)) :
    (show T ⟶ A.J from A.ι.app (op T) (-x)) = (show T ⟶ A.J from A.ι.app (op T) x)⁻¹ := by
  have h := A.map_add (op T) (-x) x
  rw [neg_add_cancel] at h
  exact eq_inv_of_mul_eq_one_left (h.symm.trans (A.ι_app_zero T))

/-- `ι(T)` sends `x - y` to `ι(x) ι(y)⁻¹`. -/
public lemma ι_app_sub (x y : (relativePicZeroFunctor k f).obj (op T)) :
    (show T ⟶ A.J from A.ι.app (op T) (x - y)) =
      (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y)⁻¹ := by
  rw [sub_eq_add_neg]
  exact (A.map_add (op T) x (-y)).trans (congrArg _ (A.ι_app_neg T y))

/-- `ι(T)` sends the sum of a list to the product of the images. -/
public lemma ι_app_list_sum (l : List ((relativePicZeroFunctor k f).obj (op T))) :
    (show T ⟶ A.J from A.ι.app (op T) l.sum) =
      (l.map fun x => (show T ⟶ A.J from A.ι.app (op T) x)).prod := by
  induction l with
  | nil => exact A.ι_app_zero T
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ← ih, List.sum_cons]
    exact A.map_add (op T) a l.sum

/-- `ι(T)` sends a finite sum to the product of the images. -/
public lemma ι_app_sum {n : ℕ} (x : Fin n → (relativePicZeroFunctor k f).obj (op T)) :
    (show T ⟶ A.J from A.ι.app (op T) (∑ i, x i)) =
      (List.ofFn fun i => (show T ⟶ A.J from A.ι.app (op T) (x i))).prod := by
  induction n with
  | zero => simpa using A.ι_app_zero T
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, ← ih]
    exact A.map_add (op T) _ _

end Jacobian

end Faltings
