module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-!
# Points of the base change of a group scheme along a field extension

Let `A` be a scheme over a field `k`, let `K/k` be a field extension with
`π : Spec K ⟶ Spec k`, and let `A_K = A ×_k K` be the base change. For a `K`-scheme `T`, the
adjunction `Over.map π ⊣ Over.pullback π` identifies the `T`-points `T ⟶ A_K` over `K` with the
`k`-morphisms `T ⟶ A`, `T` being regarded as a `k`-scheme through `π`. When `A` is a group scheme
over `k`, with `A_K` carrying the base-changed group law, this bijection is an isomorphism of
groups.

## Main definitions and results

* `Faltings.P`: a `T`-point of `A_K` as a `k`-morphism `T ⟶ A`.
* `Faltings.mapPullbackAdj_homEquiv_mul`: the adjunction bijection is multiplicative.
* `Faltings.pEquiv`: `P` as an isomorphism of groups.
* `Faltings.P_left`, `Faltings.lift_P_left`: the underlying morphisms of schemes.
* `Faltings.P_comp_left`, `Faltings.P_comp_right`: naturality of `P` in `T` and in `A`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

universe u

namespace Faltings

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- A `T`-point of `A_K` as a `k`-morphism `T ⟶ A`. -/
@[expose] public noncomputable abbrev P (A : Over (Spec (.of k))) {T : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) : (Over.map π).obj T ⟶ A :=
  ((Over.mapPullbackAdj π).homEquiv T A).symm u

/-- Transposition along `Over.map π ⊣ Over.pullback π` respects the group laws of `A` and
`A_K`. -/
public lemma mapPullbackAdj_homEquiv_mul (A : Over (Spec (.of k))) [GrpObj A]
    {T : Over (Spec (.of K))} (a b : (Over.map π).obj T ⟶ A) :
    (Over.mapPullbackAdj π).homEquiv T A (a * b) =
      (Over.mapPullbackAdj π).homEquiv T A a * (Over.mapPullbackAdj π).homEquiv T A b := by
  change (Over.mapPullbackAdj π).homEquiv T A (a * b) = lift _ _ ≫
    Functor.LaxMonoidal.μ (Over.pullback π) A A ≫ (Over.pullback π).map μ[A]
  simp only [Hom.mul_def, (Over.mapPullbackAdj π).homEquiv_unit,
    Functor.map_comp, ← Functor.Monoidal.lift_μ, comp_lift_assoc, Category.assoc]

/-- `P` as an isomorphism of groups. -/
@[expose] public noncomputable def pEquiv (A : Over (Spec (.of k))) [GrpObj A]
    (T : Over (Spec (.of K))) : (T ⟶ (Over.pullback π).obj A) ≃* ((Over.map π).obj T ⟶ A) :=
  MulEquiv.symm
    { (Over.mapPullbackAdj π).homEquiv T A with
      map_mul' := mapPullbackAdj_homEquiv_mul A }

public lemma pEquiv_apply (A : Over (Spec (.of k))) [GrpObj A] {T : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) : pEquiv A T u = P A u := rfl

/-- `P` is multiplicative. -/
public lemma P_mul (A : Over (Spec (.of k))) [GrpObj A] {T : Over (Spec (.of K))}
    (u v : T ⟶ (Over.pullback π).obj A) : P A (u * v) = P A u * P A v :=
  map_mul (pEquiv A T) u v

/-- The underlying morphism of `P A u` is `u` followed by the projection `A_K ⟶ A`. -/
public lemma P_left (A : Over (Spec (.of k))) {T : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) :
    (P A u).left = u.left ≫ pullback.fst A.hom π := by
  simp [P, Over.mapPullbackAdj]

/-- The `T`-point `(P u, T ⟶ Spec K)` of `A ⊗ Spec K` has underlying morphism that of `u`. -/
public lemma lift_P_left (A : Over (Spec (.of k))) {T : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) :
    (lift (P A u) (Over.homMk T.hom : (Over.map π).obj T ⟶ Over.mk π)).left = u.left := by
  apply pullback.hom_ext
  · change (lift (P A u) (Over.homMk T.hom : (Over.map π).obj T ⟶ Over.mk π)).left ≫
      (fst A (Over.mk π)).left = _
    rw [← Over.comp_left, lift_fst, P_left]
    rfl
  · change (lift (P A u) (Over.homMk T.hom : (Over.map π).obj T ⟶ Over.mk π)).left ≫
      (snd A (Over.mk π)).left = _
    rw [← Over.comp_left, lift_snd]
    exact (Over.w u).symm

/-- `P` is natural in the `K`-scheme `T`. -/
public lemma P_comp_left (A : Over (Spec (.of k))) {T T' : Over (Spec (.of K))} (v : T' ⟶ T)
    (u : T ⟶ (Over.pullback π).obj A) : P A (v ≫ u) = (Over.map π).map v ≫ P A u :=
  (Over.mapPullbackAdj π).homEquiv_naturality_left_symm v u

/-- `P` is natural in the `k`-scheme `A`. -/
public lemma P_comp_right {A B : Over (Spec (.of k))} {T : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) (m : A ⟶ B) :
    P B (u ≫ (Over.pullback π).map m) = P A u ≫ m :=
  (Over.mapPullbackAdj π).homEquiv_naturality_right_symm u m

end Faltings
