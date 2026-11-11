module

public import Mordell.NeronTate.Pairing.Basic
public import Mordell.Jacobian.DeltaClass
public import Mordell.NeronTate.Additivity
public import Mordell.NeronTate.Functoriality

/-!
# The Néron–Tate height of `δ` is minus the Néron pairing

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one, of
genus `g ≥ 1`, `(J, ι)` a Jacobian of `C`, `θ = cl(Θ) ∈ Pic(J)` the class of the theta divisor,
and `δ = s₁^* θ + s₂^* θ - s₁₂^* θ ∈ Pic(J × J)` (`Faltings.deltaClass`). Over an algebraic
closure `K` of `k`, the Néron–Tate height of `δ` on the abelian variety `(J × J)_K` is minus the
Néron pairing (`Faltings.neronPairing`): `ĥ_δ(x, y) = -⟨x, y⟩` for `x, y ∈ J(K)`.

The maps `s₁, s₂, s₁₂ : J × J → J` are homomorphisms (`J` is commutative), so by functoriality
of Néron–Tate heights `ĥ_θ ∘ s₁ + ĥ_θ ∘ s₂ - ĥ_θ ∘ s₁₂` is a Néron–Tate height of `δ`, hence equal
to `ĥ_δ` by uniqueness, and its value at `(x, y)` is `ĥ_θ(x) + ĥ_θ(y) - ĥ_θ(x + y) = -⟨x, y⟩`.

## Main results

* `Faltings.isNeronTateHeight_deltaClass_apply_eq_neg_neronPairing`: `ĥ_δ(x, y) = -⟨x, y⟩`.

## Implementation notes

`J × J` is the monoidal product `J ⊗ J` in schemes over `Spec k`, an abelian variety over `k`
because the fibre product of two geometrically integral proper `k`-varieties is again one
(`AlgebraicGeometry.Cube.geometricallyIntegral_fst_comp`). Its base change to `K` carries the
class `1 ⊗ δ_K ∈ ℚ ⊗ Pic((J × J)_K)`, `δ_K` the pull-back of `δ` along the projection. A pair
`(x, y)` of points `Spec K ⟶ J` over `k` is the section `((x, y), 1)` of `(J × J)_K ⟶ Spec K`.
The height `ĥ_δ` is any function that is a Néron–Tate height of `1 ⊗ δ_K`
(`Faltings.IsNeronTateHeight`); it is unique.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, proof of Lemma 2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj TensorProduct

universe u

namespace Faltings

/-- Pulling a Picard class back around the two sides of a commutative square gives the same
class. -/
private lemma schemePullbackClassHom_comp_of_comm {W X Y Z : Scheme.{u}}
    {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (w : a ≫ b = c ≫ d) (x : Z.picardGroup) :
    Stacks.Picard.schemePullbackClassHom a (Stacks.Picard.schemePullbackClassHom b x) =
      Stacks.Picard.schemePullbackClassHom c (Stacks.Picard.schemePullbackClassHom d x) := by
  change Stacks.Picard.schemePullbackClass a (Stacks.Picard.schemePullbackClass b x) =
    Stacks.Picard.schemePullbackClass c (Stacks.Picard.schemePullbackClass d x)
  rw [Stacks.Picard.schemePullbackClass_comp, w, ← Stacks.Picard.schemePullbackClass_comp]

/-- The base change of `g : A ⟶ B` along `φ`, followed by the first projection, is the first
projection followed by `g`. -/
private lemma pullback_map_left_fst {S T : Scheme.{u}} (φ : T ⟶ S) {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback φ).map g).left ≫ pullback.fst B.hom φ = pullback.fst A.hom φ ≫ g.left :=
  pullback.lift_fst _ _ _

/-- The base change of `g : A ⟶ B` along `φ` commutes with the second projections. -/
private lemma pullback_map_left_snd {S T : Scheme.{u}} (φ : T ⟶ S) {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback φ).map g).left ≫ pullback.snd B.hom φ = pullback.snd A.hom φ :=
  pullback.lift_snd _ _ _

/-- Pulling the `ℚ`-class of a base-changed class back along the base change of `g : A ⟶ B`
gives the base change of the pull-back along `g`. -/
private lemma baseChange_schemePullbackClassHom_pullback_map {S T : Scheme.{u}} (φ : T ⟶ S)
    {A B : Over S} (g : A ⟶ B) (θ : B.left.picardGroup) :
    (Stacks.Picard.schemePullbackClassHom ((Over.pullback φ).map g).left).toIntLinearMap.baseChange
        ℚ ((1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst B.hom φ) θ) =
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φ)
        (Stacks.Picard.schemePullbackClassHom g.left θ) := by
  rw [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    schemePullbackClassHom_comp_of_comm (pullback_map_left_fst φ g)]

/-- The base change to `T` of a point `z` of `A` over `φ : T ⟶ S`, followed by the base change of
`g : A ⟶ B`, is the base change of the point `z ≫ g`. -/
private lemma pullback_lift_comp_pullback_map_left {S T : Scheme.{u}} {φ : T ⟶ S} {A B : Over S}
    (g : A ⟶ B) (z : Over.mk φ ⟶ A) :
    pullback.lift z.left (𝟙 T) (by simp) ≫ ((Over.pullback φ).map g).left =
      pullback.lift (z ≫ g).left (𝟙 T) (by simp) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback_map_left_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      Over.comp_left]
  · rw [Category.assoc, pullback_map_left_snd, pullback.lift_snd, pullback.lift_snd]

/-- The square `A ⊗ A` of an abelian variety `A` is an abelian variety. -/
public lemma isAbelianVariety_tensorObj {k : Type u} [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsAbelianVariety k A] : IsAbelianVariety k (A ⊗ A) := by
  have hgi : GeometricallyIntegral (pullback.fst A.hom A.hom ≫ A.hom) :=
    Cube.geometricallyIntegral_fst_comp A.hom A.hom
  have : IsIntegral (pullback A.hom A.hom) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst A.hom A.hom ≫ A.hom)
  have : IsVariety k (pullback.fst A.hom A.hom ≫ A.hom) := IsVariety.mk
  have : IsProperVariety k (pullback.fst A.hom A.hom ≫ A.hom) := IsProperVariety.mk
  exact IsAbelianVariety.mk (toIsProperVariety := this) (toGeometricallyIntegral := hgi)

/-- **The Néron–Tate height of `δ` is minus the Néron pairing.** Over an algebraic closure `K`
of the number field `k`, every Néron–Tate height `f` of the class
`δ = s₁^* θ + s₂^* θ - s₁₂^* θ` (`Faltings.deltaClass`) on `(J × J)_K` satisfies
`f(x, y) = -⟨x, y⟩` (`Faltings.neronPairing`) for all `x, y ∈ J(K)`. -/
@[faltings "lem_nt_height_delta_class"]
public theorem isNeronTateHeight_deltaClass_apply_eq_neg_neronPairing {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    haveI : IsAbelianVariety k (A.J ⊗ A.J) := by
      have : GeometricallyIntegral (pullback.fst A.J.hom A.J.hom ≫ A.J.hom) :=
        Cube.geometricallyIntegral_fst_comp A.J.hom A.J.hom
      have : IsIntegral (pullback A.J.hom A.J.hom) :=
        GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst A.J.hom A.J.hom ≫ A.J.hom)
      have : IsVariety k (pullback.fst A.J.hom A.J.hom ≫ A.J.hom) := IsVariety.mk
      have : IsProperVariety k (pullback.fst A.J.hom A.J.hom ≫ A.J.hom) := IsProperVariety.mk
      exact IsAbelianVariety.mk (toIsProperVariety := this)
        (toGeometricallyIntegral := by assumption)
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JJK : Over (Spec (.of K)) := (Over.pullback φK).obj (A.J ⊗ A.J)
    let δK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JJK.left :=
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst (A.J ⊗ A.J).hom φK)
        (deltaClass X A hg j hj D hrad hsupp)
    let pt : Additive (Over.mk φK ⟶ A.J) → Additive (Over.mk φK ⟶ A.J) →
        {p : Spec (.of K) ⟶ JJK.left // p ≫ JJK.hom = 𝟙 _} :=
      fun x y ↦ ⟨pullback.lift (lift x.toMul y.toMul).left (𝟙 _)
        (by rw [Category.id_comp]; exact Over.w _), pullback.lift_snd _ _ _⟩
    ∀ f : {p : Spec (.of K) ⟶ JJK.left // p ≫ JJK.hom = 𝟙 _} → ℝ,
      IsNeronTateHeight JJK δK f → ∀ x y,
        f (pt x y) = -neronPairing X A hg j hj D hrad hsupp K x y := by
  intro φK JJK δK pt f hf x y
  have := A.isAbelianVariety
  letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  have := isAbelianVariety_tensorObj A.J
  let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
  let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
    (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)
      (Stacks.Divisors.picardClass D)
  -- the Néron–Tate height `ĥ_θ` used by `neronPairing`
  let F := Classical.epsilon fun F ↦ IsNeronTateHeight JK θK F
  have hF : IsNeronTateHeight JK θK F :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic JK θK)
  -- `ĥ_θ ∘ s₁ + ĥ_θ ∘ s₂ - ĥ_θ ∘ s₁₂` is a Néron–Tate height of `δ`, so it is `f`
  let s₁ : JJK ⟶ JK := (Over.pullback φK).map (fst A.J A.J)
  let s₂ : JJK ⟶ JK := (Over.pullback φK).map (snd A.J A.J)
  let s₁₂ : JJK ⟶ JK := (Over.pullback φK).map μ[A.J]
  have : IsMonHom s₁ := open scoped Obj in Functor.map.instIsMonHom _ _ _
  have : IsMonHom s₂ := open scoped Obj in Functor.map.instIsMonHom _ _ _
  have : IsMonHom s₁₂ := open scoped Obj in Functor.map.instIsMonHom _ _ _
  have hδ := ((hF.comp s₁).smul_add_smul (hF.comp s₂) 1 1).smul_add_smul (hF.comp s₁₂) 1 (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg, Rat.cast_one, one_mul, Rat.cast_neg,
    neg_one_mul] at hδ
  rw [baseChange_schemePullbackClassHom_pullback_map,
    baseChange_schemePullbackClassHom_pullback_map,
    baseChange_schemePullbackClassHom_pullback_map, ← TensorProduct.tmul_add,
    ← TensorProduct.tmul_sub, ← map_add, ← map_sub] at hδ
  rw [hf.unique hδ]
  -- evaluate at `(x, y)`: the three points are `x`, `y` and `x + y` read on `J_K`
  have e : ∀ (s : A.J ⊗ A.J ⟶ A.J) (z : Additive (Over.mk φK ⟶ A.J)),
      lift x.toMul y.toMul ≫ s = z.toMul → ∀ hp,
      F ⟨(pt x y).1 ≫ ((Over.pullback φK).map s).left, hp⟩ =
        F ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩ := by
    rintro s z hz hp
    congr 1
    exact Subtype.ext ((pullback_lift_comp_pullback_map_left s _).trans (by simp only [hz]))
  simp only [s₁, s₂, s₁₂, e _ x (lift_fst _ _), e _ y (lift_snd _ _), e _ (x + y) rfl]
  change _ = -QuadraticMap.polar (F ∘ _) x y
  simp only [QuadraticMap.polar, Function.comp_apply]
  ring

end Faltings

end
