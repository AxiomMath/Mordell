module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.PicardPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube

/-!
# The parallelogram relation for classes on an abelian variety

Let `A` be an abelian variety over a field `k`. On `A × A` write `s₁, s₂` for the two
projections, `s₁₂(x, y) = x + y` and `s₁₋₂(x, y) = x - y`, and for a class `c` in
`Pic(A) ⊗ ℚ` write `c⁻ = [-1]^* c`. Then in `Pic(A × A) ⊗ ℚ`
`s₁₂^* c + s₁₋₂^* c = 2 s₁^* c + s₂^* (c + c⁻)`.
It is the theorem of the cube applied to the triple of maps `(s₁, s₂, -s₂)`.

## Main results

* `Faltings.pullback_add_add_pullback_sub_eq`: the parallelogram relation in
  `ℚ ⊗[ℤ] Pic(A × A)`.

## Implementation notes

The abelian variety is a group object `A` in `Over (Spec k)` with
`AlgebraicGeometry.IsAbelianVariety k A`, and `A × A` is the cartesian product `A ⊗ A`. The
morphisms `A ⊗ A ⟶ A` form a group (the group structure the group object `A` induces on
`Hom`, written multiplicatively). In that group `s₁ = fst A A`, `s₂ = snd A A`,
`s₁₂ = fst A A * snd A A` and `s₁₋₂ = fst A A / snd A A`, and `[-1] = ι[A]`. The pull-back
of rational classes along `f` is the base change to `ℚ` of
`Stacks.Picard.schemePullbackClassHom f.left`, which is the additive map
`Pic(A) → Pic(A ⊗ A)`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Theorem 5.1, Corollary 5.4.
* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

universe u

namespace Faltings

/-- Pull-back along the unit morphism `1 : B ⟶ A` of a group object kills every class. -/
private lemma schemePullbackClassHom_one {k : Type u} [Field k]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] {B : Over (Spec (CommRingCat.of k))}
    (x : Stacks.Picard.ofScheme A.left) :
    Stacks.Picard.schemePullbackClassHom (1 : B ⟶ A).left x = 0 :=
  (schemePullbackClassHom_eq_pullbackPicardClass _ x).trans
    (Stacks.Groupoids.pullbackPicardClass_one _ _)

/-- The theorem of the cube for a triple `(a, b, c)` of morphisms `B ⟶ A`, on `Pic(B)`. -/
private lemma schemePullbackClassHom_cube (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (x : Stacks.Picard.ofScheme A.left) {B : Over (Spec (CommRingCat.of k))} (a b c : B ⟶ A) :
    Stacks.Picard.schemePullbackClassHom (a * b * c).left x +
        Stacks.Picard.schemePullbackClassHom a.left x +
        Stacks.Picard.schemePullbackClassHom b.left x +
        Stacks.Picard.schemePullbackClassHom c.left x =
      Stacks.Picard.schemePullbackClassHom (a * b).left x +
        Stacks.Picard.schemePullbackClassHom (a * c).left x +
        Stacks.Picard.schemePullbackClassHom (b * c).left x := by
  simp only [schemePullbackClassHom_eq_pullbackPicardClass]
  exact Stacks.Groupoids.pullbackPicardClass_cubeRelation A
    (Stacks.Groupoids.hasTheoremOfTheCube k A) _ _ a b c

/-- The parallelogram relation on `Pic(A × A)`: the cube relation for `(s₁, s₂, -s₂)`. -/
private lemma schemePullbackClassHom_parallelogram (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (x : Stacks.Picard.ofScheme A.left) :
    Stacks.Picard.schemePullbackClassHom (fst A A * snd A A).left x +
        Stacks.Picard.schemePullbackClassHom (fst A A / snd A A).left x =
      Stacks.Picard.schemePullbackClassHom (fst A A).left x +
        Stacks.Picard.schemePullbackClassHom (fst A A).left x +
        Stacks.Picard.schemePullbackClassHom (snd A A).left
          (x + Stacks.Picard.schemePullbackClassHom ι[A].left x) := by
  have h := schemePullbackClassHom_cube k A x (fst A A) (snd A A) (snd A A)⁻¹
  rw [mul_inv_cancel, mul_inv_cancel_right, ← div_eq_mul_inv, Hom.inv_def,
    ← schemePullbackClassHom_comp_left, schemePullbackClassHom_one] at h
  have h' := h.trans (add_zero _)
  rw [map_add]
  exact h'.symm.trans (add_assoc _ _ _)

/-- **Parallelogram relation for classes.** For an abelian variety `A` over `k` and a class
`c ∈ Pic(A) ⊗ ℚ`, in `Pic(A × A) ⊗ ℚ`
`s₁₂^* c + s₁₋₂^* c = 2 s₁^* c + s₂^* (c + [-1]^* c)`,
where `s₁, s₂` are the projections, `s₁₂ = fst * snd` is the sum and `s₁₋₂ = fst / snd` the
difference. -/
@[faltings "lem_nt_parallelogram_classes"]
theorem pullback_add_add_pullback_sub_eq (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) :
    (Stacks.Picard.schemePullbackClassHom (fst A A * snd A A).left).toIntLinearMap.baseChange
        ℚ c +
      (Stacks.Picard.schemePullbackClassHom (fst A A / snd A A).left).toIntLinearMap.baseChange
        ℚ c =
    2 • (Stacks.Picard.schemePullbackClassHom (fst A A).left).toIntLinearMap.baseChange ℚ c +
      (Stacks.Picard.schemePullbackClassHom (snd A A).left).toIntLinearMap.baseChange ℚ
        (c + (Stacks.Picard.schemePullbackClassHom ι[A].left).toIntLinearMap.baseChange ℚ c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, zero_add, add_zero, smul_zero]
  | tmul q x =>
    simp only [LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      ← TensorProduct.tmul_add, schemePullbackClassHom_parallelogram, two_nsmul]
  | add x y hx hy =>
    simp only [map_add, smul_add] at hx hy ⊢
    convert congrArg₂ (· + ·) hx hy using 1 <;> abel

end Faltings


/-!
# Pull-back of classes along multiplication by an integer

Let `A` be an abelian variety over a field `k`, and for `n ∈ ℤ` let `[n] : A → A` be
multiplication by `n`, the `n`-th power of the identity in the group `A ⟶ A` of morphisms into
the group object `A`. Pull-back along `[n]` is an additive endomorphism of `Pic(A)`, hence a
`ℚ`-linear endomorphism `[n]^*` of `ℚ ⊗[ℤ] Pic(A)`. Writing `c⁻ = [-1]^* c`, for every class
`c ∈ ℚ ⊗[ℤ] Pic(A)` and every `n ∈ ℤ`,

`[n]^* c = (n² + n) / 2 • c + (n² - n) / 2 • c⁻`.

## Main results

* `Faltings.multiplication_pullback`: the formula above.

## Implementation notes

The Picard group of a scheme and the pull-back of classes are `Stacks.Picard.ofScheme` and
`Stacks.Picard.schemePullbackClassHom`; on `ℚ ⊗[ℤ] Pic(A)` the pull-back is the base change to
`ℚ` of the `ℤ`-linear map underlying it. Multiplication by `n` is `((𝟙 A : A ⟶ A) ^ n).left`, so
that `[-1]` is the inversion of the group object.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Corollary 5.4.
* [MumAV] D. Mumford, *Abelian Varieties*, Sec. 6, Cor. 3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Faltings

/-- The formula `[n]^* x = T(n) • x + T(-n) • [-1]^* x` in `Pic(A)`, `T` the triangular
numbers: `Stacks.Groupoids.zpowIdPicardClass_eq` applied to a representative of `x`, with the
theorem of the cube supplying its hypothesis. -/
private lemma zpow_pullback_eq (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety k A] (x : Stacks.Picard.ofScheme A.left) (n : ℤ) :
    Stacks.Picard.schemePullbackClassHom ((𝟙 A : A ⟶ A) ^ n).left x =
      Stacks.Groupoids.triangularNumber n • x +
        Stacks.Groupoids.triangularNumber (-n) •
          Stacks.Picard.schemePullbackClassHom ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left x := by
  set L := (Stacks.Picard.picardRepresentative A.left.toRingedSpace x).obj
  have hL := (Stacks.Picard.picardRepresentative A.left.toRingedSpace x).property
  have h : Stacks.SheafOfModules.pullbackPicardClass ((𝟙 A : A ⟶ A) ^ n).left L hL =
      Stacks.Groupoids.triangularNumber n •
          Stacks.SheafOfModules.picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        Stacks.Groupoids.triangularNumber (-n) •
          Stacks.SheafOfModules.pullbackPicardClass ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left L hL :=
    (Stacks.Groupoids.zpowIdPicardClass_eq A L hL
      (Stacks.Groupoids.hasTheoremOfTheCube k A) n).trans
      (by rw [← Stacks.Groupoids.zpowIdPicardClass_neg_one A L hL]; rfl)
  rw [schemePullbackClassHom_eq_pullbackPicardClass,
    schemePullbackClassHom_eq_pullbackPicardClass]
  convert h using 3
  exact (Stacks.Picard.classOf_picardRepresentative A.left.toRingedSpace x).symm

/-- The triangular number `T(n)`, cast to `ℚ`, is `(n² + n) / 2`. -/
private lemma triangularNumber_cast (n : ℤ) :
    ((Stacks.Groupoids.triangularNumber n : ℤ) : ℚ) = ((n : ℚ) ^ 2 + n) / 2 := by
  have h : (2 : ℚ) * (Stacks.Groupoids.triangularNumber n : ℚ) = n * (n + 1) := by
    exact_mod_cast Stacks.Groupoids.two_mul_triangularNumber n
  linarith

/-- **Pull-back by multiplication by `n`** on an abelian variety: for every class
`c ∈ ℚ ⊗[ℤ] Pic(A)` and `n ∈ ℤ`, `[n]^* c = (n² + n)/2 • c + (n² - n)/2 • [-1]^* c`. -/
@[faltings "lem_nt_multiplication_pullback"]
theorem multiplication_pullback (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety k A] (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) (n : ℤ) :
    (Stacks.Picard.schemePullbackClassHom ((𝟙 A : A ⟶ A) ^ n).left).toIntLinearMap.baseChange
        ℚ c =
      (((n : ℚ) ^ 2 + n) / 2) • c +
        (((n : ℚ) ^ 2 - n) / 2) •
          (Stacks.Picard.schemePullbackClassHom
            ((𝟙 A : A ⟶ A) ^ (-1 : ℤ)).left).toIntLinearMap.baseChange ℚ c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [show ((n : ℚ) ^ 2 - n) / 2 = Stacks.Groupoids.triangularNumber (-n) by
        rw [triangularNumber_cast]; push_cast; ring, ← triangularNumber_cast,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      AddMonoidHom.coe_toIntLinearMap, zpow_pullback_eq k A x n, tmul_add, tmul_smul, tmul_smul,
      Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add, smul_add]; abel

end Faltings
