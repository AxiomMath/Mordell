module

public import Mathlib
public import Mordell.AbelianVariety.PicZero
public import Mordell.AbelianVariety.TheoremOfTheSquare

/-!
# The odd part of a class on an abelian variety lies in `Pic⁰`

Let `A` be an abelian variety over a field `k` and write `c⁻ = [-1]^* c` for the pull-back of a
class `c ∈ Pic(A)` along the inversion `[-1] : A → A`. Then `c - c⁻` lies in `Pic⁰(A)`.

Writing `[x] = x^* c` for a morphism `x : B → A`, the theorem of the cube for the triple
`(f, g, (f g)⁻¹)`, whose product is `1`, reads
`[f] + [g] + [(f g)⁻¹] = [f g] + [g⁻¹] + [f⁻¹]` (using that `A` is commutative), and since
`[x⁻¹] = x^* c⁻` this says that `d = c - c⁻` satisfies `(f g)^* d = f^* d + g^* d`. For
`(f, g) = (pr₁, pr₂)` this is the defining relation of `Pic⁰` for `d`.

## Main results

* `Faltings.sub_pullback_inv_mem_picZero`: for every `c ∈ Pic(A)`, `c - [-1]^* c ∈ Pic⁰(A)`.

## Implementation notes

The inversion `[-1]` is the inverse `ι[A]` of the group object `A` in `Over (Spec k)`; the
pull-back of classes is `Stacks.Picard.schemePullbackClassHom` along the underlying morphism of
schemes, and `Pic⁰(A)` is `Faltings.picZero k A`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, proof of Theorem 6.6; Ch. I, Theorem 5.3,
  Proposition 8.4.
-/

@[expose] public section

namespace Faltings

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Faltings.AbelianVariety (schemePullbackClass_cube schemePullbackClass_comp_spec_field
  schemePullbackClass_sub)

universe u

/-- Pull-back along the unit morphism `1 : B ⟶ A` is zero, as it factors through `Spec k`. -/
private lemma schemePullbackClass_one {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] {B : Over (Spec (CommRingCat.of k))}
    (x : Stacks.Picard.ofScheme A.left) :
    Stacks.Picard.schemePullbackClass (1 : B ⟶ A).left x = 0 := by
  rw [Hom.one_def, Over.comp_left]
  exact schemePullbackClass_comp_spec_field _ _ x

/-- Pull-back along `x⁻¹ = x ≫ ι` is pull-back of `[-1]^* c` along `x`. -/
private lemma schemePullbackClass_inv {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] {B : Over (Spec (CommRingCat.of k))}
    (x : B ⟶ A) (c : Stacks.Picard.ofScheme A.left) :
    Stacks.Picard.schemePullbackClass (x⁻¹).left c =
      Stacks.Picard.schemePullbackClass x.left (Stacks.Picard.schemePullbackClass ι[A].left c) := by
  rw [Hom.inv_def, Over.comp_left, Stacks.Picard.schemePullbackClass_comp]

/-- On a commutative abelian variety `A`, the odd part `d = c - [-1]^* c` of a class is
additive on morphisms: `(f g)^* d = f^* d + g^* d`. This is the cube relation for the triple
`(f, g, (f g)⁻¹)`. -/
private lemma schemePullbackClass_mul_sub_inv {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A] [IsAbelianVariety k A]
    (c : Stacks.Picard.ofScheme A.left) {B : Over (Spec (CommRingCat.of k))} (f g : B ⟶ A) :
    Stacks.Picard.schemePullbackClass (f * g).left
        (c - Stacks.Picard.schemePullbackClass ι[A].left c) =
      Stacks.Picard.schemePullbackClass f.left
          (c - Stacks.Picard.schemePullbackClass ι[A].left c) +
        Stacks.Picard.schemePullbackClass g.left
          (c - Stacks.Picard.schemePullbackClass ι[A].left c) := by
  have h := schemePullbackClass_cube A c f g (f * g)⁻¹
  rw [mul_inv_cancel, schemePullbackClass_one, zero_add,
    show f * (f * g)⁻¹ = g⁻¹ by rw [mul_inv_rev, mul_left_comm, mul_inv_cancel, _root_.mul_one],
    show g * (f * g)⁻¹ = f⁻¹ by rw [mul_inv_rev, mul_inv_cancel_left],
    schemePullbackClass_inv, schemePullbackClass_inv, schemePullbackClass_inv] at h
  rw [schemePullbackClass_sub, schemePullbackClass_sub, schemePullbackClass_sub, ← sub_eq_zero,
    ← neg_eq_zero]
  convert sub_eq_zero.mpr h using 1
  have key : ∀ {G : Type (u + 1)} [AddCommGroup G] (a b c d e h : G), -(a - b - (c - d + (e - h))) = c + e + b - (a + h + d) := by
    intros; abel
  exact key _ _ _ _ _ _

/-- On an abelian variety `A` over `k`, for every class `c ∈ Pic(A)` the difference
`c - [-1]^* c` lies in `Pic⁰(A)`, where `[-1] = ι[A]` is the inversion of `A`. -/
@[faltings "lem_nt_odd_part_in_pic0"]
theorem sub_pullback_inv_mem_picZero (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety k A] (c : Stacks.Picard.ofScheme A.left) :
    c - Stacks.Picard.schemePullbackClassHom ι[A].left c ∈ picZero k A := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have := schemePullbackClass_mul_sub_inv A c (fst A A) (snd A A)
  rwa [Hom.mul_def, lift_fst_snd, Category.id_comp] at this

end Faltings
