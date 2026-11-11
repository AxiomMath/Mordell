module
public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.PicardPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The subgroup `Pic⁰` of an abelian variety

Let `A` be an abelian variety over a field `k`, and write `s₁, s₂ : A × A → A` for the two
projections and `s₁₂ : A × A → A` for the group law, `s₁₂(x, y) = x + y`. The subgroup
`Pic⁰(A)` of the Picard group `Pic(A)` consists of the classes `c` with
`s₁₂^* c = s₁^* c + s₂^* c` in `Pic(A × A)`.

## Main definitions

* `Faltings.picZero k A`: the subgroup `Pic⁰(A)` of `Pic(A)`, the equalizer of the two group
  homomorphisms `s₁₂^*` and `s₁^* + s₂^*` from `Pic(A)` to `Pic(A × A)`.

## Implementation notes

The abelian variety is a group object `A` in schemes over `Spec k`; the product `A × A` is the
monoidal product `A ⊗ A` in `Over (Spec k)`, whose underlying scheme is the fibre product
`A ×_k A`. The projections are `fst A A` and `snd A A`, and the addition map is the
multiplication `μ` of the group object. The Picard group of a scheme and the pull-back of
classes are those of the Stacks project library (`Stacks.Picard.ofScheme` and
`Stacks.Picard.schemePullbackClassHom`); the group law of `Pic` is the tensor product of
invertible sheaves, written additively.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Theorem 5.5, Remark 5.6, Proposition 8.4,
  Remark 8.5.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace Faltings

variable (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]

/-- The subgroup `Pic⁰(A)` of the Picard group of an abelian variety `A` over `k`: the classes
`c` with `s₁₂^* c = s₁^* c + s₂^* c` in `Pic(A × A)`, where `s₁, s₂` are the projections
`A × A → A` and `s₁₂` is the group law. -/
@[expose, faltings "def_nt_pic0"]
public noncomputable def picZero [IsAbelianVariety k A] : AddSubgroup (Stacks.Picard.ofScheme A.left) :=
  (Stacks.Picard.schemePullbackClassHom μ[A].left).eqLocus
    (Stacks.Picard.schemePullbackClassHom (fst A A).left +
      Stacks.Picard.schemePullbackClassHom (snd A A).left)

end Faltings


/-!
# Classes in `Pic⁰` are additive

Let `A` be an abelian variety over a field `k` and `M ∈ Pic⁰(A)`. For a variety `V` over `k`
and two `k`-morphisms `α, β : V → A`, the pull-back of `M` along the pointwise sum
`α + β = μ ∘ (α, β)` is the sum of the pull-backs: `(α + β)^* M = α^* M + β^* M`.
It follows by pulling back the defining identity `s₁₂^* M = s₁^* M + s₂^* M` of `Pic⁰(A)`
along `(α, β) : V → A × A`.

## Main results

* `Faltings.picZero_pullback_lift_mul`: `(α + β)^* M = α^* M + β^* M` for
  `M ∈ Faltings.picZero k A`.

## Implementation notes

The sum `α + β` of two morphisms into the group object `A` is written as the composite
`lift α β ≫ μ[A]` of the pairing `V → A ⊗ A` with the group law, so that the map is pinned
explicitly rather than through an instance on the hom-set. The group law of `Pic` is written
additively, as in `Faltings.picZero`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Remark 8.5.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace Faltings

/-- For `M ∈ Pic⁰(A)` and morphisms `α, β : V → A` from a variety `V`, the pull-back of `M`
along `α + β = μ ∘ (α, β)` is `α^* M + β^* M`. -/
@[faltings "lem_nt_pic0_additive"]
public theorem picZero_pullback_lift_mul (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety k A] {M : Stacks.Picard.ofScheme A.left}
    (hM : M ∈ picZero k A) (V : Over (Spec (CommRingCat.of k))) [IsVariety k V.hom]
    (α β : V ⟶ A) :
    Stacks.Picard.schemePullbackClassHom (lift α β ≫ μ[A]).left M =
      Stacks.Picard.schemePullbackClassHom α.left M +
        Stacks.Picard.schemePullbackClassHom β.left M := by
  have h := congrArg (Stacks.Picard.schemePullbackClassHom (lift α β).left) hM
  rwa [AddMonoidHom.add_apply, map_add, schemePullbackClassHom_comp_left,
    schemePullbackClassHom_comp_left, schemePullbackClassHom_comp_left, lift_fst, lift_snd] at h

end Faltings


/-!
# Classes in `Pic⁰` are odd

Let `A` be an abelian variety over a field `k` and `[-1] : A ⟶ A` the inversion of its group
law. Every class `M ∈ Pic⁰(A)` satisfies `[-1]^* M = -M` in `Pic(A)`; in particular its image
`1 ⊗ M` in `Pic(A) ⊗ ℚ` is odd in the sense of `Faltings.IsOddClass`.

The proof uses the additivity of `M`: along the pair `(𝟙, [-1])`, whose sum is the constant map
`0`, it gives `0^* M = M + [-1]^* M`; along `(0, 0)`, whose sum is `0` again, it gives
`0^* M = 0^* M + 0^* M`, so `0^* M = 0`.

## Main results

* `Faltings.schemePullbackClassHom_inv_of_mem_picZero`: `[-1]^* M = -M` for `M ∈ Pic⁰(A)`.

## Implementation notes

The identity is stated in `Pic(A)` itself rather than in `Pic(A) ⊗ ℚ`: it is the integral
statement, and it implies `Faltings.IsOddClass k A (1 ⊗ₜ M)` by applying the base change of
`[-1]^*` to `1 ⊗ₜ M`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Remark 8.5.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonObj

namespace Faltings

/-- A class in `Pic⁰(A)` pulls back to `0` along the constant map `0 = η ∘ (A → pt)`: additivity
along `(0, 0)` gives `0^* M = 0^* M + 0^* M`. -/
private lemma schemePullbackClassHom_one_of_mem_picZero (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    {M : Stacks.Picard.ofScheme A.left} (hM : M ∈ picZero k A) :
    Stacks.Picard.schemePullbackClassHom (toUnit A ≫ η[A]).left M = 0 := by
  have h := picZero_pullback_lift_mul k A hM A (toUnit A ≫ η[A]) (toUnit A ≫ η[A])
  rw [MonObj.lift_comp_one_left] at h
  exact left_eq_add.mp h

/-- On an abelian variety `A` over `k`, pull-back along the inversion `[-1] = ι[A]` acts as
`-1` on `Pic⁰(A)`: `[-1]^* M = -M` for every `M ∈ Faltings.picZero k A`. -/
@[faltings "lem_nt_pic0_odd"]
public theorem schemePullbackClassHom_inv_of_mem_picZero (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    {M : Stacks.Picard.ofScheme A.left} (hM : M ∈ picZero k A) :
    Stacks.Picard.schemePullbackClassHom ι[A].left M = -M := by
  have h := picZero_pullback_lift_mul k A hM A (𝟙 A) ι[A]
  rw [GrpObj.right_inv, schemePullbackClassHom_one_of_mem_picZero k A hM, Over.id_left,
    show Stacks.Picard.schemePullbackClassHom (𝟙 A.left) M = M from
      Stacks.Picard.schemePullbackClass_id A.left M] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end Faltings
