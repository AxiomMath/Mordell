module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Even classes in the rational Picard group of an abelian variety

Let `A` be an abelian variety over a field `k`, and let `[-1] : A ⟶ A` be the inversion of its
group law. Pull-back along `[-1]` is an additive endomorphism of `Pic(A)`, hence a `ℚ`-linear
endomorphism `c ↦ c⁻` of `ℚ ⊗[ℤ] Pic(A)`. A class `c ∈ ℚ ⊗[ℤ] Pic(A)` is *even* (symmetric)
if `c⁻ = c`.

## Main definitions

* `Faltings.IsEvenClass`: the class `c ∈ ℚ ⊗[ℤ] Pic(A)` satisfies `[-1]^* c = c`.

## Implementation notes

`Pic(A) ⊗ ℚ` is `ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left`, and `c⁻` is the base change to `ℚ` of
the pull-back `Stacks.Picard.schemePullbackClassHom` along the inversion
`(GrpObj.inv (X := A)).left` of the group object `A` in schemes over `Spec k`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Corollary 5.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace Faltings

/-- A class `c ∈ Pic(A) ⊗ ℚ` on an abelian variety `A` over `k` is *even* (symmetric) if
`c⁻ = c`, where `c⁻ = [-1]^* c` is pull-back along the inversion `[-1] : A ⟶ A`. -/
@[faltings "def_nt_even_odd_class"]
def IsEvenClass (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
    [IsAbelianVariety k A] (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) : Prop :=
  (Stacks.Picard.schemePullbackClassHom (GrpObj.inv (X := A)).left).toIntLinearMap.baseChange ℚ c
    = c

end Faltings

/-!
# Odd classes in the rational Picard group of an abelian variety

Let `A` be an abelian variety over a field `k`, and let `[-1] : A ⟶ A` be the inversion of its
group law. Pull-back along `[-1]` is an additive endomorphism of `Pic(A)`, hence a `ℚ`-linear
endomorphism `c ↦ c⁻` of `Pic(A) ⊗ ℚ`. A class `c ∈ Pic(A) ⊗ ℚ` is *odd* (antisymmetric)
if `c⁻ = -c`.

## Main definitions

* `Faltings.IsOddClass`: the class `c ∈ ℚ ⊗[ℤ] Pic(A)` satisfies `[-1]^* c = -c`.

## Implementation notes

The abelian variety is a group object `A` in `Over (Spec k)` with
`AlgebraicGeometry.IsAbelianVariety k A`. `Pic(A) ⊗ ℚ` is
`ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left`, and `c⁻` is the base change to `ℚ` of
`Stacks.Picard.schemePullbackClassHom ι[A].left`, the pull-back along the inversion `ι[A]`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Corollary 5.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonObj
open scoped TensorProduct

namespace Faltings

/-- A class `c ∈ Pic(A) ⊗ ℚ` on an abelian variety `A` over `k` is *odd* (antisymmetric) if
`c⁻ = -c`, where `c⁻ = [-1]^* c` is pull-back along the inversion `[-1] = ι[A] : A ⟶ A`. -/
@[faltings "def_nt_odd_class"]
def IsOddClass (k : Type u) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
    [IsAbelianVariety k A] (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) : Prop :=
  (Stacks.Picard.schemePullbackClassHom ι[A].left).toIntLinearMap.baseChange ℚ c = -c

end Faltings
