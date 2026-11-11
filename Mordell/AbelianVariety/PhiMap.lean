module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# The map `φ_c` on an abelian variety

Let `A` be an abelian variety over a field `k`, `c ∈ Pic(A)`, `K/k` a field extension and
`a ∈ A(K)`. Writing `A_K = A ×_k Spec K` and `τ_a : A_K → A_K` for translation by `a`, put
`φ_c(a) = τ_a^* c - c ∈ Pic(A_K)`, where `c` also denotes its pull-back to `A_K`.

## Main definitions

* `Faltings.AbelianVariety.phiMap`: the class `φ_c(a) = τ_a^* c - c` in `Pic(A_K)`.

## Implementation notes

An abelian variety is a group object `A` of `Over (Spec k)` satisfying
`AlgebraicGeometry.IsAbelianVariety k A`, and a `K`-point of `A` is a morphism
`Spec K ⟶ A` over `Spec k`. The base change `A_K` is the cartesian product `A ⊗ Spec K` in
`Over (Spec k)`, whose underlying scheme is the fibre product `A ×_{Spec k} Spec K`.
The class `τ_a^* c` (with `c` base-changed to `A_K`) is the pull-back of `c` along the
composite `A_K → A_K → A`, `x ↦ x + a`, which is the morphism
`lift (fst A _) (snd A _ ≫ a) ≫ μ`; the base change of `c` itself is its pull-back along the
projection `fst A _ : A_K → A`. Pic is written additively. The fields `k` and `K` lie in a
common universe, so that `Spec K` and `A` are objects of the same category.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, v2.00 (2008), Ch. I, §8.
* [B] E. Bombieri, *The Mordell conjecture revisited*, Ann. SNS Pisa (4) 17 (1990), Sec. 2.
-/

namespace Faltings.AbelianVariety

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

variable {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  [IsAbelianVariety k A] {K : Type u} [Field K] [Algebra k K]

/-- For an abelian variety `A` over `k`, a class `c ∈ Pic(A)` and a point `a ∈ A(K)` over a
field extension `K/k`, the class `φ_c(a) = τ_a^* c - c` in `Pic(A_K)`, where
`A_K = A ⊗ Spec K` is the base change, `τ_a` is translation by `a`, and `c` on the right is
the pull-back of `c` to `A_K`. -/
@[expose, faltings "def_nt_phi_map"]
public noncomputable def phiMap (c : Stacks.Picard.ofScheme A.left)
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    Stacks.Picard.ofScheme (A ⊗ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).left :=
  Stacks.Picard.schemePullbackClass (lift (fst _ _) (snd _ _ ≫ a) ≫ μ).left c -
    Stacks.Picard.schemePullbackClass (fst A _).left c

end Faltings.AbelianVariety
