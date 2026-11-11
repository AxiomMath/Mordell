module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.PicardPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Ampleness is preserved by automorphisms

Let `A` be an abelian variety over a field `k` and `σ` an automorphism of the underlying scheme
of `A` (not necessarily over `k`, nor compatible with the group law). Ampleness of an invertible
sheaf depends only on its isomorphism class (`AlgebraicGeometry.Scheme.Modules.isAmple_of_iso`),
so it is a property of classes in the Picard group `Pic(A)`. If `c ∈ Pic(A)` is ample, so is its
pull-back `σ^* c`: an invertible sheaf representing `σ^* [L]` is isomorphic to `σ^* L`, and the
pull-back of an ample sheaf along an isomorphism of schemes is ample
(`AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso`).

## Main results

* `Faltings.isAmple_of_picardClass_eq_schemePullbackClass`: on an abelian variety `A`, an
  invertible sheaf whose class in `Pic(A)` is the pull-back along an automorphism `σ` of the
  class of an ample invertible sheaf is ample.

## Implementation notes

The Picard group is `Stacks.Picard.ofScheme A.left`, the class of an invertible sheaf `L` is
`Stacks.SheafOfModules.picardClass`, and the pull-back of classes is
`Stacks.Picard.schemePullbackClass`. A class `c` is ample when one, equivalently every,
invertible sheaf representing it is ample; every class has a representative, so quantifying
over a representative `L` of `c` and any representative `M` of `σ^* c` states the assertion for
every class.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I.
* [Stacks] The Stacks project, Tag 01PS.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- On an abelian variety `A` over a field `k`, the pull-back of an ample class of `Pic(A)` along
an automorphism `σ` of the scheme `A` is ample: if `L` is an ample invertible sheaf on `A` and the
invertible sheaf `M` represents `σ^* [L]`, then `M` is ample. -/
@[faltings "lem_nt_ample_pullback_automorphism"]
theorem isAmple_of_picardClass_eq_schemePullbackClass (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (σ : A.left ≅ A.left) (L M : A.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.left.toRingedSpace.presheaf
      (structureSheafRing A.left.toRingedSpace).property M]
    (hL : Scheme.Modules.IsAmple A.left L)
    (hM : Stacks.SheafOfModules.picardClass A.left.presheaf
        (Stacks.RingedSpace.structureIsSheaf A.left.toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M ‹_›) =
      Stacks.Picard.schemePullbackClass σ.hom
        (Stacks.SheafOfModules.picardClass A.left.presheaf
          (Stacks.RingedSpace.structureIsSheaf A.left.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L ‹_›))) :
    Scheme.Modules.IsAmple A.left M := by
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (hM.trans (schemePullbackClassHom_picardClass σ.hom L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L ‹_›)))
  exact Scheme.Modules.isAmple_of_iso e.symm (Scheme.Modules.isAmple_pullback_of_isIso σ.hom L hL)

end Faltings
