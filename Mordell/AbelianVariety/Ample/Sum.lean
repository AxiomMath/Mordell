module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Scheme

/-!
# Sums of ample classes on an abelian variety

Let `A` be an abelian variety over a field `k`. Ampleness of an invertible sheaf depends only on
its isomorphism class (`AlgebraicGeometry.Scheme.Modules.isAmple_of_iso`), so it is a property of
classes in the Picard group `Pic(A)`. The ample classes are closed under the group law: if `c`
and `c'` are ample, so is `c + c'`.

## Main results

* `Faltings.isAmple_of_schemeClassOf_eq_mul`: on an abelian variety, an invertible sheaf whose
  class in `Pic(A)` is the product of the classes of two ample invertible sheaves is ample.

## Implementation notes

`Stacks.SheafPicardGroup.schemePicardGroup` is a multiplicative group, whose law is induced by the
tensor product (`Stacks.SheafPicardGroup.schemeClassOf_tensorSheaf`). The sum `c + c'` of the
source is therefore written `c * c'` here. A class `c` is ample when one, equivalently every,
invertible sheaf representing it is ample; every class has a representative, so quantifying
over representatives `L`, `L'` of `c`, `c'` and any representative `M` of `c * c'` states the
assertion for all pairs of classes. Nothing about abelian varieties is used in the proof:
the tensor product of two ample invertible sheaves on any scheme is ample (Stacks Tag 0890,
`AlgebraicGeometry.Scheme.Modules.isAmple_tensor_of_power_sections_cover`), and ampleness
passes along the isomorphism `M ≅ L ⊗ L'` given by the equality of classes.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Proposition 6.6(a).
* [MumAV] D. Mumford, *Abelian Varieties*, §6, Application 1.
-/

@[expose] public section

namespace Faltings

open AlgebraicGeometry CategoryTheory Stacks.SheafPicardGroup

/-- The tensor product of two ample invertible sheaves is ample (Stacks Tag 0890). -/
private lemma isAmple_tensorProductModule (X : Scheme) (L L' : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L']
    (hL : Scheme.Modules.IsAmple X L) (hL' : Scheme.Modules.IsAmple X L') :
    Scheme.Modules.IsAmple X (Scheme.Modules.tensorProductModule X L L') :=
  Scheme.Modules.isAmple_tensor_of_power_sections_cover X L L' hL fun x =>
    let ⟨n, hn, s, hs, _⟩ := hL'.2 x; ⟨n, hn, s, hs⟩

/-- On an abelian variety `A` over a field `k`, the sum of two ample classes in the Picard group
is ample: if `L` and `L'` are ample invertible sheaves on `A` and the invertible sheaf `M`
represents the class `[L] * [L']` in `Stacks.SheafPicardGroup.schemePicardGroup A.left`, then
`M` is ample. -/
@[faltings "lem_nt_ample_facts"]
theorem isAmple_of_schemeClassOf_eq_mul (k : Type*) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (L L' M : A.left.Modules) [Stacks.Ample.IsInvertibleModule A.left L]
    [Stacks.Ample.IsInvertibleModule A.left L'] [Stacks.Ample.IsInvertibleModule A.left M]
    (hL : Scheme.Modules.IsAmple A.left L) (hL' : Scheme.Modules.IsAmple A.left L')
    (hM : schemeClassOf A.left M = schemeClassOf A.left L * schemeClassOf A.left L') :
    Scheme.Modules.IsAmple A.left M := by
  have e : Nonempty (Scheme.Modules.tensorProductModule A.left L L' ≅ M) := by
    rw [← schemeClassOf_eq_schemeClassOf_iff, hM]
    exact @schemeClassOf_tensorSheaf A.left L L' _ _
      (inferInstance : Stacks.Ample.IsInvertibleModule A.left
        (Scheme.Modules.tensorProductModule A.left L L'))
  exact Scheme.Modules.isAmple_of_iso e.some (isAmple_tensorProductModule A.left L L' hL hL')

end Faltings
