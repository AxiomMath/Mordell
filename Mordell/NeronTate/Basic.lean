module

public import Mathlib
public import Mordell.Attr
public import Mordell.Height.Class.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyProjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Néron–Tate heights

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, `k = k̄` is an
algebraic closure of a number field), and let `c ∈ Pic(A) ⊗ ℚ`. A function `f : A(k) → ℝ` is a
*Néron–Tate height of `c`* if

* `f - h` is bounded for some height `h` associated to `c` (`Faltings.IsHeightOfClass`), and
* `f x = ½ b(x, x) + ℓ(x)` for a symmetric biadditive form `b` and an additive function `ℓ` on
  the group `A(k)`.

Since two heights associated to `c` differ by a bounded function, the first clause does not
depend on the choice of `h`, and a Néron–Tate height of `c` is unique when it exists (a bounded
quadratic-plus-linear function vanishes).

## Main definitions

* `Faltings.IsNeronTateHeight A c f`: `f` is a Néron–Tate height of `c ∈ Pic(A) ⊗ ℚ`.

## Implementation notes

A `k`-point of `A` is a section `p : Spec k ⟶ A` of the structure morphism, the points on which
`Faltings.IsHeightOfClass` evaluates heights. The group law of `A(k)` is that of the group
`Over.mk (𝟙 (Spec k)) ⟶ A` of morphisms into the group object `A`, written additively through
`Additive`; a section `p` is the morphism `Over.homMk p`. The biadditive form is curried,
`b : A(k) →+ A(k) →+ ℝ`, and symmetry is the pointwise identity `b x y = b y x`.

`Pic(A) ⊗ ℚ` is `ℚ ⊗[ℤ] Pic(A)` as elsewhere in the theory of abelian varieties here, and is
passed to `Faltings.IsHeightOfClass`, which takes `Pic(A) ⊗[ℤ] ℚ`, through `TensorProduct.comm`.
That `A` is smooth and projective (Stacks, Tags 0BFC and 0BFA), which `Faltings.IsHeightOfClass`
requires, is supplied from `AlgebraicGeometry.smooth_of_isAbelianVariety` and
`AlgebraicGeometry.isProjective_of_isAbelianVariety`.

The base field is any algebraic extension `k / ℚ`, the generality of `Faltings.IsHeightOfClass`.
For an abelian variety over a number field `k₀`, the source's `A(k̄₀)` and `Pic(A) ⊗ ℚ` are those
of the base change of `A` to an algebraic closure `k = k̄₀`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- A function `f : A(k) → ℝ` on the points of an abelian variety `A` over a field `k` algebraic
over `ℚ` is a **Néron–Tate height** of `c ∈ Pic(A) ⊗ ℚ` if `f - h` is bounded for a height `h`
associated to `c`, and `f x = ½ b(x, x) + ℓ(x)` for a symmetric biadditive form `b` and an
additive function `ℓ` on the group `A(k)`. -/
@[faltings "def_nt_neron_tate_height"]
def IsNeronTateHeight {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (f : {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ) : Prop :=
  letI : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  letI : Smooth A.hom := smooth_of_isAbelianVariety k A
  (∃ h, IsHeightOfClass A.hom (TensorProduct.comm ℤ ℚ _ c) h ∧ ∃ C : ℝ, ∀ x, |f x - h x| ≤ C) ∧
  ∃ b : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →+
      Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →+ ℝ,
    (∀ x y, b x y = b y x) ∧ ∃ ℓ : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →+ ℝ,
      ∀ p, f p = b (.ofMul (Over.homMk p.1 p.2)) (.ofMul (Over.homMk p.1 p.2)) / 2 +
        ℓ (.ofMul (Over.homMk p.1 p.2))

end Faltings
