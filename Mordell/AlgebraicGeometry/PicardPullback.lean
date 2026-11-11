module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Pull-back of Picard classes of schemes

For a morphism of schemes `φ : X ⟶ Y`, the pull-back `φ^* : Pic(Y) → Pic(X)` is
`Stacks.Picard.schemePullbackClassHom φ`. This file computes it on classes: the pull-back of the
class of an invertible module `M` is the class of `φ^* M`, and the pull-back of an arbitrary class
is the pull-back class of its chosen representative. It also records functoriality for morphisms
in `Over S`, read on the underlying schemes.

## Main results

* `Faltings.schemePullbackClassHom_picardClass`: `φ^* [M] = [φ^* M]`.
* `Faltings.schemePullbackClassHom_eq_pullbackPicardClass`: `φ^* x` is the pull-back class of the
  chosen representative of `x`.
* `Faltings.schemePullbackClassHom_comp_left`: `f^* (g^* x) = (f ≫ g)^* x` for `f`, `g` in
  `Over S`.
* `Faltings.schemePullbackClass_zsmul`: `φ^* (a • x) = a • φ^* x` for `a : ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- Pull-back of Picard classes along `φ` is the class of the pulled-back module. -/
public lemma schemePullbackClassHom_picardClass {X Y : Scheme.{u}} (φ : X ⟶ Y) (M : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M) :
    Stacks.Picard.schemePullbackClassHom φ (Y.picardClass M hM) =
      X.picardClass ((Scheme.Modules.pullback φ).obj M) inferInstance := by
  have h1 : Stacks.Picard.schemePullbackClassHom φ (Y.picardClass M hM) =
      Stacks.SheafOfModules.pullbackPicardClass φ M hM :=
    Stacks.Picard.pullbackClass_classOf _ _ _
  rw [h1]
  refine (X.picardClass_eq_iff _ _ _ _).2 ⟨?_⟩
  exact ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    φ.toLRSHom.toShHom).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction φ)).app _

/-- Pull-back of classes along a morphism of schemes, evaluated on `x`, is the pull-back class
of the chosen representative of `x`. -/
public lemma schemePullbackClassHom_eq_pullbackPicardClass {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (x : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClassHom φ x =
      Stacks.SheafOfModules.pullbackPicardClass φ
        (Stacks.Picard.picardRepresentative Y.toRingedSpace x).obj
        (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property := by
  conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x]
  exact Stacks.Picard.pullbackClass_classOf _ _ _

/-- Pull-back of Picard classes along a composite in `Over S`, read on the underlying schemes:
`f^* (g^* x) = (f ≫ g)^* x`. -/
public lemma schemePullbackClassHom_comp_left {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : Stacks.Picard.ofScheme Z.left) :
    Stacks.Picard.schemePullbackClassHom f.left (Stacks.Picard.schemePullbackClassHom g.left x) =
      Stacks.Picard.schemePullbackClassHom (f ≫ g).left x :=
  Stacks.Picard.schemePullbackClass_comp f.left g.left x

/-- Pull-back on Picard groups commutes with integer multiples. -/
public theorem schemePullbackClass_zsmul {Y Z : Scheme.{u}} (b : Y ⟶ Z) (a : ℤ)
    (x : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass b (a • x) = a • Stacks.Picard.schemePullbackClass b x :=
  map_zsmul (Stacks.Picard.schemePullbackClassHom b) a x

end Faltings
