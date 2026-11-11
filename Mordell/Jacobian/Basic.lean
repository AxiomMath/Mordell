module
public import Mordell.Jacobian.PicZeroFunctor

/-!
# The Jacobian of a curve

Let `C` be a smooth projective curve over a field `k`, with structure morphism `f : C ⟶ Spec k`,
and let `P⁰_C` be its relative Picard functor of degree zero on `k`-schemes. A *Jacobian* of `C` is
an abelian variety `J` over `k` together with a morphism of group-valued functors `ι : P⁰_C ⟶ J`,
where `J` is regarded as its functor of points `T ↦ J(T) = Hom_k(T, J)`, a group under the group
law of `J`, such that `ι(T) : P⁰_C(T) → J(T)` is bijective for every `k`-scheme `T` with
`C(T) ≠ ∅`.
In [Bombieri, Section 5] the abelian variety `J` is denoted `A = Pic₀(C)`.

## Main definitions

* `Faltings.Jacobian k f`: the type of Jacobians `(J, ι)` of the curve `f : C ⟶ Spec k`.

## Implementation notes

The `k`-schemes are the category `Over (Spec k)`, and `J(T)` is the set of morphisms `T ⟶ J` over
`k`, that is the functor of points `yoneda.obj J`; its group structure is
`CategoryTheory.Hom.group`, written multiplicatively, induced by the group object `J`. The morphism
`ι` is given as a natural transformation of the underlying set-valued functors (`P⁰_C` composed
with the forgetful functor from abelian groups) together with the field `Jacobian.map_add`, which
says each `ι(T)` sends sums in `P⁰_C(T)` to products in `J(T)`; together they are a morphism of
group-valued functors, as in [MilAV]. The condition `C(T) ≠ ∅` is the existence of a `k`-morphism
`T ⟶ C`, and bijectivity of `ι(T)` is `IsIso` in the category of types.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 1.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Faltings

attribute [local instance] Hom.group

/-- A **Jacobian** of a smooth projective curve `f : C ⟶ Spec k` is a pair `(J, ι)` of an
abelian variety `J` over `k` and a morphism of group-valued functors `ι : P⁰_C ⟶ J(-)` from
the relative Picard functor of degree zero to the functor of points of `J`, such that
`ι(T) : P⁰_C(T) → J(T)` is bijective for every `k`-scheme `T` with `C(T) ≠ ∅`. -/
@[faltings "def_nt_jacobian"]
public structure Jacobian (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f] where
  /-- The abelian variety `J` over `k`. -/
  J : Over (Spec (.of k))
  /-- The group law of `J`. -/
  [grpObj : GrpObj J]
  /-- `J` is an abelian variety over `k`. -/
  isAbelianVariety : IsAbelianVariety k J
  /-- The underlying morphism of set-valued functors of `ι : P⁰_C ⟶ J(-)`. -/
  ι : relativePicZeroFunctor k f ⋙ forget AddCommGrpCat ⟶ yoneda.obj J
  /-- `ι(T)` is a group homomorphism: it sends sums in `P⁰_C(T)` to products in `J(T)`. -/
  map_add : ∀ (T : (Over (Spec (.of k)))ᵒᵖ) (x y : (relativePicZeroFunctor k f).obj T),
    ι.app T (x + y) =
      @HMul.hMul (T.unop ⟶ J) (T.unop ⟶ J) (T.unop ⟶ J) _ (ι.app T x) (ι.app T y)
  /-- `ι(T)` is bijective whenever `C(T) ≠ ∅`. -/
  isIso_app : ∀ T : Over (Spec (.of k)), Nonempty (T ⟶ Over.mk f) → IsIso (ι.app (op T))

attribute [instance] Jacobian.grpObj

end Faltings
