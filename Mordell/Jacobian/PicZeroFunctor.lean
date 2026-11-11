module
public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree

/-!
# The relative Picard functor of degree zero of a curve

Let `C` be a smooth projective curve over a field `k`, with structure morphism
`f : C ⟶ Spec k`. For a `k`-scheme `T` write `q : C ×_k T ⟶ T` for the projection. The group
`P⁰_C(T)` consists of the classes of invertible sheaves on `C ×_k T` whose degree on every
fibre `C_t`, `t ∈ T`, is zero, modulo the classes `q^* Pic(T)` pulled back from the base.
Pull-back along `C ×_k T' ⟶ C ×_k T` for a `k`-morphism `T' ⟶ T` preserves fibrewise degree
zero (the degree is natural in the base) and sends `q^* Pic(T)` into `q'^* Pic(T')`, so
`T ↦ P⁰_C(T)` is a contravariant functor from `k`-schemes to abelian groups.

For a field `K ⊇ k` the base `Spec K` has trivial Picard group, so `P⁰_C(Spec K)` is the group
of degree-zero classes in `Pic(C_K)`.

## Main definitions

* `Faltings.relativePicZeroFunctor k f`: the functor `P⁰_C` on `k`-schemes, valued in abelian
  groups.

## Implementation notes

The `k`-schemes are the category `Over (Spec k)`, and `C ×_k T` is the pull-back of `f` along
the structure morphism of `T`. The Picard group of a scheme is taken in its small model
`Stacks.Picard.smallOfScheme`, so the functor takes values in abelian groups of the universe of
the schemes, the same universe as the functor of points `T ↦ (T ⟶ J)` of a `k`-scheme `J`.
The degree on the fibres is `Stacks.RigidifiedPicard.degree`, the function on `T` recording the
degree of a class on each fibre of `C ×_k T ⟶ T`; it applies because the fibres of `f` have
dimension at most one. The subgroup divided out is `q^* Pic(T)` intersected with the classes of
fibrewise degree zero; since a class pulled back from `T` is trivial on every fibre, this is
`q^* Pic(T)` itself.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 1.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [Stacks Project, Tag 0BA0]
-/

open CategoryTheory AlgebraicGeometry Opposite Stacks.Picard Stacks.RigidifiedPicard

universe u

namespace Faltings

/-- **The relative Picard functor of degree zero `P⁰_C`** of a smooth projective curve
`f : C ⟶ Spec k`. Its value at a `k`-scheme `T` is the group of classes of invertible sheaves on
`C ×_k T` of degree zero on every fibre of the projection `q : C ×_k T ⟶ T`, modulo
`q^* Pic(T)`; a `k`-morphism `T' ⟶ T` acts by pull-back along `C ×_k T' ⟶ C ×_k T`. -/
@[expose, faltings "def_nt_relative_pic0_functor"]
public noncomputable def relativePicZeroFunctor (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  have hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)
  let Z (T : Over (Spec (.of k))) := (degree f hdim T).ker
  let N (T : Over (Spec (.of k))) : AddSubgroup (Z T) :=
    (smallSchemePullbackClassHom (bcProj f T)).range.addSubgroupOf (Z T)
  let φ {T U : Over (Spec (.of k))} (g : T ⟶ U) : Z U →+ Z T :=
    ((smallSchemePullbackClassHom (bcMap f g)).comp (Z U).subtype).codRestrict _
      fun x => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
          degree_smallSchemePullbackClassHom_bcMap, (AddMonoidHom.mem_ker.1 x.2)]
        rfl
  have hφ {T U : Over (Spec (.of k))} (g : T ⟶ U) : N U ≤ (N T).comap (φ g) := by
    rintro x ⟨y, hy⟩
    refine ⟨smallSchemePullbackClassHom g.left y, ?_⟩
    show _ = smallSchemePullbackClassHom (bcMap f g) (x : _)
    rw [show (x : smallOfScheme (bc f U)) = _ from hy.symm, smallSchemePullbackClassHom_comp,
      smallSchemePullbackClassHom_comp, bcMap_snd]
  { obj T := AddCommGrpCat.of (Z T.unop ⧸ N T.unop)
    map g := AddCommGrpCat.ofHom (QuotientAddGroup.map _ _ (φ g.unop) (hφ g.unop))
    map_id T := by
      ext x
      exact congrArg (QuotientAddGroup.mk' (N T.unop)) <| Subtype.ext <|
        show smallSchemePullbackClassHom (bcMap f (𝟙 T.unop)) (x : _) = x by
          rw [bcMap_id, smallSchemePullbackClassHom_id]
    map_comp g h := by
      ext x
      exact congrArg (QuotientAddGroup.mk' _) <| Subtype.ext <|
        show smallSchemePullbackClassHom (bcMap f (h.unop ≫ g.unop)) (x : _) =
          smallSchemePullbackClassHom (bcMap f h.unop)
            (smallSchemePullbackClassHom (bcMap f g.unop) (x : _)) by
          rw [bcMap_comp, smallSchemePullbackClassHom_comp] }

end Faltings
