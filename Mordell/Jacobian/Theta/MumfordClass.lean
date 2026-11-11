module

public import Mathlib
public import Mordell.Attr
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Jacobian.Theta.Basic
public import Mordell.Jacobian.AbelJacobi
public import Mordell.CurveProduct.Diagonal
public import Mordell.Jacobian.Theta.PrimeDivisor
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import Mordell.Jacobian.Theta.PullbackTranslate
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Variety.RationalPointsHomExt
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection

/-!
# Pull-back of the Mumford class, base point

Let `k` be algebraically closed and let `(C, P₀)` be a curve over `k` with a rational point
`P₀ ∈ C(k)`, of genus `g ≥ 1`. Let `(J, ι)` be a Jacobian of `C`, `j = j_{P₀}` the Abel–Jacobi
map and `Θ = Θ_{P₀} ⊆ J` the theta divisor, with class `θ = cl(Θ) = [𝒪_J(Θ)] ∈ Pic(J)`. On
`J × J` let `s₁, s₂` be the projections and `s₁₂(x, y) = x + y` the group law. Then on `C × C`
`(j × j)^* (s₁₂^* θ - s₁^* θ - s₂^* θ) = -cl(Δ - P₀ × C - C × P₀)`,
where `Δ` is the diagonal. Equivalently, `(j × j)^*` of Mumford's class
`L'(θ) = s₁₂^* θ - s₁^* θ - s₂^* θ` is minus the canonical divisorial correspondence.

## Main results

* `Faltings.schemePullbackClassHom_tensorHom_mumfordClass_eq_neg_vojtaClass`: the identity above,
  with `cl(Δ - P₀ × C - C × P₀)` the class
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass X 0 0 1`.

## Implementation notes

The point `P₀` is recorded as the degree-one divisor of the curve: `X.P = P₀`, the single
closed point `P₀` with multiplicity one. Over an algebraically closed field every closed point
is rational, so this is the source's hypothesis `P₀ ∈ C(k)`.

The class `θ` is `Stacks.Divisors.picardClass D` for a reduced effective Cartier divisor `D`
on `J` (`D.radical = D`) whose support is `Θ`, as in `Faltings.deltaClass`. Such a `D` is the
vanishing ideal of `Θ`, the reduced closed subscheme on `Θ`, so `θ = cl(Θ)` does not depend on
the choice of `D`. The products `C × C` and `J × J` are the monoidal products in schemes over
`Spec k`, whose underlying schemes are the fibre products over `k`, and `j × j` is
`j ⊗ₘ j`; `s₁, s₂` are the cartesian projections and `s₁₂` is the multiplication `μ` of `J`.
The Picard groups are written additively.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Summary 6.11.
* [H] Sec. 3, proof of Mumford's inequality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj Opposite

universe u

namespace Faltings

open Stacks.Picard in
/-- Pull-back of classes along a composite, in the additive form. -/
private lemma pb_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ofScheme Z) :
    schemePullbackClassHom f (schemePullbackClassHom g x) = schemePullbackClassHom (f ≫ g) x :=
  schemePullbackClass_comp f g x

/-- The pull-back of a class along a morphism factoring through the spectrum of a field
vanishes, in the additive form. -/
private lemma pb_comp_spec_field {K : Type u} [Field K] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Spec (CommRingCat.of K) ⟶ Y)
    (x : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClassHom (p ≫ q) x = 0 :=
  Faltings.AbelianVariety.schemePullbackClass_comp_spec_field p q x

/-- The point `Spec k` as a `k`-scheme, as in `Faltings.IsAbelJacobiMap` for `K = k`. -/
local notation:max "ptK " k:max => fieldExtensionPoint k k

section Cube

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  (θ : Stacks.Picard.ofScheme A.left)

open Stacks.Picard

/-- The pull-back of a class along the constant morphism `1` vanishes. -/
private lemma pb_one {B : Over (Spec (.of k))} :
    schemePullbackClassHom (1 : B ⟶ A).left θ = 0 := by
  change schemePullbackClass ((toUnit B).left ≫ η[A].left) θ = 0
  exact Faltings.AbelianVariety.schemePullbackClass_comp_spec_field _ _ _

/-- The Mumford form `(u, v) ↦ (u v)^* θ - u^* θ - v^* θ` changes sign when `u` is inverted:
the theorem of the cube for `(u⁻¹, u, v)`. -/
private lemma mumford_inv_left [IsAbelianVariety k A] [IsCommMonObj A] {B : Over (Spec (.of k))}
    (u v : B ⟶ A) :
    schemePullbackClassHom (u * v).left θ - schemePullbackClassHom u.left θ -
        schemePullbackClassHom v.left θ =
      -(schemePullbackClassHom (v * u⁻¹).left θ - schemePullbackClassHom (u⁻¹).left θ -
        schemePullbackClassHom v.left θ) := by
  have h := Faltings.AbelianVariety.schemePullbackClass_cube A θ (u⁻¹) u v
  rw [inv_mul_cancel, _root_.one_mul, mul_comm u⁻¹ v] at h
  have h1 := pb_one A θ (B := B)
  change schemePullbackClass _ θ + schemePullbackClass _ θ + schemePullbackClass _ θ +
    schemePullbackClass _ θ = schemePullbackClass _ θ + schemePullbackClass _ θ +
    schemePullbackClass _ θ at h
  change schemePullbackClass _ θ = 0 at h1
  change schemePullbackClass _ θ - schemePullbackClass _ θ - schemePullbackClass _ θ =
    -(schemePullbackClass _ θ - schemePullbackClass _ θ - schemePullbackClass _ θ)
  rw [h1, zero_add] at h
  rw [← sub_eq_zero, ← sub_eq_zero.2 h.symm]
  abel

/-- The Mumford form is natural in the source. -/
private lemma mumford_comp {B B' : Over (Spec (.of k))} (h : B' ⟶ B) (u v : B ⟶ A) :
    schemePullbackClassHom h.left (schemePullbackClassHom (u * v).left θ -
        schemePullbackClassHom u.left θ - schemePullbackClassHom v.left θ) =
      schemePullbackClassHom ((h ≫ u) * (h ≫ v)).left θ -
        schemePullbackClassHom (h ≫ u).left θ - schemePullbackClassHom (h ≫ v).left θ := by
  rw [← MonObj.comp_mul, map_sub, map_sub, pb_comp, pb_comp, pb_comp]
  rfl

/-- The Mumford form is symmetric. -/
private lemma mumford_comm [IsCommMonObj A] {B : Over (Spec (.of k))} (u v : B ⟶ A) :
    schemePullbackClassHom (u * v).left θ - schemePullbackClassHom u.left θ -
        schemePullbackClassHom v.left θ =
      schemePullbackClassHom (v * u).left θ - schemePullbackClassHom v.left θ -
        schemePullbackClassHom u.left θ := by
  rw [mul_comm u v]
  abel

/-- The Mumford form of `(f ≫ j, f ≫ w)` for `w` with `w^* θ = 0` is
`-f^*((w j⁻¹)^* θ - (j⁻¹)^* θ)`. -/
private lemma mumford_comp_inv [IsAbelianVariety k A] [IsCommMonObj A]
    {B C : Over (Spec (.of k))} (f : B ⟶ C) (j w : C ⟶ A)
    (hw : schemePullbackClassHom w.left θ = 0) :
    schemePullbackClassHom ((f ≫ j) * (f ≫ w)).left θ - schemePullbackClassHom (f ≫ j).left θ -
        schemePullbackClassHom (f ≫ w).left θ =
      -schemePullbackClassHom f.left (schemePullbackClassHom (w * j⁻¹).left θ -
        schemePullbackClassHom (j⁻¹).left θ) := by
  rw [← mumford_comp, mumford_inv_left A θ j w, mul_comm w, hw, sub_zero, map_neg]

end Cube

/-- Classes of equal elements of a subgroup agree in a quotient of it. -/
private lemma mk_subtype_congr {G : Type*} [AddCommGroup G] {K : AddSubgroup G} (N : AddSubgroup K)
    {z z' : G} (e : z = z') (h : z ∈ K) (h' : z' ∈ K) :
    (QuotientAddGroup.mk (⟨z, h⟩ : K) : K ⧸ N) = QuotientAddGroup.mk ⟨z', h'⟩ := by
  subst e
  rfl

section Divisors

open Stacks.Picard

/-- The class of the image of a closed immersion `i` pulls back along an isomorphism `φ` to the
class of the image of the lift `i'` of `i` through `φ`. -/
private lemma pb_picardClass_ker_of_isIso {Y Y' Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (i' : Z ⟶ Y') (φ : Y' ⟶ Y) [IsIso φ] (h : i' ≫ φ = i)
    [Stacks.Divisors.IsEffectiveCartierDivisor (Scheme.Hom.ker i)]
    [Stacks.Divisors.IsEffectiveCartierDivisor (Scheme.Hom.ker i')] :
    schemePullbackClassHom φ (Stacks.Divisors.picardClass (Scheme.Hom.ker i)) =
      Stacks.Divisors.picardClass (Scheme.Hom.ker i') := by
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor (Scheme.Hom.ker i) := inferInstance
  have : Stacks.Divisors.IsPullbackDefined φ (Scheme.Hom.ker i) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hE
  have hsq : IsPullback i' (𝟙 _) φ i := IsPullback.of_vert_isIso ⟨by rw [h, Category.id_comp]⟩
  change schemePullbackClass φ _ = _
  rw [Stacks.Divisors.schemePullbackClass_picardClass]
  apply Stacks.Divisors.picardClass_congr
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hsq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

end Divisors

section Seesaw

variable {k : Type u} [Field k]

open Stacks.Picard Stacks.RigidifiedPicard

/-- `Spec k ⟶ Spec k` induced by `algebraMap k k` is the identity. -/
private lemma specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- `C ×_k Spec k ⟶ C` is an isomorphism. -/
private lemma isIso_fst_ptK {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsIso (pullback.fst f (ptK k).hom) := by
  have : IsIso (ptK k).hom := by
    rw [show (ptK k).hom = 𝟙 _ from specMap_algebraMap_self]
    exact IsIso.id _
  infer_instance

/-- The swap `C ×_k C ≅ C ×_k C`. -/
private noncomputable abbrev swapCC (X : CurveWithDegreeOneDivisor k) :
    pullback X.f X.f ⟶ pullback X.f X.f :=
  (lift (snd (Over.mk X.f) (Over.mk X.f)) (fst (Over.mk X.f) (Over.mk X.f))).left

/-- The swap exchanges the projections. -/
private lemma swapCC_fst (X : CurveWithDegreeOneDivisor k) :
    swapCC X ≫ pullback.fst X.f X.f = pullback.snd X.f X.f :=
  congrArg Over.Hom.left (lift_fst _ _)

/-- The swap exchanges the projections. -/
private lemma swapCC_snd (X : CurveWithDegreeOneDivisor k) :
    swapCC X ≫ pullback.snd X.f X.f = pullback.fst X.f X.f :=
  congrArg Over.Hom.left (lift_snd _ _)

/-- **The seesaw on `C × C`.** A class on `C ×_k C` that is symmetric and restricts to zero on
every fibre `C × {y}` over a `k`-point `y` vanishes. Its classifying map `C ⟶ J` is constant,
so by injectivity of `ι(C)` it is pulled back from the second factor; by symmetry also from the
first, and restricting to one fibre shows the class on the factor is zero. -/
private lemma eq_zero_of_symm_of_fibres [IsAlgClosed k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (y₀ : ptK k ⟶ Over.mk X.f)
    (x : Stacks.Picard.ofScheme (pullback X.f X.f))
    (hsym : schemePullbackClassHom (swapCC X) x = x)
    (hfib : ∀ y : ptK k ⟶ Over.mk X.f, schemePullbackClassHom (bcMap X.f y) x = 0) :
    x = 0 := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  set T : Over (Spec (.of k)) := Over.mk X.f
  set xs : smallOfScheme (bc X.f T) := (smallEquiv.{u} (bc X.f T)).symm x with hxs
  -- the restrictions of `xs` to the fibres over `k`-points vanish
  have hfibs : ∀ y : ptK k ⟶ T, smallSchemePullbackClassHom (bcMap X.f y) xs = 0 := by
    intro y
    apply (smallEquiv.{u} _).injective
    rw [smallEquiv_smallSchemePullbackClassHom, hxs, AddEquiv.apply_symm_apply, map_zero]
    exact hfib y
  -- the same holds over the points `𝟙_ ⟶ C`, through `𝟙_ ⟶ ptK k`
  have hfibs' : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ T,
      smallSchemePullbackClassHom (bcMap X.f p) xs = 0 := by
    intro p
    have hp : p = Over.homMk (U := 𝟙_ (Over (Spec (.of k)))) (V := ptK k) (𝟙 _)
        (by simp) ≫ (toUnit (ptK k) ≫ p) := by
      rw [← Category.assoc, toUnit_unique (_ ≫ toUnit (ptK k)) (𝟙 _), Category.id_comp]
    rw [hp, bcMap_comp, ← smallSchemePullbackClassHom_comp, hfibs, map_zero]
  -- `xs` has degree zero on every fibre
  have hdeg : degree X.f hdim T xs = 0 := by
    have hloc : IsLocallyConstant (degree X.f hdim T xs) :=
      isLocallyConstant_relativeInvertibleDegreeHom (bcProj X.f T)
        ⟨inferInstance, inferInstance, inferInstance⟩
        (topologicalKrullDim_fiber_bcProj_le X.f hdim T)
        (smallEquiv _ xs)
    obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
    have h0 : degree X.f hdim T xs (y₀.left a) = 0 := by
      have := congrFun (degree_smallSchemePullbackClassHom_bcMap X.f hdim y₀ xs) a
      rw [hfibs y₀, map_zero] at this
      exact this.symm
    have hpre : _root_.IsPreconnected (Set.univ : Set X.C) :=
      (IrreducibleSpace.isIrreducible_univ X.C).isPreirreducible.isPreconnected
    funext t
    rw [hloc.apply_eq_of_isPreconnected hpre trivial trivial (y := y₀.left a), h0]
    rfl
  -- its class in `P⁰_C(C)` has trivial image under `ι(C)`
  let cls : (relativePicZeroFunctor k X.f).obj (op T) :=
    QuotientAddGroup.mk (⟨xs, hdeg⟩ : (degree X.f hdim T).ker)
  have hι0 : (A.ι.app (op T) cls : T ⟶ A.J) = A.ι.app (op T) 0 := by
    have := A.isAbelianVariety
    have : LocallyOfFiniteType T.hom := (inferInstance : LocallyOfFiniteType X.f)
    have : IsReduced T.left := (inferInstance : IsReduced X.C)
    refine Stacks.Varieties.overHom_ext_of_points (X := T) (Y := A.J) _ _ fun p => ?_
    have n1 := NatTrans.naturality_apply A.ι p.op cls
    have n2 := NatTrans.naturality_apply A.ι p.op 0
    have hm : (relativePicZeroFunctor k X.f).map p.op cls = 0 := by
      have e : (relativePicZeroFunctor k X.f).map p.op cls =
          QuotientAddGroup.mk (⟨smallSchemePullbackClassHom (bcMap X.f p) xs, by
            rw [AddMonoidHom.mem_ker, hfibs' p, map_zero]⟩ :
            (degree X.f hdim (𝟙_ (Over (Spec (.of k))))).ker) := rfl
      rw [e]
      exact (congrArg (QuotientAddGroup.mk (s := _)) (Subtype.ext (hfibs' p))).trans
        (QuotientAddGroup.mk_zero _)
    have hm' : (relativePicZeroFunctor k X.f ⋙ forget AddCommGrpCat).map p.op cls =
        (relativePicZeroFunctor k X.f ⋙ forget AddCommGrpCat).map p.op 0 := by
      change (relativePicZeroFunctor k X.f).map p.op cls = (relativePicZeroFunctor k X.f).map p.op 0
      rw [hm, map_zero]
    exact n1.symm.trans ((congrArg _ hm').trans n2)
  have hcls : cls = 0 := by
    have := A.isIso_app T ⟨𝟙 T⟩
    exact ((isIso_iff_bijective _).1 inferInstance).1 hι0
  -- so `x` is pulled back from the second factor
  obtain ⟨c, hc⟩ : ∃ c : Stacks.Picard.ofScheme X.C,
      schemePullbackClassHom (pullback.snd X.f X.f) c = x := by
    have hmem := (QuotientAddGroup.eq_zero_iff _).1 hcls
    obtain ⟨c, hc⟩ := AddSubgroup.mem_addSubgroupOf.1 hmem
    refine ⟨smallEquiv _ c, ?_⟩
    have := congrArg (smallEquiv.{u} (bc X.f T)) hc
    rw [smallEquiv_smallSchemePullbackClassHom] at this
    exact this.trans (AddEquiv.apply_symm_apply _ _)
  -- and, by symmetry, from the first factor
  have hc' : schemePullbackClassHom (pullback.fst X.f X.f) c = x := by
    rw [← hsym, ← hc, pb_comp, swapCC_snd]
  -- restricting to the fibre over `y₀` shows `c = 0`
  have := isIso_fst_ptK X.f
  have h0 : schemePullbackClassHom (pullback.fst X.f (ptK k).hom) c = 0 := by
    rw [← hfib y₀, ← hc', pb_comp, show bcMap X.f y₀ ≫ pullback.fst X.f X.f = _ from
      bcMap_fst X.f y₀]
  have hc0 : c = 0 := by
    have := congrArg (schemePullbackClassHom (inv (pullback.fst X.f (ptK k).hom))) h0
    rw [pb_comp, IsIso.inv_hom_id, map_zero] at this
    exact (schemePullbackClass_id _ c).symm.trans this
  rw [← hc', hc0, map_zero]

end Seesaw

section Vojta

variable {k : Type u} [Field k]

open Stacks.Picard

/-- The swap of `C ×_k C` fixes `cl(Δ - P × C - C × P)`. -/
private lemma pb_swapCC_vojtaClass (X : CurveWithDegreeOneDivisor k) :
    schemePullbackClassHom (swapCC X) (X.vojtaClass 0 0 1) = X.vojtaClass 0 0 1 := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have := (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  have hss : swapCC X ≫ swapCC X = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, swapCC_fst, swapCC_snd, Category.id_comp]
    · rw [Category.assoc, swapCC_snd, swapCC_fst, Category.id_comp]
  have : IsIso (swapCC X) := ⟨⟨swapCC X, hss, hss⟩⟩
  have hΔ : schemePullbackClassHom (swapCC X)
      (Stacks.Divisors.picardClass (pullback.diagonal X.f).ker) =
      Stacks.Divisors.picardClass (pullback.diagonal X.f).ker :=
    pb_picardClass_ker_of_isIso _ _ _ (by
      apply pullback.hom_ext
      · rw [Category.assoc, swapCC_fst, pullback.diagonal_snd, pullback.diagonal_fst]
      · rw [Category.assoc, swapCC_snd, pullback.diagonal_snd, pullback.diagonal_fst])
  rw [X.vojtaClass_zero_zero_one, map_sub, map_sub, hΔ, pb_comp, pb_comp, swapCC_fst, swapCC_snd]
  abel

/-- The Mumford form `s₁₂^* θ - s₁^* θ - s₂^* θ` pulled back along `j × j`, as a class on
`C ×_k C`: `(j ∘ pr₁ + j ∘ pr₂)^* θ - (j ∘ pr₁)^* θ - (j ∘ pr₂)^* θ`. -/
private noncomputable abbrev mumfordCC (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] (j : Over.mk X.f ⟶ J) (θ : Stacks.Picard.ofScheme J.left) :
    Stacks.Picard.ofScheme (pullback X.f X.f) :=
  schemePullbackClassHom (show pullback X.f X.f ⟶ J.left from
      ((fst (Over.mk X.f) (Over.mk X.f) ≫ j) * (snd (Over.mk X.f) (Over.mk X.f) ≫ j)).left) θ -
    schemePullbackClassHom (show pullback X.f X.f ⟶ J.left from
      (fst (Over.mk X.f) (Over.mk X.f) ≫ j).left) θ -
    schemePullbackClassHom (show pullback X.f X.f ⟶ J.left from
      (snd (Over.mk X.f) (Over.mk X.f) ≫ j).left) θ

/-- `(j × j)^*(s₁₂^* θ - s₁^* θ - s₂^* θ)` is the Mumford form of `(j ∘ pr₁, j ∘ pr₂)`. -/
private lemma pb_tensorHom_mumford (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] (j : Over.mk X.f ⟶ J) (θ : Stacks.Picard.ofScheme J.left) :
    schemePullbackClassHom (j ⊗ₘ j).left (schemePullbackClassHom μ[J].left θ -
        schemePullbackClassHom (fst J J).left θ - schemePullbackClassHom (snd J J).left θ) =
      mumfordCC X j θ := by
  have h := mumford_comp J θ (j ⊗ₘ j) (fst J J) (snd J J)
  rwa [show fst J J * snd J J = μ[J] by rw [Hom.mul_def, lift_fst_snd, Category.id_comp],
    tensorHom_fst, tensorHom_snd] at h

/-- The swap of `C ×_k C` fixes the Mumford form, `J` being commutative. -/
private lemma pb_swapCC_mumfordCC (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] [IsCommMonObj J] (j : Over.mk X.f ⟶ J) (θ : Stacks.Picard.ofScheme J.left) :
    schemePullbackClassHom (swapCC X) (mumfordCC X j θ) = mumfordCC X j θ := by
  have h := mumford_comp J θ (lift (snd (Over.mk X.f) (Over.mk X.f))
    (fst (Over.mk X.f) (Over.mk X.f))) (fst (Over.mk X.f) (Over.mk X.f) ≫ j)
    (snd (Over.mk X.f) (Over.mk X.f) ≫ j)
  rwa [lift_fst_assoc, lift_snd_assoc, mumford_comm J θ (snd (Over.mk X.f) (Over.mk X.f) ≫ j)
    (fst (Over.mk X.f) (Over.mk X.f) ≫ j)] at h

end Vojta

section Fibres

variable {k : Type u} [Field k]

open Stacks.Picard Stacks.RigidifiedPicard

/-- The structure morphism `C ⟶ Spec k`, as a morphism of `k`-schemes to the point. -/
private noncomputable abbrev toPt (X : CurveWithDegreeOneDivisor k) : Over.mk X.f ⟶ ptK k :=
  Over.homMk (U := Over.mk X.f) (V := ptK k) X.f (by simp [Algebra.algebraMap_self])

/-- On `C × pt` the second projection factors through the first. -/
private lemma snd_eq_fst_toPt (X : CurveWithDegreeOneDivisor k) :
    snd (Over.mk X.f) (ptK k) = fst (Over.mk X.f) (ptK k) ≫ toPt X := by
  ext
  have h1 : (ptK k).hom = 𝟙 _ := specMap_algebraMap_self
  have h2 : pullback.snd X.f (ptK k).hom ≫ (ptK k).hom = pullback.snd X.f (ptK k).hom := by
    conv_lhs => arg 2; rw [h1]
    exact Category.comp_id _
  exact h2.symm.trans pullback.condition.symm

/-- **The Mumford form on a fibre `C × {y}`.** Its restriction is `-(ψ_y^* θ - ψ_0^* θ)` pulled
back from `C`, where `ψ_y = y - j`. -/
private lemma pb_bcMap_mumfordCC (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] [IsCommMonObj J] [IsAbelianVariety k J] (j : Over.mk X.f ⟶ J)
    (θ : Stacks.Picard.ofScheme J.left) (y : ptK k ⟶ Over.mk X.f) :
    schemePullbackClassHom (bcMap X.f y) (mumfordCC X j θ) =
      -schemePullbackClassHom (pullback.fst X.f (ptK k).hom)
        (schemePullbackClassHom ((toPt X ≫ y ≫ j) * j⁻¹).left θ -
          schemePullbackClassHom (j⁻¹).left θ) := by
  have h1 := mumford_comp J θ (Over.mk X.f ◁ y) (fst (Over.mk X.f) (Over.mk X.f) ≫ j)
    (snd (Over.mk X.f) (Over.mk X.f) ≫ j)
  rw [whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, snd_eq_fst_toPt, Category.assoc] at h1
  have h0 : schemePullbackClassHom (toPt X ≫ y ≫ j).left θ = 0 :=
    Faltings.AbelianVariety.schemePullbackClass_comp_spec_field X.f (y ≫ j).left θ
  exact h1.trans (mumford_comp_inv J θ (fst (Over.mk X.f) (ptK k)) j _ h0)

/-- `cl(Δ - P × C - C × P) = 𝓛_P - pr₂^*[P]`, with `𝓛_P = cl(Δ - pr₁^* P)` the universal
class. -/
private lemma vojtaClass_eq_abelJacobiClass (X : CurveWithDegreeOneDivisor k) :
    X.vojtaClass 0 0 1 = (show Stacks.Picard.ofScheme (pullback X.f X.f) from
      X.abelJacobiClass (𝟙 (Over.mk X.f))) -
      schemePullbackClassHom (pullback.snd X.f X.f) X.classP := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have := (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  have hPF := X.isEffectiveCartierDivisor_pointFamily (𝟙 (Over.mk X.f))
  have hk : (pullback.diagonal X.f).ker = (X.pointFamily (𝟙 (Over.mk X.f))).zeroDivisor :=
    (ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_ker (X.pointFamily (𝟙 (Over.mk X.f)))).symm
  have hΔ : Stacks.Divisors.picardClass (pullback.diagonal X.f).ker =
      @Stacks.Divisors.picardClass _ (X.pointFamily (𝟙 (Over.mk X.f))).zeroDivisor hPF := by
    revert hPF
    rw [← hk]
    intro
    rfl
  rw [X.vojtaClass_zero_zero_one, hΔ]
  rfl

/-- **`cl(Δ - P × C - C × P)` on a fibre `C × {y}`** is `cl(y - P)`. -/
private lemma pb_bcMap_vojtaClass (X : CurveWithDegreeOneDivisor k) (y : ptK k ⟶ Over.mk X.f) :
    schemePullbackClassHom (bcMap X.f y) (X.vojtaClass 0 0 1) = X.abelJacobiClass y := by
  rw [vojtaClass_eq_abelJacobiClass, map_sub, pb_comp,
    show bcMap X.f y ≫ pullback.snd X.f X.f = bcProj X.f (ptK k) ≫ y.left from bcMap_snd X.f y,
    pb_comp_spec_field, sub_zero]
  exact (X.abelJacobiClass_pullback y (𝟙 _)).trans (by rw [Category.comp_id])

/-- A `k`-point `y` of `C` is a section of `C ⟶ Spec k`. -/
private lemma left_comp_f (X : CurveWithDegreeOneDivisor k) (y : ptK k ⟶ Over.mk X.f) :
    y.left ≫ X.f = 𝟙 _ :=
  (Over.w y).trans specMap_algebraMap_self

/-- `C` pointed by a `k`-point `y`, as a family over `Spec k`. -/
private noncomputable abbrev pointedC (X : CurveWithDegreeOneDivisor k)
    (y : ptK k ⟶ Over.mk X.f) : ModuliEllipticCurves.PointedFamily (Spec (.of k)) :=
  ⟨X.C, X.f, y.left, left_comp_f X y⟩

/-- The image of a `k`-point of `C` is a closed point. -/
private lemma isClosed_left_apply (X : CurveWithDegreeOneDivisor k) (y : ptK k ⟶ Over.mk X.f)
    (a : Spec (.of k)) : IsClosed ({y.left a} : Set X.C) := by
  have : IsSeparated (pointedC X y).map := (inferInstance : IsSeparated X.f)
  have : IsClosedImmersion (pointedC X y).zero :=
    ModuliEllipticCurves.PointedFamily.isClosedImmersion_zero _
  rw [← Set.image_singleton]
  exact (pointedC X y).zero.isClosedEmbedding.isClosedMap _ isClosed_singleton

/-- The closed point of `C` underlying a `k`-point. -/
private noncomputable abbrev closedPt (X : CurveWithDegreeOneDivisor k) (y : ptK k ⟶ Over.mk X.f)
    (a : Spec (.of k)) : {x : X.C // IsClosed ({x} : Set X.C)} :=
  ⟨y.left a, isClosed_left_apply X y a⟩

/-- **The divisor of a `k`-point `y` on `C_k = C ×_k Spec k`** is the pull-back of the point
`y` of `C`: `pr₁^*[𝒪_C(y)] = [𝒪(Q)]`, `Q` the section `(y, id)`. -/
private lemma pb_fst_picardClass_pointIdeal (X : CurveWithDegreeOneDivisor k)
    (y : ptK k ⟶ Over.mk X.f) (a : Spec (.of k)) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f (closedPt X y a)
    haveI := X.isEffectiveCartierDivisor_pointFamily y
    schemePullbackClassHom (pullback.fst X.f (ptK k).hom)
        (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (closedPt X y a))) =
      Stacks.Divisors.picardClass (X.pointFamily y).zeroDivisor := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have i1 := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f (closedPt X y a)
  have i3 := X.isEffectiveCartierDivisor_pointFamily y
  have : IsSeparated (pointedC X y).map := (inferInstance : IsSeparated X.f)
  have : IsSeparated (X.pointFamily y).map := inferInstanceAs (IsSeparated (bcProj X.f (ptK k)))
  have : IsClosedImmersion (pointedC X y).zero :=
    ModuliEllipticCurves.PointedFamily.isClosedImmersion_zero _
  have : IsClosedImmersion (X.pointFamily y).zero :=
    ModuliEllipticCurves.PointedFamily.isClosedImmersion_zero _
  have h1 : Stacks.Zeta.pointIdeal (closedPt X y a) = (pointedC X y).zero.ker :=
    ((pointedC X y).zeroDivisor_eq_vanishingIdeal a).symm.trans
      (pointedC X y).zeroDivisor_eq_ker
  have h2 : (X.pointFamily y).zeroDivisor = (X.pointFamily y).zero.ker :=
    (X.pointFamily y).zeroDivisor_eq_ker
  have i2 : Stacks.Divisors.IsEffectiveCartierDivisor (pointedC X y).zero.ker := h1 ▸ i1
  have i4 : Stacks.Divisors.IsEffectiveCartierDivisor (X.pointFamily y).zero.ker := h2 ▸ i3
  have := isIso_fst_ptK X.f
  rw [Stacks.Divisors.picardClass_congr h1, Stacks.Divisors.picardClass_congr h2]
  exact pb_picardClass_ker_of_isIso _ _ _ (pullback.lift_fst _ _ _)

end Fibres

/-- The ideal sheaf of a prime divisor with support `S` is the vanishing ideal of the
closure of `S`. -/
private lemma idealSheaf_eq_vanishingIdeal_closure {Y : Scheme.{u}}
    (Z : Stacks.Divisors.PrimeDivisor Y) {S : Set Y} (hZ : Z.support = S) :
    Z.idealSheaf = Scheme.IdealSheafData.vanishingIdeal ⟨closure S, isClosed_closure⟩ := by
  have : IsIntegral Z.idealSheaf.subscheme := Z.integral
  have hc : IsClosed S := hZ ▸ Z.idealSheaf.support.isClosed
  exact (Stacks.Intersection.ExteriorProductProjections.vanishingIdeal_support_of_isReduced
    Z.idealSheaf).symm.trans (congrArg Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.ext (hZ.trans hc.closure_eq.symm)))

/-- If the divisor `P` of `X` is a single closed point `P₀`, then `P₀` has residue degree one. -/
private lemma residueDegree_eq_one_of_P_eq_single {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (P₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single P₀ 1) : X.f.residueDegree P₀.1 = 1 := by
  have h := X.degree_P
  rw [hP, Finsupp.sum_single_index (by simp)] at h
  exact_mod_cast (_root_.one_mul _).symm.trans h

/-- `((n - 1) a + b) - n a = b - a` in an additive group. -/
private lemma sub_one_smul_add_sub_smul {G : Type*} [AddCommGroup G] (n : ℤ) (a b : G) :
    (n - 1) • a + b - n • a = b - a := by
  rw [sub_smul, one_smul]
  abel

/-- **The fibre computation.** On each fibre `C × {y}` over a `k`-point `y`, the pull-back of
Mumford's class and `cl(Δ - P₀ × C - C × P₀)` cancel. -/
private lemma pb_bcMap_mumfordCC_add_vojtaClass {k : Type u} [Field k] [IsAlgClosed k]
    (X : CurveWithDegreeOneDivisor k) (P₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single P₀ 1) (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    [Stacks.Divisors.IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩)]
    (y : ptK k ⟶ Over.mk X.f) :
    haveI := A.isAbelianVariety
    Stacks.Picard.schemePullbackClassHom (Stacks.RigidifiedPicard.bcMap X.f y)
      (mumfordCC X j (Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩)) + X.vojtaClass 0 0 1) = 0 := by
  have := A.isAbelianVariety
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (Stacks.RigidifiedPicard.topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
  -- `Θ` as a prime divisor
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg j hj
  have hZI := idealSheaf_eq_vanishingIdeal_closure Z hZ
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf :=
    hZI ▸ (inferInstance : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩))
  have hθ : Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩) =
      Stacks.Divisors.picardClass Z.idealSheaf :=
    Stacks.Divisors.picardClass_congr hZI.symm
  have card := schemePullbackClass_thetaDivisor_translate_eq X P₀ hP A hι hg j hj Z hZ
  rw [hθ, map_add, pb_bcMap_mumfordCC, pb_bcMap_vojtaClass]
  -- the classes of the points `P₀` and `y`
  set y' := closedPt X y a with hy'
  have hP₀ := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f P₀
  have hy'e := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f y'
  have hrdP := residueDegree_eq_one_of_P_eq_single X P₀ hP
  have hrdy : X.f.residueDegree y'.1 = 1 :=
    (Stacks.Chow.residueDegree_eq_one_of_section X.f y.left (left_comp_f X y) a).1
  have hclassP : X.classP = Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal P₀) := by
    rw [CurveWithDegreeOneDivisor.classP, hP, Finsupp.sum_single_index (by simp), one_smul]
  -- `cl(y - P₀)` on `C_k`
  have hAJ : X.abelJacobiClass y = Stacks.Picard.schemePullbackClassHom
      (pullback.fst X.f (ptK k).hom) (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal y') -
        Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal P₀)) := by
    rw [map_sub, pb_fst_picardClass_pointIdeal X y a, ← hclassP]
    rfl
  -- `ψ_0^* θ = g [P₀]`
  have c0 : Stacks.Picard.schemePullbackClassHom (j⁻¹).left
      (Stacks.Divisors.picardClass Z.idealSheaf) =
      (genus X.f : ℤ) • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal P₀) := by
    have h := card (Finsupp.single P₀ (genus X.f : ℤ))
      (Finsupp.single_nonneg.2 (Int.natCast_nonneg _))
      (by rw [Finsupp.sum_single_index (by simp), hrdP]; simp) 1
    have h' := h (by
      intro hdeg
      rw [← A.ι_app_zero (ptK k)]
      dsimp only
      congr 1
      refine (mk_subtype_congr _ ?_ (zero_mem _) (AddMonoidHom.mem_ker.2 hdeg)).trans ?_
      · rw [Finsupp.sum_single_index (by simp), sub_self]
        symm
        rw [AddEquiv.map_eq_zero_iff]
        exact map_zero (Stacks.Picard.schemePullbackClassHom _)
      · rfl)
    simp only [comp_one, _root_.one_mul] at h'
    rw [Finsupp.sum_single_index (by simp)] at h'
    exact h'
  -- `ψ_y^* θ = (g - 1) [P₀] + [y]`
  have hD : (Finsupp.single P₀ ((genus X.f : ℤ) - 1) + Finsupp.single y' 1).sum
      (fun x n =>
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) =
      ((genus X.f : ℤ) - 1) • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal P₀) +
        Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal y') := by
    rw [Finsupp.sum_add_index', Finsupp.sum_single_index (by simp),
      Finsupp.sum_single_index (by simp), one_smul]
    · intro _
      exact zero_smul _ _
    · intro _ _ _
      exact add_smul _ _ _
  have c1 : Stacks.Picard.schemePullbackClassHom ((toPt X ≫ y ≫ j) * j⁻¹).left
      (Stacks.Divisors.picardClass Z.idealSheaf) =
      ((genus X.f : ℤ) - 1) • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal P₀) +
        Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal y') := by
    have h := card (Finsupp.single P₀ ((genus X.f : ℤ) - 1) + Finsupp.single y' 1)
      (add_nonneg (Finsupp.single_nonneg.2 (by have := hg; omega))
        (Finsupp.single_nonneg.2 zero_le_one))
      (by
        rw [Finsupp.sum_add_index', Finsupp.sum_single_index (by simp),
          Finsupp.sum_single_index (by simp), hrdP, hrdy]
        · push_cast
          ring
        · intro _
          exact zero_mul _
        · intro _ _ _
          exact add_mul _ _ _) (y ≫ j)
    have h' := h (by
      intro hdeg
      rw [hj.comp_eq hdim k y]
      dsimp only
      congr 1
      refine mk_subtype_congr _ ?_ _ (AddMonoidHom.mem_ker.2 hdeg)
      congr 1
      rw [hD, hAJ]
      change _ = Stacks.Picard.schemePullbackClassHom _ _
      congr 1
      rw [sub_smul, one_smul]
      abel)
    rw [hD] at h'
    exact h'
  rw [c1, c0, hAJ, sub_one_smul_add_sub_smul, neg_add_cancel]

variable {k : Type u} [Field k]

/-- **Pull-back of the Mumford class** ([MilAV, III, Summary 6.11]). Let `k` be algebraically
closed, `X = (C, P₀)` a curve with a rational point `P₀` (`X.P = P₀`), of genus `g ≥ 1`,
`A = (J, ι)` a Jacobian with `ι` additive (`hι`), `j = j_{P₀}` the Abel–Jacobi map and
`θ = cl(Θ)` the class of the reduced effective Cartier divisor `D` whose support is the theta
divisor `Θ = Faltings.thetaDivisor X A hg j hj`. Then
`(j × j)^* (s₁₂^* θ - s₁^* θ - s₂^* θ) = -cl(Δ - P₀ × C - C × P₀)` in `Pic(C ×_k C)`. -/
@[faltings "lem_nt_mumford_class_point"]
theorem schemePullbackClassHom_tensorHom_mumfordClass_eq_neg_vojtaClass [IsAlgClosed k]
    (X : CurveWithDegreeOneDivisor k) (P₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single P₀ 1) (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj) :
    let θ := Stacks.Divisors.picardClass D
    Stacks.Picard.schemePullbackClassHom (j ⊗ₘ j).left
        (Stacks.Picard.schemePullbackClassHom μ[A.J].left θ -
          Stacks.Picard.schemePullbackClassHom (fst A.J A.J).left θ -
          Stacks.Picard.schemePullbackClassHom (snd A.J A.J).left θ) =
      -X.vojtaClass 0 0 1 := by
  /- `D` is the vanishing ideal of `Θ`: it is radical with support `Θ`, which is closed. -/
  have hDvan : D = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ := by
    have hcl : (⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ :
        TopologicalSpace.Closeds A.J.left) = D.support := by
      ext1
      rw [TopologicalSpace.Closeds.coe_mk, ← hsupp, D.support.isClosed.closure_eq]
    rw [hcl, Scheme.IdealSheafData.vanishingIdeal_support, hrad]
  subst hDvan
  intro θ
  have := A.isAbelianVariety
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  rw [pb_tensorHom_mumford]
  apply eq_neg_of_add_eq_zero_left
  refine eq_zero_of_symm_of_fibres X A (Over.homMk (pointOfClosedPoint X.f P₀.1 P₀.2) (by simp))
    _ ?_ (pb_bcMap_mumfordCC_add_vojtaClass X P₀ hP A hι hg j hj)
  rw [map_add, pb_swapCC_vojtaClass, pb_swapCC_mumfordCC]

end Faltings
