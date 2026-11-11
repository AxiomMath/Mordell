module
public import Mordell.Jacobian.Theta.Basic
public import Mordell.Jacobian.AbelJacobi
public import Mordell.Jacobian.Points
public import Mordell.Curve.EffectiveDivisorDegree
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingDiagonal
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingCartier
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankDisjointCover
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveResolution
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# Pull-back of translates of `Θ⁻`

Let `k` be algebraically closed, `(C, P₀)` a curve over `k` with a point `P₀ ∈ C(k)`, of genus
`g ≥ 1`, `(J, ι)` a Jacobian of `C`, `j = j_{P₀}` the Abel–Jacobi map and `Θ = Θ_{P₀}` the
theta divisor. Let `a ∈ J(k)` and let `D` be an effective divisor of degree `g` on `C` with
`cl(D - g P₀) = a`. Then `j^* 𝒪_J(Θ⁻ + a) ≅ 𝒪_C(D)`, where `Θ⁻ = (-1)^* Θ` and `Θ⁻ + a` is
its translate by `a`.

## Main results

* `Faltings.schemePullbackClass_thetaDivisor_translate_eq`: in `Pic(C)`, the pull-back along
  `j` of the class of `Θ⁻ + a` is the class of `𝒪_C(D)`.

## Implementation notes

The divisor `Θ⁻ + a = {x ∈ J | a - x ∈ Θ}` is the inverse image of `Θ` under the morphism
`x ↦ a - x` of `J`, so `𝒪_J(Θ⁻ + a)` is the pull-back of `𝒪_J(Θ)` along it, and
`j^* 𝒪_J(Θ⁻ + a)` is the pull-back of `𝒪_J(Θ)` along `x ↦ a - j(x)`, which is the product
`(const_a) * j⁻¹` in the group `Hom_k(C, J)`. The divisor `Θ` is entered as a prime divisor
of `J` with support `Faltings.thetaDivisor`, whose existence is
`Faltings.exists_primeDivisor_support_eq_thetaDivisor`; it is a Cartier divisor because `J`
is smooth, and the class `𝒪_J(Θ)` is the Picard class of that effective Cartier divisor.

The point `P₀ ∈ C(k)` is a closed point `x₀` with `P = x₀`, and a divisor on `C` is a finite
`ℤ`-combination of closed points; `D` is effective (`0 ≤ D`) of degree
`∑ D x • [κ(x) : k] = g`. A point `a ∈ J(k)` is a `k`-morphism `Spec k ⟶ J`, and
`cl(D - g P₀) = a` says that `ι(Spec k)` sends the degree-zero class `[𝒪_C(D)] - g [𝒪_C(P₀)]`,
pulled back to `C_k = C ×_k Spec k`, to `a`; as in `Faltings.IsAbelJacobiMap`, this is stated
for every proof that the class has degree zero, which it always has.

The structure `Faltings.Jacobian` asks of `ι` only that it be a morphism of set-valued functors.
The statement also assumes `hι`, that `ι` sends sums of classes to products in the group
`Hom_k(T, J)`, as in [MilAV, III, §1]. Without it the statement fails for `g ≥ 2`. If `ι` is
replaced by `ι · t`, then `j` becomes `j · t`, `a` becomes `a · t` and `Θ` becomes `Θ + (g-1)t`,
while `x ↦ a - j(x)` stays the same.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Lemma 6.8(a), Lemma 6.7.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.RigidifiedPicard
open scoped MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- `Spec k` as a `k`-scheme, in the form used for `k`-points. -/
local notation:max "ptT " k:max => fieldExtensionPoint k k

section Helpers

/-- The constant map `C ⟶ J` at a `k`-point `a`. -/
private noncomputable def constC (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    (a : ptT k ⟶ J) : Over.mk X.f ⟶ J :=
  Over.homMk (U := Over.mk X.f) (V := ptT k) X.f (by simp [Algebra.algebraMap_self]) ≫ a

private lemma constC_mul (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))} [GrpObj J]
    (a b : ptT k ⟶ J) : constC X (a * b) = constC X a * constC X b :=
  MonObj.comp_mul _ _ _

private lemma constC_one (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))} [GrpObj J] :
    constC X (1 : ptT k ⟶ J) = 1 :=
  MonObj.comp_one _

private lemma schemePullbackClass_constC (X : CurveWithDegreeOneDivisor k)
    {J : Over (Spec (.of k))} (a : ptT k ⟶ J) (x : Stacks.Picard.ofScheme J.left) :
    Stacks.Picard.schemePullbackClass (constC X a).left x = 0 := by
  rw [constC, Over.comp_left]
  exact Faltings.AbelianVariety.schemePullbackClass_comp_spec_field X.f a.left x

/-- `F(a) = (a - j)^* θ`. -/
private noncomputable def pullF (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] (j : Over.mk X.f ⟶ J) (θ : Stacks.Picard.ofScheme J.left) (a : ptT k ⟶ J) :
    Stacks.Picard.ofScheme X.C :=
  Stacks.Picard.schemePullbackClass ((constC X a) * j⁻¹).left θ

/-- The theorem of the cube in the form `F(a b) + F(1) = F(a) + F(b)`. -/
private lemma pullF_mul (X : CurveWithDegreeOneDivisor k) {J : Over (Spec (.of k))}
    [GrpObj J] [IsAbelianVariety k J] (j : Over.mk X.f ⟶ J) (θ : Stacks.Picard.ofScheme J.left)
    (a b : ptT k ⟶ J) :
    pullF X j θ (a * b) + pullF X j θ 1 = pullF X j θ a + pullF X j θ b := by
  have h := Faltings.AbelianVariety.schemePullbackClass_cube J θ (constC X a) (constC X b) j⁻¹
  rw [← constC_mul, schemePullbackClass_constC, schemePullbackClass_constC,
    schemePullbackClass_constC] at h
  simp only [add_zero, zero_add] at h
  simp only [pullF, constC_one, one_mul]
  exact h

/-- Over an algebraically closed field, every closed point of a `k`-scheme locally of finite type
is the image of a `k`-point. -/
private lemma exists_pt_of_isClosed [IsAlgClosed k] (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] (y : Y.left) (hy : IsClosed ({y} : Set Y.left)) :
    ∃ u : ptT k ⟶ Y, ∀ p, u.left.base p = y := by
  obtain ⟨b, hb, p, hp⟩ := exists_algebraicClosure_point_of_isClosed Y.hom y hy
  let φ : AlgebraicClosure k →ₐ[k] k := IsAlgClosed.lift
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ b) ?_, fun q => ?_⟩
  · simp only [Over.mk_hom, Category.assoc, hb, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact φ.commutes x
  · change b (Spec.map (CommRingCat.ofHom φ.toRingHom) q) = y
    rw [← hp]
    congr 1
    exact Subsingleton.elim _ _

/-- The structure morphism `Spec k ⟶ Spec k` of `ptT k` is an isomorphism. -/
private lemma isIso_ptT_hom (k : Type u) [Field k] : IsIso (ptT k).hom := by
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  infer_instance

/-- The structure morphism of a `k`-scheme, to `ptT k`. -/
private noncomputable def toPtT (Y : Over (Spec (.of k))) : Y ⟶ ptT k :=
  haveI := isIso_ptT_hom k
  Over.homMk (Y.hom ≫ inv (ptT k).hom) (by simp)

/-- Morphisms into `ptT k` are unique. -/
private lemma hom_ptT_ext {Y : Over (Spec (.of k))} (f g : Y ⟶ ptT k) : f = g := by
  have := isIso_ptT_hom k
  ext1
  rw [← cancel_mono (ptT k).hom, Over.w f, Over.w g]

/-- `Pic` commutes with addition along any morphism. -/
private lemma schemePullbackClass_add {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (a b : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass h (a + b) =
      Stacks.Picard.schemePullbackClass h a + Stacks.Picard.schemePullbackClass h b :=
  map_add (Stacks.Picard.schemePullbackClassHom h) a b

/-- A curve over an algebraically closed field has a `k`-point. -/
private lemma nonempty_ptT_hom_curve [IsAlgClosed k] (X : CurveWithDegreeOneDivisor k) :
    Nonempty (ptT k ⟶ Over.mk X.f) := by
  have : CompactSpace X.C := (quasiCompact_iff_compactSpace X.f).1 inferInstance
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X.C) isClosed_univ
    ⟨(inferInstance : Nonempty X.C).some, trivial⟩
  have : LocallyOfFiniteType (Over.mk X.f).hom := (inferInstance : LocallyOfFiniteType X.f)
  obtain ⟨Q, -⟩ := exists_pt_of_isClosed (Over.mk X.f) x hx
  exact ⟨Q⟩

/-- **The universal class**: some `w ∈ P⁰_C(J)` has `ι(w) = 𝟙_J`. -/
private lemma exists_ι_app_eq_id [IsAlgClosed k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) :
    ∃ w : (relativePicZeroFunctor k X.f).obj (op A.J), A.ι.app (op A.J) w = 𝟙 A.J := by
  obtain ⟨Q⟩ := nonempty_ptT_hom_curve X
  have := A.isIso_app A.J ⟨toPtT A.J ≫ Q⟩
  exact ((isIso_iff_bijective _).1 this).2 (𝟙 A.J)

/-- The universal class pulls back along `y : T ⟶ J` to a class with `ι = y`. -/
private lemma ι_app_map_of_eq_id (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    {w : (relativePicZeroFunctor k X.f).obj (op A.J)} (hw : A.ι.app (op A.J) w = 𝟙 A.J)
    {T : Over (Spec (.of k))} (y : T ⟶ A.J) :
    A.ι.app (op T) ((relativePicZeroFunctor k X.f).map y.op w) = y := by
  have h := NatTrans.naturality_apply A.ι y.op w
  rw [hw] at h
  exact h.trans (Category.comp_id y)

/-- A `k`-point `u` of `J` lies in `U`. -/
private def PtMem {J : Over (Spec (.of k))} (u : ptT k ⟶ J) (U : Set J.left) : Prop :=
  ∀ p, u.left.base p ∈ U

/-- In an abelian variety over an algebraically closed field, for nonempty opens `U`, `V` and a
`k`-point `a`, some `k`-point `u` has `u ∈ U` and `a u ∈ V`. -/
private lemma exists_ptMem_mul [IsAlgClosed k] (J : Over (Spec (.of k))) [GrpObj J]
    [IsAbelianVariety k J] {U V : Set J.left} (hU : IsOpen U) (hU' : U.Nonempty) (hV : IsOpen V)
    (hV' : V.Nonempty) (a : ptT k ⟶ J) : ∃ u : ptT k ⟶ J, PtMem u U ∧ PtMem (a * u) V := by
  let π : J ⟶ ptT k := toPtT J
  let m : J ⟶ J := (π ≫ a) * 𝟙 J
  let m' : J ⟶ J := (π ≫ a⁻¹) * 𝟙 J
  have hm : ∀ u : ptT k ⟶ J, u ≫ m = a * u := fun u => by
    rw [MonObj.comp_mul, ← Category.assoc, hom_ptT_ext (u ≫ π) (𝟙 _), Category.id_comp,
      Category.comp_id]
  have hm'm : m' ≫ m = 𝟙 J := by
    rw [MonObj.comp_mul, ← Category.assoc, hom_ptT_ext (m' ≫ π) π, Category.comp_id]
    change (π ≫ a) * ((π ≫ a⁻¹) * 𝟙 J) = 𝟙 J
    rw [GrpObj.comp_inv]
    exact mul_inv_cancel_left _ _
  have hAV : IsAbelianVariety k J := inferInstance
  have hVar := hAV.toIsProperVariety.toIsVariety
  have : LocallyOfFiniteType J.hom := hVar.toLocallyOfFiniteType
  have : JacobsonSpace J.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) J.hom
  have hW : IsOpen (U ∩ m.left.base ⁻¹' V) := hU.inter (hV.preimage m.left.continuous)
  have hW' : (U ∩ m.left.base ⁻¹' V).Nonempty := by
    obtain ⟨v, hv⟩ := hV'
    refine nonempty_preirreducible_inter hU (hV.preimage m.left.continuous) hU'
      ⟨m'.left.base v, ?_⟩
    change (m' ≫ m).left.base v ∈ V
    rw [hm'm]
    exact hv
  obtain ⟨y, hyW, hy⟩ := nonempty_inter_closedPoints hW' hW.isLocallyClosed
  obtain ⟨u, hu⟩ := exists_pt_of_isClosed J y hy
  refine ⟨u, fun p => (hu p).symm ▸ hyW.1, fun p => ?_⟩
  rw [← hm u]
  change m.left.base (u.left.base p) ∈ V
  rw [hu p]
  exact hyW.2

end Helpers

section Classes

variable (X : CurveWithDegreeOneDivisor k)

private lemma hdimX : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
  (topologicalKrullDim_fiber_spec X.f s).trans_le
    (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)

/-- A curve is covered by two affine opens. -/
private lemma exists_twoAffineCover : ∃ U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens,
    (⊤ : X.C.Opens) = ⨆ i, U i ∧ ∀ i, IsAffineOpen (U i) := by
  have : IsNoetherian (Spec (.of k)) := inferInstance
  have : IsNoetherian X.C := isNoetherian_of_locallyOfFiniteType (Y := Spec (.of k)) X.f
  have : X.C.IsSeparated := ⟨by
    rw [← terminal.comp_from X.f]
    have : IsSeparated (terminal.from (Spec (.of k))) :=
      Scheme.IsSeparated.isSeparated_terminal_from
    infer_instance⟩
  exact Stacks.TwoAffineCech.exists_cover_isAffineOpen X.C
    (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)

/-- The pull-back of a class of `C` to `C_k = C ×_k Spec k`, in the small model. -/
private noncomputable def zHom :
    Stacks.Picard.ofScheme X.C →+ Stacks.Picard.smallOfScheme (bc X.f (ptT k)) :=
  (smallEquiv (bc X.f (ptT k))).symm.toAddMonoidHom.comp
    (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f (ptT k).hom))

/-- The class `[𝒪_C(x)]` of a closed point. -/
private noncomputable def classPt (x : {x : X.C // IsClosed ({x} : Set X.C)}) :
    Stacks.Picard.ofScheme X.C :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
  Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)

/-- With `P = x₀`, the point `x₀` is rational, so `[𝒪_C(x₀)]` has degree one. -/
private lemma invertibleCurveDegreeHom_classPt_of_eq_single
    (x₀ : {x : X.C // IsClosed ({x} : Set X.C)}) (hP : X.P = Finsupp.single x₀ 1)
    (hdim : topologicalKrullDim X.C ≤ 1) :
    invertibleCurveDegreeHom k X.f hdim (classPt X x₀) = 1 := by
  have h := X.degree_P
  rw [hP, Finsupp.sum_single_index (by simp)] at h
  rw [show invertibleCurveDegreeHom k X.f hdim (classPt X x₀) = X.f.residueDegree x₀.1 from
    X.invertibleCurveDegreeHom_picardClass_pointIdeal hdim x₀]
  simpa using h

variable (A : Jacobian k X.f)

/-- `ι` of the class of `c ∈ Pic(C)` of degree zero, as a `k`-point of `J`. -/
private noncomputable def ιc (c : Stacks.Picard.ofScheme X.C)
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) : ptT k ⟶ A.J :=
  A.ι.app (op (ptT k)) (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
    QuotientAddGroup.mk (⟨zHom X c, hc⟩ : (degree X.f (hdimX X) (ptT k)).ker))

private lemma degree_zHom_add {c c' : Stacks.Picard.ofScheme X.C}
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0)
    (hc' : degree X.f (hdimX X) (ptT k) (zHom X c') = 0) :
    degree X.f (hdimX X) (ptT k) (zHom X (c + c')) = 0 := by
  rw [map_add, map_add, hc, hc', add_zero]

private lemma ιc_add
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    {c c' : Stacks.Picard.ofScheme X.C}
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0)
    (hc' : degree X.f (hdimX X) (ptT k) (zHom X c') = 0) :
    ιc X A (c + c') (degree_zHom_add X hc hc') = ιc X A c hc * ιc X A c' hc' := by
  refine Eq.trans ?_ (hι (ptT k) _ _)
  change A.ι.app _ _ = A.ι.app _ _
  congr 1
  have e : (⟨zHom X (c + c'), degree_zHom_add X hc hc'⟩ : (degree X.f (hdimX X) (ptT k)).ker) =
      ⟨zHom X c, hc⟩ + ⟨zHom X c', hc'⟩ :=
    Subtype.ext (map_add (zHom X) c c')
  rw [e]
  rfl

/-- Every `k`-point of `J` is `ι` of a class of degree zero. -/
private lemma exists_ιc_eq [IsAlgClosed k] (u : ptT k ⟶ A.J) :
    ∃ (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0),
      ιc X A c hc = u := by
  obtain ⟨Q⟩ := nonempty_ptT_hom_curve X
  have := A.isIso_app (ptT k) ⟨Q⟩
  obtain ⟨w, hw⟩ := ((isIso_iff_bijective _).1 this).2 u
  induction w using QuotientAddGroup.induction_on with | H zz => ?_
  obtain ⟨z', hz'⟩ := zz
  have := isIso_ptT_hom k
  obtain ⟨c, hzc⟩ : ∃ c, zHom X c = z' := by
    refine ⟨Stacks.Picard.schemePullbackClass (inv (pullback.fst X.f (ptT k).hom))
      (smallEquiv.{u} _ z'), ?_⟩
    change (smallEquiv.{u} _).symm (Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom)
      (Stacks.Picard.schemePullbackClass (inv (pullback.fst X.f (ptT k).hom))
        (smallEquiv.{u} _ z'))) = z'
    rw [AddEquiv.symm_apply_eq, Stacks.Picard.schemePullbackClass_comp, IsIso.hom_inv_id,
      Stacks.Picard.schemePullbackClass_id]
  subst hzc
  exact ⟨c, hz', hw⟩

/-- The fibre degree of the pull-back of `c ∈ Pic(C)` to `C_k` is the degree of `c`. -/
private lemma degree_zHom_apply (c : Stacks.Picard.ofScheme X.C) (t : (ptT k).left) :
    degree X.f (hdimX X) (ptT k) (zHom X c) t =
      invertibleCurveDegreeHom k X.f
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f) c := by
  let T := ptT k
  let π : bc X.f T ⟶ Spec (.of k) := bcProj X.f T
  have : SmoothOfRelativeDimension 1 π :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  rw [degree_apply]
  refine (relativeInvertibleDegreeHomAt_spec π hdimT _ t _).trans ?_
  have e : smallEquiv (bc X.f T) (zHom X c) =
      Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) c :=
    AddEquiv.apply_symm_apply _ _
  rw [e, invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k k
    (IsPullback.of_hasPullback X.f T.hom) _ hdimT]

/-- `cl(D - g P₀)` has degree zero for a divisor `D` of degree `g`. -/
private lemma degree_zHom_classD (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1) (D : {x : X.C // IsClosed ({x} : Set X.C)} →₀ ℤ)
    (hDdeg : (D.sum fun x n => n * (X.f.residueDegree x.1 : ℤ)) = genus X.f) :
    degree X.f (hdimX X) (ptT k)
      (zHom X ((D.sum fun x n => n • classPt X x) - (genus X.f : ℤ) • classPt X x₀)) = 0 := by
  let T := ptT k
  let π : bc X.f T ⟶ Spec (.of k) := bcProj X.f T
  have : SmoothOfRelativeDimension 1 π :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  have hpt : ∀ x, invertibleCurveDegreeHom k X.f hdimC (classPt X x) = X.f.residueDegree x.1 :=
    fun x => X.invertibleCurveDegreeHom_picardClass_pointIdeal hdimC x
  funext t
  rw [degree_apply]
  refine (relativeInvertibleDegreeHomAt_spec π hdimT _ t _).trans ?_
  have e : smallEquiv (bc X.f T) (zHom X ((D.sum fun x n => n • classPt X x) -
      (genus X.f : ℤ) • classPt X x₀)) = Stacks.Picard.schemePullbackClass
        (pullback.fst X.f T.hom) ((D.sum fun x n => n • classPt X x) -
          (genus X.f : ℤ) • classPt X x₀) :=
    AddEquiv.apply_symm_apply _ _
  rw [e, invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k k
    (IsPullback.of_hasPullback X.f T.hom) hdimC hdimT, map_sub, map_zsmul, map_finsuppSum,
    invertibleCurveDegreeHom_classPt_of_eq_single X x₀ hP]
  simp only [map_zsmul, hpt, smul_eq_mul, mul_one]
  rw [hDdeg]
  simp

/-- **From a dense open to all of `J`.** For any class `θ` on `J`, if
`(ι(c) - j)^* θ = c + g [P₀]` for the `ι(c)` in a nonempty open `U`, then it holds for every
class `c` of degree zero: by the theorem of the cube, `a ↦ (a - j)^* θ` is affine. -/
private lemma pullF_ιc_eq_of_isOpen [IsAlgClosed k]
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (j : Over.mk X.f ⟶ A.J) (θ : Stacks.Picard.ofScheme A.J.left)
    (x₀ : {x : X.C // IsClosed ({x} : Set X.C)}) {U : Set A.J.left} (hU : IsOpen U)
    (hU' : U.Nonempty)
    (hgen : ∀ (c : Stacks.Picard.ofScheme X.C)
      (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0),
        PtMem (ιc X A c hc) U → pullF X j θ (ιc X A c hc) = c + (genus X.f : ℤ) • classPt X x₀)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    pullF X j θ (ιc X A c hc) = c + (genus X.f : ℤ) • classPt X x₀ := by
  have := A.isAbelianVariety
  have hF1 : pullF X j θ 1 = (genus X.f : ℤ) • classPt X x₀ := by
    obtain ⟨w, hw, -⟩ := exists_ptMem_mul A.J hU hU' hU hU' 1
    obtain ⟨w', hw', hww'⟩ := exists_ptMem_mul A.J hU hU' hU hU' w
    obtain ⟨c₁, h₁, rfl⟩ := exists_ιc_eq X A w
    obtain ⟨c₂, h₂, rfl⟩ := exists_ιc_eq X A w'
    have e := pullF_mul X j θ (ιc X A c₁ h₁) (ιc X A c₂ h₂)
    rw [← ιc_add X A hι h₁ h₂] at e hww'
    rw [hgen _ _ hww', hgen _ _ hw, hgen _ _ hw'] at e
    exact (eq_sub_of_add_eq' e).trans (by abel)
  obtain ⟨v, hv, hav⟩ := exists_ptMem_mul A.J hU hU' hU hU' (ιc X A c hc)
  obtain ⟨c₂, h₂, rfl⟩ := exists_ιc_eq X A v
  have e := pullF_mul X j θ (ιc X A c hc) (ιc X A c₂ h₂)
  rw [← ιc_add X A hι hc h₂] at e hav
  rw [hgen _ _ hav, hgen _ _ hv, hF1] at e
  exact (eq_sub_of_add_eq e.symm).trans (by abel)

end Classes

section ConstantMaps

variable (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)

/-- The constant map at `ι(c)` is `ι(C)` of the pull-back of the class `c` to `C × C`. -/
private lemma constC_ιc (c : Stacks.Picard.ofScheme X.C)
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    constC X (ιc X A c hc) = A.ι.app (op (Over.mk X.f))
      ((relativePicZeroFunctor k X.f).map (toPtT (Over.mk X.f)).op
        (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
          QuotientAddGroup.mk (⟨zHom X c, hc⟩ : (degree X.f (hdimX X) (ptT k)).ker))) := by
  have h := ConcreteCategory.congr_hom (A.ι.naturality (toPtT (Over.mk X.f)).op)
    (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
      QuotientAddGroup.mk (⟨zHom X c, hc⟩ : (degree X.f (hdimX X) (ptT k)).ker))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  refine Eq.trans ?_ h.symm
  exact congrArg (· ≫ ιc X A c hc) (hom_ptT_ext _ _)

/-- `x ↦ ι(c) - j(x)` is `ι(C)` of `pr^* c - 𝓛_P`, for `𝓛_P` the universal class. -/
private lemma constC_mul_inv_eq
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j) (c : Stacks.Picard.ofScheme X.C)
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    constC X (ιc X A c hc) * j⁻¹ = A.ι.app (op (Over.mk X.f))
      ((relativePicZeroFunctor k X.f).map (toPtT (Over.mk X.f)).op
        (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
          QuotientAddGroup.mk (⟨zHom X c, hc⟩ : (degree X.f (hdimX X) (ptT k)).ker)) -
        X.univClass) :=
  (congrArg₂ (fun x y => x * y⁻¹) (constC_ιc X A c hc) hj.eq_ι_app_univClass).trans
    (A.ι_app_sub _ _ _).symm

/-- **The universal class along `ψ_c = ι(c) - j`**: it pulls back to `pr^* c - 𝓛_P` in
`P⁰_C(C)`, `ι(C)` being injective. -/
private lemma map_ψ_universal_eq [IsAlgClosed k]
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {w : (relativePicZeroFunctor k X.f).obj (op A.J)} (hw : A.ι.app (op A.J) w = 𝟙 A.J)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    (relativePicZeroFunctor k X.f).map (constC X (ιc X A c hc) * j⁻¹).op w =
      (relativePicZeroFunctor k X.f).map (toPtT (Over.mk X.f)).op
        (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
          QuotientAddGroup.mk (⟨zHom X c, hc⟩ : (degree X.f (hdimX X) (ptT k)).ker)) -
        X.univClass := by
  have := A.isIso_app (Over.mk X.f) ⟨𝟙 _⟩
  exact ((isIso_iff_bijective _).1 this).1
    ((ι_app_map_of_eq_id X A hw _).trans (constC_mul_inv_eq X A hj c hc))

/-- **The Fitting divisor of a family pulls back to the divisor of a section** (the computation
of [MilAV, III, Lemma 6.7]): if a family `Θ` on `C ×_k T` pulls back along `ψ : C ⟶ T` to
`pr₁^* N - [Δ] + pr₂^* n`, with `H¹(N) = 0` and `H⁰(N) = k s`, then `ψ⁻¹ Fit₀ R¹pr_* Θ = Z(s)`. -/
private lemma familyFitting_comap_eq_zeroScheme
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) {T : Over (Spec (.of k))}
    [Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.FamilyFitting.diagIdeal X.f)]
    (Θ : Stacks.Picard.ofScheme (pullback X.f T.hom)) (ψ : Over.mk X.f ⟶ T)
    (N : X.C.Modules) [SheafOfModules.IsInvertible X.C.sheaf.obj X.C.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f N t 1) = 0)
    (hN0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f N t 0) = 1)
    (n : Stacks.Picard.ofScheme X.C)
    (hA : Stacks.Picard.schemePullbackClass (pullback.map X.f X.f X.f T.hom (𝟙 _) ψ.left (𝟙 _)
        (by simp) (by rw [Category.comp_id]; exact (Over.w ψ).symm)) Θ =
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f)
          (X.C.picardClass N ‹_›) - Stacks.Divisors.picardClass
            (Stacks.FamilyFitting.diagIdeal X.f)) +
        Stacks.Picard.schemePullbackClass (pullback.snd X.f X.f) n) :
    (Stacks.FamilyFitting.familyFitting X.f U hU hUaff T.hom
        (Stacks.PicardCurve.rep Θ)).comap ψ.left =
      AlgebraicGeometry.zeroScheme X.C N s := by
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
    (pullback.map X.f X.f X.f T.hom (𝟙 _) ψ.left (𝟙 _) (by simp)
      (by rw [Category.comp_id]; exact (Over.w ψ).symm)) Θ
  refine (Stacks.FamilyFitting.familyFitting_comap X.f U hU hUaff T.hom _ X.f ψ.left
    (Over.w ψ) _ e.symm).trans ?_
  rw [hA]
  refine (Stacks.FamilyFitting.familyFitting_rep_add_pullback X.f U hU hUaff X.f _ n).trans ?_
  exact Stacks.FamilyFitting.familyFitting_diag_eq_zeroScheme X.f U hU hUaff N s hs hN1 hN0 _
    (sub_add_cancel _ _)

/-- Two degree-zero classes with the same image in `P⁰_C(T)` differ by a class from `T`. -/
private lemma exists_eq_add_of_mk_eq {T : Over (Spec (.of k))}
    {a b : Stacks.Picard.smallOfScheme (bc X.f T)} (ha : a ∈ (degree X.f (hdimX X) T).ker)
    (hb : b ∈ (degree X.f (hdimX X) T).ker)
    (h : (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨a, ha⟩ : (degree X.f (hdimX X) T).ker)) =
      (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨b, hb⟩ : (degree X.f (hdimX X) T).ker))) :
    ∃ n, b = a + Stacks.Picard.smallSchemePullbackClassHom (bcProj X.f T) n := by
  obtain ⟨n, hn⟩ := (QuotientAddGroup.eq.1 h : _)
  refine ⟨n, ?_⟩
  have hn' : Stacks.Picard.smallSchemePullbackClassHom (bcProj X.f T) n = -a + b := hn
  rw [hn']
  abel

/-- **The universal class along `ψ_c`, in `Pic(C ×_k C)`**: a representative `ξ` of the universal
class pulls back along `ψ_c = ι(c) - j` to `pr₁^*(c + [P]) - [Δ]`, up to a class from the base. -/
private lemma exists_schemePullbackClass_bcMap_ψ [IsAlgClosed k]
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    ∃ n : Stacks.Picard.ofScheme X.C,
      Stacks.Picard.schemePullbackClass (bcMap X.f (constC X (ιc X A c hc) * j⁻¹))
          (smallEquiv.{u} _ ξ) =
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f (Over.mk X.f).hom) c -
          X.abelJacobiClass (𝟙 (Over.mk X.f))) +
        Stacks.Picard.schemePullbackClass (bcProj X.f (Over.mk X.f)) n := by
  have h := map_ψ_universal_eq X A hj hw c hc
  have hb : Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f (constC X (ιc X A c hc) * j⁻¹))
      ξ ∈ (degree X.f (hdimX X) (Over.mk X.f)).ker := by
    rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_bcMap,
      AddMonoidHom.mem_ker.1 hξ]
    rfl
  have ha : Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f (toPtT (Over.mk X.f))) (zHom X c) -
      (smallEquiv.{u} _).symm (X.abelJacobiClass (𝟙 (Over.mk X.f))) ∈
        (degree X.f (hdimX X) (Over.mk X.f)).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, degree_smallSchemePullbackClassHom_bcMap,
      AddMonoidHom.mem_ker.1 (show zHom X c ∈ (degree X.f (hdimX X) (ptT k)).ker from hc),
      X.degree_abelJacobiClass_id (hdimX X)]
    rfl
  obtain ⟨n, hn⟩ := exists_eq_add_of_mk_eq X ha hb h.symm
  refine ⟨smallEquiv.{u} _ n, ?_⟩
  have := congrArg (smallEquiv.{u} _) hn
  rw [smallEquiv_smallSchemePullbackClassHom, map_add, map_sub,
    smallEquiv_smallSchemePullbackClassHom, smallEquiv_smallSchemePullbackClassHom,
    AddEquiv.apply_symm_apply] at this
  rw [this]
  have hz : smallEquiv.{u} _ (zHom X c) =
      Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom) c :=
    AddEquiv.apply_symm_apply _ _
  rw [hz, Stacks.Picard.schemePullbackClass_comp, bcMap_fst]
  rfl

/-- With `P = x₀`, the class `[𝒪_C(P)]` is `[𝒪_C(x₀)]`. -/
private lemma classP_eq_classPt (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1) : X.classP = classPt X x₀ := by
  simp only [CurveWithDegreeOneDivisor.classP, hP]
  rw [Finsupp.sum_single_index (by simp), one_smul]
  rfl

/-- The family `Θ = ξ + (g - 1) pr₁^*[x₀]` pulls back along `ψ_c` to
`pr₁^*(c + g [x₀]) - [Δ]`, up to a class from the base. -/
private lemma exists_schemePullbackClass_bcMap_thetaFamily [IsAlgClosed k]
    [Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.FamilyFitting.diagIdeal X.f)]
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (x₀ : {x : X.C // IsClosed ({x} : Set X.C)}) (hP : X.P = Finsupp.single x₀ 1)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    ∃ n : Stacks.Picard.ofScheme X.C,
      Stacks.Picard.schemePullbackClass (bcMap X.f (constC X (ιc X A c hc) * j⁻¹))
          (smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
            Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀)) =
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f)
            (c + (genus X.f : ℤ) • classPt X x₀) -
          Stacks.Divisors.picardClass (Stacks.FamilyFitting.diagIdeal X.f)) +
        Stacks.Picard.schemePullbackClass (pullback.snd X.f X.f) n := by
  obtain ⟨n, hn⟩ := exists_schemePullbackClass_bcMap_ψ X A hj hξ hw c hc
  refine ⟨n, ?_⟩
  rw [schemePullbackClass_add, hn, schemePullbackClass_zsmul,
    Stacks.Picard.schemePullbackClass_comp, bcMap_fst]
  have hAJ : X.abelJacobiClass (𝟙 (Over.mk X.f)) =
      Stacks.Divisors.picardClass (Stacks.FamilyFitting.diagIdeal X.f) -
        Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f) (classPt X x₀) := by
    rw [← classP_eq_classPt X x₀ hP]
    rfl
  rw [hAJ, schemePullbackClass_add, schemePullbackClass_zsmul]
  change Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f) c -
      (Stacks.Divisors.picardClass (Stacks.FamilyFitting.diagIdeal X.f) -
        Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f) (classPt X x₀)) +
      Stacks.Picard.schemePullbackClass (pullback.snd X.f X.f) n +
      ((genus X.f : ℤ) - 1) • Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f)
        (classPt X x₀) = _
  rw [sub_smul, one_smul]
  abel

/-- **`ψ_c⁻¹ Θ' = Z(s)`** for the Fitting divisor `Θ'` of the theta family, whenever
`N = c + g [x₀]` has `H¹ = 0` and `H⁰ = k s`. -/
private lemma familyFitting_thetaFamily_comap [IsAlgClosed k]
    [Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.FamilyFitting.diagIdeal X.f)]
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i))
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (x₀ : {x : X.C // IsClosed ({x} : Set X.C)}) (hP : X.P = Finsupp.single x₀ 1)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0)
    [SheafOfModules.IsInvertible X.C.sheaf.obj X.C.ringCatSheaf.property
      (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀))]
    (s : Γ(Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀), ⊤)) (hs : s ≠ 0)
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f
        (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 1) = 0)
    (hN0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f
        (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 0) = 1) :
    (Stacks.FamilyFitting.familyFitting X.f U hU hUaff A.J.hom
        (Stacks.PicardCurve.rep (smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
          Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀)))).comap
        (constC X (ιc X A c hc) * j⁻¹).left =
      AlgebraicGeometry.zeroScheme X.C
        (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) s := by
  obtain ⟨n, hn⟩ :=
    exists_schemePullbackClass_bcMap_thetaFamily X A hj x₀ hP hξ hw c hc
  refine familyFitting_comap_eq_zeroScheme X U hU hUaff _ _ _ s hs hN1 hN0 n ?_
  refine hn.trans ?_
  congr 3
  exact (Stacks.Picard.classOf_picardRepresentative _ _).symm

/-- **The theta family has fibre degree `g - 1`.** -/
private lemma degree_thetaFamily (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker) :
    degree X.f (hdimX X) A.J ((smallEquiv.{u} _).symm (smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
        Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀))) =
      fun _ => (genus X.f : ℤ) - 1 := by
  have h1 : Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀) =
      smallEquiv.{u} _ (Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f (toPtT A.J))
        (zHom X (classPt X x₀))) := by
    rw [smallEquiv_smallSchemePullbackClassHom,
      show smallEquiv.{u} _ (zHom X (classPt X x₀)) = Stacks.Picard.schemePullbackClass
        (pullback.fst X.f (ptT k).hom) (classPt X x₀) from AddEquiv.apply_symm_apply _ _,
      Stacks.Picard.schemePullbackClass_comp, bcMap_fst]
  rw [h1, ← map_zsmul, ← map_add, AddEquiv.symm_apply_apply, map_add, map_zsmul,
    AddMonoidHom.mem_ker.1 hξ, degree_smallSchemePullbackClassHom_bcMap]
  funext t
  simp only [zero_add, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [degree_zHom_apply, invertibleCurveDegreeHom_classPt_of_eq_single X x₀ hP, mul_one]

end ConstantMaps

section Generic

variable (X : CurveWithDegreeOneDivisor k)

/-- **Riemann–Roch on the fibres of a family**: a class `θ` on `C ×_k T` of fibre degree `d`
has `h⁰ - h¹ = d + 1 - g` on every fibre. -/
private lemma finrank_fibreCohomology_sub_eq (T : Over (Spec (.of k)))
    (θ : Stacks.Picard.ofScheme (pullback X.f T.hom)) (d : ℤ)
    (hθ : degree X.f (hdimX X) T ((smallEquiv.{u} _).symm θ) = fun _ => d) (t : T.left) :
    (Module.finrank (T.left.residueField t)
        (Stacks.FibreCohomology.fibreCohomology (pullback.snd X.f T.hom)
          (Stacks.PicardCurve.rep θ) t 0) : ℤ) -
      Module.finrank (T.left.residueField t)
        (Stacks.FibreCohomology.fibreCohomology (pullback.snd X.f T.hom)
          (Stacks.PicardCurve.rep θ) t 1) =
      d + 1 - genus X.f := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  set π := pullback.snd X.f T.hom
  set K := T.left.residueField t
  have hfib : IsPullback (pullback.fst π (T.left.fromSpecResidueField t))
      (pullback.snd π (T.left.fromSpecResidueField t)) π (T.left.fromSpecResidueField t) :=
    IsPullback.of_hasPullback _ _
  let := Stacks.AbelMap.residueFieldAlgebra t
  have hZ : IsPullback (pullback.fst π (T.left.fromSpecResidueField t) ≫ pullback.fst X.f T.hom)
      (pullback.snd π (T.left.fromSpecResidueField t)) X.f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have h := hfib.paste_horiz (IsPullback.of_hasPullback X.f T.hom)
    rwa [← Stacks.AbelMap.residueFieldPoint_hom t] at h
  have : IsProper (pullback.snd π (T.left.fromSpecResidueField t)) :=
    Stacks.AbelMap.isProper_of_isPullback (K := K) X.f _ _ hZ
  have := Stacks.AbelMap.isIso_globalSections_of_isPullback (K := K) X.f _ _ hZ
  have hd : topologicalKrullDim ↥(pullback π (T.left.fromSpecResidueField t)) ≤ 1 :=
    topologicalKrullDim_fiber_bcProj_le X.f (hdimX X) T t
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
    (pullback.fst π (T.left.fromSpecResidueField t)) θ
  have hfib' : IsPullback (pullback.fst π (T.left.fromSpecResidueField t))
      (pullback.snd π (T.left.fromSpecResidueField t)) π
      (Spec.map (𝟙 _) ≫ T.left.fromSpecResidueField t) := by
    rwa [Spec.map_id, Category.id_comp]
  have h := Stacks.FibreCohomology.finrank_eq_of_isPullback (K := K) π (Stacks.PicardCurve.rep θ)
    t (𝟙 _) _ _ hfib' _ e
  rw [← h 0, ← h 1]
  have := (Stacks.Picard.picardRepresentative _
    (Stacks.Picard.schemePullbackClass (pullback.fst π (T.left.fromSpecResidueField t)) θ)).property
  rw [finrank_sub_finrank_eq_invertibleCurveDegree_add_genus K _ hd,
    genus_baseChange k K _ _ X.f hZ]
  congr 2
  have h2 := congrFun hθ t
  rw [degree_apply, AddEquiv.apply_symm_apply, relativeInvertibleDegreeHomAt_apply] at h2
  rw [← h2, ← invertibleCurveDegreeHom_picardClass]
  congr 1
  exact Stacks.Picard.classOf_picardRepresentative _ _

variable (A : Jacobian k X.f)

/-- `Pic(Spec k) = 0`, in the small model. -/
private lemma subsingleton_smallOfScheme_ptT :
    Subsingleton (Stacks.Picard.smallOfScheme (ptT k).left) := by
  have : DiscreteTopology (ptT k).left := inferInstanceAs (DiscreteTopology (PrimeSpectrum k))
  have := Stacks.Picard.subsingleton_ofScheme_of_discreteTopology (ptT k).left
  exact (smallEquiv (ptT k).left).toEquiv.subsingleton

/-- **The universal class at a `k`-point**: if `ι(Spec k)` sends the class of `z` to `y`, the
universal class pulls back along `y` to `z`. -/
private lemma smallSchemePullbackClassHom_bcMap_universal [IsAlgClosed k]
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (y : ptT k ⟶ A.J) {z : Stacks.Picard.smallOfScheme (bc X.f (ptT k))}
    (hz : z ∈ (degree X.f (hdimX X) (ptT k)).ker)
    (hy : A.ι.app (op (ptT k)) (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
      QuotientAddGroup.mk (⟨z, hz⟩ : (degree X.f (hdimX X) (ptT k)).ker)) = y) :
    Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f y) ξ = z := by
  obtain ⟨Q⟩ := nonempty_ptT_hom_curve X
  have := A.isIso_app (ptT k) ⟨Q⟩
  have h := ((isIso_iff_bijective _).1 this).1 ((ι_app_map_of_eq_id X A hw y).trans hy.symm)
  have hb : Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f y) ξ ∈
      (degree X.f (hdimX X) (ptT k)).ker := by
    rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_bcMap,
      AddMonoidHom.mem_ker.1 hξ]
    rfl
  obtain ⟨n, hn⟩ := exists_eq_add_of_mk_eq X hz hb h.symm
  have := subsingleton_smallOfScheme_ptT (k := k)
  rw [hn, Subsingleton.elim n 0, map_zero, add_zero]

/-- **Fibres at `k`-points**: the fibre cohomology of a family on `C ×_k T` at the image of a
`k`-point `y` of `T` is the cohomology on `C_k` of its pull-back along `y`. -/
private lemma finrank_fibreCohomology_ptT {T : Over (Spec (.of k))} (y : ptT k ⟶ T)
    (θ : Stacks.Picard.ofScheme (pullback X.f T.hom)) (p : (ptT k).left) (n : ℕ) :
    Module.finrank (T.left.residueField (y.left p))
        (Stacks.FibreCohomology.fibreCohomology (pullback.snd X.f T.hom)
          (Stacks.PicardCurve.rep θ) (y.left p) n) =
      Module.finrank k (cohomologyOverField k (bcProj X.f (ptT k))
        (Stacks.PicardCurve.rep (Stacks.Picard.schemePullbackClass (bcMap X.f y) θ)) n) := by
  have : Subsingleton (ptT k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso (bcMap X.f y) θ
  have hsq : IsPullback (bcMap X.f y) (bcProj X.f (ptT k)) (pullback.snd X.f T.hom)
      (Spec.map (T.left.descResidueField (Scheme.stalkClosedPointTo y.left)) ≫
        T.left.fromSpecResidueField (y.left (IsLocalRing.closedPoint k))) := by
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    exact bcMap_isPullback_proj X.f y
  exact (Stacks.FibreCohomology.finrank_eq_of_isPullback (K := k) (pullback.snd X.f T.hom)
    (Stacks.PicardCurve.rep θ) _ _ _ _ hsq _ e n).symm

/-- The fibre cohomology of a class on `C` is its cohomology after base change to `C_k`. -/
private lemma finrank_fibreCohomology_curve (N : Stacks.Picard.ofScheme X.C) (t : Spec (.of k))
    (n : ℕ) :
    Module.finrank ((Spec (.of k)).residueField t)
        (Stacks.FibreCohomology.fibreCohomology X.f (Stacks.PicardCurve.rep N) t n) =
      Module.finrank k (cohomologyOverField k (bcProj X.f (ptT k))
        (Stacks.PicardCurve.rep (Stacks.Picard.schemePullbackClass
          (pullback.fst X.f (ptT k).hom) N)) n) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain rfl : t = (ptT k).hom (IsLocalRing.closedPoint k) := Subsingleton.elim _ _
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
    (pullback.fst X.f (ptT k).hom) N
  have hsq : IsPullback (pullback.fst X.f (ptT k).hom) (bcProj X.f (ptT k)) X.f
      (Spec.map ((Spec (.of k)).descResidueField (Scheme.stalkClosedPointTo (ptT k).hom)) ≫
        (Spec (.of k)).fromSpecResidueField ((ptT k).hom (IsLocalRing.closedPoint k))) := by
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    exact IsPullback.of_hasPullback _ _
  exact (Stacks.FibreCohomology.finrank_eq_of_isPullback (K := k) X.f
    (Stacks.PicardCurve.rep N) _ _ _ _ hsq _ e n).symm

/-- **The theta-type family at a `k`-point**: if `ι(Spec k)` sends the class of `z` to `y`, then
`ξ + m pr₁^* x` pulls back along `y` to `z + m pr₁^* x` on `C_k`. -/
private lemma schemePullbackClass_bcMap_theta [IsAlgClosed k]
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (m : ℤ) (x : Stacks.Picard.ofScheme X.C) (y : ptT k ⟶ A.J)
    {z : Stacks.Picard.smallOfScheme (bc X.f (ptT k))}
    (hz : z ∈ (degree X.f (hdimX X) (ptT k)).ker)
    (hy : A.ι.app (op (ptT k)) (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
      QuotientAddGroup.mk (⟨z, hz⟩ : (degree X.f (hdimX X) (ptT k)).ker)) = y) :
    Stacks.Picard.schemePullbackClass (bcMap X.f y)
        (smallEquiv.{u} _ ξ + m • Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) x) =
      smallEquiv.{u} _ z +
        m • Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom) x := by
  rw [schemePullbackClass_add, schemePullbackClass_zsmul,
    Stacks.Picard.schemePullbackClass_comp, bcMap_fst,
    ← smallEquiv_smallSchemePullbackClassHom,
    smallSchemePullbackClassHom_bcMap_universal X A hξ hw y hz hy]

/-- **The theta-type family at the point `ι(c)`**: `ξ + m pr₁^* x` pulls back along `ι(c)` to
`pr₁^*(c + m x)` on `C_k`. -/
private lemma schemePullbackClass_bcMap_ιc [IsAlgClosed k]
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (m : ℤ) (x c : Stacks.Picard.ofScheme X.C)
    (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) :
    Stacks.Picard.schemePullbackClass (bcMap X.f (ιc X A c hc))
        (smallEquiv.{u} _ ξ + m • Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) x) =
      Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom) (c + m • x) := by
  have h1 := smallSchemePullbackClassHom_bcMap_universal X A hξ hw (ιc X A c hc) hc rfl
  rw [schemePullbackClass_add, schemePullbackClass_zsmul, schemePullbackClass_add,
    schemePullbackClass_zsmul, Stacks.Picard.schemePullbackClass_comp, bcMap_fst,
    ← smallEquiv_smallSchemePullbackClassHom, h1]
  congr 1
  exact AddEquiv.apply_symm_apply _ _

/-- **The normalized locus** ([MilAV, III, Lemma 6.7]; [Stacks, Tag 0B9Y]): a nonempty open
`V ⊆ J` such that `c + g [x₀]` has `h¹ = 0` and `h⁰ = 1` whenever `ι(c) ∈ V`. -/
private lemma exists_isOpen_normalized [IsAlgClosed k]
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J) :
    ∃ V : Set A.J.left, IsOpen V ∧ V.Nonempty ∧
      ∀ (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0),
        PtMem (ιc X A c hc) V →
          (∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
            (Stacks.FibreCohomology.fibreCohomology X.f
              (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 1) = 0) ∧
          (∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
            (Stacks.FibreCohomology.fibreCohomology X.f
              (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 0) = 1) := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  set Θ₁ := smallEquiv.{u} _ ξ + (genus X.f : ℤ) •
    Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀)
  have key : ∀ (c : Stacks.Picard.ofScheme X.C)
      (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0) (p : (ptT k).left) (n : ℕ),
      Module.finrank (A.J.left.residueField ((ιc X A c hc).left p))
        (Stacks.FibreCohomology.fibreCohomology (pullback.snd X.f A.J.hom)
          (Stacks.PicardCurve.rep Θ₁) ((ιc X A c hc).left p) n) =
      Module.finrank k (cohomologyOverField k (bcProj X.f (ptT k))
        (Stacks.PicardCurve.rep (Stacks.Picard.schemePullbackClass
          (pullback.fst X.f (ptT k).hom) (c + (genus X.f : ℤ) • classPt X x₀))) n) := by
    intro c hc p n
    rw [finrank_fibreCohomology_ptT, schemePullbackClass_bcMap_ιc X A hξ hw]
  refine ⟨_, Stacks.TwoAffineCech.isOpen_setOf_fibreCohomology_of_isPullback X.f U hU hUaff
    A.J.hom _ _ (IsPullback.of_hasPullback X.f A.J.hom) (Stacks.PicardCurve.rep Θ₁) 1, ?_, ?_⟩
  · have hθ : invertibleCurveDegreeHom k X.f
        (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)).le
        ((genus X.f : ℤ) • classPt X x₀) = genus X.f := by
      rw [map_zsmul, invertibleCurveDegreeHom_classPt_of_eq_single X x₀ hP]
      simp
    obtain ⟨c₀, hdeg, h0, h1⟩ :=
      exists_invertibleCurveDegreeHom_eq_zero_finrank_cohomologyOverField_eq_one k k X.f 0
        (map_zero _) _ hθ
    have hc : degree X.f (hdimX X) (ptT k) (zHom X c₀) = 0 :=
      funext fun t => (degree_zHom_apply X c₀ t).trans hdeg
    have hcl : Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom)
        (c₀ + (genus X.f : ℤ) • classPt X x₀) =
        0 + Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom) c₀ +
          Stacks.Picard.schemePullbackClass (pullback.fst X.f (ptT k).hom)
            ((genus X.f : ℤ) • classPt X x₀) := by
      rw [zero_add]
      exact map_add (Stacks.Picard.schemePullbackClassHom _) _ _
    refine ⟨(ιc X A c₀ hc).left (show (ptT k).left from IsLocalRing.closedPoint k), ?_, ?_⟩
    · rw [key, hcl]
      exact @Module.finrank_zero_of_subsingleton k _ _ _ _ _ (ModuleCat.subsingleton_of_isZero h1)
    · rw [key, hcl]
      exact h0
  · intro c hc hmem
    have h := hmem (show (ptT k).left from IsLocalRing.closedPoint k)
    refine ⟨fun t => ?_, fun t => ?_⟩
    all_goals rw [finrank_fibreCohomology_curve, ← key c hc (show (ptT k).left from
      IsLocalRing.closedPoint k)]
    exacts [h.1, h.2]

open Stacks.TwoAffineCech Stacks.FamilyFitting in
/-- **`H¹` vanishes off the Fitting divisor**: at a point `x` outside the support of the Fitting
ideal sheaf of `R¹pr_* M`, the fibre of `M` has `H¹ = 0`. -/
private lemma finrank_fibreCohomology_one_eq_zero_of_notMem_support
    (U : Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) {T : Scheme.{u}} (tT : T ⟶ Spec (.of k))
    (M : (pullback X.f tT).Modules) [Stacks.Ample.IsInvertibleModule _ M] {x : T}
    (hx : x ∉ (familyFitting X.f U hU hUaff tT M).support) :
    Module.finrank (T.residueField x)
      (Stacks.FibreCohomology.fibreCohomology (pullback.snd X.f tT) M x 1) = 0 := by
  classical
  obtain ⟨_, ⟨V₀, hV₀', rfl⟩, hxV₀, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV₀ : IsAffineOpen V₀ := hV₀'
  let := chartAlgebra tT hV₀.fromSpec
  have hA := isPullback_chart X.f tT hV₀.fromSpec
  have hsqT := isPullback_chartMap_snd X.f tT hV₀.fromSpec
  have : IsSeparated (pullback.snd X.f (hV₀.fromSpec ≫ tT)) :=
    isSeparated_of_isPullback' X.f _ _ hA
  have : IsProper (pullback.snd X.f (hV₀.fromSpec ≫ tT)) :=
    isProper_of_isPullback' X.f _ _ hA
  have : IsProper (pullback.snd X.f tT) := inferInstance
  have : ((Scheme.Modules.pullback (chartMap X.f tT hV₀.fromSpec)).obj M).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have : M.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  set p := hV₀.primeIdealOf ⟨x, hxV₀⟩
  set d := cechD (pullback.snd X.f (hV₀.fromSpec ≫ tT))
    (sqCover U (pullback.fst X.f (hV₀.fromSpec ≫ tT)))
    ((Scheme.Modules.pullback (chartMap X.f tT hV₀.fromSpec)).obj M)
  have hmodel := hasFiniteProjectiveModel_of_isPullback X.f U hU hUaff _ _ hA
    ((Scheme.Modules.pullback (chartMap X.f tT hV₀.fromSpec)).obj M)
  have := module_finite_coker_of_model hmodel
  have hI : (familyFitting X.f U hU hUaff tT M).ideal ⟨V₀, hV₀⟩ =
      fittingIdeal (R := Γ(T, V₀)) (M := coker d) ((0 : ℕ) : ℤ) := by
    rw [familyFitting_ideal, chartFitting, cechFitting, fittingCoker]
  have hp : p ∉ Module.support Γ(T, V₀) (coker d) := by
    rw [← (fittingIdeal_basic_properties.{u, u, u, u} (R := Γ(T, V₀))
      (M := coker d)).2.2.2.2.2.2.1]
    intro hmem
    apply hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hxV₀, hI,
      Scheme.mem_zeroLocus_iff]
    intro f hf hxf
    have h1 : (p : Spec Γ(T, V₀)) ∈ hV₀.fromSpec ⁻¹ᵁ T.basicOpen f := by
      change hV₀.fromSpec p ∈ T.basicOpen f
      rw [hV₀.fromSpec_primeIdealOf]
      exact hxf
    rw [hV₀.fromSpec_preimage_basicOpen] at h1
    exact h1 (hmem hf)
  have hsub : Subsingleton (TensorProduct Γ(T, V₀) p.asIdeal.ResidueField (coker d)) :=
    not_nontrivial_iff_subsingleton.1 fun h =>
      hp ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).2 h)
  have h1 := finrank_cohomologyOverField_one_eq (pullback.snd X.f (hV₀.fromSpec ≫ tT))
    (sqCover U (pullback.fst X.f (hV₀.fromSpec ≫ tT)))
    ((Scheme.Modules.pullback (chartMap X.f tT hV₀.fromSpec)).obj M)
    (iSup_sqCover U hU _) (isAffineOpen_sqCover X.f U hUaff _ _ hA) p
  rw [finrank_fibre_eq_fibreCohomology,
    Stacks.FibreCohomology.finrank_fibreCohomology_eq_of_isPullback
    (pullback.snd X.f tT) M _ _ _ hsqT _ (Iso.refl _) _ 1] at h1
  have hx' : hV₀.fromSpec (specPoint p) = x := hV₀.fromSpec_primeIdealOf ⟨x, hxV₀⟩
  rw [hx'] at h1
  rw [h1]
  have e := cokerBaseChangeEquiv d p.asIdeal.ResidueField
  rw [show Module.finrank p.asIdeal.ResidueField
      ((TensorProduct Γ(T, V₀) p.asIdeal.ResidueField _) ⧸ (LinearMap.baseChange _ d).range) =
      Module.finrank p.asIdeal.ResidueField (coker (LinearMap.baseChange p.asIdeal.ResidueField d))
      from rfl, e.finrank_eq]
  exact Module.finrank_zero_of_subsingleton

/-- The line bundle `𝒪(E)` of an effective Cartier divisor `E` on `C_k` has a nonzero global
section. -/
private lemma finrank_cohomologyOverField_picardClass_pos
    (E : (bc X.f (ptT k)).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E] :
    0 < Module.finrank k (cohomologyOverField k (bcProj X.f (ptT k))
      (Stacks.PicardCurve.rep (Stacks.Divisors.picardClass E)) 0) := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsIntegral (bc X.f (ptT k)) := isIntegral_bc_spec X.f _
  have : IsProper (bcProj X.f (ptT k)) := inferInstanceAs (IsProper (pullback.snd X.f _))
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_picardClass_iso (Stacks.Divisors.divisorSheaf E)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard E)
  have hs := divisorSheafGlobalSection_ne_zero E
  have : Nontrivial Γ(Stacks.PicardCurve.rep (Stacks.Divisors.picardClass E), ⊤) :=
    ⟨⟨e.inv.app ⊤ (Stacks.Divisors.divisorSheafGlobalSection E), 0, fun h => hs (by
      have key : Stacks.Divisors.divisorSheafGlobalSection E =
          e.hom.app ⊤ (e.inv.app ⊤ (Stacks.Divisors.divisorSheafGlobalSection E)) := by
        change _ = (e.inv ≫ e.hom).app ⊤ _
        rw [e.inv_hom_id]
        rfl
      rw [key, h, map_zero])⟩⟩
  have : Nontrivial (cohomologyOverField k (bcProj X.f (ptT k))
      (Stacks.PicardCurve.rep (Stacks.Divisors.picardClass E)) 0) :=
    (cohomologyOverFieldZeroEquivSections k _ _).nontrivial
  have : (Stacks.PicardCurve.rep (Stacks.Divisors.picardClass E)).IsCoherent := by
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field
      k (bcProj X.f (ptT k))
    have := (Stacks.Picard.picardRepresentative _ (Stacks.Divisors.picardClass E)).property
    exact Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (bc X.f (ptT k)) _
  have := finiteDimensional_cohomologyOverField_of_isProper k (bcProj X.f (ptT k))
    (Stacks.PicardCurve.rep (Stacks.Divisors.picardClass E)) 0
  exact Module.finrank_pos

open Stacks.FamilyFitting in
/-- **`Θ ⊆ Θ'` at closed points** ([MilAV, III, Lemma 6.7]): at a closed point `y` of the theta
divisor the theta family has `h¹ ≠ 0`, so `y` lies on its Fitting divisor. For `y = Σ j(Qᵢ)` the
fibre is `𝒪(Q₁ + ⋯ + Q_{g-1})`, which has a nonzero section, and `h⁰ = h¹` by Riemann–Roch. -/
private lemma mem_support_familyFitting_of_mem_thetaDivisor [IsAlgClosed k]
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    (hg : 1 ≤ genus X.f) {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    {y : A.J.left} (hy : y ∈ thetaDivisor X A hg j hj) (hyc : IsClosed ({y} : Set A.J.left)) :
    y ∈ (familyFitting X.f U hU hUaff A.J.hom (Stacks.PicardCurve.rep
      (smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
        Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀)))).support := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have := A.isAbelianVariety
  set Θc := smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
    Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀)
  by_contra hy'
  have h1 := finrank_fibreCohomology_one_eq_zero_of_notMem_support X U hU hUaff A.J.hom _ hy'
  -- a `k`-point of `C^{g-1}` over `y`
  set P := ∏ᶜ fun _ : Fin (genus X.f - 1) => Over.mk X.f
  set σ : P ⟶ A.J := (List.ofFn fun i : Fin (genus X.f - 1) =>
    Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i ≫ j).prod
  obtain ⟨p, hp⟩ : ∃ p, σ.left.base p = y := hy
  have : IsProper (Over.mk X.f).hom := (inferInstance : IsProper X.f)
  have : IsProper P.hom := Stacks.RigidifiedPicard.isProper_fibrePower_hom _ _
  have : LocallyOfFiniteType P.hom := inferInstance
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) P.hom
  have hF : IsClosed (σ.left.base ⁻¹' {y}) := hyc.preimage σ.left.continuous
  obtain ⟨p', hp'F, hp'c⟩ := nonempty_inter_closedPoints ⟨p, hp⟩ hF.isLocallyClosed
  obtain ⟨q, hq⟩ := exists_pt_of_isClosed P p' hp'c
  set pt : (ptT k).left := IsLocalRing.closedPoint k
  have hu : (q ≫ σ).left pt = y := by
    change σ.left (q.left pt) = y
    rw [hq]
    exact hp'F
  -- `q ≫ σ = ι(Σ cl(Qᵢ - P))`
  set Q : Fin (genus X.f - 1) → (ptT k ⟶ Over.mk X.f) := fun i =>
    q ≫ Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i
  let a : Fin (genus X.f - 1) → (degree X.f (hdimX X) (ptT k)).ker := fun i =>
    ⟨(smallEquiv.{u} _).symm (X.abelJacobiClass (Q i)),
      X.degree_abelJacobiClass_field (hdimX X) k (Q i)⟩
  set z := ∑ i, a i
  have hz : A.ι.app (op (ptT k)) (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
      QuotientAddGroup.mk (⟨z.1, z.2⟩ : (degree X.f (hdimX X) (ptT k)).ker)) = q ≫ σ := by
    have e1 : (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
        QuotientAddGroup.mk (⟨z.1, z.2⟩ : (degree X.f (hdimX X) (ptT k)).ker)) =
        (List.ofFn fun i => (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
          QuotientAddGroup.mk (a i))).sum := by
      rw [List.sum_ofFn]
      exact QuotientAddGroup.mk_sum (N := (Stacks.Picard.smallSchemePullbackClassHom
        (bcProj X.f (ptT k))).range.addSubgroupOf (degree X.f (hdimX X) (ptT k)).ker)
        (s := Finset.univ) (f := a)
    rw [e1]
    refine (A.ι_app_list_sum (ptT k) _).trans ?_
    rw [comp_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply]
    exact ((hj.comp_eq (hdimX X) k (Q i)).trans rfl).symm.trans (Category.assoc _ _ _)
  -- the fibre class
  set D : Fin (genus X.f - 1) → (bc X.f (ptT k)).IdealSheafData := fun i =>
    (X.pointFamily (Q i)).zeroDivisor
  have hD : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (D i) := fun i =>
    X.isEffectiveCartierDivisor_pointFamily (Q i)
  have hcl : Stacks.Picard.schemePullbackClass (bcMap X.f (q ≫ σ)) Θc =
      Stacks.Divisors.picardClass (∏ i ∈ Finset.univ, D i ^ (fun _ => 1) i) := by
    rw [schemePullbackClass_bcMap_theta X A hξ hw _ _ (q ≫ σ) z.2 hz,
      Stacks.Divisors.picardClass_prod_pow]
    have hz1 : smallEquiv.{u} _ z.1 = ∑ i, X.abelJacobiClass (Q i) := by
      rw [show z.1 = ∑ i, (a i).1 from AddSubgroup.val_finsetSum _ _ _, map_sum]
      exact Finset.sum_congr rfl fun i _ => AddEquiv.apply_symm_apply _ _
    rw [hz1]
    simp only [CurveWithDegreeOneDivisor.abelJacobiClass, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_one, one_smul]
    rw [classP_eq_classPt X x₀ hP, ← natCast_zsmul, Nat.cast_sub hg, Nat.cast_one]
    abel
  -- the fibre has a nonzero section
  have hpos : 0 < Module.finrank k (cohomologyOverField k (bcProj X.f (ptT k))
      (Stacks.PicardCurve.rep (Stacks.Picard.schemePullbackClass (bcMap X.f (q ≫ σ)) Θc)) 0) := by
    rw [hcl]
    exact finrank_cohomologyOverField_picardClass_pos X _
  have hRR := finrank_fibreCohomology_sub_eq X A.J Θc ((genus X.f : ℤ) - 1)
    (degree_thetaFamily X A x₀ hP hξ) y
  rw [← hu, finrank_fibreCohomology_ptT, finrank_fibreCohomology_ptT] at hRR
  rw [← hu, finrank_fibreCohomology_ptT] at h1
  omega

open Stacks.FamilyFitting in
/-- **`Θ' ≤ 𝓘_Θ`**: the Fitting divisor of the theta family vanishes on the prime divisor `Θ`,
which is reduced and whose closed points all lie on `Θ'`. -/
private lemma familyFitting_le_idealSheaf [IsAlgClosed k]
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    (hg : 1 ≤ genus X.f) {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (Z : Stacks.Divisors.PrimeDivisor A.J.left) (hZ : Z.support = thetaDivisor X A hg j hj) :
    familyFitting X.f U hU hUaff A.J.hom (Stacks.PicardCurve.rep
      (smallEquiv.{u} _ ξ + ((genus X.f : ℤ) - 1) •
        Stacks.Picard.schemePullbackClass (pullback.fst X.f A.J.hom) (classPt X x₀))) ≤
      Z.idealSheaf := by
  have := Z.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z.idealSheaf _ rfl,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  have hAV : IsAbelianVariety k A.J := A.isAbelianVariety
  have hV := hAV.toIsProperVariety.toIsVariety
  have : LocallyOfFiniteType A.J.hom := hV.toLocallyOfFiniteType
  have : JacobsonSpace A.J.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) A.J.hom
  intro y hy
  have hcl := closure_inter_closedPoints (X := A.J.left) Z.idealSheaf.support.isClosed
  have hy' : y ∈ closure ((Z.idealSheaf.support : Set A.J.left) ∩ closedPoints A.J.left) := by
    rwa [hcl]
  refine (Scheme.IdealSheafData.support _).isClosed.closure_subset_iff.2 ?_ hy'
  rintro y ⟨hy, hyc⟩
  exact mem_support_familyFitting_of_mem_thetaDivisor X A U hU hUaff x₀ hP hg hj hξ hw
    (show y ∈ thetaDivisor X A hg j hj from hZ ▸ hy) hyc

open Stacks.FamilyFitting in
/-- **The degree comparison** ([MilAV, III, Lemma 6.7]): for `N = c + g [x₀]` with `h¹ = 0` and
`h⁰ = 1`, the divisor `ψ_c⁻¹ Θ` contains `ψ_c⁻¹ Θ' = Z(s)`, which has degree `g`; so the degree
`d` of `ψ_c^*[𝒪(Θ)]` is at most `g`, and `ψ_c^*[𝒪(Θ)] = N` once `d = g`. -/
private lemma exists_degree_pullF_of_normalized [IsAlgClosed k]
    (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens) (hU : (⊤ : X.C.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    (hg : 1 ≤ genus X.f) {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {ξ : Stacks.Picard.smallOfScheme (bc X.f A.J)} (hξ : ξ ∈ (degree X.f (hdimX X) A.J).ker)
    (hw : A.ι.app (op A.J) (show (relativePicZeroFunctor k X.f).obj (op A.J) from
      QuotientAddGroup.mk (⟨ξ, hξ⟩ : (degree X.f (hdimX X) A.J).ker)) = 𝟙 A.J)
    (Z : Stacks.Divisors.PrimeDivisor A.J.left)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf]
    (hZ : Z.support = thetaDivisor X A hg j hj)
    (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0)
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f
        (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 1) = 0)
    (hN0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f
        (Stacks.PicardCurve.rep (c + (genus X.f : ℤ) • classPt X x₀)) t 0) = 1) :
    ∃ d : ℕ, d ≤ genus X.f ∧
      invertibleCurveDegreeHom k X.f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
        (pullF X j (Stacks.Divisors.picardClass Z.idealSheaf) (ιc X A c hc)) = d ∧
      (d = genus X.f → pullF X j (Stacks.Divisors.picardClass Z.idealSheaf) (ιc X A c hc) =
        c + (genus X.f : ℤ) • classPt X x₀) ∧
      (∀ S : Finset {x : X.C // IsClosed ({x} : Set X.C)},
        (∀ x ∈ S, X.f.residueDegree x.1 = 1) →
        (∀ x ∈ S, (constC X (ιc X A c hc) * j⁻¹).left x.1 ∈ Z.support) → S.card ≤ d) := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : Stacks.Divisors.IsEffectiveCartierDivisor (diagIdeal X.f) :=
    X.isEffectiveCartierDivisor_pointFamily (𝟙 _)
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  set N := c + (genus X.f : ℤ) • classPt X x₀
  have hNinv : SheafOfModules.IsInvertible X.C.sheaf.obj X.C.ringCatSheaf.property
      (Stacks.PicardCurve.rep N) := (Stacks.Picard.picardRepresentative _ N).property
  obtain ⟨s, hs⟩ := X.exists_section_ne_zero U hU hUaff (Stacks.PicardCurve.rep N) hN1 hN0
  have hcomap := familyFitting_thetaFamily_comap X A U hU hUaff hj x₀ hP hξ hw c hc s hs hN1
    hN0
  set ψ := constC X (ιc X A c hc) * j⁻¹
  set D := AlgebraicGeometry.zeroScheme X.C (Stacks.PicardCurve.rep N) s
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero
      (L := Stacks.PicardCurve.rep N) s hs
  set E : X.C.IdealSheafData := Z.idealSheaf.comap ψ.left
  have hDE : D ≤ E := hcomap ▸ Scheme.IdealSheafData.comap_mono ψ.left
    (familyFitting_le_idealSheaf X A U hU hUaff x₀ hP hg hj hξ hw Z hZ)
  have : IsNoetherian X.C := isNoetherian_of_locallyOfFiniteType (Y := Spec (.of k)) X.f
  have hreg : IsRegular X.C := isRegular_of_smooth_over_regular X.f
  have hDne : (D.support : Set X.C) ≠ Set.univ := fun h => by
    have hmem := Set.mem_univ (genericPoint X.C)
    rw [← h] at hmem
    exact genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hD hmem
  have hcart : ∀ I : X.C.IdealSheafData, I.support ≤ D.support →
      Stacks.Divisors.IsEffectiveCartierDivisor I :=
    fun I hI => isEffectiveCartierDivisor_of_isRegular_of_support_ne_univ hdimC hreg I
      (fun h => hDne (Set.eq_univ_of_univ_subset (h ▸ hI)))
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor E :=
    hcart E (Scheme.IdealSheafData.support_antitone hDE)
  have hpb : Stacks.Divisors.picardClass E =
      pullF X j (Stacks.Divisors.picardClass Z.idealSheaf) (ιc X A c hc) :=
    (Stacks.Zeta.schemePullbackClass_picardClass_comap _ _ hE).symm
  have hDcl : Stacks.Divisors.picardClass D = N :=
    (AlgebraicGeometry.picardClass_zeroScheme (Stacks.PicardCurve.rep N)
      (Stacks.Picard.picardRepresentative _ N).property s).trans
        (Stacks.Picard.classOf_picardRepresentative _ _)
  have hdegN : invertibleCurveDegreeHom k X.f hdimC N = genus X.f := by
    have h0 := (degree_zHom_apply X c (IsLocalRing.closedPoint k)).symm.trans
      (congrFun hc (IsLocalRing.closedPoint k))
    rw [map_add, map_zsmul, invertibleCurveDegreeHom_classPt_of_eq_single X x₀ hP]
    simp only [smul_eq_mul, mul_one]
    rw [show invertibleCurveDegreeHom k X.f hdimC c = 0 from h0, zero_add]
  have : IsIntegral X.C := inferInstance
  obtain ⟨dE, hdE, -⟩ :=
    exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree k X.f hdimC E
      (hD := hE)
  obtain ⟨dD, hdD, -⟩ :=
    exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree k X.f hdimC D
  have := hdE
  have := hdD
  obtain ⟨R, hR, hRr⟩ := exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le X.f E D dE dD hDE
  have hRc : Stacks.Divisors.IsEffectiveCartierDivisor R := hcart R (by
    rw [hR, Scheme.IdealSheafData.support_mul]
    exact le_sup_right)
  have hcls : Stacks.Divisors.picardClass D =
      Stacks.Divisors.picardClass E + Stacks.Divisors.picardClass R := by
    rw [Stacks.Divisors.picardClass_congr hR, Stacks.Divisors.picardClass_mul]
  have hdegE := X.invertibleCurveDegreeHom_picardClass_of_rank E hdE
  have hdegR := X.invertibleCurveDegreeHom_picardClass_of_rank R hRr
  have hdegD := X.invertibleCurveDegreeHom_picardClass_of_rank D hdD
  have key : (dD : ℤ) = dE + ((dD - dE : ℕ) : ℤ) := by
    rw [← hdegD, hcls, map_add, hdegE, hdegR]
  have hdDg : (dD : ℤ) = genus X.f := by rwa [← hdegD, hDcl]
  refine ⟨dE, by omega, by rw [← hpb]; exact hdegE, fun hdg => ?_, fun S hS1 hSZ => ?_⟩
  swap
  · have h := X.card_le_invertibleCurveDegreeHom_picardClass S hS1 E (fun x hx => by
      change x.1 ∈ (Z.idealSheaf.comap ψ.left).support
      rw [Scheme.IdealSheafData.support_comap]
      exact hSZ x hx)
    rw [hdegE] at h
    exact_mod_cast h
  rw [show dD - dE = 0 by omega] at hRr
  rw [← hpb, ← hDcl, hcls, picardClass_eq_zero_of_rank_zero X.f R hRr, add_zero]

/-- **Every `k`-point of `J` is a sum of `g` points of `j(C)`**: for `y = ι(c)`, the class
`c + g [P]` has degree `g`, so by Riemann–Roch it is the class of an effective divisor of degree
`g`, which is a sum of `g` rational points as `k` is algebraically closed. -/
private lemma exists_list_prod_comp_eq [IsAlgClosed k]
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j) (y : ptT k ⟶ A.J) :
    ∃ Q : Fin (genus X.f) → (ptT k ⟶ Over.mk X.f), (List.ofFn fun i => Q i ≫ j).prod = y := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_ιc_eq X A y
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  let T := ptT k
  let π : bc X.f T ⟶ Spec (.of k) := bcProj X.f T
  have : SmoothOfRelativeDimension 1 π :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have : IsIntegral (bc X.f T) := isIntegral_bc_spec X.f _
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop) :=
    isIso_globalSections_bc_spec X.f (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  set N := Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom)
    (c + (genus X.f : ℤ) • X.classP)
  have hc0 : invertibleCurveDegreeHom k X.f hdimC c = 0 :=
    (degree_zHom_apply X c (IsLocalRing.closedPoint k)).symm.trans
      (congrFun hc (IsLocalRing.closedPoint k))
  have hN : invertibleCurveDegreeHom k π hdimT N = genus X.f := by
    rw [invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k k
      (IsPullback.of_hasPullback X.f T.hom) hdimC hdimT, map_add, map_zsmul,
      X.invertibleCurveDegreeHom_classP, hc0]
    simp
  have hgen : genus π = genus X.f := genus_bc_spec X.f _
  obtain ⟨D, hD, d, hrank, hd, hclass⟩ :=
    exists_isEffectiveCartierDivisor_picardClass_eq k π hdimT N (by rw [hN, hgen])
  have hdg : d = genus X.f := by rw [hN] at hd; exact_mod_cast hd
  let Zh : Stacks.Hilbert.HilbertFamily (Over.mk X.f) T (genus X.f) := ⟨D, hdg ▸ hrank⟩
  obtain ⟨x, hx⟩ := Stacks.Hilbert.exists_familyOfPoints_eq_of_isAlgClosed (Over.mk X.f) T.hom _ Zh
  refine ⟨x, ?_⟩
  have hC : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i)) := fun i =>
    X.isEffectiveCartierDivisor_pointFamily (x i)
  have hDprod : D = ∏ i ∈ Finset.univ,
      Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i) ^ (fun _ => 1) i := by
    have := congrArg Stacks.Hilbert.HilbertFamily.ideal hx
    rw [Stacks.Hilbert.familyOfPoints_ideal] at this
    simp only [pow_one]
    exact this.symm
  have hsum : Stacks.Divisors.picardClass D =
      ∑ i, Stacks.Divisors.picardClass (Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i)) := by
    have hI : Stacks.Divisors.IsEffectiveCartierDivisor (∏ i ∈ Finset.univ,
        Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i) ^ (fun _ => 1) i) :=
      @Stacks.Divisors.IsEffectiveCartierDivisor.finsetProdPow _ _ Finset.univ
        (fun i => Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i)) (fun _ => 1) hC
    have h := @Stacks.Divisors.picardClass_prod_pow _ _ Finset.univ
      (fun i => Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i)) (fun _ => 1) hC
    rw [@Stacks.Divisors.picardClass_congr _ _ _ hDprod hD hI]
    refine h.trans ?_
    simp only [Nat.cast_one, one_smul]
  let a : Fin (genus X.f) → (degree X.f (hdimX X) (ptT k)).ker := fun i =>
    ⟨(smallEquiv.{u} _).symm (X.abelJacobiClass (x i)),
      X.degree_abelJacobiClass_field (hdimX X) k (x i)⟩
  have hz : zHom X c = (∑ i, a i).1 := by
    rw [AddSubgroup.val_finsetSum]
    apply (smallEquiv.{u} _).injective
    rw [map_sum]
    simp only [a, AddEquiv.apply_symm_apply]
    rw [show smallEquiv.{u} _ (zHom X c) = Stacks.Picard.schemePullbackClass
      (pullback.fst X.f T.hom) c from AddEquiv.apply_symm_apply _ _]
    simp only [CurveWithDegreeOneDivisor.abelJacobiClass, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h2 : (∑ i, Stacks.Divisors.picardClass (Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i)))
        = N := hsum.symm.trans hclass
    refine Eq.trans ?_ (congrArg (fun s => s - genus X.f •
      Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) X.classP) h2.symm)
    rw [← natCast_zsmul]
    change _ = Stacks.Picard.schemePullbackClassHom _ (c + (genus X.f : ℤ) • X.classP) - _
    rw [map_add, map_zsmul]
    exact (add_sub_cancel_right _ _).symm
  have h1 : ιc X A c hc = A.ι.app (op (ptT k))
      (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
        QuotientAddGroup.mk (∑ i, a i)) := by
    change A.ι.app _ _ = A.ι.app _ _
    congr 1
    exact congrArg QuotientAddGroup.mk (Subtype.ext hz)
  rw [h1]
  have e1 : (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
      QuotientAddGroup.mk (∑ i, a i)) =
      (List.ofFn fun i => (show (relativePicZeroFunctor k X.f).obj (op (ptT k)) from
        QuotientAddGroup.mk (a i))).sum := by
    rw [List.sum_ofFn]
    exact QuotientAddGroup.mk_sum (N := (Stacks.Picard.smallSchemePullbackClassHom
      (bcProj X.f (ptT k))).range.addSubgroupOf (degree X.f (hdimX X) (ptT k)).ker)
      (s := Finset.univ) (f := a)
  rw [e1]
  refine Eq.symm ((A.ι_app_list_sum (ptT k) _).trans ?_)
  rw [List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact ((hj.comp_eq (hdimX X) k (x i)).trans rfl).symm

/-- The image of a `k`-point of a separated `k`-scheme is a closed point. -/
private lemma isClosed_singleton_left_apply {Y : Over (Spec (.of k))} [IsSeparated Y.hom]
    (x : ptT k ⟶ Y) (p : (ptT k).left) : IsClosed ({x.left p} : Set Y.left) := by
  have := isIso_ptT_hom k
  have : Subsingleton (ptT k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : IsProper (x.left ≫ Y.hom) := by rw [Over.w x]; infer_instance
  have : IsProper x.left := .of_comp _ Y.hom
  have h := x.left.isClosedMap.isClosed_range
  have e : Set.range x.left.base = {x.left p} := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rwa [e] at h

/-- A nonempty open subset of `C` contains a rational point outside a given finite set of
closed points: it contains the generic point, which is not closed as `dim C = 1`. -/
private lemma exists_ptT_mem_open_notMem [IsAlgClosed k] {O : Set X.C} (hO : IsOpen O)
    (hne : O.Nonempty) (F : Finset X.C) (hF : ∀ z ∈ F, IsClosed ({z} : Set X.C)) :
    ∃ x : ptT k ⟶ Over.mk X.f, ∀ p, x.left p ∈ O ∧ x.left p ∉ F := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsIntegral X.C := inferInstance
  have hη : genericPoint X.C ∉ F := by
    intro hη
    have hcl : closure ({genericPoint X.C} : Set X.C) = Set.univ := (genericPoint_spec X.C).def
    rw [(hF _ hη).closure_eq] at hcl
    have : Subsingleton X.C := ⟨fun a b => by
      have ha : a ∈ ({genericPoint X.C} : Set X.C) := hcl ▸ Set.mem_univ a
      have hb : b ∈ ({genericPoint X.C} : Set X.C) := hcl ▸ Set.mem_univ b
      exact ha.trans hb.symm⟩
    have : DiscreteTopology X.C := ⟨Subsingleton.elim _ _⟩
    have h0 : topologicalKrullDim X.C = 0 :=
      topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
    have h1 : topologicalKrullDim X.C = ((1 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 X.f
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hFc : IsClosed (F : Set X.C) := by
    rw [← Set.biUnion_of_singleton (F : Set X.C)]
    exact F.finite_toSet.isClosed_biUnion fun z hz => hF z hz
  have hW : IsOpen (O ∩ (F : Set X.C)ᶜ) := hO.inter hFc.isOpen_compl
  have hWne : (O ∩ (F : Set X.C)ᶜ).Nonempty :=
    ⟨genericPoint X.C, ((genericPoint_spec X.C).mem_open_set_iff hO).2 (by simpa using hne), hη⟩
  have : LocallyOfFiniteType X.f := inferInstance
  have : JacobsonSpace X.C := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) X.f
  obtain ⟨z, hzW, hzc⟩ := nonempty_inter_closedPoints hWne hW.isLocallyClosed
  have : LocallyOfFiniteType (Over.mk X.f).hom := (inferInstance : LocallyOfFiniteType X.f)
  obtain ⟨x, hx⟩ := exists_pt_of_isClosed (Over.mk X.f) z hzc
  exact ⟨x, fun p => (hx p) ▸ hzW⟩

omit [Field k] in
/-- Replacing one factor of a product in a commutative group. -/
private lemma list_prod_ofFn_update {G : Type*} [CommGroup G] {n : ℕ} (f : Fin n → G)
    (i : Fin n) (b : G) :
    (List.ofFn (Function.update f i b)).prod = (List.ofFn f).prod * (f i)⁻¹ * b := by
  classical
  rw [List.prod_ofFn, List.prod_ofFn, Finset.prod_update_of_mem (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    mul_comm (f i), mul_inv_cancel_right, mul_comm]

omit [Field k] in
/-- Splitting off one factor of a product over `Fin N`, `N ≥ 1`. -/
private lemma prod_univ_eq_mul_prod_succAbove {G : Type*} [CommMonoid G] {N : ℕ} (hN : 1 ≤ N)
    (f : Fin N → G) (l : Fin N) :
    ∏ l₀, f l₀ = f l * ∏ m : Fin (N - 1),
      f (Fin.cast (by omega) ((Fin.cast (by omega) l : Fin (N - 1 + 1)).succAbove m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact Fin.prod_univ_succAbove f l

/-- **One perturbation step**: a factor `Qᵢ` of a product `Σ j(Q_l) ∈ V` can be moved off a
given finite set of closed points, keeping the product in `V`. -/
private lemma exists_update_ptMem [IsAlgClosed k] (j : Over.mk X.f ⟶ A.J) {V : Set A.J.left}
    (hVo : IsOpen V) {n : ℕ} (Q : Fin n → (ptT k ⟶ Over.mk X.f))
    (hQ : PtMem (List.ofFn fun l => Q l ≫ j).prod V) (i : Fin n) (F : Finset X.C)
    (hF : ∀ z ∈ F, IsClosed ({z} : Set X.C)) :
    ∃ x : ptT k ⟶ Over.mk X.f, (∀ p, x.left p ∉ F) ∧
      PtMem (List.ofFn fun l => Function.update Q i x l ≫ j).prod V := by
  classical
  have := A.isAbelianVariety
  have hAV : IsAbelianVariety k A.J := inferInstance
  have : IsProper A.J.hom := hAV.toIsProperVariety.toIsProper
  have : GeometricallyIntegral A.J.hom := hAV.toGeometricallyIntegral
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral _
  set y := (List.ofFn fun l => Q l ≫ j).prod
  set φ : Over.mk X.f ⟶ A.J := constC X (y * (Q i ≫ j)⁻¹) * j
  have hφ : ∀ x : ptT k ⟶ Over.mk X.f, x ≫ φ = y * (Q i ≫ j)⁻¹ * (x ≫ j) := by
    intro x
    rw [MonObj.comp_mul, constC, ← Category.assoc, hom_ptT_ext (x ≫ _) (𝟙 _), Category.id_comp]
  have hupd : ∀ x : ptT k ⟶ Over.mk X.f,
      (List.ofFn fun l => Function.update Q i x l ≫ j).prod = y * (Q i ≫ j)⁻¹ * (x ≫ j) := by
    intro x
    have e : (fun l => Function.update Q i x l ≫ j) =
        Function.update (fun l => Q l ≫ j) i (x ≫ j) := by
      funext l
      by_cases h : l = i
      · subst h
        simp
      · simp [h]
    rw [e, list_prod_ofFn_update]
  have hO : IsOpen (φ.left.base ⁻¹' V) := hVo.preimage φ.left.continuous
  have hne : (φ.left.base ⁻¹' V).Nonempty := by
    refine ⟨(Q i).left (IsLocalRing.closedPoint k), ?_⟩
    change (Q i ≫ φ).left (IsLocalRing.closedPoint k) ∈ V
    rw [hφ, inv_mul_cancel_right]
    exact hQ _
  obtain ⟨x, hx⟩ := exists_ptT_mem_open_notMem X hO hne F hF
  refine ⟨x, fun p => (hx p).2, fun p => ?_⟩
  rw [hupd, ← hφ]
  exact (hx p).1

/-- **A normalized point with `g` distinct rational points on `ψ⁻¹ Θ`**: in a nonempty open
`V ⊆ J` there is `ι(c)` with `c = cl(Q₁ + ⋯ + Q_g - g P₀)` for distinct `Qᵢ ∈ C(k)`; then
`ψ_c(Qᵢ) = Σ_{l ≠ i} j(Q_l)` lies on `Θ`. -/
private lemma exists_ptMem_finset_mem_thetaDivisor [IsAlgClosed k]
    (hg : 1 ≤ genus X.f) {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    {V : Set A.J.left} (hVo : IsOpen V) (hVne : V.Nonempty) :
    ∃ (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0),
      PtMem (ιc X A c hc) V ∧
      ∃ S : Finset {x : X.C // IsClosed ({x} : Set X.C)}, S.card = genus X.f ∧
        (∀ x ∈ S, X.f.residueDegree x.1 = 1) ∧
        (∀ x ∈ S, (constC X (ιc X A c hc) * j⁻¹).left x.1 ∈ thetaDivisor X A hg j hj) := by
  classical
  have := A.isAbelianVariety
  have hAV : IsAbelianVariety k A.J := inferInstance
  have : IsProper A.J.hom := hAV.toIsProperVariety.toIsProper
  have : GeometricallyIntegral A.J.hom := hAV.toGeometricallyIntegral
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral _
  have : IsSeparated (Over.mk X.f).hom := (inferInstance : IsSeparated X.f)
  have hV := hAV.toIsProperVariety.toIsVariety
  have : LocallyOfFiniteType A.J.hom := hV.toLocallyOfFiniteType
  have : JacobsonSpace A.J.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) A.J.hom
  set pt : (ptT k).left := IsLocalRing.closedPoint k
  -- a rational point of `V`, written as a sum of `g` points of `j(C)`
  obtain ⟨v, hvV, hvc⟩ := nonempty_inter_closedPoints hVne hVo.isLocallyClosed
  obtain ⟨y₀, hy₀⟩ := exists_pt_of_isClosed A.J v hvc
  obtain ⟨Q₀, hQ₀⟩ := exists_list_prod_comp_eq X A hj y₀
  -- move the points apart one at a time
  have key : ∀ m : ℕ, ∃ Q : Fin (genus X.f) → (ptT k ⟶ Over.mk X.f),
      PtMem (List.ofFn fun l => Q l ≫ j).prod V ∧
      ∀ l l' : Fin (genus X.f), l.val < m → l'.val < m → (Q l).left pt = (Q l').left pt →
        l = l' := by
    intro m
    induction m with
    | zero =>
      refine ⟨Q₀, fun p => ?_, fun l l' hl => absurd hl (Nat.not_lt_zero _)⟩
      rw [hQ₀, hy₀]
      exact hvV
    | succ m ih =>
      obtain ⟨Q, hQ, hinj⟩ := ih
      by_cases hm : m < genus X.f
      · set i : Fin (genus X.f) := ⟨m, hm⟩
        set F := (Finset.univ.erase i).image fun l => (Q l).left pt
        have hF : ∀ z ∈ F, IsClosed ({z} : Set X.C) := by
          intro z hz
          obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hz
          exact isClosed_singleton_left_apply (Q l) pt
        obtain ⟨x, hxF, hx⟩ := exists_update_ptMem X A j hVo Q hQ i F hF
        refine ⟨Function.update Q i x, hx, fun l l' hl hl' he => ?_⟩
        have hmemF : ∀ l, l ≠ i → (Q l).left pt ∈ F := fun l hl =>
          Finset.mem_image.2 ⟨l, Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩, rfl⟩
        by_cases hli : l = i <;> by_cases hli' : l' = i
        · rw [hli, hli']
        · exfalso
          rw [hli, Function.update_self, Function.update_of_ne hli'] at he
          exact hxF pt (he ▸ hmemF l' hli')
        · exfalso
          rw [hli', Function.update_self, Function.update_of_ne hli] at he
          exact hxF pt (he.symm ▸ hmemF l hli)
        · rw [Function.update_of_ne hli, Function.update_of_ne hli'] at he
          have h1 : l.val ≠ m := fun h => hli (Fin.ext h)
          have h2 : l'.val ≠ m := fun h => hli' (Fin.ext h)
          exact hinj l l' (by omega) (by omega) he
      · exact ⟨Q, hQ, fun l l' hl hl' => hinj l l' (by omega) (by omega)⟩
  obtain ⟨Q, hQ, hinj⟩ := key (genus X.f)
  have hinj' : Function.Injective fun l => (Q l).left pt := fun l l' h =>
    hinj l l' l.2 l'.2 h
  set y := (List.ofFn fun l => Q l ≫ j).prod
  obtain ⟨c, hc, hcy⟩ := exists_ιc_eq X A y
  refine ⟨c, hc, hcy ▸ hQ, ?_⟩
  let pts : Fin (genus X.f) → {x : X.C // IsClosed ({x} : Set X.C)} := fun l =>
    ⟨(Q l).left pt, isClosed_singleton_left_apply (Q l) pt⟩
  refine ⟨Finset.univ.image pts, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun l l' h => hinj' (congrArg Subtype.val h)),
      Finset.card_univ, Fintype.card_fin]
  · intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    have hσ : (Q l).left ≫ X.f = 𝟙 _ := by
      have h := Over.w (Q l)
      rwa [show (ptT k).hom = 𝟙 _ by
        change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
        rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
        rfl] at h
    exact (Stacks.Chow.residueDegree_eq_one_of_section X.f (Q l).left hσ pt).1
  · intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    rw [hcy]
    change (Q l ≫ (constC X y * j⁻¹)).left pt ∈ thetaDivisor X A hg j hj
    have h1 : Q l ≫ (constC X y * j⁻¹) = y * (Q l ≫ j)⁻¹ := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, constC, ← Category.assoc,
        hom_ptT_ext (Q l ≫ _) (𝟙 _), Category.id_comp]
    rw [h1]
    let e : Fin (genus X.f - 1) → Fin (genus X.f) := fun m =>
      Fin.cast (by omega) ((Fin.cast (by omega) l : Fin (genus X.f - 1 + 1)).succAbove m)
    let q' : ptT k ⟶ ∏ᶜ fun _ : Fin (genus X.f - 1) => Over.mk X.f :=
      Pi.lift fun m => Q (e m)
    refine ⟨q'.left pt, ?_⟩
    change (q' ≫ (List.ofFn fun i : Fin (genus X.f - 1) =>
      Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i ≫ j).prod).left pt = _
    congr 2
    rw [comp_list_prod, List.map_ofFn]
    have e2 : ((fun x => q' ≫ x) ∘ fun i : Fin (genus X.f - 1) =>
        Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i ≫ j) = fun m => Q (e m) ≫ j := by
      funext m
      simp only [Function.comp_apply, q', Pi.lift_π_assoc]
    rw [e2, List.prod_ofFn]
    have e3 : y = (Q l ≫ j) * ∏ m : Fin (genus X.f - 1), (Q (e m) ≫ j) := by
      change (List.ofFn fun l => Q l ≫ j).prod = _
      rw [List.prod_ofFn]
      exact prod_univ_eq_mul_prod_succAbove hg (fun l => Q l ≫ j) l
    rw [e3, mul_comm, inv_mul_cancel_left]

/-- **The generic case** ([MilAV, III, Lemma 6.7]): for `a = ι(c)` in a dense open subset of `J`,
`(a - j)^* 𝒪_J(Θ) = c + g [P₀]`. -/
private lemma exists_isOpen_pullF_eq [IsAlgClosed k] (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1)
    (hg : 1 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (Z : Stacks.Divisors.PrimeDivisor A.J.left)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf]
    (hZ : Z.support = thetaDivisor X A hg j hj) :
    ∃ U : Set A.J.left, IsOpen U ∧ U.Nonempty ∧
      ∀ (c : Stacks.Picard.ofScheme X.C) (hc : degree X.f (hdimX X) (ptT k) (zHom X c) = 0),
        PtMem (ιc X A c hc) U →
          pullF X j (Stacks.Divisors.picardClass Z.idealSheaf) (ιc X A c hc) =
            c + (genus X.f : ℤ) • classPt X x₀ := by
  have := A.isAbelianVariety
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  obtain ⟨U, hU, hUaff⟩ := exists_twoAffineCover X
  obtain ⟨w, hw⟩ := exists_ι_app_eq_id X A
  induction w using QuotientAddGroup.induction_on with | H zz => ?_
  obtain ⟨ξ, hξ⟩ := zz
  obtain ⟨V, hVo, hVne, hV⟩ := exists_isOpen_normalized X A U hU hUaff x₀ hP hξ hw
  have hdeg := fun c hc (hcV : PtMem (ιc X A c hc) V) =>
    exists_degree_pullF_of_normalized X A U hU hUaff x₀ hP hg hj hξ hw Z hZ c hc
      (hV c hc hcV).1 (hV c hc hcV).2
  set θ := Stacks.Divisors.picardClass Z.idealSheaf
  set deg := invertibleCurveDegreeHom k X.f hdimC
  -- the degree is bounded on `V`
  have hbound : ∀ a : ptT k ⟶ A.J, PtMem a V →
      0 ≤ deg (pullF X j θ a) ∧ deg (pullF X j θ a) ≤ genus X.f := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := exists_ιc_eq X A a
    obtain ⟨d, hdg, hd, -, -⟩ := hdeg c hc ha
    rw [hd]
    exact ⟨by positivity, by exact_mod_cast hdg⟩
  -- and constant, by the theorem of the cube
  set e : (ptT k ⟶ A.J) → ℤ := fun a => deg (pullF X j θ a) - deg (pullF X j θ 1)
  have he : ∀ a b, e (a * b) = e a + e b := by
    intro a b
    have h := congrArg deg (pullF_mul X j θ a b)
    rw [map_add, map_add] at h
    simp only [e]
    linarith
  have hconst : ∀ a, e a = 0 := by
    intro a
    have hpow : ∀ n : ℕ, e (a ^ n) = n * e a := by
      intro n
      induction n with
      | zero => simp [e]
      | succ n ih => rw [pow_succ, he, ih]; push_cast; ring
    have hb : ∀ n : ℕ, |e (a ^ n)| ≤ genus X.f := by
      intro n
      obtain ⟨u, hu, hau⟩ := exists_ptMem_mul A.J hVo hVne hVo hVne (a ^ n)
      have h1 := he (a ^ n) u
      have h2 := hbound u hu
      have h3 := hbound _ hau
      simp only [e] at h1 ⊢
      rw [abs_le]
      constructor <;> linarith
    by_contra hne
    have h := hb (genus X.f + 1)
    rw [hpow, abs_mul] at h
    have h1 : (1 : ℤ) ≤ |e a| := Int.one_le_abs hne
    have h2 : (0 : ℤ) ≤ |((genus X.f + 1 : ℕ) : ℤ)| := abs_nonneg _
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((genus X.f + 1 : ℕ) : ℤ))] at h
    push_cast at h
    nlinarith
  -- a normalized point where the degree is `g`
  obtain ⟨c₀, hc₀, hc₀V, S, hScard, hS1, hSZ⟩ :=
    exists_ptMem_finset_mem_thetaDivisor X A hg hj hVo hVne
  obtain ⟨d₀, hd₀g, hd₀, -, hd₀S⟩ := hdeg c₀ hc₀ hc₀V
  have hd₀' : d₀ = genus X.f :=
    le_antisymm hd₀g (hScard ▸ hd₀S S hS1 fun x hx => hZ ▸ hSZ x hx)
  refine ⟨V, hVo, hVne, fun c hc hcV => ?_⟩
  obtain ⟨d, -, hd, hdN, -⟩ := hdeg c hc hcV
  apply hdN
  have h1 := hconst (ιc X A c hc)
  have h2 := hconst (ιc X A c₀ hc₀)
  simp only [e] at h1 h2
  rw [hd] at h1
  rw [hd₀, hd₀'] at h2
  omega

end Generic

/-- **Pull-back of translates of `Θ⁻`** ([MilAV, III, Lemma 6.8(a)]). Let `k` be algebraically
closed, `X = (C, P₀)` a curve over `k` with a point `P₀ = x₀`, of genus `g ≥ 1`, `A = (J, ι)` a
Jacobian of `C`, `j = j_{P₀}` the Abel–Jacobi map and `Z` the prime divisor of `J` with support
the theta divisor `Faltings.thetaDivisor X A hg j hj`, where `ι` is assumed additive (`hι`).
Let `a ∈ J(k)` and let `D` be an effective divisor of degree `g` on `C` with `cl(D - g P₀) = a`.
Then the pull-back of `𝒪_J(Θ)` along `x ↦ a - j(x)`, that is `j^* 𝒪_J(Θ⁻ + a)`, is the class of
`𝒪_C(D)` in `Pic(C)`. -/
@[faltings "lem_nt_pullback_theta_translates"]
public theorem schemePullbackClass_thetaDivisor_translate_eq [IsAlgClosed k]
    (X : CurveWithDegreeOneDivisor k) (x₀ : {x : X.C // IsClosed ({x} : Set X.C)})
    (hP : X.P = Finsupp.single x₀ 1) (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (Z : Stacks.Divisors.PrimeDivisor A.J.left)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf]
    (hZ : Z.support = thetaDivisor X A hg j hj)
    (D : {x : X.C // IsClosed ({x} : Set X.C)} →₀ ℤ) (hD₀ : 0 ≤ D)
    (hDdeg : (D.sum fun x n => n * (X.f.residueDegree x.1 : ℤ)) = genus X.f)
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k))) ⟶ A.J) :
    let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    /- The class `[𝒪_C(D)] = ∑ D x • [𝒪_C(x)]` in `Pic(C)`. -/
    let classD : Stacks.Picard.ofScheme X.C := D.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    /- The class `[𝒪_C(P₀)]` in `Pic(C)`. -/
    let classP₀ : Stacks.Picard.ofScheme X.C :=
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x₀
      Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x₀)
    /- `cl(D - g P₀)`, pulled back to `C_k = C ×_k Spec k`. -/
    let z : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom)
        (classD - (genus X.f : ℤ) • classP₀))
    (∀ hdeg : degree X.f hdim T z = 0,
      a = A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T).ker))) →
    /- `x ↦ a - j(x)`, the composite of `j` with `x ↦ a - x`. -/
    let ψ : Over.mk X.f ⟶ A.J :=
      (Over.homMk (U := Over.mk X.f) (V := T) X.f (by simp [T, Algebra.algebraMap_self]) ≫ a) *
        j⁻¹
    Stacks.Picard.schemePullbackClass ψ.left (Stacks.Divisors.picardClass Z.idealSheaf) =
      classD := by
  intro T hdim classD classP₀ z ha ψ
  obtain ⟨U, hU, hU', hgen⟩ := exists_isOpen_pullF_eq X A x₀ hP hg j hj Z hZ
  have hc := degree_zHom_classD X x₀ hP D hDdeg
  have ha' : a = ιc X A _ hc := ha hc
  subst ha'
  exact (pullF_ιc_eq_of_isOpen X A hι j _ x₀ hU hU' hgen _ hc).trans (sub_add_cancel _ _)

end Faltings
