module
public import Mordell.Jacobian.Theta.Basic
public import Mordell.Jacobian.Dimension
public import Mordell.Jacobian.Points
public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CodimensionOne
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.AmbientCurveResolution
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions

/-!
# The theta divisor is a prime divisor

Let `(C, P)` be a curve over a field `k` with a divisor of degree one, of genus `g ≥ 1`, let
`(J, ι)` be a Jacobian of `C` and `j = j_P` the Abel–Jacobi map. The theta divisor
`Θ = W^{g-1} ⊆ J`, the image of `C^{g-1}` under `(Q₁, …, Q_{g-1}) ↦ j(Q₁) + ⋯ + j(Q_{g-1})`,
is a prime divisor of `J`: it is the support of an integral closed subscheme of codimension one.

The proof is a dimension count. For `r ≥ 0` let `W_r ⊆ J` be the image of `C^r` under
`(Q₁, …, Q_r) ↦ j(Q₁) + ⋯ + j(Q_r)`, so that `Θ = W_{g-1}`. Each `W_r` is closed (the summation
morphism is proper) and irreducible (`C^r` is), and `W_{r+1}` is the image of the preimage of
`W_r` under the projection `J ×_k C ⟶ J`, flat of relative dimension one, so
`dim W_{r+1} ≤ dim W_r + 1` and `dim W_r ≤ r`. Moreover `W_g = J`: every `k̄`-point of `J` is
`ι` of a class of degree zero on `C_{k̄}`, which by Riemann–Roch is `Σᵢ cl(Qᵢ - P)` for `g`
points `Qᵢ ∈ C(k̄)`. Since `dim J = g`, this forces `dim Θ = g - 1`, so `Θ` is an irreducible
closed subset of codimension one, the support of a prime divisor.

## Main results

* `Faltings.exists_primeDivisor_support_eq_thetaDivisor`: there is a prime divisor of `J` whose
  support is `Faltings.thetaDivisor X A hg j hj`.
* `Faltings.exists_isEffectiveCartierDivisor_support_eq_thetaDivisor`: there is a reduced
  effective Cartier divisor on `J` whose support is `Faltings.thetaDivisor X A hg j hj`.

## Implementation notes

A prime divisor is `Stacks.Divisors.PrimeDivisor`, an integral closed subscheme of codimension
one recorded by its ideal sheaf (Stacks 0BE2). Since `Faltings.thetaDivisor` is a subset of the
underlying space of `J`, the statement is that this subset is the support of such a subscheme;
the subscheme is then unique, being the reduced induced structure on the closure of its generic
point (`Stacks.Divisors.PrimeDivisor.genericPoint_injective`).

Sums of classes become sums of points of `J` because `ι` is additive (`Faltings.Jacobian.map_add`),
and `dim J = g` is `Faltings.Jacobian.topologicalKrullDim_eq_genus`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Theorem 5.1(a).
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
  CartesianMonoidalCategory
open MonObj

universe u

namespace Faltings

section PointClasses

/-! ### The classes `cl(Q - P_K)` of points with values in a field -/

open Stacks.RigidifiedPicard

variable {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)

/-- **Riemann–Roch on `C_K`.** Over an algebraically closed field `K`, every class in
`P⁰_C(Spec K)` is `Σᵢ cl(Qᵢ - P_K)` for `g` points `Qᵢ ∈ C(K)`: the class plus `g [P_K]` has
degree `g`, so it is the class of an effective divisor of degree `g`, which is a sum of `g`
points because `K` is algebraically closed. -/
private lemma exists_sum_pointClass_eq (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (w : (relativePicZeroFunctor k X.f).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ Q : Fin (genus X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f),
      ∑ i, X.pointClass (Q i) = w := by
  have hdim := relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let T : Over (Spec (.of k)) := Over.mk g
  let π : bc X.f T ⟶ Spec (.of K) := bcProj X.f T
  induction w using QuotientAddGroup.induction_on with | H zz => ?_
  obtain ⟨z, hz⟩ := zz
  have hz' : degree X.f hdim T z = 0 := hz
  have : SmoothOfRelativeDimension 1 π := X.smoothOfRelativeDimension_bcProj T
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsIntegral (bc X.f T) := isIntegral_bc_spec X.f g
  have := isIso_globalSections_bc_spec X.f g
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  let P' := Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) X.classP
  have hP : invertibleCurveDegreeHom K π hdimT P' = 1 :=
    X.invertibleCurveDegreeHom_schemePullbackClass_classP K hdimT
  have hz0 : invertibleCurveDegreeHom K π hdimT (smallEquiv.{u} _ z) = 0 := by
    have h := (degree_apply X.f hdim T z (IsLocalRing.closedPoint K)).symm.trans
      (congrFun hz' (IsLocalRing.closedPoint K))
    rw [← relativeInvertibleDegreeHomAt_spec π hdimT _ (IsLocalRing.closedPoint K)]
    exact h
  let c := smallEquiv.{u} _ z + (genus X.f : ℤ) • P'
  have hc : invertibleCurveDegreeHom K π hdimT c = genus X.f := by
    change invertibleCurveDegreeHom K π hdimT (smallEquiv.{u} _ z + (genus X.f : ℤ) • P') = _
    rw [map_add, map_zsmul, hz0, hP]
    simp
  have hgen : genus π = genus X.f := genus_bc_spec X.f g
  obtain ⟨D, hD, d, hrank, hd, hclass⟩ :=
    exists_isEffectiveCartierDivisor_picardClass_eq K π hdimT c (by rw [hc, hgen])
  have hdg : d = genus X.f := by rw [hc] at hd; exact_mod_cast hd
  let Z : Stacks.Hilbert.HilbertFamily (Over.mk X.f) T (genus X.f) := ⟨D, hdg ▸ hrank⟩
  obtain ⟨x, hx⟩ := Stacks.Hilbert.exists_familyOfPoints_eq_of_isAlgClosed (Over.mk X.f) g _ Z
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
  let N := (Stacks.Picard.smallSchemePullbackClassHom (bcProj X.f T)).range.addSubgroupOf
    (degree X.f hdim T).ker
  have key : (∑ i, X.pointClass (x i)) = ((∑ i, (⟨_, AddMonoidHom.mem_ker.2
      (X.degree_abelJacobiClass_field hdim K (x i))⟩ : (degree X.f hdim T).ker) :
        (degree X.f hdim T).ker) : (degree X.f hdim T).ker ⧸ N) :=
    (QuotientAddGroup.mk_sum _ _).symm
  rw [key]
  refine congrArg (QuotientAddGroup.mk (s := N)) ?_
  apply Subtype.ext
  rw [AddSubgroup.val_finsetSum, ← map_sum (smallEquiv.{u} (bc X.f T)).symm,
    AddEquiv.symm_apply_eq]
  have hF : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (X.pointFamily (x i)).zeroDivisor :=
    fun i => X.isEffectiveCartierDivisor_pointFamily (x i)
  simp only [CurveWithDegreeOneDivisor.abelJacobiClass]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (∑ i, Stacks.Divisors.picardClass
      (Stacks.Hilbert.pointIdeal (Over.mk X.f) T (x i))) = c := hsum.symm.trans hclass
  refine (congrArg (fun s => s - genus X.f • P') h2).trans ?_
  rw [← natCast_zsmul]
  exact add_sub_cancel_right _ _

end PointClasses

section Assembly

variable {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
  (j : Over.mk X.f ⟶ A.J)

/-- `ι` at a `k`-scheme `T`, with values in `J(T) = Hom_k(T, J)`. -/
private abbrev ιT (T : Over (Spec (.of k))) (a : (relativePicZeroFunctor k X.f).obj (op T)) :
    T ⟶ A.J :=
  A.ι.app (op T) a

/-- The image `W_r` of `C^r` in `J`. -/
private noncomputable abbrev W (r : ℕ) : Set A.J.left := Set.range (sumMap r j).left

private lemma isClosed_W (r : ℕ) : IsClosed (W X A j r) := by
  have hAV : IsAbelianVariety k A.J := A.isAbelianVariety
  have : IsSeparated A.J.hom := hAV.toIsProperVariety.toIsVariety.toIsSeparated
  have : IsProper (Over.mk X.f).hom := (inferInstance : IsProper X.f)
  have : IsProper (∏ᶜ fun _ : Fin r => Over.mk X.f).hom :=
    Stacks.RigidifiedPicard.isProper_fibrePower_hom _ r
  have : IsProper ((sumMap r j).left ≫ A.J.hom) := by rw [Over.w]; infer_instance
  have : IsProper (sumMap r j).left := .of_comp _ A.J.hom
  exact (sumMap r j).left.isClosedMap.isClosed_range

private lemma isIrreducible_W (r : ℕ) : IsIrreducible (W X A j r) := by
  have : GeometricallyIrreducible (Over.mk X.f).hom :=
    (inferInstance : GeometricallyIrreducible X.f)
  have : UniversallyOpen (Over.mk X.f).hom := (inferInstance : UniversallyOpen X.f)
  have : IrreducibleSpace (∏ᶜ fun _ : Fin r => Over.mk X.f).left :=
    Stacks.Scheme.irreducibleSpace_fibrePower _ r
  rw [W, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (sumMap r j).left.continuous.continuousOn

private lemma topologicalKrullDim_W_zero : topologicalKrullDim (W X A j 0) = 0 := by
  have := Stacks.Scheme.isIso_fibrePower_zero_hom (Over.mk X.f)
  have : Subsingleton (∏ᶜ fun _ : Fin 0 => Over.mk X.f).left :=
    (asIso (∏ᶜ fun _ : Fin 0 => Over.mk X.f).hom).hom.homeomorph.injective.subsingleton
  have hne : Nonempty (∏ᶜ fun _ : Fin 0 => Over.mk X.f).left :=
    ⟨(inv (∏ᶜ fun _ : Fin 0 => Over.mk X.f).hom) (IsLocalRing.closedPoint k)⟩
  have : Subsingleton (W X A j 0) := (Set.subsingleton_range _).coe_sort
  have : Nonempty (W X A j 0) := ⟨⟨_, Set.mem_range_self hne.some⟩⟩
  have : DiscreteTopology (W X A j 0) := ⟨Subsingleton.elim _ _⟩
  exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty

/-- Forgetting the last coordinate, `C^{r+1} ⟶ C^r`. -/
private noncomputable abbrev initProj (r : ℕ) :
    (∏ᶜ fun _ : Fin (r + 1) => Over.mk X.f) ⟶ ∏ᶜ fun _ : Fin r => Over.mk X.f :=
  Pi.lift fun i => Pi.π (fun _ : Fin (r + 1) => Over.mk X.f) i.castSucc

/-- The morphism `(x, Q) ↦ x + j(Q)`, `J ×_k C ⟶ J`. -/
private noncomputable abbrev addJ : A.J ⊗ Over.mk X.f ⟶ A.J :=
  fst _ _ * (snd _ _ ≫ j)

/-- `σ_{r+1} = (σ_r ∘ init, last) ≫ (x, Q) ↦ x + j(Q)`. -/
private lemma sumMap_succ (r : ℕ) :
    sumMap (r + 1) j =
      lift (initProj X r ≫ sumMap r j) (Pi.π (fun _ : Fin (r + 1) => Over.mk X.f)
        (Fin.last r)) ≫ addJ X A j := by
  rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, comp_list_prod, List.map_ofFn, sumMap,
    List.ofFn_succ', List.prod_concat]
  congr 2
  congr 1
  funext i
  simp only [Function.comp_apply, initProj, Pi.lift_π_assoc]

/-- The product `J ×_k C` is a variety. -/
private lemma isVariety_prod :
    IsVariety k (pullback.fst A.J.hom X.f ≫ A.J.hom) := by
  have hAV : IsAbelianVariety k A.J := A.isAbelianVariety
  have hV := hAV.toIsProperVariety.toIsVariety
  have : IsIntegral A.J.left := hV.toIsIntegral
  have : LocallyOfFiniteType A.J.hom := hV.toLocallyOfFiniteType
  have : IsSeparated A.J.hom := hV.toIsSeparated
  have : QuasiCompact A.J.hom := hV.toQuasiCompact
  have : IsLocallyNoetherian A.J.left := LocallyOfFiniteType.isLocallyNoetherian A.J.hom
  have : IsIntegral (pullback A.J.hom X.f) := inferInstance
  exact ⟨⟩

/-- `dim W_{r+1} ≤ dim W_r + 1`, in the form needed for closed subsets of `W_{r+1}`. -/
private lemma topologicalKrullDim_le_W_add_one (r n : ℕ)
    (hn : topologicalKrullDim (W X A j r) ≤ (n : WithBot ℕ∞)) (S : Set A.J.left)
    (hS : IsClosed S) (hSW : S ⊆ W X A j (r + 1)) :
    topologicalKrullDim S ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
  have hAV : IsAbelianVariety k A.J := A.isAbelianVariety
  have hV := hAV.toIsProperVariety.toIsVariety
  have hVC : IsVariety k X.f := inferInstance
  have := isVariety_prod X A
  -- the first projection `J ×_k C ⟶ J` is flat of relative dimension one
  have : Flat (pullback.fst A.J.hom X.f) := inferInstance
  have : Nonempty X.C := inferInstance
  have hC : topologicalKrullDim X.C = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 X.f
  have he : topologicalKrullDim ↥(pullback A.J.hom X.f) =
      topologicalKrullDim A.J.left + ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_pullback_of_isVariety k A.J.hom X.f, hC]
  have hpre := Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le k
    (pullback.fst A.J.hom X.f ≫ A.J.hom) A.J.hom (pullback.fst A.J.hom X.f) rfl 1 he
    ⟨W X A j r, isClosed_W X A j r⟩ n hn
  refine Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le k
    (pullback.fst A.J.hom X.f ≫ A.J.hom) A.J.hom
    (addJ X A j).left (Over.w (addJ X A j)) _
    ((isClosed_W X A j r).preimage (pullback.fst A.J.hom X.f).continuous) (n + 1) hpre S hS ?_
  refine hSW.trans ?_
  rintro _ ⟨z, rfl⟩
  refine ⟨(lift (initProj X r ≫ sumMap r j) (Pi.π (fun _ : Fin (r + 1) => Over.mk X.f)
    (Fin.last r))).left z, ⟨(initProj X r).left z, ?_⟩, ?_⟩
  · change (sumMap r j).left ((initProj X r).left z) = (fst A.J (Over.mk X.f)).left
      ((lift (initProj X r ≫ sumMap r j) (Pi.π (fun _ : Fin (r + 1) => Over.mk X.f)
        (Fin.last r))).left z)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
      lift_fst]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← sumMap_succ]

/-- `Spec k̄` as a `k`-scheme. -/
local notation "ptK" => fieldExtensionPoint k (AlgebraicClosure k)

/-- **Every `k̄`-point of `J` is a sum of `g` points of `j(C)`.** -/
private lemma exists_comp_sumMap_eq (hj : IsAbelJacobiMap X A j) (b : ptK ⟶ A.J) :
    ∃ q : ptK ⟶ ∏ᶜ fun _ : Fin (genus X.f) => Over.mk X.f, q ≫ sumMap (genus X.f) j = b := by
  have := A.isAbelianVariety
  have hAV : IsAbelianVariety k A.J := inferInstance
  have : IsProper A.J.hom := hAV.toIsProperVariety.toIsProper
  have : GeometricallyIntegral A.J.hom := hAV.toGeometricallyIntegral
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral _
  have := A.isIso_app ptK X.nonempty_algebraicClosure_point
  obtain ⟨w, hw⟩ := ((isIso_iff_bijective _).1 this).2 b
  obtain ⟨Q, hQ⟩ := exists_sum_pointClass_eq X (AlgebraicClosure k) w
  refine ⟨Pi.lift Q, ?_⟩
  have h1 : Pi.lift Q ≫ sumMap (genus X.f) j =
      ((List.ofFn fun i => X.pointClass (Q i)).map (ιT X A ptK)).prod := by
    rw [comp_list_prod, List.map_ofFn, List.map_ofFn]
    congr 1
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.lift_π_assoc]
    exact hj.comp_eq_ι_pointClass (Q i)
  rw [h1, ← hw, ← hQ, ← List.sum_ofFn]
  exact (A.ι_app_list_sum ptK _).symm

private lemma W_genus_eq_univ (hj : IsAbelJacobiMap X A j) :
    W X A j (genus X.f) = Set.univ := by
  have hAV : IsAbelianVariety k A.J := A.isAbelianVariety
  have hV := hAV.toIsProperVariety.toIsVariety
  have : LocallyOfFiniteType A.J.hom := hV.toLocallyOfFiniteType
  have : JacobsonSpace A.J.left := LocallyOfFiniteType.jacobsonSpace A.J.hom
  refine Set.eq_univ_of_univ_subset ?_
  rw [← closure_closedPoints, (isClosed_W X A j _).closure_subset_iff]
  intro y hy
  obtain ⟨b, hb, p, rfl⟩ := exists_algebraicClosure_point_of_isClosed A.J.hom y hy
  obtain ⟨q, hq⟩ := exists_comp_sumMap_eq X A j hj (Over.homMk b hb)
  refine ⟨q.left p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hq]
  rfl

private lemma topologicalKrullDim_W_le (r : ℕ) :
    topologicalKrullDim (W X A j r) ≤ (r : WithBot ℕ∞) := by
  induction r with
  | zero => rw [topologicalKrullDim_W_zero]; rfl
  | succ r ih =>
    exact topologicalKrullDim_le_W_add_one X A j r r ih _ (isClosed_W X A j (r + 1)) subset_rfl

/-- A Krull dimension squeezed between `0` and a natural number is a natural number. -/
private lemma exists_nat_eq_of_nonneg_of_le {x : WithBot ℕ∞} {m : ℕ} (h0 : 0 ≤ x)
    (hle : x ≤ m) : ∃ d : ℕ, x = d := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    lift e to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top m) (WithBot.coe_le_coe.1 hle)
    exact ⟨e, rfl⟩

/-- **`dim Θ = g - 1`.** `dim W_{g-1} ≤ g - 1`, and `W_g = J` with `dim J = g` and
`dim W_g ≤ dim W_{g-1} + 1` force equality. -/
private lemma topologicalKrullDim_W_pred_add_one (hj : IsAbelJacobiMap X A j)
    (hg : 1 ≤ genus X.f) :
    topologicalKrullDim (W X A j (genus X.f - 1)) + 1 = (genus X.f : WithBot ℕ∞) := by
  have hle := topologicalKrullDim_W_le X A j (genus X.f - 1)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim (W X A j (genus X.f - 1)) = d := by
    have hne := (isIrreducible_W X A j (genus X.f - 1)).nonempty.to_subtype
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (W X A j (genus X.f - 1))) :=
      ⟨.closureSingleton hne.some⟩
    exact exists_nat_eq_of_nonneg_of_le Order.krullDim_nonneg hle
  rw [hd] at hle
  have hdm : d ≤ genus X.f - 1 := by exact_mod_cast hle
  have hgd : genus X.f ≤ d + 1 := by
    have h := topologicalKrullDim_le_W_add_one X A j _ d hd.le Set.univ isClosed_univ
      (by rw [Nat.sub_add_cancel hg, W_genus_eq_univ X A j hj])
    rw [topologicalKrullDim_univ, Jacobian.topologicalKrullDim_eq_genus] at h
    exact_mod_cast h
  rw [hd, show genus X.f = d + 1 by omega]
  norm_cast

end Assembly

variable {k : Type u} [Field k]

/-- **The theta divisor is a prime divisor** ([MilAV, III, Theorem 5.1(a)]). For a curve
`X = (C, P)` with a divisor of degree one, of genus `g ≥ 1`, a Jacobian `A = (J, ι)` and the
Abel–Jacobi map `j = j_P`, the theta divisor `Faltings.thetaDivisor X A hg j hj ⊆ J` is the
support of a prime divisor of `J`, i.e. of an integral closed subscheme of codimension one. -/
@[faltings "lem_nt_theta_prime_divisor"]
public theorem exists_primeDivisor_support_eq_thetaDivisor (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) :
    ∃ Z : Stacks.Divisors.PrimeDivisor A.J.left, Z.support = thetaDivisor X A hg j hj := by
  have := A.isAbelianVariety
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_W X A j _) (isClosed_W X A j (genus X.f - 1))
  have hξW : closure ({ξ} : Set A.J.left) = thetaDivisor X A hg j hj := hξ.def
  have hcoh : Order.coheight ξ = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    refine codimension_eq_one_of_topologicalKrullDim_add_one
      (Jacobian.topologicalKrullDim_eq_genus X A) _ ?_
    rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton, hξW]
    exact topologicalKrullDim_W_pred_add_one X A j hj hg
  exact ⟨.ofCoheightOne ξ hcoh, by rw [Stacks.Divisors.PrimeDivisor.support_eq_closure,
    Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne, hξW]⟩

/-- **The theta divisor is the support of a reduced effective Cartier divisor.** For a curve
`X = (C, P)` with a divisor of degree one, of genus `g ≥ 1`, a Jacobian `A = (J, ι)` and the
Abel–Jacobi map `j = j_P`, there is a sheaf of ideals `D` on `J`, an effective Cartier divisor
equal to its own radical, whose support is `Faltings.thetaDivisor X A hg j hj`: the ideal sheaf
of the prime divisor `Θ`, which is Cartier since the local rings of the smooth variety `J` are
regular, hence factorial. -/
public theorem exists_isEffectiveCartierDivisor_support_eq_thetaDivisor
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 1 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) :
    ∃ D : A.J.left.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      D.radical = D ∧ (D.support : Set A.J.left) = thetaDivisor X A hg j hj := by
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg j hj
  have := A.isAbelianVariety
  have : Smooth A.J.hom := smooth_of_isAbelianVariety k A.J
  have : IsLocallyNoetherian A.J.left := LocallyOfFiniteType.isLocallyNoetherian A.J.hom
  have := Z.integral
  refine ⟨Z.idealSheaf, ?_, radical_eq_of_isReduced _, hZ⟩
  refine @isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid _ ‹_›
    Z.idealSheaf Z.integral Z.codimension_one fun x _ => ?_
  have := isRegularLocalRing_stalk_of_smooth_over_field A.J.hom x
  exact IsRegularLocalRing.uniqueFactorizationMonoid (A.J.left.presheaf.stalk x)

end Faltings
