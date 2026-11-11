module
public import Mordell.Jacobian.BaseChange
public import Mordell.Jacobian.Theta.PullbackTranslate
public import Mordell.Jacobian.Theta.BaseChange
public import Mordell.Jacobian.Theta.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import Mordell.Jacobian.Autoduality.PhiTheta
/-!
# Bombieri's Lemma 1: the pull-back of `θ⁻` along the Abel–Jacobi map

Let `(C, P)` be a curve over a field `k` with a divisor `P = ∑ nₓ x` of degree one, of genus
`g ≥ 1`, let `(J, ι)` be a Jacobian of `C`, `j = j_P : C ⟶ J` the Abel–Jacobi map and
`Θ = Θ_P ⊆ J` the theta divisor, with class `θ = cl(Θ) = [𝒪_J(Θ)] ∈ Pic(J)`. Write
`θ⁻ = [-1]^* θ` for its pull-back along the inversion of `J`. Then
`j^*(θ⁻) = g · cl(P)` in `Pic(C)`, where `cl(P) = ∑ nₓ [𝒪_C(x)]`.

## Main results

* `Faltings.schemePullbackClass_abelJacobi_thetaNeg`: `j^*([-1]^* θ) = g • cl(P)` in `Pic(C)`.

## Implementation notes

The class `θ` is the class `Stacks.Divisors.picardClass D` of the reduced effective Cartier
divisor `D` on `J` whose support is `Faltings.thetaDivisor X A hg j hj`; `Θ` is a prime divisor
on the smooth `J`, so such a `D` exists and is unique, and it is taken as an argument with the
properties that pin it (`D.radical = D`, support `Θ`), exactly as in `Faltings.deltaClass` and
`Faltings.neronPairing`. The inversion `[-1]` is the
inverse `ι[A.J]` of the group object `J` over `Spec k`, and pull-backs of classes are
`Stacks.Picard.schemePullbackClassHom`.

The proof passes to an algebraic closure `K` of `k`; the pull-back `Pic(C) → Pic(C_K)` is
injective ([Stacks, Tag 0CC5]). Over `K` choose a rational point `P₀` of `C_K`, put
`e = ι(cl(P_K - P₀))`, `j₀ = j_{P₀}` for the base-changed Jacobian `(J_K, ι_K)` and
`θ₀ = cl(Θ_{P₀})`. Then `j = j₀ · e⁻¹` on `C_K` (`Faltings.IsAbelJacobiMap.comp_fst_eq_mul_inv`)
and `θ₀ = τ^* θ_K` for the translation `τ = τ_{-(g-1)e}`
(`Faltings.thetaDivisor_baseChange_eq_image_translate`), so that `j` followed by the inversion
is `x ↦ e^g · j₀(x)⁻¹` followed by `τ`. By Riemann–Roch there is an effective divisor `D` of
degree `g` on `C_K` with `D ∼ g P_K`, so `ι_K` sends `cl(D - g P₀) = g · cl(P_K - P₀)` to `e^g`,
and `Faltings.schemePullbackClass_thetaDivisor_translate_eq` gives `j^* θ⁻ = cl(D) = g · cl(P_K)`
on `C_K`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, Lemma 1.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 6 (Lemma 6.8).
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.RigidifiedPicard
open scoped MonObj

universe u

namespace Faltings

/-! ### Picard classes on base changes -/

/-- The pull-back `Pic(C) → Pic(C_K)` along a field extension `K / k` is injective
([Stacks, Tag 0CC5]). -/
private lemma injective_schemePullbackClassHom_pullback_fst {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (K : Type u) [Field K] [Algebra k K] :
    Function.Injective (Stacks.Picard.schemePullbackClassHom
      (pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := by
  have : IsIntegral X.C := GeometricallyIntegral.isIntegral_of_subsingleton X.f
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : CompactSpace X.C := (quasiCompact_iff_compactSpace X.f).1 inferInstance
  have : QuasiSeparatedSpace X.C := (quasiSeparated_iff_quasiSeparatedSpace X.f).1 inferInstance
  have hfd : letI := Stacks.AlgebraicGeometry.PicardBaseChange.globalSectionsAlgebra X.f
      FiniteDimensional k Γ(X.C, ⊤) := by
    let := Stacks.AlgebraicGeometry.PicardBaseChange.globalSectionsAlgebra X.f
    change Module.Finite k Γ(X.C, ⊤)
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k X.f).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))
  exact Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional
    X.C (algebraMap k K) X.f hfd

/-! ### Additivity of `ι` -/

/-- An additive `ι` sends `n • x` to the `n`-th power of the point `ι(x)`. -/
private lemma ι_app_nsmul {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (T : Over (Spec (.of k))) (x : (relativePicZeroFunctor k X.f).obj (op T)) (n : ℕ) :
    (show T ⟶ A.J from A.ι.app (op T) (n • x)) = (show T ⟶ A.J from A.ι.app (op T) x) ^ n := by
  induction n with
  | zero =>
    have h := hι T 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact (hι T _ _).trans (by rw [ih])

/-! ### An identity in a commutative group -/

/-- `s^g p⁻¹ (s^{g-1})⁻¹ = (p s⁻¹)⁻¹` for `g ≥ 1`. -/
private lemma pow_mul_inv_mul_inv_pow_sub_one {G : Type*} [CommGroup G] (s p : G) {g : ℕ}
    (hg : 1 ≤ g) : s ^ g * p⁻¹ * (s ^ (g - 1))⁻¹ = (p * s⁻¹)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, (Nat.sub_add_cancel hg).symm⟩
  rw [Nat.add_sub_cancel, mul_inv_rev, inv_inv, pow_succ, mul_right_comm, mul_comm (s ^ n) s,
    mul_inv_cancel_right]

/-! ### The main argument -/

variable {k : Type u} [Field k]

/-- **Bombieri's Lemma 1, first identity.** For a curve `X = (C, P)` with a divisor of degree one,
of genus `g ≥ 1`, a Jacobian `A = (J, ι)` with `ι` additive (`hι`) and the Abel–Jacobi map
`j = j_P`, let `θ = cl(Θ) ∈ Pic(J)` be the class of the reduced effective Cartier divisor `D` whose
support is the theta divisor `Θ = Faltings.thetaDivisor X A hg j hj`, and `θ⁻ = [-1]^* θ`. Then
`j^*(θ⁻) = g • cl(P)` in `Pic(C)`, where `cl(P) = ∑ nₓ [𝒪_C(x)]` for `P = ∑ nₓ x`. -/
@[faltings "lem_nt_bombieri_lemma1"]
public theorem schemePullbackClass_abelJacobi_thetaNeg (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    /- The class `θ = cl(Θ) = [𝒪_J(Θ)]` in `Pic(J)`. -/
    let θ := Stacks.Divisors.picardClass D
    /- The class `cl(P) = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`. -/
    let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    Stacks.Picard.schemePullbackClassHom j.left
        (Stacks.Picard.schemePullbackClassHom ι[A.J].left θ) =
      (genus X.f : ℤ) • classP := by
  have hDvan : D = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ := by
    have hcl : (⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ :
        TopologicalSpace.Closeds A.J.left) = D.support := by
      ext1
      rw [TopologicalSpace.Closeds.coe_mk, ← hsupp, D.support.isClosed.closure_eq]
    rw [hcl, Scheme.IdealSheafData.vanishingIdeal_support, hrad]
  subst hDvan
  intro θ₁ classP₁
  let K := AlgebraicClosure k
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  have := A.isAbelianVariety
  have hCK : IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    isSmoothProjectiveCurve_pullback_snd X.f _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : {x : ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      // IsClosed ({x} : Set ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))},
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree x₀.1 = 1 :=
    by
    have : CompactSpace ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      (quasiCompact_iff_compactSpace
        (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).1 inferInstance
    exact exists_closedPoint_residueDegree_eq_one _
  let P₀ := Finsupp.single x₀ (1 : ℤ)
  have hP₀ : (P₀.sum fun x n =>
      n * ((pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree
        x.1 : ℤ)) = 1 := by
    simp [P₀, hx₀]
  obtain ⟨_, _, ι', _, hι', _, hι'c⟩ := Jacobian.exists_baseChange k K X.f A
  let X₀ : CurveWithDegreeOneDivisor K :=
    ⟨pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))), P₀, hP₀⟩
  let A₀ : Jacobian K X₀.f :=
    ⟨(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J, inferInstance,
      ι', Jacobian.map_add_of_baseChange X.f A ι' hι'c, hι'⟩
  have hgen : genus X₀.f = genus X.f :=
    genus_baseChange k K (pullback.fst X.f _) X₀.f X.f (IsPullback.of_hasPullback X.f _)
  have hg₀ : 1 ≤ genus X₀.f := hgen ▸ hg
  obtain ⟨j₀, hj₀, -⟩ := existsUnique_isAbelJacobiMap X₀ A₀
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have : Smooth (bcProj X.f T) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve K (bcProj X.f T) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one (bcProj X.f T)
  let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
  let classP₀ : Stacks.Picard.ofScheme (bc X.f T) := P₀.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (C := bc X.f T) (bcProj X.f T) x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (C := bc X.f T) x)
  let classx₀ : Stacks.Picard.ofScheme (bc X.f T) :=
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (C := bc X.f T) (bcProj X.f T) x₀
    Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (C := bc X.f T) x₀)
  have hP₀c : classP₀ = classx₀ := by
    simp only [classP₀, P₀]
    rw [Finsupp.sum_single_index]
    · exact one_smul _ _
    · exact zero_smul _ _
  let zₑ : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
    (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀)
  have hdegₑ : degree X.f hdim T zₑ = 0 := by
    have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
      topologicalKrullDim_le_one_of_smoothOfRelativeDimension (bcProj X.f T)
    have h1 : invertibleCurveDegreeHom K (bcProj X.f T) hdimT
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP) = 1 :=
      (invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
        (IsPullback.of_hasPullback X.f T.hom)
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f) hdimT classP).trans
          (X.invertibleCurveDegreeHom_classP _)
    have h2 : invertibleCurveDegreeHom K (bcProj X.f T) hdimT classP₀ = 1 := by
      rw [hP₀c]
      exact (X₀.invertibleCurveDegreeHom_picardClass_pointIdeal hdimT x₀).trans
        (by rw [hx₀, Nat.cast_one])
    funext t
    rw [degree_apply, AddEquiv.apply_symm_apply]
    refine (relativeInvertibleDegreeHomAt_spec (bcProj X.f T) hdimT _ t _).trans ?_
    rw [map_sub, h1, h2]
    rfl
  let e : T ⟶ A.J := A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
    QuotientAddGroup.mk (⟨zₑ, hdegₑ⟩ : (degree X.f hdim T).ker))
  have he : ∀ hdeg : degree X.f hdim T zₑ = 0, e = A.ι.app (op T)
      (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker)) := fun _ => rfl
  have hΘ' :=
    thetaDivisor_baseChange_eq_image_translate X A hι hg hj K P₀ hP₀ ι' hι'c hj₀ e he
  have hrel := P_comp_eq_mul_inv X A hι hj K P₀ hP₀ ι' hι'c hι' hj₀ e he
  let JK : Over (Spec (.of K)) :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J
  have : IsAbelianVariety K JK := A₀.isAbelianVariety
  have : IsCommMonObj JK := isCommMonObj_of_isProper_of_geometricallyIntegral JK
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK :=
    Over.homMk (pullback.lift e.left (𝟙 _) (by simp [T]))
      (pullback.lift_snd _ _ _)
  let τ : JK ⟶ JK := 𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ eK ^ (genus X.f - 1))⁻¹
  have hΘ'' : pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹'
      thetaDivisor X A hg j hj = τ.left '' thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := hΘ'
  have : IsIso τ := by
    refine ⟨⟨𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ eK ^ (genus X.f - 1)), ?_, ?_⟩⟩
    · rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        Over.mkIdTerminal.hom_ext (τ ≫ Over.homMk JK.hom (Category.comp_id _))
          (Over.homMk JK.hom (Category.comp_id _)), mul_assoc, inv_mul_cancel, mul_one]
    · rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc,
        Over.mkIdTerminal.hom_ext (_ ≫ Over.homMk JK.hom (Category.comp_id _))
          (Over.homMk JK.hom (Category.comp_id _)), mul_assoc, mul_inv_cancel, mul_one]
  have : IsIso τ.left := (Over.forget _).map_isIso τ
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := flat_specMap_algebraMap k K
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg j hj
  obtain ⟨Z₀, hZ₀⟩ := exists_primeDivisor_support_eq_thetaDivisor X₀ A₀ hg₀ j₀ hj₀
  have hΘcl : closure (thetaDivisor X A hg j hj) = thetaDivisor X A hg j hj := by
    rw [← hZ]; exact Z.idealSheaf.support.isClosed.closure_eq
  have hΘ₀cl : closure (thetaDivisor X₀ A₀ hg₀ j₀ hj₀) = thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := by
    rw [← hZ₀]; exact Z₀.idealSheaf.support.isClosed.closure_eq
  let D := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ : TopologicalSpace.Closeds A.J.left)
  let D₀ := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (thetaDivisor X₀ A₀ hg₀ j₀ hj₀), isClosed_closure⟩ :
      TopologicalSpace.Closeds A₀.J.left)
  have : IsReduced D.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsReduced D₀.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hD : (D.support : Set A.J.left) = thetaDivisor X A hg j hj := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hΘcl
  have hD₀ : (D₀.support : Set A₀.J.left) = thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hΘ₀cl
  let φ := τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hD₀D : D₀ = D.comap φ := by
    have := isReduced_comap_of_support_eq_thetaDivisor X A hg hj D hD K φ JK.hom
      (IsPullback.of_iso (IsPullback.of_hasPullback A.J.hom _) (asIso τ.left).symm (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (by simp [φ]) (by
          simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp]
          exact Over.w τ) (by simp) (by simp))
    refine eq_comap_of_preimage_support_eq D₀ D φ ?_
    rw [hD, hD₀]
    exact preimage_comp_eq_of_preimage_eq_image τ.left.isOpenEmbedding.injective hΘ''
  have : Stacks.Divisors.IsPullbackDefined φ D :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have hD₀C : Stacks.Divisors.IsEffectiveCartierDivisor D₀ := by
    rw [hD₀D]
    exact ‹Stacks.Divisors.IsPullbackDefined φ D›
  have hθ₀ : Stacks.Divisors.picardClass D₀ =
      Stacks.Picard.schemePullbackClass φ (Stacks.Divisors.picardClass D) := by
    rw [Stacks.Divisors.schemePullbackClass_picardClass]
    exact Stacks.Divisors.picardClass_congr hD₀D
  have hι₀ := ι'_add X A hι K ι' hι'c
  have : Smooth X₀.f := SmoothOfRelativeDimension.smooth 1 X₀.f
  have : IsCurve K X₀.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X₀.f
  have : IsLocallyNoetherian X₀.C := LocallyOfFiniteType.isLocallyNoetherian X₀.f
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  have hdimX₀ : topologicalKrullDim X₀.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X₀.f
  have hdim₀ : ∀ s, topologicalKrullDim ↥(X₀.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X₀.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X₀.f)
  let pr : X₀.C ⟶ X.C := pullback.fst X.f T.hom
  have hdegP : invertibleCurveDegreeHom K X₀.f hdimX₀
      (Stacks.Picard.schemePullbackClass pr classP) = 1 :=
    (invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
      (IsPullback.of_hasPullback X.f T.hom) hdimC hdimX₀ classP).trans
        (X.invertibleCurveDegreeHom_classP hdimC)
  obtain ⟨E, hE0, hEc⟩ := exists_nonneg_divisorClass_eq X₀.f
    ((genus X.f : ℤ) • Stacks.Picard.schemePullbackClass pr classP) (by
      have h : Stacks.Picard.picardDegree X₀.f (Stacks.Zeta.topologicalKrullDim_le_one X₀.f)
          ((genus X.f : ℤ) • Stacks.Picard.schemePullbackClass pr classP) =
            invertibleCurveDegreeHom K X₀.f hdimX₀
              ((genus X.f : ℤ) • Stacks.Picard.schemePullbackClass pr classP) := rfl
      rw [h, map_zsmul, hdegP, hgen, smul_eq_mul, mul_one])
  let classD : Stacks.Picard.ofScheme X₀.C := E.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
  have hDc : classD = (genus X.f : ℤ) • Stacks.Picard.schemePullbackClass pr classP :=
    (Stacks.Zeta.divisorClass_apply X₀.f E).symm.trans hEc
  have hEdeg : (E.sum fun x n => n * (X₀.f.residueDegree x.1 : ℤ)) = genus X₀.f := by
    have h1 : invertibleCurveDegreeHom K X₀.f hdimX₀ classD =
        E.sum fun x n => n * (X₀.f.residueDegree x.1 : ℤ) := by
      simp only [classD]
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun x _ => ?_
      rw [map_zsmul, smul_eq_mul]
      exact congrArg (_ * ·) (X₀.invertibleCurveDegreeHom_picardClass_pointIdeal hdimX₀ x)
    rw [← h1, hDc, map_zsmul, hdegP, hgen, smul_eq_mul, mul_one]
  let TK : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K)))
  let z₀ : Stacks.Picard.smallOfScheme (bc X₀.f TK) := (smallEquiv (bc X₀.f TK)).symm
    (Stacks.Picard.schemePullbackClass (pullback.fst X₀.f TK.hom)
      (classD - (genus X₀.f : ℤ) • (show Stacks.Picard.ofScheme X₀.C from classx₀)))
  have hbcK : bcIso X K K = pullback.fst X₀.f TK.hom := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · refine (pullback.lift_snd _ _ _).trans
        (Eq.trans ?_ (pullback.condition (f := X₀.f) (g := TK.hom)).symm)
      simp [TK, Algebra.algebraMap_self]
      rfl
  have hz₀ : z₀ = Stacks.Picard.smallSchemePullbackClassHom (bcIso X K K) (genus X.f • zₑ) := by
    apply (smallEquiv.{u} _).injective
    rw [smallEquiv_smallSchemePullbackClassHom, map_nsmul]
    simp only [z₀, zₑ, AddEquiv.apply_symm_apply]
    erw [AddEquiv.apply_symm_apply]
    rw [hbcK, hDc, hgen, hP₀c, smul_sub, natCast_zsmul, natCast_zsmul]
  have hdegg : degree X.f hdim T (genus X.f • zₑ) = 0 := by
    rw [map_nsmul, hdegₑ, smul_zero]
  have hdeg₀ : degree X₀.f hdim₀ TK z₀ = 0 := by
    rw [hz₀, hbcK]
    refine (degree_smallSchemePullbackClassHom_of_isPullback (T := T) (T' := TK) X.f X₀.f hdim
      hdim₀ (pullback.fst X₀.f TK.hom) TK.hom (IsPullback.of_hasPullback X₀.f TK.hom)
      (genus X.f • zₑ)).trans ?_
    rw [hdegg]
    rfl
  let a : TK ⟶ A₀.J := ι'.app (op TK) (QuotientAddGroup.mk ⟨z₀, hdeg₀⟩)
  have hιg : A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
      QuotientAddGroup.mk (⟨genus X.f • zₑ, hdegg⟩ : (degree X.f hdim T).ker)) =
        e ^ genus X.f :=
    ι_app_nsmul X A hι T (QuotientAddGroup.mk (⟨zₑ, hdegₑ⟩ : (degree X.f hdim T).ker)) (genus X.f)
  have ha : a.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      (e ^ genus X.f).left :=
    (ι'_app_left_fst X A K ι' hι'c K hdim hdim₀ _ hdegg z₀ hdeg₀ hz₀).trans
      (congrArg Over.Hom.left hιg)
  have hZD : Z₀.idealSheaf = D₀ := by
    have := Z₀.integral
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    ext1
    exact hZ₀.trans hΘ₀cl.symm
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z₀.idealSheaf := hZD ▸ hD₀C
  let ψ : Over.mk X₀.f ⟶ A₀.J :=
    (Over.homMk (U := Over.mk X₀.f) (V := TK) X₀.f (by simp [TK, Algebra.algebraMap_self]) ≫ a) *
      j₀⁻¹
  have hT : Stacks.Picard.schemePullbackClass ψ.left
      (Stacks.Divisors.picardClass Z₀.idealSheaf) = classD :=
    schemePullbackClass_thetaDivisor_translate_eq X₀ x₀ rfl A₀ hι₀ hg₀ j₀ hj₀ Z₀ hZ₀ E hE0 hEdeg a
      (fun _ => rfl)
  let σ : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X₀.f) ⟶ T :=
    Over.homMk X₀.f
  have hPa : P A.J (Over.homMk (U := Over.mk X₀.f) (V := TK) X₀.f
      (by simp [TK, Algebra.algebraMap_self]) ≫ a) = (σ ≫ e) ^ genus X.f := by
    rw [← MonObj.comp_pow]
    apply Over.OverMorphism.ext
    rw [P_left]
    change (X₀.f ≫ a.left) ≫ _ = X₀.f ≫ (e ^ genus X.f).left
    rw [Category.assoc, ha]
  have hPc : ∀ d : Over.mk X₀.f ⟶ Over.mk (𝟙 (Spec (.of K))),
      P A.J (d ≫ eK ^ (genus X.f - 1)) = (σ ≫ e) ^ (genus X.f - 1) := by
    intro d
    rw [P_comp_left, ← pEquiv_apply, map_pow, pEquiv_apply, MonObj.comp_pow]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, P_left]
    change d.left ≫ pullback.lift e.left _ _ ≫ pullback.fst _ _ = X₀.f ≫ e.left
    rw [pullback.lift_fst]
    congr 1
    simpa using Over.w d
  have hPτ : P A.J (ψ ≫ τ) = (P (Over.mk X.f) (𝟙 _) ≫ j)⁻¹ := by
    have h1 : ψ ≫ τ = ψ *
        ((ψ ≫ Over.homMk JK.hom (Category.comp_id _)) ≫ eK ^ (genus X.f - 1))⁻¹ := by
      simp only [τ]
      rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, Category.assoc]
    rw [h1, ← pEquiv_apply, map_mul, map_inv, pEquiv_apply, pEquiv_apply, hPc]
    simp only [ψ]
    rw [← pEquiv_apply, map_mul, map_inv, pEquiv_apply, pEquiv_apply, hPa, hrel]
    exact pow_mul_inv_mul_inv_pow_sub_one _ _ hg
  have hmor : ψ.left ≫ φ = pr ≫ j.left ≫ ι[A.J].left := by
    have h1 : (P A.J (ψ ≫ τ)).left = ψ.left ≫ φ := by
      rw [P_left]
      rfl
    have h2 : ((P (Over.mk X.f) (𝟙 _) ≫ j) ≫ ι[A.J]).left = pr ≫ j.left ≫ ι[A.J].left := by
      rw [Over.comp_left, Over.comp_left, P_left, Over.id_left, Category.id_comp,
        Category.assoc]
      rfl
    rw [← h1, ← h2, hPτ, Hom.inv_def]
  apply injective_schemePullbackClassHom_pullback_fst X K
  change Stacks.Picard.schemePullbackClass pr (Stacks.Picard.schemePullbackClass j.left
      (Stacks.Picard.schemePullbackClass ι[A.J].left θ₁)) =
    Stacks.Picard.schemePullbackClassHom pr ((genus X.f : ℤ) • classP)
  calc Stacks.Picard.schemePullbackClass pr (Stacks.Picard.schemePullbackClass j.left
        (Stacks.Picard.schemePullbackClass ι[A.J].left θ₁))
      = Stacks.Picard.schemePullbackClass (ψ.left ≫ φ) (Stacks.Divisors.picardClass D) := by
        rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
          hmor, Category.assoc]
    _ = Stacks.Picard.schemePullbackClass ψ.left
          (Stacks.Picard.schemePullbackClass φ (Stacks.Divisors.picardClass D)) :=
        (Stacks.Picard.schemePullbackClass_comp _ _ _).symm
    _ = Stacks.Picard.schemePullbackClass ψ.left (Stacks.Divisors.picardClass Z₀.idealSheaf) := by
        rw [← hθ₀, Stacks.Divisors.picardClass_congr hZD]
    _ = classD := hT
    _ = (genus X.f : ℤ) • Stacks.Picard.schemePullbackClass pr classP := hDc
    _ = Stacks.Picard.schemePullbackClassHom pr ((genus X.f : ℤ) • classP) :=
        (map_zsmul (Stacks.Picard.schemePullbackClassHom pr) _ _).symm

end Faltings
