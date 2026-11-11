module

public import Mathlib
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Curve.PointClass
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.FiniteGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OverBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.ChartProjection
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints

/-!
# Very ample classes on `C × C`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g`, and let
`X = C ×_k C` with projections `pr₁, pr₂`. For an integer `N ≥ 2g + 1` the class
`H_N = pr₁^*[𝒪_C(NP)] + pr₂^*[𝒪_C(NP)]` in `Pic(X)` is very ample: every invertible
`𝒪_X`-module of class `H_N` is very ample relative to the structure morphism `X ⟶ Spec k`.
The proof embeds `C` by the very ample `𝒪_C(NP)` (degree `N ≥ 2g + 1`) and composes the
product embedding with the Segre embedding.

## Main definitions

* `Faltings.projToBase`: the structure morphism `ℙⁿ_S ⟶ S`.

## Main results

* `Faltings.exists_isImmersion_toProjectiveSpaceOver`: over an affine base, a relatively very
  ample invertible module has a generating family of global sections whose morphism
  `φ_s : Y ⟶ ℙⁿ_S` is an immersion.
* `Faltings.CurveWithDegreeOneDivisor.isRelativelyVeryAmple_of_picardClass_eq_vojtaClass`:
  an invertible module on `C ×_k C` of class `vojtaClass X N N 0 = H_N`, `N ≥ 2g + 1`, is very
  ample over `k`.

## Implementation notes

The class `H_N` is `Faltings.CurveWithDegreeOneDivisor.vojtaClass X N N 0`, the class
`N (P × C) + N (C × P)`. Very ampleness is a property of an invertible module, not of a class;
it is invariant under isomorphism, so "the class is very ample" is stated for every invertible
module in the class. Very ampleness is Stacks' relative notion (Tag 01VM),
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, over the base `Spec k`, the notion in which
[Stacks, Tag 0H2V] (degree `≥ 2g + 1` on a curve) is stated.

The Segre embedding `ℙⁿ ×_S ℙᵐ ⟶ ℙ^{nm+n+m}` is never formed. Very ampleness over an affine
base gives generating families `s` of `M₁` and `t` of `M₂` whose morphisms to projective space
are immersions ([Stacks, Tag 02NP], [Stacks, Tag 01ND]); the products `s_α t_β` generate
`pr₁^* M₁ ⊗ pr₂^* M₂`, and the morphism they define pulls `𝒪(1)` back to `pr₁^* M₁ ⊗ pr₂^* M₂`
by construction. On the chart of `s_α t_β` it becomes `φ_s × φ_t` after the two linear
projections `T_{α'β} ↦ T_{α'}` and `T_{αβ'} ↦ T_{β'}`, because
`(s_{α'} t_β)/(s_α t_β) = s_{α'}/s_α` and `(s_α t_{β'})/(s_α t_β) = t_{β'}/t_β`; a product of
immersions is an immersion ([Stacks, Tag 07RK]), so this morphism is an immersion.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 0H2V](https://stacks.math.columbia.edu/tag/0H2V)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 07RK](https://stacks.math.columbia.edu/tag/07RK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.ProductFamilyTwist
  Stacks.ProductFamilyRatio

universe u

namespace Faltings

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-- The structure morphism `ℙⁿ_S ⟶ S`. -/
noncomputable abbrev projToBase (n : ℕ) (S : Scheme.{u}) : projectiveSpaceOver n S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))

section ProductFamily

variable {X : Scheme.{u}} {F G : X.Modules} [IsInvertibleModule X F] [IsInvertibleModule X G]

omit [IsInvertibleModule X F] [IsInvertibleModule X G] in
/-- The product `s t` of two global sections is `s` multiplied on the left onto `t`. -/
private theorem prodSection_eq_mulLeft (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    prodSection s t =
      (Stacks.TensorSectionNonvanishing.mulLeft (unitOfSection F s) G).app ⊤ t := by
  rw [prodSection, Stacks.TensorSectionNonvanishing.unitMul_eq_mulLeft,
    Stacks.SectionProduct.globalSection_comp, globalSection_unitOfSection]

/-- The chart of a product family lies in the chart of the second family. -/
private theorem nvCover_prodFamily_le_right {ι κ : Type*} (s : ι → Γ(F, ⊤))
    (t : κ → Γ(G, ⊤)) (p : ι × κ) :
    nvCover (prodFamily s t) p ≤ nvCover t p.2 := by
  rw [show nvCover (prodFamily s t) p = nvOpen (F ⊗ G) (prodSection (s p.1) (t p.2)) from rfl,
    nvOpen_prodSection]
  exact inf_le_right

/-- **The coordinate ratios of a product family along a fixed first index are the coordinate
ratios of the second family**: `(s_α t_{β'}) / (s_α t_β) = t_{β'} / t_β`. -/
private theorem ratio_prodFamily_right {ι κ : Type*} (s : ι → Γ(F, ⊤)) (t : κ → Γ(G, ⊤))
    (a : ι) (b b' : κ) :
    ratio (prodFamily s t) (a, b) (a, b') =
      resO (nvCover_prodFamily_le_right s t (a, b)) (ratio t b b') := by
  refine (eq_div (prodFamily s t (a, b)) le_rfl ?_).symm
  change resO (nvCover_prodFamily_le_right s t (a, b)) (ratio t b b') •
      resT (nvCover (prodFamily s t) (a, b)) (prodSection (s a) (t b)) =
    resT (nvCover (prodFamily s t) (a, b)) (prodSection (s a) (t b'))
  have hn : ∀ (W : X.Opens) (x : Γ(G, ⊤)),
      resT W ((Stacks.TensorSectionNonvanishing.mulLeft (unitOfSection F (s a)) G).app ⊤ x) =
        (Stacks.TensorSectionNonvanishing.mulLeft (unitOfSection F (s a)) G).app W
          (resT W x) := fun W x =>
    (PresheafOfModules.naturality_apply
      (Stacks.TensorSectionNonvanishing.mulLeft (unitOfSection F (s a)) G).val
      (homOfLE (le_top : W ≤ ⊤)).op x).symm
  rw [prodSection_eq_mulLeft, prodSection_eq_mulLeft, hn, hn, ← Scheme.Modules.Hom.app_smul,
    resO_ratio_smul t (nvCover_prodFamily_le_right s t (a, b)) b']

/-- **The product family of two pinned families pins an immersion as soon as the pair of the two
pinned morphisms is one.** Let `s` and `t` be generating families of global sections of
invertible modules `F` and `G` on an `S`-scheme `X`, with pinned morphisms `j₁ : X ⟶ ℙⁿ_S` and
`j₂ : X ⟶ ℙᵐ_S`. If `(j₁, j₂) : X ⟶ ℙⁿ_S ×_S ℙᵐ_S` is an immersion, so is the morphism
`X ⟶ ℙ^{nm+n+m}_S` pinned by the products `s_α t_β`: on the chart of `s_α t_β` it becomes
`(j₁, j₂)` after the two linear projections `T_{α'β} ↦ T_{α'}` and `T_{αβ'} ↦ T_{β'}`, which is
the Segre embedding read on charts. -/
private theorem isImmersion_toProjectiveSpaceOver_prodFamily {X S : Scheme.{u}} (f : X ⟶ S)
    {F G : X.Modules} [IsInvertibleModule X F] [IsInvertibleModule X G] {n m : ℕ}
    (s : Fin (n + 1) → Γ(F, ⊤)) (hs : GeneratesStalks s)
    (t : Fin (m + 1) → Γ(G, ⊤)) (ht : GeneratesStalks t)
    (hP : GeneratesStalks (prodFamily s t ∘ segreIndexEquiv n m))
    (himm : IsImmersion (pullback.lift (f := projToBase n S) (g := projToBase m S)
      (toProjectiveSpaceOver s hs f) (toProjectiveSpaceOver t ht f)
      ((toProjectiveSpaceOver_fst s hs f).trans (toProjectiveSpaceOver_fst t ht f).symm))) :
    IsImmersion (toProjectiveSpaceOver (prodFamily s t ∘ segreIndexEquiv n m) hP f) := by
  set P := prodFamily s t ∘ segreIndexEquiv n m with hPdef
  set q := toProjectiveSpaceOver P hP f
  have hqchart := fun k => ι_toProjectiveSpaceOver P hP f k
  have hPφ : ∀ p : Fin (n + 1) × Fin (m + 1), P (segreIdx n m p.1 p.2) = prodFamily s t p :=
    fun p => by simp [hPdef]
  refine Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover P hP q
    hqchart (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) ?_ ?_
  · intro x
    obtain ⟨k, hk⟩ := exists_mem_nvCover_of_generatesStalks _ hP x
    exact ⟨segreIndexEquiv n m k, by simpa only [segreIdx_segreIndexEquiv] using hk⟩
  · rintro ⟨α, β⟩
    set i := segreIdx n m α β
    have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart P hP q hqchart i
    set g := q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S i) (nvCover P i)
      hpre.ge
    refine ⟨g, ?_, Scheme.Hom.resLE_comp_ι _ _⟩
    have hcov : nvCover P i = nvCover (prodFamily s t) (α, β) :=
      Stacks.ChartImmersionFinish.nvCover_reindex (prodFamily s t) P
        (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) hPφ (α, β)
    have hle₁ : nvCover P i ≤ nvCover s α :=
      hcov.le.trans (nvCover_prodFamily_le_left s t (α, β))
    have hle₂ : nvCover P i ≤ nvCover t β :=
      hcov.le.trans (nvCover_prodFamily_le_right s t (α, β))
    -- the coordinate ratios of `P` along the two factors
    have hratio₁ : ∀ α', ratio P i (segreIdx n m α' β) = resO hle₁ (ratio s α α') := by
      intro α'
      rw [Stacks.ChartImmersionFinish.ratio_reindex (prodFamily s t) P
        (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) hPφ (α, β) (α', β),
        ratio_prodFamily, Stacks.ChartImmersionFinish.resO_resO]
    have hratio₂ : ∀ β', ratio P i (segreIdx n m α β') = resO hle₂ (ratio t β β') := by
      intro β'
      rw [Stacks.ChartImmersionFinish.ratio_reindex (prodFamily s t) P
        (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) hPφ (α, β) (α, β'),
        ratio_prodFamily_right, Stacks.ChartImmersionFinish.resO_resO]
    -- the two linear projections out of the chart
    let h₁ : Fin (n + 1) → Γ((projectiveSpaceOver.standardChart (n * m + n + m) S i).toScheme, ⊤) :=
      fun α' => chartCoordScheme (n * m + n + m) S i (segreIdx n m α' β)
    let h₂ : Fin (m + 1) → Γ((projectiveSpaceOver.standardChart (n * m + n + m) S i).toScheme, ⊤) :=
      fun β' => chartCoordScheme (n * m + n + m) S i (segreIdx n m α β')
    have hh₁ : Ideal.span (Set.range h₁) = ⊤ := span_range_chartProjFamily n m S α β
    have hh₂ : Ideal.span (Set.range h₂) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      exact Ideal.subset_span ⟨β, chartCoordScheme_self _ S i⟩
    have hpull₁ : ∀ α', g.appTop (h₁ α') = (X.homOfLE hle₁).appTop (chartRatio s α α') := by
      intro α'
      rw [appTop_resLE_chartCoordScheme P q i (hqchart i) hpre.ge (segreIdx n m α' β),
        chartRatio, chartRatio, Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv, hratio₁ α']
    have hpull₂ : ∀ β', g.appTop (h₂ β') = (X.homOfLE hle₂).appTop (chartRatio t β β') := by
      intro β'
      rw [appTop_resLE_chartCoordScheme P q i (hqchart i) hpre.ge (segreIdx n m α β'),
        chartRatio, chartRatio, Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv, hratio₂ β']
    have hc₁ := Stacks.LinearChartProjection.resLE_comp_chartProjOf P s q
      (toProjectiveSpaceOver_fst P hP f) (toProjectiveSpaceOver s hs f)
      (toProjectiveSpaceOver_fst s hs f) i α (ι_toProjectiveSpaceOver s hs f α) hle₁ hpre.ge
      h₁ hh₁ hpull₁
    have hc₂ := Stacks.LinearChartProjection.resLE_comp_chartProjOf P t q
      (toProjectiveSpaceOver_fst P hP f) (toProjectiveSpaceOver t ht f)
      (toProjectiveSpaceOver_fst t ht f) i β (ι_toProjectiveSpaceOver t ht f β) hle₂ hpre.ge
      h₂ hh₂ hpull₂
    have hw : Stacks.LinearChartProjection.chartProjOf i h₁ hh₁ ≫ projToBase n S =
        Stacks.LinearChartProjection.chartProjOf i h₂ hh₂ ≫ projToBase m S :=
      (Stacks.AmpleProjectiveImmersion.liftOver_fst _ _).trans
        (Stacks.AmpleProjectiveImmersion.liftOver_fst _ _).symm
    have hcomp : g ≫ pullback.lift _ _ hw = (nvCover P i).ι ≫
        pullback.lift (f := projToBase n S) (g := projToBase m S)
          (toProjectiveSpaceOver s hs f) (toProjectiveSpaceOver t ht f)
          ((toProjectiveSpaceOver_fst s hs f).trans (toProjectiveSpaceOver_fst t ht f).symm) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        exact hc₁
      · simp only [Category.assoc, pullback.lift_snd]
        exact hc₂
    have : IsImmersion (g ≫ pullback.lift _ _ hw) := by
      rw [hcomp]
      infer_instance
    exact IsImmersion.of_comp g (pullback.lift _ _ hw)

end ProductFamily

section VeryAmple

/-- **A relatively very ample invertible module is the pullback of `𝒪(1)` along the morphism
`φ_{(M, (s₀, …, sₙ))}` of a generating family, and that morphism is an immersion.** Over an
affine base and for a morphism of finite type, very ampleness gives an immersion into some
`ℙⁿ_S` pulling `𝒪(1)` back to `M` ([Stacks, Tag 02NP]); the pulled back coordinates are a
generating family, and the immersion is the morphism they define ([Stacks, Tag 01ND]). -/
theorem exists_isImmersion_toProjectiveSpaceOver {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsAffine S] (M : Y.Modules)
    [IsInvertibleModule Y M] (hM : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f M) :
    ∃ (n : ℕ) (s : Fin (n + 1) → Γ(M, ⊤)) (hs : GeneratesStalks s),
      IsImmersion (toProjectiveSpaceOver s hs f) := by
  obtain ⟨n, φ, hφ, hover, ⟨e⟩⟩ :=
    Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple f M hM
  have hT := (Stacks.ProjectiveSpaceModuli.pullbackTuple φ
    (Stacks.ProjectiveSpaceModuli.universalTupleOver n S)).generates
  have hs := generatesStalks_congr e.symm hT
  refine ⟨n, _, hs, ?_⟩
  have hφeq := (Stacks.ProjectiveSpaceModuli.eq_toProjectiveSpaceOver_iff _ hs f φ).2
    ⟨hover, e.symm, fun i => rfl⟩
  exact hφeq ▸ hφ

/-- **An invertible module whose generating family defines an immersion into `ℙⁿ_S` is very
ample relative to `S`**, `M` being the pullback of `𝒪(1)` along that immersion. -/
private theorem isRelativelyVeryAmple_of_isImmersion_toProjectiveSpaceOver {Y S : Scheme.{u}}
    [IsAffine S] (f : Y ⟶ S) (M : Y.Modules) [IsInvertibleModule Y M] {n : ℕ}
    (s : Fin (n + 1) → Γ(M, ⊤)) (hs : GeneratesStalks s)
    (h : IsImmersion (toProjectiveSpaceOver s hs f)) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f M := by
  obtain ⟨α, -⟩ := Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver s hs f
  exact Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver
    (fun m => Stacks.SymGraded.hasFreeBundleTwistOne S m) f M
    ⟨n, _, h, toProjectiveSpaceOver_fst s hs f, ⟨α.symm⟩⟩

/-- **The external tensor product of two relatively very ample invertible modules is very
ample** over an affine base: if `M₁` is very ample for `f₁ : Y₁ ⟶ S` and `M₂` for
`f₂ : Y₂ ⟶ S`, then `pr₁^* M₁ ⊗ pr₂^* M₂` is very ample for `Y₁ ×_S Y₂ ⟶ S`. -/
private theorem isRelativelyVeryAmple_tensorObj_pullback {S Y₁ Y₂ : Scheme.{u}} [IsAffine S]
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂] (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    [IsInvertibleModule Y₁ M₁] [IsInvertibleModule Y₂ M₂]
    (h₁ : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f₁ M₁)
    (h₂ : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f₂ M₂) :
    haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.fst f₁ f₂) M₁
    haveI := Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd f₁ f₂) M₂
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (pullback.fst f₁ f₂ ≫ f₁)
      ((Scheme.Modules.pullback (pullback.fst f₁ f₂)).obj M₁ ⊗
        (Scheme.Modules.pullback (pullback.snd f₁ f₂)).obj M₂) := by
  have := Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.fst f₁ f₂) M₁
  have := Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd f₁ f₂) M₂
  obtain ⟨n, s, hs, hj₁⟩ := exists_isImmersion_toProjectiveSpaceOver f₁ M₁ h₁
  obtain ⟨m, t, ht, hj₂⟩ := exists_isImmersion_toProjectiveSpaceOver f₂ M₂ h₂
  set p₁ := pullback.fst f₁ f₂
  set p₂ := pullback.snd f₁ f₂
  have hs' := (Stacks.ProjectiveSpaceModuli.pullbackTuple p₁ ⟨M₁, inferInstance, s, hs⟩).generates
  have ht' := (Stacks.ProjectiveSpaceModuli.pullbackTuple p₂ ⟨M₂, inferInstance, t, ht⟩).generates
  have e₁ : toProjectiveSpaceOver _ hs' (p₁ ≫ f₁) = p₁ ≫ toProjectiveSpaceOver s hs f₁ := by
    apply pullback.hom_ext
    · rw [toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst]
    · rw [toProjectiveSpaceOver_snd, Category.assoc, toProjectiveSpaceOver_snd,
        comp_toProjectiveSpaceAtUniverse s hs p₁ hs']
      rfl
  have e₂ : toProjectiveSpaceOver _ ht' (p₁ ≫ f₁) = p₂ ≫ toProjectiveSpaceOver t ht f₂ := by
    apply pullback.hom_ext
    · rw [toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst, pullback.condition]
    · rw [toProjectiveSpaceOver_snd, Category.assoc, toProjectiveSpaceOver_snd,
        comp_toProjectiveSpaceAtUniverse t ht p₂ ht']
      rfl
  have hP := generatesStalks_comp_equiv (segreIndexEquiv n m) (generatesStalks_prodFamily hs' ht')
  refine isRelativelyVeryAmple_of_isImmersion_toProjectiveSpaceOver _ _ _ hP
    (isImmersion_toProjectiveSpaceOver_prodFamily _ _ hs' _ ht' hP ?_)
  have : MorphismProperty.IsStableUnderComposition @IsImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hmap := MorphismProperty.pullbackMap (P := @IsImmersion) (f := f₁) (g := f₂)
    (f' := projToBase n S) (g' := projToBase m S) hj₁ hj₂
    (toProjectiveSpaceOver_fst s hs f₁).symm (toProjectiveSpaceOver_fst t ht f₂).symm
  convert hmap using 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pullback.lift_fst, e₁]
  · rw [pullback.lift_snd, pullback.lift_snd, e₂]

end VeryAmple

section PicardClass

/-- **The class in `Pic(Y)` of a tensor product is the sum of the classes**: `[A ⊗ B] = [A] + [B]`
for invertible `𝒪_Y`-modules `A` and `B`. -/
theorem picardClass_tensorObj (Y : Scheme.{u}) (A B : Y.Modules)
    (hA : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) A)
    (hB : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) B)
    (hAB : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (A ⊗ B)) :
    Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (A ⊗ B) hAB =
      Stacks.SheafOfModules.picardClass Y.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) A hA +
        Stacks.SheafOfModules.picardClass Y.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) B hB := by
  have hT := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) _ _ _ _ hA hB
  exact ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ hT).2
    ⟨Stacks.TensorSheafSpellingIso.monoidalTensorIso _ _ _⟩).trans
    (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hA hB hT).symm

/-- **The class of an external tensor product is the sum of the pulled back classes**:
`[g₁^* M ⊗ g₂^* M] = g₁^*[M] + g₂^*[M]` in `Pic(Y)`, for `g₁ g₂ : Y ⟶ Z`. -/
private theorem picardClass_tensorObj_pullback {Y Z : Scheme.{u}} (g₁ g₂ : Y ⟶ Z)
    (M : Z.Modules) (hM : Stacks.SheafOfModules.IsInvertible Z.presheaf
      (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) M)
    (h : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
      ((Scheme.Modules.pullback g₁).obj M ⊗ (Scheme.Modules.pullback g₂).obj M)) :
    Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
        ((Scheme.Modules.pullback g₁).obj M ⊗ (Scheme.Modules.pullback g₂).obj M) h =
      Stacks.Picard.schemePullbackClassHom g₁ (Stacks.SheafOfModules.picardClass Z.presheaf
          (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) M hM) +
        Stacks.Picard.schemePullbackClassHom g₂ (Stacks.SheafOfModules.picardClass Z.presheaf
          (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) M hM) := by
  have : IsInvertibleModule Z M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ M).mp hM
  have hpull : ∀ (g : Y ⟶ Z) (hg : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) ((Scheme.Modules.pullback g).obj M)),
      Stacks.SheafOfModules.picardClass Y.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
          ((Scheme.Modules.pullback g).obj M) hg =
        Stacks.Picard.schemePullbackClassHom g (Stacks.SheafOfModules.picardClass Z.presheaf
          (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) M hM) := fun g _ =>
    ((Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom M hM).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
        ⟨((Stacks.ProjectiveBundleQuotients.pullbackIso g).app M).symm⟩)).symm
  have hA := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr (Stacks.InvertiblePullback.isInvertibleModule_pullback g₁ M)
  have hB := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr (Stacks.InvertiblePullback.isInvertibleModule_pullback g₂ M)
  rw [← hpull g₁ hA, ← hpull g₂ hB]
  exact picardClass_tensorObj Y _ _ hA hB h

end PicardClass

namespace CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- **`H_N` is very ample on `C × C`.** Let `(C, P)` be a curve over `k` with a divisor of
degree one, of genus `g`, and `N ≥ 2g + 1`. Every invertible module `L` on `C ×_k C` whose class
in `Pic(C ×_k C)` is `H_N = vojtaClass X N N 0 = pr₁^*[𝒪_C(NP)] + pr₂^*[𝒪_C(NP)]` is very ample
relative to `C ×_k C ⟶ Spec k`. -/
@[faltings "lem_nt_h_ample_c_times_c"]
theorem isRelativelyVeryAmple_of_picardClass_eq_vojtaClass (X : CurveWithDegreeOneDivisor k)
    (N : ℤ) (hN : 2 * (genus X.f : ℤ) + 1 ≤ N) (L : (pullback X.f X.f).Modules)
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f) L]
    (hL : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          L).mpr ‹_›) = X.vojtaClass N N 0) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (pullback.fst X.f X.f ≫ X.f) L := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hdim1 : topologicalKrullDim X.C = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k X.f
  -- an invertible module `𝒪_C(NP)` of class `N [𝒪_C(P)]`
  obtain ⟨M, hMs, hM⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.C.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) (N • X.classP)
  have : IsInvertibleModule X.C M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ M).mp hMs
  -- `𝒪_C(NP)` has degree `N`, so it is very ample, [Stacks, Tag 0H2V]
  let S : CohenMacaulayCurveSituation.{u} :=
    { k := k, X := X.C, f := X.f, dimension_one := hdim1 }
  have : GeometricallyIntegral S.f := (inferInstance : GeometricallyIntegral X.f)
  have hMva : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple X.f M := by
    refine S.isRelativelyVeryAmple_of_two_mul_genus_add_one_le M ?_
    change 2 * (genus X.f : ℤ) + 1 ≤ invertibleCurveDegree k X.f hdim1.le M
    rwa [← invertibleCurveDegreeHom_picardClass k X.f hdim1.le M hMs, hM, map_zsmul,
      X.invertibleCurveDegreeHom_classP, smul_eq_mul, mul_one]
  -- `pr₁^* 𝒪_C(NP) ⊗ pr₂^* 𝒪_C(NP)` is very ample and of class `H_N`
  have : IsInvertibleModule (pullback X.f X.f)
      ((Scheme.Modules.pullback (pullback.fst X.f X.f)).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ M
  have : IsInvertibleModule (pullback X.f X.f)
      ((Scheme.Modules.pullback (pullback.snd X.f X.f)).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ M
  have hABi := Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj
    ((Scheme.Modules.pullback (pullback.fst X.f X.f)).obj M)
    ((Scheme.Modules.pullback (pullback.snd X.f X.f)).obj M)
  have hABs := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr hABi
  have hclass := picardClass_tensorObj_pullback (pullback.fst X.f X.f) (pullback.snd X.f X.f) M
    hMs hABs
  rw [hM, map_zsmul, map_zsmul] at hclass
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ L _ _ hABs).1 (hL.trans <| by
    rw [vojtaClass,
      (zero_smul ℤ _ : (0 : ℤ) • _ = (0 : Stacks.Picard.ofScheme (pullback X.f X.f))), add_zero]
    exact hclass.symm)
  exact @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple.of_iso _ _ _ _ _ hABi _ e.symm
    (isRelativelyVeryAmple_tensorObj_pullback X.f X.f M M hMva hMva)

end CurveWithDegreeOneDivisor

end Faltings
