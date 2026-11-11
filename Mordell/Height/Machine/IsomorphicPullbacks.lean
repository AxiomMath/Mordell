module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import Mordell.Height.Weil.LinearMapLower
public import Mordell.Height.Weil.LinearMapUpper
public import Mordell.AlgebraicGeometry.ProjectiveSpace.MorphismOfSections
public import Mordell.AlgebraicGeometry.ClosedImage
public import Mordell.Height.Weil.Galois
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import StacksFrontier.AlgebraicGeometry.Cube.SectionNeighbourhood
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates

/-!
# Morphisms with isomorphic pullbacks of `𝒪(1)` have heights differing by a bounded amount

Let `X` be a projective variety over a field `k` algebraic over `ℚ` (in the source, `k = ℚ̄`),
and let `φ : X ⟶ ℙⁿ_k` and `ψ : X ⟶ ℙᵐ_k` be morphisms of `k`-schemes, not necessarily
embeddings, with `φ^* 𝒪(1) ≅ ψ^* 𝒪(1)`. Then `h ∘ φ - h ∘ ψ` is bounded on `X(k)`, where `h` is
the absolute logarithmic Weil height `Faltings.weilHeight`.

For the proof, the sections `φ^* T₀, …, φ^* Tₙ` of `L = φ^* 𝒪(1)` and
`ψ^* T₀, …, ψ^* Tₘ` (carried to `L` by the isomorphism) have no common zero, so they define a
morphism `λ : X ⟶ ℙ^{n+m+1}_k` with `λ^* 𝒪(1) ≅ L`, whose image `Z` is closed. The coordinate
projections `A`, `B` onto the two blocks satisfy `A ∘ λ = φ`, `B ∘ λ = ψ`, and their zero loci do
not meet `Z`. The upper bound for linear maps and the lower bound for linear maps on a closed
subvariety bound `h ∘ φ - h ∘ λ` and `h ∘ ψ - h ∘ λ`, and one subtracts.

## Main results

* `Faltings.exists_abs_weilHeight_sub_le_of_pullback_iso`: there is a constant `C` with
  `|h(φ(p)) - h(ψ(p))| ≤ C` for every `k`-point `p` of `X`.

## Implementation notes

A `k`-point of `X` is a section `p : Spec k ⟶ X` of the structure morphism `f`. Its image
`φ ∘ p` is a `k`-point of `ℙⁿ_k`, read as a point of `ℙ k (Fin (n + 1) → k)` as in
`Faltings.ProjectiveEmbedding.height`: through the coordinate isomorphism
`AlgebraicGeometry.basisProjectiveSpaceOfModuleIso` of the standard basis, the identification
of `k`-points of `𝐏(V)` with lines of functionals on `V`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient`,
`AlgebraicGeometry.ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual`), and the
dual-basis identification of a functional with its coordinate vector. The section of `𝐏(kⁿ⁺¹)`
is quantified over together with the equation pinning it to `φ ∘ p`, which determines it. The
sheaf `𝒪(1)` on `ℙⁿ_k` is `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n
(Spec k)`.

In the source, `λ` is given by a basis of `H⁰(X, L)`; here it is given by the `n + m + 2`
sections themselves, so that `A` and `B` are coordinate projections and the finite
dimensionality of `H⁰(X, L)` is not used.

The homogeneous coordinates of `φ(p)`, `ψ(p)` and `λ(p)` are compared through the affine chart
values `(T_j / T_i)(p)`: two morphisms whose coordinates are the same sections of one line bundle
pull back the same ratios `T_j / T_i`. The closed set `Z` is recorded by the homogeneous members
of its vanishing ideal. The lower bound on a closed subvariety holds over an algebraically closed
field, so the points are moved to the algebraic closure of `k`, which preserves the height
(`Faltings.weilHeight_mk_map`); the projective Nullstellensatz over `k` shows that the zero set
of these forms over any extension of `k` still avoids the zero loci of `A` and `B`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Prop. 5.1.3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

/-! ### Charts of `ℙᴺ_k` and their coordinates -/

section Charts

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section ChartValues

variable {k : Type u} [Field k] {N : ℕ}

/-- **The chart values of two charts containing a `k`-point are proportional.** -/
private theorem mk_chartVal_eq_mk_chartVal (w : Spec (.of k) ⟶ Proj (polyGrading k N))
    (hw : w ≫ projToSpecCoeff k N = 𝟙 _) (a b : Fin (N + 1))
    (ha : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X a))
    (hb : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X b)) :
    Projectivization.mk k (chartVal w b hb) (chartVal_ne_zero w b hb) =
      Projectivization.mk k (chartVal w a ha) (chartVal_ne_zero w a ha) := by
  have key : ∀ j, chartVal w b hb j = chartVal w b hb a * chartVal w a ha j := by
    intro j
    have hl : (MvPolynomial.X j - MvPolynomial.C (chartVal w a ha j) * MvPolynomial.X a :
        MvPolynomial (Fin (N + 1)) k).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X k j).sub (MvPolynomial.isHomogeneous_C_mul_X _ a)
    have h1 := (mem_asHomogeneousIdeal_iff_eval_chartVal w hw a ha hl default).mpr
      (by simp [chartVal_self])
    have h2 := (mem_asHomogeneousIdeal_iff_eval_chartVal w hw b hb hl default).mp h1
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C] at h2
    linear_combination h2
  exact (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
    ⟨chartVal w b hb a, funext fun j => by rw [Pi.smul_apply, smul_eq_mul, ← key]⟩

/-- The chart values of a composite `p ≫ v` are read off from the pull-backs along `v` of the
chart functions to any open `W` through which `p` factors. -/
public theorem chartVal_eq_of_comp {X : Scheme.{u}} (p : Spec (.of k) ⟶ X)
    (v : X ⟶ Proj (polyGrading k N)) (w : Spec (.of k) ⟶ Proj (polyGrading k N))
    (hwv : p ≫ v = w) (i : Fin (N + 1))
    (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i)) {W : X.Opens}
    (hW : W ≤ v ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i)) (hp : ⊤ ≤ p ⁻¹ᵁ W)
    (j : Fin (N + 1)) :
    chartVal w i hi j = (Scheme.ΓSpecIso (.of k)).hom (p.appLE W ⊤ hp (v.appLE _ W hW
      ((Proj.awayToSection (polyGrading k N) (MvPolynomial.X i)).hom
        (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j)))) := by
  subst hwv
  unfold chartVal
  rw [← Scheme.Hom.appLE_comp_appLE p v _ W ⊤ hW hp, CommRingCat.comp_apply]

end ChartValues

section Nullstellensatz

variable {k : Type u} [Field k] {N : ℕ}

/-- **The projective Nullstellensatz on a closed set.** Let `Z ⊆ Proj k[T₀, …, T_N]` be closed
and `T` a finite family of linear forms with no common zero on `Z`. Then a power of every
homogeneous polynomial of positive degree lies in the ideal generated by the vanishing ideal of
`Z` and the `T i`. -/
private theorem exists_pow_eq_add_sum_mul {ι : Type*} [Fintype ι]
    (Z : Set (ProjectiveSpectrum (polyGrading k N))) (hZ : IsClosed Z)
    (T : ι → MvPolynomial (Fin (N + 1)) k) (hT : ∀ i, T i ∈ polyGrading k N 1)
    (hZT : ∀ z ∈ Z, ∃ i, T i ∉ z.asHomogeneousIdeal)
    {a : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (ha : a ∈ polyGrading k N d) (hd : d ≠ 0) :
    ∃ e : ℕ, ∃ R ∈ ProjectiveSpectrum.vanishingIdeal Z,
      ∃ G : ι → MvPolynomial (Fin (N + 1)) k, a ^ e = R + ∑ i, G i * T i := by
  set J := ProjectiveSpectrum.vanishingIdeal Z
  have hspan : (Ideal.span (Set.range T)).IsHomogeneous (polyGrading k N) :=
    Ideal.homogeneous_span _ _ (by rintro _ ⟨i, rfl⟩; exact ⟨1, hT i⟩)
  have hI : (J.toIdeal ⊔ Ideal.span (Set.range T)).IsHomogeneous (polyGrading k N) :=
    J.isHomogeneous.sup hspan
  have hrad : a ∈ (J.toIdeal ⊔ Ideal.span (Set.range T)).radical := by
    rw [hI.radical_eq, Submodule.mem_sInf]
    rintro P ⟨hPh, hIP, hPp⟩
    by_cases hirr : (HomogeneousIdeal.irrelevant (polyGrading k N)).toIdeal ≤ P
    · apply hirr
      rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ ha hd]
    · exfalso
      let x : ProjectiveSpectrum (polyGrading k N) :=
        ⟨⟨P, hPh⟩, hPp, hirr⟩
      have hx : x ∈ Z := by
        rw [← hZ.closure_eq, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
        exact fun r hr => hIP (Ideal.mem_sup_left hr)
      obtain ⟨i, hi⟩ := hZT x hx
      exact hi (hIP (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  obtain ⟨e, he⟩ := hrad
  obtain ⟨R, hR, y, hy, hRy⟩ := Submodule.mem_sup.mp he
  obtain ⟨G, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
  exact ⟨e, R, hR, G, hRy.symm⟩

/-- A vector killing the images of the homogeneous members of a homogeneous ideal kills the
images of all its members. -/
private theorem eval_map_eq_zero_of_mem {K : Type*} [CommRing K] (τ : k →+* K)
    (J : HomogeneousIdeal (polyGrading k N)) (V : Fin (N + 1) → K)
    (hV : ∀ R ∈ J, ∀ d, R.IsHomogeneous d → MvPolynomial.eval V (MvPolynomial.map τ R) = 0)
    {R : MvPolynomial (Fin (N + 1)) k} (hR : R ∈ J) :
    MvPolynomial.eval V (MvPolynomial.map τ R) = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose (polyGrading k N) R, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => hV _ (J.isHomogeneous d hR) d ?_
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).1 (SetLike.coe_mem _)

/-- **Zeros of the vanishing ideal of a closed set off a family of linear forms.** If a vector
over a field `K ⊇ k` kills the homogeneous members of the vanishing ideal of a closed
`Z ⊆ Proj k[T₀, …, T_N]` and a family of linear forms without common zero on `Z`, it kills every
homogeneous polynomial of positive degree. -/
private theorem eval_map_eq_zero_of_isClosed {K : Type*} [Field K] (τ : k →+* K) {ι : Type*}
    [Finite ι] (Z : Set (ProjectiveSpectrum (polyGrading k N))) (hZ : IsClosed Z)
    (T : ι → MvPolynomial (Fin (N + 1)) k) (hT : ∀ i, T i ∈ polyGrading k N 1)
    (hZT : ∀ z ∈ Z, ∃ i, T i ∉ z.asHomogeneousIdeal) (V : Fin (N + 1) → K)
    (hV : ∀ R ∈ ProjectiveSpectrum.vanishingIdeal Z, ∀ d, R.IsHomogeneous d →
      MvPolynomial.eval V (MvPolynomial.map τ R) = 0)
    (hVT : ∀ i, MvPolynomial.eval V (MvPolynomial.map τ (T i)) = 0)
    {a : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (ha : a ∈ polyGrading k N d) (hd : d ≠ 0) :
    MvPolynomial.eval V (MvPolynomial.map τ a) = 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨e, R, hR, G, he⟩ := exists_pow_eq_add_sum_mul Z hZ T hT hZT ha hd
  have h := congrArg (fun F => MvPolynomial.eval V (MvPolynomial.map τ F)) he
  simp only [map_pow, map_add, map_sum, map_mul, hVT, mul_zero, Finset.sum_const_zero, add_zero,
    eval_map_eq_zero_of_mem τ _ V hV hR] at h
  exact eq_zero_of_pow_eq_zero h

end Nullstellensatz

section Sections

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ}

/-- The pull-back `t^* T_j` of the `j`-th homogeneous coordinate along a morphism
`t : X ⟶ ℙʳ_k`, a global section of `t^* 𝒪(1)`. -/
@[expose] public noncomputable abbrev coordSection (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (j : Fin (r + 1)) :
    Γ((Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))), ⊤) :=
  pullbackGlobalSections t _ (pullbackGlobalSections
    (projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k))) (twistingSheafAtUniverse r)
    (coordGlobalSection r j))

/-- A relation `s = a • t` between restrictions of global sections pulls back along any
morphism. -/
public theorem res_pullbackGlobalSections_eq_smul {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (F : Z.Modules) (T : Z.Opens) (a : Γ(Z, T)) (s t : Γ(F, ⊤))
    (h : F.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op s =
      a • F.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op t) :
    ((Scheme.Modules.pullback g).obj F).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ T ≤ ⊤)).op
        (pullbackGlobalSections g F s) =
      g.app T a • ((Scheme.Modules.pullback g).obj F).presheaf.map
        (homOfLE (le_top : g ⁻¹ᵁ T ≤ ⊤)).op (pullbackGlobalSections g F t) := by
  rw [← pullbackGlobalSections_res, ← pullbackGlobalSections_res, h, pullbackSectionOn_smul]

/-- The preimage in `ℙʳ_k` of the chart `D₊(Tᵢ)` of `ℙʳ_ℤ`, read in the polynomial model. -/
private theorem preimage_toIntegral_basicOpen (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (i : Fin (r + 1)) :
    (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ Proj.basicOpen (polyGrading k r)
        (MvPolynomial.X i) =
      t ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) ⁻¹ᵁ
        Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading r) (MvPolynomial.X i)) := by
  rw [← (polynomialComparison k r).toIntegral, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  erw [Stacks.ProjectiveSpaceChartRatio.coordinateProjMap_preimage_basicOpen k r i]

/-- **The transition identity for pulled-back coordinates.** Over an open `W` mapping into the
chart `D₊(Tᵢ)`, `t^* T_j = t^♯(T_j / T_i) · t^* T_i`. -/
public theorem resT_coordSection (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (i j : Fin (r + 1)) {W : X.Opens}
    (hW : W ≤ (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i)) :
    resT W (coordSection t j) =
      (t ≫ (polynomialComparison k r).iso.hom).appLE _ W hW
          ((Proj.awayToSection (polyGrading k r) (MvPolynomial.X i)).hom
            (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r i j)) •
        resT W (coordSection t i) := by
  set T := projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k))
  set U := Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading r) (MvPolynomial.X i)
  have h0 := coordGlobalSection_res_eq r i j
  have h1 := res_pullbackGlobalSections_eq_smul T _ U _ _ _ h0
  have h2 := res_pullbackGlobalSections_eq_smul t _ (T ⁻¹ᵁ U) _ _ _ h1
  have hW' : W ≤ t ⁻¹ᵁ (T ⁻¹ᵁ U) := hW.trans (preimage_toIntegral_basicOpen t i).le
  have h3 := congrArg (resM hW') h2
  rw [resM_smul] at h3
  simp only [resM, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at h3
  refine h3.trans ?_
  congr 1
  have e1 : Proj.basicOpen (polyGrading k r) (MvPolynomial.X i) ≤
      coordinateProjMap k r (integralGradedHom k r) (mapDomain_integralGradedHom_eq_top k r) ⁻¹ᵁ
        Proj.basicOpen (polyGrading (ULift.{u} ℤ) r) (MvPolynomial.X i) :=
    (Stacks.ProjectiveSpaceChartRatio.coordinateProjMap_preimage_basicOpen k r i).ge
  have hWT : W ≤ (t ≫ T) ⁻¹ᵁ U := by rw [Scheme.Hom.comp_preimage]; exact hW'
  refine Eq.trans (b := (t ≫ T).appLE U W hWT
    ((Proj.awayToSection (Stacks.SectionsToProjectiveSpace.coordGrading r)
      (MvPolynomial.X i)).hom (coordFrac i j))) ?_ ?_
  · rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    exact (Stacks.TwistPullbackPinned.appLE_apply t _ W hW' _).symm
  rw [appLE_congr_hom (show t ≫ T = (t ≫ (polynomialComparison k r).iso.hom) ≫
      coordinateProjMap k r (integralGradedHom k r) (mapDomain_integralGradedHom_eq_top k r) by
    rw [Category.assoc]; exact congrArg (t ≫ ·) (polynomialComparison k r).toIntegral.symm)
    U W _ (hW.trans (Scheme.Hom.preimage_mono _ e1))]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ W e1 hW, CommRingCat.comp_apply]
  have key := Stacks.ProjectiveSpaceChartRatio.appLE_awayToSection_coordinateProjMap k r i e1
    (coordFrac i j)
  rw [Stacks.ProjectiveSpaceChartRatio.chartBaseChange_coordFrac] at key
  exact congrArg _ key

/-- **[Stacks, Tag 0H78] for `AlgebraicGeometry.pullbackGlobalSections`**: a pulled-back global
section does not vanish at `x` exactly when the section does not vanish at the image of `x`. -/
public theorem mem_nonvanishingLocus_pullbackGlobalSections_iff {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) (y : Y) :
    y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback g).obj M)
        (pullbackGlobalSections g M s) ↔
      g.base y ∈ Stacks.Ample.nonvanishingLocus M s := by
  have hsec : pullbackGlobalSections g M s =
      Stacks.NonvanishingPullback.pullbackGlobalSection g M s := by
    change ((Scheme.Modules.pullback g).obj M).presheaf.map
        (eqToHom (show g ⁻¹ᵁ (⊤ : Z.Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection g M s) = _
    exact Functor.map_id_apply _ _ _
  rw [hsec]
  exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff g M s y

/-- **`t^* T_j` does not vanish at `x` exactly when `t(x)` lies in the chart `D₊(T_j)`.** -/
public theorem mem_nonvanishingLocus_coordSection_iff
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (j : Fin (r + 1)) (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus _ (coordSection t j) ↔
      (t ≫ (polynomialComparison k r).iso.hom).base x ∈
        Proj.basicOpen (polyGrading k r) (MvPolynomial.X j) := by
  rw [mem_nonvanishingLocus_pullbackGlobalSections_iff,
    mem_nonvanishingLocus_pullbackGlobalSections_iff]
  rw [show (t ≫ (polynomialComparison k r).iso.hom).base x ∈
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X j) ↔
      x ∈ (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
        Proj.basicOpen (polyGrading k r) (MvPolynomial.X j) from Iff.rfl,
    preimage_toIntegral_basicOpen]
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (Stacks.SectionsToProjectiveSpace.coordGrading r) 1 1
    ⟨MvPolynomial.X j, Stacks.SectionsToProjectiveSpace.X_mem_coordGrading_one j⟩
    (by rw [whereInvertible_coordGrading_eq_top]; trivial)

/-- A morphism of `𝒪_X`-modules commutes with restricting global sections. -/
public theorem resT_hom_app {L M : X.Modules} (β : L ⟶ M) (W : X.Opens) (s : Γ(L, ⊤)) :
    resT W (β.app ⊤ s) = β.app W (resT W s) :=
  (PresheafOfModules.naturality_apply β.val (homOfLE (le_top : W ≤ ⊤)).op s).symm

/-- The transition identity, carried along a morphism of modules `t^* 𝒪(1) ⟶ L`. -/
public theorem resT_hom_app_coordSection (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    {L : X.Modules}
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ⟶ L)
    (i j : Fin (r + 1)) {W : X.Opens}
    (hW : W ≤ (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i)) :
    resT W (β.app ⊤ (coordSection t j)) =
      (t ≫ (polynomialComparison k r).iso.hom).appLE _ W hW
          ((Proj.awayToSection (polyGrading k r) (MvPolynomial.X i)).hom
            (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r i j)) •
        resT W (β.app ⊤ (coordSection t i)) := by
  rw [resT_hom_app, resT_hom_app, resT_coordSection t i j hW, Scheme.Modules.Hom.app_smul]

/-- **Two morphisms to projective space whose coordinates are the same sections of one line
bundle have the same chart functions.** If `β : t^* 𝒪(1) ≅ L` and `β' : t'^* 𝒪(1) ⟶ L` carry
`t^* T_j` and `t'^* T_{σ j}` to the same section of `L` for every `j`, then on an open mapping
into `D₊(Tᵢ)` under `t` and into `D₊(T_{σ i})` under `t'`, the pull-backs of `T_j / T_i` and of
`T_{σ j} / T_{σ i}` agree. -/
private theorem appLE_coordFracAt_eq {r' : ℕ} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ L)
    (β' : (Scheme.Modules.pullback t').obj (projectiveSpaceTwistingSheaf r' (Spec (.of k))) ⟶ L)
    (σ : Fin (r + 1) → Fin (r' + 1))
    (hσ : ∀ j, β.hom.app ⊤ (coordSection t j) = β'.app ⊤ (coordSection t' (σ j)))
    (i j : Fin (r + 1)) {W : X.Opens}
    (hW : W ≤ (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i))
    (hW' : W ≤ (t' ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X (σ i))) :
    (t ≫ (polynomialComparison k r).iso.hom).appLE _ W hW
        ((Proj.awayToSection (polyGrading k r) (MvPolynomial.X i)).hom
          (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r i j)) =
      (t' ≫ (polynomialComparison k r').iso.hom).appLE _ W hW'
        ((Proj.awayToSection (polyGrading k r') (MvPolynomial.X (σ i))).hom
          (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r' (σ i) (σ j))) := by
  have hnv : W ≤ nvOpen L (β.hom.app ⊤ (coordSection t i)) := by
    intro x hx
    change x ∈ Stacks.Ample.nonvanishingLocus L (β.hom.app ⊤ (coordSection t i))
    rw [show β.hom.app ⊤ (coordSection t i) = β.hom.val.app (Opposite.op ⊤) (coordSection t i)
      from rfl, Cube.nonvanishingLocus_hom_app_top_of_iso, mem_nonvanishingLocus_coordSection_iff]
    exact hW hx
  have h1 := resT_hom_app_coordSection t β.hom i j hW
  have h2 := resT_hom_app_coordSection t' β' (σ i) (σ j) hW'
  rw [← hσ, ← hσ] at h2
  exact eq_of_smul_eq_smul _ hnv (h1.symm.trans h2)

end Sections

section Geometry

open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The point of `ℙ k (Fin (r + 1) → k)` attached to a `k`-point `q` of `𝐏(k^{r+1})`: the
one-dimensional quotient of `q`, read as the class of a coordinate vector. -/
@[expose] public noncomputable abbrev coordPoint {r : ℕ}
    (q : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (r + 1) → k) //
      q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _}) : ℙ k (Fin (r + 1) → k) :=
  (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
    (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ q)).map
      (Pi.basisFun k (Fin (r + 1))).toDualEquiv.symm.toLinearMap
      (Pi.basisFun k (Fin (r + 1))).toDualEquiv.symm.injective

/-- A morphism out of `Spec k` maps the whole of `Spec k` into an open containing the image of
its one point. -/
public theorem top_le_preimage_of_mem {Y : Scheme.{u}} (w : Spec (.of k) ⟶ Y) {U : Y.Opens}
    (h : w.base default ∈ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro a _
  rwa [Subsingleton.elim a default]

/-- **Coordinates that are the same sections of one line bundle cut out the same charts.** If
`β : t^* 𝒪(1) ≅ L` and `β' : t'^* 𝒪(1) ≅ L` carry `t^* T_j` and `t'^* T_{σ j}` to the same
section of `L`, then `t(x) ∈ D₊(T_j)` exactly when `t'(x) ∈ D₊(T_{σ j})`. -/
private theorem mem_basicOpen_iff_of_iso {r r' : ℕ} {L : X.Modules}
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ L)
    (β' : (Scheme.Modules.pullback t').obj (projectiveSpaceTwistingSheaf r' (Spec (.of k))) ≅ L)
    (j : Fin (r + 1)) (j' : Fin (r' + 1))
    (h : β.hom.app ⊤ (coordSection t j) = β'.hom.app ⊤ (coordSection t' j')) (x : X) :
    (t ≫ (polynomialComparison k r).iso.hom).base x ∈
        Proj.basicOpen (polyGrading k r) (MvPolynomial.X j) ↔
      (t' ≫ (polynomialComparison k r').iso.hom).base x ∈
        Proj.basicOpen (polyGrading k r') (MvPolynomial.X j') := by
  rw [← mem_nonvanishingLocus_coordSection_iff, ← mem_nonvanishingLocus_coordSection_iff,
    ← Cube.nonvanishingLocus_hom_app_top_of_iso β, ← Cube.nonvanishingLocus_hom_app_top_of_iso β']
  exact Iff.of_eq (congrArg (x ∈ Stacks.Ample.nonvanishingLocus L ·) h)

/-- **Two morphisms to projective space whose coordinates are the same sections of one line
bundle have the same chart values at a `k`-point.** -/
private theorem chartVal_comp_eq {r r' : ℕ} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ L)
    (β' : (Scheme.Modules.pullback t').obj (projectiveSpaceTwistingSheaf r' (Spec (.of k))) ⟶ L)
    (σ : Fin (r + 1) → Fin (r' + 1))
    (hσ : ∀ j, β.hom.app ⊤ (coordSection t j) = β'.app ⊤ (coordSection t' (σ j)))
    (p : Spec (.of k) ⟶ X) (i : Fin (r + 1))
    (hi : ⊤ ≤ ((p ≫ t) ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i))
    (hi' : ⊤ ≤ ((p ≫ t') ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X (σ i))) (j : Fin (r + 1)) :
    chartVal _ i hi j = chartVal _ (σ i) hi' (σ j) := by
  set W := (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i) ⊓
    (t' ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X (σ i))
  have hp : ⊤ ≤ p ⁻¹ᵁ W := fun a ha => ⟨by simpa using hi ha, by simpa using hi' ha⟩
  rw [chartVal_eq_of_comp p _ _ (Category.assoc _ _ _).symm i hi inf_le_left hp j,
    chartVal_eq_of_comp p _ _ (Category.assoc _ _ _).symm (σ i) hi' inf_le_right hp (σ j),
    appLE_coordFracAt_eq t t' β β' σ hσ i j]

/-- Restricting two representatives of the same point to the same coordinates gives the same
point, when the restrictions are nonzero. -/
private theorem mk_comp_eq_mk_comp {ι κ : Type*} {a b : ι → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Projectivization.mk k a ha = Projectivization.mk k b hb) (g : κ → ι)
    (hag : a ∘ g ≠ 0) (hbg : b ∘ g ≠ 0) :
    Projectivization.mk k (a ∘ g) hag = Projectivization.mk k (b ∘ g) hbg := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' k _ _ ha hb).1 h
  exact (Projectivization.mk_eq_mk_iff' k _ _ hag hbg).2 ⟨c, by rw [← hc]; rfl⟩

/-- **Nonvanishing of both blocks.** If every point of a closed `Z ⊆ Proj k[T₀, …, T_{n+m+1}]`
lies off some hyperplane `T_j = 0` with `j` in the first block and off some `T_{n+1+l} = 0` in
the second, then every nonzero common zero of the homogeneous members of the vanishing ideal of
`Z`, over any field `K ⊇ k`, has both blocks of coordinates nonzero. -/
private theorem blocks_ne_zero_of_isClosed {n m : ℕ}
    (Z : Set (ProjectiveSpectrum (polyGrading k (n + 1 + m)))) (hZ : IsClosed Z)
    (hZφ : ∀ z ∈ Z, ∃ j, MvPolynomial.X (Fin.castAdd (m + 1) j) ∉ z.asHomogeneousIdeal)
    (hZψ : ∀ z ∈ Z, ∃ l : Fin (m + 1),
      MvPolynomial.X (Fin.natAdd (n + 1) l : Fin (n + 1 + m + 1)) ∉ z.asHomogeneousIdeal)
    (K : Type u) [Field K] (τ : k →+* K) (V : Fin (n + 1 + (m + 1)) → K) (hV : V ≠ 0)
    (hVS : ∀ F ∈ {F : MvPolynomial (Fin (n + 1 + (m + 1))) k |
        F ∈ ProjectiveSpectrum.vanishingIdeal Z ∧ ∃ d, F.IsHomogeneous d},
      MvPolynomial.eval V (MvPolynomial.map τ F) = 0) :
    (fun j => V (Fin.castAdd (m + 1) j)) ≠ 0 ∧ (fun l => V (Fin.natAdd (n + 1) l)) ≠ 0 := by
  have key : ∀ {ι : Type} [Finite ι] (T : ι → Fin (n + 1 + (m + 1))),
      (∀ z ∈ Z, ∃ i, MvPolynomial.X (T i) ∉ z.asHomogeneousIdeal) → (fun i => V (T i)) ≠ 0 := by
    intro ι _ T hZT h0
    refine hV (funext fun a => ?_)
    have := eval_map_eq_zero_of_isClosed τ Z hZ (fun i => MvPolynomial.X (T i))
      (fun i => MvPolynomial.isHomogeneous_X k (T i)) hZT V
      (fun R hR d hd => hVS R ⟨hR, d, hd⟩) (fun i => by simpa using congrFun h0 i)
      (MvPolynomial.isHomogeneous_X k a) one_ne_zero
    simpa using this
  exact ⟨key _ hZφ, key _ hZψ⟩

/-- **The geometric half of the comparison.** For morphisms `φ : X ⟶ ℙⁿ_k`, `ψ : X ⟶ ℙᵐ_k`
with `φ^* 𝒪(1) ≅ ψ^* 𝒪(1)`, there is a set `S` of homogeneous polynomials in `n + m + 2`
variables such that every common zero of `S` over any field has both blocks of coordinates
nonzero, and such that every `k`-point `p` of `X` has a coordinate vector `v`, a common zero of
`S`, whose two blocks are homogeneous coordinates of `φ(p)` and `ψ(p)`.

The vector `v` is the image of `p` under the morphism `λ = (φ^* T₀ : ⋯ : φ^* Tₙ : ψ^* T₀ : ⋯ :
ψ^* Tₘ) : X ⟶ ℙ^{n+m+1}_k` defined by the sections of `L = φ^* 𝒪(1)`, `ψ^* Tₗ` being carried to
`L` by the given isomorphism, and `S` is the set of homogeneous members of the vanishing ideal of
the closed image `λ(X)`. -/
private theorem exists_relations {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] {n m : ℕ}
    (φ : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφ : φ ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = f)
    (ψ : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hψ : ψ ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k) = f)
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅
      (Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf m (Spec (.of k)))) :
    ∃ S : Set (MvPolynomial (Fin (n + 1 + (m + 1))) k), (∀ F ∈ S, ∃ d, F.IsHomogeneous d) ∧
      (∀ (K : Type u) [Field K] (τ : k →+* K) (V : Fin (n + 1 + (m + 1)) → K), V ≠ 0 →
        (∀ F ∈ S, MvPolynomial.eval V (MvPolynomial.map τ F) = 0) →
          (fun j => V (Fin.castAdd (m + 1) j)) ≠ 0 ∧ (fun l => V (Fin.natAdd (n + 1) l)) ≠ 0) ∧
      ∀ (p : Spec (.of k) ⟶ X), p ≫ f = 𝟙 _ →
      ∀ (qφ : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (n + 1) → k) //
          q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _})
        (qψ : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (m + 1) → k) //
          q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _}),
        qφ.1 = p ≫ φ ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (n + 1)))).inv.left →
        qψ.1 = p ≫ ψ ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (m + 1)))).inv.left →
        ∃ v : Fin (n + 1 + (m + 1)) → k, (∀ F ∈ S, MvPolynomial.eval v F = 0) ∧
          ∃ (h₁ : (fun j => v (Fin.castAdd (m + 1) j)) ≠ 0)
            (h₂ : (fun l => v (Fin.natAdd (n + 1) l)) ≠ 0),
            coordPoint qφ = Projectivization.mk k _ h₁ ∧
              coordPoint qψ = Projectivization.mk k _ h₂ := by
  classical
  set L := (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n (Spec (.of k)))
  let s : Fin (n + 1 + (m + 1)) → Γ(L, ⊤) :=
    Fin.append (coordSection φ) fun l => e.inv.app ⊤ (coordSection ψ l)
  have hsφ : ∀ j, s (Fin.castAdd (m + 1) j) = coordSection φ j := fun j => Fin.append_left _ _ j
  have hsψ : ∀ l, s (Fin.natAdd (n + 1) l) = e.inv.app ⊤ (coordSection ψ l) := fun l =>
    Fin.append_right _ _ l
  have hs : ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus L (s j) := by
    intro x
    obtain ⟨j, hj⟩ := exists_mem_basicOpen φ x
    exact ⟨Fin.castAdd (m + 1) j, by rw [hsφ, mem_nonvanishingLocus_coordSection_iff]; exact hj⟩
  obtain ⟨t, ht, α, hα⟩ :=
    exists_hom_and_iso_pullback_projectiveSpaceTwistingSheaf f L (r := n + 1 + m) s hs
  have trφ : ∀ x j, (φ ≫ (polynomialComparison k n).iso.hom).base x ∈
      Proj.basicOpen (polyGrading k n) (MvPolynomial.X j) ↔
      (t ≫ (polynomialComparison k (n + 1 + m)).iso.hom).base x ∈
        Proj.basicOpen (polyGrading k (n + 1 + m)) (MvPolynomial.X (Fin.castAdd (m + 1) j)) :=
    fun x j => mem_basicOpen_iff_of_iso φ t (Iso.refl _) α j _ (by rw [hα, hsφ]; rfl) x
  have trψ : ∀ x l, (ψ ≫ (polynomialComparison k m).iso.hom).base x ∈
      Proj.basicOpen (polyGrading k m) (MvPolynomial.X l) ↔
      (t ≫ (polynomialComparison k (n + 1 + m)).iso.hom).base x ∈
        Proj.basicOpen (polyGrading k (n + 1 + m)) (MvPolynomial.X (Fin.natAdd (n + 1) l)) :=
    fun x l => mem_basicOpen_iff_of_iso ψ t e.symm α l _ (by rw [hα, hsψ]; rfl) x
  set g := t ≫ (polynomialComparison k (n + 1 + m)).iso.hom
  set Z : Set (ProjectiveSpectrum (polyGrading k (n + 1 + m))) := Set.range g.base
  have hZ : IsClosed Z := by
    have : IsProper f := inferInstance
    have : IsSeparated (projToSpecCoeff k (n + 1 + m)) := inferInstance
    exact isClosed_range_of_isProper_of_isSeparated g f (projToSpecCoeff k (n + 1 + m))
      (by
        rw [Category.assoc,
          Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff]
        exact ht)
  have hZφ : ∀ z ∈ Z, ∃ j, MvPolynomial.X (Fin.castAdd (m + 1) j) ∉ z.asHomogeneousIdeal := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := exists_mem_basicOpen φ x
    exact ⟨j, (trφ x j).1 hj⟩
  have hZψ : ∀ z ∈ Z, ∃ l : Fin (m + 1),
      MvPolynomial.X (Fin.natAdd (n + 1) l : Fin (n + 1 + m + 1)) ∉ z.asHomogeneousIdeal := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl⟩ := exists_mem_basicOpen ψ x
    exact ⟨l, (trψ x l).1 hl⟩
  set S : Set (MvPolynomial (Fin (n + 1 + (m + 1))) k) :=
    {F | F ∈ ProjectiveSpectrum.vanishingIdeal Z ∧ ∃ d, F.IsHomogeneous d}
  have hnz : ∀ (K : Type u) [Field K] (τ : k →+* K) (V : Fin (n + 1 + (m + 1)) → K), V ≠ 0 →
      (∀ F ∈ S, MvPolynomial.eval V (MvPolynomial.map τ F) = 0) →
        (fun j => V (Fin.castAdd (m + 1) j)) ≠ 0 ∧ (fun l => V (Fin.natAdd (n + 1) l)) ≠ 0 :=
    blocks_ne_zero_of_isClosed Z hZ hZφ hZψ
  refine ⟨S, fun F hF => hF.2, hnz, fun p hp qφ qψ hqφ hqψ => ?_⟩
  set x₀ := p.base default
  obtain ⟨j, hj⟩ := exists_mem_basicOpen φ x₀
  obtain ⟨l, hl⟩ := exists_mem_basicOpen ψ x₀
  have hjφ : ⊤ ≤ ((p ≫ φ) ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k n) (MvPolynomial.X j) :=
    top_le_preimage_of_mem _ hj
  have hlψ : ⊤ ≤ ((p ≫ ψ) ≫ (polynomialComparison k m).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k m) (MvPolynomial.X l) :=
    top_le_preimage_of_mem _ hl
  have hjt : ⊤ ≤ ((p ≫ t) ≫ (polynomialComparison k (n + 1 + m)).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k (n + 1 + m)) (MvPolynomial.X (Fin.castAdd (m + 1) j)) :=
    top_le_preimage_of_mem _ ((trφ x₀ j).1 hj)
  have hlt : ⊤ ≤ ((p ≫ t) ≫ (polynomialComparison k (n + 1 + m)).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k (n + 1 + m)) (MvPolynomial.X (Fin.natAdd (n + 1) l)) :=
    top_le_preimage_of_mem _ ((trψ x₀ l).1 hl)
  set w := (p ≫ t) ≫ (polynomialComparison k (n + 1 + m)).iso.hom
  have hw : w ≫ projToSpecCoeff k (n + 1 + m) = 𝟙 _ := by
    rw [Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff,
      Category.assoc]
    erw [ht]
    rw [hp]
  set v := chartVal w _ hjt
  have hv0 : v ≠ 0 := chartVal_ne_zero w _ hjt
  have hvS : ∀ F ∈ S, MvPolynomial.eval v F = 0 := by
    rintro F ⟨hFZ, d, hd⟩
    refine (mem_asHomogeneousIdeal_iff_eval_chartVal w hw _ hjt hd default).1 ?_
    exact (ProjectiveSpectrum.mem_vanishingIdeal _ _).1 hFZ _ ⟨x₀, rfl⟩
  obtain ⟨h₁, h₂⟩ := hnz k (RingHom.id k) v hv0 (by simpa using hvS)
  refine ⟨v, hvS, h₁, h₂, ?_, ?_⟩
  · refine (dictionary_eq_mk_chartVal (p ≫ φ) qφ (hqφ.trans (Category.assoc p φ _).symm)
      (by
        rw [Category.assoc,
          Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff,
          Category.assoc]
        erw [hφ]
        rw [hp]) j hjφ).trans ?_
    exact mk_congr (funext fun j' => chartVal_comp_eq φ t (Iso.refl _) α.hom
      (Fin.castAdd (m + 1)) (fun j => by rw [hα, hsφ]; rfl) p j hjφ hjt j') _ _
  · refine (dictionary_eq_mk_chartVal (p ≫ ψ) qψ (hqψ.trans (Category.assoc p ψ _).symm)
      (by
        rw [Category.assoc,
          Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff,
          Category.assoc]
        erw [hψ]
        rw [hp]) l hlψ).trans ?_
    have e1 : chartVal _ l hlψ = chartVal w _ hlt ∘ Fin.natAdd (n + 1) :=
      funext fun l' => chartVal_comp_eq ψ t e.symm α.hom (Fin.natAdd (n + 1))
        (fun l => by rw [hα, hsψ]; rfl) p l hlψ hlt l'
    have h₃ : chartVal w _ hlt ∘
        (Fin.natAdd (n + 1) : Fin (m + 1) → Fin (n + 1 + (m + 1))) ≠ 0 := by
      rw [← e1]; exact chartVal_ne_zero _ l hlψ
    have h₄ := mk_comp_eq_mk_comp (chartVal_ne_zero w _ hlt) hv0
      (mk_chartVal_eq_mk_chartVal w hw _ _ hjt hlt)
      (Fin.natAdd (n + 1) : Fin (m + 1) → Fin (n + 1 + (m + 1))) h₃ h₂
    exact (mk_congr e1 _ h₃).trans h₄

end Geometry

end Charts

section Heights

variable {K : Type u} [Field K]

/-- The matrix of the linear map `v ↦ v ∘ g` restricting a vector to the coordinates `g j`. -/
private noncomputable def restrictMatrix {ι κ : Type*} [DecidableEq ι] (g : κ → ι) :
    κ × ι → K :=
  fun p => if p.2 = g p.1 then 1 else 0

private theorem sum_restrictMatrix_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] (g : κ → ι)
    (V : ι → K) : (fun j => ∑ i, restrictMatrix g (j, i) * V i) = V ∘ g := by
  funext j
  simp [restrictMatrix]

private theorem restrictMatrix_ne_zero {ι κ : Type*} [DecidableEq ι] [Nonempty κ] (g : κ → ι) :
    (restrictMatrix g : κ × ι → K) ≠ 0 := fun h => by
  obtain ⟨j⟩ := ‹Nonempty κ›
  simpa [restrictMatrix] using congrFun h (j, g j)

variable [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

/-- **Restricting coordinates on a closed set.** If the coordinates `g j` have no common zero on
the zero set of a family `S` of forms over an algebraically closed `K / ℚ`, then on that zero set
the height of `[v ∘ g]` and of `[v]` differ by a bounded amount. -/
private theorem exists_abs_weilHeight_comp_sub_le [IsAlgClosed K] {ι κ : Type*} [Fintype ι]
    [LinearOrder ι] [Fintype κ] [LinearOrder κ] [Nonempty κ] (g : κ → ι)
    (S : Set (MvPolynomial ι K)) (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d)
    (hg : ∀ V : ι → K, V ≠ 0 → (∀ F ∈ S, MvPolynomial.eval V F = 0) → V ∘ g ≠ 0) :
    ∃ C : ℝ, ∀ (V : ι → K) (hV : V ≠ 0) (hVg : V ∘ g ≠ 0),
      (∀ F ∈ S, MvPolynomial.eval V F = 0) →
      |weilHeight (Projectivization.mk K (V ∘ g) hVg) -
        weilHeight (Projectivization.mk K V hV)| ≤ C := by
  classical
  let : LinearOrder (κ × ι) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hA := restrictMatrix_ne_zero (K := K) g
  obtain ⟨C, hC⟩ := weilHeight_le_weilHeight_linearMap_apply_add (restrictMatrix g) hA S
    hS fun V hV hVS => by rw [sum_restrictMatrix_mul]; exact hg V hV hVS
  refine ⟨max C (weilHeight (Projectivization.mk K _ hA) + Real.log (Fintype.card ι)), ?_⟩
  intro V hV hVg hVS
  have hAV : (fun j => ∑ i, restrictMatrix g (j, i) * V i) ≠ 0 := by
    rw [sum_restrictMatrix_mul]; exact hVg
  have e := mk_congr (K := K) (sum_restrictMatrix_mul g V) hAV hVg
  have h1 := hC V hV hAV hVS
  have h2 := weilHeight_linearMap_apply_le (restrictMatrix g) hA V hV hAV
  rw [e] at h1 h2
  exact abs_le.2 ⟨by linarith [le_max_left C (weilHeight (Projectivization.mk K _ hA) +
    Real.log (Fintype.card ι))], by linarith [le_max_right C (weilHeight
      (Projectivization.mk K _ hA) + Real.log (Fintype.card ι))]⟩

end Heights

/-- Let `X` be a projective variety over a field `k` algebraic over `ℚ`, with structure morphism
`f`, and let `φ : X ⟶ ℙⁿ_k`, `ψ : X ⟶ ℙᵐ_k` be morphisms of `k`-schemes with
`φ^* 𝒪(1) ≅ ψ^* 𝒪(1)`. Then there is a constant `C` with `|h(φ(p)) - h(ψ(p))| ≤ C` for every
`k`-point `p` of `X`, where `h` is `Faltings.weilHeight` and `φ(p)`, `ψ(p)` are read in
homogeneous coordinates as points of `ℙ k (Fin (n + 1) → k)`, `ℙ k (Fin (m + 1) → k)`. -/
@[faltings "lem_ht_same_line_bundle_bounded"]
public theorem exists_abs_weilHeight_sub_le_of_pullback_iso {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] {n m : ℕ}
    (φ : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφ : φ ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = f)
    (ψ : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hψ : ψ ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k) = f)
    (e : (Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅
      (Scheme.Modules.pullback ψ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf m (Spec (.of k)))) :
    ∃ C : ℝ, ∀ (p : Spec (.of k) ⟶ X), p ≫ f = 𝟙 _ →
      ∀ (qφ : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k
          (Fin (n + 1) → k) // q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _})
        (qψ : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k
          (Fin (m + 1) → k) // q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _}),
        qφ.1 = p ≫ φ ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (n + 1)))).inv.left →
        qψ.1 = p ≫ ψ ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (m + 1)))).inv.left →
        |weilHeight ((ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
              (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ qφ)).map
                (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.toLinearMap
                (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.injective) -
          weilHeight ((ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
              (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ qψ)).map
                (Pi.basisFun k (Fin (m + 1))).toDualEquiv.symm.toLinearMap
                (Pi.basisFun k (Fin (m + 1))).toDualEquiv.symm.injective)| ≤ C := by
  obtain ⟨S, hShom, hSnz, hpts⟩ := exists_relations φ hφ ψ hψ e
  let K := AlgebraicClosure k
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  let τ : k →ₐ[ℚ] K := IsScalarTower.toAlgHom ℚ k K
  set S' : Set (MvPolynomial (Fin (n + 1 + (m + 1))) K) := MvPolynomial.map (τ : k →+* K) '' S
  have hS' : ∀ F ∈ S', ∃ d, F.IsHomogeneous d := by
    rintro _ ⟨F, hF, rfl⟩
    obtain ⟨d, hd⟩ := hShom F hF
    exact ⟨d, hd.map _⟩
  have hnz := fun (V : Fin (n + 1 + (m + 1)) → K) (hV : V ≠ 0)
      (hVS : ∀ F ∈ S', MvPolynomial.eval V F = 0) =>
    hSnz K τ V hV fun F hF => hVS _ ⟨F, hF, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_abs_weilHeight_comp_sub_le (Fin.castAdd (m + 1)) S' hS'
    fun V hV hVS => (hnz V hV hVS).1
  obtain ⟨C₂, hC₂⟩ := exists_abs_weilHeight_comp_sub_le (Fin.natAdd (n + 1)) S' hS'
    fun V hV hVS => (hnz V hV hVS).2
  refine ⟨C₁ + C₂, fun p hp qφ qψ hqφ hqψ => ?_⟩
  obtain ⟨v, hvS, h₁, h₂, e₁, e₂⟩ := hpts p hp qφ qψ hqφ hqψ
  change |weilHeight (coordPoint qφ) - weilHeight (coordPoint qψ)| ≤ _
  rw [e₁, e₂, ← weilHeight_mk_map τ _ h₁, ← weilHeight_mk_map τ _ h₂]
  set V : Fin (n + 1 + (m + 1)) → K := fun i => τ (v i)
  have hV : V ≠ 0 := fun h => h₁ (funext fun j =>
    (map_eq_zero τ).1 (congrFun h (Fin.castAdd (m + 1) j)))
  have hVS : ∀ F ∈ S', MvPolynomial.eval V F = 0 := by
    rintro _ ⟨F, hF, rfl⟩
    exact (MvPolynomial.map_eval (τ : k →+* K) v F).symm.trans (by rw [hvS F hF, map_zero])
  have h₁' := (hnz V hV hVS).1
  have h₂' := (hnz V hV hVS).2
  exact (abs_sub_le (weilHeight (Projectivization.mk K _ h₁')) (weilHeight
    (Projectivization.mk K V hV)) (weilHeight (Projectivization.mk K _ h₂'))).trans
    (add_le_add (hC₁ V hV h₁' hVS) (abs_sub_comm (weilHeight (Projectivization.mk K V hV)) _ ▸
      hC₂ V hV h₂' hVS))

end Faltings
