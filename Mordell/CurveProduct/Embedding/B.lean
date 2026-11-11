module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import Mordell.CurveProduct.H1Ample
public import Mordell.AlgebraicGeometry.VeryAmple.GloballyGenerated
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses

/-!
# The embedding `φ_B`

Let `(C, P)` be a curve over a field `k` with a divisor `P = ∑ nₓ x` of degree one, let
`X = C ×_k C` and let `Δ' = Δ - P × C - C × P`. There is `s₀` such that for every `s ≥ s₀` the
divisor `B = s (P × C) + s (C × P) - Δ'` is very ample. Concretely, let `L ≅ 𝒪_X(B)` be an
invertible `𝒪_X`-module of class
`Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)` in `Pic(X)`. Then `L` is very ample
relative to the structure morphism `X ⟶ Spec k`, and `H⁰(X, L)` is a nonzero
finite-dimensional `k`-vector space. For every `k`-basis `y₀, …, yₘ` of `H⁰(X, L)`, the
sections `yᵢ` generate `L` and the morphism `φ_B : X ⟶ ℙᵐ_k` they define is a closed immersion
over `k`, with an isomorphism `φ_B^* 𝒪(1) ≅ L` sending the `i`-th homogeneous coordinate to `yᵢ`.
So the hyperplane sections of `φ_B` are the divisors of the sections of `L`, that is the members
of `|B|`. Finally no `yᵢ` vanishes identically on `X`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver_vojtaClass`:
  for `s ≫ 0`, a `k`-basis of `H⁰(C ×_k C, 𝒪(B))` defines a closed immersion
  `C ×_k C ⟶ ℙᵐ_k` over `k` pulling `𝒪(1)` back to `𝒪(B)`, none of whose coordinates vanishes
  identically.

## Implementation notes

The divisor `B` enters through its class `vojtaClass X s s (-1)`, so `𝒪_X(B)` is any invertible
module `L` of that class; any two such are isomorphic. The `k`-module structure on `Γ(X, L)` is
restriction of scalars along `k → Γ(X, 𝒪_X)`, given by the structure morphism
`pullback.fst X.f X.f ≫ X.f`. Very ampleness is
`Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` for that structure morphism. The embedding is
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver`, and the comparison with `𝒪(1)` is stated,
as for `Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver`, on the
pull-back of `Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse` along the composite to the
integral model, pinned on the homogeneous coordinates. "`yᵢ` does not vanish identically" is the
statement that the nonvanishing locus of `yᵢ` is nonempty.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 01VM], [Stacks Project, Tag 01QA]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable {k : Type u} [Field k]

section Projection

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceChartRatio Stacks.ProductFamilyRatio

/-- On `X_{Pᵢ}`, the ratio of a combination `∑ₗ cₗ Pₗ` of the members of `P` by a member of
another family equal to `Pᵢ` is the combination `∑ₗ cₗ (Pₗ / Pᵢ)` of the ratios of `P`. -/
private theorem resO_ratio_eq_sum {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (f : X ⟶ Spec (.of R)) {N m : ℕ}
    (P : Fin (N + 1) → Γ(M, ⊤)) (t : Fin (m + 1) → Γ(M, ⊤)) (i : Fin (N + 1)) (β : Fin (m + 1))
    (hβ : t β = P i) (hle : nvCover P i ≤ nvCover t β) (a : Fin (N + 1) → R)
    (β' : Fin (m + 1)) (ht : t β' = ∑ l, baseRingHom f (a l) • P l) :
    resO hle (ratio t β β') =
      ∑ l, resO (le_top : nvCover P i ≤ ⊤) (baseRingHom f (a l)) * ratio P i l := by
  refine eq_of_smul_eq_smul (P i) le_rfl ?_
  have h1 : resT (nvCover P i) (P i) = resT (nvCover P i) (t β) := congrArg _ hβ.symm
  rw [h1, resO_ratio_smul t hle β', ← h1, ht, ← sum_mul_resO_ratio_smul P f le_rfl a]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact (congrArg (fun g => X.presheaf.map g (ratio P i l))
    (Subsingleton.elim _ (𝟙 _))).trans (by simp)

/-- The combination of a family with a standard basis vector of coefficients is the
corresponding member. -/
private theorem sum_single_smul {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {M : X.Modules}
    {N : ℕ} (P : Fin N → Γ(M, ⊤)) (i : Fin N) :
    ∑ l, baseRingHom f ((Pi.single i 1 : Fin N → k) l) • P l = P i := by
  rw [Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, map_one, one_smul]

/-- **A linear projection transports immersions back.** Let `P` and `t` be generating families
of global sections of an invertible module `M` on a scheme `X` over `k`, with
`t_β = ∑ₗ c_{βl} Pₗ`. Suppose the charts `X_{P_{ψ j}}` cover `X` and each `P_{ψ j}` is itself a
member of `t` with coefficient vector the standard basis vector. If the morphism
`φ_t : X ⟶ ℙᵐ_k` is an immersion, so is `φ_P : X ⟶ ℙᴺ_k`: on the chart `D₊(T_{ψ j})` the linear
projection `T ↦ (∑ₗ c_{βl} Tₗ)_β` is defined everywhere and carries `φ_P` to `φ_t`. -/
private theorem isImmersion_toProjectiveSpaceOver_of_eq_sum {X : Scheme.{u}} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (f : X ⟶ Spec (.of k)) {N m : ℕ}
    (P : Fin (N + 1) → Γ(M, ⊤)) (hP : GeneratesStalks P)
    (t : Fin (m + 1) → Γ(M, ⊤)) (ht : GeneratesStalks t)
    (c : Fin (m + 1) → Fin (N + 1) → k)
    (hc : ∀ β, t β = ∑ l, baseRingHom f (c β l) • P l)
    {J : Type*} (ψ : J → Fin (N + 1)) (hJ : ∀ x : X, ∃ j, x ∈ nvCover P (ψ j))
    (hψ : ∀ j, ∃ β, c β = Pi.single (ψ j) 1)
    (himm : IsImmersion (toProjectiveSpaceOver t ht f)) :
    IsImmersion (toProjectiveSpaceOver P hP f) := by
  set q := toProjectiveSpaceOver P hP f
  have hqchart := fun l => ι_toProjectiveSpaceOver P hP f l
  refine Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover P hP q
    hqchart ψ hJ fun j => ?_
  obtain ⟨β, hβ⟩ := hψ j
  set i := ψ j
  have htβ : t β = P i := by rw [hc β, hβ, sum_single_smul]
  have hle : nvCover P i ≤ nvCover t β := le_of_eq (congrArg _ htβ.symm)
  have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart P hP q hqchart i
  set g := q.resLE (projectiveSpaceOver.standardChart N (Spec (.of k)) i) (nvCover P i)
    hpre.ge
  refine ⟨g, ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  let κ := baseRingHom ((projectiveSpaceOver.standardChart N (Spec (.of k)) i).ι ≫
    projToBase N (Spec (.of k)))
  let h : Fin (m + 1) →
      Γ((projectiveSpaceOver.standardChart N (Spec (.of k)) i).toScheme, ⊤) :=
    fun β' => ∑ l, κ (c β' l) * chartCoordScheme N (Spec (.of k)) i l
  have hhβ : h β = 1 := by
    simp [h, hβ, Pi.single_apply, chartCoordScheme_self]
  have hh : Ideal.span (Set.range h) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hhβ]
    exact Ideal.subset_span ⟨β, rfl⟩
  have hκ : ∀ a : k, g.appTop (κ a) =
      (nvCover P i).topIso.inv (resO (le_top : nvCover P i ≤ ⊤) (baseRingHom f a)) := by
    intro a
    have e : g ≫ (projectiveSpaceOver.standardChart N (Spec (.of k)) i).ι ≫
        projToBase N (Spec (.of k)) = (nvCover P i).ι ≫ f := by
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg _ (toProjectiveSpaceOver_fst P hP f)
    rw [← baseRingHom_ι, ← e, ← baseRingHom_comp]
    rfl
  have hpull : ∀ β' : Fin (m + 1),
      g.appTop (h β') = (X.homOfLE hle).appTop (chartRatio t β β') := by
    intro β'
    rw [chartRatio, Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv,
      resO_ratio_eq_sum f P t i β htβ hle (c β') β' (hc β')]
    simp only [h, map_sum, map_mul, hκ]
    exact Finset.sum_congr rfl fun l _ =>
      congrArg _ (appTop_resLE_chartCoordScheme P q i (hqchart i) hpre.ge l)
  have hcomp := Stacks.LinearChartProjection.resLE_comp_chartProjOf P t q
    (toProjectiveSpaceOver_fst P hP f) (toProjectiveSpaceOver t ht f)
    (toProjectiveSpaceOver_fst t ht f) i β (ι_toProjectiveSpaceOver t ht f β) hle hpre.ge
    h hh hpull
  have : IsImmersion (g ≫ Stacks.LinearChartProjection.chartProjOf i h hh) :=
    hcomp ▸ inferInstance
  exact IsImmersion.of_comp g (Stacks.LinearChartProjection.chartProjOf i h hh)

/-- A family of global sections whose span contains a generating family of sections
generates. -/
private theorem generatesStalks_of_forall_mem_span {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M] {n m : ℕ}
    (s : Fin n → Γ(M, ⊤)) (hs : GeneratesStalks s) (t : Fin m → Γ(M, ⊤))
    (hst : letI : Module k Γ(M, ⊤) := Module.compHom _ (baseRingHom f)
      ∀ i, s i ∈ Submodule.span k (Set.range t)) :
    GeneratesStalks t :=
  generatesStalks_fin_of_mem_span f M t (fun i : ULift.{u} (Fin n) => s i.down)
    ((generatesStalks_ulift_iff s).2 hs) fun i => hst i.down

/-- **Every basis of the complete linear system of a very ample invertible module defines an
immersion.** Let `L` be very ample relative to `f : X ⟶ Spec k`, so that some generating family
`s` of global sections defines an immersion. Every `k`-basis `y` of `Γ(X, L)` then generates `L`,
and `φ_y` is an immersion: the concatenation `(s, y)` defines an immersion because `s` does (the
coordinate projection onto the `s`-part is defined on the charts of `s`), and `φ_y` is an
immersion because `φ_{(s, y)}` is the linear projection of `φ_y` by `T ↦ (s(T), T)`. -/
private theorem isImmersion_toProjectiveSpaceOver_basis {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) {m : ℕ}
    (y : letI : Module k Γ(L, ⊤) := Module.compHom _ (baseRingHom f)
      Module.Basis (Fin (m + 1)) k Γ(L, ⊤)) :
    ∃ hy : GeneratesStalks ⇑y, IsImmersion (toProjectiveSpaceOver ⇑y hy f) := by
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingHom f)
  obtain ⟨n, s, hs, himm⟩ := exists_isImmersion_toProjectiveSpaceOver f L hL
  have hy : GeneratesStalks ⇑y :=
    generatesStalks_of_forall_mem_span f s hs y fun i => y.mem_span _
  refine ⟨hy, ?_⟩
  let P : Fin (n + 1 + m + 1) → Γ(L, ⊤) := (Fin.append s ⇑y : Fin (n + 1 + (m + 1)) → Γ(L, ⊤))
  have hP : GeneratesStalks P := generatesStalks_of_forall_mem_span f s hs P fun i =>
    Submodule.subset_span ⟨Fin.castAdd (m + 1) i, Fin.append_left s (⇑y) i⟩
  have h1 : IsImmersion (toProjectiveSpaceOver P hP f) := by
    refine isImmersion_toProjectiveSpaceOver_of_eq_sum f P hP s hs
      (fun β => Pi.single (Fin.castAdd (m + 1) β) 1) (fun β => ?_) (Fin.castAdd (m + 1))
      (fun x => ?_) (fun j => ⟨j, rfl⟩) himm
    · rw [sum_single_smul]
      exact (Fin.append_left _ _ _).symm
    · obtain ⟨α, hα⟩ := exists_mem_nvCover_of_generatesStalks s hs x
      refine ⟨α, ?_⟩
      have : P (Fin.castAdd (m + 1) α) = s α := Fin.append_left _ _ _
      simpa only [nvCover, this] using hα
  refine isImmersion_toProjectiveSpaceOver_of_eq_sum f (⇑y) hy P hP
    (Fin.append (fun α => ⇑(y.repr (s α))) (fun j => Pi.single j 1) :
      Fin (n + 1 + (m + 1)) → Fin (m + 1) → k) ?_ id
    (fun x => exists_mem_nvCover_of_generatesStalks _ hy x)
    (fun j => ⟨Fin.natAdd (n + 1) j, Fin.append_right _ _ _⟩) h1
  refine Fin.addCases (m := n + 1) (n := m + 1) (fun α => ?_) (fun j => ?_)
  · rw [show P (Fin.castAdd (m + 1) α) = s α from Fin.append_left _ _ _, Fin.append_left]
    exact (y.sum_repr (s α)).symm
  · rw [show P (Fin.natAdd (n + 1) j) = y j from Fin.append_right _ _ _, Fin.append_right,
      sum_single_smul]

/-- **The embedding of a very ample invertible module by its complete linear system.** Let
`f : X ⟶ Spec k` be proper with `X` reduced and nonempty, and let `L` be very ample relative to
`f`. Then `Γ(X, L)` is a nonzero finite-dimensional `k`-vector space, and every `k`-basis
`y₀, …, yₘ` of it generates `L`, defines a closed immersion `φ_y : X ⟶ ℙᵐ_k` over `k` with
`φ_y^* 𝒪(1) ≅ L` carrying the `i`-th coordinate to `yᵢ`, and has no member vanishing
identically. -/
private theorem embedding_of_isRelativelyVeryAmple {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [IsReduced X] [Nonempty X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    0 < Module.finrank k Γ(L, ⊤) ∧
      ∀ {m : ℕ} (y : Module.Basis (Fin (m + 1)) k Γ(L, ⊤)),
        ∃ hy : GeneratesStalks ⇑y,
          IsClosedImmersion (toProjectiveSpaceOver ⇑y hy f) ∧
          (∃ α : (Scheme.Modules.pullback (toProjectiveSpaceOver ⇑y hy f ≫
                projectiveSpaceOver.toIntegralAtUniverse m _)).obj
                  (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ⟶ L,
            IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
              (toProjectiveSpaceOver ⇑y hy f ≫
                projectiveSpaceOver.toIntegralAtUniverse m _) i) = y i) ∧
          ∀ i, Stacks.NonvanishingOpen.nonvanishingOpen _ L (y i) ≠ ⊥ := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper f L
  refine ⟨?_, fun {m} y => ?_⟩
  · obtain ⟨n, s, hs, -⟩ := exists_isImmersion_toProjectiveSpaceOver f L hL
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs (Classical.arbitrary X)
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨s i, fun h0 => ?_⟩
    have : Classical.arbitrary X ∈ Stacks.Ample.nonvanishingLocus L (s i) := hi
    rwa [h0, Stacks.Ample.nonvanishingLocus_zero] at this
  obtain ⟨hy, himm⟩ := isImmersion_toProjectiveSpaceOver_basis f L hL y
  refine ⟨hy, ?_, ?_, fun i => ?_⟩
  · have : IsProper (Stacks.Tag01VT.projectiveSpaceHom m (Spec (.of k))) :=
      projectiveSpaceOver_isProper m (Spec (.of k))
    have : IsProper (toProjectiveSpaceOver ⇑y hy f ≫
        Stacks.Tag01VT.projectiveSpaceHom m (Spec (.of k))) :=
      (toProjectiveSpaceOver_fst _ hy f).symm ▸ inferInstance
    have : IsProper (toProjectiveSpaceOver ⇑y hy f) :=
      IsProper.of_comp _ (Stacks.Tag01VT.projectiveSpaceHom m (Spec (.of k)))
    have : IsPreimmersion (toProjectiveSpaceOver ⇑y hy f) := himm.toIsPreimmersion
    exact IsClosedImmersion.of_isPreimmersion _
      (toProjectiveSpaceOver ⇑y hy f).isClosedMap.isClosed_range
  · obtain ⟨α, hiso, hα⟩ :=
      exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse (⇑y) hy
    have hsnd := toProjectiveSpaceOver_snd (⇑y) hy f
    refine ⟨(Scheme.Modules.pullbackCongr hsnd).hom.app _ ≫ α, inferInstance, fun i => ?_⟩
    rw [← hα i]
    change α.app ⊤ (((Scheme.Modules.pullbackCongr hsnd).hom.app _).app ⊤ _) = _
    rw [pullbackCoordSection_eq, pullbackCoordSection_eq]
    exact congrArg (α.app ⊤) (pullbackSectionTop_congr hsnd _ _)
  · obtain ⟨x, hx⟩ := nonempty_nonvanishingLocus_of_ne_zero L (y i) (y.ne_zero i)
    rw [nonvanishingLocus_sectionsOfTop_eq] at hx
    exact fun h => (h ▸ hx : x ∈ (⊥ : X.Opens))

end Projection

section Classes

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-- `B = a₀ H₁ - Δ' + H_{s - a₀}` in `Pic(C × C)`. -/
private theorem vojtaClass_eq_add (X : CurveWithDegreeOneDivisor k)
    (a s : ℤ) :
    X.vojtaClass s s (-1) =
      (-X.vojtaClass 0 0 1 + a • X.vojtaClass 1 1 0) + X.vojtaClass (s - a) (s - a) 0 := by
  have key : ∀ x y z : Stacks.Picard.ofScheme (pullback X.f X.f),
      s • x + s • y + (-1 : ℤ) • z =
        (-((0 : ℤ) • x + (0 : ℤ) • y + (1 : ℤ) • z) +
          a • ((1 : ℤ) • x + (1 : ℤ) • y + (0 : ℤ) • z)) +
          ((s - a) • x + (s - a) • y + (0 : ℤ) • z) :=
    fun x y z => by module
  exact key _ _ _

/-- **`B` is very ample for `s ≫ 0`.** There is `a₀` such that every invertible module on
`C ×_k C` of class `B = vojtaClass s s (-1)`, `s ≥ a₀ + 2g + 1`, is very ample over `k`: it is
`(𝒪(-Δ') ⊗ H₁^{⊗ a₀}) ⊗ H_{s - a₀}`, a globally generated invertible module twisted by a very
ample one. -/
private theorem exists_isRelativelyVeryAmple_of_picardClass_eq_vojtaClass
    (X : CurveWithDegreeOneDivisor k) :
    ∃ a₀ : ℤ, ∀ s : ℤ, a₀ + 2 * (genus X.f : ℤ) + 1 ≤ s →
      ∀ (L : (pullback X.f X.f).Modules) [hLinv : Stacks.Ample.IsInvertibleModule _ L],
        Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
            (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
          X.vojtaClass s s (-1) →
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (pullback.fst X.f X.f ≫ X.f) L := by
  set Y := pullback X.f X.f
  obtain ⟨L₁, hL₁, hL₁a, hL₁c⟩ :=
    CurveWithDegreeOneDivisor.exists_isAmple_picardClass_eq_vojtaClass_one_one_zero X
  have : Stacks.Ample.IsInvertibleModule Y L₁ := hL₁
  obtain ⟨D, hDs, hDc⟩ := Stacks.SheafOfModules.exists_picardClass_eq Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (-X.vojtaClass 0 0 1)
  have : Stacks.Ample.IsInvertibleModule Y D :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ D).mp hDs
  -- [Stacks, Tag 01QA]: `𝒪(-Δ') ⊗ H₁^{⊗ a}` is globally generated for `a ≥ a₀`
  obtain ⟨a₀, ha₀⟩ :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      L₁ ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hL₁a)).2 D
      (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule D)
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule D)
  refine ⟨a₀, fun s hs L hLinv hL => ?_⟩
  set G := D ⊗ Stacks.Ample.tensorPowModule Y L₁ a₀
  have hG := ha₀ a₀ le_rfl
  have : Stacks.Ample.IsInvertibleModule Y G :=
    Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ _
  obtain ⟨V, hVs, hVc⟩ := Stacks.SheafOfModules.exists_picardClass_eq Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (X.vojtaClass (s - a₀) (s - a₀) 0)
  have : Stacks.Ample.IsInvertibleModule Y V :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ V).mp hVs
  have hVva := CurveWithDegreeOneDivisor.isRelativelyVeryAmple_of_picardClass_eq_vojtaClass X
    (s - a₀) (by omega) V hVc
  have hGV := isRelativelyVeryAmple_tensorModules_of_isGeneratedByGlobalSections k
    (pullback.fst X.f X.f ≫ X.f) G V hG hVva
  have hTs : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
      (Stacks.Ample.tensorPowModule Y L₁ a₀) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      _ _ _).mpr inferInstance
  have hGs := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ G).mpr inferInstance
  have hGc : Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) G hGs =
        -X.vojtaClass 0 0 1 + a₀ • X.vojtaClass 1 1 0 := by
    rw [picardClass_tensorObj Y D _ hDs hTs hGs, hDc, picardClass_tensorPowModule, hL₁c]
  have hTMs := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ Y.presheaf
    (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) _ _ G V hGs hVs
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ L _ _ hTMs).1 (hL.trans (by
    rw [vojtaClass_eq_add X a₀ s, ← hGc, ← hVc,
      Stacks.SheafOfModules.picardClass_tensorSheaf _ _ G V hGs hVs hTMs]
    rfl))
  exact Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple.of_iso e.symm hGV

end Classes

/-- **The embedding `φ_B`.** Let `X = (C, P)` be a curve over `k` with a divisor of degree one.
There is `s₀` such that for every `s ≥ s₀` and every invertible module `L` on `C ×_k C` of class
`vojtaClass X s s (-1)`, the class of `B = s (P × C) + s (C × P) - Δ'`: `L` is very ample over
`k`, `Γ(C ×_k C, L)` is a nonzero finite-dimensional `k`-vector space, and every `k`-basis
`y₀, …, yₘ` of it generates `L`, defines a closed immersion `φ_B : C ×_k C ⟶ ℙᵐ_k` over `k`
with an isomorphism `φ_B^* 𝒪(1) ≅ L` sending the `i`-th homogeneous coordinate to `yᵢ`, and has
no member vanishing identically. -/
@[faltings "lem_nt_b_very_ample"]
theorem CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver_vojtaClass
    (X : CurveWithDegreeOneDivisor k) :
    ∃ s₀ : ℤ, ∀ s : ℤ, s₀ ≤ s →
      ∀ (L : (pullback X.f X.f).Modules) [hLinv : Stacks.Ample.IsInvertibleModule _ L],
        Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
            (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
          X.vojtaClass s s (-1) →
        letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (pullback.fst X.f X.f ≫ X.f) L ∧
        0 < Module.finrank k Γ(L, ⊤) ∧
        ∀ {m : ℕ} (y : Module.Basis (Fin (m + 1)) k Γ(L, ⊤)),
          ∃ hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y,
            IsClosedImmersion
                (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
                  (pullback.fst X.f X.f ≫ X.f)) ∧
            (∃ α : (Scheme.Modules.pullback
                (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
                    (pullback.fst X.f X.f ≫ X.f) ≫
                  projectiveSpaceOver.toIntegralAtUniverse m _)).obj
                    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ⟶ L,
              IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
                (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
                    (pullback.fst X.f X.f ≫ X.f) ≫
                  projectiveSpaceOver.toIntegralAtUniverse m _) i) = y i) ∧
            ∀ i, Stacks.NonvanishingOpen.nonvanishingOpen _ L (y i) ≠ ⊥ := by
  obtain ⟨a₀, ha₀⟩ := exists_isRelativelyVeryAmple_of_picardClass_eq_vojtaClass X
  refine ⟨a₀ + 2 * (genus X.f : ℤ) + 1, fun s hs L hLinv hL => ?_⟩
  have hva := ha₀ s hs L hL
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : IsIntegral (pullback X.f X.f) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst X.f X.f)
  exact ⟨hva, embedding_of_isRelativelyVeryAmple _ L hva⟩

end Faltings
