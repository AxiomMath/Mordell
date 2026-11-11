module
public import Mordell.BombieriVojta.Representative.Basic
import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
import StacksFrontier.AlgebraicGeometry.GradedSectionsModule.IntGraded

/-!
# A section of `𝒪(V)` vanishes if and only if its representative does

In Section 6 of Bombieri's proof of the Mordell conjecture, a global section `s` of
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` on `C × C` has representatives: families `(F_i)_{0 ≤ i ≤ m}`
of bihomogeneous forms of bidegree `(δ₁, δ₂)` with `F_i|_{C × C} = s · y_i^d`. If `s = 0` then
every `F_i|_{C × C}` vanishes. Conversely, on `U_i = {y_i ≠ 0}` the section `y_i^d` of
`φ_B^*𝒪(d)` is a frame, so `F_i|_{C × C} = 0` forces `s|_{U_i} = 0`. The `U_i` cover `C × C`,
because the coordinates `y_i` have no common zero, so `s = 0`.

## Main results

* `Faltings.IsVojtaRepresentative.eq_zero_iff`: if `F` is a representative of `s`, then `s = 0`
  if and only if the restriction to `X` of every form `F i` is zero;
  `Faltings.IsVojtaRepresentative.eq_zero_iff_vojtaFormRestriction` is the same statement with the
  restriction written as `Faltings.vojtaFormRestriction`.
* `Faltings.exists_mem_nonvanishingLocus_vojtaCoordinatePow`: the nonvanishing loci of the
  sections `y_i ^ a` cover `X`.

## Implementation notes

* As for `Faltings.vojtaLineBundle` and `Faltings.IsVojtaRepresentative`, `C × C` is an
  arbitrary scheme `X` over an arbitrary base `S`, with morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and
  `φ : X ⟶ ℙᵐ_S`. The argument only uses that the open sets `φ⁻¹ D₊(T_i)` cover `X`, which
  holds for any morphism to `ℙᵐ_S`.
* The restriction `F|_X ∈ H⁰(X, ψ^*𝒪(δ₁, δ₂))` of a form
  `F = ∑_α c_α x^{α₁} x'^{α₂}` is `∑_α c_α · ψ^*(pr₁^* x^{α₁} ⊗ pr₂^* x'^{α₂})`. This is the
  restriction `Faltings.vojtaFormRestriction` used in `Faltings.IsVojtaRepresentative`, written
  out as in `Faltings.isVojtaRepresentative_iff`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

namespace Faltings

universe u

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

/-- Global sections of an invertible module whose nonvanishing loci cover `X` are jointly
epimorphic, read as morphisms out of the monoidal unit. -/
public theorem eq_zero_of_forall_comp_eq_zero {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] {I : Type u} (t : I → Γ(M, ⊤))
    (hcov : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M (t i))
    {W : X.Modules} (g : M ⟶ W)
    (hg : ∀ i, (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X M).symm (t i) ≫ g = 0) :
    g = 0 := by
  classical
  let σ : I → M.sections := fun i => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (t i)
  have hepi : Epi (M.freeHomEquiv.symm σ) := by
    refine (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf M σ).mpr
      fun x => ?_
    obtain ⟨i, hi⟩ := hcov x
    have hval : ∀ j : I, (σ j).eval (op ⊤) = t j := fun j =>
      (Stacks.NonvanishingSpelling.sectionsEquiv X M).apply_symm_apply (t j)
    simp only [hval]
    exact Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus M t hi
  refine (cancel_epi (M.freeHomEquiv.symm σ)).mp <|
    Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _ fun i => ?_
  have e : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm σ = M.unitHomEquiv.symm (σ i) :=
    Cofan.IsColimit.fac _ _ i
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) e)).trans <|
    ((cancel_epi (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)).hom).mp ?_).trans
    ((congrArg (_ ≫ ·) comp_zero).trans comp_zero).symm
  exact ((Category.assoc _ _ _).symm.trans (hg i)).trans comp_zero.symm

/-- Tensoring on the right with an invertible module is faithful. -/
public theorem eq_zero_of_whiskerRight_eq_zero {X : Scheme.{u}} {A K N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X N] (f : A ⟶ K) (hf : f ▷ N = 0) : f = 0 := by
  have : (tensorRight N).Faithful :=
    Stacks.SheafOfModules.Invertible.faithful_tensorRight X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) N
  have : (tensorRight N).Additive := Stacks.SectionRingGeometric.schemeTensorRightAdditive X N
  exact (tensorRight N).map_injective (hf.trans ((tensorRight N).map_zero A K).symm)

/-- The product `a ⊗ b : 𝟙 ⟶ A ⊗ B` of two global sections, read as morphisms out of the
monoidal unit. -/
private noncomputable abbrev sectionTensor {X : Scheme.{u}} {A B : X.Modules} (a : Γ(A, ⊤))
    (b : Γ(B, ⊤)) : 𝟙_ X.Modules ⟶ A ⊗ B :=
  (λ_ (𝟙_ X.Modules)).inv ≫
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X A).symm a ⊗ₘ
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X B).symm b)

private theorem sectionTensor_zero_left {X : Scheme.{u}} {A B : X.Modules} (b : Γ(B, ⊤)) :
    sectionTensor (0 : Γ(A, ⊤)) b = 0 := by
  have : (tensorRight (𝟙_ X.Modules)).Additive :=
    Stacks.SectionRingGeometric.schemeTensorRightAdditive X _
  have h : (0 : 𝟙_ X.Modules ⟶ A) ▷ (𝟙_ X.Modules) = 0 := (tensorRight _).map_zero _ _
  simp only [sectionTensor, map_zero, MonoidalCategory.tensorHom_def, h, zero_comp, comp_zero]

/-- A global section `s` of `K` vanishes as soon as every product `s ⊗ t i` does, for sections
`t i` of an invertible module whose nonvanishing loci cover `X`. -/
private theorem eq_zero_of_forall_sectionTensor_eq_zero {X : Scheme.{u}} {K N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X N] {I : Type u} (t : I → Γ(N, ⊤))
    (hcov : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus N (t i)) (s : Γ(K, ⊤))
    (h : ∀ i, sectionTensor s (t i) = 0) : s = 0 := by
  set e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  have hs : (e K).symm s ▷ N = 0 := by
    have hg := eq_zero_of_forall_comp_eq_zero N t hcov ((λ_ N).inv ≫ ((e K).symm s ▷ N))
      (fun i => by
        rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc,
          ← MonoidalCategory.tensorHom_def']
        exact h i)
    simpa using hg
  simpa using congrArg (e K) (eq_zero_of_whiskerRight_eq_zero _ hs)

/-- The abstract form of the statement: if `μ : M ⊗ N ≅ Z` and `s ⊗ y i ↦ r i ⊗ 1` under
`L ⊗ M ⊗ N ⟶ L ⊗ Z`, where the `y i` and `1` are sections of invertible modules whose
nonvanishing loci cover `X`, then `s = 0` if and only if every `r i` vanishes. -/
private theorem eq_zero_iff_of_sectionTensor {X : Scheme.{u}} {ι : Type}
    {L M N Z : X.Modules} [Stacks.Ample.IsInvertibleModule X N]
    [Stacks.Ample.IsInvertibleModule X Z] (μ : M ⊗ N ⟶ Z) [IsIso μ]
    (y : ι → Γ(N, ⊤)) (hy : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus N (y i))
    (one : Γ(Z, ⊤)) (hone : ∀ x : X, x ∈ Stacks.Ample.nonvanishingLocus Z one)
    (s : Γ(L ⊗ M, ⊤)) (r : ι → Γ(L, ⊤))
    (h : ∀ i, Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ (sectionTensor s (y i))) ≫
        (α_ L M N).hom ≫ (L ◁ μ)) =
      Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ (sectionTensor (r i) one)) :
    s = 0 ↔ ∀ i, r i = 0 := by
  have h' : ∀ i, sectionTensor s (y i) ≫ ((α_ L M N).hom ≫ (L ◁ μ)) =
      sectionTensor (r i) one := fun i =>
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).injective (by simpa using h i)
  constructor
  · rintro rfl i
    have h0 : sectionTensor (r i) one = 0 := by
      rw [← h' i, sectionTensor_zero_left, zero_comp]
    exact eq_zero_of_forall_sectionTensor_eq_zero (fun _ : PUnit.{u + 1} => one)
      (fun x => ⟨PUnit.unit, hone x⟩) (r i) (fun _ => h0)
  · intro hr
    refine eq_zero_of_forall_sectionTensor_eq_zero (fun j : ULift.{u} ι => y j.down)
      (fun x => (hy x).elim fun i hi => ⟨⟨i⟩, hi⟩) s fun j => ?_
    have h1 := h' j.down
    rw [hr, sectionTensor_zero_left] at h1
    exact (cancel_mono _).mp (h1.trans zero_comp.symm)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On `ℙʳ_ℤ`, the nonvanishing locus of the section of `𝒪(k)` given by a form `f` of degree `k`
is the standard open `D₊(f)`, in every degree `k`. -/
public theorem nonvanishingLocus_degreeSection (r k : ℕ)
    (f : MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) k) :
    Stacks.Ample.nonvanishingLocus
        (X := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)))
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (k : ℤ))
        (ProjectiveSpectrum.Proj.degreeSection
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) k f) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (f : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)) : Set _) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n * 1 := ⟨k, (mul_one k).symm⟩
  exact
    Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.nonvanishingLocus_degreeSection_eq_basicOpen
      _ (Stacks.AlgebraicGeometry.ProjTwistTensorPow.adjoin_degreeOne_integralModel r) one_pos n f

/-- The pullback to `X` of the section of `𝒪(a)` given by a form `f` of degree `a` does not
vanish at the points mapping into `D₊(f)`. -/
public theorem mem_nonvanishingLocus_pullback_degreeSection {S X : Scheme.{u}} {r : ℕ}
    (φ : X ⟶ projectiveSpaceOver r S) (a : ℕ)
    (f : MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a) (x : X)
    (hx : (φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S).base x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (f : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ))) :
    x ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback φ).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse r S)).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (a : ℤ))))
      (pullbackGlobalSections φ _
        (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse r S) _
          (ProjectiveSpectrum.Proj.degreeSection
            (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a f))) := by
  rw [← Stacks.NonvanishingOpen.mem_nonvanishingOpen,
    Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections,
    Scheme.Hom.mem_preimage]
  refine (congrArg (φ.base x ∈ ·)
    (Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections
      _ _ _)).mpr ?_
  exact (Set.ext_iff.mp (nonvanishingLocus_degreeSection r a f) _).mpr hx

/-- `D₊(T_i) ⊆ D₊(T_i ^ a)`. -/
public theorem mem_basicOpen_X_pow {r : ℕ} (a : ℕ) (i : Fin (r + 1))
    (p : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)))
    (hp : p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)) :
    p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i ^ a) := by
  rw [Proj.mem_basicOpen] at hp ⊢
  exact fun hmem => hp (p.isPrime.mem_of_pow_mem a hmem)

/-- Every point lies in `D₊(1)`. -/
public theorem mem_basicOpen_one {r : ℕ}
    (p : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))) :
    p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) 1 := by
  rw [Proj.mem_basicOpen]
  exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/-- The sections `y_i ^ a` pulled back to `X` (`Faltings.vojtaCoordinatePow`) have nonvanishing
loci covering `X`. -/
public theorem exists_mem_nonvanishingLocus_vojtaCoordinatePow {S X : Scheme.{u}} {r : ℕ}
    (φ : X ⟶ projectiveSpaceOver r S) (a : ℕ) (x : X) :
    ∃ i : Fin (r + 1), x ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback φ).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse r S)).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (a : ℤ))))
      (vojtaCoordinatePow φ a i) := by
  obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X
    ((φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S).base x)
  exact ⟨i, mem_nonvanishingLocus_pullback_degreeSection φ a _ x (mem_basicOpen_X_pow a i _ hi)⟩

/-- If the family of forms `F` is a representative of the global section `s` of
`Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d` (`Faltings.IsVojtaRepresentative`), then `s = 0` if and
only if each form `F i` restricts to zero on `X`, as a global section of
`ψ^*(pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂))`. -/
@[faltings "lem_bv_section_zero_iff"]
public theorem IsVojtaRepresentative.eq_zero_iff {S X : Scheme.{u}} {n m : ℕ}
    {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ}
    {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) :
    s = 0 ↔
      letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      letI : ∀ r : ℕ,
          GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let g : ∀ r : ℕ, projectiveSpaceOver r S ⟶ projectiveSpaceAtUniverse.{u} r := fun r =>
        projectiveSpaceOver.toIntegralAtUniverse r S
      let T : ∀ r : ℕ, ℤ → (projectiveSpaceAtUniverse.{u} r).Modules := fun r a =>
        ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a
      let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
        (Scheme.Modules.pullback (g r)).obj (T r a)
      let form : ∀ (r a : ℕ),
          MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a →
            Γ(twist r a, ⊤) := fun r a p =>
        pullbackGlobalSections (g r) (T r a)
          (ProjectiveSpectrum.Proj.degreeSection
            (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a p)
      let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
      let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
      let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
      let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
      let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
      let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules},
          Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
        fun {Y} {_ _} a b =>
          let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
          eY _ ((λ_ (𝟙_ Y.Modules)).inv ≫ ((eY _).symm a ⊗ₘ (eY _).symm b))
      let σ : X ⟶ S := ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)
      let mono : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(L, ⊤) := fun α =>
        if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
            (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
          pullbackGlobalSections ψ (O₁ ⊗ O₂) (tensorSec
            (pullbackGlobalSections p₁ (twist n δ₁)
              (form n δ₁ ⟨MvPolynomial.monomial
                (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
                MvPolynomial.isHomogeneous_monomial _ h.1⟩))
            (pullbackGlobalSections p₂ (twist n δ₂)
              (form n δ₂ ⟨MvPolynomial.monomial
                (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
                MvPolynomial.isHomogeneous_monomial _ h.2⟩)))
        else 0
      let restrict : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤) → Γ(L, ⊤) := fun P =>
        ∑ α ∈ P.support, σ.appTop (P.coeff α) • mono α
      ∀ i, restrict (F i) = 0 := by
  obtain ⟨-, hF2⟩ := (isVojtaRepresentative_iff ψ φ δ₁ δ₂ d s F).1 hF
  let g : ∀ r : ℕ, projectiveSpaceOver r S ⟶ projectiveSpaceAtUniverse.{u} r := fun r =>
    projectiveSpaceOver.toIntegralAtUniverse r S
  let T : ∀ r : ℕ, ℤ → (projectiveSpaceAtUniverse.{u} r).Modules := fun r a =>
    ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a
  let twist : ∀ r : ℕ, ℤ → (projectiveSpaceOver r S).Modules := fun r a =>
    (Scheme.Modules.pullback (g r)).obj (T r a)
  let form : ∀ (r a : ℕ), MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a →
      Γ(twist r a, ⊤) := fun r a p =>
    pullbackGlobalSections (g r) (T r a)
      (ProjectiveSpectrum.Proj.degreeSection
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a p)
  let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
  let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
  let L : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
  let M : X.Modules := (Scheme.Modules.pullback φ).obj (twist m (-(d : ℤ)))
  let N : X.Modules := (Scheme.Modules.pullback φ).obj (twist m d)
  let Z : X.Modules := (Scheme.Modules.pullback φ).obj (twist m 0)
  let μ : M ⊗ N ⟶ Z :=
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ (twist m (-(d : ℤ))) (twist m d)).inv ≫
      (Scheme.Modules.pullback φ).map
        ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (g m) (T m (-(d : ℤ))) (T m d)).inv ≫
          (Scheme.Modules.pullback (g m)).map
            ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (T m (-(d : ℤ))) (T m d)).hom ≫
              Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (-(d : ℤ)) d ≫
              eqToHom (congrArg (T m) (neg_add_cancel (d : ℤ)))))
  let y : Fin (m + 1) → Γ(N, ⊤) := fun i =>
    pullbackGlobalSections φ (twist m d)
      (form m d ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)
  let one : Γ(Z, ⊤) := pullbackGlobalSections φ (twist m 0)
    (form m 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩)
  have : Stacks.Ample.IsInvertibleModule X N := by
    dsimp only [N, twist, g, T]
    infer_instance
  have : Stacks.Ample.IsInvertibleModule X Z := by
    dsimp only [Z, twist, g, T]
    infer_instance
  have : IsIso μ := by
    refine IsIso.comp_isIso' (Iso.isIso_inv _) (@Functor.map_isIso _ _ _ _ _ _ _ _ ?_)
    refine IsIso.comp_isIso' (Iso.isIso_inv _) (@Functor.map_isIso _ _ _ _ _ _ _ _ ?_)
    refine IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' ?_
      (Iso.isIso_hom (eqToIso (congrArg (T m) (neg_add_cancel (d : ℤ))))))
    exact Stacks.AlgebraicGeometry.ProjTwistTensorPow.isIso_twistMultiplicationMap_integralModel
      m _ _
  have hy : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus N (y i) :=
    exists_mem_nonvanishingLocus_vojtaCoordinatePow φ d
  have hone : ∀ x : X, x ∈ Stacks.Ample.nonvanishingLocus Z one := fun x =>
    mem_nonvanishingLocus_pullback_degreeSection φ 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩ x
      (mem_basicOpen_one _)
  exact eq_zero_iff_of_sectionTensor μ y hy one hone s _ hF2

/-- `Faltings.IsVojtaRepresentative.eq_zero_iff` with the restriction of forms written as
`Faltings.vojtaFormRestriction`: if `F` is a representative of `s`, then `s = 0` if and only if
`vojtaFormRestriction ψ δ₁ δ₂ (F i) = 0` for every `i`. -/
public theorem IsVojtaRepresentative.eq_zero_iff_vojtaFormRestriction {S X : Scheme.{u}}
    {n m : ℕ} {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ}
    {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) :
    s = 0 ↔ ∀ i, vojtaFormRestriction ψ δ₁ δ₂ (F i) = 0 := by
  refine hF.eq_zero_iff.trans (forall_congr' fun i => ?_)
  simp only [vojtaFormRestriction, AddMonoidHom.comp_apply, Finsupp.liftAddHom_apply,
    prodSection_eq_leftUnitor_inv_tensorHom]
  rfl

end Faltings
