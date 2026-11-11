module
public import Mordell.BombieriVojta.Representative.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import Mordell.BombieriVojta.SmallSection.U2Sections

/-!
# Sections of `𝒪(V)` have representatives

In Section 6 of Bombieri's proof of the Mordell conjecture, `C` is a smooth projective
geometrically integral curve of genus `g ≥ 2` over a number field `k`, with a divisor `P` of
degree one. The embeddings are `φ_{NP} : C → ℙⁿ` (with `N ≥ 2g + 1`, `n = N - g`) and
`φ_B : C × C → ℙᵐ`, and `ψ = φ_{NP} × φ_{NP}`. The integers `s ≥ 1`, `d ≥ 1`, `d₁`, `d₂` are such
that `δᵢ = (dᵢ + s d) / N` are positive integers, and
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. Let `L = k` or `L = k̄`. If every global section of
`ψ^*𝒪(δ₁, δ₂)` defined over `L` is the restriction of a bihomogeneous form of bidegree
`(δ₁, δ₂)` with coefficients in `L`, then every global section `s` of `𝒪(V)` defined over `L` has
a representative `F = (F_i)` with coefficients in `L`: one takes for `F_i` a form restricting to
`s · y_i^d`.

## Main results

* `Faltings.exists_isVojtaRepresentative`: under the surjectivity hypothesis, every global
  section of `Faltings.vojtaLineBundle ψ φ δ₁ δ₂ d` on `(C × C)_L` has a representative in the
  sense of `Faltings.IsVojtaRepresentative`.

## Implementation notes

* Sections and forms "defined over `L`" are those on the base change `X = (C ×_k C)_L`, an
  abstract pullback square `IsPullback ι π (pullback.fst f f ≫ f) (Spec (L/k))`, with base
  `S = Spec L`; the coefficients `Γ(Spec L, 𝒪)` are `L`. The case `L = k` is the case where
  `algebraMap k L` is bijective, and `L = k̄` is `IsAlgClosure k L`.
* `ψ : X ⟶ ℙⁿ_L ×_L ℙⁿ_L` and `φ : X ⟶ ℙᵐ_L` are the base changes of `φ_{NP} × φ_{NP}` and of
  `φ_B`. They are fixed by their components: over `Spec L` they lie over `π`, and on the
  integral models of projective space they are `ι ≫ prᵢ ≫ φ_{NP}` and `ι ≫ φ_B`.
* The restriction of a form `P = ∑_α c_α x^{α₁} x'^{α₂}` of bidegree `(δ₁, δ₂)` is
  `∑_α c_α · ψ^*(pr₁^* x^{α₁} ⊗ pr₂^* x'^{α₂})`, that is `Faltings.vojtaFormRestriction`. It
  is written out exactly as in `Faltings.isVojtaRepresentative_iff`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

/-- In a monoidal category, if `o : 𝟙 ⟶ Z` is an isomorphism then every morphism
`𝟙 ⟶ L ⊗ Z` is the product of a morphism `𝟙 ⟶ L` with `o`. -/
private theorem exists_unitors_inv_comp_tensorHom_eq {C : Type*} [Category C]
    [MonoidalCategory C] {L Z : C} (o : 𝟙_ C ⟶ Z) [IsIso o] (u : 𝟙_ C ⟶ L ⊗ Z) :
    ∃ t : 𝟙_ C ⟶ L, (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ o) = u := by
  refine ⟨u ≫ L ◁ inv o ≫ (ρ_ L).hom, ?_⟩
  rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, ← Category.assoc,
    ← rightUnitor_inv_naturality]
  simp [← whiskerLeft_comp]

/-- Let `C` be a smooth projective geometrically integral curve of genus `≥ 2` over a number field
`k`, with a divisor `P` of degree one. Let `φNP : C ⟶ ℙⁿ_k` (`N ≥ 2g + 1`, `n = N - g`) and
`φB : C ×_k C ⟶ ℙᵐ_k` be closed immersions over `k`. Let `s ≥ 1` and `d ≥ 1` be integers, and
`d₁, d₂` integers with `dᵢ + s d = N δᵢ` for positive integers `δᵢ`. Let `L` be `k` or an
algebraic closure of `k`, and let `X = (C ×_k C)_L`, with `ψ : X ⟶ ℙⁿ_L ×_L ℙⁿ_L` and
`φ : X ⟶ ℙᵐ_L` the base changes of `φNP × φNP` and `φB`. If every global section of
`ψ^*𝒪(δ₁, δ₂)` is the restriction of a form of bidegree `(δ₁, δ₂)` with coefficients in `L`,
then every global section of `vojtaLineBundle ψ φ δ₁ δ₂ d` has a representative with coefficients
in `L`. -/
@[faltings "lem_bv_section_forms"]
public theorem exists_isVojtaRepresentative (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (hg : 2 ≤ genus f)
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1)
    (sB : ℕ) (hsB : 1 ≤ sB) (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n m : ℕ} (hn : n = N - genus f)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (φB : pullback f f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pullback.fst f f ≫ f)
    [IsClosedImmersion φB]
    (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd : 1 ≤ d) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hδd₁ : d₁ + sB * d = N * δ₁) (hδd₂ : d₂ + sB * d = N * δ₂)
    (L : Type u) [Field L] [Algebra k L]
    (hL : Function.Bijective (algebraMap k L) ∨ IsAlgClosure k L)
    {X : Scheme.{u}} (ι : X ⟶ pullback f f) (π : X ⟶ Spec (.of L))
    (hX : IsPullback ι π (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of L)) ↘ Spec (.of L))
      (projectiveSpaceOver n (Spec (.of L)) ↘ Spec (.of L)))
    (hψπ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of L)) ↘ Spec (.of L)) = π)
    (hψ₁ : ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of L)) =
      ι ≫ pullback.fst f f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (hψ₂ : ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of L)) =
      ι ≫ pullback.snd f f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (φ : X ⟶ projectiveSpaceOver m (Spec (.of L)))
    (hφπ : φ ≫ (projectiveSpaceOver m (Spec (.of L)) ↘ Spec (.of L)) = π)
    (hφ : φ ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of L)) =
      ι ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
    (hsurj :
      letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      letI : ∀ r : ℕ,
          GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      let S : Scheme.{u} := Spec (.of L)
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
      let Lψ : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
      let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
        fun {Y} {_ _} a b => Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _
          ((λ_ (𝟙_ Y.Modules)).inv ≫
            ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm a ⊗ₘ
              (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm b))
      let σ : X ⟶ S := ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)
      let mono : ((Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) → Γ(Lψ, ⊤) := fun α =>
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
      let restrict : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤) → Γ(Lψ, ⊤) := fun Q =>
        ∑ α ∈ Q.support, σ.appTop (Q.coeff α) • mono α
      ∀ t : Γ(Lψ, ⊤), ∃ Q : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤),
        Q.IsWeightedHomogeneous
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂) ∧
        restrict Q = t)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) :
    ∃ F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of L), ⊤),
      IsVojtaRepresentative ψ φ δ₁ δ₂ d s F := by
  classical
  let := Stacks.SheafInternalHom.schemeMonoidalCategory
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let S : Scheme.{u} := Spec (.of L)
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
  let e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
  let O₁ := (Scheme.Modules.pullback p₁).obj (twist n δ₁)
  let O₂ := (Scheme.Modules.pullback p₂).obj (twist n δ₂)
  let Lψ : X.Modules := (Scheme.Modules.pullback ψ).obj (O₁ ⊗ O₂)
  let M : X.Modules := (Scheme.Modules.pullback φ).obj (twist m (-(d : ℤ)))
  let Nd : X.Modules := (Scheme.Modules.pullback φ).obj (twist m d)
  let Z : X.Modules := (Scheme.Modules.pullback φ).obj (twist m 0)
  let tensorSec : ∀ {Y : Scheme.{u}} {A B : Y.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
    fun {Y} {_ _} a b =>
      let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
      eY _ ((λ_ (𝟙_ Y.Modules)).inv ≫ ((eY _).symm a ⊗ₘ (eY _).symm b))
  let μ : M ⊗ Nd ⟶ Z :=
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ (twist m (-(d : ℤ))) (twist m d)).inv ≫
      (Scheme.Modules.pullback φ).map
        ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (g m) (T m (-(d : ℤ))) (T m d)).inv ≫
          (Scheme.Modules.pullback (g m)).map
            ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (T m (-(d : ℤ))) (T m d)).hom ≫
              Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (-(d : ℤ)) d ≫
              eqToHom (congrArg (T m) (neg_add_cancel (d : ℤ)))))
  let y : Fin (m + 1) → Γ(Nd, ⊤) := fun i =>
    pullbackGlobalSections φ (twist m d)
      (form m d ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)
  let one : Γ(Z, ⊤) := pullbackGlobalSections φ (twist m 0)
    (form m 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩)
  have hone : IsIso ((e Z).symm one) := by
    apply isIso_symm_pullbackGlobalSections
    apply isIso_symm_pullbackGlobalSections
    exact isIso_symm_degreeSection_zero_one _
  have ht : ∀ i, ∃ t : 𝟙_ X.Modules ⟶ Lψ, (λ_ (𝟙_ X.Modules)).inv ≫ (t ⊗ₘ (e Z).symm one) =
      (e _).symm (tensorSec s (y i)) ≫ (α_ Lψ M Nd).hom ≫ (Lψ ◁ μ) := fun i =>
    exists_unitors_inv_comp_tensorHom_eq _ _
  choose t ht using ht
  choose Q hQ₁ hQ₂ using fun i => hsurj (e Lψ (t i))
  refine ⟨Q, (isVojtaRepresentative_iff ψ φ δ₁ δ₂ d s Q).2 ⟨hQ₁, fun i => ?_⟩⟩
  refine Eq.trans ?_ (congrArg (fun z => tensorSec z one) (hQ₂ i)).symm
  rw [← ht i]
  change e _ _ = e _ ((λ_ _).inv ≫ ((e _).symm (e _ (t i)) ⊗ₘ (e _).symm one))
  rw [AddEquiv.symm_apply_apply]

end Faltings
