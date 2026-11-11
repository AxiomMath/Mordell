module

public import Mathlib
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Embedding.NP

/-!
# The product embedding `ψ = φ_{NP} × φ_{NP}`

Let `(C, P)` be a curve over a field `k` with a divisor `P = ∑ nₓ x` of degree one, let `g` be
the genus of `C`, let `N ≥ 2g + 1`, let `L ≅ 𝒪_C(NP)` and let `x₀, …, xₙ` be a `k`-basis of
`H⁰(C, L)`, defining the closed immersion `φ_{NP} : C ⟶ ℙⁿ_k` over `k`. Then the product
`ψ = φ_{NP} × φ_{NP} : C ×_k C ⟶ ℙⁿ_k ×_k ℙⁿ_k` is a closed immersion, and for all integers
`δ₁, δ₂` the pull-back along `ψ` of `𝒪(δ₁, δ₂) = pr₁^* 𝒪(δ₁) ⊗ pr₂^* 𝒪(δ₂)` is
`𝒪(δ₁ (NP) × C + δ₂ C × (NP))`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_map_toProjectiveSpaceOver`: `ψ` is a
  closed immersion and `ψ^* 𝒪(δ₁, δ₂) ≅ 𝒪(δ₁ (NP) × C + δ₂ C × (NP))`.

## Implementation notes

The product `ψ` is `pullback.map` of `φ_{NP} = Stacks.ProjectiveFromSections.toProjectiveSpaceOver`
with itself over the identity of `Spec k`, from `C ×_k C = pullback X.f X.f` to the fibre product
of `ℙⁿ_k` with itself over `Spec k`. Invertible sheaves enter through their classes in the Picard
group, written additively, and two invertible sheaves are isomorphic exactly when their classes
agree. The class of `𝒪(δ₁, δ₂)` is `δ₁ pr₁^*[𝒪(1)] + δ₂ pr₂^*[𝒪(1)]`, with `𝒪(1)` on `ℙⁿ_k` pulled
back from the twisting sheaf `Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse` of the
integral model, and the class of `δ₁ (NP) × C + δ₂ C × (NP)` is
`Faltings.CurveWithDegreeOneDivisor.vojtaClass X (δ₁ N) (δ₂ N) 0`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable {k : Type u} [Field k]

/-- **The product embedding `ψ`.** Let `X = (C, P)` be a curve over `k` with a divisor of
degree one, of genus `g`, let `N ≥ 2g + 1`, let `L` be an invertible `𝒪_C`-module of class
`N • [𝒪_C(P)]`, and let `x₀, …, xₙ` be a `k`-basis of `Γ(C, L)`, generating `L`, with
morphism `φ = toProjectiveSpaceOver x hx X.f : C ⟶ ℙⁿ_k`. Then
`ψ = φ × φ : C ×_k C ⟶ ℙⁿ_k ×_k ℙⁿ_k` is a closed immersion, and for all integers `δ₁, δ₂` the
class of `ψ^* 𝒪(δ₁, δ₂)` is `vojtaClass X (δ₁ N) (δ₂ N) 0`, the class of
`δ₁ (NP) × C + δ₂ C × (NP)`. -/
@[faltings "lem_nt_psi_embedding"]
theorem CurveWithDegreeOneDivisor.isClosedImmersion_map_toProjectiveSpaceOver
    (X : CurveWithDegreeOneDivisor k) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    ∀ {n : ℕ} (x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
    let p : projectiveSpaceOver n (Spec (.of k)) ⟶ Spec (.of k) := pullback.fst _ _
    let φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f
    let ψ : pullback X.f X.f ⟶ pullback p p :=
      pullback.map X.f X.f p p φ φ (𝟙 _) (by simp [φ, p]) (by simp [φ, p])
    let 𝒪₁ : Stacks.Picard.ofScheme (projectiveSpaceAtUniverse.{u} n) :=
      Stacks.SheafOfModules.picardClass (projectiveSpaceAtUniverse.{u} n).presheaf
        (Stacks.RingedSpace.structureIsSheaf (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance)
    IsClosedImmersion ψ ∧ ∀ δ₁ δ₂ : ℤ,
      Stacks.Picard.schemePullbackClassHom ψ
          (δ₁ • Stacks.Picard.schemePullbackClassHom
              (pullback.fst p p ≫ projectiveSpaceOver.toIntegralAtUniverse n _) 𝒪₁ +
            δ₂ • Stacks.Picard.schemePullbackClassHom
              (pullback.snd p p ≫ projectiveSpaceOver.toIntegralAtUniverse n _) 𝒪₁) =
        X.vojtaClass (δ₁ * N) (δ₂ * N) 0 := by
  letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  intro n x hx p φ ψ 𝒪₁
  obtain ⟨-, _, hφ, α, hα, -⟩ :=
    CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver X N hN L hL x
  have hφ' : IsClosedImmersion φ := hφ
  haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  refine ⟨MorphismProperty.pullbackMap (P := @IsClosedImmersion) hφ' hφ'
    (by simp [φ, p]) (by simp [φ, p]), fun δ₁ δ₂ => ?_⟩
  have hc : ∀ {A B D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ D) y,
      Stacks.Picard.schemePullbackClassHom f (Stacks.Picard.schemePullbackClassHom g y) =
        Stacks.Picard.schemePullbackClassHom (f ≫ g) y :=
    fun f g y => Stacks.Picard.schemePullbackClass_comp f g y
  haveI := hα
  let g : X.C ⟶ projectiveSpaceAtUniverse.{u} n :=
    φ ≫ projectiveSpaceOver.toIntegralAtUniverse n _
  -- `φ^* 𝒪(1) ≅ L`, transported from the scheme pull-back to the ringed-space one.
  let α' : (Scheme.Modules.pullback g).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L := asIso α
  let β : (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L :=
    (((Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        g.toLRSHom.toShHom)).app _).symm ≪≫ α'
  have key : Stacks.Picard.schemePullbackClassHom g 𝒪₁ =
      Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) :=
    (Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom _ _).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨β⟩)
  -- Since `ψ ≫ prᵢ = prᵢ ≫ φ`, `ψ^* prᵢ^* [𝒪(1)] = prᵢ^* [L]`.
  have e : ∀ (q : pullback p p ⟶ _) (r : pullback X.f X.f ⟶ X.C), ψ ≫ q = r ≫ φ →
      Stacks.Picard.schemePullbackClassHom ψ (Stacks.Picard.schemePullbackClassHom
        (q ≫ projectiveSpaceOver.toIntegralAtUniverse n _) 𝒪₁) =
      Stacks.Picard.schemePullbackClassHom r
        (Stacks.SheafOfModules.picardClass X.C.presheaf
          (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv)) := by
    intro q r h
    rw [hc, ← Category.assoc, h, Category.assoc, ← hc, key]
  rw [map_add, map_zsmul, map_zsmul, e _ _ (pullback.lift_fst _ _ _),
    e _ _ (pullback.lift_snd _ _ _), hL]
  simp only [CurveWithDegreeOneDivisor.vojtaClass, zero_smul, add_zero, map_zsmul]
  rw [mul_zsmul, mul_zsmul, map_zsmul, map_zsmul, zero_zsmul, add_zero]

end Faltings
