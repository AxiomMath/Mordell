module

public import Mordell.AlgebraicGeometry.PicardPullback
public import Mordell.BombieriVojta.LineBundle.Basic
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveAmple
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OverBase
public import Mordell.CurveProduct.VeryAmple

/-!
# The class of the line bundle `𝒪(V)`

Let `(C, P)` be a curve over a number field `k` with a divisor `P` of degree one, of genus
`g ≥ 2`, and fix the auxiliary data of Bombieri's Section 3: an integer `s ≥ 1` such that
`B = s (P × C) + s (C × P) - Δ'` is very ample, an invertible sheaf `𝒪(B)` on `C ×_k C` with a
`k`-basis `y₀, …, y_m` of its global sections, defining `φ_B : C ×_k C ⟶ ℙᵐ_k`, an integer
`N ≥ 2g + 1`, an invertible sheaf `𝒪(NP)` on `C` with a `k`-basis `x₀, …, xₙ` of its
global sections, defining an embedding `φ_{NP} : C ⟶ ℙⁿ_k`, and the product
`ψ = φ_{NP} × φ_{NP}`. In the setting of Section 6, `d₁, d₂, d` are integers with `d ≥ 1` such
that `δᵢ = (dᵢ + s d) / N` are positive integers. Then the line bundle
`𝒪(V) = ψ^* 𝒪(δ₁, δ₂) ⊗ φ_B^* 𝒪(d)⁻¹` is isomorphic to `𝒪_{C × C}(V)` for
`V = d₁ (P × C) + d₂ (C × P) + d Δ'`, i.e. to every invertible sheaf on `C ×_k C` whose class is
`Faltings.CurveWithDegreeOneDivisor.vojtaClass X d₁ d₂ d`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.nonempty_vojtaLineBundle_iso`: `𝒪(V) ≅ 𝒪_{C × C}(V)`.

## Implementation notes

The sheaf `𝒪_{C × C}(V)` is determined up to isomorphism by its class `vojtaClass X d₁ d₂ d`
in `Pic(C ×_k C)`, so the statement takes an arbitrary invertible `𝒪_{C × C}`-module `𝓛` of
that class. Likewise `𝒪(NP)` and `𝒪(B)` are arbitrary invertible modules of classes
`N • [𝒪_C(P)]` and `vojtaClass X s s (-1)`. The morphisms `φ_{NP}` and `φ_B` are
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of the bases, which needs the bases to
generate the sheaves stalkwise; that `φ_{NP}` is an embedding is `IsClosedImmersion φ_{NP}`;
`ψ` is `pullback.map φ_{NP} φ_{NP}` over the identity of `Spec k`. The divisibility
`δᵢ = (dᵢ + s d) / N` is written `N δᵢ = dᵢ + s d` in `ℤ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.ExceptionalCurveContraction (cls cls_eq_of_iso nonempty_iso_of_cls_eq
  schemePullbackClass_cls cls_tensorPowModule)
open Stacks.Ample (IsInvertibleModule)

universe u

namespace Faltings

section

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {Y : Scheme.{u}}

/-- The class of a tensor product of invertible modules is the sum of the classes. -/
theorem cls_tensorObj (A B : Y.Modules) [IsInvertibleModule Y A]
    [IsInvertibleModule Y B] : cls (A ⊗ B) = cls A + cls B :=
  picardClass_tensorObj Y A B _ _ _

/-- The additive pullback map on Picard groups is pullback of classes. -/
private theorem schemePullbackClassHom_apply {Z : Scheme.{u}} (b : Y ⟶ Z)
    (x : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClassHom b x = Stacks.Picard.schemePullbackClass b x :=
  rfl

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver) in
/-- `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(-d)` is invertible. -/
theorem isInvertibleModule_vojtaLineBundle {S : Scheme.{u}} {n m : ℕ}
    (ψ : Y ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φB : Y ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) :
    IsInvertibleModule Y (vojtaLineBundle ψ φB δ₁ δ₂ d) := by
  change IsInvertibleModule Y ((Scheme.Modules.pullback ψ).obj
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj (twistOver n S δ₁) ⊗
        (Scheme.Modules.pullback (pullback.snd _ _)).obj (twistOver n S δ₂)) ⊗
    (Scheme.Modules.pullback φB).obj (twistOver m S (-d)))
  infer_instance

/-- `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(-d)` is invertible, in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_vojtaLineBundle {S : Scheme.{u}} {n m : ℕ}
    (ψ : Y ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φB : Y ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (vojtaLineBundle ψ φB δ₁ δ₂ d) :=
  (isInvertibleModule_vojtaLineBundle ψ φB δ₁ δ₂ d :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 _).toAlgebraicGeometry

/-- On `ℙⁿ_S`, the class of `𝒪(a)` is `a` times the class of `𝒪(1)`. -/
theorem cls_twistOver (n : ℕ) (S : Scheme.{u}) (a : ℤ) :
    cls (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n S a) =
      a • cls (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n S 1) := by
  rw [← cls_tensorPowModule]
  exact (cls_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso n S a)).symm

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver) in
/-- The class of `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(-d)` when `ψ` is a product `φ ∘ q₁ × φ ∘ q₂`. -/
theorem cls_vojtaLineBundle {S C : Scheme.{u}} {n m : ℕ}
    (ψ : Y ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φB : Y ⟶ projectiveSpaceOver m S) (φ : C ⟶ projectiveSpaceOver n S) (q₁ q₂ : Y ⟶ C)
    (h₁ : ψ ≫ pullback.fst _ _ = q₁ ≫ φ) (h₂ : ψ ≫ pullback.snd _ _ = q₂ ≫ φ) (δ₁ δ₂ d : ℤ)
    [IsInvertibleModule Y (vojtaLineBundle ψ φB δ₁ δ₂ d)] :
    cls (vojtaLineBundle ψ φB δ₁ δ₂ d) =
      δ₁ • Stacks.Picard.schemePullbackClass q₁ (cls ((Scheme.Modules.pullback φ).obj
          (twistOver n S 1))) +
        δ₂ • Stacks.Picard.schemePullbackClass q₂ (cls ((Scheme.Modules.pullback φ).obj
          (twistOver n S 1))) -
        d • cls ((Scheme.Modules.pullback φB).obj (twistOver m S 1)) := by
  change cls ((Scheme.Modules.pullback ψ).obj
      ((Scheme.Modules.pullback (pullback.fst _ _)).obj (twistOver n S δ₁) ⊗
        (Scheme.Modules.pullback (pullback.snd _ _)).obj (twistOver n S δ₂)) ⊗
    (Scheme.Modules.pullback φB).obj (twistOver m S (-d))) = _
  rw [cls_tensorObj, ← schemePullbackClass_cls, cls_tensorObj, ← schemePullbackClass_cls,
    ← schemePullbackClass_cls, ← schemePullbackClass_cls, cls_twistOver n S δ₁,
    cls_twistOver n S δ₂, cls_twistOver m S (-d), ← schemePullbackClass_cls,
    ← schemePullbackClass_cls]
  simp only [Stacks.Picard.schemePullbackClass_add, schemePullbackClass_zsmul,
    Stacks.Picard.schemePullbackClass_comp, h₁, h₂]
  rw [neg_smul, sub_eq_add_neg]

variable {k : Type u} [Field k]

/-- **The class of `𝒪(V)`.** Let `X = (C, P)` be a curve over a number field `k` with a divisor
of degree one, of genus `g ≥ 2`. Let `s ≥ 1` and let `LB` be an invertible sheaf on `C ×_k C`
of class `vojtaClass X s s (-1)` (the divisor `B`), very ample over `k`, with a generating
`k`-basis `y` of its global sections and morphism `φ_B`. Let `N ≥ 2g + 1` and let `L` be an
invertible sheaf on `C` of class `N • [𝒪_C(P)]`, with a generating `k`-basis `x` of its global
sections such that the morphism `φ_{NP}` it defines is a closed immersion, and let
`ψ = φ_{NP} × φ_{NP}`. Let `d ≥ 1` and let `δ₁, δ₂` be positive integers with
`N δᵢ = dᵢ + s d`. Then `vojtaLineBundle ψ φ_B δ₁ δ₂ d` is isomorphic to every invertible
sheaf `𝓛` on `C ×_k C` of class `vojtaClass X d₁ d₂ d`. -/
@[faltings "lem_bv_line_bundle_vojta_class"]
theorem CurveWithDegreeOneDivisor.nonempty_vojtaLineBundle_iso
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f) (s : ℤ) (hs : 1 ≤ s)
    (N : ℕ)
    (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (LB : (pullback X.f X.f).Modules) [hLBinv : Stacks.Ample.IsInvertibleModule _ LB]
    (hLB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) LB
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ LB hLBinv) =
      X.vojtaClass s s (-1))
    (hB : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (pullback.fst X.f X.f ≫ X.f) LB) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
    ∀ {n m : ℕ} (x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x)
      (y : Module.Basis (Fin (m + 1)) k Γ(LB, ⊤))
      (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y)
      (d₁ d₂ d δ₁ δ₂ : ℤ), 1 ≤ d → 0 < δ₁ → 0 < δ₂ →
      N * δ₁ = d₁ + s * d → N * δ₂ = d₂ + s * d →
      ∀ (𝓛 : (pullback X.f X.f).Modules) [h𝓛inv : Stacks.Ample.IsInvertibleModule _ 𝓛],
        Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
            (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) 𝓛
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ 𝓛 h𝓛inv) =
          X.vojtaClass d₁ d₂ d →
        let p : projectiveSpaceOver n (Spec (.of k)) ⟶ Spec (.of k) :=
          pullback.fst _ _
        let φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f
        IsClosedImmersion φ →
        let ψ : pullback X.f X.f ⟶ pullback p p :=
          pullback.map X.f X.f p p φ φ (𝟙 _) (by simp [φ, p]) (by simp [φ, p])
        let φB := Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
          (pullback.fst X.f X.f ≫ X.f)
        Nonempty (vojtaLineBundle ψ φB δ₁ δ₂ d ≅ 𝓛) := by
  intro n m x hx y hy d₁ d₂ d δ₁ δ₂ hd hδ₁ hδ₂ hδ₁N hδ₂N 𝓛 h𝓛inv h𝓛 p φ hφ ψ φB
  have := isInvertibleModule_vojtaLineBundle ψ φB δ₁ δ₂ d
  apply nonempty_iso_of_cls_eq
  rw [cls_vojtaLineBundle ψ φB φ (pullback.fst X.f X.f) (pullback.snd X.f X.f)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)]
  obtain ⟨α, -⟩ :=
    Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver (⇑x) hx X.f
  obtain ⟨β, -⟩ := Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver (⇑y) hy
    (pullback.fst X.f X.f ≫ X.f)
  rw [cls_eq_of_iso α, cls_eq_of_iso β, show cls L = _ from hL, show cls LB = _ from hLB,
    show cls 𝓛 = _ from h𝓛]
  unfold CurveWithDegreeOneDivisor.vojtaClass
  simp only [schemePullbackClassHom_apply, schemePullbackClass_zsmul]
  rw [smul_smul, smul_smul, mul_comm δ₁, mul_comm δ₂, hδ₁N, hδ₂N]
  module

end

end Faltings
