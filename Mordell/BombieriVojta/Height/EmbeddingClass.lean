module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import Mordell.CurveProduct.VojtaClass
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.CompositePullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OverBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveAmple
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.BasicUnconditional
public import Mordell.BombieriVojta.Height.SegreVeroneseClass

/-!
# The class of the combination `ψ_{d₁+sd, d₂+sd} - φ_{NdB}`

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, and fix Bombieri's auxiliary embeddings: an integer `s ≥ 1` such that
`B = s (P × C) + s (C × P) - Δ'` is very ample, the closed immersion `φ_B : C × C ⟶ ℙᵐ_k`
given by a `k`-basis of `H⁰(C × C, 𝒪(B))`, an integer `N ≥ 2g + 1` and the morphism
`φ_{NP} : C ⟶ ℙⁿ_k` given by a `k`-basis of `H⁰(C, 𝒪(NP))`. For integers `d₁, d₂, d` with
`d ≥ 1`, `δ₁ = d₁ + s d ≥ 1` and `δ₂ = d₂ + s d ≥ 1`, let
`ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ (φ_{NP} × φ_{NP})` be the Segre–Veronese embedding and
`φ_{NdB} = v_{Nd} ∘ φ_B` the Veronese embedding of degree `N d`. Then, in `Pic(C × C)`,
`cl(ψ_{δ₁,δ₂}) - cl(φ_{NdB}) = N cl(V)`, where `cl(φ) = [φ^* 𝒪(1)]` and
`V = d₁ (P × C) + d₂ (C × P) + d Δ'` is the Vojta divisor.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.pullbackClass_segreVeronese_sub_veronese_eq_vojtaClass`:
  `[ψ_{δ₁,δ₂}^* 𝒪(1)] - [φ_{NdB}^* 𝒪(1)] = N • vojtaClass d₁ d₂ d`.

## Implementation notes

Classes of invertible sheaves are taken in `Stacks.Picard.ofScheme`, written additively. The
sheaf `𝒪(1)` on `ℙʳ_k` is pulled back from the twisting sheaf
`Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse r` of the integral model, so that
`cl(φ)` is `Stacks.Picard.schemePullbackClassHom (φ ≫ toIntegralAtUniverse r _) [𝒪(1)]`.
The divisors `NP` and `B` enter through invertible modules `L` on `C` and `M` on `C ×_k C` of
the classes `N • [𝒪_C(P)]` and `vojtaClass s s (-1)`, and `φ_{NP}`, `φ_B` are the morphisms
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` given by `k`-bases of their global
sections. The Segre–Veronese morphism `v_{δ₁,δ₂} : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` is any `k`-morphism
whose value at every pair of field-valued points is `Faltings.segreVeroneseComposite`, which
determines it, as in `Faltings.exists_isClosedImmersion_segreVeronese_comp`; the Veronese
morphism `v_{Nd} : ℙᵐ ⟶ ℙᴿ` of the integral model is pinned by its chart formulas
`y_{σ J} / y_{σ(Nd • eᵢ)} ↦ x^J / xᵢ^{Nd}`, as in
`Faltings.nonempty_pullback_veronese_projectiveSpaceTwistingSheaf_iso`, and `φ_{NdB}` is any
morphism to `ℙᴿ_k` whose composite with the projection to the integral model is
`v_{Nd} ∘ φ_B`. The degrees `δ₁`, `δ₂` and `N d` are natural numbers given with their defining
equations in `ℤ`.

The proof follows the source. Since `v_{δ₁,δ₂}^* 𝒪(1) = 𝒪(δ₁, δ₂)` and `φ_{NP}^* 𝒪(1) ≅ L`,
`cl(ψ) = δ₁ N (P × C) + δ₂ N (C × P)`; since `v_{Nd}^* 𝒪(1) = 𝒪(N d)` and `φ_B^* 𝒪(1) ≅ M`,
`cl(φ_{NdB}) = N d [B]`. The difference is
`N ((δ₁ - s d) (P × C) + (δ₂ - s d) (C × P) + d Δ') = N [V]`, computed directly in
`Pic(C ×_k C)`.

The morphism `v_{δ₁,δ₂}` is only pinned by its values on field-valued points. Since
`ℙⁿ_k ×_k ℙⁿ_k` is smooth over `k`, hence reduced, and `ℙʳ_ℤ` is separated, `v` followed by the
projection to the integral model is determined by its values at the residue fields, where it
agrees with the Segre–Veronese morphism `sv = Faltings.segreVeroneseHom` glued from the product
charts `D₊(x_i) × D₊(y_j)` with coordinates `x^a y^b / x_i^{δ₁} y_j^{δ₂}`. For morphisms
`f₁, f₂ : Y ⟶ ℙⁿ_ℤ` the monomials `x^a y^b` in the pulled-back coordinates are global sections of
`(f₁^* 𝒪(1))^{⊗ δ₁} ⊗ (f₂^* 𝒪(1))^{⊗ δ₂}` generating it, and the twist identification of
[Stacks, Tag 01NE] gives `sv(f₁, f₂)^* 𝒪(1) ≅ (f₁^* 𝒪(1))^{⊗ δ₁} ⊗ (f₂^* 𝒪(1))^{⊗ δ₂}`. Here the
tensor power `A^{⊗ (k + 1)}` is the iterated tensor product `A ⊗ (A ⊗ (⋯ ⊗ A))`, and a monomial
of degree `k + 1` is the product along a word in the variables in which each variable occurs as
often as its exponent.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 619
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

open Faltings.CurveWithDegreeOneDivisor (isInvertibleModule_powMod
  nonempty_pullback_segreVeroneseHom_iso powMod)

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings

variable {n : ℕ}

/-! ### Classes in the Picard group -/

section Picard

open Stacks.AmpleProjectiveImmersion AlgebraicGeometry.ExceptionalCurveContraction

attribute [local instance] isInvertibleModule_powMod

variable {Y : Scheme.{u}}

/-- The class of `M ⊗ N` is `[M] + [N]`. -/
private theorem cls_tensorObj (M N : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule Y N] :
    cls (Scheme.Modules.tensorObj M N) = cls M + cls N :=
  (Y.picardClass_tensorSheaf M N _ _ _).symm

/-- The class of the `(k + 1)`-fold tensor power of `A` is `(k + 1) • [A]`. -/
private theorem cls_powMod (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] :
    ∀ k : ℕ, cls (powMod A k) = (k + 1) • cls A
  | 0 => by rw [zero_add, one_smul]; rfl
  | k + 1 => by
      rw [show cls (powMod A (k + 1)) = cls (Scheme.Modules.tensorObj A (powMod A k)) from rfl,
        cls_tensorObj, cls_powMod A k, add_smul (k + 1) 1, one_smul, add_comm]

/-- **`sv(f₁, f₂)^* 𝒪(1)` has class `δ₁ [f₁^* 𝒪(1)] + δ₂ [f₂^* 𝒪(1)]`**, for `δ₁, δ₂ ≥ 1`. -/
private theorem cls_pullback_segreVeroneseHom {δ₁ δ₂ r : ℕ} (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂) (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n) :
    cls ((Scheme.Modules.pullback (segreVeroneseHom e f₁ f₂)).obj
        (twistingSheafAtUniverse.{u} r)) =
      δ₁ • cls ((Scheme.Modules.pullback f₁).obj (twistingSheafAtUniverse.{u} n)) +
        δ₂ • cls ((Scheme.Modules.pullback f₂).obj (twistingSheafAtUniverse.{u} n)) := by
  obtain ⟨α⟩ := nonempty_pullback_segreVeroneseHom_iso (Nat.sub_add_cancel h₁).symm
    (Nat.sub_add_cancel h₂).symm e f₁ f₂
  rw [cls_eq_of_iso α, cls_tensorObj, cls_powMod, cls_powMod, Nat.sub_add_cancel h₁,
    Nat.sub_add_cancel h₂]

/-- The class of `(b ≫ g)^* 𝒪(1)` is the pull-back along `b` of the class of `g^* 𝒪(1)`. -/
private theorem cls_pullback_comp {X Z : Scheme.{u}} {p : ℕ} (b : X ⟶ Z)
    (g : Z ⟶ projectiveSpaceAtUniverse.{u} p) :
    cls ((Scheme.Modules.pullback (b ≫ g)).obj (twistingSheafAtUniverse.{u} p)) =
      Stacks.Picard.schemePullbackClassHom b
        (cls ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} p))) :=
  (cls_eq_of_iso (B := (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj _))
    ((Scheme.Modules.pullbackComp b g).app _).symm).trans
    (schemePullbackClass_cls b _).symm

end Picard

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule
  MvPolynomial.gradedAlgebra

open MvPolynomial in
/-- **The class of `ψ_{d₁+sd, d₂+sd} - φ_{NdB}`.** Let `X = (C, P)` be a curve of genus
`g ≥ 2` over a number field `k` with a divisor of degree one, `s ≥ 1`, `N ≥ 2g + 1`, `L` an
invertible `𝒪_C`-module of class `N • [𝒪_C(P)]` and `M` an invertible `𝒪_{C × C}`-module of
class `vojtaClass s s (-1)` (that of `B`). Let `φ_{NP} : C ⟶ ℙⁿ_k` and `φ_B : C ×_k C ⟶ ℙᵐ_k`
be the morphisms given by `k`-bases `x` of `Γ(C, L)` and `y` of `Γ(C ×_k C, M)`, with `φ_B` a
closed immersion. Let `d₁, d₂, d` be integers with `d ≥ 1`, `δ₁ = d₁ + s d ≥ 1`,
`δ₂ = d₂ + s d ≥ 1`, let `v : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` be the Segre–Veronese morphism of bidegree
`(δ₁, δ₂)`, `ψ = v ∘ (φ_{NP} × φ_{NP})`, and let `φ_{NdB} : C ×_k C ⟶ ℙᴿ_k` be the Veronese
composite of degree `N d` of `φ_B`. Then
`[ψ^* 𝒪(1)] - [φ_{NdB}^* 𝒪(1)] = N • vojtaClass d₁ d₂ d` in `Pic(C ×_k C)`. -/
@[faltings "lem_bv_class_vojta_embeddings"]
theorem CurveWithDegreeOneDivisor.pullbackClass_segreVeronese_sub_veronese_eq_vojtaClass
    {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f) (s : ℤ) (hs : 1 ≤ s)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (M : (pullback X.f X.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule (pullback X.f X.f) M]
    (hM : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      X.vojtaClass s s (-1))
    (d₁ d₂ d : ℤ) (hd : 1 ≤ d) (δ₁ δ₂ e : ℕ) (hδ₁ : (δ₁ : ℤ) = d₁ + s * d)
    (hδ₂ : (δ₂ : ℤ) = d₂ + s * d) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (he : (e : ℤ) = N * d) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
    ∀ {n m r R : ℕ} (x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x)
      (y : Module.Basis (Fin (m + 1)) k Γ(M, ⊤))
      (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y)
      (_ : IsClosedImmersion
        (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy (pullback.fst X.f X.f ≫ X.f)))
      (ε : Fin (r + 1) ≃
        {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂})
      (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
      (_ : v ≫ (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) =
          pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
      (_ : ∀ (K : Type u) [Field K] [Algebra k K] (c c' : Fin (n + 1) → K) (hc : c ≠ 0)
          (hc' : c' ≠ 0) (hcs : Ideal.span (Set.range c) = ⊤)
          (hcs' : Ideal.span (Set.range c') = ⊤)
          (w : {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂} →
            K) (hw : w ≠ 0) (hws : Ideal.span (Set.range (w ∘ ε)) = ⊤),
          segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id (.mk K c hc, .mk K c' hc') = .mk K w hw →
            pullback.lift
                (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
                  (projectiveSpacePoint (R := .of K) c hcs) (terminal.hom_ext _ _))
                (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
                  (projectiveSpacePoint (R := .of K) c' hcs') (terminal.hom_ext _ _))
                ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm) ≫ v ≫
                  projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
              projectiveSpacePoint (R := .of K) (w ∘ ε) hws)
      (σ : {I : Fin (m + 1) →₀ ℕ // I.degree = e} ≃ Fin (R + 1))
      (V : projectiveSpaceAtUniverse.{u} m ⟶ projectiveSpaceAtUniverse.{u} R)
      (_ : ∀ i : Fin (m + 1),
        ∃ g : Spec (.of (HomogeneousLocalization.Away
              (homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))) ⟶
            Spec (.of (HomogeneousLocalization.Away
              (homogeneousSubmodule (Fin (R + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)))),
          g ≫ Proj.awayι (homogeneousSubmodule (Fin (R + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
              ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) one_pos =
            Proj.awayι (homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)
              ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) one_pos ≫ V ∧
          ∀ J : {I : Fin (m + 1) →₀ ℕ // I.degree = e},
            g.appTop ((Scheme.ΓSpecIso _).inv
                (HomogeneousLocalization.Away.mk _
                  ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) 1
                  (MvPolynomial.X (σ J))
                  ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))) =
              (Scheme.ΓSpecIso _).inv
                (HomogeneousLocalization.Away.mk _
                  ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) e
                  (monomial J.1 (1 : ULift.{u} ℤ))
                  ((mem_homogeneousSubmodule _ _).2
                    (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2)))))
      (φNdB : pullback X.f X.f ⟶ projectiveSpaceOver R (Spec (.of k)))
      (_ : φNdB ≫ projectiveSpaceOver.toIntegralAtUniverse R (Spec (.of k)) =
        Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy (pullback.fst X.f X.f ≫ X.f) ≫
          projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) ≫ V),
      let φNP := Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f
      let ψ : pullback X.f X.f ⟶ projectiveSpaceOver r (Spec (.of k)) :=
        pullback.map X.f X.f _ _ φNP φNP (𝟙 _)
          (by
            rw [Category.comp_id]
            exact (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _).symm)
          (by
            rw [Category.comp_id]
            exact (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _).symm) ≫ v
      let 𝒪₁ : ∀ p : ℕ, Stacks.Picard.ofScheme (projectiveSpaceAtUniverse.{u} p) := fun p =>
        Stacks.SheafOfModules.picardClass (projectiveSpaceAtUniverse.{u} p).presheaf
          (Stacks.RingedSpace.structureIsSheaf (projectiveSpaceAtUniverse.{u} p).toRingedSpace)
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} p)
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance)
      Stacks.Picard.schemePullbackClassHom
          (ψ ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k))) (𝒪₁ r) -
        Stacks.Picard.schemePullbackClassHom
          (φNdB ≫ projectiveSpaceOver.toIntegralAtUniverse R (Spec (.of k))) (𝒪₁ R) =
      (N : ℤ) • X.vojtaClass d₁ d₂ d := by
  intro n m r R x hx y hy _ ε v hv_over hv σ V hV φNdB hφNdB φNP ψ 𝒪₁
  have hsv : ψ ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
      segreVeroneseHom ε
        (pullback.fst X.f X.f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _)
        (pullback.snd X.f X.f ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) := by
    rw [Category.assoc, comp_toIntegral_eq_segreVeroneseHom h₁ h₂ ε v hv,
      ← segreVeroneseHom_comp]
    congr 1 <;> simp only [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]
  have he₁ : 1 ≤ e := by
    have : (1 : ℤ) ≤ N := by exact_mod_cast (Nat.le_add_left 1 _).trans hN
    exact_mod_cast he ▸ one_le_mul_of_one_le_of_one_le this hd
  obtain ⟨α, -⟩ :=
    Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver (⇑x) hx X.f
  obtain ⟨β⟩ := nonempty_pullback_veronese_projectiveSpaceTwistingSheaf_iso e he₁ R σ V hV _
    φNdB hφNdB
  obtain ⟨γ, -⟩ := Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver
    (⇑y) hy (pullback.fst X.f X.f ≫ X.f)
  open AlgebraicGeometry.ExceptionalCurveContraction Stacks.AmpleProjectiveImmersion in
  · change Stacks.Picard.schemePullbackClass _ (cls (twistingSheafAtUniverse.{u} r)) -
      Stacks.Picard.schemePullbackClass _ (cls (twistingSheafAtUniverse.{u} R)) = _
    rw [schemePullbackClass_cls, schemePullbackClass_cls,
      cls_eq_of_iso ((Scheme.Modules.pullbackCongr hsv).app _),
      cls_pullback_segreVeroneseHom h₁ h₂,
      cls_pullback_comp (pullback.fst X.f X.f), cls_pullback_comp (pullback.snd X.f X.f),
      cls_eq_of_iso (((Scheme.Modules.pullbackComp φNP _).app _).symm ≪≫ α), show cls L = _ from hL,
      cls_eq_of_iso (((Scheme.Modules.pullbackComp φNdB _).app _).symm ≪≫ β),
      cls_tensorPowModule, cls_eq_of_iso γ,
      show cls M = _ from hM]
    simp only [← natCast_zsmul, map_zsmul, CurveWithDegreeOneDivisor.vojtaClass]
    rw [hδ₁, hδ₂, he]
    module

end Faltings
