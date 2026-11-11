module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Projection.Product
import Mordell.BombieriVojta.Norm.SectionRatio
import Mordell.BombieriVojta.Norm.SectionRatioEval
import Mordell.BombieriVojta.Norm.NumeratorDegree
import Mordell.BombieriVojta.Norm.FormNormPolynomial
import Mordell.BombieriVojta.Norm.Relation
import Mordell.BombieriVojta.Representative.Vanishing
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import Mordell.BombieriVojta.Norm.PolynomialTPolynomial

/-!
# The bidegree of the polynomials `T_i`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one, `N ≥ 2g + 1`, `n = N - g`, and `x₀, …, xₙ` a generic `k`-basis of
`L(NP)` giving `φ_{NP} : C → ℙⁿ`, with `ψ = φ_{NP} × φ_{NP}`. Let `φ_B : C × C → ℙᵐ` be given by
a basis `y₀, …, y_m` of `H⁰(C × C, 𝒪(B))`, generic for the projections, `ηᵢ = yᵢ / y₀`, and
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` with `N δᵢ = dᵢ + s d`. Let `σ ≠ 0` be a global section of
`𝒪(V)` with a representative `{F_i}` with coefficients in `k`, `1 ≤ a, b ≤ n`, and `(U_i, V_i)`
reduced representations of the norms `Norm ηᵢ` in `R = k[ξ_a, ξ'_b]`. Then for `1 ≤ i ≤ m` the
element `T_i = G_0 / V_i^d` is a non-zero polynomial of degree at most `N d₁` in `ξ_a` and at most
`N d₂` in `ξ'_b`.

Indeed `T_i ∈ R` and `T_i U_i^d = G_i`; `G_0` is the norm of the non-zero function
`g = F_0(ξ, ξ')`, so `T_i ≠ 0`; and degrees add in the domain `R`, so
`deg_{ξ_a} T_i = deg_{ξ_a} G_i - d deg_{ξ_a} U_i ≤ N² δ₁ - d N s = N d₁`, and likewise in `ξ'_b`.

## Main results

* `Faltings.BombieriRoth.exists_degreeOf_le_algebraMap_eq_polynomialT`: for `i ≠ 0`,
  `Faltings.BombieriRoth.polynomialT` is the image of a non-zero `T ∈ k[X₀, X₁]` with
  `deg_{X₀} T ≤ N d₁` and `deg_{X₁} T ≤ N d₂`.
* `Faltings.BombieriRoth.exists_ne_zero_affineEvaluation_eq_mul_pow`: a representative `{F_i}`
  of a section `s ≠ 0` satisfies `F_i(ξ, ξ') = g · (y_i / y_0)ᵈ` for some `g ≠ 0` in `k(C × C)`.
* `Faltings.BombieriRoth.degreeOf_le_of_mul_pow_eq`: the degree bound for `T` in `T Uᵈ = G`.

## Implementation notes

The setting is that of `Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`:
the curve data of `Faltings.BombieriVojta.productProjectionToProjectiveLine`, `C × C` an abstract
pullback square, `φ_{NP}`, `ψ` and `φ_B` pinned by their coordinates, and the genericity of the
`yᵢ` written through orders of vanishing. The ring `R = k[ξ_a, ξ'_b]` is
`MvPolynomial (Fin 2) k`, its algebra map to the subfield `k⟮ξ_a, ξ'_b⟯` of `k(C × C)` pinned by
`X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

open Faltings.BombieriRoth (exists_germ_app_ratio_eq_div)

open Faltings.BombieriRoth (eval₂_map_eq_affineEvaluation)

namespace Faltings.BombieriRoth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits BombieriSiegel BombieriVojta

universe u

namespace Sections

open MonoidalCategory Opposite
open scoped Stacks.TensorSectionNonvanishing

private theorem tensorSec_eq {Y : Scheme.{u}} (A B : Y.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _ ((λ_ (𝟙_ Y.Modules)).inv ≫
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm a ⊗ₘ
        (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm b)) =
    (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv.val.app (op ⊤)
      (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op ⊤) A B a b) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  let eY := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
  have ha : ((eY A).symm a).val.app (op ⊤)
      ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app
      (op ⊤) (Stacks.SectionRingGeometric.unitOne Y)) = a := by
    have := (eY A).apply_symm_apply a
    rwa [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply] at this
  have hb : ((eY B).symm b).val.app (op ⊤)
      ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app
      (op ⊤) (Stacks.SectionRingGeometric.unitOne Y)) = b := by
    have := (eY B).apply_symm_apply b
    rwa [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply] at this
  rw [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app]
  change ((eY A).symm a ⊗ₘ (eY B).symm b).val.app (op ⊤) ((λ_ (𝟙_ Y.Modules)).inv.val.app (op ⊤)
    ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app (op ⊤)
      (Stacks.SectionRingGeometric.unitOne Y))) = _
  have ht := Stacks.ProjectiveBundleConormal.sheafifyUnitIso_hom_unitIso_inv (X := Y) (V := ⊤)
    (Stacks.SectionRingGeometric.unitOne Y)
  have h1 := Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomLeftUnitor_inv_one
    Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (𝟙_ Y.Modules) (op ⊤)
    _ ht ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app
      (op ⊤) (Stacks.SectionRingGeometric.unitOne Y))
  refine (congrArg _ h1).trans ?_
  have h2 := Stacks.SheafOfModules.tensorSectionsAt_localizedTensorHom
    Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) ((eY A).symm a)
    ((eY B).symm b) (op ⊤) ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app
      (op ⊤) (Stacks.SectionRingGeometric.unitOne Y))
    ((Stacks.SectionRingGeometric.unitComparison Y).inv.val.app
      (op ⊤) (Stacks.SectionRingGeometric.unitOne Y))
  exact h2.trans (congrArg₂ (fun x y => (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv.val.app (op ⊤)
      (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op ⊤) A B x y)) ha hb)

/-- The product of two local sections of `A` and `B` over `V`, as a local section of the monoidal
tensor product `A ⊗ B`. -/
private noncomputable abbrev lmul {Y : Scheme.{u}} (V : Y.Opens) (A B : Y.Modules) (a : Γ(A, V))
    (b : Γ(B, V)) :
    Γ((letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (A ⊗ B : Y.Modules)), V) :=
  (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv.val.app (op V)
    (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op V) A B a b)

private theorem lmul_res {Y : Scheme.{u}} {V W : Y.Opens} (i : W ⟶ V) (A B : Y.Modules)
    (a : Γ(A, V)) (b : Γ(B, V)) :
    (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (A ⊗ B : Y.Modules)).presheaf.map i.op
        (lmul V A B a b) =
      lmul W A B (A.presheaf.map i.op a) (B.presheaf.map i.op b) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  refine (PresheafOfModules.naturality_apply (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv.val i.op _).symm.trans ?_
  exact congrArg _ (PresheafOfModules.naturality_apply
    (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (A.val ⊗ B.val)) i.op
    (a ⊗ₜ b)).symm

private theorem lmul_smul_left {Y : Scheme.{u}} (V : Y.Opens) (A B : Y.Modules) (r : Γ(Y, V))
    (a : Γ(A, V)) (b : Γ(B, V)) :
    lmul V A B (r • a) b = r • lmul V A B a b := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  refine Eq.trans ?_ (((Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      A B).inv.val.app (op V)).hom.map_smul
      r _)
  exact congrArg _ (((Stacks.SheafOfModules.TensorSheafification.toSheafify Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (A.val ⊗ B.val)).app
      (op V)).hom.map_smul r (a ⊗ₜ b))

private theorem lmul_smul_right {Y : Scheme.{u}} (V : Y.Opens) (A B : Y.Modules) (r : Γ(Y, V))
    (a : Γ(A, V)) (b : Γ(B, V)) :
    lmul V A B a (r • b) = r • lmul V A B a b := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  refine Eq.trans ?_ (((Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
      A B).inv.val.app (op V)).hom.map_smul
      r _)
  exact congrArg _ (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_smul_right
    Y.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op V) A B r a b)

/-- The pullback of a local section along `f`, by the unit of the pullback-pushforward
adjunction. -/
private noncomputable abbrev pu {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Modules) (V : Z.Opens) :
    Γ(F, V) ⟶ Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V

private theorem pu_smul {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Z.Modules) (V : Z.Opens)
    (r : Γ(Z, V)) (a : Γ(A, V)) :
    pu f A V (r • a) = f.app V r • pu f A V a :=
  Stacks.RingedSpace.pullbackUnit_smul f.toLRSHom.toShHom A (op V) r a

private theorem pu_res {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Z.Modules) {V W : Z.Opens}
    (i : W ⟶ V) (a : Γ(A, V)) :
    ((Scheme.Modules.pullback f).obj A).presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
        (pu f A V a) =
      pu f A W (A.presheaf.map i.op a) :=
  Stacks.RingedSpace.pullbackUnit_restrict f.toLRSHom.toShHom A i.op a

private theorem pullbackGlobalSections_eq_pu {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Z.Modules)
    (a : Γ(A, ⊤)) : pullbackGlobalSections f A a = pu f A ⊤ a :=
  congrArg (fun φ : Γ(A, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj A, ⊤) => φ a)
    (pullbackGlobalSections_eq_unit f A)

/-- Restriction from the whole space to an open. -/
private noncomputable abbrev resTop {Y : Scheme.{u}} (A : Y.Modules) (V : Y.Opens) :
    Γ(A, ⊤) ⟶ Γ(A, V) :=
  A.presheaf.map (homOfLE le_top).op

private theorem pu_resTop {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Z.Modules) (V : Z.Opens)
    (a : Γ(A, ⊤)) :
    ((Scheme.Modules.pullback f).obj A).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
        (pu f A ⊤ a) = pu f A V (A.presheaf.map (homOfLE le_top).op a) :=
  (congrArg (fun i => ((Scheme.Modules.pullback f).obj A).presheaf.map i (pu f A ⊤ a))
    (congrArg Quiver.Hom.op (Subsingleton.elim _ _))).trans (pu_res f A (homOfLE le_top) a)

private theorem modules_map_map {Y : Scheme.{u}} (A : Y.Modules) {V W W' : Y.Opens}
    (i : op V ⟶ op W) (j : op W ⟶ op W') (k : op V ⟶ op W') (a : Γ(A, V)) :
    A.presheaf.map j (A.presheaf.map i a) = A.presheaf.map k a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun l => A.presheaf.map l a) (Subsingleton.elim _ _)

/-- Restricting the pullback of a pulled-back global section to an open inside the preimage of
an open `V`. -/
private theorem resTop_pu_pu {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (h : Y ⟶ Z) (A : Z.Modules)
    (V : Z.Opens) {U : X.Opens} (hU : U ≤ φ ⁻¹ᵁ h ⁻¹ᵁ V) (a : Γ(A, ⊤)) :
    ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj A)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op
        (pullbackGlobalSections φ _ (pullbackGlobalSections h A a)) =
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj A)).presheaf.map
        (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ V) (pu h A V (A.presheaf.map (homOfLE le_top).op a))) := by
  rw [pullbackGlobalSections_eq_pu, pullbackGlobalSections_eq_pu]
  refine (modules_map_map _ (homOfLE (le_top : φ ⁻¹ᵁ h ⁻¹ᵁ V ≤ ⊤)).op (homOfLE hU).op
    _ _).symm.trans ?_
  refine congrArg _ ((pu_resTop φ _ (h ⁻¹ᵁ V) _).trans ?_)
  exact congrArg _ (pu_resTop h A V a)

/-- Scalars through two pullbacks and a restriction. -/
private theorem res_pu_pu_smul {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (h : Y ⟶ Z) (C : Z.Modules)
    (W : Z.Opens) {U : X.Opens} (hU : U ≤ φ ⁻¹ᵁ h ⁻¹ᵁ W) (r : Γ(Z, W)) (w : Γ(C, W)) :
    ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj C)).presheaf.map
        (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ W) (pu h C W (r • w))) =
      X.presheaf.map (homOfLE hU).op (φ.app (h ⁻¹ᵁ W) (h.app W r)) •
        ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj C)).presheaf.map
          (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ W) (pu h C W w)) := by
  rw [pu_smul, pu_smul, Scheme.Modules.map_smul]

/-- Restricting a pulled-back global section to an open inside the preimage of `V`. -/
private theorem resTop_pullbackGlobalSections {X Y : Scheme.{u}} (φ : X ⟶ Y) (A : Y.Modules)
    (V : Y.Opens) {U : X.Opens} (hU : U ≤ φ ⁻¹ᵁ V) (a : Γ(A, ⊤)) :
    resTop ((Scheme.Modules.pullback φ).obj A) U (pullbackGlobalSections φ A a) =
      ((Scheme.Modules.pullback φ).obj A).presheaf.map (homOfLE hU).op
        (pu φ A V (A.presheaf.map (homOfLE le_top).op a)) := by
  rw [pullbackGlobalSections_eq_pu]
  refine (modules_map_map _ (homOfLE (le_top : φ ⁻¹ᵁ V ≤ ⊤)).op (homOfLE hU).op _ _).symm.trans ?_
  exact congrArg _ (pu_resTop φ A V a)

/-- The product of two global sections, as in the statement: through morphisms out of the
monoidal unit. -/
private noncomputable abbrev tsec {Y : Scheme.{u}} {A B : Y.Modules} (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    Γ((letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (A ⊗ B : Y.Modules)), ⊤) :=
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _ ((λ_ (𝟙_ Y.Modules)).inv ≫
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm a ⊗ₘ
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm b))

/-- The restriction to `U` of `ψ^*(q₁^* h^* t₁ ⊗ q₂^* h^* t₂)`, where `t₁ = r₁ t₁'` and
`t₂ = r₂ t₂'` over `V`. -/
private theorem resTop_pullback_lmul_smul {X P Y Z : Scheme.{u}} (ψ : X ⟶ P) (q₁ q₂ : P ⟶ Y)
    (h : Y ⟶ Z) {A₁ A₂ : Z.Modules} (V : Z.Opens) {U : X.Opens}
    (hU : U ≤ ψ ⁻¹ᵁ (q₁ ⁻¹ᵁ h ⁻¹ᵁ V ⊓ q₂ ⁻¹ᵁ h ⁻¹ᵁ V)) (t₁ t₁' : Γ(A₁, ⊤)) (t₂ t₂' : Γ(A₂, ⊤))
    (r₁ r₂ : Γ(Z, V)) (h₁ : resTop A₁ V t₁ = r₁ • resTop A₁ V t₁')
    (h₂ : resTop A₂ V t₂ = r₂ • resTop A₂ V t₂') :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    resTop ((Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback q₁).obj
        ((Scheme.Modules.pullback h).obj A₁) ⊗ (Scheme.Modules.pullback q₂).obj
          ((Scheme.Modules.pullback h).obj A₂))) U
      (pullbackGlobalSections ψ ((Scheme.Modules.pullback q₁).obj
        ((Scheme.Modules.pullback h).obj A₁) ⊗ (Scheme.Modules.pullback q₂).obj
          ((Scheme.Modules.pullback h).obj A₂)) (tsec
        (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁))
        (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂)))) =
      X.presheaf.map (homOfLE hU).op (ψ.app _
        (P.presheaf.map (homOfLE inf_le_left).op (q₁.app (h ⁻¹ᵁ V) (h.app V r₁)) *
          P.presheaf.map (homOfLE inf_le_right).op (q₂.app (h ⁻¹ᵁ V) (h.app V r₂)))) •
      resTop ((Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback q₁).obj
        ((Scheme.Modules.pullback h).obj A₁) ⊗ (Scheme.Modules.pullback q₂).obj
          ((Scheme.Modules.pullback h).obj A₂))) U
      (pullbackGlobalSections ψ ((Scheme.Modules.pullback q₁).obj
        ((Scheme.Modules.pullback h).obj A₁) ⊗ (Scheme.Modules.pullback q₂).obj
          ((Scheme.Modules.pullback h).obj A₂)) (tsec
        (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁'))
        (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂')))) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  have hW₁ : q₁ ⁻¹ᵁ h ⁻¹ᵁ V ⊓ q₂ ⁻¹ᵁ h ⁻¹ᵁ V ≤ q₁ ⁻¹ᵁ h ⁻¹ᵁ V := inf_le_left
  have hW₂ : q₁ ⁻¹ᵁ h ⁻¹ᵁ V ⊓ q₂ ⁻¹ᵁ h ⁻¹ᵁ V ≤ q₂ ⁻¹ᵁ h ⁻¹ᵁ V := inf_le_right
  have e1 : tsec (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁))
      (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂)) = lmul ⊤ _ _
        (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁))
        (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂)) := tensorSec_eq _ _ _ _
  have e2 : tsec (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁'))
      (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂')) = lmul ⊤ _ _
        (pullbackGlobalSections q₁ _ (pullbackGlobalSections h A₁ t₁'))
        (pullbackGlobalSections q₂ _ (pullbackGlobalSections h A₂ t₂')) := tensorSec_eq _ _ _ _
  rw [e1, e2]
  rw [resTop_pullbackGlobalSections ψ _ _ hU, resTop_pullbackGlobalSections ψ _ _ hU, lmul_res,
    lmul_res, resTop_pu_pu q₁ h A₁ V hW₁, resTop_pu_pu q₁ h A₁ V hW₁, resTop_pu_pu q₂ h A₂ V hW₂,
    resTop_pu_pu q₂ h A₂ V hW₂, h₁, h₂, res_pu_pu_smul, res_pu_pu_smul, lmul_smul_left,
    lmul_smul_right, smul_smul, pu_smul, Scheme.Modules.map_smul]

/-! ### Restrictions of pulled-back functions -/

private theorem presheaf_map_map {X : Scheme.{u}} {V W W' : X.Opens} (i : op V ⟶ op W)
    (j : op W ⟶ op W') (k : op V ⟶ op W') (r : Γ(X, V)) :
    X.presheaf.map j (X.presheaf.map i r) = X.presheaf.map k r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun l => X.presheaf.map l r) (Subsingleton.elim _ _)

/-- A function restricted along `W ≤ V`, pulled back along `ψ` and restricted to `U`, is the
pullback over `V` restricted to `U`. -/
private theorem res_app_res {X P : Scheme.{u}} (ψ : X ⟶ P) {V W : P.Opens} (hW : W ≤ V)
    {U : X.Opens} (hU : U ≤ ψ ⁻¹ᵁ W) (z : Γ(P, V)) :
    X.presheaf.map (homOfLE hU).op (ψ.app W (P.presheaf.map (homOfLE hW).op z)) =
      X.presheaf.map (homOfLE (hU.trans fun _ hx => hW hx)).op (ψ.app V z) := by
  have h := congrArg (fun k => k.hom z) (ψ.naturality (homOfLE hW).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [show (ψ.app W) ((P.presheaf.map (homOfLE hW).op) z) =
    X.presheaf.map ((TopologicalSpace.Opens.map ψ.base).map (homOfLE hW).op.unop).op
      (ψ.app V z) from h]
  exact presheaf_map_map _ _ _ _

/-! ### Computations on the standard chart `D₊(T₀)` of the integral model -/

/-- In the localization away from `x`, `(∏ vᵢ^{αᵢ}) / x^{∑ αᵢ} = ∏ (vᵢ / x)^{αᵢ}`. -/
private theorem mk_prod_pow {A : Type*} [CommRing A] (x : A) {ι : Type*} [Fintype ι] (v : ι → A)
    (α : ι → ℕ) (hx : ∀ n : ℕ, x ^ n ∈ Submonoid.powers x) :
    Localization.mk (∏ i, v i ^ α i) ⟨x ^ (∑ i, α i), hx _⟩ =
      ∏ i, (Localization.mk (v i) ⟨x ^ 1, hx 1⟩ : Localization (Submonoid.powers x)) ^ α i := by
  simp only [Localization.mk_eq_mk']
  have key : ∀ i, IsLocalization.mk' (Localization (Submonoid.powers x)) (v i) ⟨x ^ 1, hx 1⟩ *
      algebraMap A _ x = algebraMap A _ (v i) := by
    intro i
    rw [← pow_one (algebraMap A _ x), ← map_pow]
    exact IsLocalization.mk'_spec _ _ _
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_prod, map_pow, ← Finset.prod_pow_eq_pow_sum, ← key, mul_pow,
    Finset.prod_mul_distrib]

/-- On `D₊(T₀)`, the monomial `T^α` of degree `δ` is `T^α / T₀^δ` times `T₀^δ`. -/
private theorem degreeSection_monomial_eq (r δ : ℕ) (α : Fin (r + 1) →₀ ℕ) (hα : α.degree = δ) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
    let T : ℤ → (projectiveSpaceAtUniverse.{u} r).Modules :=
      fun a => ProjectiveSpectrum.Proj.twistingSheaf 𝒜 a
    let D₀ : (projectiveSpaceAtUniverse.{u} r).Opens :=
      ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X 0)
    let ρ : Γ(projectiveSpaceAtUniverse.{u} r, D₀) := Proj.awayToSection 𝒜 (MvPolynomial.X 0)
      (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) δ
        (MvPolynomial.monomial α 1) (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_monomial _ hα)))
    (T δ).presheaf.map (homOfLE (le_top : D₀ ≤ ⊤)).op
        (ProjectiveSpectrum.Proj.degreeSection 𝒜 δ
          ⟨MvPolynomial.monomial α 1, MvPolynomial.isHomogeneous_monomial _ hα⟩) =
      ρ •
        (T δ).presheaf.map (homOfLE (le_top : D₀ ≤ ⊤)).op
          (ProjectiveSpectrum.Proj.degreeSection 𝒜 δ
            ⟨MvPolynomial.X 0 ^ δ, MvPolynomial.isHomogeneous_X_pow 0 δ⟩) := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  intro 𝒜 T D₀ ρ
  refine Subtype.ext (funext fun x => ?_)
  have : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  have hmem : MvPolynomial.monomial α 1 ∈ 𝒜 (δ • 1) := by
    rw [smul_eq_mul, mul_one]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_monomial _ hα)
  change LocalizedModule.mk (MvPolynomial.monomial α 1) 1 =
    HomogeneousLocalization.val (((Proj.awayToSection 𝒜 (MvPolynomial.X 0))
      (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) δ
        (MvPolynomial.monomial α 1) hmem)).1 x) *
      LocalizedModule.mk (MvPolynomial.X 0 ^ δ) 1
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  erw [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk', ← Localization.mk_eq_mk']
  change Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  rw [Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [OneMemClass.coe_one, RingHom.id_apply, mul_one, one_mul]
  ring

/-- In the homogeneous localization away from `T₀`, `T^α / T₀^{|α|} = ∏_ν (T_ν / T₀)^{α_ν}`. -/
private theorem away_mk_monomial (r δ : ℕ) (α : Fin (r + 1) →₀ ℕ) (hα : α.degree = δ) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
    HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) δ
        (MvPolynomial.monomial α 1) (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_monomial _ hα)) =
      ∏ ν, (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) 1
        (MvPolynomial.X ν) (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_X _ ν))) ^ α ν := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  intro 𝒜
  apply HomogeneousLocalization.val_injective
  refine Eq.trans ?_ (map_prod (algebraMap
    (HomogeneousLocalization 𝒜 (Submonoid.powers (MvPolynomial.X 0)))
    (Localization (Submonoid.powers (MvPolynomial.X 0)))) _ _).symm
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply]
  have h1 : (MvPolynomial.monomial α (1 : ULift.{u} ℤ)) = ∏ i, MvPolynomial.X i ^ α i := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype]
    intro i; simp
  refine Eq.trans ?_ (mk_prod_pow (MvPolynomial.X (R := ULift.{u} ℤ) (0 : Fin (r + 1)))
    MvPolynomial.X α (fun n => ⟨n, rfl⟩))
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  dsimp only
  rw [h1, ← hα, Finsupp.degree_eq_sum]

/-- The pullback of `T^α / T₀^{|α|}` is the product of the pullbacks of the `T_ν / T₀`. -/
private theorem res_app_away_monomial {X : Scheme.{u}} (r δ : ℕ)
    (h : X ⟶ projectiveSpaceAtUniverse.{u} r) (α : Fin (r + 1) →₀ ℕ) (hα : α.degree = δ)
    {U : X.Opens} :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
    let D₀ : (projectiveSpaceAtUniverse.{u} r).Opens :=
      ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X 0)
    let ρα : Γ(projectiveSpaceAtUniverse.{u} r, D₀) := Proj.awayToSection 𝒜 (MvPolynomial.X 0)
      (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) δ
        (MvPolynomial.monomial α 1) (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_monomial _ hα)))
    let ρ : Fin (r + 1) → Γ(projectiveSpaceAtUniverse.{u} r, D₀) := fun ν =>
      Proj.awayToSection 𝒜 (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) 1
          (MvPolynomial.X ν) (by
            rw [smul_eq_mul, mul_one]
            exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
              (MvPolynomial.isHomogeneous_X _ ν)))
    ∀ hU : U ≤ h ⁻¹ᵁ D₀,
    X.presheaf.map (homOfLE hU).op (h.app D₀ ρα) =
      ∏ ν, (X.presheaf.map (homOfLE hU).op (h.app D₀ (ρ ν))) ^ α ν := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  intro 𝒜 D₀ ρα ρ hU
  have hρ : ρα = ∏ ν, ρ ν ^ α ν := by
    change Proj.awayToSection 𝒜 (MvPolynomial.X 0) _ = _
    rw [away_mk_monomial r δ α hα, map_prod]
    simp only [map_pow]
    rfl
  rw [hρ, map_prod, map_prod]
  simp only [map_pow]

end Sections

namespace Vanishing

open Opposite

/-- On an integral scheme, a global section of an invertible module which vanishes on a nonempty
open set is zero. -/
private theorem eq_zero_of_res_eq_zero {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {W : X.Opens} {x : X} (hx : x ∈ W) (t : Γ(L, ⊤))
    (ht : L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t = 0) : t = 0 := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›
  refine Stacks.ChernCap42.eq_zero_of_germ_eq_zero (x := x) L t ?_
  change (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf ⊤ x trivial).hom t = 0
  rw [← TopCat.Presheaf.germ_res_apply L.val.presheaf (homOfLE le_top : W ⟶ ⊤) x hx t]
  change (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf W x hx).hom
    (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) = 0
  rw [ht]
  exact (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf W x hx).hom.map_zero

open MonoidalCategory Sections in
/-- **A section whose representative vanishes at the generic point is zero.** If `F` represents
`s` and every `F_i(ξ, ξ')` vanishes in the function field, then `s = 0`. -/
private theorem eq_zero_of_eval₂_eq_zero {S X : Scheme.{u}} [IsIntegral X] {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) :
    letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    let D : ∀ r : ℕ, (projectiveSpaceOver r S).Opens := fun r =>
      projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)
    let ratio : ∀ r : ℕ, Fin (r + 1) → Γ(projectiveSpaceOver r S, D r) := fun r k =>
      (projectiveSpaceOver.toIntegralAtUniverse r S).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
            (MvPolynomial.X k) (by simpa using MvPolynomial.isHomogeneous_X _ k)))
    let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    ∀ (hx : genericPoint X ∈ (ψ ≫ p₁) ⁻¹ᵁ D n) (hx' : genericPoint X ∈ (ψ ≫ p₂) ⁻¹ᵁ D n),
    let ξ : Fin (n + 1) → X.functionField := fun ν =>
      X.presheaf.germ _ (genericPoint X) hx ((ψ ≫ p₁).app (D n) (ratio n ν))
    let ξ' : Fin (n + 1) → X.functionField := fun ν =>
      X.presheaf.germ _ (genericPoint X) hx' ((ψ ≫ p₂).app (D n) (ratio n ν))
    let c : Γ(S, ⊤) →+* X.functionField :=
      ((ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom
    (∀ i, MvPolynomial.eval₂ c (Sum.elim ξ ξ') (F i) = 0) → s = 0 := by
  intro D ratio p₁ p₂ hx hx' ξ ξ' c h0
  refine (IsVojtaRepresentative.eq_zero_iff hF).2 ?_
  intro g' T' twist' form p₁' p₂' O₁' O₂' L' tensorSec' σ' mono restrict i
  have hhom := hF.1
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let D₀ : ∀ r : ℕ, (projectiveSpaceAtUniverse.{u} r).Opens := fun r =>
    ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)
  let W : X.Opens := (ψ ≫ p₁) ⁻¹ᵁ D n ⊓ (ψ ≫ p₂) ⁻¹ᵁ D n
  have hW₁ : W ≤ (ψ ≫ p₁) ⁻¹ᵁ D n := inf_le_left
  have hW₂ : W ≤ (ψ ≫ p₂) ⁻¹ᵁ D n := inf_le_right
  have hηW : genericPoint X ∈ W := ⟨hx, hx'⟩
  have hW' : W ≤ ψ ⁻¹ᵁ (p₁' ⁻¹ᵁ (g' n) ⁻¹ᵁ D₀ n ⊓ p₂' ⁻¹ᵁ (g' n) ⁻¹ᵁ D₀ n) :=
    fun x hx => ⟨hW₁ hx, hW₂ hx⟩
  -- the section `x₀^{δ₁} x₀'^{δ₂}`, globally and on `W`
  let xpow : Γ(L', ⊤) := pullbackGlobalSections ψ (O₁' ⊗ O₂')
    (tensorSec' (pullbackGlobalSections p₁' (twist' n δ₁)
        (form n δ₁ ⟨MvPolynomial.X 0 ^ δ₁, MvPolynomial.isHomogeneous_X_pow 0 δ₁⟩))
      (pullbackGlobalSections p₂' (twist' n δ₂)
        (form n δ₂ ⟨MvPolynomial.X 0 ^ δ₂, MvPolynomial.isHomogeneous_X_pow 0 δ₂⟩)))
  let xX : Γ(L', W) := resTop L' W xpow
  let ξW : Fin (n + 1) → Γ(X, W) := fun ν =>
    X.presheaf.map (homOfLE hW₁).op ((ψ ≫ p₁).app (D n) (ratio n ν))
  let ξ'W : Fin (n + 1) → Γ(X, W) := fun ν =>
    X.presheaf.map (homOfLE hW₂).op ((ψ ≫ p₂).app (D n) (ratio n ν))
  let cW : Γ(S, ⊤) →+* Γ(X, W) := (X.presheaf.map (homOfLE le_top).op).hom.comp σ'.appTop.hom
  -- the restriction of the form `F i` to `W` is its dehomogenisation times `x₀^{δ₁} x₀'^{δ₂}`
  have hR : resTop L' W (restrict (F i)) =
      MvPolynomial.eval₂ cW (Sum.elim ξW ξ'W) (F i) • xX := by
    have hmono : ∀ α ∈ (F i).support, resTop L' W (mono α) =
        ((∏ ν, ξW ν ^ α (Sum.inl ν)) * ∏ ν, ξ'W ν ^ α (Sum.inr ν)) • xX := by
      intro α hα
      have hw := hhom i (MvPolynomial.mem_support_iff.mp hα)
      have hdeg : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
          (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ := by
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type] at hw
        simp only [Sum.elim_inl, Sum.elim_inr, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
          Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
          Finset.sum_const_zero, add_zero, zero_add] at hw
        simp only [Finsupp.degree_eq_sum, Finsupp.comapDomain_apply]
        exact hw
      have hm : mono α = pullbackGlobalSections ψ (O₁' ⊗ O₂') (tensorSec'
          (pullbackGlobalSections p₁' (twist' n δ₁) (form n δ₁
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.1⟩))
          (pullbackGlobalSections p₂' (twist' n δ₂) (form n δ₂
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.2⟩))) := dite_eq_left hdeg
      rw [hm]
      refine (resTop_pullback_lmul_smul ψ p₁' p₂' (g' n) (D₀ n) hW' _ _ _ _ _ _
        (degreeSection_monomial_eq n δ₁ _ hdeg.1)
        (degreeSection_monomial_eq n δ₂ _ hdeg.2)).trans ?_
      refine congrArg₂ (· • ·) ?_ rfl
      rw [map_mul, map_mul]
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [res_app_res]
        exact res_app_away_monomial n δ₁ (ψ ≫ p₁' ≫ g' n) _ hdeg.1 _
      · rw [res_app_res]
        exact res_app_away_monomial n δ₂ (ψ ≫ p₂' ≫ g' n) _ hdeg.2 _
    have hexp : MvPolynomial.eval₂ cW (Sum.elim ξW ξ'W) (F i) = ∑ α ∈ (F i).support,
        cW ((F i).coeff α) * ((∏ ν, ξW ν ^ α (Sum.inl ν)) * ∏ ν, ξ'W ν ^ α (Sum.inr ν)) := by
      rw [MvPolynomial.eval₂_eq']
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hexp, Finset.sum_smul]
    change resTop L' W (∑ α ∈ (F i).support, σ'.appTop ((F i).coeff α) • mono α) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Scheme.Modules.map_smul, hmono α hα, smul_smul]
    rfl
  -- the dehomogenisation vanishes on `W`, its germ at the generic point being `F_i(ξ, ξ')`
  have hE : MvPolynomial.eval₂ cW (Sum.elim ξW ξ'W) (F i) = 0 := by
    apply germ_injective_of_isIntegral X (genericPoint X) hηW
    rw [map_zero, ← h0 i, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) hηW _
    · funext ν
      rcases ν with ν | ν
      · exact X.presheaf.germ_res_apply (homOfLE hW₁) (genericPoint X) hηW _
      · exact X.presheaf.germ_res_apply (homOfLE hW₂) (genericPoint X) hηW _
  have iTw : ∀ r (a : ℤ), Stacks.Ample.IsInvertibleModule (projectiveSpaceOver r S) (twist' r a) :=
    fun r a => @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ (g' r) (T' r a)
      (Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule
        (ULift.{u} ℤ) r a)
  have iO₁ : Stacks.Ample.IsInvertibleModule _ O₁' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ p₁' _ (iTw n δ₁)
  have iO₂ : Stacks.Ample.IsInvertibleModule _ O₂' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ p₂' _ (iTw n δ₂)
  have iL : Stacks.Ample.IsInvertibleModule X L' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ψ _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ O₁' O₂' iO₁ iO₂)
  refine eq_zero_of_res_eq_zero L' hηW _ ?_
  change resTop L' W (restrict (F i)) = 0
  rw [hR, hE, zero_smul]

end Vanishing

/-- **The representative identity at the generic point, with `g ≠ 0`.** If `{F_i}` represents
`s ≠ 0` in `𝒪(V)`, then there is `g ≠ 0` in `k(X)` with `F_i(ξ, ξ') = g · (y_i / y_0)ᵈ` for every
`i`, where `F_i(ξ, ξ')` is the affine evaluation at `ξ_ν = pr₁^*(x_ν / x_0)`,
`ξ'_ν = pr₂^*(x_ν / x_0)`. -/
public theorem exists_ne_zero_affineEvaluation_eq_mul_pow {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) {n m : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP) (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    [Algebra k C.functionField] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hyspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) = ⊤)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) hyspan
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    (δ₁ δ₂ d : ℕ) (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1)) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ j, affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F j) =
      g * (y j / y 0) ^ d := by
  have hs₁ : Function.Surjective pr₁ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.1
  have hs₂ : Function.Surjective pr₂ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.2
  obtain ⟨hxC, hξC⟩ := exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  obtain ⟨hyX, hηX⟩ := exists_germ_app_ratio_eq_div φB y (hy 0) _ _ hφB
  have hx₁ := (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC 0).1
  have hx₂ := (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC 0).1
  have key := IsVojtaRepresentative.eval₂_eq_vojtaSectionRatio_mul_pow ψ φB δ₁ δ₂ d s hs _ hF
    (hψ₁ ▸ hx₁) (hψ₂ ▸ hx₂) hyX
  refine ⟨vojtaSectionRatio ψ φB δ₁ δ₂ d s,
    fun h => hs (Vanishing.eq_zero_of_eval₂_eq_zero ψ φB δ₁ δ₂ d s _ hF
      (hψ₁ ▸ hx₁) (hψ₂ ▸ hx₂) fun i => by rw [key i, h, zero_mul]), fun j => ?_⟩
  refine (eval₂_map_eq_affineEvaluation ι₁ ι₂ x 0 (hx0 0) (δ₁, δ₂) (F j) _ _ ?_ _ _
    ?_ ?_).symm.trans ((key j).trans ?_)
  · intro c₀
    rw [hkX]
    have e₁ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
        pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [← Category.assoc, hψ₁, Category.assoc]
    have e₂ : C.fromSpecStalk (genericPoint C) ≫
        (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) =
        C.fromSpecStalk (genericPoint C) ≫ f := by
      rw [hφNP]
    have hC := germ_appTop_eq_of_fromSpecStalk_comp_eq (Y := C)
      (g := φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) (g' := f) e₂
      ((Scheme.ΓSpecIso (.of k)).inv c₀)
    obtain ⟨_, h₁⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      ((φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c₀))
    obtain ⟨_, h₂⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c₀))
    rw [hC] at h₁
    have h₃ : (ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop =
        (pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))).appTop := by
      rw [e₁]
    change X.presheaf.germ ⊤ (genericPoint X) trivial ((ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop _) = _
    rw [h₃]
    exact h₁.trans h₂.symm
  · intro ν
    refine (germ_app_congr hψ₁ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC _).snd.trans
      (congrArg ι₁ (hξC ν))
  · intro ν
    refine (germ_app_congr hψ₂ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC _).snd.trans
      (congrArg ι₂ (hξC ν))
  · exact congrArg (fun z => vojtaSectionRatio ψ φB δ₁ δ₂ d s * z ^ d) (hηX j)

/-- **Degrees add.** If `T Uᵈ = G` in a polynomial ring over a domain, with `deg_j G ≤ N² δ`,
`deg_j U = N s` and `N δ = e + s d`, then `deg_j T ≤ N e`. -/
public theorem degreeOf_le_of_mul_pow_eq {σ R : Type*} [CommRing R] [IsDomain R]
    {T U G : MvPolynomial σ R} {d : ℕ} (hT : T ≠ 0) (hU : U ≠ 0) (hTG : T * U ^ d = G) (j : σ)
    {N δ e s : ℕ} (hG : G.degreeOf j ≤ N ^ 2 * δ) (hUj : U.degreeOf j = N * s)
    (hδ : N * δ = e + s * d) : T.degreeOf j ≤ N * e := by
  have h := MvPolynomial.degreeOf_mul_eq hT (pow_ne_zero d hU) (n := j)
  rw [hTG, MvPolynomial.degreeOf_pow_eq _ _ _ hU, hUj] at h
  have : N ^ 2 * δ = N * e + N * s * d := by rw [sq, mul_assoc, hδ]; ring
  nlinarith

open Classical in
/-- **The bidegree of `T_i`** (Bombieri). In the setting of
`Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`, let `s ≠ 0` be a
global section of `𝒪(V) = Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d` with a representative `F` with
coefficients in `k`, where `N δᵢ = dᵢ + sB d`. Let `1 ≤ a, b ≤ n`, let `R = k[X₀, X₁]` map to
`k⟮ξ_a, ξ'_b⟯` by `X₀ ↦ ξ_a`, `X₁ ↦ ξ'_b`, and let `(U, V)` be a family of reduced
representations of the norms of `ηᵢ = y i / y 0`. Then for `i ≠ 0`,
`T_i = Faltings.BombieriRoth.polynomialT … i` is the image of a non-zero polynomial `T` of degree
at most `N d₁` in `X₀` and at most `N d₂` in `X₁`. -/
@[faltings "lem_bvr_polynomial_t_degree"]
public theorem exists_degreeOf_le_algebraMap_eq_polynomialT (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ AlgebraicGeometry.genus f) (P₁ : C →₀ ℤ)
    (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ)
    (hN : 2 * AlgebraicGeometry.genus f + 1 ≤ N)
    {n : ℕ} (hn : n = N - AlgebraicGeometry.genus f) (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    -- (N): the basis `x` is generic
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (hG3 : SatisfiesG3 k f x)
    -- the product `X = C ×_k C` with its projections and diagonal
    {X : Scheme.{u}} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) [IsIntegral X]
    [IsLocallyNoetherian X] (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k C.functionField] (hkC : ‹Algebra k C.functionField› = functionFieldAlgebra k f)
    [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB) {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (B : X → ℤ) (hB : ∀ w : X, B w =
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hD : ∀ i (w : X), 0 ≤ X.ord (y i) w + B w)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : X.functionField, (∀ w : X, 0 ≤ X.ord h w + B w) →
      h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ w : X, Order.coheight w = 1 → ∃ i, X.ord (y i) w + B w = 0)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k))) [IsClosedImmersion φB]
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of X.functionField)).inv.hom))
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w' : X,
      0 < X.ord (y i) w + B w → 0 < X.ord (y 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i j : Fin (m + 1),
      i.val = 1 → j.val = 2 → ∀ w w' : X, 0 < X.ord (y i) w + B w →
      0 < X.ord (y j) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w : X,
      0 < X.ord (y i) w + B w →
      0 ≤ X.ord (ι₁ (x a' / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b' / x 0)) w)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ q : X,
        (∀ r ∈ 𝔪,
          (∀ w : X, w ⤳ q → Order.coheight w = 1 → 0 ≤ X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) ∧
          ∃ w : X, w ⤳ q ∧ Order.coheight w = 1 ∧ 0 < X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) →
        ∀ w : X, w ⤳ q → Order.coheight w = 1 → X.ord (y i) w + B w = 0)
    -- the Vojta data: `d₁, d₂, d` positive integers with `δᵢ = (dᵢ + sB d) / N` integers
    (d₁ d₂ d δ₁ δ₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 0 < d)
    (hδ₁N : N * δ₁ = d₁ + sB * d) (hδ₂N : N * δ₂ = d₂ + sB * d)
    -- the section `s ≠ 0` of `𝒪(V)` and its representative with coefficients in `k`
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1))
    (a b : Fin n)
    -- the ring `R = k[ξ_a, ξ'_b]` and a family of reduced representations of the `Norm ηᵢ`
    [Algebra (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})]
    (hR : ∀ p : MvPolynomial (Fin 2) k,
      (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) p :
          X.functionField) =
        MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] p)
    (U V : Fin (m + 1) → MvPolynomial (Fin 2) k)
    (hUV : IsReducedNormRepresentation
      (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (MvPolynomial (Fin 2) k) (fun i => y i / y 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    ∃ T : MvPolynomial (Fin 2) k, T ≠ 0 ∧ T.degreeOf 0 ≤ N * d₁ ∧ T.degreeOf 1 ≤ N * d₂ ∧
      algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) T =
        polynomialT ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) F (fun i => y i / y 0) U V hUV d i := by
  subst hkC
  let : Algebra k C.functionField := functionFieldAlgebra k f
  -- the representative identity `F_j(ξ, ξ') = g η_jᵈ` with `g ≠ 0`
  obtain ⟨g, hg0, hgF⟩ := exists_ne_zero_affineEvaluation_eq_mul_pow hX x hli.ne_zero φNP
    hφNP hφNPx ψ hψ₁ hψ₂ hkX ι₁ ι₂ hι₁ hι₂ y hy _ φB hφB δ₁ δ₂ d s hs F hF
  -- `R → k⟮ξ_a, ξ'_b⟯` is injective, `ξ_a` and `ξ'_b` being algebraically independent
  have hNcl := isClosed_of_mem_support_smul hP₁cl (N : ℤ)
  have hdeg := finsum_smul_mul_residueDegree f hP₁ (N : ℤ)
  have hv : ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] =
      ![ι₁ (x a.succ / x 0), ι₂ (x b.succ / x 0)] := by
    rw [map_div₀, map_div₀]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})) :=
    fun p q hpq => injective_aeval_of_transcendental f hX (fun _ => rfl) ι₁ ι₂ hι₁ hι₂
      (transcendental_div k f hg _ hNcl N hN hdeg x hli hspan hG1 a.succ_ne_zero)
      (transcendental_div k f hg _ hNcl N hN hdeg x hli hspan hG1 b.succ_ne_zero)
      (by have h := congrArg Subtype.val hpq; rwa [hR, hR, hv] at h)
  have := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  -- `deg U_i = N s_B`, `T_i` is a polynomial `T`, and `G_i` is a polynomial `G` of bidegree
  -- at most `(N² δ₁, N² δ₂)`
  obtain ⟨hU₀, hU₁⟩ := degreeOf_num_eq_of_isReducedNormRepresentation k f hg P₁ hP₁cl hP₁ N hN
    hn x hli hspan hG1 hG2 hG3 hX Δ hΔ₁ hΔ₂ φNP hφNP hφNPx ψ hψ₁ hψ₂ rfl hkX ι₁ ι₂ hι₁ hι₂ sB hsB
    heΔ B hB y hy hD hyli hyspan hybpf φB hφB hBG1 hBG1' hBG2 hBG3 a b hR hUV i hi
  obtain ⟨T, hT⟩ := polynomialT_mem_range_algebraMap k f hg P₁ hP₁cl hP₁ N hN hn x hli hspan hG1
    hG2 hG3 hX Δ hΔ₁ hΔ₂ φNP hφNP hφNPx ψ hψ₁ hψ₂ rfl hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ B hB y hy hD hyli
    hyspan hybpf φB hφB hBG1 hBG1' hBG2 hBG3 d₁ d₂ d δ₁ δ₂ hd₁ hd₂ hd hδ₁N hδ₂N s hs F hF a b hR
    U V hUV i
  obtain ⟨G, hG₀, hG₁, hGe⟩ := exists_aeval_eq_formNorm_of_isVojtaRepresentative k f hg P₁ hP₁cl
    hP₁ N hN hn x hli hspan hG1 hG2 hG3 hX Δ hΔ₁ hΔ₂ φNP hφNP hφNPx ψ hψ₁ hψ₂ rfl hkX ι₁ ι₂ hι₁ hι₂
    sB hsB heΔ B hB y hy hD hyli hyspan hybpf φB hφB hBG1 hBG1' hBG2 hBG3 d₁ d₂ d δ₁ δ₂
    hd₁ hd₂ hd hδ₁N hδ₂N s hs F hF a b i
  have hV0 : algebraMap (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
        (V i) ^ d ≠ 0 :=
    pow_ne_zero d ((map_ne_zero_iff _ hinj).mpr (hUV.ne_zero i))
  -- the norm relation `G_0 U_iᵈ = G_i V_iᵈ` gives `T U_iᵈ = G` in `R`
  have hTG : T * U i ^ d = G := hinj <| by
    rw [map_mul, map_pow, hT, polynomialT, div_mul_eq_mul_div,
      IsReducedNormRepresentation.formNorm_mul_num_pow_eq ι₁ ι₂ x 0 a.succ b.succ
        (Fin.succ_ne_zero a) (Fin.succ_ne_zero b) (δ₁, δ₂) F g hg0 (fun j => y j / y 0)
        (div_self (hy 0)) hgF hUV i,
      mul_div_cancel_right₀ _ hV0]
    exact Subtype.ext (by rw [hR, hv]; exact hGe.symm)
  -- `T ≠ 0`, because `G_0 = Norm g ≠ 0`
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [map_zero, polynomialT, eq_comm, div_eq_zero_iff, or_iff_left hV0, formNorm, hgF 0,
      div_self (hy 0), one_pow, mul_one] at hT
    exact ((Ne.isUnit hg0).map (Algebra.norm _)).ne_zero hT
  have hU : U i ≠ 0 := by
    rintro h0
    rw [h0, MvPolynomial.degreeOf_zero] at hU₀
    exact (Nat.mul_pos (by omega) hsB).ne hU₀
  exact ⟨T, hT0, degreeOf_le_of_mul_pow_eq hT0 hU hTG 0 hG₀ hU₀ hδ₁N,
    degreeOf_le_of_mul_pow_eq hT0 hU hTG 1 hG₁ hU₁ hδ₂N, hT⟩

end Faltings.BombieriRoth
