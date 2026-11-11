module
public import Mordell.BombieriVojta.Norm.SectionRatio
public import Mordell.BombieriVojta.Representative.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Cube.SectionNeighbourhood
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct.ReindexFrame

/-!
# The function `g` in affine coordinates

In Section 9 of Bombieri's proof of the Mordell conjecture, a global section `s` of
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` on `C × C` gives the rational function
`g = s / (x₀^{δ₁} x₀'^{δ₂} / y₀^d)` (`Faltings.vojtaSectionRatio`). If `F = (F_i)` is a
representative of `s` (`Faltings.IsVojtaRepresentative`), so that `s = F_i(x, x') / y_i^d`, then
`g = F_i(ξ, ξ') / η_i^d` for every `i`, where `ξ_ν = x_ν / x₀`, `ξ'_ν = x'_ν / x₀'` and
`η_i = y_i / y₀` are the affine coordinates, viewed as rational functions on `C × C`.

## Main results

* `Faltings.IsVojtaRepresentative.eval₂_eq_vojtaSectionRatio_mul_pow`: `F_i(ξ, ξ') = g · η_i^d`.

## Implementation notes

* As for `Faltings.vojtaLineBundle`, `C × C` is an integral scheme `X` over a base `S`, with
  morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`.
* The affine coordinate `T_k / T₀` on `ℙʳ` is the section
  `HomogeneousLocalization.Away.mk _ _ 1 (X k) _` of the structure sheaf on the standard chart
  `D₊(T₀)` of the integral model, through `AlgebraicGeometry.Proj.awayToSection`; it is pulled
  back along `ψ ≫ pr₁`, `ψ ≫ pr₂` and `φ` (composed with the comparison to the integral model)
  and read in the function field as its germ at the generic point. This requires the generic
  point of `X` to lie in the three charts, that is `x₀ x₀' y₀ ≢ 0` on `X`, which holds in the
  source's setting since the coordinates are those of embeddings of `C`, and is a hypothesis
  here.
* The identity is stated as `F_i(ξ, ξ') = g · η_i^d` rather than `g = F_i(ξ, ξ') / η_i^d`. The two
  agree when `η_i ≠ 0`, which holds in the source's setting, and the multiplicative form holds
  also when `y_i` vanishes identically on `X`.
* The coefficients of the forms, in `Γ(S, 𝒪_S)`, act on the function field through the structure
  morphism `X ⟶ S` (`ψ ≫ pr₁ ≫ (ℙⁿ_S ⟶ S)`, as in `Faltings.IsVojtaRepresentative`).
* The proof works on `U = D(x₀ x₀' y₀)`, where `s|_U = g_U · (x ⊗ z)` with `x = x₀^{δ₁} x₀'^{δ₂}`
  and `z = y₀^{-d}`. Restricting the representative identity `s · y_i^d = F_i(x, x') ⊗ 1` to `U`
  and using `z · y_i^d = η_i^d · 1` and `F_i(x, x')|_U = F_i(ξ, ξ') · x` gives
  `(g_U η_i^d) · (x ⊗ 1) = F_i(ξ, ξ') · (x ⊗ 1)`; the section `x ⊗ 1` vanishes nowhere on `U`, so
  it generates freely and may be cancelled. Taking germs at the generic point gives the statement.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

namespace Faltings

universe u

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

private theorem lmul_assoc {Y : Scheme.{u}} (V : Y.Opens) (A B C : Y.Modules)
    (a : Γ(A, V)) (b : Γ(B, V)) (c : Γ(C, V)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    (α_ A B C).hom.app V (lmul V (A ⊗ B) C (lmul V A B a b) c) =
      lmul V A (B ⊗ C) a (lmul V B C b c) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  have h1 := Stacks.SheafOfModules.tensorObjIsoLeft_inv_tensorSectionsAt Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B C (op V)
    (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op V) A B a b) c
  have h2 := Stacks.SheafOfModules.tensorObjIsoRight_inv_tensorSectionsAt Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B C (op V) a
    (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op V) B C b c)
  have h3 := Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomAssociator Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B C (op V) a b c
  exact (congrArg _ h1.symm).trans (h3.trans h2)

private theorem lmul_whiskerLeft {Y : Scheme.{u}} (V : Y.Opens) (A : Y.Modules) {B B' : Y.Modules}
    (g : B ⟶ B') (a : Γ(A, V)) (b : Γ(B, V)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    (A ◁ g).app V (lmul V A B a b) = lmul V A B' a (g.app V b) :=
  Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomWhiskerLeft Y.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B (op V) g a b

/-- The pullback of a local section along `f`, by the unit of the pullback-pushforward
adjunction. -/
private noncomputable abbrev pu {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Modules) (V : Z.Opens) :
    Γ(F, V) ⟶ Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V

private theorem tensorIsoTensorModules_hom_lmul {Y : Scheme.{u}} (V : Y.Opens) (A B : Y.Modules)
    (a : Γ(A, V)) (b : Γ(B, V)) :
    (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y A B).hom.val.app (op V) (lmul V A B a b) =
      Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op V) A B a b := by
  rw [show Stacks.AmplePullbackPart1.tensorIsoTensorModules Y A B =
      Stacks.SheafOfModules.tensorObjIso Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B from
    (Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso A B).symm]
  exact Stacks.SheafOfModules.hom_val_app_inv_val_app _ _ _

private theorem pu_lmul {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A B : Z.Modules) (V : Z.Opens)
    (a : Γ(A, V)) (b : Γ(B, V)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).hom
        (f ⁻¹ᵁ V) (pu f (A ⊗ B) V (lmul V A B a b)) =
      lmul (f ⁻¹ᵁ V) _ _ (pu f A V a) (pu f B V b) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  have hT : ∀ (W : Scheme.{u}) (A B : W.Modules),
      Stacks.AmplePullbackPart1.tensorIsoTensorModules W A B =
        Stacks.SheafOfModules.tensorObjIso W.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf W) A B := fun W A B =>
    (Stacks.ProjectiveBundleConormal.tensorObjIso_eq_tensorIso A B).symm
  have h1 := Stacks.RingedSpace.pullbackUnit_naturality f.toLRSHom.toShHom
    (Stacks.AmplePullbackPart1.tensorIsoTensorModules Z A B).hom (op V) (lmul V A B a b)
  have h3 := Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul f.toLRSHom.toShHom A B (op V) a b
  refine (congrArg (fun w => (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y _ _).inv.val.app
      (op (f ⁻¹ᵁ V)) ((Stacks.RelativeVeryAmple.pullbackTensorModulesIso f A B).hom.val.app
        (op (f ⁻¹ᵁ V)) w))
      (h1.trans (congrArg _ (tensorIsoTensorModules_hom_lmul V A B a b)))).trans ?_
  refine (congrArg (fun w => (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y _ _).inv.val.app
      (op (f ⁻¹ᵁ V)) w) h3).trans ?_
  exact congrArg (fun (e : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory;
      ((Scheme.Modules.pullback f).obj A ⊗ (Scheme.Modules.pullback f).obj B : Y.Modules)) ≅ _) =>
      e.inv.val.app (op (f ⁻¹ᵁ V))
    (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op (f ⁻¹ᵁ V)) _ _
      (pu f A V a) (pu f B V b))) (hT Y _ _)

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

private theorem pu_nat {Y Z : Scheme.{u}} (f : Y ⟶ Z) {A B : Z.Modules} (φ : A ⟶ B)
    (V : Z.Opens) (a : Γ(A, V)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ V) (pu f A V a) = pu f B V (φ.app V a) :=
  Stacks.RingedSpace.pullbackUnit_naturality f.toLRSHom.toShHom φ (op V) a

private theorem pullbackGlobalSections_eq_pu {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Z.Modules)
    (a : Γ(A, ⊤)) : pullbackGlobalSections f A a = pu f A ⊤ a :=
  congrArg (fun φ : Γ(A, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj A, ⊤) => φ a)
    (pullbackGlobalSections_eq_unit f A)

private theorem eps_comp {Y : Scheme.{u}} {A B : Y.Modules}
    (v : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; 𝟙_ Y.Modules) ⟶ A)
    (φ : A ⟶ B) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y B (v ≫ φ) =
      φ.app ⊤ (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y A v) :=
  rfl

private theorem modules_iso_inv_hom_app {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (V : Y.Opens) (x : Γ(A, V)) :
    Scheme.Modules.Hom.app e.inv V (Scheme.Modules.Hom.app e.hom V x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
  rfl

/-- Restriction from the whole space to an open. -/
private noncomputable abbrev resTop {Y : Scheme.{u}} (A : Y.Modules) (V : Y.Opens) :
    Γ(A, ⊤) ⟶ Γ(A, V) :=
  A.presheaf.map (homOfLE le_top).op

private theorem app_res {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B) {V W : Y.Opens}
    (i : W ⟶ V) (a : Γ(A, V)) :
    B.presheaf.map i.op (φ.app V a) = φ.app W (A.presheaf.map i.op a) :=
  (PresheafOfModules.naturality_apply φ.val i.op a).symm

/-- Let `s|_U = f • (x ⊗ z)`, `μ (z ⊗ y|_U) = η • 1|_U` and `R|_U = F • x`, and suppose the
representative identity `s · y = R ⊗ 1` holds and `r ↦ r • (x ⊗ 1|_U)` is injective on `Γ(U)`.
Then `f η = F`. -/
private theorem core {X : Scheme.{u}} (U : X.Opens) {L M N Z : X.Modules}
    (μ : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (M ⊗ N : X.Modules)) ⟶ Z)
    (s : Γ((letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (L ⊗ M : X.Modules)), ⊤))
    (y : Γ(N, ⊤)) (R : Γ(L, ⊤)) (one : Γ(Z, ⊤)) (xX : Γ(L, U)) (zX : Γ(M, U))
    (f η F : Γ(X, U))
    (hs : resTop _ U s = f • lmul U L M xX zX)
    (hμ : μ.app U (lmul U M N zX (resTop N U y)) = η • resTop Z U one)
    (hR : resTop L U R = F • xX)
    (hF : letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      let e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      let tensorSec : ∀ {A B : X.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
        fun {_ _} a b => e _ ((λ_ (𝟙_ X.Modules)).inv ≫ ((e _).symm a ⊗ₘ (e _).symm b))
      e (L ⊗ Z) ((e _).symm (tensorSec s y) ≫ (α_ L M N).hom ≫ (L ◁ μ)) = tensorSec R one)
    (hinj : Function.Injective fun r : Γ(X, U) => r • lmul U L Z xX (resTop Z U one)) :
    f * η = F := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  apply hinj
  dsimp only
  have h := congrArg (resTop _ U) hF
  dsimp only at h
  rw [eps_comp, AddEquiv.apply_symm_apply, tensorSec_eq, tensorSec_eq] at h
  simp only [resTop] at h hs hR hμ hinj ⊢
  change (L ⊗ Z).presheaf.map (homOfLE le_top).op
      (((α_ L M N).hom ≫ L ◁ μ).app ⊤ (lmul ⊤ (L ⊗ M) N s y)) =
    (L ⊗ Z).presheaf.map (homOfLE le_top).op (lmul ⊤ L Z R one) at h
  calc (f * η) • lmul U L Z xX (Z.presheaf.map (homOfLE le_top).op one)
      = f • lmul U L Z xX (η • Z.presheaf.map (homOfLE le_top).op one) := by
        rw [lmul_smul_right, smul_smul]
    _ = f • lmul U L Z xX (μ.app U (lmul U M N zX (N.presheaf.map (homOfLE le_top).op y))) := by
        rw [hμ]
    _ = f • (L ◁ μ).app U (lmul U L (M ⊗ N) xX
          (lmul U M N zX (N.presheaf.map (homOfLE le_top).op y))) := by
        rw [lmul_whiskerLeft]
    _ = f • (L ◁ μ).app U ((α_ L M N).hom.app U (lmul U (L ⊗ M) N (lmul U L M xX zX)
          (N.presheaf.map (homOfLE le_top).op y))) := by
        rw [lmul_assoc]
    _ = ((α_ L M N).hom ≫ L ◁ μ).app U (lmul U (L ⊗ M) N (f • lmul U L M xX zX)
          (N.presheaf.map (homOfLE le_top).op y)) := by
        rw [lmul_smul_left, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.comp_app]
        rfl
    _ = ((α_ L M N).hom ≫ L ◁ μ).app U (lmul U (L ⊗ M) N
          ((L ⊗ M).presheaf.map (homOfLE le_top).op s) (N.presheaf.map (homOfLE le_top).op y)) := by
        rw [hs]
    _ = (L ⊗ Z).presheaf.map (homOfLE le_top).op
          (((α_ L M N).hom ≫ L ◁ μ).app ⊤ (lmul ⊤ (L ⊗ M) N s y)) := by
        rw [app_res, lmul_res]
    _ = (L ⊗ Z).presheaf.map (homOfLE le_top).op (lmul ⊤ L Z R one) := h
    _ = lmul U L Z (F • xX) (Z.presheaf.map (homOfLE le_top).op one) := by
        rw [lmul_res, hR]
    _ = F • lmul U L Z xX (Z.presheaf.map (homOfLE le_top).op one) := lmul_smul_left _ _ _ _ _ _

private theorem app_lmul_pu {Y Z : Scheme.{u}} (f : Y ⟶ Z) {A B C : Z.Modules}
    (θ : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (A ⊗ B : Z.Modules)) ⟶ C)
    (V : Z.Opens) (a : Γ(A, V)) (b : Γ(B, V)) :
    Scheme.Modules.Hom.app ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv ≫
        (Scheme.Modules.pullback f).map θ) (f ⁻¹ᵁ V)
      (lmul (f ⁻¹ᵁ V) _ _ (pu f A V a) (pu f B V b)) = pu f C V (θ.app V (lmul V A B a b)) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map θ) (f ⁻¹ᵁ V)
    (Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv
      (f ⁻¹ᵁ V) (lmul (f ⁻¹ᵁ V) _ _ (pu f A V a) (pu f B V b))) = _
  have h := congrArg (Scheme.Modules.Hom.app
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv (f ⁻¹ᵁ V))
    (pu_lmul f A B V a b)
  exact (congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map θ) (f ⁻¹ᵁ V))
    ((modules_iso_inv_hom_app _ _ _).symm.trans h)).symm.trans (pu_nat f θ V _)

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

/-- A morphism `φ^*h^*A ⊗ φ^*h^*B ⟶ φ^*h^*C` pulled back from `θ : A ⊗ B ⟶ C`, on the product of
two doubly pulled-back local sections. -/
private theorem app_pu_pu_lmul {X Y Z : Scheme.{u}} (φ : X ⟶ Y) (h : Y ⟶ Z) {A B C : Z.Modules}
    (θ : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (A ⊗ B : Z.Modules)) ⟶ C)
    (W : Z.Opens) {U : X.Opens} (hU : U ≤ φ ⁻¹ᵁ h ⁻¹ᵁ W) (a : Γ(A, W)) (b : Γ(B, W)) :
    Scheme.Modules.Hom.app ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ
        ((Scheme.Modules.pullback h).obj A) ((Scheme.Modules.pullback h).obj B)).inv ≫
        (Scheme.Modules.pullback φ).map ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso h
          A B).inv ≫ (Scheme.Modules.pullback h).map θ)) U
      (lmul U _ _
        (((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj A)).presheaf.map
          (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ W) (pu h A W a)))
        (((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj B)).presheaf.map
          (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ W) (pu h B W b)))) =
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback h).obj C)).presheaf.map
        (homOfLE hU).op (pu φ _ (h ⁻¹ᵁ W) (pu h C W (θ.app W (lmul W A B a b)))) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  refine (congrArg _ (lmul_res (homOfLE hU) _ _ (pu φ _ (h ⁻¹ᵁ W) (pu h A W a))
    (pu φ _ (h ⁻¹ᵁ W) (pu h B W b))).symm).trans ?_
  refine (app_res _ (homOfLE hU) _).symm.trans ?_
  refine congrArg _ ((app_lmul_pu φ _ (h ⁻¹ᵁ W) (pu h A W a) (pu h B W b)).trans ?_)
  exact congrArg _ (app_lmul_pu h θ W a b)

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

/-! ### Sections over an open and global sections of the open subscheme -/

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

private theorem restrictSection_open {X : Scheme.{u}} (U : X.Opens) (A : X.Modules) {V : X.Opens}
    (hUV : U ≤ V) (a : Γ(A, V)) :
    Stacks.NonvanishingLocusRestrict.restrictSection U A (A.presheaf.map (homOfLE hUV).op a) =
      ((Scheme.Modules.pullback U.ι).obj A).presheaf.map
        (homOfLE (fun x _ => hUV x.2 : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ V)).op (pu U.ι A V a) := by
  have h := pu_res U.ι A (homOfLE hUV) a
  refine (congrArg (((Scheme.Modules.pullback U.ι).obj A).presheaf.map
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op) h.symm).trans ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem restrictSection_top {X : Scheme.{u}} (U : X.Opens) (A : X.Modules) (a : Γ(A, ⊤)) :
    Stacks.NonvanishingLocusRestrict.restrictSection U A (A.presheaf.map (homOfLE le_top).op a) =
      pullbackGlobalSections U.ι A a := by
  rw [restrictSection_open]
  exact congrArg (fun i => ((Scheme.Modules.pullback U.ι).obj A).presheaf.map i
    (pu U.ι A ⊤ a)) (congrArg Quiver.Hom.op (Subsingleton.elim _ _))

private theorem restrictSection_smul {X : Scheme.{u}} (U : X.Opens) (A : X.Modules) (r : Γ(X, U))
    (a : Γ(A, U)) :
    Stacks.NonvanishingLocusRestrict.restrictSection U A (r • a) =
      U.topIso.inv r • Stacks.NonvanishingLocusRestrict.restrictSection U A a := by
  unfold Stacks.NonvanishingLocusRestrict.restrictSection
  have h := pu_smul U.ι A U r a
  change ((Scheme.Modules.pullback U.ι).obj A).presheaf.map _ (pu U.ι A U (r • a)) = _
  rw [h, Scheme.Modules.map_smul]
  congr 1
  rw [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
  exact presheaf_map_map _ _ _ r

private theorem restrictSection_injective {X : Scheme.{u}} (U : X.Opens) (A : X.Modules) :
    Function.Injective (Stacks.NonvanishingLocusRestrict.restrictSection U A) := fun a b h => by
  rw [← Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection U A a,
    ← Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection U A b, h]

private theorem restrictSection_app {X : Scheme.{u}} (U : X.Opens) {A B : X.Modules} (φ : A ⟶ B)
    (w : Γ(A, U)) :
    Stacks.NonvanishingLocusRestrict.restrictSection U B (φ.app U w) =
      ((Scheme.Modules.pullback U.ι).map φ).app ⊤
        (Stacks.NonvanishingLocusRestrict.restrictSection U A w) := by
  unfold Stacks.NonvanishingLocusRestrict.restrictSection
  change ((Scheme.Modules.pullback U.ι).obj B).presheaf.map _ (pu U.ι B U (φ.app U w)) = _
  rw [← pu_nat]
  exact app_res _ _ _

private theorem restrictSection_lmul {X : Scheme.{u}} (U : X.Opens) (A B : X.Modules)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    lmul ⊤ _ _ (Stacks.NonvanishingLocusRestrict.restrictSection U A a)
        (Stacks.NonvanishingLocusRestrict.restrictSection U B b) =
      Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso U.ι A B).hom ⊤
        (Stacks.NonvanishingLocusRestrict.restrictSection U (A ⊗ B) (lmul U A B a b)) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  unfold Stacks.NonvanishingLocusRestrict.restrictSection
  refine (lmul_res _ _ _ _ _).symm.trans ?_
  refine (congrArg _ (pu_lmul U.ι A B U a b).symm).trans ?_
  exact (PresheafOfModules.naturality_apply
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso U.ι A B).hom.val
    (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).op _).symm

private theorem eqToHom_twistingSheaf_apply {S : Type u} {σ : Type*} [CommRing S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] {a b : ℤ} (h : a = b)
    (V : (AlgebraicGeometry.Proj 𝒮).Opens) :
    let T : ℤ → (AlgebraicGeometry.Proj 𝒮).Modules := fun c =>
      ProjectiveSpectrum.Proj.twistingSheaf 𝒮 c
    ∀ (z : Γ(T a, V)) (x : V), ((eqToHom (congrArg T h)).app V z).1 x = z.1 x := by
  intro T z x
  subst h
  rfl

/-! ### Computations on the standard chart `D₊(T₀)` of the integral model -/

/-- On `D₊(T₀)`, the product of `T₀^{-d}` and `T_i^d` is `(T_i / T₀)^d` times the unit
section of `𝒪(0)`. -/
private theorem twistMul_yinv_eq (r d : ℕ) (i : Fin (r + 1)) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
    let T : ℤ → (projectiveSpaceAtUniverse.{u} r).Modules :=
      fun a => ProjectiveSpectrum.Proj.twistingSheaf 𝒜 a
    let D₀ : (projectiveSpaceAtUniverse.{u} r).Opens :=
      ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X 0)
    let yinv₀ : Γ(T (-(d : ℤ)), D₀) :=
      Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioSection 𝒜 (p := MvPolynomial.X 0)
        (q := 1) (e := 0) (d := 1) (n := -(d : ℤ)) (c := -(d : ℤ))
        ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _))
        (SetLike.one_mem_graded _) (by simp) (W := D₀) (by rw [mul_one]; exact le_rfl)
    let μQ : (T (-(d : ℤ)) ⊗ T d : (projectiveSpaceAtUniverse.{u} r).Modules) ⟶ T 0 :=
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceAtUniverse.{u} r)
        (T (-(d : ℤ))) (T d)).hom ≫
        Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 (-(d : ℤ)) d ≫
          eqToHom (congrArg T (neg_add_cancel (d : ℤ)))
    let ρ : Γ(projectiveSpaceAtUniverse.{u} r, D₀) := Proj.awayToSection 𝒜 (MvPolynomial.X 0)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X i)
        (by rw [smul_eq_mul, mul_one]; exact
          (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ i)))
    μQ.app D₀ (lmul D₀ _ _ yinv₀ ((T d).presheaf.map (homOfLE le_top).op
        (ProjectiveSpectrum.Proj.degreeSection 𝒜 d
          ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩))) =
      ρ ^ d •
        (T 0).presheaf.map (homOfLE (le_top : D₀ ≤ ⊤)).op
          (ProjectiveSpectrum.Proj.degreeSection 𝒜 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩) := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  intro 𝒜 T D₀ yinv₀ μQ ρ
  refine Subtype.ext (funext fun x => ?_)
  refine (eqToHom_twistingSheaf_apply 𝒜 (neg_add_cancel (d : ℤ)) D₀ _ x).trans ?_
  have h1 := tensorIsoTensorModules_hom_lmul D₀ (T (-(d : ℤ))) (T d) yinv₀
    ((T d).presheaf.map (homOfLE le_top).op (ProjectiveSpectrum.Proj.degreeSection 𝒜 d
          ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩))
  refine (congrArg (fun w => (((Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
    𝒜 (-(d : ℤ)) d).val.app (op D₀)).hom w).1 x) h1).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul 𝒜 (-(d : ℤ)) d D₀
    yinv₀ _ x).trans ?_
  have : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  change Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioFun 𝒜 (-(d : ℤ))
      (by rw [mul_one]) x *
      LocalizedModule.mk (MvPolynomial.X i ^ d) 1 =
    HomogeneousLocalization.val ((((Proj.awayToSection 𝒜 (MvPolynomial.X 0))
      (HomogeneousLocalization.Away.mk 𝒜 (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X i)
        (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_X _ i)))).1 x) ^ d) *
      LocalizedModule.mk 1 1
  rw [HomogeneousLocalization.val_pow]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  erw [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioFun, RingHom.id_apply]
  rw [← Localization.mk_eq_mk', Localization.mk_pow]
  change Localization.mk _ _ * Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  rw [Localization.mk_mul, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [SubmonoidClass.coe_pow, Int.toNat_neg_natCast, neg_neg,
    Int.toNat_natCast, pow_zero, one_pow, mul_one, one_mul, pow_one]

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

/-! ### Nonvanishing loci -/

private theorem nonvanishingLocus_app_subset {Y : Scheme.{u}} {A B : Y.Modules} (g : A ⟶ B)
    (a : Γ(A, ⊤)) :
    Stacks.Ample.nonvanishingLocus B (g.app ⊤ a) ⊆ Stacks.Ample.nonvanishingLocus A a := by
  intro x hx hc
  apply hx
  rw [← Stacks.ModuleStalk.mapFun_Γgerm]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul g x hc

private theorem mem_nonvanishingLocus_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) (a : Γ(A, ⊤)) (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj A)
        (pullbackGlobalSections f A a) ↔
      f.base x ∈ Stacks.Ample.nonvanishingLocus A a := by
  rw [pullbackGlobalSections_eq_pu]
  exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f A a x

private theorem tsec_eq_globalSection_unitMul {Y : Scheme.{u}} {A B : Y.Modules} (a : Γ(A, ⊤))
    (b : Γ(B, ⊤)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    tsec a b = Stacks.SectionProduct.globalSection Y _
      (Stacks.TensorSectionNonvanishing.unitMul
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y A).symm a)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y B).symm b)) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  unfold tsec Stacks.SectionProduct.globalSection Stacks.TensorSectionNonvanishing.unitMul
    Stacks.TensorSectionNonvanishing.mulRight
  congr 1
  rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, ← Category.assoc,
    ← rightUnitor_inv_naturality, Category.assoc]

private theorem nonvanishingLocus_tsec {Y : Scheme.{u}} {A B : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y A] [Stacks.Ample.IsInvertibleModule Y B]
    (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    Stacks.Ample.nonvanishingLocus (A ⊗ B) (tsec a b) =
      Stacks.Ample.nonvanishingLocus A a ∩ Stacks.Ample.nonvanishingLocus B b := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  rw [tsec_eq_globalSection_unitMul, Stacks.TensorSectionNonvanishing.nonvanishingLocus_unitMul]
  simp only [Stacks.SectionProduct.globalSection, AddEquiv.apply_symm_apply]

private theorem nonvanishingLocus_tsec_subset_left {Y : Scheme.{u}} {A B : Y.Modules}
    (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    Stacks.Ample.nonvanishingLocus (A ⊗ B) (tsec a b) ⊆ Stacks.Ample.nonvanishingLocus A a := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  rw [tsec_eq_globalSection_unitMul]
  have h := Stacks.TensorSectionNonvanishing.nonvanishingLocus_unitMul_subset_left
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y A).symm a)
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y B).symm b)
  simpa only [Stacks.SectionProduct.globalSection, AddEquiv.apply_symm_apply] using h

/-- The degree-`δ` section attached to a form `f` does not vanish on `D₊(f)`. -/
private theorem mem_nonvanishingLocus_degreeSection (r δ : ℕ) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)
    ∀ (f : 𝒜 δ) (x : projectiveSpaceAtUniverse.{u} r),
      x ∈ ProjectiveSpectrum.basicOpen 𝒜 (f : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)) →
      x ∈ Stacks.Ample.nonvanishingLocus (X := projectiveSpaceAtUniverse.{u} r)
        (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (δ : ℤ))
        (ProjectiveSpectrum.Proj.degreeSection 𝒜 δ f) := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  intro 𝒜 f x hx
  have hwhere : Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒜 1 = ⊤ :=
    (Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus 𝒜 1).trans
      (Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one 𝒜
        (Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
          (Fin (r + 1)) (ULift.{u} ℤ)) 1)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, δ = k * 1 := ⟨δ, (Nat.mul_one δ).symm⟩
  exact (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒜 1 k f (x := x) (by rw [hwhere]; trivial)).2 hx

/-! ### Nowhere-vanishing sections generate freely -/

private theorem presheaf_map_homOfLE_refl {Y : Scheme.{u}} (A : Y.Modules) {V : Y.Opens}
    (w : Γ(A, V)) : A.presheaf.map (homOfLE (le_refl V)).op w = w := by
  rw [show (homOfLE (le_refl V)).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- A global section of an invertible module that vanishes nowhere generates it. -/
private theorem exists_smul_eq_of_forall_mem_nonvanishingLocus {Y : Scheme.{u}} (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {t : Γ(A, ⊤)}
    (ht : ∀ x, x ∈ Stacks.Ample.nonvanishingLocus A t) (w : Γ(A, ⊤)) :
    ∃ g : Γ(Y, ⊤), g • t = w := by
  obtain ⟨g, hg⟩ := Stacks.ProjectiveBundleConormal.exists_eq_smul_res_of_subset_nonvanishingLocusOn
    A t ⊤ le_rfl (fun x _ => (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top A t).symm ▸
      ht x) w
  exact ⟨g, (congrArg (fun v => g • v) (presheaf_map_homOfLE_refl A t).symm).trans hg.symm⟩

/-- A global section of an invertible module that vanishes nowhere generates it freely. -/
private theorem smul_left_injective_of_forall_mem_nonvanishingLocus {Y : Scheme.{u}}
    (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] {t : Γ(A, ⊤)}
    (ht : ∀ x, x ∈ Stacks.Ample.nonvanishingLocus A t) :
    Function.Injective fun g : Γ(Y, ⊤) => g • t := fun g g' h =>
  Stacks.ProjectiveBundleConormal.smul_res_injective_of_subset_nonvanishingLocusOn A t ⊤ le_rfl
    (fun x _ => (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top A t).symm ▸ ht x) <|
    (congrArg (fun v => g • v) (presheaf_map_homOfLE_refl A t)).trans
      (h.trans (congrArg (fun v => g' • v) (presheaf_map_homOfLE_refl A t)).symm)

/-- The product of two pulled-back sections, carried to the pullback of the tensor product, does
not vanish where neither factor does. -/
private theorem mem_nonvanishingLocus_inv_lmul {X Y : Scheme.{u}} (f : Y ⟶ X) {A B : X.Modules}
    [Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback f).obj A)]
    [Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback f).obj B)]
    {a : Γ((Scheme.Modules.pullback f).obj A, ⊤)} {b : Γ((Scheme.Modules.pullback f).obj B, ⊤)}
    {x : Y} (ha : x ∈ Stacks.Ample.nonvanishingLocus _ a)
    (hb : x ∈ Stacks.Ample.nonvanishingLocus _ b) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj (A ⊗ B))
      (Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv ⊤
        (lmul ⊤ _ _ a b)) := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  refine (Set.ext_iff.mp (AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso
    (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).symm _) x).mpr ?_
  have h : x ∈ Stacks.Ample.nonvanishingLocus _ (tsec a b) := by
    rw [nonvanishingLocus_tsec]
    exact ⟨ha, hb⟩
  have e : tsec a b = lmul ⊤ _ _ a b := tensorSec_eq _ _ _ _
  rwa [e] at h

/-- **The function `g` in affine coordinates.** Let `s ≠ 0` be a global section of
`𝒪(V) = vojtaLineBundle ψ φ δ₁ δ₂ d` with representative `F = (F_i)`, and
`g = vojtaSectionRatio ψ φ δ₁ δ₂ d s`. Let `ξ_ν`, `ξ'_ν`, `η_i ∈ K(X)` be the rational functions
`x_ν / x₀`, `x'_ν / x₀'` and `y_i / y₀`, the germs of the pullbacks of the affine coordinates
`T_k / T₀` of the standard charts along `ψ ≫ pr₁`, `ψ ≫ pr₂` and `φ`. Then
`F_i(ξ, ξ') = g · η_i^d` for every `i`, that is `g = F_i(ξ, ξ') / η_i^d`. -/
@[faltings "lem_bvr_function_g"]
public theorem IsVojtaRepresentative.eval₂_eq_vojtaSectionRatio_mul_pow
    {S X : Scheme.{u}} [IsIntegral X] {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) :
    letI : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    -- the standard chart `D₊(T₀)` of `ℙʳ_S`, pulled back from the integral model
    let D : ∀ r : ℕ, (projectiveSpaceOver r S).Opens := fun r =>
      projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)
    -- the affine coordinate `T_k / T₀` on `D₊(T₀)`
    let ratio : ∀ (r : ℕ) (k : Fin (r + 1)), Γ(projectiveSpaceOver r S, D r) := fun r k =>
      (projectiveSpaceOver.toIntegralAtUniverse r S).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
            (MvPolynomial.X k) (by simpa using MvPolynomial.isHomogeneous_X _ k)))
    let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    ∀ (hx : genericPoint X ∈ (ψ ≫ p₁) ⁻¹ᵁ D n) (hx' : genericPoint X ∈ (ψ ≫ p₂) ⁻¹ᵁ D n)
      (hy : genericPoint X ∈ φ ⁻¹ᵁ D m),
    -- `ξ_ν`, `ξ'_ν`, `η_i` in the function field
    let ξ : Fin (n + 1) → X.functionField := fun ν =>
      X.presheaf.germ _ (genericPoint X) hx ((ψ ≫ p₁).app (D n) (ratio n ν))
    let ξ' : Fin (n + 1) → X.functionField := fun ν =>
      X.presheaf.germ _ (genericPoint X) hx' ((ψ ≫ p₂).app (D n) (ratio n ν))
    let η : Fin (m + 1) → X.functionField := fun i =>
      X.presheaf.germ _ (genericPoint X) hy (φ.app (D m) (ratio m i))
    -- the coefficients act through the structure morphism `X ⟶ S`
    let c : Γ(S, ⊤) →+* X.functionField :=
      ((ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom
    ∀ i, MvPolynomial.eval₂ c (Sum.elim ξ ξ') (F i) =
      vojtaSectionRatio ψ φ δ₁ δ₂ d s * η i ^ d := by
  intro D ratio p₁ p₂ hx hx' hy ξ ξ' η c i
  unfold vojtaSectionRatio
  extract_lets 𝒜 g T twist pull tensorSec x₀pow D₀ D' q₁ q₂ O₁ O₂ L M U ι yinv₀ yinv xpow eU e sU
  rw [isVojtaRepresentative_iff] at hF
  extract_lets T' twist' form ε O₁' O₂' L' M' N Z tensorSec' μ y one σ mono
    restrict at hF
  obtain ⟨hhom, hrep⟩ := hF
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  have hηU : genericPoint X ∈ U := ⟨⟨hx, hx'⟩, hy⟩
  have hUne : Nonempty U := ⟨⟨_, hηU⟩⟩
  rw [dite_eq_left hUne]
  -- the sections `x₀^{δ₁} x₀'^{δ₂}` and `y₀^{-d}` over `U`
  let xX : Γ(L, U) := resTop L U (pullbackGlobalSections ψ (O₁ ⊗ O₂)
    (tensorSec (pullbackGlobalSections q₁ (twist n δ₁) (x₀pow n δ₁))
      (pullbackGlobalSections q₂ (twist n δ₂) (x₀pow n δ₂))))
  let zX : Γ(M, U) := M.presheaf.map (homOfLE (fun _ h => h.2 : U ≤ φ ⁻¹ᵁ D' m)).op
    (pull φ (twist m (-(d : ℤ))) (D' m) (pull (g m) (T m (-(d : ℤ))) (D₀ m) yinv₀))
  have hxpow : xpow = Stacks.NonvanishingLocusRestrict.restrictSection U L xX :=
    (restrictSection_top U L _).symm
  have hyinv : yinv = Stacks.NonvanishingLocusRestrict.restrictSection U M zX :=
    (restrictSection_open U M _ _).symm
  have he0 : e =
      Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι L M).inv
      ⊤ (lmul ⊤ _ _ xpow yinv) :=
    (eps_comp ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv U _).symm
        (tensorSec xpow yinv))
      (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι L M).inv).trans
      (congrArg _ ((AddEquiv.apply_symm_apply _ _).trans (tensorSec_eq _ _ xpow yinv)))
  have he : e = Stacks.NonvanishingLocusRestrict.restrictSection U (L ⊗ M) (lmul U L M xX zX) := by
    rw [he0, hxpow, hyinv, restrictSection_lmul]
    exact modules_iso_inv_hom_app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι L M) ⊤ _
  have hsU : sU = Stacks.NonvanishingLocusRestrict.restrictSection U (L ⊗ M)
      (resTop (L ⊗ M) U s) :=
    (restrictSection_top U (L ⊗ M) s).symm
  -- the affine coordinates and the coefficients, as functions on `U`
  have hUy : U ≤ φ ⁻¹ᵁ D m := fun _ h => h.2
  have hUx : U ≤ (ψ ≫ p₁) ⁻¹ᵁ D n := fun _ h => h.1.1
  have hUx' : U ≤ (ψ ≫ p₂) ⁻¹ᵁ D n := fun _ h => h.1.2
  let ηU : Γ(X, U) := X.presheaf.map (homOfLE hUy).op (φ.app (D m) (ratio m i))
  let ξU : Fin (n + 1) → Γ(X, U) := fun ν =>
    X.presheaf.map (homOfLE hUx).op ((ψ ≫ p₁).app (D n) (ratio n ν))
  let ξ'U : Fin (n + 1) → Γ(X, U) := fun ν =>
    X.presheaf.map (homOfLE hUx').op ((ψ ≫ p₂).app (D n) (ratio n ν))
  let cU : Γ(S, ⊤) →+* Γ(X, U) := (X.presheaf.map (homOfLE le_top).op).hom.comp σ.appTop.hom
  have hμ' : ∀ j, μ.app U (lmul U M N zX (resTop N U (y j))) =
      (X.presheaf.map (homOfLE hUy).op (φ.app (D m) (ratio m j))) ^ d • resTop Z U one := by
    intro j
    have hyU := resTop_pu_pu φ (g m) (T m d) (D₀ m) hUy
      (ProjectiveSpectrum.Proj.degreeSection (𝒜 m) d
        ⟨MvPolynomial.X j ^ d, MvPolynomial.isHomogeneous_X_pow j d⟩)
    have honeU := resTop_pu_pu φ (g m) (T m 0) (D₀ m) hUy
      (ProjectiveSpectrum.Proj.degreeSection (𝒜 m) 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩)
    have hQ := twistMul_yinv_eq.{u} m d j
    have hyi : resTop N U (y j) = N.presheaf.map (homOfLE hUy).op
        (pu φ (twist m d) (D' m) (pu (g m) (T m d) (D₀ m) ((T m d).presheaf.map
          (homOfLE le_top).op (ProjectiveSpectrum.Proj.degreeSection (𝒜 m) d
            ⟨MvPolynomial.X j ^ d, MvPolynomial.isHomogeneous_X_pow j d⟩)))) := hyU
    have hz : zX = M.presheaf.map (homOfLE hUy).op
        (pu φ (twist m (-(d : ℤ))) (D' m) (pu (g m) (T m (-(d : ℤ))) (D₀ m) yinv₀)) := rfl
    rw [hyi, hz]
    refine (app_pu_pu_lmul φ (g m) _ (D₀ m) hUy yinv₀ _).trans ?_
    refine (congrArg (fun w => ((Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback (g m)).obj (T m 0))).presheaf.map (homOfLE hUy).op
        (pu φ _ ((g m) ⁻¹ᵁ D₀ m) (pu (g m) _ (D₀ m) w))) hQ).trans ?_
    refine (res_pu_pu_smul φ (g m) (T m 0) (D₀ m) hUy _ _).trans ?_
    have hsc : X.presheaf.map (homOfLE hUy).op (φ.app ((g m) ⁻¹ᵁ D₀ m) ((g m).app (D₀ m)
        ((Proj.awayToSection (𝒜 m) (MvPolynomial.X 0)
          (HomogeneousLocalization.Away.mk (𝒜 m) (MvPolynomial.isHomogeneous_X _ 0) 1
            (MvPolynomial.X j) (by
              rw [smul_eq_mul, mul_one]
              exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
                (MvPolynomial.isHomogeneous_X _ j)))) ^ d))) =
        (X.presheaf.map (homOfLE hUy).op (φ.app (D m) (ratio m j))) ^ d :=
      (congrArg _ ((congrArg _ (map_pow _ _ _)).trans (map_pow _ _ _))).trans (map_pow _ _ _)
    exact congrArg₂ (· • ·) hsc honeU.symm
  have hμ : μ.app U (lmul U M N zX (resTop N U (y i))) = ηU ^ d • resTop Z U one := hμ' i
  -- invertibility of the line bundles involved
  have iTw : ∀ r (a : ℤ), Stacks.Ample.IsInvertibleModule (projectiveSpaceOver r S) (twist r a) :=
    fun r a => @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ (g r) (T r a)
      (Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule
        (ULift.{u} ℤ) r a)
  have iO₁ : Stacks.Ample.IsInvertibleModule _ O₁ :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ q₁ _ (iTw n δ₁)
  have iO₂ : Stacks.Ample.IsInvertibleModule _ O₂ :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ q₂ _ (iTw n δ₂)
  have iL : Stacks.Ample.IsInvertibleModule X L :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ψ _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ O₁ O₂ iO₁ iO₂)
  have iM : Stacks.Ample.IsInvertibleModule X M :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ φ _ (iTw m _)
  have iZ : Stacks.Ample.IsInvertibleModule X Z :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ φ _ (iTw m 0)
  have iLU : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback ι).obj L) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ι _ iL
  have iMU : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback ι).obj M) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ι _ iM
  have iZU : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback ι).obj Z) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ι _ iZ
  have iLMU : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback ι).obj (L ⊗ M)) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ι _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ L M iL iM)
  have iLZU : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback ι).obj (L ⊗ Z)) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ι _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ L Z iL iZ)
  -- nonvanishing of `x₀^{δ₁} x₀'^{δ₂}`, of `1` and of `y₀^{-d}` on `U`
  have hxpow_nv : ∀ x : (U : Scheme.{u}),
      x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ι).obj L) xpow := by
    intro x
    have hxU : ι.base x ∈ U := x.2
    rw [mem_nonvanishingLocus_pullbackGlobalSections, mem_nonvanishingLocus_pullbackGlobalSections]
    change ψ.base (ι.base x) ∈ Stacks.Ample.nonvanishingLocus (O₁ ⊗ O₂) (tsec _ _)
    rw [@nonvanishingLocus_tsec _ _ _ iO₁ iO₂]
    refine ⟨?_, ?_⟩
    · exact (mem_nonvanishingLocus_pullbackGlobalSections q₁ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g n) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection n δ₁ _ _
            fun h => hxU.1.1 (Ideal.IsPrime.mem_of_pow_mem (ProjectiveSpectrum.isPrime _) _ h)))
    · exact (mem_nonvanishingLocus_pullbackGlobalSections q₂ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g n) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection n δ₂ _ _
            fun h => hxU.1.2 (Ideal.IsPrime.mem_of_pow_mem (ProjectiveSpectrum.isPrime _) _ h)))
  have hone_nv : ∀ x : (U : Scheme.{u}), x ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback ι).obj Z) (pullbackGlobalSections ι Z one) := by
    intro x
    refine (mem_nonvanishingLocus_pullbackGlobalSections ι _ _ _).mpr
      ((mem_nonvanishingLocus_pullbackGlobalSections φ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g m) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection m 0 _ _ ?_)))
    change _ ∈ ProjectiveSpectrum.basicOpen _ 1
    rw [ProjectiveSpectrum.basicOpen_one]
    trivial
  have hr0 : X.presheaf.map (homOfLE hUy).op (φ.app (D m) (ratio m 0)) = 1 := by
    have h1 : HomogeneousLocalization.Away.mk (𝒜 m) (MvPolynomial.isHomogeneous_X _ 0) 1
        (MvPolynomial.X 0) (by
          rw [smul_eq_mul, mul_one]
          exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
            (MvPolynomial.isHomogeneous_X _ 0)) = 1 := by
      apply HomogeneousLocalization.val_injective
      erw [HomogeneousLocalization.Away.val_mk]
      rw [HomogeneousLocalization.val_one, ← Localization.mk_one]
      exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))
    change X.presheaf.map (homOfLE hUy).op (φ.app (D m) ((g m).app _
      (Proj.awayToSection (𝒜 m) (MvPolynomial.X 0) _))) = 1
    rw [h1]
    exact (congrArg _ ((congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans
      (map_one _))).trans (map_one _)
  have hy0 : μ.app U (lmul U M N zX (resTop N U (y 0))) = resTop Z U one := by
    rw [hμ' 0, hr0, one_pow, one_smul]
  have hΦ : Stacks.NonvanishingLocusRestrict.restrictSection U Z (resTop Z U one) =
      ((Scheme.Modules.pullback ι).map μ).app ⊤
        (Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι M N).inv ⊤
          (lmul ⊤ _ _ yinv (pullbackGlobalSections ι N (y 0)))) := by
    rw [← hy0, restrictSection_app, hyinv, ← restrictSection_top U N (y 0), restrictSection_lmul]
    exact congrArg _ (modules_iso_inv_hom_app _ _ _).symm
  have hyinv_nv : ∀ x : (U : Scheme.{u}),
      x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ι).obj M) yinv := by
    intro x
    have h1 : x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ι).obj Z)
        (Stacks.NonvanishingLocusRestrict.restrictSection U Z (resTop Z U one)) := by
      rw [restrictSection_top]
      exact hone_nv x
    rw [hΦ] at h1
    have h2 := nonvanishingLocus_app_subset _ _ h1
    have h3 : x ∈ Stacks.Ample.nonvanishingLocus _
        (lmul ⊤ _ _ yinv (pullbackGlobalSections ι N (y 0))) :=
      (Set.ext_iff.mp (AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso
        (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι M N).symm _) x).mp h2
    have h4 : x ∈ Stacks.Ample.nonvanishingLocus _
        (tsec yinv (pullbackGlobalSections ι N (y 0))) := by
      have e : tsec yinv (pullbackGlobalSections ι N (y 0)) =
          lmul ⊤ _ _ yinv (pullbackGlobalSections ι N (y 0)) := tensorSec_eq _ _ _ _
      rwa [e]
    exact nonvanishingLocus_tsec_subset_left _ _ h4
  have hex : ∃ f : Γ((U : Scheme.{u}), ⊤), f • e = sU := by
    rw [he0]
    exact exists_smul_eq_of_forall_mem_nonvanishingLocus _
      (fun x => mem_nonvanishingLocus_inv_lmul ι (hxpow_nv x) (hyinv_nv x)) sU
  rw [dite_eq_left hex]
  have hs' : resTop (L ⊗ M) U s = U.topIso.hom hex.choose • lmul U L M xX zX := by
    apply restrictSection_injective U
    rw [restrictSection_smul, ← he, ← hsU, ← CategoryTheory.comp_apply, Iso.hom_inv_id,
      CategoryTheory.id_apply]
    exact hex.choose_spec.symm
  have hR : resTop L U (restrict (F i)) =
      MvPolynomial.eval₂ cU (Sum.elim ξU ξ'U) (F i) • xX := by
    have hmono : ∀ α ∈ (F i).support, resTop L U (mono α) =
        ((∏ ν, ξU ν ^ α (Sum.inl ν)) * ∏ ν, ξ'U ν ^ α (Sum.inr ν)) • xX := by
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
          (pullbackGlobalSections p₁ (twist' n δ₁) (form n δ₁
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.1⟩))
          (pullbackGlobalSections p₂ (twist' n δ₂) (form n δ₂
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.2⟩))) := dite_eq_left hdeg
      rw [hm]
      have hU' : U ≤ ψ ⁻¹ᵁ (p₁ ⁻¹ᵁ (g n) ⁻¹ᵁ D₀ n ⊓ p₂ ⁻¹ᵁ (g n) ⁻¹ᵁ D₀ n) := fun _ h => h.1
      refine (resTop_pullback_lmul_smul ψ p₁ p₂ (g n) (D₀ n) hU' _ _ _ _ _ _
        (degreeSection_monomial_eq n δ₁ _ hdeg.1)
        (degreeSection_monomial_eq n δ₂ _ hdeg.2)).trans ?_
      refine congrArg₂ (· • ·) ?_ rfl
      rw [map_mul, map_mul]
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [res_app_res]
        exact res_app_away_monomial n δ₁ (ψ ≫ p₁ ≫ g n) _ hdeg.1 _
      · rw [res_app_res]
        exact res_app_away_monomial n δ₂ (ψ ≫ p₂ ≫ g n) _ hdeg.2 _
    have hexp : MvPolynomial.eval₂ cU (Sum.elim ξU ξ'U) (F i) = ∑ α ∈ (F i).support,
        cU ((F i).coeff α) * ((∏ ν, ξU ν ^ α (Sum.inl ν)) * ∏ ν, ξ'U ν ^ α (Sum.inr ν)) := by
      rw [MvPolynomial.eval₂_eq']
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hexp, Finset.sum_smul]
    change resTop L U (∑ α ∈ (F i).support, σ.appTop ((F i).coeff α) • mono α) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Scheme.Modules.map_smul, hmono α hα, smul_smul]
    rfl
  have hinj : Function.Injective fun r : Γ(X, U) => r • lmul U L Z xX (resTop Z U one) := by
    intro r r' h
    have hB : Stacks.NonvanishingLocusRestrict.restrictSection U (L ⊗ Z)
        (lmul U L Z xX (resTop Z U one)) =
        Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ι L Z).inv ⊤
          (lmul ⊤ _ _ xpow (pullbackGlobalSections ι Z one)) := by
      rw [hxpow, ← restrictSection_top U Z one, restrictSection_lmul]
      exact (modules_iso_inv_hom_app _ _ _).symm
    have h' := congrArg (Stacks.NonvanishingLocusRestrict.restrictSection U (L ⊗ Z)) h
    simp only at h'
    rw [restrictSection_smul, restrictSection_smul, hB] at h'
    have := congrArg U.topIso.hom (smul_left_injective_of_forall_mem_nonvanishingLocus _
      (fun x => mem_nonvanishingLocus_inv_lmul ι (hxpow_nv x) (hone_nv x)) h')
    rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  have key := core (L := L) (M := M) (N := N) (Z := Z) U μ s (y i) (restrict (F i)) one xX zX
    _ _ _ hs' hμ hR (hrep i) hinj
  have hγ := congrArg (X.germToFunctionField U) key
  rw [map_mul, map_pow, MvPolynomial.eval₂_comp_left] at hγ
  have hη : X.germToFunctionField U ηU = η i :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUy) _ hηU _
  have hc : (X.germToFunctionField U).hom.comp cU = c := by
    ext r
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE le_top) _ hηU _
  have hξ : (X.germToFunctionField U) ∘ Sum.elim ξU ξ'U = Sum.elim ξ ξ' := by
    funext ν
    rcases ν with ν | ν
    · exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUx) _ hηU _
    · exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUx') _ hηU _
  rw [hη, hc, hξ] at hγ
  exact hγ.symm

end Faltings
