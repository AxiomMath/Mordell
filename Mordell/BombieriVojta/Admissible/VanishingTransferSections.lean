module

public import Mordell.BombieriVojta.Admissible.BiorderIdeal
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Norm.Relation
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.Polynomial.HasseDeriv
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.BombieriVojta.Norm.SectionRatioEval
public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass

/-!
# Dehomogenising a representative on a product chart

Local products and pull-backs of sections, restriction to open subschemes, charts `D₊(T₀)` and
nonvanishing loci, ending in the identity `F(ξ, ξ') = σ · u` for a representative of a section of
`𝒪(V)` on `D₊(x₀) × D₊(x₀')` (`VanishingTransfer.Sections.exists_eval₂_eq_mul_of_smul_eq`).
-/

universe u

namespace Faltings.BombieriRoth.VanishingTransfer

/-! ### Dehomogenising a representative on the chart `D₊(x₀) × D₊(x₀')` -/

namespace Sections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open scoped Stacks.TensorSectionNonvanishing
open Faltings

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
  rw [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
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
  refine h2.trans ?_
  exact congrArg₂ (fun x y => (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv.val.app (op ⊤)
      (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op ⊤) A B x y)) ha hb

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
    Function.Injective (Stacks.NonvanishingLocusRestrict.restrictSection U A) :=
  Function.LeftInverse.injective
    (Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection U A)

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

/-! ### Nonvanishing loci -/

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

/-- **Cancelling the product `x ⊗ 1`.** If `s|_U = σ • e_U` and `e_U · y` is `u` times `x ⊗ 1`,
then the dehomogenised form `F` of the representative identity `s · y = R ⊗ 1` is `σ u`. -/
private theorem mul_eq_of_tensorSec_eq {X : Scheme.{u}} (U : X.Opens) {L M N Z : X.Modules}
    (μ : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (M ⊗ N : X.Modules)) ⟶ Z)
    (s : Γ((letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (L ⊗ M : X.Modules)), ⊤))
    (y : Γ(N, ⊤)) (R : Γ(L, ⊤)) (one : Γ(Z, ⊤)) (xX : Γ(L, U))
    (eU : Γ((letI := Stacks.SheafInternalHom.schemeMonoidalCategory; (L ⊗ M : X.Modules)), U))
    (σ u F : Γ(X, U))
    (hs : resTop _ U s = σ • eU)
    (hE : letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      ((α_ L M N).hom ≫ L ◁ μ).app U (lmul U (L ⊗ M) N eU (resTop N U y)) =
        u • lmul U L Z xX (resTop Z U one))
    (hR : resTop L U R = F • xX)
    (hF : letI := Stacks.SheafInternalHom.schemeMonoidalCategory
      let e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      let tensorSec : ∀ {A B : X.Modules}, Γ(A, ⊤) → Γ(B, ⊤) → Γ(A ⊗ B, ⊤) :=
        fun {_ _} a b => e _ ((λ_ (𝟙_ X.Modules)).inv ≫ ((e _).symm a ⊗ₘ (e _).symm b))
      e (L ⊗ Z) ((e _).symm (tensorSec s y) ≫ (α_ L M N).hom ≫ (L ◁ μ)) = tensorSec R one)
    (hinj : Function.Injective fun r : Γ(X, U) => r • lmul U L Z xX (resTop Z U one)) :
    σ * u = F := by
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  apply hinj
  dsimp only
  have h := congrArg (resTop _ U) hF
  dsimp only at h
  rw [eps_comp, AddEquiv.apply_symm_apply, tensorSec_eq, tensorSec_eq] at h
  simp only [resTop] at h hs hR hE hinj ⊢
  change (L ⊗ Z).presheaf.map (homOfLE le_top).op
      (((α_ L M N).hom ≫ L ◁ μ).app ⊤ (lmul ⊤ (L ⊗ M) N s y)) =
    (L ⊗ Z).presheaf.map (homOfLE le_top).op (lmul ⊤ L Z R one) at h
  calc (σ * u) • lmul U L Z xX (Z.presheaf.map (homOfLE le_top).op one)
      = σ • (u • lmul U L Z xX (Z.presheaf.map (homOfLE le_top).op one)) := by
        rw [smul_smul]
    _ = σ • ((α_ L M N).hom ≫ L ◁ μ).app U
          (lmul U (L ⊗ M) N eU (N.presheaf.map (homOfLE le_top).op y)) := by
        rw [hE]
    _ = ((α_ L M N).hom ≫ L ◁ μ).app U (lmul U (L ⊗ M) N (σ • eU)
          (N.presheaf.map (homOfLE le_top).op y)) := by
        rw [lmul_smul_left, Scheme.Modules.Hom.app_smul]
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

/-- Let `F` be a representative of the global section `s` of `vojtaLineBundle ψ φ δ₁ δ₂ d`, let
`σ • e = s|_U` for a section `e` over `U`, and let `W ≤ U` be an open on which both projections of
`ψ` land in the chart `D₊(T₀)` of `ℙⁿ_S`. Then for every `i` the dehomogenisation `F_i(ξ, ξ')`
of `F i` in the affine coordinates `ξ_ν = T_ν / T₀` on the two factors is `σ|_W` times a section
over `W`. -/
public theorem exists_eval₂_eq_mul_of_smul_eq
    {S X : Scheme.{u}} {n m : ℕ}
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
    let ratio : ∀ (r : ℕ) (k : Fin (r + 1)), Γ(projectiveSpaceOver r S, D r) := fun r k =>
      (projectiveSpaceOver.toIntegralAtUniverse r S).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
            (MvPolynomial.X k) (by simpa using MvPolynomial.isHomogeneous_X _ k)))
    let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    ∀ (U W : X.Opens) (hWU : W ≤ U) (hW₁ : W ≤ (ψ ≫ p₁) ⁻¹ᵁ D n) (hW₂ : W ≤ (ψ ≫ p₂) ⁻¹ᵁ D n)
      (e : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, U)) (σ : Γ(X, U))
      (hσ : σ • e = (vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE le_top).op s) (i),
    ∃ v : Γ(X, W), MvPolynomial.eval₂
        ((X.presheaf.map (homOfLE le_top).op).hom.comp
          (ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)).appTop.hom)
        (Sum.elim (fun ν => X.presheaf.map (homOfLE hW₁).op ((ψ ≫ p₁).app (D n) (ratio n ν)))
          (fun ν => X.presheaf.map (homOfLE hW₂).op ((ψ ≫ p₂).app (D n) (ratio n ν)))) (F i) =
      X.presheaf.map (homOfLE hWU).op σ * v := by
  intro D ratio p₁ p₂ U W hWU hW₁ hW₂ e σ hσ i
  rw [isVojtaRepresentative_iff] at hF
  extract_lets g' T' twist' form ε O₁' O₂' L' M' N Z tensorSec' μ y one σ' mono
    restrict at hF
  obtain ⟨hhom, hrep⟩ := hF
  let _ : ∀ Y : Scheme.{u}, MonoidalCategory Y.Modules :=
    Stacks.SheafInternalHom.schemeMonoidalCategory
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  let D₀ : ∀ r : ℕ, (projectiveSpaceAtUniverse.{u} r).Opens := fun r =>
    ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)
  have hW' : W ≤ ψ ⁻¹ᵁ (p₁ ⁻¹ᵁ (g' n) ⁻¹ᵁ D₀ n ⊓ p₂ ⁻¹ᵁ (g' n) ⁻¹ᵁ D₀ n) :=
    fun x hx => ⟨hW₁ hx, hW₂ hx⟩
  let xpow : Γ(L', ⊤) := pullbackGlobalSections ψ (O₁' ⊗ O₂')
    (tensorSec' (pullbackGlobalSections p₁ (twist' n δ₁)
        (form n δ₁ ⟨MvPolynomial.X 0 ^ δ₁, MvPolynomial.isHomogeneous_X_pow 0 δ₁⟩))
      (pullbackGlobalSections p₂ (twist' n δ₂)
        (form n δ₂ ⟨MvPolynomial.X 0 ^ δ₂, MvPolynomial.isHomogeneous_X_pow 0 δ₂⟩)))
  let xX : Γ(L', W) := resTop L' W xpow
  let ξW : Fin (n + 1) → Γ(X, W) := fun ν =>
    X.presheaf.map (homOfLE hW₁).op ((ψ ≫ p₁).app (D n) (ratio n ν))
  let ξ'W : Fin (n + 1) → Γ(X, W) := fun ν =>
    X.presheaf.map (homOfLE hW₂).op ((ψ ≫ p₂).app (D n) (ratio n ν))
  let cW : Γ(S, ⊤) →+* Γ(X, W) := (X.presheaf.map (homOfLE le_top).op).hom.comp σ'.appTop.hom
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
        simpa only [Finsupp.degree_eq_sum, Finsupp.comapDomain_apply] using hw
      have hm : mono α = pullbackGlobalSections ψ (O₁' ⊗ O₂') (tensorSec'
          (pullbackGlobalSections p₁ (twist' n δ₁) (form n δ₁
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.1⟩))
          (pullbackGlobalSections p₂ (twist' n δ₂) (form n δ₂
            ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
              MvPolynomial.isHomogeneous_monomial _ hdeg.2⟩))) := dite_eq_left hdeg
      rw [hm]
      refine (resTop_pullback_lmul_smul ψ p₁ p₂ (g' n) (D₀ n) hW' _ _ _ _ _ _
        (degreeSection_monomial_eq n δ₁ _ hdeg.1)
        (degreeSection_monomial_eq n δ₂ _ hdeg.2)).trans ?_
      refine congrArg₂ (· • ·) ?_ rfl
      rw [map_mul, map_mul]
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [res_app_res]
        exact res_app_away_monomial n δ₁ (ψ ≫ p₁ ≫ g' n) _ hdeg.1 _
      · rw [res_app_res]
        exact res_app_away_monomial n δ₂ (ψ ≫ p₂ ≫ g' n) _ hdeg.2 _
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
  have iTw : ∀ r (a : ℤ), Stacks.Ample.IsInvertibleModule (projectiveSpaceOver r S) (twist' r a) :=
    fun r a => @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ (g' r) (T' r a)
      (Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule
        (ULift.{u} ℤ) r a)
  have iO₁ : Stacks.Ample.IsInvertibleModule _ O₁' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ p₁ _ (iTw n δ₁)
  have iO₂ : Stacks.Ample.IsInvertibleModule _ O₂' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ p₂ _ (iTw n δ₂)
  have iL : Stacks.Ample.IsInvertibleModule X L' :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ ψ _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ O₁' O₂' iO₁ iO₂)
  have iZ : Stacks.Ample.IsInvertibleModule X Z :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ φ _ (iTw m 0)
  have iLW : Stacks.Ample.IsInvertibleModule W ((Scheme.Modules.pullback W.ι).obj L') :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ W.ι _ iL
  have iZW : Stacks.Ample.IsInvertibleModule W ((Scheme.Modules.pullback W.ι).obj Z) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ W.ι _ iZ
  have iLZW : Stacks.Ample.IsInvertibleModule W ((Scheme.Modules.pullback W.ι).obj (L' ⊗ Z)) :=
    @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ W.ι _
      (@Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ L' Z iL iZ)
  have hxpow_nv : ∀ x : (W : Scheme.{u}), x ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback W.ι).obj L') (pullbackGlobalSections W.ι L' xpow) := by
    intro x
    have hxU : W.ι.base x ∈ W := x.2
    rw [mem_nonvanishingLocus_pullbackGlobalSections, mem_nonvanishingLocus_pullbackGlobalSections]
    change ψ.base (W.ι.base x) ∈ Stacks.Ample.nonvanishingLocus (O₁' ⊗ O₂') (tsec _ _)
    rw [@nonvanishingLocus_tsec _ _ _ iO₁ iO₂]
    exact ⟨(mem_nonvanishingLocus_pullbackGlobalSections p₁ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g' n) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection n δ₁ _ _ fun h =>
            (hW' hxU).1 (Ideal.IsPrime.mem_of_pow_mem (ProjectiveSpectrum.isPrime _) _ h))),
      (mem_nonvanishingLocus_pullbackGlobalSections p₂ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g' n) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection n δ₂ _ _ fun h =>
            (hW' hxU).2 (Ideal.IsPrime.mem_of_pow_mem (ProjectiveSpectrum.isPrime _) _ h)))⟩
  have hone_nv : ∀ x : (W : Scheme.{u}), x ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback W.ι).obj Z) (pullbackGlobalSections W.ι Z one) := by
    intro x
    refine (mem_nonvanishingLocus_pullbackGlobalSections W.ι _ _ _).mpr
      ((mem_nonvanishingLocus_pullbackGlobalSections φ _ _ _).mpr
        ((mem_nonvanishingLocus_pullbackGlobalSections (g' m) _ _ _).mpr
          (mem_nonvanishingLocus_degreeSection m 0 _ _ ?_)))
    change _ ∈ ProjectiveSpectrum.basicOpen _ 1
    rw [ProjectiveSpectrum.basicOpen_one]
    trivial
  have hB : Stacks.NonvanishingLocusRestrict.restrictSection W (L' ⊗ Z)
      (lmul W L' Z xX (resTop Z W one)) =
      Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso W.ι L' Z).inv ⊤
        (lmul ⊤ _ _ (pullbackGlobalSections W.ι L' xpow) (pullbackGlobalSections W.ι Z one)) := by
    rw [← restrictSection_top W L' xpow, ← restrictSection_top W Z one, restrictSection_lmul]
    exact (modules_iso_inv_hom_app _ _ _).symm
  have hG_nv : ∀ x : (W : Scheme.{u}), x ∈ Stacks.Ample.nonvanishingLocus _
      (Stacks.NonvanishingLocusRestrict.restrictSection W (L' ⊗ Z)
        (lmul W L' Z xX (resTop Z W one))) := fun x => by
    rw [hB]
    exact mem_nonvanishingLocus_inv_lmul W.ι (hxpow_nv x) (hone_nv x)
  have hinj : Function.Injective fun r : Γ(X, W) => r • lmul W L' Z xX (resTop Z W one) := by
    intro r r' h
    have h' := congrArg (Stacks.NonvanishingLocusRestrict.restrictSection W (L' ⊗ Z)) h
    simp only at h'
    rw [restrictSection_smul, restrictSection_smul] at h'
    have := congrArg W.topIso.hom (smul_left_injective_of_forall_mem_nonvanishingLocus _
      hG_nv h')
    rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at this
  let eW : Γ(L' ⊗ M', W) := (L' ⊗ M').presheaf.map (homOfLE hWU).op e
  let σW : Γ(X, W) := X.presheaf.map (homOfLE hWU).op σ
  have hs : resTop (L' ⊗ M') W s = σW • eW := by
    have h := congrArg ((vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE hWU).op) hσ
    rw [Scheme.Modules.map_smul, modules_map_map _ _ _ (homOfLE (le_top : W ≤ ⊤)).op] at h
    exact h.symm
  obtain ⟨v, hv⟩ : ∃ v : Γ(X, W), ((α_ L' M' N).hom ≫ L' ◁ μ).app W
      (lmul W (L' ⊗ M') N eW (resTop N W (y i))) = v • lmul W L' Z xX (resTop Z W one) := by
    obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_forall_mem_nonvanishingLocus _ hG_nv
      (Stacks.NonvanishingLocusRestrict.restrictSection W (L' ⊗ Z)
        (((α_ L' M' N).hom ≫ L' ◁ μ).app W (lmul W (L' ⊗ M') N eW (resTop N W (y i)))))
    refine ⟨W.topIso.hom g₀, restrictSection_injective W (L' ⊗ Z) ?_⟩
    rw [restrictSection_smul, Iso.hom_inv_id_apply]
    exact hg₀.symm
  exact ⟨v, (mul_eq_of_tensorSec_eq W μ s (y i) (restrict (F i)) one xX eW σW v _ hs hv hR
    (hrep i) hinj).symm⟩

end Sections

end Faltings.BombieriRoth.VanishingTransfer
