module
public import Mordell.BombieriVojta.Representative.ChartBase
public import Mordell.BombieriVojta.TripleFunction.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism

/-!
# The local generator `e_{ijj'}` of `𝒪(V)`

In Section 6 of Bombieri's proof of the Mordell conjecture, the rational function
`G_{ijj'} = s / e_{ijj'}` on `C × C` (`Faltings.BombieriVojta.tripleFunction`) is the quotient of
a global section `s` of `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(d)⁻¹` by the section
`e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` on the open `U_{ijj'}` where `x_j`, `x'_{j'}` and `y_i`
do not vanish. This file builds `e_{ijj'}` from the local generators `T_k ^ a` of the twisting
sheaves on the standard charts `D₊(T_k)`, which generate: multiplication by them is bijective on
the sections over every smaller open.

## Main definitions

* `Faltings.BombieriVojta.TripleGenerator.IsGen M U e`: the section `e` of `M` over `U` generates
  `M` on `U`.
* `Faltings.BombieriVojta.TripleGenerator.chartU ψ φ i j j'`: the open `U_{ijj'}`;
  `Faltings.BombieriVojta.TripleGenerator.genU ψ φ δ₁ δ₂ a i j j'`: the section
  `x_j^{δ₁} x'_{j'}^{δ₂} ⊗ y_i^a` of `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(a)` on it.

## Main results

* `Faltings.BombieriVojta.TripleGenerator.isGen_gen`,
  `Faltings.BombieriVojta.TripleGenerator.isGen_res_pb_gen`: `T_k ^ a` and its pullbacks generate.
* `Faltings.BombieriVojta.TripleGenerator.tripleFunction_eq`: `G_{ijj'}` is the germ at the
  generic point of the coordinate of `s` against `genU ψ φ δ₁ δ₂ (-d) i j j'`.

## Implementation notes

* `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S` are arbitrary, as for
  `Faltings.BombieriVojta.tripleFunction`. The twisting sheaves and charts of `ℙʳ_S` are pulled
  back from the integral model `ℙʳ_ℤ` (`Faltings.projTwist`, `Faltings.projChart`), and the local
  generator `T_k ^ a` of `𝒪(a)` is `Stacks.PicardUFD.twistChartGenerator`.
* Products of sections are `Stacks.SectionTensorFormula.tensorSection`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

namespace Faltings.BombieriVojta.TripleGenerator

universe u

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

/-- The unit of `f^* ⊣ f_*` is natural in the module. -/
public lemma pullbackUnitApp_map {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' : Y.Modules} (φ : M ⟶ M')
    {T : Y.Opens} (t : Γ(M, T)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ T) (pullbackUnitApp f t) =
      pullbackUnitApp f (φ.app T t) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ
  have := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pullback f).obj M') => ψ.app T t) h
  exact this.symm

/-- `e` generates `M` over `U`: multiplication by its restriction is bijective on the sections
over every smaller open. -/
@[expose] public def IsGen {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (e : Γ(M, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun r : Γ(X, V) => r • M.presheaf.map (homOfLE h).op e)

/-- A generator on `U` restricts to a generator on every smaller open. -/
public lemma IsGen.restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {e : Γ(M, U)}
    (he : IsGen M U e) {V : X.Opens} (hV : V ≤ U) :
    IsGen M V (M.presheaf.map (homOfLE hV).op e) := by
  intro W hW
  have h := he W (hW.trans hV)
  convert h using 3 with r
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Multiplication by a generator on `U` is bijective on the sections over `U`. -/
public lemma IsGen.bijective {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {e : Γ(M, U)}
    (he : IsGen M U e) : Function.Bijective (fun r : Γ(X, U) => r • e) := by
  convert he U le_rfl using 3 with r
  rw [show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- An isomorphism of sheaves of modules is bijective on the sections over every object. -/
public lemma bijective_hom_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.{u} R} (e : A ≅ B) (V : Cᵒᵖ) :
    Function.Bijective (e.hom.val.app V) :=
  Function.bijective_iff_has_inverse.mpr ⟨e.inv.val.app V,
    fun x => Stacks.SheafOfModules.inv_val_app_hom_val_app e V x,
    fun y => Stacks.SheafOfModules.hom_val_app_inv_val_app e V y⟩

/-- An isomorphism of modules carries generators to generators. -/
public lemma IsGen.of_iso {X : Scheme.{u}} {M N : X.Modules} (φ : M ≅ N) {U : X.Opens}
    {e : Γ(M, U)} (he : IsGen M U e) : IsGen N U (φ.hom.app U e) := by
  intro V hV
  have hnat : N.presheaf.map (homOfLE hV).op (φ.hom.app U e) =
      φ.hom.app V (M.presheaf.map (homOfLE hV).op e) :=
    (PresheafOfModules.naturality_apply φ.hom.val (homOfLE hV).op e).symm
  have hφ : Function.Bijective (φ.hom.app V) := bijective_hom_val_app φ (op V)
  convert hφ.comp (he V hV) using 1
  funext r
  rw [Function.comp_apply, hnat, Scheme.Modules.Hom.app_smul]

open Stacks.SectionTensorFormula in
/-- Multiplication by the product of two generators on `V` is bijective on the sections over
`V`. -/
public lemma IsGen.tensorSection_self {X : Scheme.{u}} {A B : X.Modules} {V : X.Opens}
    {a : Γ(A, V)} {b : Γ(B, V)} (ha : IsGen A V a) (hb : IsGen B V b) :
    Function.Bijective (fun r : Γ(X, V) => r • tensorSection A B a b) := by
  let sa : Stacks.Cohomology.Generators.GeneratorSections X.toRingedSpace A V := ⟨a, ha⟩
  let sb : Stacks.Cohomology.Generators.GeneratorSections X.toRingedSpace B V := ⟨b, hb⟩
  have h := Stacks.Cohomology.Generators.bijective_smul_toTensorSheafSection X.toRingedSpace A B V
    sa sb
  let ι := Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf
    (schemeSheafCondition X) A B
  have key : (fun r : Γ(X, V) => r • tensorSection A B a b) =
      (ι.hom.val.app (op V)) ∘ (fun r : X.presheaf.obj (op V) =>
        @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj
          (op V)) _ _ r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B
          (op V) (sa.val ⊗ₜ[X.toRingedSpace.presheaf.obj (op V)] sb.val))) := by
    funext r
    exact ((ι.hom.val.app (op V)).hom.map_smul r _).symm
  rw [key]
  exact (bijective_hom_val_app ι (op V)).comp h

open Stacks.SectionTensorFormula in
/-- The product of two generators is a generator of the tensor product. -/
public lemma IsGen.tensorSection {X : Scheme.{u}} {A B : X.Modules} {U : X.Opens}
    {a : Γ(A, U)} {b : Γ(B, U)} (ha : IsGen A U a) (hb : IsGen B U b) :
    IsGen (A ⊗ B) U (tensorSection A B a b) := by
  intro V hV
  rw [map_tensorSection]
  exact IsGen.tensorSection_self (ha.restrict hV) (hb.restrict hV)

/-- The pullback of a generator of an invertible module is a generator. -/
public lemma IsGen.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M)
    {U : Y.Opens} {e : Γ(M, U)} (he : IsGen M U e) :
    IsGen ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) (pullbackUnitApp f e) :=
  (Stacks.SheafOfModules.pullbackGenerator f M hM U ⟨e, he⟩).property

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The local generator `T_k ^ a` of `𝒪(a)` on the standard chart `D₊(T_k)` of the integral model
generates. -/
public lemma isGen_twistChartGenerator (r : ℕ) (a : ℤ) (k : Fin (r + 1)) :
    IsGen (X := AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)))
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k))
      (Stacks.PicardUFD.twistChartGenerator (ULift.{u} ℤ) a k).val :=
  (Stacks.PicardUFD.twistChartGenerator (ULift.{u} ℤ) a k).property

/-- The twisting sheaf `𝒪(a)` of the integral model is invertible. -/
public lemma isInvertible_twistingSheaf (r : ℕ) (a : ℤ) :
    Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).presheaf
      (structureSheafRing (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).toRingedSpace).property
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) a) :=
  Stacks.PicardUFD.isInvertible_twistingSheaf (ULift.{u} ℤ) (n := r) (m := a)

/-- The pullback of an invertible module is invertible. -/
public lemma isInvertible_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M) :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj M) :=
  letI : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property M := hM
  Stacks.RingedSpace.isInvertible_modulePullback f.toLRSHom.toShHom M

/-- The generator `T_k ^ a` of `𝒪(a)` on `D₊(T_k)`. -/
public noncomputable abbrev genI (r : ℕ) (a : ℤ) (k : Fin (r + 1)) :
    Γ(projTwist.{u} r a, projChart r k) :=
  (Stacks.PicardUFD.twistChartGenerator (ULift.{u} ℤ) a k).val

section Plumbing

variable {X Y : Scheme.{u}}

/-- Restricting twice is restricting once. -/
public lemma res_res' (M : Y.Modules) {T T' T'' : Y.Opens} (h : T' ≤ T) (h' : T'' ≤ T')
    (t : Γ(M, T)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op t) =
      M.presheaf.map (homOfLE (h'.trans h)).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of sections is semilinear. -/
public lemma res_smul' (M : Y.Modules) {T T' : Y.Opens} (h : T' ≤ T) (c : Γ(Y, T))
    (t : Γ(M, T)) :
    M.presheaf.map (homOfLE h).op (c • t) =
      Y.presheaf.map (homOfLE h).op c • M.presheaf.map (homOfLE h).op t :=
  Scheme.Modules.map_smul M (homOfLE h) c t

/-- The pullback of a global section, restricted to `f⁻¹ T`, is the pullback of its restriction
to `T`. -/
public lemma res_pullbackGlobalSections (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens)
    (t : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ T ≤ ⊤)).op
        (AlgebraicGeometry.pullbackGlobalSections f M t) =
      pullbackUnitApp f (M.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op t) :=
  resT_pullbackGlobalSections f M T t

/-- A morphism of modules commutes with restriction of sections. -/
public lemma hom_app_res {M N : Y.Modules} (f : M ⟶ N) {T T' : Y.Opens} (h : T' ≤ T)
    (t : Γ(M, T)) :
    f.app T' (M.presheaf.map (homOfLE h).op t) = N.presheaf.map (homOfLE h).op (f.app T t) :=
  PresheafOfModules.naturality_apply f.val (homOfLE h).op t

end Plumbing

section Setting

variable {S X : Scheme.{u}} {n m : ℕ}
  (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
  (φ : X ⟶ projectiveSpaceOver m S)

/-- The restriction of a section of an `𝒪_X`-module to a smaller open. -/
public noncomputable abbrev res {Y : Scheme.{u}} (M : Y.Modules) {T T' : Y.Opens} (h : T' ≤ T)
    (t : Γ(M, T)) : Γ(M, T') :=
  M.presheaf.map (homOfLE h).op t

/-- The comparison morphism `ℙʳ_S ⟶ ℙʳ_ℤ`. -/
public noncomputable abbrev toI (S : Scheme.{u}) (r : ℕ) :
    projectiveSpaceOver r S ⟶ AlgebraicGeometry.Proj (projGrading.{u} r) :=
  projectiveSpaceOver.toIntegralAtUniverse r S

/-- The standard chart `D₊(T_k)` of `ℙʳ_S`. -/
public noncomputable abbrev chart (S : Scheme.{u}) (r : ℕ) (k : Fin (r + 1)) :
    (projectiveSpaceOver r S).Opens :=
  toI S r ⁻¹ᵁ projChart.{u} r k

/-- The twisting sheaf `𝒪(a)` on `ℙʳ_S`. -/
public noncomputable abbrev twist (S : Scheme.{u}) (r : ℕ) (a : ℤ) :
    (projectiveSpaceOver r S).Modules :=
  (Scheme.Modules.pullback (toI S r)).obj (projTwist.{u} r a)

/-- The generator `T_k ^ a` of `𝒪(a)` on the chart `D₊(T_k)` of `ℙʳ_S`. -/
public noncomputable abbrev gen (S : Scheme.{u}) (r : ℕ) (a : ℤ) (k : Fin (r + 1)) :
    Γ(twist S r a, chart S r k) :=
  pullbackUnitApp (toI S r) (genI.{u} r a k)

/-- The open `pr₁⁻¹ D₊(T_j) ∩ pr₂⁻¹ D₊(T_{j'})` of `ℙⁿ_S ×_S ℙⁿ_S`. -/
public noncomputable abbrev chartW (S : Scheme.{u}) (n : ℕ) (j j' : Fin (n + 1)) :
    (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).Opens :=
  pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ chart S n j ⊓
    pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ chart S n j'

/-- The sheaf `pr₁^*𝒪(δ₁) ⊗ pr₂^*𝒪(δ₂)` on `ℙⁿ_S ×_S ℙⁿ_S`. -/
public noncomputable abbrev twist₂ (S : Scheme.{u}) (n : ℕ) (δ₁ δ₂ : ℤ) :
    (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).Modules :=
  (Scheme.Modules.pullback (pullback.fst (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S))).obj (twist S n δ₁) ⊗
    (Scheme.Modules.pullback (pullback.snd (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S))).obj (twist S n δ₂)

/-- The generator `x_j^{δ₁} x'_{j'}^{δ₂}` of `𝒪(δ₁, δ₂)` on `chartW`. -/
public noncomputable abbrev genW (S : Scheme.{u}) (n : ℕ) (δ₁ δ₂ : ℤ) (j j' : Fin (n + 1)) :
    Γ(twist₂ S n δ₁ δ₂, chartW S n j j') :=
  Stacks.SectionTensorFormula.tensorSection _ _
    (res _ inf_le_left (pullbackUnitApp (pullback.fst (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S)) (gen S n δ₁ j)))
    (res _ inf_le_right (pullbackUnitApp (pullback.snd (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S)) (gen S n δ₂ j')))

/-- The open `U_{ijj'}`. -/
public noncomputable abbrev chartU (i : Fin (m + 1)) (j j' : Fin (n + 1)) : X.Opens :=
  ψ ⁻¹ᵁ chartW S n j j' ⊓ φ ⁻¹ᵁ chart S m i

/-- The generator `x_j^{δ₁} x'_{j'}^{δ₂} ⊗ y_i^a` of `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(a)` on `U_{ijj'}`;
for `a = -d` it is the section `e_{ijj'}` of `𝒪(V)`. -/
public noncomputable abbrev genU (δ₁ δ₂ a : ℤ) (i : Fin (m + 1)) (j j' : Fin (n + 1)) :
    Γ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m a), chartU ψ φ i j j') :=
  Stacks.SectionTensorFormula.tensorSection _ _
    (res _ inf_le_left (pullbackUnitApp ψ (genW S n δ₁ δ₂ j j')))
    (res _ inf_le_right (pullbackUnitApp φ (gen S m a i)))

/-- `G_{ijj'}` is the germ of the coordinate of `s` against
`e_{ijj'} = genU ψ φ δ₁ δ₂ (-d) i j j'`. -/
public lemma tripleFunction_eq (δ₁ δ₂ d : ℤ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) (x : X) (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (hx : x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j'))) :
    haveI : Nonempty (chartU ψ φ i j j') := ⟨⟨x, ⟨hx.2.1, hx.2.2⟩, hx.1⟩⟩
    tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx =
      X.germToFunctionField (chartU ψ φ i j j')
        (Function.invFun (fun g : Γ(X, chartU ψ φ i j j') => g • genU ψ φ δ₁ δ₂ (-d) i j j')
          (res _ le_top s)) :=
  rfl

/-- The first projection `ℙⁿ_S ×_S ℙⁿ_S ⟶ ℙⁿ_S`. -/
public noncomputable abbrev pr₁ (S : Scheme.{u}) (n : ℕ) :
    pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⟶
      projectiveSpaceOver n S :=
  pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)

/-- The second projection `ℙⁿ_S ×_S ℙⁿ_S ⟶ ℙⁿ_S`. -/
public noncomputable abbrev pr₂ (S : Scheme.{u}) (n : ℕ) :
    pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⟶
      projectiveSpaceOver n S :=
  pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)

/-- The twisting sheaf `𝒪(a)` of `ℙʳ_S` is invertible. -/
public lemma isInvertible_twist (S : Scheme.{u}) (r : ℕ) (a : ℤ) :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceOver r S).presheaf
      (structureSheafRing (projectiveSpaceOver r S).toRingedSpace).property (twist S r a) :=
  isInvertible_pullback (toI S r) (isInvertible_twistingSheaf r a)

/-- `T_k ^ a` generates `𝒪(a)` on the chart `D₊(T_k)` of `ℙʳ_S`. -/
public lemma isGen_gen (S : Scheme.{u}) (r : ℕ) (a : ℤ) (k : Fin (r + 1)) :
    IsGen (twist S r a) (chart S r k) (gen S r a k) :=
  IsGen.pullback (toI S r) (isInvertible_twistingSheaf r a) (isGen_twistChartGenerator r a k)

/-- The pullback of `T_k ^ a` generates on every open inside the preimage of `D₊(T_k)`. -/
public lemma isGen_res_pb_gen {Z : Scheme.{u}} {r : ℕ} (f : Z ⟶ projectiveSpaceOver r S) (a : ℤ)
    (k : Fin (r + 1)) {V : Z.Opens} (hV : V ≤ f ⁻¹ᵁ chart S r k) :
    IsGen ((Scheme.Modules.pullback f).obj (twist S r a)) V
      (((Scheme.Modules.pullback f).obj (twist S r a)).presheaf.map (homOfLE hV).op
        (pullbackUnitApp f (gen S r a k))) :=
  (IsGen.pullback f (isInvertible_twist S r a) (isGen_gen S r a k)).restrict hV

end Setting

end Faltings.BombieriVojta.TripleGenerator
