module
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.TripleFunction.Basic
public import Mordell.BombieriVojta.TripleFunction.Generator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism

/-!
# The formula `G_{ijj'} = F_i(ξ_j, ξ'_{j'})`

In Section 6 of Bombieri's proof of the Mordell conjecture, `G_{ijj'} = s / e_{ijj'}` is the
rational function on `C × C` obtained by dividing a global section `s` of `𝒪(V)` by
`e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` (`Faltings.BombieriVojta.tripleFunction`). If
`F = (F_i)` is a representative of `s` (`Faltings.IsVojtaRepresentative`), so that
`F_i|_{C × C} = s · y_i^d`, then dividing by `x_j^{δ₁} x'_{j'}^{δ₂}` and using the bihomogeneity of
`F_i` of bidegree `(δ₁, δ₂)` gives `G_{ijj'} = F_i(x / x_j, x' / x'_{j'}) = F_i(ξ_j, ξ'_{j'})`.

## Main results

* `Faltings.BombieriVojta.tripleFunction_eq_eval₂`: `G_{ijj'} = F_i(ξ_j, ξ'_{j'})` in the
  function field of `X`.
* `Faltings.BombieriVojta.TripleGenerator.isGen_genU`: the section
  `e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` generates `𝒪(V)` on the open `U_{ijj'}`.

## Implementation notes

* As for `Faltings.BombieriVojta.tripleFunction`, `C × C` is an arbitrary irreducible scheme `X`
  over an arbitrary base `S`, with `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`. The integers
  `δ₁, δ₂, d` are natural numbers, as in `Faltings.IsVojtaRepresentative`.
* The affine function `ξ_{νj} = x_ν / x_j` is the function `T_ν / T_j` on the standard chart
  `D₊(T_j)` of the integral model (`AlgebraicGeometry.Proj.awayToSection`), pulled back along
  `ψ ≫ pr₁` and read in the function field by `AlgebraicGeometry.Scheme.germToFunctionField`;
  `ξ'_{νj'}` is the same along `ψ ≫ pr₂`. The point `x` lies in both inverse images, so they are
  non-empty.
* The forms have coefficients in `Γ(S, 𝒪_S)`, which map to the function field through the
  structure morphism `X ⟶ S`, as in `Faltings.IsVojtaRepresentative`. The evaluation
  `F ↦ F(ξ_j, ξ'_{j'})` is therefore `MvPolynomial.eval₂` along that ring map, at
  `Sum.inl ν ↦ ξ_{νj}` and `Sum.inr ν ↦ ξ'_{νj'}`; over a field `k` it is
  `Faltings.BombieriVojta.aevalAffineFunctions`.
* Products of sections are `Stacks.SectionTensorFormula.tensorSection`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

namespace Faltings.BombieriVojta

universe u

open TripleGenerator

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

open Stacks.SectionTensorFormula in
private lemma tensorSection_tensorHom {X : Scheme.{u}} {A A' B B' : X.Modules} (f : A ⟶ A')
    (g : B ⟶ B') {U : X.Opens} (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ⊗ₘ g).app U (tensorSection A B a b) = tensorSection A' B' (f.app U a) (g.app U b) :=
  Stacks.SheafOfModules.tensorSectionsAt_localizedTensorHom X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) f g (op U) a b

open Stacks.SectionTensorFormula in
private lemma tensorSection_associator {X : Scheme.{u}} (A B C : X.Modules) {U : X.Opens}
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (α_ A B C).hom.app U (tensorSection (A ⊗ B) C (tensorSection A B a b) c) =
      tensorSection A (B ⊗ C) a (tensorSection B C b c) := by
  have h1 := Stacks.SheafOfModules.tensorObjIsoLeft_inv_tensorSectionsAt X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B C (op U)
    (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op U) A B a b) c
  have h2 := Stacks.SheafOfModules.tensorObjIsoRight_inv_tensorSectionsAt X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B C (op U) a
    (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op U) B C b c)
  have h3 := Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomAssociator X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B C (op U) a b c
  rwa [h1, h2] at h3

private lemma sheafifyUnitIso_unitSection {X : Scheme.{u}} :
    (Stacks.SheafOfModules.sheafifyUnitIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)).hom.val.app (op ⊤)
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (𝟙_ X.Modules) (𝟙 _)) =
      (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)).obj.obj (op ⊤)) :=
  Stacks.SheafOfModules.hom_val_app_inv_val_app
    (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)) (op ⊤) _

open Stacks.SectionTensorFormula in
private lemma globalSection_tensorHom {X : Scheme.{u}} (A B : X.Modules) (a : Γ(A, ⊤))
    (b : Γ(B, ⊤)) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (A ⊗ B)
      ((λ_ (𝟙_ X.Modules)).inv ≫
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X A).symm a ⊗ₘ
          (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X B).symm b)) =
      tensorSection A B a b := by
  have h1 := Stacks.SheafOfModules.tensorSectionsAt_sheafInternalHomLeftUnitor_inv_one X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (𝟙_ X.Modules) (op ⊤) _
    sheafifyUnitIso_unitSection
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (𝟙_ X.Modules) (𝟙 _))
  set e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  have hA : ((e A).symm a).app ⊤ (e (𝟙_ X.Modules) (𝟙 _)) = a := by
    have : e A (𝟙 _ ≫ (e A).symm a) = ((e A).symm a).app ⊤ (e (𝟙_ X.Modules) (𝟙 _)) := rfl
    rw [← this, Category.id_comp, AddEquiv.apply_symm_apply]
  have hB : ((e B).symm b).app ⊤ (e (𝟙_ X.Modules) (𝟙 _)) = b := by
    have : e B (𝟙 _ ≫ (e B).symm b) = ((e B).symm b).app ⊤ (e (𝟙_ X.Modules) (𝟙 _)) := rfl
    rw [← this, Category.id_comp, AddEquiv.apply_symm_apply]
  calc e (A ⊗ B) ((λ_ (𝟙_ X.Modules)).inv ≫ ((e A).symm a ⊗ₘ (e B).symm b))
      = ((e A).symm a ⊗ₘ (e B).symm b).app ⊤ ((λ_ (𝟙_ X.Modules)).inv.app ⊤
          (e (𝟙_ X.Modules) (𝟙 _))) := rfl
    _ = ((e A).symm a ⊗ₘ (e B).symm b).app ⊤ (tensorSection _ _ (e (𝟙_ X.Modules) (𝟙 _))
          (e (𝟙_ X.Modules) (𝟙 _))) := congrArg _ h1
    _ = tensorSection A B a b := by rw [tensorSection_tensorHom, hA, hB]

open Stacks.SectionTensorFormula in
private lemma tensorSection_whiskerLeft {X : Scheme.{u}} (A : X.Modules) {B B' : X.Modules}
    (g : B ⟶ B') {U : X.Opens} (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ g).app U (tensorSection A B a b) = tensorSection A B' a (g.app U b) := by
  rw [← MonoidalCategory.id_tensorHom, tensorSection_tensorHom]
  rfl

open Stacks.SectionTensorFormula in
/-- The comparison `f^*A ⊗ f^*B ≅ f^*(A ⊗ B)` carries `f^*a ⊗ f^*b` to `f^*(a ⊗ b)`. -/
private lemma pullbackTensorMonoidalIso_inv_tensorSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : Y.Modules) {U : Y.Opens} (a : Γ(A, U)) (b : Γ(B, U)) :
    Scheme.Modules.Hom.app (X := X)
      (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv (f ⁻¹ᵁ U)
      (tensorSection _ _ (pullbackUnitApp f a) (pullbackUnitApp f b)) =
        pullbackUnitApp f (tensorSection A B a b) := by
  have h1 := Stacks.SheafOfModules.hom_val_app_inv_val_app
    (Stacks.SheafOfModules.tensorObjIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
      ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)) (op (f ⁻¹ᵁ U))
    (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op (f ⁻¹ᵁ U)) _ _
      (pullbackUnitApp f a) (pullbackUnitApp f b))
  have h2 := Stacks.SectionProduct.comparison_pullbackUnit_tensorSectionsAt A B f U a b
  have h3 := Stacks.SheafOfModules.inv_val_app_hom_val_app
    ((Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).app (A, B)) (op (f ⁻¹ᵁ U))
    (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (Scheme.Modules.tensorObj A B) (op U)
        (Stacks.SheafOfModules.tensorSectionsAt Y.sheaf.obj Y.ringCatSheaf.property (op U)
          A B a b))
  have h4 := pullbackUnitApp_map f (Stacks.SheafOfModules.tensorObjIso Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv
    (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op U) A B a b)
  have e0 : ∀ (Z : Scheme.{u}) (C D : Z.Modules),
      Stacks.AmplePullbackPart1.tensorIsoTensorModules Z C D =
        Stacks.SheafOfModules.tensorObjIso Z.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Z) C D := fun _ _ _ => Iso.ext rfl
  have e1 : (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso f A B).inv =
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules X _ _).hom ≫
        (Stacks.RelativeVeryAmple.pullbackTensorModulesIso f A B).inv ≫
          (Scheme.Modules.pullback f).map
            (Stacks.AmplePullbackPart1.tensorIsoTensorModules Y A B).inv := rfl
  have h1' : (Stacks.AmplePullbackPart1.tensorIsoTensorModules X
      ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)).hom.app (f ⁻¹ᵁ U)
      (tensorSection _ _ (pullbackUnitApp f a) (pullbackUnitApp f b)) =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op (f ⁻¹ᵁ U)) _ _
        (pullbackUnitApp f a) (pullbackUnitApp f b) := h1
  have k : Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map
      (Stacks.SheafOfModules.tensorObjIso Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) A B).inv) (f ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (Stacks.RelativeVeryAmple.pullbackTensorModulesIso f A B).inv
        (f ⁻¹ᵁ U) (Scheme.Modules.Hom.app (Stacks.AmplePullbackPart1.tensorIsoTensorModules X
        ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)).hom (f ⁻¹ᵁ U)
        (tensorSection _ _ (pullbackUnitApp f a) (pullbackUnitApp f b)))) =
          pullbackUnitApp f (tensorSection A B a b) := by
    rw [h1']
    erw [← h2, h3]
    exact h4
  rw [e1, e0 Y]
  exact k

/-- The germ of `Function.invFun (· • e) s` is determined by any coefficient `h` with
`h • e = s`, provided such a coefficient exists and all of them have the same germ. -/
private lemma germ_invFun_smul_eq {X : Scheme.{u}} [IrreducibleSpace X] {M : X.Modules}
    {U : X.Opens} {_ : Nonempty U} (e s : Γ(M, U)) (y : X.functionField)
    (hex : ∃ h : Γ(X, U), h • e = s)
    (huniq : ∀ h : Γ(X, U), h • e = s → X.germToFunctionField U h = y) :
    X.germToFunctionField U (Function.invFun (fun g : Γ(X, U) => g • e) s) = y :=
  huniq _ (Function.invFun_eq hex)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The unit section of `𝒪(0)` restricts on each chart to the generator `T_k ^ 0`. -/
private lemma degreeSection_one_restrict (r : ℕ) (k : Fin (r + 1)) :
    (projTwist.{u} r ((0 : ℕ) : ℤ)).presheaf.map (homOfLE le_top).op
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) 0
        ⟨1, MvPolynomial.isHomogeneous_one _ _⟩) = genI r 0 k := by
  apply Subtype.ext
  funext x
  change (Localization.mk _ _ : Localization _) = Localization.mk _ _
  simp [Localization.mk_one]

/-- `∏ (g_ν / f) ^ α_ν · f ^ |α| = ∏ g_ν ^ α_ν` in a localization in which `f` is inverted. -/
private lemma finsuppProd_mk_mul_mk_pow {A ι : Type*} [CommRing A] {P : Submonoid A}
    (α : ι →₀ ℕ) (g : ι → A) {f : A} (hf : f ∈ P) :
    α.prod (fun ν e => (Localization.mk (g ν) ⟨f, hf⟩ : Localization P) ^ e) *
        Localization.mk (f ^ (α.sum fun _ e => e)) 1 =
      Localization.mk (α.prod fun ν e => g ν ^ e) 1 := by
  have hw : (Localization.mk 1 ⟨f, hf⟩ : Localization P) * Localization.mk f 1 = 1 := by
    rw [Localization.mk_mul, one_mul, mul_one]
    exact Localization.mk_self ⟨f, hf⟩
  have hr : ∀ ν, (Localization.mk (g ν) ⟨f, hf⟩ : Localization P) =
      Localization.mk (g ν) 1 * Localization.mk 1 ⟨f, hf⟩ := fun ν => by
    rw [Localization.mk_mul, mul_one, one_mul]
  simp_rw [hr, mul_pow]
  rw [Finsupp.prod_mul]
  have h1 : (α.prod fun _ e => (Localization.mk 1 ⟨f, hf⟩ : Localization P) ^ e) =
      (Localization.mk 1 ⟨f, hf⟩ : Localization P) ^ (α.sum fun _ e => e) := by
    rw [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  have h2 : (α.prod fun ν e => (Localization.mk (g ν) 1 : Localization P) ^ e) =
      Localization.mk (α.prod fun ν e => g ν ^ e) 1 := by
    simp_rw [Localization.mk_one_eq_algebraMap, ← map_pow]
    exact (map_finsuppProd (algebraMap A (Localization P)) _ _).symm
  rw [h1, h2, mul_assoc, Localization.mk_one_eq_algebraMap (f ^ _), map_pow,
    ← Localization.mk_one_eq_algebraMap f, ← mul_pow, hw, one_pow, mul_one]

private lemma localization_smul_mk {A : Type*} [CommRing A] {P : Submonoid A}
    (a : Localization P) (m : A) (t : P) :
    a • LocalizedModule.mk m t = ((a * Localization.mk m t : Localization P) :
      LocalizedModule P A) := by
  induction a using Localization.induction_on with
  | H p =>
    rw [LocalizedModule.mk_smul_mk, Localization.mk_mul]
    rfl

private lemma moduleScalarMap_finsuppProd {A ι σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)) (α : ι →₀ ℕ)
    (c : ι → (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op U)) (x : U) :
    ProjectiveSpectrum.Proj.moduleScalarMap 𝒜 U (α.prod fun ν e => c ν ^ e) x =
      α.prod fun ν e => (ProjectiveSpectrum.Proj.moduleScalarMap 𝒜 U (c ν) x) ^ e := by
  rw [map_finsuppProd, Finsupp.prod, Finsupp.prod, Finset.prod_apply]
  simp only [map_pow, Pi.pow_apply]

/-- On the chart `D₊(T_k)`, the section of `𝒪(d)` given by a monomial `T^α` of degree `d` is
`∏_ν (T_ν / T_k) ^ α_ν` times the generator `T_k ^ d`. -/
private lemma degreeSection_monomial_restrict (r d : ℕ) (k : Fin (r + 1))
    (α : Fin (r + 1) →₀ ℕ) (hα : α.degree = d) :
    (projTwist.{u} r (d : ℤ)).presheaf.map (homOfLE le_top).op
      (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) d
        ⟨MvPolynomial.monomial α 1, MvPolynomial.isHomogeneous_monomial _ hα⟩) =
      (α.prod fun ν e => projRatio.{u} r k ν ^ e) • genI r d k := by
  apply Subtype.ext
  funext x
  change LocalizedModule.mk (MvPolynomial.monomial α 1) 1 =
    ((α.prod fun ν e => projRatio.{u} r k ν ^ e).1 x).val •
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r) (d : ℤ)
        (le_refl (projChart.{u} r k)) x
  have hev : ((α.prod fun ν e => projRatio.{u} r k ν ^ e).1 x).val =
      α.prod fun ν e => (Localization.mk (MvPolynomial.X ν) ⟨MvPolynomial.X k, x.2⟩ :
        Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) ^ e := by
    refine (moduleScalarMap_finsuppProd (projGrading.{u} r) (projChart.{u} r k) α _ x).trans ?_
    exact Finset.prod_congr rfl fun ν _ => congrArg (· ^ α ν) (val_projRatio r k ν x)
  have htriv : Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r)
      (d : ℤ) (le_refl (projChart.{u} r k)) x = Localization.mk (MvPolynomial.X k ^ d) 1 := by
    change Localization.mk _ _ = _
    congr 1
    simp
  rw [hev, htriv]
  erw [localization_smul_mk]
  have hsum : (α.sum fun _ e => e) = d := hα
  rw [← hsum, MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  exact (finsuppProd_mk_mul_mk_pow α MvPolynomial.X x.2).symm

private lemma eqToHom_projTwist_val (r : ℕ) {a b : ℤ} (h : a = b)
    (h' : projTwist.{u} r a = projTwist r b)
    (W : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens) (t : Γ(projTwist.{u} r a, W)) :
    ((eqToHom h').app W t).1 = t.1 := by
  subst h
  rfl

open Stacks.SectionTensorFormula in
/-- The multiplication `𝒪(-d) ⊗ 𝒪(d) ⟶ 𝒪(0)` carries `T_i ^ (-d) ⊗ T_i ^ d` to `T_i ^ 0` on the
chart `D₊(T_i)` of the integral model. -/
private lemma twistMul_genI (m d : ℕ) (i : Fin (m + 1))
    (h' : projTwist.{u} m (-(d : ℤ) + d) = projTwist m 0) :
    Scheme.Modules.Hom.app
      ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (projTwist.{u} m (-(d : ℤ)))
          (projTwist m d)).hom ≫
        Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap (projGrading.{u} m)
          (-(d : ℤ)) d ≫ eqToHom h') (projChart m i)
      (tensorSection _ _ (genI m (-(d : ℤ)) i)
        ((projTwist.{u} m d).presheaf.map (homOfLE le_top).op
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} m) d
            ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩))) =
      genI m 0 i := by
  have h1 := Stacks.SheafOfModules.hom_val_app_inv_val_app
    (Stacks.SheafOfModules.tensorObjIso (AlgebraicGeometry.Proj (projGrading.{u} m)).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _)
      (projTwist.{u} m (-(d : ℤ))) (projTwist m d)) (op (projChart m i))
    (Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj (projGrading.{u} m)).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _) (op (projChart m i)) _ _
      (genI m (-(d : ℤ)) i)
      ((projTwist.{u} m d).presheaf.map (homOfLE le_top).op
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} m) d
            ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)))
  set yI := (projTwist.{u} m d).presheaf.map (homOfLE le_top).op
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} m) d
            ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩) with hyI
  have h1' : Scheme.Modules.Hom.app (Stacks.AmplePullbackPart1.tensorIsoTensorModules _
      (projTwist.{u} m (-(d : ℤ))) (projTwist m d)).hom (projChart m i)
      (tensorSection _ _ (genI m (-(d : ℤ)) i) yI) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (AlgebraicGeometry.Proj (projGrading.{u} m)).toRingedSpace
        (projTwist m (-(d : ℤ))) (projTwist m d) (op (projChart m i))
        (genI m (-(d : ℤ)) i ⊗ₜ yI) := h1
  apply Subtype.ext
  funext x
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h1']
  erw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  refine (congrFun (eqToHom_projTwist_val m (neg_add_cancel (d : ℤ)) h' _ _) x).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul (projGrading.{u} m)
    (-(d : ℤ)) d (projChart m i) (genI m (-(d : ℤ)) i) yI x).trans ?_
  change (Localization.mk _ _ : Localization _) * (Localization.mk (MvPolynomial.X i ^ d) 1 :
    Localization _) = Localization.mk _ _
  rw [Localization.mk_mul]
  simp only [neg_neg, Int.toNat_natCast, Int.toNat_zero, neg_zero, pow_zero, one_mul, mul_one,
    Int.toNat_neg_natCast]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

private lemma finsuppProd_sumElim {ι R : Type*} [Finite ι] [CommMonoid R] (α : (ι ⊕ ι) →₀ ℕ)
    (f g : ι → R) :
    α.prod (fun v e => Sum.elim f g v ^ e) =
      (α.comapDomain Sum.inl Sum.inl_injective.injOn).prod (fun ν e => f ν ^ e) *
        (α.comapDomain Sum.inr Sum.inr_injective.injOn).prod (fun ν e => g ν ^ e) := by
  classical
  have := Fintype.ofFinite ι
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp [Finsupp.comapDomain_apply]

namespace TripleGenerator

section Setting

variable {S X : Scheme.{u}} {n m : ℕ}
  (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
  (φ : X ⟶ projectiveSpaceOver m S)

open Stacks.SectionTensorFormula in
/-- The pullback of `x_j^{δ₁} x'_{j'}^{δ₂}` generates on every open inside the preimage of
`chartW S n j j'`. -/
public lemma isGen_res_pb_genW (δ₁ δ₂ : ℤ) (j j' : Fin (n + 1)) {V : X.Opens}
    (hV : V ≤ ψ ⁻¹ᵁ chartW S n j j') :
    IsGen ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)) V
      (((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)).presheaf.map (homOfLE hV).op
        (pullbackUnitApp ψ (genW S n δ₁ δ₂ j j'))) := by
  refine IsGen.restrict ?_ hV
  have ha := isGen_res_pb_gen (pr₁ S n) δ₁ j (inf_le_left : chartW S n j j' ≤ _)
  have hb := isGen_res_pb_gen (pr₂ S n) δ₂ j' (inf_le_right : chartW S n j j' ≤ _)
  have h := IsGen.of_iso (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ψ _ _).symm
    (IsGen.tensorSection
      (IsGen.pullback ψ (isInvertible_pullback _ (isInvertible_twist S n δ₁)) ha)
      (IsGen.pullback ψ (isInvertible_pullback _ (isInvertible_twist S n δ₂)) hb))
  rw [show pullbackUnitApp ψ (genW S n δ₁ δ₂ j j') = _ from
    (pullbackTensorMonoidalIso_inv_tensorSection ψ _ _ _ _).symm]
  exact h

/-- `genU ψ φ δ₁ δ₂ a i j j'` generates `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(a)` on `U_{ijj'}`. -/
public lemma isGen_genU (δ₁ δ₂ a : ℤ) (i : Fin (m + 1)) (j j' : Fin (n + 1)) :
    IsGen _ (chartU ψ φ i j j') (genU ψ φ δ₁ δ₂ a i j j') :=
  IsGen.tensorSection (isGen_res_pb_genW ψ δ₁ δ₂ j j' inf_le_left)
    (isGen_res_pb_gen φ a i inf_le_right)

end Setting

end TripleGenerator

section Setting

variable {S X : Scheme.{u}} {n m : ℕ}
  (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
  (φ : X ⟶ projectiveSpaceOver m S)

/-- The product of two global sections, as in `Faltings.IsVojtaRepresentative`. -/
private noncomputable abbrev tensorSecG {Y : Scheme.{u}} {A B : Y.Modules} (a : Γ(A, ⊤))
    (b : Γ(B, ⊤)) : Γ(A ⊗ B, ⊤) :=
  Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _
    ((λ_ (𝟙_ Y.Modules)).inv ≫
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm a ⊗ₘ
        (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm b))

private lemma tensorSecG_eq {Y : Scheme.{u}} {A B : Y.Modules} (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    tensorSecG a b = Stacks.SectionTensorFormula.tensorSection A B a b :=
  globalSection_tensorHom A B a b

/-- The section of `𝒪(a)` on `ℙʳ_S` given by an integral form of degree `a`. -/
private noncomputable abbrev formS (S : Scheme.{u}) (r a : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a) :
    Γ(twist S r a, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (toI S r) (projTwist.{u} r a)
    (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) a p)

variable (δ₁ δ₂ d : ℕ)

/-- `y_i^d` restricted to `X`. -/
private noncomputable abbrev yS (i : Fin (m + 1)) :
    Γ((Scheme.Modules.pullback φ).obj (twist S m d), ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections φ (twist S m d)
    (formS S m d ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩)

/-- The unit section of `φ^*𝒪(0)`. -/
private noncomputable abbrev oneS : Γ((Scheme.Modules.pullback φ).obj (twist S m 0), ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections φ (twist S m 0)
    (formS S m 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩)

/-- The multiplication `φ^*𝒪(-d) ⊗ φ^*𝒪(d) ⟶ φ^*𝒪(0)`. -/
private noncomputable abbrev μS :
    (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ))) ⊗
        (Scheme.Modules.pullback φ).obj (twist S m d) ⟶
      (Scheme.Modules.pullback φ).obj (twist S m 0) :=
  (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ (twist S m (-(d : ℤ)))
      (twist S m d)).inv ≫
    (Scheme.Modules.pullback φ).map
      ((Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (toI S m) (projTwist.{u} m (-(d : ℤ)))
          (projTwist m d)).inv ≫
        (Scheme.Modules.pullback (toI S m)).map
          ((Stacks.AmplePullbackPart1.tensorIsoTensorModules _ (projTwist.{u} m (-(d : ℤ)))
              (projTwist m d)).hom ≫
            Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap (projGrading.{u} m)
              (-(d : ℤ)) d ≫
            eqToHom (congrArg (projTwist.{u} m) (neg_add_cancel (d : ℤ)))))

/-- The restriction to `X` of the monomial `x^{α₁} x'^{α₂}`, when it has bidegree `(δ₁, δ₂)`. -/
private noncomputable abbrev monoS (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) :
    Γ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂), ⊤) :=
  if h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂ then
    AlgebraicGeometry.pullbackGlobalSections ψ (twist₂ S n δ₁ δ₂) (tensorSecG
      (AlgebraicGeometry.pullbackGlobalSections (pullback.fst (projectiveSpaceOver n S ↘ S)
        (projectiveSpaceOver n S ↘ S)) (twist S n δ₁)
        (formS S n δ₁ ⟨MvPolynomial.monomial (α.comapDomain Sum.inl Sum.inl_injective.injOn) 1,
          MvPolynomial.isHomogeneous_monomial _ h.1⟩))
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (projectiveSpaceOver n S ↘ S)
        (projectiveSpaceOver n S ↘ S)) (twist S n δ₂)
        (formS S n δ₂ ⟨MvPolynomial.monomial (α.comapDomain Sum.inr Sum.inr_injective.injOn) 1,
          MvPolynomial.isHomogeneous_monomial _ h.2⟩)))
  else 0

/-- The restriction to `X` of a form of bidegree `(δ₁, δ₂)`. -/
private noncomputable abbrev restrictS (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) :
    Γ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂), ⊤) :=
  ∑ α ∈ P.support, (ψ ≫ pullback.fst (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver n S ↘ S) ≫ (projectiveSpaceOver n S ↘ S)).appTop (P.coeff α) •
    monoS ψ δ₁ δ₂ α

private lemma isVojtaRepresentative_spec {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (i : Fin (m + 1)) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
        (Scheme.Modules.pullback φ).obj (twist S m 0))
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
          (((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
            (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))) ⊗
            (Scheme.Modules.pullback φ).obj (twist S m d))).symm
          (tensorSecG (A := (Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
            (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))) s (yS φ d i)) ≫
        (α_ ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂))
          ((Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ))))
          ((Scheme.Modules.pullback φ).obj (twist S m d))).hom ≫
        ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ◁ μS φ d)) =
      tensorSecG (restrictS ψ δ₁ δ₂ (F i)) (oneS φ) :=
  ((isVojtaRepresentative_iff ψ φ δ₁ δ₂ d s F).1 hF).2 i

private lemma formS_res (r a : ℕ) (k : Fin (r + 1))
    (p : MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ) a) :
    (twist S r a).presheaf.map (homOfLE (le_top : chart S r k ≤ ⊤)).op (formS S r a p) =
      pullbackUnitApp (toI S r) ((projTwist.{u} r a).presheaf.map (homOfLE le_top).op
        (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} r) a p)) :=
  res_pullbackGlobalSections _ _ _ _

private lemma formS_monomial_res (r d : ℕ) (k : Fin (r + 1)) (β : Fin (r + 1) →₀ ℕ)
    (hβ : β.degree = d) :
    (twist S r d).presheaf.map (homOfLE (le_top : chart S r k ≤ ⊤)).op
        (formS S r d ⟨MvPolynomial.monomial β 1, MvPolynomial.isHomogeneous_monomial _ hβ⟩) =
      (toI S r).app (projChart r k) (β.prod fun ν e => projRatio.{u} r k ν ^ e) • gen S r d k := by
  refine (res_pullbackGlobalSections _ _ _ _).trans ?_
  rw [degreeSection_monomial_restrict r d k β hβ, pullbackUnitApp_smul]

private lemma formS_one_res (r : ℕ) (k : Fin (r + 1)) :
    (twist S r ((0 : ℕ) : ℤ)).presheaf.map (homOfLE (le_top : chart S r k ≤ ⊤)).op
        (formS S r 0 ⟨1, MvPolynomial.isHomogeneous_one _ _⟩) = gen S r 0 k := by
  refine (res_pullbackGlobalSections _ _ _ _).trans ?_
  rw [degreeSection_one_restrict]
  rfl

/-- The function `∏ (x_ν / x_j) ^ α_ν ∏ (x'_ν / x'_{j'}) ^ α'_ν` on `chartW S n j j'`. -/
private noncomputable abbrev coefW (S : Scheme.{u}) (n : ℕ) (j j' : Fin (n + 1))
    (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ) :
    Γ(pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S), chartW S n j j') :=
  (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
      (homOfLE inf_le_left).op ((pr₁ S n).app _ ((toI S n).app _
        ((α.comapDomain Sum.inl Sum.inl_injective.injOn).prod
          fun ν e => projRatio.{u} n j ν ^ e))) *
    (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
      (homOfLE inf_le_right).op ((pr₂ S n).app _ ((toI S n).app _
        ((α.comapDomain Sum.inr Sum.inr_injective.injOn).prod fun ν e => projRatio.{u} n j' ν ^ e)))

private lemma monoS_res (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (α : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ)
    (h : (α.comapDomain Sum.inl Sum.inl_injective.injOn).degree = δ₁ ∧
      (α.comapDomain Sum.inr Sum.inr_injective.injOn).degree = δ₂) :
    ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)).presheaf.map
        (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (monoS ψ δ₁ δ₂ α) =
      X.presheaf.map (homOfLE (inf_le_left : chartU ψ φ i j j' ≤ ψ ⁻¹ᵁ chartW S n j j')).op
          (ψ.app _ (coefW S n j j' α)) •
        ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)).presheaf.map
          (homOfLE (inf_le_left : chartU ψ φ i j j' ≤ ψ ⁻¹ᵁ chartW S n j j')).op
          (pullbackUnitApp ψ (genW S n δ₁ δ₂ j j')) := by
  rw [monoS, dite_eq_left h, tensorSecG_eq,
    ← res_res' _ (le_top : ψ ⁻¹ᵁ chartW S n j j' ≤ ⊤) inf_le_left]
  rw [res_pullbackGlobalSections, Stacks.SectionTensorFormula.map_tensorSection,
    ← res_res' _ (le_top : pr₁ S n ⁻¹ᵁ chart S n j ≤ ⊤) inf_le_left,
    ← res_res' _ (le_top : pr₂ S n ⁻¹ᵁ chart S n j' ≤ ⊤) inf_le_right,
    res_pullbackGlobalSections, res_pullbackGlobalSections,
    formS_monomial_res _ _ _ _ h.1, formS_monomial_res _ _ _ _ h.2, pullbackUnitApp_smul,
    pullbackUnitApp_smul,
    res_smul', res_smul', Stacks.SectionTensorFormula.tensorSection_smul_left,
    Stacks.SectionTensorFormula.tensorSection_smul_right, smul_smul, pullbackUnitApp_smul,
    res_smul']

/-- The structure morphism `X ⟶ S` through the first factor. -/
private noncomputable abbrev σS : X ⟶ S :=
  ψ ≫ pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ≫
    (projectiveSpaceOver n S ↘ S)

/-- The function `F(x / x_j, x' / x'_{j'})` on `U_{ijj'}`. -/
private noncomputable abbrev evalU (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) : Γ(X, chartU ψ φ i j j') :=
  ∑ α ∈ P.support, X.presheaf.map (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op
      ((σS ψ).appTop (P.coeff α)) *
    X.presheaf.map (homOfLE (inf_le_left : chartU ψ φ i j j' ≤ ψ ⁻¹ᵁ chartW S n j j')).op
      (ψ.app _ (coefW S n j j' α))

private lemma restrictS_res (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) :
    ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)).presheaf.map
        (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (restrictS ψ δ₁ δ₂ P) =
      evalU ψ φ i j j' P •
        ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂)).presheaf.map
          (homOfLE (inf_le_left : chartU ψ φ i j j' ≤ ψ ⁻¹ᵁ chartW S n j j')).op
          (pullbackUnitApp ψ (genW S n δ₁ δ₂ j j')) := by
  rw [restrictS, map_sum, evalU, Finset.sum_smul]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [res_smul', monoS_res ψ φ δ₁ δ₂ i j j' α
    (degree_comapDomain_of_weight (hP (MvPolynomial.mem_support_iff.mp hα))), smul_smul]

private lemma oneS_res (i : Fin (m + 1)) (j j' : Fin (n + 1)) :
    ((Scheme.Modules.pullback φ).obj (twist S m 0)).presheaf.map
        (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (oneS φ) =
      ((Scheme.Modules.pullback φ).obj (twist S m 0)).presheaf.map
        (homOfLE (inf_le_right : chartU ψ φ i j j' ≤ φ ⁻¹ᵁ chart S m i)).op
        (pullbackUnitApp φ (gen S m 0 i)) := by
  rw [← res_res' _ (le_top : φ ⁻¹ᵁ chart S m i ≤ ⊤) inf_le_right, res_pullbackGlobalSections]
  exact congrArg _ (congrArg (pullbackUnitApp φ) (formS_one_res m i))

open Stacks.SectionTensorFormula in
private lemma μS_app (i : Fin (m + 1)) (j j' : Fin (n + 1)) :
    (μS φ d).app (chartU ψ φ i j j')
      (tensorSection _ _
        (((Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))).presheaf.map
          (homOfLE (inf_le_right : chartU ψ φ i j j' ≤ φ ⁻¹ᵁ chart S m i)).op
          (pullbackUnitApp φ (gen S m (-(d : ℤ)) i)))
        (((Scheme.Modules.pullback φ).obj (twist S m d)).presheaf.map
          (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (yS φ d i))) =
      ((Scheme.Modules.pullback φ).obj (twist S m 0)).presheaf.map
        (homOfLE (inf_le_right : chartU ψ φ i j j' ≤ φ ⁻¹ᵁ chart S m i)).op
        (pullbackUnitApp φ (gen S m 0 i)) := by
  rw [← res_res' _ (le_top : φ ⁻¹ᵁ chart S m i ≤ ⊤) inf_le_right, res_pullbackGlobalSections,
    formS_res, ← map_tensorSection, hom_app_res]
  congr 1
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback φ).map _) (φ ⁻¹ᵁ chart S m i)
    (Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso φ
      (twist S m (-(d : ℤ))) (twist S m d)).inv (φ ⁻¹ᵁ chart S m i)
      (tensorSection _ _ (pullbackUnitApp φ (gen S m (-(d : ℤ)) i))
        (pullbackUnitApp φ (pullbackUnitApp (toI S m) _)))) = _
  rw [pullbackTensorMonoidalIso_inv_tensorSection, pullbackUnitApp_map]
  congr 1
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullback (toI S m)).map _) (chart S m i)
    (Scheme.Modules.Hom.app (Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso (toI S m)
      (projTwist.{u} m (-(d : ℤ))) (projTwist m d)).inv (chart S m i)
      (tensorSection _ _ (pullbackUnitApp (toI S m) (genI m (-(d : ℤ)) i))
        (pullbackUnitApp (toI S m) _))) = _
  rw [pullbackTensorMonoidalIso_inv_tensorSection, pullbackUnitApp_map, twistMul_genI]

open Stacks.SectionTensorFormula in
/-- Restricting `F_i|_X = s · y_i^d` to `U_{ijj'}`: if `s|_U = h · e_{ijj'}`, then
`h · (x_j^{δ₁} x'_{j'}^{δ₂} ⊗ 1) = F_i(x/x_j, x'/x'_{j'}) · (x_j^{δ₁} x'_{j'}^{δ₂} ⊗ 1)`. -/
private lemma smul_eq_evalU_smul {s : Γ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ))), ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (h : Γ(X, chartU ψ φ i j j'))
    (hh : h • genU ψ φ δ₁ δ₂ (-(d : ℤ)) i j j' =
      ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
          (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))).presheaf.map
        (homOfLE le_top).op s) :
    h • genU ψ φ δ₁ δ₂ 0 i j j' =
      evalU ψ φ i j j' (F i) • genU ψ φ δ₁ δ₂ 0 i j j' := by
  have hspec := isVojtaRepresentative_spec ψ φ δ₁ δ₂ d hF i
  have h1 : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (tensorSecG s (yS φ d i)) ≫
        (α_ _ _ _).hom ≫ (_ ◁ μS φ d)) =
      Scheme.Modules.Hom.app (_ ◁ μS φ d) ⊤ (Scheme.Modules.Hom.app
        (α_ ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂))
          ((Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ))))
          ((Scheme.Modules.pullback φ).obj (twist S m d))).hom ⊤ (tensorSecG s (yS φ d i))) := by
    change Scheme.Modules.Hom.app (_ ◁ μS φ d) ⊤ (Scheme.Modules.Hom.app
        (α_ ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂))
          ((Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ))))
          ((Scheme.Modules.pullback φ).obj (twist S m d))).hom ⊤
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (tensorSecG s (yS φ d i))))) = _
    rw [AddEquiv.apply_symm_apply]
  rw [h1] at hspec
  have hres := congrArg (fun t => (((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m 0)).presheaf.map
      (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op t)) hspec
  simp only at hres
  have eL : ((((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m d)).presheaf.map
      (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (tensorSecG s (yS φ d i))) =
      h • tensorSection ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
          (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))) _
        (genU ψ φ δ₁ δ₂ (-(d : ℤ)) i j j')
        (((Scheme.Modules.pullback φ).obj (twist S m d)).presheaf.map
          (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op (yS φ d i)) := by
    rw [tensorSecG_eq (A := (Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
          (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))) s, map_tensorSection, ← hh,
      tensorSection_smul_left]
  have eR : ((((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
      (Scheme.Modules.pullback φ).obj (twist S m 0))).presheaf.map
      (homOfLE (le_top : chartU ψ φ i j j' ≤ ⊤)).op
        (tensorSecG (restrictS ψ δ₁ δ₂ (F i)) (oneS φ))) =
      evalU ψ φ i j j' (F i) • genU ψ φ δ₁ δ₂ 0 i j j' := by
    rw [tensorSecG_eq, map_tensorSection, restrictS_res ψ φ δ₁ δ₂ i j j' (F i) (hF.1 i),
      oneS_res, tensorSection_smul_left]
  rw [← hom_app_res, ← hom_app_res, eL, eR, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_smul, genU, tensorSection_associator, tensorSection_whiskerLeft,
    μS_app] at hres
  exact hres

private lemma germ_evalU [IrreducibleSpace X] (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) [Nonempty (chartU ψ φ i j j')]
    [Nonempty ((ψ ≫ pr₁ S n) ⁻¹ᵁ chart S n j)] [Nonempty ((ψ ≫ pr₂ S n) ⁻¹ᵁ chart S n j')]
    [Nonempty (ψ ⁻¹ᵁ chartW S n j j')] [Nonempty (⊤ : X.Opens)] :
    X.germToFunctionField _ (evalU ψ φ i j j' P) =
      P.eval₂ ((σS ψ).appTop ≫ X.germToFunctionField ⊤).hom
        (Sum.elim
          (fun ν => X.germToFunctionField _
            ((ψ ≫ pr₁ S n).app _ ((toI S n).app _ (projRatio n j ν))))
          (fun ν => X.germToFunctionField _
            ((ψ ≫ pr₂ S n).app _ ((toI S n).app _ (projRatio n j' ν))))) := by
  have : Nonempty ((TopologicalSpace.Opens.map ψ.base).obj (pr₁ S n ⁻¹ᵁ chart S n j)) :=
    ‹Nonempty ((ψ ≫ pr₁ S n) ⁻¹ᵁ chart S n j)›
  have : Nonempty ((TopologicalSpace.Opens.map ψ.base).obj (pr₂ S n ⁻¹ᵁ chart S n j')) :=
    ‹Nonempty ((ψ ≫ pr₂ S n) ⁻¹ᵁ chart S n j')›
  rw [evalU, map_sum, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, germToFunctionField_resO, germToFunctionField_resO, map_mul, app_resO, app_resO,
    map_mul, germToFunctionField_resO, germToFunctionField_resO]
  congr 1
  change _ = α.prod (fun v e => Sum.elim
    (fun ν => X.germToFunctionField _
      ((ψ ≫ pr₁ S n).app _ ((toI S n).app _ (projRatio n j ν))))
    (fun ν => X.germToFunctionField _
      ((ψ ≫ pr₂ S n).app _ ((toI S n).app _ (projRatio n j' ν)))) v ^ e)
  rw [finsuppProd_sumElim]
  congr 1
  · let R := ((toI S n).app (projChart n j) ≫ (ψ ≫ pr₁ S n).app _ ≫
      X.germToFunctionField ((ψ ≫ pr₁ S n) ⁻¹ᵁ chart S n j)).hom
    change R _ = _
    rw [map_finsuppProd]
    simp only [map_pow]
    rfl
  · let R := ((toI S n).app (projChart n j') ≫ (ψ ≫ pr₂ S n).app _ ≫
      X.germToFunctionField ((ψ ≫ pr₂ S n) ⁻¹ᵁ chart S n j')).hom
    change R _ = _
    rw [map_finsuppProd]
    simp only [map_pow]
    rfl

end Setting

/-- If `F = (F_i)` is a representative of the global section `s` of
`vojtaLineBundle ψ φ δ₁ δ₂ d`, then for a triple `(i, j, j')` that is non-vanishing at `x`, the
rational function `G_{ijj'} = tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx` is `F_i(ξ_j, ξ'_{j'})`:
the form `F_i` evaluated at `x_ν ↦ ξ_{νj}` and `x'_ν ↦ ξ'_{νj'}`, where `ξ_{νj}` and `ξ'_{νj'}`
are the functions `T_ν / T_j` and `T_ν / T_{j'}` on the standard charts pulled back along
`ψ ≫ pr₁` and `ψ ≫ pr₂`, and the coefficients act through the structure morphism `X ⟶ S`. -/
@[faltings "lem_bv_triple_function_formula"]
public theorem tripleFunction_eq_eval₂ {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F)
    (x : X) (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (hx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j'))) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    -- `D₊(T_k)` on the integral model of `ℙⁿ`
    let D : Fin (n + 1) → (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).Opens := fun k =>
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)
    -- the function `T_ν / T_k` on `D₊(T_k)`
    let ratio : (k : Fin (n + 1)) → Fin (n + 1) →
        Γ(AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)), D k) :=
      fun k ν => Proj.awayToSection _ (MvPolynomial.X k)
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X _ k) 1 (MvPolynomial.X ν)
          (by simpa using MvPolynomial.isHomogeneous_X _ ν))
    let g := projectiveSpaceOver.toIntegralAtUniverse n S
    let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    haveI : Nonempty ((ψ ≫ p₁) ⁻¹ᵁ (g ⁻¹ᵁ D j)) := ⟨⟨x, hx.2.1⟩⟩
    haveI : Nonempty ((ψ ≫ p₂) ⁻¹ᵁ (g ⁻¹ᵁ D j')) := ⟨⟨x, hx.2.2⟩⟩
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    -- `ξ_{νj}` and `ξ'_{νj'}` in the function field of `X`
    let ξ : Fin (n + 1) → X.functionField := fun ν =>
      X.germToFunctionField _ ((ψ ≫ p₁).app _ (g.app _ (ratio j ν)))
    let ξ' : Fin (n + 1) → X.functionField := fun ν =>
      X.germToFunctionField _ ((ψ ≫ p₂).app _ (g.app _ (ratio j' ν)))
    -- the coefficients act through the structure morphism `X ⟶ S`
    let c : Γ(S, ⊤) →+* X.functionField :=
      ((ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)).appTop ≫ X.germToFunctionField ⊤).hom
    tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx = (F i).eval₂ c (Sum.elim ξ ξ') := by
  intro D ratio g p₁ p₂ ξ ξ' c
  have : Nonempty (chartU ψ φ i j j') := ⟨⟨x, ⟨hx.2.1, hx.2.2⟩, hx.1⟩⟩
  have : Nonempty ((ψ ≫ pr₁ S n) ⁻¹ᵁ chart S n j) := ⟨⟨x, hx.2.1⟩⟩
  have : Nonempty ((ψ ≫ pr₂ S n) ⁻¹ᵁ chart S n j') := ⟨⟨x, hx.2.2⟩⟩
  have : Nonempty (ψ ⁻¹ᵁ chartW S n j j') := ⟨⟨x, hx.2.1, hx.2.2⟩⟩
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  refine (tripleFunction_eq ψ φ δ₁ δ₂ d s x i j j' hx).trans ?_
  refine (germ_invFun_smul_eq _ _ (X.germToFunctionField _ (evalU ψ φ i j j' (F i))) ?_ ?_).trans
    (germ_evalU ψ φ i j j' (F i))
  · exact (isGen_genU ψ φ δ₁ δ₂ _ i j j').bijective.2 _
  · intro h hh
    exact congrArg _ ((isGen_genU ψ φ δ₁ δ₂ 0 i j j').bijective.1
      (smul_eq_evalU_smul ψ φ δ₁ δ₂ d hF i j j' h hh))

end Faltings.BombieriVojta
