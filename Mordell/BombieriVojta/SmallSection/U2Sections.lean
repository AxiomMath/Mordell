module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.SmallSection.U2
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import Mordell.BombieriVojta.Representative.NeZero
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule
-- not re-exported: its chart lemmas share names with private helpers of `DimensionOfU2CapU1`
import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.BombieriVojta.SmallSection.DimU0
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism

/-!
# `U₂` is the space of global sections of `𝒪(V)`

In Section 8 of Bombieri's proof of the Mordell conjecture, `C` is a curve over a number field `k`,
`ψ = φ_{NP} × φ_{NP} : C × C → ℙⁿ × ℙⁿ` has coordinates `(x, x')`, `φ_B : C × C → ℙᵐ` has
coordinates `y`, and `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. In `k(C × C)` write
`η_i = y_i / y_0 = P_i / Q_i`. The space `U₂ ⊆ k(C × C)^{m+1}` of tuples `(F_i(ξ, ξ'))_i`, for
forms `F_i` of bidegree `(δ₁, δ₂)` over `k`, solving the basic system
`(P_i Q_j)^d u_j = (P_j Q_i)^d u_i`, is isomorphic as a `k`-vector space to
`H⁰(C × C, 𝒪(V))`, provided every global section of `ψ^*𝒪(δ₁, δ₂)` over `k` is the restriction of
a form of bidegree `(δ₁, δ₂)` over `k` (which holds for `δ₁, δ₂ ≥ δ₀`).

The isomorphism sends the tuple `(F_i(ξ, ξ'))_i` to the unique global section `s` of which
`(F_i)_i` is a representative: by the basic system (`Faltings.exists_isVojtaRepresentative_iff`)
such an `s` exists, and it depends only on the tuple. Conversely every global section has a
representative with coefficients in `k`, whose tuple lies in `U₂`.

## Main results

* `Faltings.exists_linearEquiv_affineEvaluationTuplesBasicSystem`: there is a `k`-linear
  isomorphism from `U₂` (`Faltings.BombieriVojta.affineEvaluationTuplesBasicSystem`) to the global
  sections of `Faltings.vojtaLineBundle`, sending the tuple of values of a family of forms to the
  section that family represents (`Faltings.IsVojtaRepresentative`).

## Implementation notes

* The setting is that of `Faltings.exists_isVojtaRepresentative_iff`: `C × C` is the fibre
  product `pullback f f` over `Spec k`, `ψ = pullback.map _ _ _ _ φNP φNP (𝟙 _) _ _`, the
  coordinates `x_ν` and `η_i` are the pullbacks of `T_ν / T_0` along `φNP` and `φB`, and the
  integer `δ₀` enters only through its defining property at `(δ₁, δ₂)`.
* `H⁰(C × C, 𝒪(V))` is `Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)`, a `Γ(C × C, ⊤)`-module, made a
  `k`-vector space by restriction of scalars along `k ≅ Γ(Spec k, ⊤) ⟶ Γ(C × C, ⊤)`.
* The isomorphism is pinned by its values: whenever the tuple `(F_i(ξ, ξ'))_i` of a family of
  forms over `k` lies in `U₂`, the family represents the image of the tuple. Since every element
  of `U₂` is such a tuple and a representative determines its section, this characterises it.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 630–631
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Faltings

universe u

section Linearity

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

/-- The product of two global sections is multiplication on the right by the second. -/
private theorem prodSection_eq_mulRight_app {X : Scheme.{u}} {F G : X.Modules} (s : Γ(F, ⊤))
    (t : Γ(G, ⊤)) :
    Stacks.ProductFamilyTwist.prodSection s t =
      (Stacks.TensorSectionNonvanishing.mulRight F
        (Stacks.ProductFamilyTwist.unitOfSection G t)).app ⊤ s := by
  rw [Stacks.ProductFamilyTwist.prodSection, Stacks.TensorSectionNonvanishing.unitMul,
    Stacks.SectionProduct.globalSection_comp, Stacks.ProductFamilyTwist.globalSection_unitOfSection]

/-- Reading a product of sections as a morphism, composing, and reading back is multiplication
followed by the morphism. -/
private theorem globalSection_symm_prodSection_comp {X : Scheme.{u}} {F G T : X.Modules}
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) (c : F ⊗ G ⟶ T) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X T
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection s t) ≫ c) =
      (Stacks.TensorSectionNonvanishing.mulRight F
        (Stacks.ProductFamilyTwist.unitOfSection G t) ≫ c).app ⊤ s := by
  change Stacks.SectionProduct.globalSection X T (_ ≫ c) = _
  rw [Stacks.SectionProduct.globalSection_comp]
  change c.app ⊤ (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm _)) = _
  rw [AddEquiv.apply_symm_apply, prodSection_eq_mulRight_app]
  rfl

/-- The restriction of forms is linear over the coefficients, which act through `X ⟶ S`. -/
private theorem vojtaFormRestriction_C_mul {S X : Scheme.{u}} {n : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (δ₁ δ₂ : ℕ) (a : Γ(S, ⊤)) (F : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)) :
    vojtaFormRestriction ψ δ₁ δ₂ (MvPolynomial.C a * F) =
      (ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop a •
        vojtaFormRestriction ψ δ₁ δ₂ F := by
  induction F using MvPolynomial.induction_on' with
  | monomial α b =>
    rw [MvPolynomial.C_mul_monomial]
    unfold vojtaFormRestriction
    dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    erw [Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single]
    exact (congrArg (· • _) (map_mul _ a b)).trans (mul_smul _ _ _)
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, smul_add]

/-- The identity `F|_X = s · y^d` of a representative is additive in the pair `(s, F|_X)`. -/
private theorem prodSection_comp_eq_add {X : Scheme.{u}} {A B L Z : X.Modules}
    (c : A ⊗ B ⟶ L ⊗ Z) (y : Γ(B, ⊤)) (one : Γ(Z, ⊤)) {s t : Γ(A, ⊤)} {r r' r'' : Γ(L, ⊤)}
    (hs : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection s y) ≫ c) =
      Stacks.ProductFamilyTwist.prodSection r one)
    (ht : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection t y) ≫ c) =
      Stacks.ProductFamilyTwist.prodSection r' one)
    (hr : r'' = r + r') :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection (s + t) y) ≫ c) =
      Stacks.ProductFamilyTwist.prodSection r'' one := by
  rw [globalSection_symm_prodSection_comp] at hs ht ⊢
  rw [prodSection_eq_mulRight_app] at hs ht ⊢
  rw [hr, map_add, map_add, hs, ht]

/-- The identity `F|_X = s · y^d` of a representative is compatible with scalars. -/
private theorem prodSection_comp_eq_smul {X : Scheme.{u}} {A B L Z : X.Modules}
    (c : A ⊗ B ⟶ L ⊗ Z) (y : Γ(B, ⊤)) (one : Γ(Z, ⊤)) {s : Γ(A, ⊤)} {r r' : Γ(L, ⊤)}
    (a : Γ(X, ⊤))
    (hs : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection s y) ≫ c) =
      Stacks.ProductFamilyTwist.prodSection r one)
    (hr : r' = a • r) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
        ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
          (Stacks.ProductFamilyTwist.prodSection (a • s) y) ≫ c) =
      Stacks.ProductFamilyTwist.prodSection r' one := by
  rw [globalSection_symm_prodSection_comp] at hs ⊢
  rw [prodSection_eq_mulRight_app] at hs ⊢
  rw [hr, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hs]

variable {S X : Scheme.{u}} {n m : ℕ}
  {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
  {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ}

/-- Representatives add: if `F` represents `s` and `G` represents `t`, then `F + G` represents
`s + t`. -/
private theorem isVojtaRepresentative_add {s t : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F G : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hs : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (ht : IsVojtaRepresentative ψ φ δ₁ δ₂ d t G) :
    IsVojtaRepresentative ψ φ δ₁ δ₂ d (s + t) (F + G) := by
  obtain ⟨hs₁, hs₂⟩ := hs
  obtain ⟨ht₁, ht₂⟩ := ht
  exact And.intro (fun i => (hs₁ i).add (ht₁ i))
    (fun i => prodSection_comp_eq_add _ _ _ (hs₂ i) (ht₂ i) (map_add _ _ _))

/-- Representatives scale: if `F` represents `s`, then `a F` represents `a s`, the coefficient
`a` acting on sections through `X ⟶ S`. -/
private theorem isVojtaRepresentative_C_mul {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (hs : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (a : Γ(S, ⊤)) :
    IsVojtaRepresentative ψ φ δ₁ δ₂ d
      ((ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S)).appTop a • s)
      (fun i => MvPolynomial.C a * F i) := by
  obtain ⟨hs₁, hs₂⟩ := hs
  exact And.intro (fun i => (hs₁ i).C_mul a)
    (fun i => prodSection_comp_eq_smul _ _ _ _ (hs₂ i) (vojtaFormRestriction_C_mul _ _ _ _ _))

end Linearity

section Existence

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

open Stacks.SectionRingGeometric in
/-- Reading a morphism out of the monoidal unit as a global section is natural. -/
public theorem schemeGlobalSectionsAddEquiv_comp {X : Scheme.{u}} {M N : X.Modules}
    (v : (letI := Stacks.SheafInternalHom.schemeMonoidalCategory; 𝟙_ X.Modules) ⟶ M)
    (p : M ⟶ N) :
    schemeGlobalSectionsAddEquiv X N (v ≫ p) =
      p.app ⊤ (schemeGlobalSectionsAddEquiv X M v) :=
  rfl

open Stacks.SectionRingGeometric in
/-- The morphism out of the unit given by `pullbackGlobalSections f 𝒪 1` is an isomorphism. -/
public theorem isIso_symm_pullbackGlobalSections_one {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    IsIso ((schemeGlobalSectionsAddEquiv X _).symm
      (pullbackGlobalSections f (unitModule Y) (unitOne Y))) := by
  let iY : (Scheme.Modules.pullback f).obj (unitModule Y) ≅ unitModule X :=
    Scheme.Modules.pullbackUnitIso f
  have h1 := congrArg
    (fun φ : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) ⟶
        Γ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf), ⊤) =>
      φ (unitOne Y))
    (pullbackGlobalSections_eq_unit f (SheafOfModules.unit Y.ringCatSheaf))
  have hval : Scheme.Modules.Hom.app iY.hom ⊤
      (pullbackGlobalSections f (unitModule Y) (unitOne Y)) = unitOne X := by
    refine ((congrArg (fun z => Scheme.Modules.Hom.app
      (Scheme.Modules.pullbackUnitIso f).hom ⊤ z) h1).trans
      (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections f
        (unitOne Y))).trans ?_
    exact map_one (f.app ⊤).hom
  have key : (schemeGlobalSectionsAddEquiv X _).symm
      (pullbackGlobalSections f (unitModule Y) (unitOne Y)) ≫ iY.hom =
        (unitComparison X).hom := by
    apply (schemeGlobalSectionsAddEquiv X _).injective
    rw [schemeGlobalSectionsAddEquiv_comp, AddEquiv.apply_symm_apply, hval,
      schemeGlobalSectionsAddEquiv_apply, Iso.inv_hom_id]
    rfl
  have : IsIso ((schemeGlobalSectionsAddEquiv X _).symm
      (pullbackGlobalSections f (unitModule Y) (unitOne Y)) ≫ iY.hom) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ iY.hom

open Stacks.SectionRingGeometric in
/-- The pullback of a global section that trivializes a module trivializes the pullback. -/
public theorem isIso_symm_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Y.Modules) (t : Γ(N, ⊤))
    (ht : IsIso ((schemeGlobalSectionsAddEquiv Y N).symm t)) :
    IsIso ((schemeGlobalSectionsAddEquiv X _).symm (pullbackGlobalSections f N t)) := by
  let w : unitModule Y ⟶ N := (unitComparison Y).inv ≫ (schemeGlobalSectionsAddEquiv Y N).symm t
  have htw : t = w.app ⊤ (unitOne Y) := by
    conv_lhs => rw [← AddEquiv.apply_symm_apply (schemeGlobalSectionsAddEquiv Y N) t]
    rfl
  have := isIso_symm_pullbackGlobalSections_one f
  have key : (schemeGlobalSectionsAddEquiv X _).symm (pullbackGlobalSections f N t) =
      (schemeGlobalSectionsAddEquiv X _).symm
        (pullbackGlobalSections f (unitModule Y) (unitOne Y)) ≫
        (Scheme.Modules.pullback f).map w := by
    rw [AddEquiv.symm_apply_eq, schemeGlobalSectionsAddEquiv_comp, AddEquiv.apply_symm_apply,
      htw, pullbackGlobalSections_natural]
  rw [key]
  infer_instance

open Stacks.SectionRingGeometric ProjectiveSpectrum.Proj in
/-- On `Proj 𝒮`, the section `1` of `𝒪(0)` trivializes `𝒪(0)`. -/
public theorem isIso_symm_degreeSection_zero_one {S : Type u} {σ : Type*} [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] :
    letI := Stacks.SheafInternalHom.schemeMonoidalCategory
    let T : (AlgebraicGeometry.Proj 𝒮).Modules := twistingSheaf 𝒮 ((0 : ℕ) : ℤ)
    IsIso ((schemeGlobalSectionsAddEquiv (AlgebraicGeometry.Proj 𝒮) T).symm
      (degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩)) := by
  intro T
  let w := (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit 𝒮).inv
  have key : (schemeGlobalSectionsAddEquiv (AlgebraicGeometry.Proj 𝒮) T).symm
      (degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩) = (unitComparison _).hom ≫ w := by
    apply (schemeGlobalSectionsAddEquiv _ T).injective
    refine (AddEquiv.apply_symm_apply _ _).trans ?_
    refine Eq.trans ?_ (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤
      (unitOne (AlgebraicGeometry.Proj 𝒮))) (Iso.inv_hom_id_assoc (unitComparison _) w).symm)
    apply Subtype.ext
    funext x
    rw [← twistGlobalSections_one_eq_degreeSection, twistGlobalSections_one_apply]
    exact HomogeneousLocalization.val_one.symm
  rw [key]
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)

/-- If `one` trivializes `Z`, then every family of global sections of `L ⊗ Z` is the family of
products with `one` of sections in the image of a surjection onto `Γ(L, ⊤)`. -/
private theorem exists_eq_prodSection_family {X : Scheme.{u}} {ι A : Type*} {L Z : X.Modules}
    (r : A → Γ(L, ⊤)) (hr : Function.Surjective r) (one : Γ(Z, ⊤))
    (hone : IsIso ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X Z).symm one))
    (w : ι → Γ(L ⊗ Z, ⊤)) :
    ∃ F : ι → A, ∀ i, w i = Stacks.ProductFamilyTwist.prodSection (r (F i)) one := by
  have : IsIso (Stacks.TensorSectionNonvanishing.mulRight L
      (Stacks.ProductFamilyTwist.unitOfSection Z one)) := by
    unfold Stacks.TensorSectionNonvanishing.mulRight Stacks.ProductFamilyTwist.unitOfSection
    infer_instance
  have h : ∀ i, ∃ a, w i = Stacks.ProductFamilyTwist.prodSection (r a) one := fun i => by
    obtain ⟨a, ha⟩ := hr ((inv (Stacks.TensorSectionNonvanishing.mulRight L
      (Stacks.ProductFamilyTwist.unitOfSection Z one))).app ⊤ (w i))
    refine ⟨a, ?_⟩
    rw [prodSection_eq_mulRight_app, ha, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id]
    rfl
  choose F hF using h
  exact ⟨F, hF⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Sections of `𝒪(V)` have representatives**: if every global section of `ψ^*𝒪(δ₁, δ₂)` is
the restriction of a form `r a` of bidegree `(δ₁, δ₂)`, then every global section of `𝒪(V)` has a
representative whose members are forms `r a`. -/
private theorem exists_isVojtaRepresentative_of_surjective {S X : Scheme.{u}} {n m : ℕ}
    {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ} {A : Type*}
    (r : A → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hr : ∀ a, (r a).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    (hsurj : Function.Surjective fun a => vojtaFormRestriction ψ δ₁ δ₂ (r a))
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) :
    ∃ F : Fin (m + 1) → A, IsVojtaRepresentative ψ φ δ₁ δ₂ d s fun i => r (F i) := by
  simp only [IsVojtaRepresentative]
  exact Exists.imp (fun F hF => And.intro (fun i => hr (F i)) hF)
    (exists_eq_prodSection_family (fun a => vojtaFormRestriction ψ δ₁ δ₂ (r a)) hsurj _
      (isIso_symm_pullbackGlobalSections _ _ _
        (isIso_symm_pullbackGlobalSections _ _ _ (isIso_symm_degreeSection_zero_one _))) _)

end Existence

/-- A relation `R` between a submodule `p` of `M` and a module `N` which is additive,
compatible with scalars and reflects zero, and which is total on `p` and onto `N`, is the graph of
a linear equivalence `p ≃ₗ N`. -/
private theorem exists_linearEquiv_of_rel {K M N : Type*} [Ring K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (p : Submodule K M) (R : M → N → Prop)
    (hadd : ∀ {u v s t}, R u s → R v t → R (u + v) (s + t))
    (hsmul : ∀ (c : K) {u s}, R u s → R (c • u) (c • s))
    (hzero : ∀ {u s}, R u s → (s = 0 ↔ u = 0))
    (htotal : ∀ u ∈ p, ∃ s, R u s) (honto : ∀ s, ∃ u ∈ p, R u s) :
    ∃ e : p ≃ₗ[K] N, ∀ (u : p) s, R u s ↔ e u = s := by
  have huniq : ∀ {u v s t}, R u s → R v t → (s = t ↔ u = v) := fun hs ht => by
    simpa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using hzero (hadd hs (hsmul (-1) ht))
  choose E hE using fun u : p => htotal u u.2
  let l : p →ₗ[K] N :=
    { toFun := E
      map_add' := fun u v => (huniq (hE (u + v)) (hadd (hE u) (hE v))).mpr rfl
      map_smul' := fun c u => (huniq (hE (c • u)) (hsmul c (hE u))).mpr rfl }
  refine ⟨.ofBijective l ⟨fun u v h => Subtype.ext ((huniq (hE u) (hE v)).mp h), fun s => ?_⟩,
    fun u s => ⟨fun h => (huniq (hE u) h).mpr rfl, fun h => h ▸ hE u⟩⟩
  obtain ⟨u, hu, hR⟩ := honto s
  exact ⟨⟨u, hu⟩, (huniq (hE ⟨u, hu⟩) hR).mpr rfl⟩

/-- Let `C` be a smooth projective geometrically integral curve of genus `≥ 2` over a number
field `k`, with the data of `Faltings.exists_isVojtaRepresentative_iff`, and suppose that every
global section of `ψ^*𝒪(δ₁, δ₂)` is the restriction of a form of bidegree `(δ₁, δ₂)` over `k`.
Then there is a `k`-linear isomorphism `e` from
`U₂ = BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1)) P Q d`
to the global sections of `𝒪(V) = vojtaLineBundle ψ φB δ₁ δ₂ d`, such that for every family of
forms `F_0, …, F_m` of bidegree `(δ₁, δ₂)` over `k` whose tuple of values `(F_i(ξ, ξ'))_i` lies in
`U₂`, the family `(F_i)` is a representative (`IsVojtaRepresentative`) of `e (F_i(ξ, ξ'))_i`. -/
public theorem exists_linearEquiv_affineEvaluationTuplesBasicSystem_of_surjective
    (k : Type u) [Field k] [NumberField k]
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
    (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 1 ≤ d)
    (hδd₁ : d₁ + sB * d = N * δ₁) (hδd₂ : d₂ + sB * d = N * δ₂)
    (hδ₀ : Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) =>
      vojtaFormRestriction
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) δ₁ δ₂
        (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom))
    (hx₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set C).Nonempty)
    (hy₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set (pullback f f : Scheme.{u})).Nonempty)
    (Pη Qη : Fin (m + 1) → (pullback f f : Scheme.{u}).functionField) (hQη : ∀ i, Qη i ≠ 0)
    (hPη : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      haveI : Nonempty ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X 0)) := hy₀.to_subtype
      -- `η_i = T_i / T_0` pulled back along `φB`
      ∀ i, (pullback f f : Scheme.{u}).germToFunctionField _
        ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X i)
              (by simpa using MvPolynomial.isHomogeneous_X _ i)))) = Pη i / Qη i) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    haveI : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0)) := hx₀.to_subtype
    -- the coordinates `x_ν = T_ν / T_0` pulled back along `φNP`, in `k(C)`
    let x : Fin (n + 1) → C.functionField := fun ν =>
      C.germToFunctionField _
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X ν)
              (by simpa using MvPolynomial.isHomogeneous_X _ ν))))
    -- the two projections `pr₁^*, pr₂^* : k(C) → k(C × C)`
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    let ψ := pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])
    -- `H⁰(C × C, 𝒪(V))` as a `k`-vector space, via `k ≅ Γ(Spec k, ⊤) ⟶ Γ(C × C, ⊤)`
    letI : Module k Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤) := Module.compHom _
      ((pullback.fst f f ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    ∃ e : BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1))
        Pη Qη d ≃ₗ[k] Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤),
      ∀ (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) k)
        (hF : ∀ i, F i ∈ MvPolynomial.weightedHomogeneousSubmodule k
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
        (hu : (fun i => BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) ⟨F i, hF i⟩) ∈
          BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1))
            Pη Qη d),
        IsVojtaRepresentative ψ φB δ₁ δ₂ d (e ⟨_, hu⟩)
          (fun i => (F i).map (Scheme.ΓSpecIso (.of k)).inv.hom) := by
  intro x pr₁ pr₂ ψ
  classical
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  let : Module k Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤) := Module.compHom _
    ((pullback.fst f f ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  let W := MvPolynomial.weightedHomogeneousSubmodule k
    (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
      Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂)
  let ι := (Scheme.ΓSpecIso (.of k)).inv.hom
  let ev := BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂)
  let U₂ := BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1))
    Pη Qη d
  -- `F` represents `s`
  let Rep : (Fin (m + 1) → W) → Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤) → Prop := fun F s =>
    IsVojtaRepresentative ψ φB δ₁ δ₂ d s fun i => (F i).1.map ι
  -- the tuple `u` is the tuple of values of a representative of `s`
  let R : (Fin (m + 1) → (pullback f f : Scheme.{u}).functionField) →
      Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤) → Prop := fun u s =>
    ∃ F : Fin (m + 1) → W, (fun i => ev (F i)) = u ∧ Rep F s
  have hbs : ∀ F : Fin (m + 1) → W, (∃ s, Rep F s) ↔
      ∀ i j, (Pη i * Qη j) ^ d * ev (F j) = (Pη j * Qη i) ^ d * ev (F i) := fun F =>
    exists_isVojtaRepresentative_iff k f hg P hPclosed hP sB hsB N hN hn φNP hφNP φB hφB
      d₁ d₂ δ₁ δ₂ d hd₁ hd₂ hd hδd₁ hδd₂ hδ₀ hx₀ hy₀ Pη Qη hQη hPη (fun i => (F i).1)
      (fun i => (F i).2)
  have hid : (Scheme.ΓSpecIso (.of k)).hom.hom.comp ι = RingHom.id k := by
    rw [← CommRingCat.hom_comp, Iso.inv_hom_id]
    rfl
  have hzero : ∀ {F s}, Rep F s → (s = 0 ↔ ∀ i, ev (F i) = 0) := fun {F s} hF => by
    have h : s ≠ 0 ↔ ∃ i, ev ⟨((F i).1.map ι).map (Scheme.ΓSpecIso (.of k)).hom.hom,
        by rw [MvPolynomial.map_map, hid, MvPolynomial.map_id]; exact (F i).2⟩ ≠ 0 :=
      IsVojtaRepresentative.ne_zero_iff k f hg P hPclosed hP sB hsB N hN hn φNP hφNP φB hφB
        d₁ d₂ δ₁ δ₂ d hd₁ hd₂ hd hδd₁ hδd₂ hx₀ hy₀ hF
    simp only [MvPolynomial.map_map, hid, MvPolynomial.map_id] at h
    rw [← not_iff_not]
    exact h.trans not_forall.symm
  have hσ : ψ ≫ pullback.fst (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = pullback.fst f f ≫ f := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hφNP]
  obtain ⟨e, he⟩ := exists_linearEquiv_of_rel U₂ R
    (by
      rintro u v s t ⟨F, rfl, hF⟩ ⟨G, rfl, hG⟩
      refine ⟨F + G, funext fun i => map_add ev _ _, ?_⟩
      convert isVojtaRepresentative_add hF hG using 1
      funext i
      simp)
    (by
      rintro c u s ⟨F, rfl, hF⟩
      refine ⟨c • F, funext fun i => map_smul ev _ _, ?_⟩
      have h := isVojtaRepresentative_C_mul hF (ι c)
      rw [hσ] at h
      convert h using 1
      funext i
      simp [MvPolynomial.smul_eq_C_mul])
    (by
      rintro u s ⟨F, rfl, hF⟩
      rw [hzero hF, funext_iff]
      rfl)
    (fun u hu => by
      obtain ⟨hu₀, hu₁⟩ := Submodule.mem_inf.mp hu
      choose F hF using fun i =>
        LinearMap.mem_range.mp (Submodule.mem_pi.mp hu₀ i (Set.mem_univ i))
      obtain ⟨s, hs⟩ := (hbs F).mpr fun i j => by rw [hF, hF]; exact hu₁ i j
      exact ⟨s, F, funext hF, hs⟩)
    (fun s => by
      obtain ⟨F, hF⟩ := exists_isVojtaRepresentative_of_surjective (fun G : W => G.1.map ι)
        (fun G _ hc => ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp G.2)
          fun h => hc (by rw [MvPolynomial.coeff_map, h, map_zero])) hδ₀ s
      exact ⟨fun i => ev (F i), Submodule.mem_inf.mpr ⟨Submodule.mem_pi.mpr fun i _ =>
        LinearMap.mem_range.mpr ⟨F i, rfl⟩, (hbs F).mp ⟨s, hF⟩⟩, F, rfl, hF⟩)
  refine ⟨e, fun F hF hu => ?_⟩
  obtain ⟨s, hs⟩ := (hbs fun i => ⟨F i, hF i⟩).mpr (Submodule.mem_inf.mp hu).2
  exact ((he ⟨_, hu⟩ s).mp ⟨_, rfl, hs⟩).symm ▸ hs

/-- **`U₂` is the space of sections of `𝒪(V)`**: for `δ₁, δ₂ ≥ δ₀`, where `δ₀` is
an integer such that forms of every bidegree `(a, b)` with `a, b ≥ δ₀` restrict onto the sections
of `ψ^*𝒪(a, b)` (Notation `not_bvs_delta0`). It is
`exists_linearEquiv_affineEvaluationTuplesBasicSystem_of_surjective` at `(δ₁, δ₂)`. -/
@[faltings "lem_bvs_u2_isomorphism"]
public theorem exists_linearEquiv_affineEvaluationTuplesBasicSystem (k : Type u) [Field k]
    [NumberField k]
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
    (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 1 ≤ d)
    (hδd₁ : d₁ + sB * d = N * δ₁) (hδd₂ : d₂ + sB * d = N * δ₂)
    (δ₀ : ℕ)
    (hδ₀ : ∀ a b : ℕ, δ₀ ≤ a → δ₀ ≤ b →
      Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (a, b) =>
      vojtaFormRestriction
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) a b
        (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom))
    (hδ₀₁ : δ₀ ≤ δ₁) (hδ₀₂ : δ₀ ≤ δ₂)
    (hx₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set C).Nonempty)
    (hy₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set (pullback f f : Scheme.{u})).Nonempty)
    (Pη Qη : Fin (m + 1) → (pullback f f : Scheme.{u}).functionField) (hQη : ∀ i, Qη i ≠ 0)
    (hPη : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      haveI : Nonempty ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X 0)) := hy₀.to_subtype
      -- `η_i = T_i / T_0` pulled back along `φB`
      ∀ i, (pullback f f : Scheme.{u}).germToFunctionField _
        ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X i)
              (by simpa using MvPolynomial.isHomogeneous_X _ i)))) = Pη i / Qη i) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    haveI : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0)) := hx₀.to_subtype
    -- the coordinates `x_ν = T_ν / T_0` pulled back along `φNP`, in `k(C)`
    let x : Fin (n + 1) → C.functionField := fun ν =>
      C.germToFunctionField _
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X ν)
              (by simpa using MvPolynomial.isHomogeneous_X _ ν))))
    -- the two projections `pr₁^*, pr₂^* : k(C) → k(C × C)`
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    let ψ := pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])
    -- `H⁰(C × C, 𝒪(V))` as a `k`-vector space, via `k ≅ Γ(Spec k, ⊤) ⟶ Γ(C × C, ⊤)`
    letI : Module k Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤) := Module.compHom _
      ((pullback.fst f f ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    ∃ e : BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1))
        Pη Qη d ≃ₗ[k] Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤),
      ∀ (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) k)
        (hF : ∀ i, F i ∈ MvPolynomial.weightedHomogeneousSubmodule k
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
        (hu : (fun i => BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) ⟨F i, hF i⟩) ∈
          BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) (Fin (m + 1))
            Pη Qη d),
        IsVojtaRepresentative ψ φB δ₁ δ₂ d (e ⟨_, hu⟩)
          (fun i => (F i).map (Scheme.ΓSpecIso (.of k)).inv.hom) :=
  exists_linearEquiv_affineEvaluationTuplesBasicSystem_of_surjective k f hg P hPclosed hP sB
    hsB N hN hn φNP hφNP φB hφB d₁ d₂ δ₁ δ₂ d hd₁ hd₂ hd hδd₁ hδd₂ (hδ₀ δ₁ δ₂ hδ₀₁ hδ₀₂) hx₀ hy₀
    Pη Qη hQη hPη

end Faltings
