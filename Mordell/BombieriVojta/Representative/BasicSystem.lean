module
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Representative.Chart
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackUnitModule

/-!
# The basic system

In Section 8 of Bombieri's proof of the Mordell conjecture, `C` is a curve over a number field `k`,
`ψ = φ_{NP} × φ_{NP} : C × C → ℙⁿ × ℙⁿ` has coordinates `(x, x')`, `φ_B : C × C → ℙᵐ` has
coordinates `y`, and `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. In the function field `k(C × C)` write
`ξ_ν = x_ν / x_0`, `ξ'_ν = x'_ν / x'_0` and `η_i = y_i / y_0 = P_i / Q_i` with `Q_i ≠ 0`. Then
forms `F_0, …, F_m` of bidegree `(δ₁, δ₂)` with coefficients in `k` are a representative of some
global section of `𝒪(V)` if and only if they satisfy the *basic system*
`(P_i Q_j)^d F_j(ξ, ξ') = (P_j Q_i)^d F_i(ξ, ξ')` for all `i, j`.

The proof works on the chart `U = ψ⁻¹(pr₁⁻¹ D₊(T_0) ∩ pr₂⁻¹ D₊(T_0)) ∩ φ_B⁻¹ D₊(T_0)` of the
integral scheme `C × C`, which is not empty. There a form restricts to
`F(ξ, ξ') · x_0^{δ₁} x_0'^{δ₂}` and `y_i^d` to `η_i^d · y_0^d`, so

* if `F_i = s · y_i^d`, then `F_i(ξ, ξ') = η_i^d F_0(ξ, ξ')` on `U`, because
  `x_0^{δ₁} x_0'^{δ₂} · 1` vanishes nowhere on `U`;
* if `F_i(ξ, ξ') η_j^d = F_j(ξ, ξ') η_i^d`, then `F_i · y_j^d - F_j · y_i^d` vanishes on `U`,
  hence everywhere since `C × C` is integral, and the compatible forms glue to a section.

Multiplying by `(Q_i Q_j)^d ≠ 0` turns `F_i(ξ, ξ') η_j^d = F_j(ξ, ξ') η_i^d` into the basic system.

## Main results

* `Faltings.exists_isVojtaRepresentative_iff`: the basic system characterises the families of
  forms that represent a global section of `Faltings.vojtaLineBundle`.
* `Faltings.exists_isVojtaRepresentative_iff_of_isIntegral`: on an integral `X` whose chart
  `ψ⁻¹(pr₁⁻¹ D₊(T_0) ∩ pr₂⁻¹ D₊(T_0)) ∩ φ⁻¹ D₊(T_0)` is nonempty, forms represent a section if and
  only if `F_i(ξ, ξ') η_j^d = F_j(ξ, ξ') η_i^d` in the function field;
  `Faltings.eval₂_eq_etaSec_pow_mul_of_isVojtaRepresentative` is the identity
  `F_i(ξ, ξ') = η_i^d F_k(ξ, ξ')` on any chart, for a representative.
* `Faltings.existsUnique_isVojtaRepresentative_of_compatible`,
  `Faltings.IsVojtaRepresentative.prodSection_comm`: on any `X`, forms represent a section if and
  only if `F_i|_X · y_j^d = F_j|_X · y_i^d` for all `i, j`, and the section is then unique.

## Implementation notes

* The restrictions to the charts `Faltings.chartPair ψ j₁ j₂` and `Faltings.chartOne φ k`
  (`Faltings.resT_vojtaFormRestriction`, `Faltings.resT_vojtaCoordinatePow`), with
  `Faltings.resT_prodSection_eq_smul` and `Faltings.eq_zero_of_res_eq_zero`, reduce identities
  between products of global sections to identities of functions on a chart.
* `C × C` is the fibre product `pullback f f` over `Spec k`, `ψ` is
  `pullback.map _ _ _ _ φNP φNP (𝟙 _) _ _` and `φ_B` is a morphism `pullback f f ⟶ ℙᵐ_k`. The
  forms have coefficients in `k`, and are transported to `Γ(Spec k, ⊤)` along
  `Scheme.ΓSpecIso` for `Faltings.IsVojtaRepresentative`.
* `pr₁^*, pr₂^* : k(C) →ₐ[k] k(C × C)` are `AlgebraicGeometry.functionFieldMapAlgHom` of the two
  projections, with the `k`-algebra structures `AlgebraicGeometry.stalkAlgebraOver` at the
  generic points.
* The coordinates `x_ν ∈ k(C)` are trivialised by `x_0`: `x_ν` is the rational function
  `T_ν / T_0` on `ℙⁿ`, pulled back along `φ_{NP}` (so `x_0 = 1`). Since
  `Faltings.BombieriVojta.affineEvaluation` is invariant under rescaling `x`, `F(ξ, ξ')` is
  `affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) F`. Likewise `η_i` is `T_i / T_0` on `ℙᵐ`, pulled back
  along `φ_B`. The non-vanishing of `x_0` and `y_0` (they are members of bases of the spaces of
  sections) is the non-emptiness of the charts `φ_{NP}^{-1} D₊(T_0)` and `φ_B^{-1} D₊(T_0)`.
* `P_i` and `Q_i` enter only through their values in `k(C × C)`, so they are elements of
  `k(C × C)` with `Q_i ≠ 0` and `η_i = P_i / Q_i`.
* The integer `δ₀` enters only through its defining property at `(δ₁, δ₂)`: every global section
  of `ψ^*𝒪(δ₁, δ₂)` is the restriction (`Faltings.vojtaFormRestriction`) of a form of bidegree
  `(δ₁, δ₂)` with coefficients in `k`.
* The gluing of compatible forms (in a closed monoidal abelian category, compatible morphisms out
  of the unit descend along the jointly epimorphic `y_i^d`) is carried out here for the products of
  global sections `Stacks.ProductFamilyTwist.prodSection` used by `Faltings.IsVojtaRepresentative`;
  `Faltings.existsUnique_isVojtaRepresentative` is its form with the restrictions written out.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings

universe u

open TopologicalSpace Opposite MonoidalCategory
open Stacks.ProjectiveFromSections (resT resO resM)

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

section Abstract

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Tensoring on the right with an object having a two-sided inverse is an equivalence. -/
@[expose] public noncomputable def tensorRightEquivOfIso {N M : C} (η : N ⊗ M ≅ 𝟙_ C)
    (θ : M ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  .mk (tensorRight N) (tensorRight M)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso η.symm ≪≫ tensorRightTensor N M)
    ((tensorRightTensor M N).symm ≪≫ (tensoringRight C).mapIso θ ≪≫ rightUnitorNatIso C)

/-- Whiskering on the right by an invertible object is injective on morphisms. -/
public lemma whiskerRight_injective_of_iso {N M : C} (η : N ⊗ M ≅ 𝟙_ C) (θ : M ⊗ N ≅ 𝟙_ C)
    {A B : C} : Function.Injective (fun a : A ⟶ B => a ▷ N) :=
  fun _ _ h => (tensorRightEquivOfIso η θ).fullyFaithfulFunctor.map_injective h

/-- Whiskering on the right by an invertible object is surjective on morphisms. -/
public lemma whiskerRight_surjective_of_iso {N M : C} (η : N ⊗ M ≅ 𝟙_ C) (θ : M ⊗ N ≅ 𝟙_ C)
    {A B : C} (G : A ⊗ N ⟶ B ⊗ N) : ∃ a : A ⟶ B, a ▷ N = G :=
  ⟨(tensorRightEquivOfIso η θ).fullyFaithfulFunctor.preimage G,
    (tensorRightEquivOfIso η θ).fullyFaithfulFunctor.map_preimage G⟩

/-- In a closed monoidal category, left whiskering preserves jointly epimorphic families. -/
public lemma whiskerLeft_jointly_epi [MonoidalClosed C] {ι : Type*} {N : C} (y : ι → (𝟙_ C ⟶ N))
    (hy : ∀ {T : C} (a b : N ⟶ T), (∀ i, y i ≫ a = y i ≫ b) → a = b) (K : C) {T : C}
    (a b : K ⊗ N ⟶ T) (h : ∀ i, K ◁ y i ≫ a = K ◁ y i ≫ b) : a = b := by
  apply MonoidalClosed.curry_injective
  refine hy _ _ fun i => ?_
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left, h i]

/-- A tensor product of two morphisms out of the unit, through the left factor. -/
public lemma unitor_inv_tensorHom {L N : C} (F : 𝟙_ C ⟶ L) (y : 𝟙_ C ⟶ N) :
    (λ_ (𝟙_ C)).inv ≫ (F ⊗ₘ y) = F ≫ (ρ_ L).inv ≫ L ◁ y := by
  rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, whiskerRight_id]
  simp

/-- A tensor product of two morphisms out of the unit, through the right factor. -/
public lemma unitor_inv_tensorHom' {L N : C} (F : 𝟙_ C ⟶ L) (y : 𝟙_ C ⟶ N) :
    (λ_ (𝟙_ C)).inv ≫ (F ⊗ₘ y) = y ≫ (λ_ N).inv ≫ F ▷ N := by
  rw [tensorHom_def', ← Category.assoc, ← leftUnitor_inv_naturality, Category.assoc]

/-- Compatible morphisms `F_i : 𝟙 ⟶ L` factor through jointly epimorphic `y_i : 𝟙 ⟶ N`, when `N`
is invertible. -/
public lemma exists_desc_of_compatible [Abelian C] [MonoidalClosed C] {ι : Type} [Fintype ι]
    {L N M : C} (η : N ⊗ M ≅ 𝟙_ C) (θ : M ⊗ N ≅ 𝟙_ C) (y : ι → (𝟙_ C ⟶ N))
    (hy : ∀ {T : C} (a b : N ⟶ T), (∀ i, y i ≫ a = y i ≫ b) → a = b)
    (F : ι → (𝟙_ C ⟶ L))
    (hF : ∀ i j, (λ_ _).inv ≫ (F i ⊗ₘ y j) = (λ_ _).inv ≫ (F j ⊗ₘ y i)) :
    ∃ f : N ⟶ L, ∀ i, y i ≫ f = F i := by
  have := Abelian.hasFiniteBiproducts (C := C)
  let Y : (⨁ fun _ : ι => 𝟙_ C) ⟶ N := biproduct.desc y
  have : Epi Y := ⟨fun g h hgh => hy g h fun i => by
    simpa [Y] using congrArg (biproduct.ι (fun _ : ι => 𝟙_ C) i ≫ ·) hgh⟩
  let T : (⨁ fun _ : ι => 𝟙_ C) ⟶ L := biproduct.desc F
  have hT : kernel.ι Y ≫ T = 0 := by
    set g := kernel.ι Y ≫ T
    apply whiskerRight_injective_of_iso η θ
    simp only
    refine whiskerLeft_jointly_epi y hy _ _ _ fun j => ?_
    rw [whisker_exchange, whisker_exchange, whiskerRight_id, whiskerRight_id]
    simp only [Category.assoc, zero_comp, comp_zero]
    have key : T ≫ (ρ_ L).inv ≫ L ◁ y j = Y ≫ (λ_ N).inv ≫ F j ▷ N := by
      ext i
      simp only [T, Y, biproduct.ι_desc_assoc]
      rw [← unitor_inv_tensorHom, ← unitor_inv_tensorHom', hF]
    simp only [g, Category.assoc, key, kernel.condition_assoc, zero_comp, comp_zero]
  refine ⟨Abelian.epiDesc Y T hT, fun i => ?_⟩
  calc y i ≫ Abelian.epiDesc Y T hT =
      biproduct.ι (fun _ : ι => 𝟙_ C) i ≫ Y ≫ Abelian.epiDesc Y T hT :=
        (biproduct.ι_desc_assoc y i _).symm
    _ = F i := by rw [Abelian.comp_epiDesc]; simp [T]

/-- The monoidal form of the main statement: compatible `F_i` determine a unique `s : 𝟙 ⟶ L ⊗ M`
with `s · y_i = F_i ⊗ one`. -/
public theorem existsUnique_of_compatible [Abelian C] [MonoidalClosed C] {ι : Type} [Fintype ι]
    {L M N Z : C} (μ : M ⊗ N ⟶ Z) [IsIso μ] (η : N ⊗ M ≅ 𝟙_ C) (θ : M ⊗ N ≅ 𝟙_ C)
    (y : ι → (𝟙_ C ⟶ N))
    (hy : ∀ {T : C} (a b : N ⟶ T), (∀ i, y i ≫ a = y i ≫ b) → a = b)
    (F : ι → (𝟙_ C ⟶ L)) (one : 𝟙_ C ⟶ Z)
    (hF : ∀ i j, (λ_ _).inv ≫ (F i ⊗ₘ y j) = (λ_ _).inv ≫ (F j ⊗ₘ y i)) :
    ∃! s : 𝟙_ C ⟶ L ⊗ M, ∀ i,
      (λ_ _).inv ≫ (s ⊗ₘ y i) ≫ (α_ L M N).hom ≫ L ◁ μ = (λ_ _).inv ≫ (F i ⊗ₘ one) := by
  have hrw : ∀ (s : 𝟙_ C ⟶ L ⊗ M) i, (λ_ _).inv ≫ (s ⊗ₘ y i) ≫ (α_ L M N).hom ≫ L ◁ μ =
      y i ≫ ((λ_ N).inv ≫ s ▷ N ≫ (α_ L M N).hom ≫ L ◁ μ) := fun s i => by
    rw [← Category.assoc, unitor_inv_tensorHom']
    simp
  obtain ⟨f, hf⟩ := exists_desc_of_compatible η θ y hy F hF
  obtain ⟨s, hs⟩ := whiskerRight_surjective_of_iso η θ
    ((λ_ N).hom ≫ f ≫ (ρ_ L).inv ≫ L ◁ one ≫ L ◁ inv μ ≫ (α_ L M N).inv)
  have hsG : (λ_ N).inv ≫ s ▷ N ≫ (α_ L M N).hom ≫ L ◁ μ = f ≫ (ρ_ L).inv ≫ L ◁ one := by
    rw [hs]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, IsIso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.comp_id]
  have hsi : ∀ i, (λ_ _).inv ≫ (s ⊗ₘ y i) ≫ (α_ L M N).hom ≫ L ◁ μ =
      (λ_ _).inv ≫ (F i ⊗ₘ one) := fun i => by
    rw [hrw, hsG, unitor_inv_tensorHom, ← Category.assoc, hf]
  refine ⟨s, hsi, fun s' hs' => ?_⟩
  apply whiskerRight_injective_of_iso η θ
  have h1 : (λ_ N).inv ≫ s' ▷ N ≫ (α_ L M N).hom ≫ L ◁ μ =
      (λ_ N).inv ≫ s ▷ N ≫ (α_ L M N).hom ≫ L ◁ μ := by
    refine hy _ _ fun i => ?_
    rw [← hrw, ← hrw, hs' i, hsi i]
  exact (cancel_mono ((α_ L M N).hom ≫ L ◁ μ)).mp ((cancel_epi _).mp h1)

end Abstract

section Generation

/-- A morphism of modules commutes with restriction of sections. -/
private lemma app_res {X : Scheme.{u}} {M T : X.Modules} (c : M ⟶ T) {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(M, U)) :
    c.app V (M.presheaf.map i.op x) = T.presheaf.map i.op (c.app U x) :=
  congrArg (fun f => f x) (congrArg ConcreteCategory.hom (c.mapPresheaf.naturality i.op))

/-- Global sections of an invertible module whose nonvanishing loci cover the scheme detect zero
morphisms out of it. -/
public theorem eq_zero_of_app_top_eq_zero {X : Scheme.{u}} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] {ι : Type*} (σ : ι → Γ(M, ⊤))
    (hσ : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M (σ i)) {T : X.Modules}
    (c : M ⟶ T) (hc : ∀ i, c.app ⊤ (σ i) = 0) : c = 0 := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  have hz : ∀ x : X, ∃ z, x ∈ V z := fun x => Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  choose z hxz using hz
  choose i hi using hσ
  let t : ∀ x, Stacks.SheafDescent.Trivialization X.presheaf M.val (V (z x)) :=
    fun x => (htriv (z x)).some
  let B : X → X.Opens := fun x =>
    X.basicOpen (Stacks.NonvanishingOpen.trivTop (t x) (σ (i x)))
  have hxB : ∀ x, x ∈ B x := fun x => by
    have h := Stacks.NonvanishingOpen.nonvanishingLocus_inter (t x) (σ (i x))
    have : x ∈ (Stacks.Ample.nonvanishingLocus M (σ (i x)) ∩ (V (z x) : Set X)) :=
      ⟨hi x, hxz x⟩
    rw [h] at this
    exact this
  have hBV : ∀ x, B x ≤ V (z x) := fun x => X.basicOpen_le _
  ext W u
  change c.app W u = 0
  let C : W → X.Opens := fun x => W ⊓ B x.1
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨T.presheaf, T.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) C W
    (fun x => homOfLE inf_le_left) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxB x⟩)
    _ _ fun x => ?_
  obtain ⟨x, hxW⟩ := x
  let D : X.Opens := W ⊓ B x
  let hDV : D ⟶ V (z x) := homOfLE (inf_le_right.trans (hBV x))
  let hDW : D ⟶ W := homOfLE inf_le_left
  let s₀ : Γ(M, D) := M.presheaf.map (homOfLE le_top : D ⟶ ⊤).op (σ (i x))
  let a := Stacks.NonvanishingOpen.triv (t x) hDV s₀
  have ha : a = X.presheaf.map hDV.op (Stacks.NonvanishingOpen.trivTop (t x) (σ (i x))) := by
    have : s₀ = M.presheaf.map hDV.op
        (M.presheaf.map (homOfLE (le_top : V (z x) ≤ ⊤)).op (σ (i x))) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    simp only [a, this]
    exact Stacks.NonvanishingOpen.triv_res (t x) (𝟙 _) hDV hDV _
  have hau : IsUnit a := by
    rw [ha]
    refine X.toRingedSpace.isUnit_of_isUnit_germ D _ fun y hy => ?_
    rw [TopCat.Presheaf.germ_res_apply]
    exact (X.mem_basicOpen _ y (hBV x hy.2)).mp hy.2
  let r : Γ(M, D) := M.presheaf.map hDW.op u
  have hr : r = (Stacks.NonvanishingOpen.triv (t x) hDV r * ↑hau.unit⁻¹) • s₀ := by
    refine ((t x).θ D hDV).injective ?_
    change _ = Stacks.NonvanishingOpen.triv (t x) hDV (_ • s₀)
    rw [Stacks.NonvanishingOpen.triv_smul]
    change _ = _ * a
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
    rfl
  change T.presheaf.map hDW.op (c.app W u) = T.presheaf.map hDW.op 0
  rw [map_zero, ← app_res, show M.presheaf.map hDW.op u = r from rfl, hr,
    Scheme.Modules.Hom.app_smul, app_res, hc, map_zero, smul_zero]

end Generation

section Geometric

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalClosed
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The product of two global sections, as a morphism out of the unit, is the tensor product of
the two morphisms. -/
private theorem symm_prodSection {X : Scheme.{u}} {A B : X.Modules} (a : Γ(A, ⊤))
    (b : Γ(B, ⊤)) :
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
        (Stacks.ProductFamilyTwist.prodSection a b) =
      (λ_ _).inv ≫ ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X A).symm a ⊗ₘ
        (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X B).symm b) := by
  rw [unitor_inv_tensorHom]
  exact (AddEquiv.symm_apply_eq _).mpr rfl

/-- `existsUnique_of_compatible` for global sections of `𝒪_X`-modules: if `μ : M ⊗ N ≅ Z ≅ 𝒪_X`,
the sections `y_i` of `N` detect zero morphisms out of `N`, and `R_i · y_j = R_j · y_i`, then there
is a unique global section `s` of `L ⊗ M` with `(L ◁ μ)(s · y_i) = R_i · one` for all `i`. -/
public theorem existsUnique_sections_of_compatible {X : Scheme.{u}} {ι : Type} [Finite ι]
    {L M N Z : X.Modules} (μ : M ⊗ N ⟶ Z) [IsIso μ] (eZ : Z ≅ 𝟙_ X.Modules) (y : ι → Γ(N, ⊤))
    (hy : ∀ {T : X.Modules} (c : N ⟶ T), (∀ i, Scheme.Modules.Hom.app c ⊤ (y i) = 0) → c = 0)
    (R : ι → Γ(L, ⊤)) (one : Γ(Z, ⊤))
    (hR : ∀ i j, Stacks.ProductFamilyTwist.prodSection (R i) (y j) =
      Stacks.ProductFamilyTwist.prodSection (R j) (y i)) :
    ∃! s : Γ(L ⊗ M, ⊤), ∀ i, Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (L ⊗ Z)
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm
        (Stacks.ProductFamilyTwist.prodSection s (y i)) ≫ (α_ L M N).hom ≫ (L ◁ μ)) =
      Stacks.ProductFamilyTwist.prodSection (R i) one := by
  have := Fintype.ofFinite ι
  set e := Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
  have he : ∀ {A T : X.Modules} (f : 𝟙_ X.Modules ⟶ A) (c : A ⟶ T),
      e T (f ≫ c) = Scheme.Modules.Hom.app c ⊤ (e A f) := fun f c => rfl
  have hy' : ∀ {T : X.Modules} (a b : N ⟶ T),
      (∀ i, (e N).symm (y i) ≫ a = (e N).symm (y i) ≫ b) → a = b := by
    intro T a b hab
    refine sub_eq_zero.mp (hy (a - b) fun i => ?_)
    rw [← (e N).apply_symm_apply (y i), ← he, Preadditive.comp_sub, hab i, sub_self, map_zero]
  have hF : ∀ i j, (λ_ _).inv ≫ ((e L).symm (R i) ⊗ₘ (e N).symm (y j)) =
      (λ_ _).inv ≫ ((e L).symm (R j) ⊗ₘ (e N).symm (y i)) := fun i j => by
    rw [← symm_prodSection, ← symm_prodSection, hR]
  let θ : M ⊗ N ≅ 𝟙_ X.Modules := asIso μ ≪≫ eZ
  obtain ⟨s₀, hs₀, huniq⟩ := existsUnique_of_compatible μ (β_ N M ≪≫ θ) θ
    (fun i => (e N).symm (y i)) hy' (fun i => (e L).symm (R i)) ((e Z).symm one) hF
  have key : ∀ s : Γ(L ⊗ M, ⊤), ∀ i,
      e (L ⊗ Z) ((e _).symm (Stacks.ProductFamilyTwist.prodSection s (y i)) ≫ (α_ L M N).hom ≫
          (L ◁ μ)) = Stacks.ProductFamilyTwist.prodSection (R i) one ↔
        (λ_ _).inv ≫ ((e _).symm s ⊗ₘ (e N).symm (y i)) ≫ (α_ L M N).hom ≫ L ◁ μ =
          (λ_ _).inv ≫ ((e L).symm (R i) ⊗ₘ (e Z).symm one) := fun s i => by
    rw [← (e _).apply_symm_apply (Stacks.ProductFamilyTwist.prodSection (R i) one),
      symm_prodSection, symm_prodSection]
    simp only [Category.assoc]
    exact (AddEquiv.injective _).eq_iff
  refine ⟨e _ s₀, fun i => (key _ i).mpr (by simpa using hs₀ i), fun s' hs' => ?_⟩
  rw [← (e _).apply_symm_apply s', huniq _ fun i => (key s' i).mp (hs' i)]

end Geometric

section Representative

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Compatible forms represent a section**: bihomogeneous forms of bidegree `(δ₁, δ₂)` with
`F_i|_X · y_j^d = F_j|_X · y_i^d` (products `Stacks.ProductFamilyTwist.prodSection` of
`Faltings.vojtaFormRestriction` and `Faltings.vojtaCoordinatePow`) are a representative of a
unique global section of `𝒪(V)`. This is `Faltings.existsUnique_isVojtaRepresentative` stated
with the named restrictions; the converse is `Faltings.IsVojtaRepresentative.prodSection_comm`. -/
public theorem existsUnique_isVojtaRepresentative_of_compatible {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    (hFy : ∀ i j, Stacks.ProductFamilyTwist.prodSection (vojtaFormRestriction ψ δ₁ δ₂ (F i))
        (vojtaCoordinatePow φ d j) =
      Stacks.ProductFamilyTwist.prodSection (vojtaFormRestriction ψ δ₁ δ₂ (F j))
        (vojtaCoordinatePow φ d i)) :
    ∃! s, IsVojtaRepresentative ψ φ δ₁ δ₂ d s F := by
  have hand : ∀ {α : Type u} {A : Prop} {P : α → Prop}, A → (∃! s, P s) → ∃! s, A ∧ P s :=
    fun hA ⟨s, hs, hu⟩ => ⟨s, ⟨hA, hs⟩, fun t ht => hu t ht.2⟩
  unfold IsVojtaRepresentative
  refine hand hF
    (@existsUnique_sections_of_compatible X (Fin (m + 1)) _ _ _ _ _ _ ?_ ?_ _ ?_ _ _ hFy)
  · have :=
      Stacks.AlgebraicGeometry.ProjTwistTensorPow.isIso_twistMultiplicationMap_integralModel.{u}
        m (-(d : ℤ)) d
    beta_reduce
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ this
        (Iso.isIso_hom (eqToIso (congrArg _ (neg_add_cancel (d : ℤ))))))
  · exact (Scheme.Modules.pullback φ).mapIso
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit m S) ≪≫
      Stacks.FundamentalGroup.pullbackUnitIso φ ≪≫ Stacks.Ample.unitModuleIsoTensorUnit X
  · intro T c hc
    have : Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback φ).obj
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver m S d)) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback φ _
    refine eq_zero_of_app_top_eq_zero _ (fun x => ?_) c hc
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_X_pow m d
      ((projectiveSpaceOver.toIntegralAtUniverse m S).base (φ.base x))
    refine ⟨i, mem_nonvanishingLocus_pullbackGlobalSections φ _ _
      (mem_nonvanishingLocus_pullbackGlobalSections _ _ _ ?_)⟩
    have key : (projectiveSpaceOver.toIntegralAtUniverse m S).base (φ.base x) ∈
        Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj (projGrading.{u} m))
          (projTwist.{u} m d)
          (ProjectiveSpectrum.Proj.degreeSection (projGrading.{u} m) d
            ⟨MvPolynomial.X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩) := by
      rw [Stacks.AlgebraicGeometry.ProjTwistPowers.nonvanishingLocusDegreeSection _
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.adjoin_degreeOne_integralModel m)]
      exact hi
    exact key

end Representative

/-- Restriction of global sections commutes with subtraction. -/
public theorem resT_sub {X : Scheme.{u}} {M : X.Modules} (T : X.Opens) (a b : Γ(M, ⊤)) :
    resT T (a - b) = resT T a - resT T b :=
  map_sub _ _ _

/-- The evaluation of a morphism out of the unit at the canonical generator. -/
private theorem app_top_eq_of_globalSections {X : Scheme.{u}} {A T : X.Modules} (t : Γ(A, ⊤))
    (c : A ⟶ T) (r : Γ(T, ⊤))
    (h : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X T
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X A).symm t ≫ c) = r) :
    c.app ⊤ t = r := by
  rw [← h]
  exact congrArg (c.app ⊤)
    ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X A).apply_symm_apply t).symm

/-- If a morphism of modules carries `t_i` to `r_i`, and on `U` the `t_i` are the multiples
`a_i • t_{i₀}` while the `r_i` are the multiples `b_i • r₀` of a section `r₀` that vanishes nowhere
on `U`, then `b_i = a_i b_{i₀}`. -/
private theorem eq_mul_of_app_top_eq {X : Scheme.{u}} {L₁ L₂ : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L₂] (c : L₁ ⟶ L₂) {U : X.Opens} {ι : Type*}
    (t : ι → Γ(L₁, ⊤)) (r : ι → Γ(L₂, ⊤)) (h : ∀ i, c.app ⊤ (t i) = r i) (a b : ι → Γ(X, U))
    (i₀ : ι) (r₀ : Γ(L₂, ⊤)) (ht : ∀ i, resT U (t i) = a i • resT U (t i₀))
    (hr : ∀ i, resT U (r i) = b i • resT U r₀)
    (hU : U ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L₂ r₀) (i : ι) :
    b i = a i * b i₀ := by
  have hnat : ∀ x : Γ(L₁, ⊤), resT U (c.app ⊤ x) = c.app U (resT U x) := fun x =>
    (PresheafOfModules.naturality_apply c.val (homOfLE (le_top : U ≤ ⊤)).op x).symm
  refine Stacks.ProjectiveFromSections.eq_of_smul_eq_smul r₀ hU ?_
  rw [← hr, ← h, hnat, ht, Scheme.Modules.Hom.app_smul, ← hnat, h, hr, smul_smul]

section Germs

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Germs at the generic point -/

/-- The pullback of a rational function along a dominant morphism, computed on sections. -/
public theorem functionFieldMap_germToFunctionField {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (h : Z ⟶ Y) [IsDominant h] {O : Y.Opens} [Nonempty O] [Nonempty (h ⁻¹ᵁ O)]
    (t : Γ(Y, O)) :
    functionFieldMap h (Y.germToFunctionField O t) =
      Z.germToFunctionField (h ⁻¹ᵁ O) (h.app O t) := by
  have hfeq : functionFieldMap h = (Scheme.Hom.functionFieldMap h).hom := by
    simp [Scheme.Hom.functionFieldMap, functionFieldMap, TopCat.Presheaf.stalkCongr_hom]
  rw [hfeq, Scheme.Hom.functionFieldMap_germToFunctionField h le_rfl, Scheme.Hom.app_eq_appLE]

/-- Equal morphisms pull sections back to the same rational function. -/
public theorem germToFunctionField_app_congr {X Y : Scheme.{u}} [IrreducibleSpace X]
    {h₁ h₂ : X ⟶ Y} (e : h₁ = h₂) {O : Y.Opens} (hn₁ : Nonempty (h₁ ⁻¹ᵁ O))
    (hn₂ : Nonempty (h₂ ⁻¹ᵁ O)) (t : Γ(Y, O)) :
    X.germToFunctionField (h₁ ⁻¹ᵁ O) (h := hn₁) (h₁.app O t) =
      X.germToFunctionField (h₂ ⁻¹ᵁ O) (h := hn₂) (h₂.app O t) := by
  subst e; rfl

/-- If `h' ≫ p = h ≫ φ` with `h` dominant, then pulling a section back along `h' ≫ p` gives, in
the function field, the image under `h^*` of its pullback along `φ`. -/
public theorem germToFunctionField_app_app {X Y Y' Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (h : X ⟶ Y) [IsDominant h] (φ : Y ⟶ Z) (h' : X ⟶ Y') (p : Y' ⟶ Z) (e : h' ≫ p = h ≫ φ)
    {O : Z.Opens} [hn : Nonempty (h' ⁻¹ᵁ (p ⁻¹ᵁ O))] [Nonempty (φ ⁻¹ᵁ O)] (t : Γ(Z, O)) :
    X.germToFunctionField _ (h'.app _ (p.app O t)) =
      functionFieldMap h (Y.germToFunctionField _ (φ.app O t)) := by
  obtain ⟨⟨x, hx⟩⟩ := hn
  have : Nonempty (h ⁻¹ᵁ (φ ⁻¹ᵁ O)) :=
    ⟨⟨x, show (h ≫ φ).base x ∈ O from e ▸ hx⟩⟩
  rw [functionFieldMap_germToFunctionField]
  exact germToFunctionField_app_congr e ⟨⟨x, hx⟩⟩ _ t

private theorem nonempty_of_le {X : Scheme.{u}} {U V : X.Opens} [h : Nonempty U] (hUV : U ≤ V) :
    Nonempty V :=
  let ⟨⟨x, hx⟩⟩ := h; ⟨⟨x, hUV hx⟩⟩

/-- Bihomogeneous forms with coefficients in `k` stay bihomogeneous over `Γ(Spec k, ⊤)`. -/
private theorem isWeightedHomogeneous_map {R R' ι M : Type*} [CommSemiring R] [CommSemiring R']
    [AddCommMonoid M] (φ : R →+* R') {w : ι → M} {m : M} {P : MvPolynomial ι R}
    (hP : P.IsWeightedHomogeneous w m) : (P.map φ).IsWeightedHomogeneous w m :=
  fun _ hc => hP fun h => hc (by rw [MvPolynomial.coeff_map, h, map_zero])

/-- The basic system in terms of the `η_i = P_i / Q_i`. -/
private theorem mul_div_pow_eq_iff {K : Type*} [Field K] {P₁ Q₁ P₂ Q₂ A₁ A₂ : K} (d : ℕ)
    (h₁ : Q₁ ≠ 0) (h₂ : Q₂ ≠ 0) :
    A₁ * (P₂ / Q₂) ^ d = A₂ * (P₁ / Q₁) ^ d ↔ (P₁ * Q₂) ^ d * A₂ = (P₂ * Q₁) ^ d * A₁ := by
  have h₁' := pow_ne_zero d h₁
  have h₂' := pow_ne_zero d h₂
  rw [div_pow, div_pow, mul_pow, mul_pow, mul_div_assoc', mul_div_assoc',
    div_eq_div_iff h₂' h₁']
  constructor <;> intro h <;> linear_combination (-1 : K) * h

end Germs

section Core

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.TensorSectionNonvanishing

/-- **A representative on a chart.** If `F` represents a section of `𝒪(V)`, then on
`U = ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂})) ∩ φ⁻¹ D₊(T_k)` the affine evaluations satisfy
`F_i(ξ, ξ') = η_i^d F_k(ξ, ξ')`, where `η_i = y_i / y_k`: both `F_i|_X · 1` and `s · y_i^d` are
multiples of the section `x_{j₁}^{δ₁} x'_{j₂}^{δ₂} · 1`, which vanishes nowhere on `U`. -/
public theorem eval₂_eq_etaSec_pow_mul_of_isVojtaRepresentative {S X : Scheme.{u}} {n m : ℕ}
    {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ} {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (h : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (j₁ j₂ : Fin (n + 1)) (k i : Fin (m + 1)) :
    resO (inf_le_left : chartPair ψ j₁ j₂ ⊓ chartOne φ k ≤ _) ((F i).eval₂
        (coeffMap ψ (chartPair ψ j₁ j₂)) (Sum.elim (xiFst ψ j₁ j₂) (xiSnd ψ j₁ j₂))) =
      resO (inf_le_right : chartPair ψ j₁ j₂ ⊓ chartOne φ k ≤ _) (etaSec φ k i) ^ d *
        resO (inf_le_left : chartPair ψ j₁ j₂ ⊓ chartOne φ k ≤ _) ((F k).eval₂
          (coeffMap ψ (chartPair ψ j₁ j₂)) (Sum.elim (xiFst ψ j₁ j₂) (xiSnd ψ j₁ j₂))) := by
  obtain ⟨hF, hs⟩ := h
  have key := eq_mul_of_app_top_eq _ _ _ (fun i => app_top_eq_of_globalSections _ _ _ (hs i))
    (fun i => 1 * resO inf_le_right (etaSec φ k i) ^ d)
    (fun i => resO inf_le_left ((F i).eval₂
      (coeffMap ψ (chartPair ψ j₁ j₂)) (Sum.elim (xiFst ψ j₁ j₂) (xiSnd ψ j₁ j₂))) * 1) k _
    (fun i => by
      rw [← map_pow]
      exact resT_prodSection_eq_smul (one_smul _ _).symm
        (resT_eq_smul_of_le inf_le_right (resT_vojtaCoordinatePow φ d k i)))
    (fun i => resT_prodSection_eq_smul
      (resT_eq_smul_of_le inf_le_left (resT_vojtaFormRestriction ψ δ₁ δ₂ j₁ j₂ (F i) (hF i)))
      (one_smul _ _).symm)
    (fun x hx => (Stacks.NonvanishingOpen.mem_nonvanishingOpen _ _ _ _).mpr
      (mem_nonvanishingLocus_prodSection _ _ (mem_nonvanishingLocus_baseSec ψ δ₁ δ₂ j₁ j₂ hx.1)
        (mem_nonvanishingLocus_pullbackGlobalSections φ _ _
          (mem_nonvanishingLocus_pullbackGlobalSections _ _ _
            (mem_nonvanishingLocus_degreeSection_one m _))))) i
  simpa only [mul_one, one_mul] using key

/-- **A representative is compatible**: if `F` represents a section `s` of `𝒪(V)`, then
`F_i|_X · y_j^d = F_j|_X · y_i^d` for all `i, j`, the converse of
`Faltings.existsUnique_isVojtaRepresentative_of_compatible`. Both sides are checked on the charts
`ψ⁻¹(pr₁⁻¹ D₊(T_{j₁}) ∩ pr₂⁻¹ D₊(T_{j₂})) ∩ φ⁻¹ D₊(T_k)`, which cover `X`: there both are
`F_k(ξ, ξ') η_i^d η_j^d · x_{j₁}^{δ₁} x'_{j₂}^{δ₂} y_k^d`. -/
public theorem IsVojtaRepresentative.prodSection_comm {S X : Scheme.{u}} {n m : ℕ}
    {ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : X ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℕ} {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤)}
    (h : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) (i j : Fin (m + 1)) :
    Stacks.ProductFamilyTwist.prodSection (vojtaFormRestriction ψ δ₁ δ₂ (F i))
        (vojtaCoordinatePow φ d j) =
      Stacks.ProductFamilyTwist.prodSection (vojtaFormRestriction ψ δ₁ δ₂ (F j))
        (vojtaCoordinatePow φ d i) := by
  have hcov : ∀ r (p : AlgebraicGeometry.Proj (projGrading.{u} r)), ∃ j, p ∈ projChart r j :=
    fun r p => by simpa only [pow_one] using exists_mem_basicOpen_X_pow r 1 p
  choose j₁ hj₁ using fun x : X => hcov n ((projectiveSpaceOver.toIntegralAtUniverse n S).base
    ((pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).base (ψ.base x)))
  choose j₂ hj₂ using fun x : X => hcov n ((projectiveSpaceOver.toIntegralAtUniverse n S).base
    ((pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).base (ψ.base x)))
  choose k hk using fun x : X => hcov m
    ((projectiveSpaceOver.toIntegralAtUniverse m S).base (φ.base x))
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨_, Scheme.Modules.isSheaf _⟩ : TopCat.Sheaf Ab.{u} X)
    (fun x : (⊤ : X.Opens) => chartPair ψ (j₁ x.1) (j₂ x.1) ⊓ chartOne φ (k x.1)) ⊤
    (fun _ => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨⟨x, trivial⟩, ⟨hj₁ x, hj₂ x⟩, hk x⟩) _ _ fun x => ?_
  set U := chartPair ψ (j₁ x.1) (j₂ x.1) ⊓ chartOne φ (k x.1)
  have hR : ∀ i j, resT U (Stacks.ProductFamilyTwist.prodSection
      (vojtaFormRestriction ψ δ₁ δ₂ (F i)) (vojtaCoordinatePow φ d j)) =
      (resO inf_le_left ((F i).eval₂ (coeffMap ψ (chartPair ψ (j₁ x.1) (j₂ x.1)))
          (Sum.elim (xiFst ψ (j₁ x.1) (j₂ x.1)) (xiSnd ψ (j₁ x.1) (j₂ x.1)))) *
        resO inf_le_right (etaSec φ (k x.1) j) ^ d) •
      resT U (Stacks.ProductFamilyTwist.prodSection (baseSec ψ δ₁ δ₂ (j₁ x.1) (j₂ x.1))
        (vojtaCoordinatePow φ d (k x.1))) := fun i j => by
    rw [← map_pow]
    exact resT_prodSection_eq_smul (resT_eq_smul_of_le inf_le_left
        (resT_vojtaFormRestriction ψ δ₁ δ₂ _ _ (F i) (h.1 i)))
      (resT_eq_smul_of_le inf_le_right (resT_vojtaCoordinatePow φ d _ j))
  change resT U _ = resT U _
  rw [hR, hR, eval₂_eq_etaSec_pow_mul_of_isVojtaRepresentative h _ _ (k x.1) i,
    eval₂_eq_etaSec_pow_mul_of_isVojtaRepresentative h _ _ (k x.1) j]
  congr 1
  ring

/-- **The basic system on an integral scheme.** Let `X` be integral, and let the chart
`U = ψ⁻¹(pr₁⁻¹ D₊(T_0) ∩ pr₂⁻¹ D₊(T_0)) ∩ φ⁻¹ D₊(T_0)` be nonempty. If `A_i` is the image in the
function field of `F_i(ξ, ξ')` and `η_i` that of `y_i / y_0`, then the forms `F_i` represent a
global section of `𝒪(V)` if and only if `A_i η_j^d = A_j η_i^d` for all `i, j`. -/
public theorem exists_isVojtaRepresentative_iff_of_isIntegral {S X : Scheme.{u}} [IsIntegral X]
    {n m : ℕ} (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ)
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    [Nonempty (chartPair ψ 0 0 ⊓ chartOne φ 0 : X.Opens)]
    (A η : Fin (m + 1) → X.functionField)
    (hA : ∀ i, X.germToFunctionField (chartPair ψ 0 0 ⊓ chartOne φ 0) (resO inf_le_left
      ((F i).eval₂ (coeffMap ψ (chartPair ψ 0 0)) (Sum.elim (xiFst ψ 0 0) (xiSnd ψ 0 0)))) = A i)
    (hη : ∀ i, X.germToFunctionField (chartPair ψ 0 0 ⊓ chartOne φ 0)
      (resO inf_le_right (etaSec φ 0 i)) = η i) :
    (∃ s, IsVojtaRepresentative ψ φ δ₁ δ₂ d s F) ↔ ∀ i j, A i * η j ^ d = A j * η i ^ d := by
  set U : X.Opens := chartPair ψ 0 0 ⊓ chartOne φ 0
  set ev : Fin (m + 1) → Γ(X, U) := fun i => resO inf_le_left
    ((F i).eval₂ (coeffMap ψ (chartPair ψ 0 0)) (Sum.elim (xiFst ψ 0 0) (xiSnd ψ 0 0)))
  set et : Fin (m + 1) → Γ(X, U) := fun i => resO inf_le_right (etaSec φ 0 i)
  have hinj : Function.Injective (X.germToFunctionField U).hom :=
    germ_injective_of_isIntegral X _ _
  have het : ∀ i, resO (inf_le_right : U ≤ chartOne φ 0) (etaSec φ 0 i ^ d) = et i ^ d :=
    fun i => map_pow _ _ _
  have hR : ∀ i j, resT U (Stacks.ProductFamilyTwist.prodSection
      (vojtaFormRestriction ψ δ₁ δ₂ (F i)) (vojtaCoordinatePow φ d j)) =
      (ev i * et j ^ d) • resT U (Stacks.ProductFamilyTwist.prodSection
        (baseSec ψ δ₁ δ₂ 0 0) (vojtaCoordinatePow φ d 0)) := fun i j => by
    rw [← het]
    exact resT_prodSection_eq_smul
      (resT_eq_smul_of_le inf_le_left (resT_vojtaFormRestriction ψ δ₁ δ₂ 0 0 (F i) (hF i)))
      (resT_eq_smul_of_le inf_le_right (resT_vojtaCoordinatePow φ d 0 j))
  constructor
  · rintro ⟨s, hs⟩
    have hA' : ∀ i, A i = η i ^ d * A 0 := fun i => by
      rw [← hA, ← hA, ← hη, eval₂_eq_etaSec_pow_mul_of_isVojtaRepresentative hs 0 0 0 i,
        map_mul, map_pow]
    intro i j
    rw [hA' i, hA' j]
    ring
  · intro H
    refine (existsUnique_isVojtaRepresentative_of_compatible ψ φ δ₁ δ₂ d F hF fun i j => ?_).exists
    refine sub_eq_zero.mp (eq_zero_of_res_eq_zero _ (W := U) ?_ _ ?_)
    · exact Set.nonempty_coe_sort.mp ‹_›
    · have hc : ev i * et j ^ d - ev j * et i ^ d = 0 := hinj (by
        rw [map_sub, map_zero, map_mul, map_mul, map_pow, map_pow]
        exact sub_eq_zero.mpr (by rw [hA, hA, hη, hη]; exact H i j))
      refine (resT_sub _ _ _).trans ?_
      rw [hR, hR, ← sub_smul, hc, zero_smul]

end Core

section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Let `C` be a smooth projective geometrically integral curve of genus `≥ 2` over a number
field `k`, with a divisor `P` of degree one, `φNP : C ⟶ ℙⁿ_k` (`N ≥ 2g + 1`, `n = N - g`) and
`φB : C ×_k C ⟶ ℙᵐ_k` closed immersions over `k`, and `ψ = φNP × φNP`. Let `d₁, d₂, d` be positive
integers with `dᵢ + s d = N δᵢ`, and suppose that every global section of `ψ^*𝒪(δ₁, δ₂)` is the
restriction of a form of bidegree `(δ₁, δ₂)` over `k`. In `k(C × C)` let `ξ_ν = pr₁^* x_ν`,
`ξ'_ν = pr₂^* x_ν`, where `x_ν = T_ν / T_0` pulled back along `φNP`, let `η_i = T_i / T_0` pulled
back along `φB`, and let `η_i = P_i / Q_i` with `Q_i ≠ 0`. Then forms `F_0, …, F_m` of bidegree
`(δ₁, δ₂)` over `k` are a representative (`IsVojtaRepresentative`) of a global section of
`vojtaLineBundle ψ φB δ₁ δ₂ d` if and only if `(P_i Q_j)^d F_j(ξ, ξ') = (P_j Q_i)^d F_i(ξ, ξ')`
for all `i, j`, where `F(ξ, ξ')` is `BombieriVojta.affineEvaluation`. -/
@[faltings "lem_bvs_basic_system"]
public theorem exists_isVojtaRepresentative_iff (k : Type u) [Field k] [NumberField k]
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
    [IsIntegral (pullback f f)]
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
              (by simpa using MvPolynomial.isHomogeneous_X _ i)))) = Pη i / Qη i)
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) k)
    (hF : ∀ i, F i ∈ MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) :
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
    (∃ s, IsVojtaRepresentative
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) φB δ₁ δ₂ d s
        (fun i => (F i).map (Scheme.ΓSpecIso (.of k)).inv.hom)) ↔
      ∀ i j, (Pη i * Qη j) ^ d * BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) ⟨F j, hF j⟩ =
        (Pη j * Qη i) ^ d * BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) ⟨F i, hF i⟩ := by
  intro x pr₁ pr₂
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  have : IsIntegral C := inferInstance
  set ψ := pullback.map f f (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
    (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) φNP φNP (𝟙 _)
    (by simp [hφNP]) (by simp [hφNP])
  have hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst f f ≫ φNP := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd f f ≫ φNP := pullback.lift_snd _ _ _
  have hσ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst f f ≫ f := by
    rw [← Category.assoc, hψ₁, Category.assoc, hφNP]
  set g := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  set O : C.Opens := φNP ⁻¹ᵁ (g ⁻¹ᵁ projChart n 0)
  have hmem : ∀ z : (pullback f f : Scheme.{u}), (pullback.fst f f).base z ∈ O →
      (pullback.snd f f).base z ∈ O → z ∈ chartPair ψ 0 0 := fun z h₁ h₂ => by
    refine ⟨?_, ?_⟩
    · change (ψ ≫ pullback.fst _ _).base z ∈ g ⁻¹ᵁ projChart n 0
      rw [hψ₁]
      exact h₁
    · change (ψ ≫ pullback.snd _ _).base z ∈ g ⁻¹ᵁ projChart n 0
      rw [hψ₂]
      exact h₂
  have hU : ((chartPair ψ 0 0 ⊓ chartOne φB 0 : (pullback f f : Scheme.{u}).Opens) :
      Set (pullback f f : Scheme.{u})).Nonempty := by
    obtain ⟨y₁, hy₁⟩ := (pullback.fst f f).denseRange.exists_mem_open O.isOpen hx₀
    obtain ⟨y₂, hy₂⟩ := (pullback.snd f f).denseRange.exists_mem_open O.isOpen hx₀
    obtain ⟨z, ⟨hz₁, hz₂⟩, hz₃⟩ := nonempty_preirreducible_inter
      ((pullback.fst f f ⁻¹ᵁ O) ⊓ (pullback.snd f f ⁻¹ᵁ O)).isOpen (chartOne φB 0).isOpen
      (nonempty_preirreducible_inter (pullback.fst f f ⁻¹ᵁ O).isOpen
        (pullback.snd f f ⁻¹ᵁ O).isOpen ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩) hy₀
    exact ⟨z, hmem z hz₁ hz₂, hz₃⟩
  have : Nonempty (chartPair ψ 0 0 ⊓ chartOne φB 0 : (pullback f f : Scheme.{u}).Opens) :=
    hU.to_subtype
  rw [exists_isVojtaRepresentative_iff_of_isIntegral ψ φB δ₁ δ₂ d _
    (fun i => isWeightedHomogeneous_map _
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hF i)))
    (fun i => BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) ⟨F i, hF i⟩)
    (fun i => Pη i / Qη i) ?_ ?_]
  · exact forall₂_congr fun i j => mul_div_pow_eq_iff d (hQη i) (hQη j)
  · intro i
    have : Nonempty (chartPair ψ 0 0) :=
      nonempty_of_le (U := chartPair ψ 0 0 ⊓ chartOne φB 0) inf_le_left
    have : Nonempty (⊤ : (pullback f f : Scheme.{u}).Opens) :=
      nonempty_of_le (U := chartPair ψ 0 0) le_top
    have : Nonempty O := hx₀.to_subtype
    have : Nonempty (ψ ⁻¹ᵁ (pullback.fst (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ (g ⁻¹ᵁ projChart n 0))) :=
      nonempty_of_le (U := chartPair ψ 0 0) fun z hz => hz.1
    have : Nonempty (ψ ⁻¹ᵁ (pullback.snd (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ (g ⁻¹ᵁ projChart n 0))) :=
      nonempty_of_le (U := chartPair ψ 0 0) fun z hz => hz.2
    have hx0 : x 0 = 1 := by
      change C.germToFunctionField O (φNP.app _ (g.app _ (projRatio n 0 0))) = 1
      rw [projRatio_self]
      erw [map_one, map_one, map_one]
    rw [germToFunctionField_resO, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_map]
    simp only [BombieriVojta.affineEvaluation, LinearMap.coe_mk, AddHom.coe_mk, hx0, map_one,
      one_pow, mul_one, div_one, MvPolynomial.aeval_def]
    congr 1
    · ext c
      change (pullback f f : Scheme.{u}).germToFunctionField (chartPair ψ 0 0)
        (resO le_top ((ψ ≫ _ ≫ _).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom c))) = _
      rw [germToFunctionField_resO, hσ]
      rfl
    · funext ν
      rcases ν with ν | ν
      · change (pullback f f : Scheme.{u}).germToFunctionField (chartPair ψ 0 0)
          (ψ.app _ (resO inf_le_left
            ((pullback.fst (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
              (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).app (g ⁻¹ᵁ projChart n 0)
              (g.app _ (projRatio n 0 ν))))) = functionFieldMap (pullback.fst f f) (x ν)
        rw [app_resO, germToFunctionField_resO]
        exact germToFunctionField_app_app _ φNP ψ _ hψ₁ _
      · change (pullback f f : Scheme.{u}).germToFunctionField (chartPair ψ 0 0)
          (ψ.app _ (resO inf_le_right
            ((pullback.snd (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
              (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).app (g ⁻¹ᵁ projChart n 0)
              (g.app _ (projRatio n 0 ν))))) = functionFieldMap (pullback.snd f f) (x ν)
        rw [app_resO, germToFunctionField_resO]
        exact germToFunctionField_app_app _ φNP ψ _ hψ₂ _
  · intro i
    have := nonempty_of_le (inf_le_right : chartPair ψ 0 0 ⊓ chartOne φB 0 ≤ chartOne φB 0)
    rw [germToFunctionField_resO]
    exact hPη i

end

end Faltings
