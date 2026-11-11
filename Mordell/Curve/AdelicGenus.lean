module

public import Mordell.AlgebraicGeometry.Cohomology.LongExact
public import Mordell.Curve.PrincipalParts
public import Mordell.Curve.RationalFunctionSheaf
public import Mordell.FunctionField.Adele.Quotient
public import Mordell.Curve.PlacesClosedPoints
public import Mordell.FunctionField.Genus
public import Mordell.FunctionField.SmoothProjectiveModel
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import Mordell.Curve.Normal
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison

/-!
# The adelic description of `H¹(C, 𝒪_C)`

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K` and
function field `K(C)`, a `K`-algebra through `K ≅ Γ(Spec K, ⊤) ⟶ Γ(C, ⊤) ⟶ K(C)`. For every
point `x` the local ring `𝒪_{C,x}` is a subring of `K(C)`
(`Faltings.FunctionField.algebraMap_stalk_functionField_injective`), and it contains the image of
`K`. The map `δ_C : K(C) → ⨁_{x closed} K(C)/𝒪_{C,x}`, `f ↦ (f mod 𝒪_{C,x})_x`, is well defined
(a rational function has only finitely many poles) and `K`-linear, and its cokernel is the first
cohomology of the structure sheaf:
`H¹(C, 𝒪_C) ≅ (⨁_{x closed} K(C)/𝒪_{C,x}) / δ_C(K(C))` as `K`-vector spaces. This comes from the
long exact cohomology sequence of `0 → 𝒪_C → 𝒦_C → 𝒬_C → 0`, the constant sheaf `𝒦_C` of
rational functions being acyclic and `Γ(C, 𝒬_C) = ⨁_x K(C)/𝒪_{C,x}`.

## Main results

* `Faltings.FunctionField.exists_linearEquiv_cohomologyOverField_one_structureSheaf`: there is a
  `K`-linear `δ_C` with `δ_C(g)_x = g mod 𝒪_{C,x}` at every closed point `x`, and a `K`-linear
  isomorphism from `H¹(C, 𝒪_C)` to the cokernel of `δ_C`.

## Implementation notes

`H¹(C, 𝒪_C)` is `AlgebraicGeometry.cohomologyOverField K f (SheafOfModules.unit C.ringCatSheaf) 1`,
the first right derived functor of global sections, a `K`-module through `f`. The closed points
are the subtype of `closedPoints C`. The submodule `𝒪_{C,x} ⊆ K(C)` is the `K`-span of the image of
`algebraMap (C.presheaf.stalk x) C.functionField`; since this image is a subring containing the
image of `K`, the span is the image itself. The direct sum is `DirectSum`, and `δ_C(K(C))` is
`LinearMap.range δ`.

`𝒬_C` is the sheafification of the presheaf cokernel of `𝒪_C → 𝒦_C`; that `𝒦_C → 𝒬_C` is a
cokernel in sheaves of modules follows from the sheafification adjunction, so
`0 → 𝒪_C → 𝒦_C → 𝒬_C → 0` is short exact. `H⁰` is identified with global sections through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. The long exact sequence and `H¹(C, 𝒦_C) = 0`
identify `H¹(C, 𝒪_C)` with the cokernel of `H⁰(C, 𝒦_C) → H⁰(C, 𝒬_C)`; the image of that map is the
set of classes of the constant sections `g ∈ K(C)`, which go to `δ_C(g)` under
`Faltings.FunctionField.exists_linearEquiv_principalPartsSheaf_sections`.

## References

* [Serre, *Groupes algébriques et corps de classes*, Ch. II, no. 5, Prop. 3]
* [Stichtenoth, *Algebraic Function Fields and Codes*, Cor. 1.5.5]
-/

public section

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open AlgebraicGeometry CategoryTheory Opposite Limits
open scoped DirectSum

universe u

namespace Faltings.FunctionField

section

variable (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f]

/-- The sheaf `𝒦_C` of rational functions, as a sheaf of `𝒪_C`-modules. -/
private noncomputable abbrev ratSheaf : SheafOfModules C.ringCatSheaf :=
  ⟨rationalFunctionPresheaf K f, isSheaf_rationalFunctionPresheaf K f⟩

/-- The sheaf `𝒬_C` of principal parts, as an object of `SheafOfModules C.ringCatSheaf`. -/
private noncomputable abbrev ppSheaf : SheafOfModules C.ringCatSheaf := principalPartsSheaf K f

/-- The inclusion `𝒪_C → 𝒦_C`, the germ map at the generic point on each nonempty open. -/
private noncomputable abbrev unitToRat : SheafOfModules.unit C.ringCatSheaf ⟶ ratSheaf K f :=
  ⟨toRationalFunctionPresheaf K f⟩

/-- The quotient map `𝒦_C → 𝒬_C` of sheaves of `𝒪_C`-modules. -/
private noncomputable abbrev ratToPP : ratSheaf K f ⟶ ppSheaf K f := ⟨toPrincipalPartsSheaf K f⟩

private lemma unitToRat_comp_ratToPP : unitToRat K f ≫ ratToPP K f = 0 := by
  apply (SheafOfModules.forget _).map_injective
  rw [Functor.map_comp, Functor.map_zero]
  exact cokernel.condition_assoc _ _ |>.trans zero_comp

private lemma mono_unitToRat : Mono (unitToRat K f) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (hf := rationalFunctionPresheaf_unitHom_app_injective K f))

private lemma map_ratToPP_comp {M : SheafOfModules C.ringCatSheaf} (x : ppSheaf K f ⟶ M) :
    (SheafOfModules.forget C.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 C.ringCatSheaf.obj)).map (ratToPP K f ≫ x) =
      cokernel.π (unitToRat K f).val ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 C.ringCatSheaf.obj)).homEquiv _ M x := by
  erw [Adjunction.homEquiv_unit, Functor.map_comp]
  exact Category.assoc _ _ _

/-- `𝒦_C → 𝒬_C` is a cokernel of `𝒪_C → 𝒦_C` in sheaves of `𝒪_C`-modules. -/
private noncomputable def isColimitCokernelCofork :
    IsColimit (CokernelCofork.ofπ (ratToPP K f) (unitToRat_comp_ratToPP K f)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 C.ringCatSheaf.obj)
  let G := SheafOfModules.forget C.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 C.ringCatSheaf.obj)
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {M} h hh ↦ (adj.homEquiv _ M).symm (cokernel.desc _ (G.map h) ?_)) ?_ ?_
  · have := congrArg G.map hh
    rwa [G.map_comp, G.map_zero] at this
  · intro M h hh
    apply G.map_injective
    refine (map_ratToPP_comp K f _).trans ?_
    erw [Equiv.apply_symm_apply, cokernel.π_desc]
  · intro M h hh m hm
    apply (adj.homEquiv _ M).injective
    erw [Equiv.apply_symm_apply]
    apply (cancel_epi (cokernel.π _)).1
    erw [cokernel.π_desc, ← hm]
    exact (map_ratToPP_comp K f m).symm

/-- `0 → 𝒪_C → 𝒦_C → 𝒬_C → 0` is a short exact sequence of `𝒪_C`-modules. -/
private lemma shortExact :
    (ShortComplex.mk (unitToRat K f) (ratToPP K f) (unitToRat_comp_ratToPP K f)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (isColimitCokernelCofork K f))
    (mono_unitToRat K f) (epi_of_isColimit_cofork (isColimitCokernelCofork K f))

omit [IsCurve K f] in
private lemma appLE_top_eq_appTop :
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 3

/-- Restriction of scalars from `Γ(C, 𝒪_C)` to `K`, along `f`. -/
private noncomputable abbrev restrictToK : ModuleCat.{u} Γ(C, ⊤) ⥤ ModuleCat.{u} K :=
  ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- `H¹(C, 𝒪_C)` is the cokernel of `H⁰(C, 𝒦_C) → H⁰(C, 𝒬_C)`: the long exact sequence of
`0 → 𝒪_C → 𝒦_C → 𝒬_C → 0`, with `H¹(C, 𝒦_C) = 0`. -/
private lemma exists_linearEquiv_cohomology_one_quotient :
    Nonempty (cohomologyOverField K f (SheafOfModules.unit C.ringCatSheaf) 1 ≃ₗ[K]
      (restrictToK K f).obj
          (((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).obj
            (ppSheaf K f)) ⧸
        LinearMap.range ((restrictToK K f).map
          (((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).map
            (ratToPP K f))).hom) := by
  obtain ⟨δ, -, -, h2, h3⟩ :=
    Faltings.exists_rightDerived_moduleGlobalSections_longExactSequence C.toRingedSpace
      (shortExact K f)
  exact ⟨(Function.Exact.linearEquivOfSurjective (g := ((restrictToK K f).map (δ 0)).hom) (h2 0)
    fun y ↦ (h3 0 y).1 (Subsingleton.elim
      (h := subsingleton_cohomologyOverField_rationalFunctionSheaf K f one_pos) _ _)).symm⟩

/-- On global sections, the image of `H⁰(C, 𝒦_C) → H⁰(C, 𝒬_C)` consists of the classes of the
constant sections `g ∈ K(C)`. -/
private lemma range_rightDerivedZero_map_ratToPP [Nonempty (⊤ : C.Opens)] :
    Set.range (fun z ↦ ((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace)
        |>.rightDerivedZeroIsoSelf.hom.app (ppSheaf K f)).hom
          ((((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).map
            (ratToPP K f)).hom z)) =
      Set.range (fun g : C.functionField ↦ (ratToPP K f).val.app (op ⊤)
        (show (rationalFunctionPresheaf K f).obj (op ⊤) from fun _ ↦ g)) := by
  set e := (Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerivedZeroIsoSelf
  have hn (z) : (e.hom.app (ppSheaf K f)).hom
      ((((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).map
        (ratToPP K f)).hom z) = (ratToPP K f).val.app (op ⊤) ((e.hom.app (ratSheaf K f)).hom z) :=
    congrArg (fun φ ↦ φ.hom z) (e.hom.naturality (ratToPP K f))
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(e.hom.app (ratSheaf K f)).hom z ⟨‹_›⟩,
      ((hn z).trans (congrArg ((ratToPP K f).val.app (op ⊤)).hom (funext fun _ ↦ rfl))).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(e.inv.app (ratSheaf K f)).hom fun _ ↦ g, (hn _).trans
      (congrArg ((ratToPP K f).val.app (op ⊤)).hom (Iso.inv_hom_id_apply (e.app _) _))⟩

end

/-- **Adelic description of `H¹(C, 𝒪_C)`.** Let `f : C ⟶ Spec K` be a curve over a field `K`,
with function field `K(C)`, a `K`-algebra through `f`. There is a `K`-linear map
`δ : K(C) → ⨁_{x closed} K(C)/𝒪_{C,x}` with `δ g x = g mod 𝒪_{C,x}` for all `g` and all closed
points `x`, and a `K`-linear isomorphism
`H¹(C, 𝒪_C) ≃ₗ[K] (⨁_{x closed} K(C)/𝒪_{C,x}) ⧸ LinearMap.range δ`. -/
@[faltings "prop_ff_h1_adelic"]
theorem exists_linearEquiv_cohomologyOverField_one_structureSheaf (K : Type u) [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
    ∃ δ : C.functionField →ₗ[K] ⨁ x : closedPoints C, C.functionField ⧸
        Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField)),
      (∀ (g : C.functionField) (x : closedPoints C), δ g x = Submodule.Quotient.mk g) ∧
      Nonempty (cohomologyOverField K f (SheafOfModules.unit C.ringCatSheaf) 1 ≃ₗ[K]
        (⨁ x : closedPoints C, C.functionField ⧸
          Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField))) ⧸
          LinearMap.range δ) := by
  obtain ⟨θ, hθ⟩ := exists_linearEquiv_principalPartsSheaf_sections K f
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  let φ : K →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom
  let : Module K ((principalPartsSheaf K f).val.obj (op ⊤)) :=
    Module.compHom _ (show K →+* C.ringCatSheaf.obj.obj (op ⊤) from φ)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  let δC : C.functionField →ₗ[K] ⨁ x : closedPoints C, C.functionField ⧸
      Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField)) :=
    { toFun := fun g ↦ θ ((ratToPP K f).val.app (op ⊤)
        (show (rationalFunctionPresheaf K f).obj (op ⊤) from fun _ ↦ g))
      map_add' := fun g g' ↦ by
        rw [← map_add, ← map_add]
        rfl
      map_smul' := fun k g ↦ by
        change θ ((ratToPP K f).val.app (op ⊤) ((show C.ringCatSheaf.obj.obj (op ⊤) from φ k) •
          (show (rationalFunctionPresheaf K f).obj (op ⊤) from fun _ ↦ g))) = _
        rw [map_smul]
        exact θ.map_smul k _ }
  refine ⟨δC, fun g x ↦ hθ _ x ⊤ trivial g ?_, ?_⟩
  · rw [show (homOfLE le_top : (⊤ : C.Opens) ⟶ ⊤).op = 𝟙 _ from rfl, PresheafOfModules.map_id]
    rfl
  · let e := (Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerivedZeroIsoSelf
    let ψ := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
    let θ' : (restrictToK K f).obj
        (((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).obj
          (ppSheaf K f)) ≃ₗ[K] ⨁ x : closedPoints C, C.functionField ⧸
          Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField)) :=
      { ((e.app (ppSheaf K f)).toLinearEquiv.toAddEquiv.trans θ.toAddEquiv) with
        map_smul' := fun k x ↦ by
          change θ ((e.hom.app (ppSheaf K f)).hom
            ((show C.ringCatSheaf.obj.obj (op ⊤) from ψ k) •
              (show ((Stacks.Cohomology.moduleGlobalSections C.toRingedSpace).rightDerived 0).obj
                (ppSheaf K f) from x))) = k • θ _
          rw [map_smul, show ψ k = φ k from congrArg (· k) (appLE_top_eq_appTop K f)]
          exact θ.map_smul k _ }
    obtain ⟨E⟩ := exists_linearEquiv_cohomology_one_quotient K f
    refine ⟨E.trans (Submodule.Quotient.equiv _ _ θ' ?_)⟩
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range]
    have h := range_rightDerivedZero_map_ratToPP K f
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      obtain ⟨g, hg⟩ := h.subset ⟨z, rfl⟩
      exact ⟨g, congrArg θ hg⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨z, hz⟩ := h.superset ⟨g, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, congrArg θ hz⟩

end Faltings.FunctionField

end


/-!
# The adelic quotient of a function field is `H¹` of a normal proper model

Let `F/K` be an algebraic function field of one variable, with adele ring `𝒜_F`, integral adeles
`𝒜_F(0)` and principal adeles `P_F`. Let `f : C ⟶ Spec K` be a normal proper curve over `K` and
`φ : K(C) ≃ₐ[K] F` an isomorphism of `K`-algebras, where `K(C)` is a `K`-algebra through `f`.
The closed points of `C` correspond, through `φ`, to the places of `F/K`, and the adelic
description of `H¹(C, 𝒪_C)` transports to the adelic quotient of `F`: there is a `K`-linear
isomorphism `𝒜_F / (𝒜_F(0) + P_F) ≅ H¹(C, 𝒪_C)`.

## Main results

* `Faltings.FunctionField.nonempty_linearEquiv_adele_quotient_cohomologyOverField_one`: the
  `K`-linear isomorphism `𝒜_F / (𝒜_F(0) + P_F) ≃ₗ[K] H¹(C, 𝒪_C)`.

## Implementation notes

`H¹(C, 𝒪_C)` is `AlgebraicGeometry.cohomologyOverField K f (SheafOfModules.unit C.ringCatSheaf) 1`,
a `K`-module through `f`. The sum `𝒜_F(0) + P_F` is the supremum
`Faltings.Adele.integral K F ⊔ Faltings.Adele.principal K F` of `K`-submodules of
`Faltings.Adele K F`. Normality is `AlgebraicGeometry.IsNormal C` and properness is
`AlgebraicGeometry.IsProper f`.

## References

* [Serre, *Groupes algébriques et corps de classes*, Ch. II, no. 5]
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Corollary 1.5.5
-/

public section

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u v

namespace Faltings.FunctionField

/-- Cokernels of principal-part maps are invariant under transport: if a linear equivalence
`e : M ≃ N` and a bijection `σ : ι ≃ κ` carry each `S i ⊆ M` onto `T (σ i) ⊆ N`, then the
cokernels of the diagonal maps `M → ⨁ i, M ⧸ S i` and `N → ⨁ k, N ⧸ T k` are isomorphic. -/
private lemma nonempty_linearEquiv_quotient_range_diagonal {R M N ι κ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (σ : ι ≃ κ) (S : ι → Submodule R M) (T : κ → Submodule R N)
    (hST : ∀ i, (S i).map (e : M →ₗ[R] N) = T (σ i))
    (δ : M →ₗ[R] ⨁ i, M ⧸ S i) (hδ : ∀ g i, δ g i = Submodule.Quotient.mk g)
    (δ' : N →ₗ[R] ⨁ k, N ⧸ T k) (hδ' : ∀ g k, δ' g k = Submodule.Quotient.mk g) :
    Nonempty (((⨁ i, M ⧸ S i) ⧸ LinearMap.range δ) ≃ₗ[R]
      ((⨁ k, N ⧸ T k) ⧸ LinearMap.range δ')) := by
  let τ := DirectSum.lequivCongrLeft R (M := fun k => N ⧸ T k) σ.symm
  let Ψ : (⨁ i, M ⧸ S i) ≃ₗ[R] ⨁ k, N ⧸ T k :=
    (DFinsupp.mapRange.linearEquiv fun i =>
      Submodule.Quotient.equiv (S i) (T (σ i)) e (hST i)).trans τ.symm
  have hΨ : (Ψ : _ →ₗ[R] _) ∘ₗ δ = δ' ∘ₗ (e : M →ₗ[R] N) := by
    ext g : 1
    apply τ.injective
    ext i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Ψ, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, τ, DirectSum.lequivCongrLeft_apply]
    change Submodule.Quotient.equiv (S i) (T (σ i)) e (hST i) (δ g i) = δ' (e g) (σ i)
    rw [hδ, hδ']
    rfl
  refine ⟨Submodule.Quotient.equiv _ _ Ψ ?_⟩
  rw [← LinearMap.range_comp, hΨ, LinearMap.range_comp_of_range_eq_top _ e.range]

/-- For a normal proper curve `C` with `φ : K(C) ≃ₐ[K] F`, the closed points of `C` are in
bijection with the places of `F/K`, the place of `x` having `φ(𝒪_{C,x})` as valuation ring. -/
private lemma exists_equiv_closedPoints_place (K : Type u) [Field K] (F : Type v) [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsNormal C] [IsProper f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F) :
    ∃ σ : closedPoints C ≃ Place K F, ∀ x, ((σ x).toSubalgebra : Set F) =
      φ '' Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField) := by
  choose σ hσ using fun x : closedPoints C => exists_place_eq_image_stalk K F f φ x.2
  refine ⟨Equiv.ofBijective σ ⟨fun x y hxy => ?_, fun w => ?_⟩, hσ⟩
  · obtain ⟨z, -, hz⟩ := existsUnique_isClosed_place_eq_image_stalk K F f φ (σ x)
    exact Subtype.ext ((hz x.1 ⟨x.2, hσ x⟩).trans (hz y.1 ⟨y.2, hxy ▸ hσ y⟩).symm)
  · obtain ⟨z, ⟨hz, hzw⟩, -⟩ := existsUnique_isClosed_place_eq_image_stalk K F f φ w
    exact ⟨⟨z, hz⟩, Place.ext ((hσ ⟨z, hz⟩).trans hzw.symm)⟩

/-- **Adelic quotient and `H¹` of a normal proper model.** Let `F/K` be a function field,
`f : C ⟶ Spec K` a normal proper curve over `K` and `φ : K(C) ≃ₐ[K] F` an isomorphism of
`K`-algebras. Then `𝒜_F / (𝒜_F(0) + P_F)` is `K`-linearly isomorphic to `H¹(C, 𝒪_C)`. -/
@[faltings "prop_ff_adelic_quotient_h1"]
theorem nonempty_linearEquiv_adele_quotient_cohomologyOverField_one (K : Type u) [Field K]
    (F : Type v) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsNormal C]
    [IsProper f]
    (φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
      C.functionField ≃ₐ[K] F) :
    Nonempty ((Adele K F ⧸ (Adele.integral K F ⊔ Adele.principal K F)) ≃ₗ[K]
      cohomologyOverField K f (SheafOfModules.unit C.ringCatSheaf) 1) := by
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  obtain ⟨δ, hδ, e, -⟩ := Adele.exists_linearEquiv_quotient_integral_sup_principal K F
  obtain ⟨δC, hδC, ⟨eC⟩⟩ := exists_linearEquiv_cohomologyOverField_one_structureSheaf K f
  obtain ⟨σ, hσ⟩ := exists_equiv_closedPoints_place K F f φ
  obtain ⟨Ψ⟩ := nonempty_linearEquiv_quotient_range_diagonal φ.toLinearEquiv σ
    (fun x => Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField)))
    (fun v => Subalgebra.toSubmodule v.toSubalgebra)
    (fun x => by rw [Submodule.map_span, LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
      ← hσ x, ← Subalgebra.coe_toSubmodule, Submodule.span_eq]) δC hδC δ hδ
  exact ⟨e.trans (Ψ.symm.trans eC.symm)⟩

end Faltings.FunctionField

end


/-!
# The genus of a function field is the genus of its smooth projective model

Let `K` be a perfect field, `F/K` an algebraic function field of one variable and `(C, φ)` a
smooth projective model of `F/K`. Then the genus of the curve `C`, the `K`-dimension of
`H¹(C, 𝒪_C)`, equals the genus `g(F/K)`, the `K`-dimension of the adelic quotient
`𝒜_F / (𝒜_F(0) + P_F)`.

## Main results

* `Faltings.FunctionField.SmoothProjectiveModel.genus_f_eq_genus`: the genus
  `AlgebraicGeometry.genus M.f` of the curve of a smooth projective model `M` of `F/K` is the
  genus `Faltings.genus K F` of `F/K`.

## Implementation notes

The genus of the curve is `AlgebraicGeometry.genus M.f`, the `Module.finrank` over `K` of the
first cohomology of the structure sheaf, a natural number, as is `Faltings.genus K F`. The proof
identifies that cohomology with `AlgebraicGeometry.cohomologyOverField K M.f
(SheafOfModules.unit M.C.ringCatSheaf) 1` and the latter with the adelic quotient. The
finiteness of `H¹(C, 𝒪_C)` is not part of the statement: it is
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`.

## References

* [J.-P. Serre, *Groupes algébriques et corps de classes*], Chapitre II, n° 5
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Corollary 1.5.5
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

public section

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open AlgebraicGeometry CategoryTheory

universe u v

namespace Faltings.FunctionField

/-- **The adelic genus is the genus of the curve.** Let `K` be a perfect field, `F/K` a function
field and `M` a smooth projective model of `F/K` with structure morphism `M.f : M.C ⟶ Spec K`.
Then the genus `AlgebraicGeometry.genus M.f = dim_K H¹(M.C, 𝒪_{M.C})` of the curve is `g(F/K)`. -/
@[faltings "thm_ff_genus_eq_curve_genus"]
theorem SmoothProjectiveModel.genus_f_eq_genus (K : Type u) [Field K] [PerfectField K]
    (F : Type v) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FunctionField K F] (M : SmoothProjectiveModel K F) :
    AlgebraicGeometry.genus M.f = genus K F := by
  have := M.isCurve
  have := M.isProjectiveVariety
  have := M.smooth
  have : IsNormal M.C := isNormal_of_smooth K M.f
  obtain ⟨e⟩ := nonempty_linearEquiv_adele_quotient_cohomologyOverField_one K F M.f M.φ
  rw [AlgebraicGeometry.genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField K M.f 1).toLinearEquiv.finrank_eq,
    Faltings.genus, e.finrank_eq]

end Faltings.FunctionField

end
