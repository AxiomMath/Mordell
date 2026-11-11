module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.FlasqueComplexDerivedSections

/-!
# The presheaf of rational functions on a curve

Let `K` be a field and `C` a curve over `K`, with structure morphism `f : C ⟶ Spec K` and function
field `K(C) = 𝒪_{C,η}`, the stalk at the generic point `η`. The presheaf `𝒦_C` of rational
functions has `𝒦_C(U) = K(C)` for every nonempty open `U` and `𝒦_C(∅) = 0`. Its restriction maps
between nonempty opens are the identity of `K(C)`. It is a presheaf of `𝒪_C`-modules: `Γ(U, 𝒪_C)`
acts on `𝒦_C(U)` through the germ map `Γ(U, 𝒪_C) → 𝒪_{C,η} = K(C)`. The germ maps commute with
restriction, so the restriction maps are semilinear.

## Main definitions

* `Faltings.FunctionField.rationalFunctionPresheaf`: the presheaf `𝒦_C` of rational functions on a
  curve `C`, as a presheaf of modules over the structure sheaf `C.ringCatSheaf`.

## Implementation notes

The sections over an open `U` are the functions `PLift (Nonempty U) → K(C)`. This is `K(C)` when
`U` is nonempty and the zero module when `U` is empty, with no case split in the definition.
Restriction to a smaller open `V ≤ U` precomposes with the implication `Nonempty V → Nonempty U`,
so on nonempty opens it is the identity of `K(C)`. A section `a ∈ Γ(U, 𝒪_C)` acts by multiplication
with its germ `C.germToFunctionField U a`, which is defined once `U` is nonempty.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Faltings.FunctionField

/-- The presheaf `𝒦_C` of rational functions on a curve `C` over `K`, as a presheaf of
`𝒪_C`-modules. Its sections over an open `U` are `PLift (Nonempty U) → C.functionField`, that is
`K(C)` for nonempty `U` and `0` for `U = ∅`. Restriction between nonempty opens is the identity,
and `a ∈ Γ(C, U)` acts by multiplication with its germ `C.germToFunctionField U a` at the generic
point. -/
@[faltings "def_ff_rational_function_sheaf"]
noncomputable def rationalFunctionPresheaf (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] : PresheafOfModules.{u} C.ringCatSheaf.obj :=
  letI : ∀ U : (C.Opens)ᵒᵖ,
      Module (C.ringCatSheaf.obj.obj U) (PLift (Nonempty U.unop) → C.functionField) :=
    fun U ↦ @Pi.module (PLift (Nonempty U.unop)) (fun _ ↦ C.functionField) Γ(C, U.unop) _ _
      (fun h ↦ haveI := h.down
        Module.compHom C.functionField (C.germToFunctionField U.unop).hom)
  PresheafOfModules.ofPresheaf
    { obj := fun U ↦ AddCommGrpCat.of (PLift (Nonempty U.unop) → C.functionField)
      map := fun {U V} i ↦ AddCommGrpCat.ofHom
        { toFun := fun s h ↦ s ⟨h.down.map fun x ↦ ⟨x.1, i.unop.le x.2⟩⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl } }
    (by
      intro U V i a s
      funext ⟨hV⟩
      haveI := hV
      haveI : Nonempty U.unop := hV.map fun x ↦ ⟨x.1, i.unop.le x.2⟩
      change C.germToFunctionField U.unop a * s _ =
        C.germToFunctionField V.unop (C.presheaf.map i a) * s _
      congr 1
      exact (C.presheaf.germ_res_apply' i _ _ a).symm)

end Faltings.FunctionField

end

/-!
# The presheaf of rational functions on a curve is a sheaf

Let `C` be a curve over a field `K`. The presheaf of `𝒪_C`-modules
`Faltings.FunctionField.rationalFunctionPresheaf K f`, with sections `K(C)` over every nonempty
open and `0` over `∅`, satisfies the sheaf condition for the open-cover topology of `C`. Since `C`
is irreducible, any two nonempty opens meet, so compatible sections over a cover all have the same
value in `K(C)`, which is their unique gluing.

## Main results

* `Faltings.FunctionField.isSheaf_rationalFunctionPresheaf`: the presheaf of rational functions
  on a curve is a sheaf, so together with it forms a sheaf of `𝒪_C`-modules.

## Implementation notes

A sheaf of modules in Mathlib (`SheafOfModules`) is a presheaf of modules whose underlying presheaf
of abelian groups satisfies `CategoryTheory.Presheaf.IsSheaf`; this is exactly the field
`SheafOfModules.isSheaf`. The statement is that condition, for the Grothendieck topology
`Opens.grothendieckTopology C` over which `C.ringCatSheaf` is a sheaf.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Faltings.FunctionField

universe u

/-- On an irreducible curve any two nonempty opens meet, so a compatible family of rational
functions takes the same value in `K(C)` on every nonempty member of the cover. -/
private lemma apply_eq_of_isCompatible {K : Type u} [Field K] {C : Scheme.{u}}
    {f : C ⟶ Spec (.of K)} [IsCurve K f] {ι : Type u} {U : ι → C.Opens}
    {sf : ∀ i, ((rationalFunctionPresheaf K f).presheaf ⋙ forget AddCommGrpCat).obj
      (Opposite.op (U i))}
    (hsf : TopCat.Presheaf.IsCompatible
      ((rationalFunctionPresheaf K f).presheaf ⋙ forget AddCommGrpCat) U sf)
    (i j : ι) (hi : Nonempty (U i)) (hj : Nonempty (U j)) :
    (sf i : PLift (Nonempty (U i)) → C.functionField) ⟨hi⟩ =
      (sf j : PLift (Nonempty (U j)) → C.functionField) ⟨hj⟩ := by
  obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
    (Set.nonempty_coe_sort.mp hi) (Set.nonempty_coe_sort.mp hj)
  exact congrFun (hsf i j) ⟨⟨⟨x, hx⟩⟩⟩

/-- The presheaf of rational functions `rationalFunctionPresheaf K f` on a curve `C` over `K` is a
sheaf for the open-cover topology of `C`; hence it underlies a sheaf of `𝒪_C`-modules. -/
@[faltings "lem_ff_rational_function_sheaf"]
theorem isSheaf_rationalFunctionPresheaf (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    Presheaf.IsSheaf (Opens.grothendieckTopology C) (rationalFunctionPresheaf K f).presheaf := by
  change TopCat.Presheaf.IsSheaf _
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat),
    TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι U sf hsf
  have hmem (x : (iSup U : C.Opens)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  refine ⟨fun h ↦ (sf (hmem h.down.some).choose : PLift _ → C.functionField)
    ⟨⟨⟨_, (hmem h.down.some).choose_spec⟩⟩⟩, fun i ↦ ?_, fun t ht ↦ ?_⟩
  · funext ⟨hi⟩
    exact apply_eq_of_isCompatible hsf _ _ _ _
  · funext ⟨⟨x⟩⟩
    obtain ⟨i, hi⟩ := hmem x
    exact (congrFun (ht i) ⟨⟨⟨x.1, hi⟩⟩⟩).trans (apply_eq_of_isCompatible hsf _ _ _ _)

end Faltings.FunctionField

/-!
# The sheaf of rational functions on a curve is acyclic

Let `C` be a curve over a field `K`. The presheaf of rational functions
`Faltings.FunctionField.rationalFunctionPresheaf K f` is a sheaf of `𝒪_C`-modules
(`Faltings.FunctionField.isSheaf_rationalFunctionPresheaf`), written `𝒦_C`. Its restriction maps
are identities or maps to `0`, so they are all surjective: `𝒦_C` is flasque. Hence
`Hᵖ(C, 𝒦_C) = 0` for every `p > 0`.

## Main results

* `Faltings.FunctionField.subsingleton_cohomologyOverField_rationalFunctionSheaf`: the higher
  cohomology `Hᵖ(C, 𝒦_C)`, `p > 0`, of the sheaf of rational functions on a curve vanishes.

## Implementation notes

Cohomology is `AlgebraicGeometry.cohomologyOverField K f F p`: the `p`-th right derived functor of
the global sections functor on `𝒪_C`-modules, as a `K`-vector space through `f`. Vanishing is
stated as `Subsingleton`. The sheaf `𝒦_C` is the object of `C.Modules` with underlying presheaf
`rationalFunctionPresheaf K f`.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

namespace Faltings.FunctionField

universe u

/-- The sheaf `𝒦_C` of rational functions is flasque: a section over a nonempty open `V` is an
element of `K(C)`, and the same element is a section over any larger open. -/
private lemma isFlasque_rationalFunctionSheaf (K : Type u) [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf C.ringCatSheaf).obj (show C.Modules from
      ⟨rationalFunctionPresheaf K f, isSheaf_rationalFunctionPresheaf K f⟩)) := by
  classical
  refine ⟨fun {U V} i => (AddCommGrpCat.epi_iff_surjective _).2 fun t => ?_⟩
  refine ⟨fun _ => if hV : Nonempty V.unop then t ⟨hV⟩ else 0, ?_⟩
  funext ⟨hV⟩
  exact dif_pos hV

/-- The sheaf of rational functions `𝒦_C` on a curve `C` over `K` (the presheaf
`rationalFunctionPresheaf K f`, a sheaf by `isSheaf_rationalFunctionPresheaf`) has no higher
cohomology: `Hᵖ(C, 𝒦_C) = 0` for every `p > 0`. It is flasque, and flasque sheaves of modules
are acyclic. -/
@[faltings "lem_ff_rational_function_sheaf_acyclic"]
theorem subsingleton_cohomologyOverField_rationalFunctionSheaf (K : Type u) [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] {p : ℕ} (hp : 0 < p) :
    Subsingleton (cohomologyOverField K f
      (show C.Modules from ⟨rationalFunctionPresheaf K f, isSheaf_rationalFunctionPresheaf K f⟩)
      p) :=
  ModuleCat.subsingleton_of_isZero <| (ModuleCat.restrictScalars _).map_isZero <|
    Stacks.Cech.Flasque.isZero_rightDerived_evaluation_of_isFlasque C.toTopCat C.ringCatSheaf ⊤
      _ (isFlasque_rationalFunctionSheaf K f) p hp

end Faltings.FunctionField

end

/-!
# Stalks of the sheaf of rational functions on a curve

Let `K` be a field, `C` a curve over `K` and `x ∈ C`. The presheaf `𝒦_C` of rational functions,
`Faltings.FunctionField.rationalFunctionPresheaf K f`, has value `K(C)` on every nonempty open with
identity restrictions. Its stalk at `x` is therefore the colimit of a constant diagram, and the
germ of the section `v ∈ K(C)` over any open `U ∋ x` identifies the stalk with `K(C)`.

The structure map `𝒪_C → 𝒦_C` sends `a ∈ Γ(U, 𝒪_C)` to `a • 1`, the germ of `a` at the generic
point. Under the identification above, the induced map of stalks `𝒪_{C,x} → 𝒦_{C,x} = K(C)` is the
generization map `algebraMap (C.presheaf.stalk x) C.functionField`, which is injective by
`Faltings.FunctionField.algebraMap_stalk_functionField_injective`: it is the inclusion
`𝒪_{C,x} ⊆ K(C)`.

## Main results

* `Faltings.FunctionField.exists_stalk_rationalFunctionPresheaf_addEquiv`: the stalk of `𝒦_C` at
  `x` is `K(C)`, through the germs of the constant sections, and under this identification the
  germ of `a • v` is `algebraMap (C.presheaf.stalk x) C.functionField (germ a) * v`.

## Implementation notes

The stalk is that of the underlying presheaf of abelian groups
`(rationalFunctionPresheaf K f).presheaf`. The map `𝒪_{C,x} → 𝒦_{C,x}` induced by `𝒪_C → 𝒦_C`
is pinned by its values on germs: the germ of `a ∈ Γ(U, 𝒪_C)` goes to the germ of the section
`a • v` of `𝒦_C(U)`, where `v` is the constant section (`v = 1` gives the structure map itself).

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Faltings.FunctionField

universe u

noncomputable section

variable (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] (x : C)

/-- The underlying presheaf of abelian groups of `𝒦_C`. -/
private abbrev presheafAb : TopCat.Presheaf Ab.{u} C.toTopCat :=
  (rationalFunctionPresheaf K f).presheaf

/-- Evaluation of a section of `𝒦_C` over a neighbourhood `U` of `x` at the witness `x ∈ U`,
descended to the stalk at `x`. -/
private def stalkEval : (presheafAb K f).stalk x ⟶ AddCommGrpCat.of C.functionField :=
  Limits.colimit.desc _
    { pt := AddCommGrpCat.of C.functionField
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom
            { toFun := fun (s : PLift (Nonempty U.unop.1) → C.functionField) ↦
                s ⟨⟨⟨x, U.unop.2⟩⟩⟩
              map_zero' := rfl
              map_add' := fun _ _ ↦ rfl }
          naturality := fun _ _ _ ↦ by ext; rfl } }

private lemma stalkEval_germ (U : C.Opens) (hx : x ∈ U) (s : (presheafAb K f).obj (op U)) :
    stalkEval K f x ((presheafAb K f).germ U x hx s) =
      (show PLift (Nonempty U) → C.functionField from s) ⟨⟨⟨x, hx⟩⟩⟩ := by
  rw [← ConcreteCategory.comp_apply]
  erw [Limits.colimit.ι_desc]
  rfl

/-- The stalk of `𝒦_C` at `x` is `K(C)`: evaluation at `x` is inverse to the germ of the constant
section over `C`. -/
private def stalkAddEquiv : (presheafAb K f).stalk x ≃+ C.functionField where
  toFun := stalkEval K f x
  invFun v := (presheafAb K f).germ ⊤ x (by simp)
    (show PLift (Nonempty (⊤ : C.Opens)) → C.functionField from fun _ ↦ v)
  left_inv t := by
    obtain ⟨U, hx, s, rfl⟩ := (presheafAb K f).germ_exist t
    rw [stalkEval_germ]
    exact ((presheafAb K f).germ_res_apply (homOfLE le_top) x hx _).symm.trans (by congr 1)
  right_inv _ := stalkEval_germ K f x ⊤ (by simp) _
  map_add' := map_add (stalkEval K f x).hom

end

/-- On a curve `C` over `K`, the stalk at `x` of the presheaf of rational functions is `K(C)`:
there is an additive isomorphism `e` from the stalk to `C.functionField` sending the germ at `x` of
the section `v ∈ K(C)` over any open `U ∋ x` to `v`. Under `e`, the map of stalks induced by
`𝒪_C → 𝒦_C` is the generization map `𝒪_{C,x} → K(C)`: the germ of `a • v`, for
`a ∈ Γ(C, U)`, goes to `algebraMap (C.presheaf.stalk x) C.functionField (germ a) * v`. -/
@[faltings "lem_ff_rational_function_sheaf_stalk"]
theorem exists_stalk_rationalFunctionPresheaf_addEquiv (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] (x : C) :
    ∃ e : TopCat.Presheaf.stalk (C := Ab.{u}) (X := C.toTopCat)
        (rationalFunctionPresheaf K f).presheaf x ≃+ C.functionField,
      (∀ (U : C.Opens) (hx : x ∈ U) (v : C.functionField),
        e (TopCat.Presheaf.germ (C := Ab.{u}) (X := C.toTopCat)
          (rationalFunctionPresheaf K f).presheaf U x hx
          (show PLift (Nonempty U) → C.functionField from fun _ ↦ v)) = v) ∧
      ∀ (U : C.Opens) (hx : x ∈ U) (a : Γ(C, U)) (v : C.functionField),
        e (TopCat.Presheaf.germ (C := Ab.{u}) (X := C.toTopCat)
          (rationalFunctionPresheaf K f).presheaf U x hx
          ((show C.ringCatSheaf.obj.obj (op U) from a) •
            (show (rationalFunctionPresheaf K f).obj (op U) from fun _ ↦ v))) =
          algebraMap (C.presheaf.stalk x) C.functionField (C.presheaf.germ U x hx a) * v := by
  refine ⟨stalkAddEquiv K f x, fun U hx v ↦ stalkEval_germ K f x U hx _, fun U hx a v ↦ ?_⟩
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  refine (stalkEval_germ K f x U hx _).trans ?_
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  rfl

end Faltings.FunctionField

/-!
# The structure sheaf of a curve embeds in the sheaf of rational functions

Let `C` be a curve over a field `K`. The morphism of presheaves of `𝒪_C`-modules
`𝒪_C → 𝒦_C` sending a section `a ∈ Γ(C, U)` to `a • 1` is, on a nonempty open `U`, the germ map
`Γ(C, U) → K(C)` at the generic point. It is injective on sections over every open: over a nonempty
open because the germ map of an integral scheme is injective, and over `∅` because both sides are
zero.

## Main results

* `Faltings.FunctionField.rationalFunctionPresheaf_unitHom_app_injective`: the map
  `𝒪_C → rationalFunctionPresheaf K f` given by the germ maps is injective on the sections over
  every open of `C`.

## Implementation notes

The morphism `𝒪_C → 𝒦_C` is written as `PresheafOfModules.unitHomEquiv.symm` of the global
section `1`, the same morphism whose cokernel defines `Faltings.FunctionField.principalPartsSheaf`.
Injectivity is stated on sections over each open, which is how a monomorphism of presheaves of
modules is checked.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Faltings.FunctionField

universe u

/-- On a curve `C` over `K`, the morphism `𝒪_C → rationalFunctionPresheaf K f`,
`a ↦ a • 1` (the germ map `Γ(C, U) → K(C)` on nonempty `U`), is injective on sections over every
open `U` of `C`. -/
@[faltings "lem_ff_rational_function_sheaf_injective"]
theorem rationalFunctionPresheaf_unitHom_app_injective (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] (U : (C.Opens)ᵒᵖ) :
    Function.Injective (((rationalFunctionPresheaf K f).unitHomEquiv.symm
      ⟨fun _ _ ↦ 1, fun _ ↦ rfl⟩).app U) := by
  intro a b h
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · exact TopCat.Presheaf.section_ext C.sheaf U.unop a b fun x hx ↦ (hU.false ⟨x, hx⟩).elim
  · have := congrArg (fun s : PLift (Nonempty U.unop) → C.functionField ↦ s ⟨hU⟩) h
    change C.germToFunctionField U.unop a * 1 = C.germToFunctionField U.unop b * 1 at this
    rw [mul_one, mul_one] at this
    exact Scheme.germToFunctionField_injective C U.unop this

end Faltings.FunctionField

end
