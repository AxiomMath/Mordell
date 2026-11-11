module

public import Mordell.Curve.RationalFunctionSheaf
public import Mordell.Curve.Topology
public import Mordell.Curve.FunctionField

/-!
# The sheaf of principal parts on a curve

Let `K` be a field and `C` a curve over `K` with function field `K(C)`. The presheaf `𝒦_C` of
rational functions has `𝒦_C(U) = K(C)` on every nonempty open `U`. The structure sheaf maps to it:
on a nonempty open `U` the map `Γ(U, 𝒪_C) → K(C)` is the germ map at the generic point. The sheaf
of principal parts `𝒬_C = 𝒦_C / 𝒪_C` is the quotient of `𝒦_C` by the image of this morphism, as a
sheaf of `𝒪_C`-modules.

## Main definitions

* `Faltings.FunctionField.principalPartsSheaf`: the sheaf `𝒬_C = 𝒦_C / 𝒪_C` of principal parts,
  an object of `C.Modules`.
* `Faltings.FunctionField.toRationalFunctionPresheaf`: the structure morphism `𝒪_C → 𝒦_C`.
* `Faltings.FunctionField.toPrincipalPartsSheaf`: the projection `𝒦_C → 𝒬_C`.

## Implementation notes

The morphism `𝒪_C → 𝒦_C` is the morphism from the unit presheaf of modules that corresponds,
under `PresheafOfModules.unitHomEquiv`, to the global section `1` of `𝒦_C`. On an open `U` it sends
`a` to `a • 1`, and on a nonempty `U` that is the germ `C.germToFunctionField U a`. The quotient is
the cokernel of this morphism in presheaves of modules, sheafified along the identity of
`C.ringCatSheaf`. Sheafification is a left adjoint, so it preserves cokernels. `𝒦_C` is already a
sheaf, so the result is the cokernel of `𝒪_C → 𝒦_C` in the category of sheaves of `𝒪_C`-modules,
which is the quotient sheaf the source means.

## References

* [R. Hartshorne, *Algebraic Geometry*, II Ex. 1.21(d)][Hartshorne1977]
* [J.-P. Serre, *Groupes algébriques et corps de classes*, Ch. II, no. 5][Serre1959]
-/

@[expose] public section

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Faltings.FunctionField

/-- The sheaf of principal parts `𝒬_C = 𝒦_C / 𝒪_C` on a curve `C` over `K`. It is the quotient
sheaf of `𝒪_C`-modules of the rational-function presheaf `rationalFunctionPresheaf K f` by the
image of `𝒪_C → 𝒦_C`, which on each nonempty open `U` is the germ map `Γ(U, 𝒪_C) → K(C)`. -/
@[faltings "def_ff_principal_parts_sheaf"]
noncomputable def principalPartsSheaf (K : Type u) [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] : C.Modules :=
  (PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
    (Limits.cokernel ((rationalFunctionPresheaf K f).unitHomEquiv.symm
      ⟨fun _ _ ↦ 1, fun _ ↦ rfl⟩))

section

variable (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f]

/-- The structure morphism `𝒪_C → 𝒦_C`, `a ↦ a • 1`; on a nonempty open `U` it is the germ map
`Γ(U, 𝒪_C) → K(C)`. Its cokernel, sheafified, is `principalPartsSheaf K f`. -/
noncomputable abbrev toRationalFunctionPresheaf :
    PresheafOfModules.unit C.ringCatSheaf.obj ⟶ rationalFunctionPresheaf K f :=
  (rationalFunctionPresheaf K f).unitHomEquiv.symm ⟨fun _ _ ↦ 1, fun _ ↦ rfl⟩

/-- The projection `𝒦_C → 𝒬_C` on underlying presheaves: the presheaf cokernel map of
`toRationalFunctionPresheaf K f` followed by the unit of sheafification. -/
noncomputable abbrev toPrincipalPartsSheaf : rationalFunctionPresheaf K f ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 C.ringCatSheaf.obj)).obj
      (principalPartsSheaf K f) :=
  Limits.cokernel.π (toRationalFunctionPresheaf K f) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 C.ringCatSheaf.obj)).unit.app _

end

end Faltings.FunctionField

end


/-!
# Global principal parts on a curve

Let `K` be a field and `C` a curve over `K` with function field `K(C)`, and let
`𝒬_C = 𝒦_C / 𝒪_C` be the sheaf of principal parts,
`Faltings.FunctionField.principalPartsSheaf K f`. At a point `x` of `C`, the stalk of `𝒬_C` is
`K(C)/𝒪_{C,x}`: the germ at `x` of a section that is the class of `v ∈ K(C)` on a neighbourhood
of `x` is `v mod 𝒪_{C,x}`. A global section of `𝒬_C` has only finitely many nonzero germs at the
closed points, and `s ↦ (s_x)_x` is a `K`-linear isomorphism
`Γ(C, 𝒬_C) ≃ ⨁_{x closed} K(C)/𝒪_{C,x}`.

## Main results

* `Faltings.FunctionField.exists_linearEquiv_principalPartsSheaf_sections`: the map
  `s ↦ (s_x)_{x closed}` is a `K`-linear isomorphism from `Γ(C, 𝒬_C)` onto
  `⨁_{x closed} K(C)/𝒪_{C,x}`.

## Implementation notes

`𝒪_{C,x}` is the image of the generization map
`algebraMap (C.presheaf.stalk x) C.functionField`, which is injective since `C` is integral
(`FaithfulSMul.algebraMap_injective`, from the `IsFractionRing` instance on the stalk); it is
written as the `K`-span of that image, which is the image itself. `K(C)` is a `K`-algebra through
`f`, and `Γ(C, 𝒬_C)` is a `K`-module through `K → Γ(C, 𝒪_C)`.

The germ `s_x ∈ K(C)/𝒪_{C,x}` is pinned without naming the stalk of `𝒬_C`. Let
`π : 𝒦_C → 𝒬_C` be the cokernel projection followed by the unit of sheafification. Every section
of `𝒬_C` is, near each point `x`, of the form `π(v)` for a constant section `v ∈ K(C)` over an
open `U ∋ x`, and then `s_x = v mod 𝒪_{C,x}`. The statement asks for the isomorphism to send `s`
to a family whose `x`-coordinate is `v mod 𝒪_{C,x}` whenever `s|_U = π(v)` with `x ∈ U`; this
determines it.

The isomorphism is built directly on global sections rather than through the sheaf
`U ↦ ⨁_{x ∈ U closed} K(C)/𝒪_{C,x}` and a comparison of stalks. Every section of `𝒬_C` is
locally `π(v)`, since the cokernel projection is surjective and the unit of sheafification is
locally surjective. Two local representatives `v, v'` at `x` differ by an element of `𝒪_{C,x}`:
`π(v - v') = 0` near `x` forces, by local injectivity of the unit and exactness of
`𝒪_C → 𝒦_C → 𝒦_C/𝒪_C` on sections, `v - v'` to be regular near `x`. The family of germs has
finite support because `C` is quasi-compact and each representative is regular away from finitely
many closed points; a section with vanishing germs at the closed points is zero, since at the
generic point every rational function is regular on a neighbourhood; and a finite family of
principal parts glues from the sections `π(v_y)` on the opens `C \ (B \ {y})`, where `B` is a
finite set of closed points away from which every chosen representative is regular.

## References

* [J.-P. Serre, *Groupes algébriques et corps de classes*, Ch. II, no. 5][Serre1959]
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

universe u

public section

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.FunctionField

/-- If `K` maps into the image of `A` in `L`, the `K`-span of that image is the image itself. -/
private lemma mem_range_of_mem_span {A L K : Type*} [CommRing A] [CommRing L] [Algebra A L]
    [CommSemiring K] [Algebra K L] (hK : ∀ k : K, algebraMap K L k ∈ (algebraMap A L).range)
    {v : L} (hv : v ∈ Submodule.span K (Set.range (algebraMap A L))) :
    v ∈ (algebraMap A L).range := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul k x _ hx => rw [Algebra.smul_def]; exact mul_mem (hK k) hx

private lemma germToFunctionField_res {C : Scheme.{u}} [IrreducibleSpace C] {W V : C.Opens}
    [Nonempty W] [Nonempty V] (h : W ≤ V) (a : Γ(C, V)) :
    C.germToFunctionField W (C.presheaf.map (homOfLE h).op a) = C.germToFunctionField V a :=
  C.presheaf.germ_res_apply (homOfLE h) _ _ a

/-- A finitely supported family of classes in quotients `M ⧸ N x`, indexed by `x ∈ S`, lifts to a
finitely supported family in `M`, supported in `S`. -/
private lemma exists_lift_directSum {X R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {S : Set X} (N : S → Submodule R M) (d : ⨁ x : S, M ⧸ N x) :
    ∃ w : X → M, {y | w y ≠ 0}.Finite ∧ (∀ y, w y ≠ 0 → y ∈ S) ∧
      ∀ x : S, Submodule.Quotient.mk (w x) = d x := by
  classical
  choose l hl using fun x : S ↦ Submodule.Quotient.mk_surjective _ (d x)
  let w : X → M := fun y ↦ if h : y ∈ S then if d ⟨y, h⟩ = 0 then 0 else l ⟨y, h⟩ else 0
  have hw (y : X) (hy : w y ≠ 0) : ∃ h : y ∈ S, d ⟨y, h⟩ ≠ 0 := by
    by_cases h : y ∈ S
    · exact ⟨h, fun hd ↦ hy (by simp [w, h, hd])⟩
    · exact absurd (by simp [w, h]) hy
  refine ⟨w, ((d.support : Set S).toFinite.image Subtype.val).subset fun y hy ↦ ?_,
    fun y hy ↦ (hw y hy).1, fun x ↦ ?_⟩
  · obtain ⟨h, hd⟩ := hw y hy
    exact ⟨⟨y, h⟩, by simpa using hd, rfl⟩
  · by_cases hd : d x = 0
    · simp [w, hd]
    · simp [w, hd, hl]

section

variable (K : Type u) [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f]

/-- The constant section `v` of `𝒦_C` over `U`. -/
private abbrev cst (U : C.Opens) (v : C.functionField) :
    (rationalFunctionPresheaf K f).obj (op U) :=
  (show PLift (Nonempty U) → C.functionField from fun _ ↦ v)

private lemma toRationalFunctionPresheaf_app_apply (U : C.Opens) [Nonempty U] (a : Γ(C, U)) :
    (toRationalFunctionPresheaf K f).app (op U) a = cst K f U (C.germToFunctionField U a) := by
  funext ⟨h⟩
  change C.germToFunctionField U a * 1 = _
  rw [mul_one]

private lemma cokernel_π_app_surjective (U : (C.Opens)ᵒᵖ) :
    Function.Surjective ((Limits.cokernel.π (toRationalFunctionPresheaf K f)).app U) :=
  PresheafOfModules.surjective_of_epi _ U

private lemma exists_toRationalFunctionPresheaf_app_eq (U : (C.Opens)ᵒᵖ)
    (t : (rationalFunctionPresheaf K f).obj U)
    (h : (Limits.cokernel.π (toRationalFunctionPresheaf K f)).app U t = 0) :
    ∃ a, (toRationalFunctionPresheaf K f).app U a = t := by
  have hS := (ShortComplex.cokernelSequence_exact (toRationalFunctionPresheaf K f)).map
    (PresheafOfModules.evaluation _ U)
  rw [ShortComplex.moduleCat_exact_iff] at hS
  exact hS t h

private lemma cst_eq (U : C.Opens) (x : C) (hx : x ∈ U)
    (t : (rationalFunctionPresheaf K f).obj (op U)) :
    t = cst K f U ((show PLift (Nonempty U) → C.functionField from t) ⟨⟨⟨x, hx⟩⟩⟩) := by
  funext h
  rfl

private lemma exists_toPrincipalPartsSheaf_eq (U : C.Opens)
    (s : (principalPartsSheaf K f).val.obj (op U)) (x : C) (hx : x ∈ U) :
    ∃ (W : C.Opens) (hWU : W ≤ U), x ∈ W ∧ ∃ v,
      (principalPartsSheaf K f).val.map (homOfLE hWU).op s =
        (toPrincipalPartsSheaf K f).app (op W) (cst K f W v) := by
  obtain ⟨W, hWU, ⟨c, hc⟩, hxW⟩ := (TopCat.Presheaf.isLocallySurjective_iff
    (toSheafify (Opens.grothendieckTopology C)
      (Limits.cokernel (toRationalFunctionPresheaf K f)).presheaf)).1
      (inferInstanceAs (Presheaf.IsLocallySurjective _ _)) U s x hx
  obtain ⟨t, rfl⟩ := cokernel_π_app_surjective K f (op W) c
  refine ⟨W, hWU, hxW, (show PLift (Nonempty W) → C.functionField from t) ⟨⟨⟨x, hxW⟩⟩⟩, ?_⟩
  rw [← cst_eq K f W x hxW t]
  exact hc.symm

private lemma toPrincipalPartsSheaf_app_toRationalFunctionPresheaf_app (W : (C.Opens)ᵒᵖ)
    (a : (PresheafOfModules.unit C.ringCatSheaf.obj).obj W) :
    (toPrincipalPartsSheaf K f).app W ((toRationalFunctionPresheaf K f).app W a) = 0 := by
  have : toRationalFunctionPresheaf K f ≫ toPrincipalPartsSheaf K f = 0 :=
    (Limits.cokernel.condition_assoc _ _).trans Limits.zero_comp
  exact (congrArg (fun φ ↦ (φ.app W) a) this :)

private lemma toPrincipalPartsSheaf_cst_germToFunctionField (W V : C.Opens) [Nonempty V]
    (h : W ≤ V) (a : Γ(C, V)) :
    (toPrincipalPartsSheaf K f).app (op W) (cst K f W (C.germToFunctionField V a)) = 0 := by
  have : cst K f W (C.germToFunctionField V a) =
      (toRationalFunctionPresheaf K f).app (op W) (C.presheaf.map (homOfLE h).op a) := by
    funext ⟨hW⟩
    have := hW
    change C.germToFunctionField V a =
      C.germToFunctionField W (C.presheaf.map (homOfLE h).op a) * 1
    rw [mul_one, germToFunctionField_res]
  rw [this]
  exact toPrincipalPartsSheaf_app_toRationalFunctionPresheaf_app K f _ _

private lemma mem_range_of_toPrincipalPartsSheaf_cst_eq_zero (W : C.Opens) (x : C) (hx : x ∈ W)
    (v : C.functionField)
    (h : (toPrincipalPartsSheaf K f).app (op W) (cst K f W v) = 0) :
    v ∈ Set.range (algebraMap (C.presheaf.stalk x) C.functionField) := by
  set c := (Limits.cokernel.π (toRationalFunctionPresheaf K f)).app (op W) (cst K f W v)
  have h' : (toSheafify (Opens.grothendieckTopology C)
      (Limits.cokernel (toRationalFunctionPresheaf K f)).presheaf).app (op W) c =
      (toSheafify (Opens.grothendieckTopology C)
      (Limits.cokernel (toRationalFunctionPresheaf K f)).presheaf).app (op W) 0 := by
    rwa [map_zero]
  obtain ⟨W', i, hi, hxW'⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology C)
    (toSheafify (Opens.grothendieckTopology C)
      (Limits.cokernel (toRationalFunctionPresheaf K f)).presheaf) c 0 h' x hx
  have hi' :
      (Limits.cokernel.π (toRationalFunctionPresheaf K f)).app (op W') (cst K f W' v) = 0 := by
    have := PresheafOfModules.naturality_apply (Limits.cokernel.π (toRationalFunctionPresheaf K f))
      i.op (cst K f W v)
    exact this.trans (hi.trans (map_zero _))
  obtain ⟨a, ha⟩ := exists_toRationalFunctionPresheaf_app_eq K f _ _ hi'
  have : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  have hv : C.germToFunctionField W' a = v :=
    congr_fun ((toRationalFunctionPresheaf_app_apply K f W' a).symm.trans ha) ⟨⟨⟨x, hxW'⟩⟩⟩
  exact ⟨C.presheaf.germ W' x hxW' a,
    (Scheme.algebraMap_germ_eq_germToFunctionField (X := C) hxW' a).trans hv⟩

/-- `v` represents the global section `s` of `𝒬_C` near `x`: `s = π(v)` on an open `U ∋ x`. -/
private def IsLocalRep (s : (principalPartsSheaf K f).val.obj (op ⊤)) (x : C)
    (v : C.functionField) : Prop :=
  ∃ U : C.Opens, x ∈ U ∧ (principalPartsSheaf K f).val.map (homOfLE le_top : U ⟶ ⊤).op s =
    (toPrincipalPartsSheaf K f).app (op U) (cst K f U v)

private lemma exists_isLocalRep (s : (principalPartsSheaf K f).val.obj (op ⊤)) (x : C) :
    ∃ v, IsLocalRep K f s x v := by
  obtain ⟨W, hW, hxW, v, hv⟩ := exists_toPrincipalPartsSheaf_eq K f ⊤ s x trivial
  exact ⟨v, W, hxW, hv⟩

private lemma toPrincipalPartsSheaf_cst_res {U W : C.Opens} (h : W ≤ U) (v : C.functionField) :
    (principalPartsSheaf K f).val.map (homOfLE h).op
        ((toPrincipalPartsSheaf K f).app (op U) (cst K f U v)) =
      (toPrincipalPartsSheaf K f).app (op W) (cst K f W v) :=
  (PresheafOfModules.naturality_apply (toPrincipalPartsSheaf K f) (homOfLE h).op (cst K f U v)).symm

private lemma isLocalRep_res {s : (principalPartsSheaf K f).val.obj (op ⊤)} {U W : C.Opens}
    (h : W ≤ U) {v : C.functionField}
    (hs : (principalPartsSheaf K f).val.map (homOfLE le_top : U ⟶ ⊤).op s =
      (toPrincipalPartsSheaf K f).app (op U) (cst K f U v)) :
    (principalPartsSheaf K f).val.map (homOfLE le_top : W ⟶ ⊤).op s =
      (toPrincipalPartsSheaf K f).app (op W) (cst K f W v) := by
  rw [← toPrincipalPartsSheaf_cst_res K f h, ← hs]
  exact (principalPartsSheaf K f).val.map_comp_apply (homOfLE le_top : U ⟶ ⊤).op (homOfLE h).op s

private lemma IsLocalRep.sub_mem {s : (principalPartsSheaf K f).val.obj (op ⊤)} {x : C}
    {v v' : C.functionField} (h : IsLocalRep K f s x v) (h' : IsLocalRep K f s x v') :
    v - v' ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
  obtain ⟨U, hxU, hU⟩ := h
  obtain ⟨U', hxU', hU'⟩ := h'
  have e := (isLocalRep_res K f (inf_le_left : U ⊓ U' ≤ U) hU).symm.trans
    (isLocalRep_res K f (inf_le_right : U ⊓ U' ≤ U') hU')
  have : (toPrincipalPartsSheaf K f).app (op (U ⊓ U')) (cst K f (U ⊓ U') (v - v')) = 0 := by
    rw [show cst K f (U ⊓ U') (v - v') = cst K f (U ⊓ U') v - cst K f (U ⊓ U') v' from rfl,
      map_sub, e, sub_self]
  exact mem_range_of_toPrincipalPartsSheaf_cst_eq_zero K f _ x
    (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩) _ this

private lemma IsLocalRep.add {s t : (principalPartsSheaf K f).val.obj (op ⊤)} {x : C}
    {v w : C.functionField} (h : IsLocalRep K f s x v) (h' : IsLocalRep K f t x w) :
    IsLocalRep K f (s + t) x (v + w) := by
  obtain ⟨U, hxU, hU⟩ := h
  obtain ⟨U', hxU', hU'⟩ := h'
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ?_⟩
  rw [map_add, isLocalRep_res K f (inf_le_left : U ⊓ U' ≤ U) hU,
    isLocalRep_res K f (inf_le_right : U ⊓ U' ≤ U') hU']
  exact (map_add (ConcreteCategory.hom ((toPrincipalPartsSheaf K f).app (op (U ⊓ U')))) _ _).symm

private lemma IsLocalRep.smul {s : (principalPartsSheaf K f).val.obj (op ⊤)} {x : C}
    {v : C.functionField} (h : IsLocalRep K f s x v) (r : Γ(C, ⊤)) :
    IsLocalRep K f ((show C.ringCatSheaf.obj.obj (op ⊤) from r) • s) x
      (C.germToFunctionField ⊤ (h := ⟨⟨x, trivial⟩⟩) r * v) := by
  obtain ⟨U, hxU, hU⟩ := h
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty (⊤ : C.Opens) := ⟨⟨x, trivial⟩⟩
  refine ⟨U, hxU, ?_⟩
  rw [PresheafOfModules.map_smul, hU]
  refine
    (map_smul (ConcreteCategory.hom ((toPrincipalPartsSheaf K f).app (op U))) _ _).symm.trans ?_
  congr 1
  funext ⟨_⟩
  change C.germToFunctionField U (C.presheaf.map (homOfLE le_top).op r) * v = _
  rw [germToFunctionField_res]

/-- Every element of `K(C)` lying in `𝒪_{C,y}` is regular on some open neighbourhood of `y`; at
the generic point every element of `K(C)` is regular on a neighbourhood. -/
private lemma exists_germToFunctionField_eq_of_mem (y : C) (v : C.functionField)
    (h : IsClosed ({y} : Set C) → v ∈ (algebraMap (C.presheaf.stalk y) C.functionField).range) :
    ∃ (V : C.Opens) (_ : Nonempty V) (a : Γ(C, V)), y ∈ V ∧ C.germToFunctionField V a = v := by
  by_cases hy : IsClosed ({y} : Set C)
  · obtain ⟨g, rfl⟩ := h hy
    obtain ⟨V, hyV, a, rfl⟩ := C.presheaf.exists_germ_eq (x := y) g
    have : Nonempty V := ⟨⟨y, hyV⟩⟩
    exact ⟨V, inferInstance, a, hyV,
      (Scheme.algebraMap_germ_eq_germToFunctionField (X := C) hyV a).symm⟩
  · have hgen : y = genericPoint C :=
      by_contra fun hne ↦ hy (isClosed_singleton_of_ne_genericPoint K f hne)
    obtain ⟨V, hV, a, ha⟩ := exists_germToFunctionField_eq K f v
    refine ⟨V, hV, a, ?_, ha⟩
    obtain ⟨⟨z, hz⟩⟩ := hV
    rw [hgen]
    exact ((genericPoint_spec C).mem_open_set_iff V.isOpen).2 ⟨z, by simp, hz⟩

/-- A global section of `𝒬_C` all of whose local representatives at closed points are regular
there is zero. -/
private lemma eq_zero_of_isLocalRep_mem_range (s : (principalPartsSheaf K f).val.obj (op ⊤))
    (h : ∀ x : C, IsClosed ({x} : Set C) → ∀ v, IsLocalRep K f s x v →
      v ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range) : s = 0 := by
  have key : ∀ y : C, ∃ W : C.Opens, y ∈ W ∧
      (principalPartsSheaf K f).val.map (homOfLE le_top : W ⟶ ⊤).op s = 0 := by
    intro y
    obtain ⟨v, U, hyU, hU⟩ := exists_isLocalRep K f s y
    obtain ⟨V, hV, a, hyV, ha⟩ :=
      exists_germToFunctionField_eq_of_mem K f y v fun hy ↦ h y hy v ⟨U, hyU, hU⟩
    refine ⟨U ⊓ V, ⟨hyU, hyV⟩, ?_⟩
    rw [isLocalRep_res K f inf_le_left hU, ← ha]
    exact toPrincipalPartsSheaf_cst_germToFunctionField K f _ _ inf_le_right a
  choose W hyW hW using key
  let F : TopCat.Sheaf Ab.{u} C :=
    ⟨(principalPartsSheaf K f).val.presheaf, (principalPartsSheaf K f).isSheaf⟩
  exact F.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ Opens.mem_iSup.2 ⟨y, hyW y⟩) s 0 fun y ↦ (hW y).trans (map_zero _).symm

/-- A global section of `𝒬_C` has a local representative outside `𝒪_{C,x}` at only finitely
many points `x`. -/
private lemma finite_setOf_isLocalRep_notMem (s : (principalPartsSheaf K f).val.obj (op ⊤)) :
    {x : C | ∃ v, IsLocalRep K f s x v ∧
      v ∉ (algebraMap (C.presheaf.stalk x) C.functionField).range}.Finite := by
  have key : ∀ y : C, ∃ U : C.Opens, y ∈ U ∧ ∃ V : C.Opens, (V : Set C).Nonempty ∧
      ∀ x ∈ U, x ∈ V → ∀ w, IsLocalRep K f s x w →
        w ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
    intro y
    obtain ⟨v, U, hyU, hU⟩ := exists_isLocalRep K f s y
    obtain ⟨V, hV, a, ha⟩ := exists_germToFunctionField_eq K f v
    refine ⟨U, hyU, V, ?_, fun x hxU hxV w hw ↦ ?_⟩
    · obtain ⟨⟨z, hz⟩⟩ := hV
      exact ⟨z, hz⟩
    have h1 := hw.sub_mem K f ⟨U, hxU, hU⟩
    have h2 : v ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range :=
      ⟨C.presheaf.germ V x hxV a,
        (Scheme.algebraMap_germ_eq_germToFunctionField (X := C) hxV a).trans ha⟩
    simpa using Subring.add_mem _ h1 h2
  choose U hyU V hV hgood using key
  have := noetherianSpace_of_isCurve K f
  obtain ⟨T, hT⟩ := (NoetherianSpace.isCompact (Set.univ : Set C)).elim_finite_subcover
    (fun y ↦ (U y : Set C)) (fun y ↦ (U y).isOpen) fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyU y⟩
  refine (T.finite_toSet.biUnion fun y _ ↦
    (finite_and_subset_closedPoints_of_isClosed_of_ne_univ K f (V y).isOpen.isClosed_compl
      (Set.compl_ne_univ.2 (hV y))).1).subset ?_
  rintro x ⟨w, hw, hwn⟩
  obtain ⟨y, hyT, hxU⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  exact Set.mem_iUnion₂.2 ⟨y, hyT, fun hxV ↦ hwn (hgood y x hxU hxV w hw)⟩

/-- A finitely supported family `w` of rational functions, supported at closed points, is the
family of local representatives of a global section of `𝒬_C`. -/
private lemma exists_forall_isLocalRep (w : C → C.functionField) (hw : {x | w x ≠ 0}.Finite)
    (hcl : ∀ x, w x ≠ 0 → IsClosed ({x} : Set C)) :
    ∃ s : (principalPartsSheaf K f).val.obj (op ⊤), ∀ x, IsLocalRep K f s x (w x) := by
  classical
  have hreg : ∀ y ∈ {x | w x ≠ 0}, ∃ (V : C.Opens) (_ : Nonempty V) (a : Γ(C, V)),
      C.germToFunctionField V a = w y := fun y _ ↦ exists_germToFunctionField_eq K f (w y)
  choose V hV a ha using hreg
  have hVc (y) (hy : y ∈ {x | w x ≠ 0}) :=
    finite_and_subset_closedPoints_of_isClosed_of_ne_univ K f (V y hy).isOpen.isClosed_compl
      (Set.compl_ne_univ.2 (by obtain ⟨⟨z, hz⟩⟩ := hV y hy; exact ⟨z, hz⟩))
  set B : Set C := {x | w x ≠ 0} ∪ ⋃ (y) (hy : y ∈ {x | w x ≠ 0}), ((V y hy : Set C)ᶜ)
  have hBfin : B.Finite := hw.union (hw.biUnion' fun y hy ↦ (hVc y hy).1)
  have hBcl : ∀ z ∈ B, IsClosed ({z} : Set C) := by
    rintro z (hz | hz)
    · exact hcl z hz
    · obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 hz
      exact (hVc y hy).2 hz
  have hBreg : ∀ (y : C) (W : C.Opens), (W : Set C) ⊆ Bᶜ →
      (toPrincipalPartsSheaf K f).app (op W) (cst K f W (w y)) = 0 := by
    intro y W hW
    by_cases hy : w y = 0
    · rw [hy]
      exact map_zero (ConcreteCategory.hom ((toPrincipalPartsSheaf K f).app (op W)))
    · have := hV y hy
      rw [← ha y hy]
      refine toPrincipalPartsSheaf_cst_germToFunctionField K f W _ (fun z hz ↦ ?_) _
      by_contra hzV
      exact hW hz (Or.inr (Set.mem_iUnion₂.2 ⟨y, hy, hzV⟩))
  have hopen (y : C) : IsOpen ((B \ {y})ᶜ) := by
    rw [isOpen_compl_iff]
    have := (hBfin.sdiff (t := {y})).isClosed_biUnion (f := fun z ↦ ({z} : Set C))
      fun z hz ↦ hBcl z hz.1
    rwa [Set.biUnion_of_singleton] at this
  let U : C → C.Opens := fun y ↦ ⟨(B \ {y})ᶜ, hopen y⟩
  have hyU (y : C) : y ∈ U y := fun h ↦ h.2 rfl
  let F : TopCat.Sheaf Ab.{u} C :=
    ⟨(principalPartsSheaf K f).val.presheaf, (principalPartsSheaf K f).isSheaf⟩
  let sf : ∀ y, ToType (F.1.obj (op (U y))) := fun y ↦
    (toPrincipalPartsSheaf K f).app (op (U y)) (cst K f _ (w y))
  have hcompat : TopCat.Presheaf.IsCompatible F.1 U sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    have hsub : ((U i ⊓ U j : C.Opens) : Set C) ⊆ Bᶜ := by
      rintro z ⟨hzi, hzj⟩ hzB
      have h1 : z = i := by_contra fun h ↦ hzi ⟨hzB, h⟩
      have h2 : z = j := by_contra fun h ↦ hzj ⟨hzB, h⟩
      exact hij (h1.symm.trans h2)
    refine ((toPrincipalPartsSheaf_cst_res K f inf_le_left (w i)).trans (hBreg i _ hsub)).trans
      ((toPrincipalPartsSheaf_cst_res K f inf_le_right (w j)).trans (hBreg j _ hsub)).symm
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ Opens.mem_iSup.2 ⟨y, hyU y⟩) sf hcompat
  exact ⟨s, fun x ↦ ⟨U x, hyU x, hs x⟩⟩

end

/-- **Principal parts.** Let `f : C ⟶ Spec K` be a curve over a field `K` and
`𝒬_C = principalPartsSheaf K f`. There is a `K`-linear isomorphism
`θ : Γ(C, 𝒬_C) ≃ₗ[K] ⨁_{x closed} K(C)/𝒪_{C,x}` sending a global section `s` to its family of
germs: if `x` is a closed point, `U ∋ x` an open and `v ∈ K(C)` with `s|_U` the image of the
constant section `v` of `𝒦_C(U)` under `𝒦_C → 𝒬_C`, then `θ s x = v mod 𝒪_{C,x}`. -/
@[faltings "lem_ff_principal_parts"]
theorem exists_linearEquiv_principalPartsSheaf_sections (K : Type u) [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsCurve K f] :
    letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
    letI : Module K ((principalPartsSheaf K f).val.obj (op ⊤)) :=
      Module.compHom _ (show K →+* C.ringCatSheaf.obj.obj (op ⊤) from
        ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    let π : rationalFunctionPresheaf K f ⟶
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 C.ringCatSheaf.obj)).obj
          (principalPartsSheaf K f) :=
      Limits.cokernel.π _ ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 C.ringCatSheaf.obj)).unit.app _
    ∃ θ : (principalPartsSheaf K f).val.obj (op ⊤) ≃ₗ[K] ⨁ x : closedPoints C,
        C.functionField ⧸
          Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField)),
      ∀ (s : (principalPartsSheaf K f).val.obj (op ⊤)) (x : closedPoints C) (U : C.Opens)
        (hx : x.1 ∈ U) (v : C.functionField),
        (principalPartsSheaf K f).val.map (homOfLE le_top : U ⟶ ⊤).op s =
          π.app (op U) (show (rationalFunctionPresheaf K f).obj (op U) from fun _ ↦ v) →
        θ s x = Submodule.Quotient.mk v := by
  intro π
  classical
  let φ : K →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom
  let : Algebra K C.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
  let : Module K ((principalPartsSheaf K f).val.obj (op ⊤)) :=
    Module.compHom _ (show K →+* C.ringCatSheaf.obj.obj (op ⊤) from φ)
  choose rep hrep using fun (s : (principalPartsSheaf K f).val.obj (op ⊤)) (x : C) ↦
    exists_isLocalRep K f s x
  let Q : closedPoints C → Type u := fun x ↦ C.functionField ⧸
    Submodule.span K (Set.range (algebraMap (C.presheaf.stalk x.1) C.functionField))
  have hmk (s) (x : closedPoints C) (v) (h : IsLocalRep K f s x.1 v) :
      (Submodule.Quotient.mk (rep s x.1) : Q x) = Submodule.Quotient.mk v :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ((hrep s x.1).sub_mem K f h))
  have hfin (s : (principalPartsSheaf K f).val.obj (op ⊤)) :
      {x : closedPoints C | (Submodule.Quotient.mk (rep s x.1) : Q x) ≠ 0}.Finite := by
    refine ((finite_setOf_isLocalRep_notMem K f s).preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    refine ⟨rep s x.1, hrep s x.1, fun hmem ↦ hx ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hmem)
  let θf : (principalPartsSheaf K f).val.obj (op ⊤) → ⨁ x : closedPoints C, Q x := fun s ↦
    DFinsupp.mk (hfin s).toFinset fun x ↦ Submodule.Quotient.mk (rep s x.1.1)
  have hθf (s) (x : closedPoints C) : θf s x = Submodule.Quotient.mk (rep s x.1) := by
    simp only [θf, DFinsupp.mk_apply]
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
      exact h.symm
  have hK (x : C) (k : K) :
      algebraMap K C.functionField k ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range := by
    have : Nonempty (⊤ : C.Opens) := ⟨⟨x, trivial⟩⟩
    exact ⟨C.presheaf.germ ⊤ x trivial (φ k),
      Scheme.algebraMap_germ_eq_germToFunctionField (X := C) (U := ⊤) (x := x) trivial (φ k)⟩
  let θ : (principalPartsSheaf K f).val.obj (op ⊤) →ₗ[K] ⨁ x : closedPoints C, Q x :=
    { toFun := θf
      map_add' := fun s t ↦ by
        ext x
        rw [DirectSum.add_apply, hθf, hθf, hθf,
          hmk _ x _ ((hrep s x.1).add K f (hrep t x.1)), Submodule.Quotient.mk_add]
      map_smul' := fun k s ↦ by
        ext x
        rw [RingHom.id_apply, DirectSum.smul_apply, hθf, hθf]
        refine (hmk (k • s) x _ ((hrep s x.1).smul K f (φ k))).trans ?_
        rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]
        rfl }
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    refine eq_zero_of_isLocalRep_mem_range K f s fun x hx v hv ↦ ?_
    have h0 : (Submodule.Quotient.mk v : Q ⟨x, hx⟩) = 0 := by
      rw [← hmk s ⟨x, hx⟩ v hv, ← hθf]
      exact DFunLike.congr_fun hs ⟨x, hx⟩
    exact mem_range_of_mem_span (hK x) ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have hsurj : Function.Surjective θ := by
    intro d
    obtain ⟨w, hwfin, hwS, hwd⟩ := exists_lift_directSum _ d
    obtain ⟨s, hs⟩ := exists_forall_isLocalRep K f w hwfin hwS
    refine ⟨s, DFinsupp.ext fun x ↦ ?_⟩
    change θf s x = d x
    rw [hθf, hmk s x _ (hs x.1), hwd]
  refine ⟨LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩, fun s x U hx v h ↦ ?_⟩
  change θf s x = _
  rw [hθf]
  exact hmk s x v ⟨U, hx, h⟩

end Faltings.FunctionField

end
