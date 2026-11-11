module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Spreading out an abelian variety over a number field

Let `A` be an abelian variety over a number field `k`. Then `A` spreads out to an abelian scheme
over a dense open of `Spec 𝓞 k`: there are a nonzero integer `N` and an abelian scheme `𝒜` over
`𝓞 k[1/N]` whose generic fibre `𝒜 ×_{𝓞 k[1/N]} Spec k` is isomorphic to `A` as a group scheme
over `k`.

The scheme `Spec k` is the limit of the affine schemes `Spec 𝓞 k[1/n!]`, whose transition maps
are affine and which are Noetherian, hence quasi-compact and quasi-separated. The structure
morphism of `A` is of finite presentation, so `A` is the base change of a scheme `X` of finite
presentation over some stage (Stacks 01ZM (1)). Its multiplication, unit and inverse descend to
morphisms over a later stage (Stacks 01ZM (2)), and the finitely many group axioms, which hold
after base change to `Spec k`, hold at a later stage still (Stacks 01ZM (3)). The group scheme `A`
is smooth over `k`, being geometrically reduced and of finite type, and proper; both properties
descend to a stage (Stacks 0C0C, 081F). Over the integral scheme `Spec 𝓞 k[1/n!]` the generic
fibre of `X` is geometrically irreducible, so the fibres are geometrically irreducible over a
nonempty open (Stacks 0559); that open contains a basic open `D(g)`, and `g` becomes a unit in
`𝓞 k[1/m!]` once `m!` is divisible by the norm of its numerator, so at that stage every fibre is
geometrically irreducible. Smooth morphisms have geometrically reduced fibres (Stacks 056T), so
all fibres are geometrically integral and the model is an abelian scheme.

## Main results

* `Faltings.exists_isAbelianScheme_localizationAway_pullback_iso`: an abelian variety over a
  number field spreads out to an abelian scheme over `𝓞 k[1/N]` for some nonzero integer `N`.

## Implementation notes

The ring `𝓞 k[1/N]` is the subring `Localization.subalgebra k (Submonoid.powers (N : 𝓞 k)) _`
of `k`: a localization of `𝓞 k` away from `N`, which as a subring of `k` comes with its inclusion
into `k`. The generic fibre is the base change along `Spec.map` of that inclusion, with the group
structure carried along by `(CategoryTheory.Over.pullback _).mapGrp`, and the isomorphism is
taken in `CategoryTheory.Grp (CategoryTheory.Over (Spec k))`, i.e. it is an isomorphism of group
schemes over `k`. Abelian varieties and abelian schemes are spelled out exactly as in
`Faltings.HasGoodReduction`: an abelian variety over `k` is a group object of
`Over (Spec k)` whose structure morphism is proper and geometrically integral; an abelian scheme
over `W` is a group object of `Over W` whose structure morphism is flat, proper and locally of
finite presentation, all of whose fibres `𝒜 ×_W Spec κ(w)` are proper and geometrically
integral over `κ(w)`.

In the proof, the rings `𝓞 k[1/N]` are indexed by the factorials `N = n!`, which are cofinal
among the nonzero integers ordered by divisibility; the index category is then the thin category
`(ULift ℕ)ᵒᵖ`. A group structure is carried along the descent as data `(μ, η, ι)` on the model
together with an identification `φ` of its base change with `A` intertwining the transported data
with the group law of `A`. The intertwining conditions are stable under any further base change,
because base change along a composite agrees with the composite of base changes through a natural
isomorphism, which is automatically monoidal for cartesian monoidal structures; the group axioms
for data transported by a monoidal functor are the images of the group axioms under the functor.
Smoothness of `A` over `k` is `AlgebraicGeometry.smooth_of_grpObj`, a geometrically reduced group
scheme locally of finite type over a field being smooth; this replaces the appeal to
characteristic zero (Stacks 047N).

## References

* [The Stacks Project][stacks], Tags 01ZM, 081F, 0C0C, 0559, 056T
* [J. S. Milne, *Abelian varieties*][milneAV]
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField Opposite
open Functor.LaxMonoidal

namespace Faltings

section GrpData

variable {C D : Type*} [Category* C] [CartesianMonoidalCategory C] [Category* D]
  [CartesianMonoidalCategory D]

/-- The five equations making `(m, u, v)` a group object structure on `Y`. -/
private def IsGrpData {Y : C} (m : Y ⊗ Y ⟶ Y) (u : 𝟙_ C ⟶ Y) (v : Y ⟶ Y) : Prop :=
  u ▷ Y ≫ m = (λ_ Y).hom ∧ Y ◁ u ≫ m = (ρ_ Y).hom ∧
    m ▷ Y ≫ m = (α_ Y Y Y).hom ≫ Y ◁ m ≫ m ∧
    lift v (𝟙 Y) ≫ m = toUnit Y ≫ u ∧ lift (𝟙 Y) v ≫ m = toUnit Y ≫ u

/-- The group object structure given by data satisfying the group axioms. -/
private abbrev IsGrpData.grpObj {Y : C} {m : Y ⊗ Y ⟶ Y} {u : 𝟙_ C ⟶ Y} {v : Y ⟶ Y}
    (h : IsGrpData m u v) : GrpObj Y where
  one := u
  mul := m
  inv := v
  one_mul := h.1
  mul_one := h.2.1
  mul_assoc := h.2.2.1
  left_inv := h.2.2.2.1
  right_inv := h.2.2.2.2

/-- The structure maps of a group object satisfy the group axioms. -/
private lemma isGrpData_of_grpObj (Y : C) [GrpObj Y] : IsGrpData μ[Y] η[Y] ι[Y] :=
  ⟨MonObj.one_mul Y, MonObj.mul_one Y, MonObj.mul_assoc Y, GrpObj.left_inv Y, GrpObj.right_inv Y⟩

variable (F : C ⥤ D) [F.Monoidal]

/-- The group axioms for the image of data under a monoidal functor are the images of the
group axioms. -/
private lemma isGrpData_map_iff {Y : C} (m : Y ⊗ Y ⟶ Y) (u : 𝟙_ C ⟶ Y) (v : Y ⟶ Y) :
    IsGrpData («μ» F Y Y ≫ F.map m) (ε F ≫ F.map u) (F.map v) ↔
      (F.map (u ▷ Y ≫ m) = F.map (λ_ Y).hom ∧ F.map (Y ◁ u ≫ m) = F.map (ρ_ Y).hom ∧
        F.map (m ▷ Y ≫ m) = F.map ((α_ Y Y Y).hom ≫ Y ◁ m ≫ m) ∧
        F.map (lift v (𝟙 Y) ≫ m) = F.map (toUnit Y ≫ u) ∧
        F.map (lift (𝟙 Y) v ≫ m) = F.map (toUnit Y ≫ u)) := by
  have h1 : (ε F ≫ F.map u) ▷ F.obj Y ≫ «μ» F Y Y ≫ F.map m =
      (ε F ▷ F.obj Y ≫ «μ» F (𝟙_ C) Y) ≫ F.map (u ▷ Y ≫ m) := by
    simp [μ_natural_left_assoc]
  have h1' : (λ_ (F.obj Y)).hom =
      (ε F ▷ F.obj Y ≫ «μ» F (𝟙_ C) Y) ≫ F.map (λ_ Y).hom := by
    simp [left_unitality]
  have h2 : F.obj Y ◁ (ε F ≫ F.map u) ≫ «μ» F Y Y ≫ F.map m =
      (F.obj Y ◁ ε F ≫ «μ» F Y (𝟙_ C)) ≫ F.map (Y ◁ u ≫ m) := by
    simp [μ_natural_right_assoc]
  have h2' : (ρ_ (F.obj Y)).hom =
      (F.obj Y ◁ ε F ≫ «μ» F Y (𝟙_ C)) ≫ F.map (ρ_ Y).hom := by
    simp [right_unitality]
  have h3 : («μ» F Y Y ≫ F.map m) ▷ F.obj Y ≫ «μ» F Y Y ≫ F.map m =
      («μ» F Y Y ▷ F.obj Y ≫ «μ» F (Y ⊗ Y) Y) ≫ F.map (m ▷ Y ≫ m) := by
    simp [μ_natural_left_assoc]
  have h3' : (α_ (F.obj Y) (F.obj Y) (F.obj Y)).hom ≫ F.obj Y ◁ («μ» F Y Y ≫ F.map m) ≫
      «μ» F Y Y ≫ F.map m =
      («μ» F Y Y ▷ F.obj Y ≫ «μ» F (Y ⊗ Y) Y) ≫
        F.map ((α_ Y Y Y).hom ≫ Y ◁ m ≫ m) := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc,
      Functor.map_comp]
    rw [associativity_assoc]
  have h4 : lift (F.map v) (𝟙 (F.obj Y)) ≫ «μ» F Y Y ≫ F.map m =
      F.map (lift v (𝟙 Y) ≫ m) := by
    rw [← F.map_id, Functor.Monoidal.lift_μ_assoc, ← F.map_comp]
  have h5 : lift (𝟙 (F.obj Y)) (F.map v) ≫ «μ» F Y Y ≫ F.map m =
      F.map (lift (𝟙 Y) v ≫ m) := by
    rw [← F.map_id, Functor.Monoidal.lift_μ_assoc, ← F.map_comp]
  have h45 : toUnit (F.obj Y) ≫ ε F ≫ F.map u = F.map (toUnit Y ≫ u) := by
    rw [Functor.Monoidal.toUnit_ε_assoc, ← F.map_comp]
  unfold IsGrpData
  rw [h1, h1', h2, h2', h3, h3', h4, h5, h45, cancel_epi, cancel_epi, cancel_epi]

/-- Group axioms are preserved by monoidal functors. -/
private lemma IsGrpData.map {Y : C} {m : Y ⊗ Y ⟶ Y} {u : 𝟙_ C ⟶ Y} {v : Y ⟶ Y}
    (h : IsGrpData m u v) :
    IsGrpData («μ» F Y Y ≫ F.map m) (ε F ≫ F.map u) (F.map v) :=
  (isGrpData_map_iff F m u v).2
    ⟨congrArg F.map h.1, congrArg F.map h.2.1, congrArg F.map h.2.2.1,
      congrArg F.map h.2.2.2.1, congrArg F.map h.2.2.2.2⟩

/-- Data on `Y` that an isomorphism carries to a group object structure satisfies the group
axioms. -/
private lemma isGrpData_of_iso {Y Z : D} [GrpObj Z] (φ : Y ≅ Z) {m : Y ⊗ Y ⟶ Y} {u : 𝟙_ D ⟶ Y}
    {v : Y ⟶ Y} (hm : m ≫ φ.hom = (φ.hom ⊗ₘ φ.hom) ≫ μ[Z]) (hu : u ≫ φ.hom = η[Z])
    (hv : v ≫ φ.hom = φ.hom ≫ ι[Z]) : IsGrpData m u v := by
  let : GrpObj Y := GrpObj.ofIso φ.symm
  have hm' : m = μ[Y] := by
    change m = (φ.hom ⊗ₘ φ.hom) ≫ μ[Z] ≫ φ.inv
    rw [← reassoc_of% hm]; simp
  have hu' : u = η[Y] := by
    change u = η[Z] ≫ φ.inv
    rw [← hu]; simp
  have hv' : v = ι[Y] := by
    change v = φ.hom ≫ ι[Z] ≫ φ.inv
    rw [← reassoc_of% hv]; simp
  rw [hm', hu', hv']
  exact isGrpData_of_grpObj Y

variable {C' : Type*} [Category* C'] [CartesianMonoidalCategory C']

/-- `φ` intertwines the multiplication `m` transported by `F` with that of `Z`. -/
@[expose] public def MulCompat {Y : C} {Z : D} [GrpObj Z] (m : Y ⊗ Y ⟶ Y) (φ : F.obj Y ≅ Z) :
    Prop :=
  «μ» F Y Y ≫ F.map m ≫ φ.hom = (φ.hom ⊗ₘ φ.hom) ≫ μ[Z]

/-- `φ` intertwines the unit `u` transported by `F` with that of `Z`. -/
private def OneCompat {Y : C} {Z : D} [GrpObj Z] (u : 𝟙_ C ⟶ Y) (φ : F.obj Y ≅ Z) : Prop :=
  ε F ≫ F.map u ≫ φ.hom = η[Z]

/-- `φ` intertwines the inverse `v` transported by `F` with that of `Z`. -/
@[expose] public def InvCompat {Y : C} {Z : D} [GrpObj Z] (v : Y ⟶ Y) (φ : F.obj Y ≅ Z) : Prop :=
  F.map v ≫ φ.hom = φ.hom ≫ ι[Z]

/-- Data whose transport is intertwined with a group law satisfies the group axioms after
transport. -/
private lemma isGrpData_of_compat {Y : C} {Z : D} [GrpObj Z] {m : Y ⊗ Y ⟶ Y} {u : 𝟙_ C ⟶ Y}
    {v : Y ⟶ Y} {φ : F.obj Y ≅ Z} (hm : MulCompat F m φ) (hu : OneCompat F u φ)
    (hv : InvCompat F v φ) : IsGrpData («μ» F Y Y ≫ F.map m) (ε F ≫ F.map u) (F.map v) :=
  isGrpData_of_iso φ (by simpa [MulCompat] using hm) (by simpa [OneCompat] using hu) hv

section Transport

variable {F} (T : C ⥤ C') (H' : C' ⥤ D) [T.Monoidal] [H'.Monoidal] (κ : T ⋙ H' ≅ F)
  {Y : C} {Z : D} [GrpObj Z] (φ : F.obj Y ≅ Z)

/-- A multiplication descended along `T` is intertwined with the group law of `Z`. -/
lemma mulCompat_of_map_eq (g : T.obj (Y ⊗ Y) ⟶ T.obj Y)
    (hg : H'.map g = κ.hom.app (Y ⊗ Y) ≫
      (Functor.OplaxMonoidal.δ F Y Y ≫ (φ.hom ⊗ₘ φ.hom) ≫ μ[Z] ≫ φ.inv) ≫ κ.inv.app Y) :
    MulCompat H' («μ» T Y Y ≫ g) (κ.app Y ≪≫ φ) := by
  have h := NatTrans.IsMonoidal.of_cartesianMonoidalCategory _ _ κ.hom
  have ht := NatTrans.IsMonoidal.tensor (τ := κ.hom) Y Y
  rw [Functor.LaxMonoidal.comp_μ] at ht
  simp only [MulCompat, Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc, hg,
    Iso.inv_hom_id_app_assoc, ← tensorHom_comp_tensorHom]
  rw [reassoc_of% ht]
  simp

/-- A unit descended along `T` is intertwined with the unit of `Z`. -/
private lemma oneCompat_of_map_eq (g : T.obj (𝟙_ C) ⟶ T.obj Y)
    (hg : H'.map g = κ.hom.app (𝟙_ C) ≫
      (Functor.OplaxMonoidal.η F ≫ η[Z] ≫ φ.inv) ≫ κ.inv.app Y) :
    OneCompat H' (ε T ≫ g) (κ.app Y ≪≫ φ) := by
  have h := NatTrans.IsMonoidal.of_cartesianMonoidalCategory _ _ κ.hom
  have ht := NatTrans.IsMonoidal.unit (τ := κ.hom)
  rw [Functor.LaxMonoidal.comp_ε] at ht
  simp only [OneCompat, Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc, hg,
    Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% ht]
  simp

omit [CartesianMonoidalCategory C] [F.Monoidal] [CartesianMonoidalCategory C'] in
/-- An inverse descended along `T` is intertwined with the inverse of `Z`. -/
lemma invCompat_of_map_eq (g : T.obj Y ⟶ T.obj Y)
    (hg : H'.map g = κ.hom.app Y ≫ (φ.hom ≫ ι[Z] ≫ φ.inv) ≫ κ.inv.app Y) :
    InvCompat H' g (κ.app Y ≪≫ φ) := by
  simp [InvCompat, hg]

/-- The intertwining of the multiplication persists under further base change. -/
lemma MulCompat.transport {m : Y ⊗ Y ⟶ Y} (hm : MulCompat F m φ) :
    MulCompat H' («μ» T Y Y ≫ T.map m) (κ.app Y ≪≫ φ) := by
  refine mulCompat_of_map_eq T H' κ φ _ ?_
  have : F.map m = Functor.OplaxMonoidal.δ F Y Y ≫ (φ.hom ⊗ₘ φ.hom) ≫ μ[Z] ≫ φ.inv := by
    unfold MulCompat at hm
    rw [← reassoc_of% hm]; simp
  rw [← this]
  simp

/-- The intertwining of the unit persists under further base change. -/
private lemma OneCompat.transport {u : 𝟙_ C ⟶ Y} (hu : OneCompat F u φ) :
    OneCompat H' (ε T ≫ T.map u) (κ.app Y ≪≫ φ) := by
  refine oneCompat_of_map_eq T H' κ φ _ ?_
  have : F.map u = Functor.OplaxMonoidal.η F ≫ η[Z] ≫ φ.inv := by
    rw [← hu]; simp
  rw [← this]
  simp

omit [CartesianMonoidalCategory C] [F.Monoidal] [CartesianMonoidalCategory C'] in
/-- The intertwining of the inverse persists under further base change. -/
private lemma InvCompat.transport {v : Y ⟶ Y} (hv : InvCompat F v φ) :
    InvCompat H' (T.map v) (κ.app Y ≪≫ φ) := by
  refine invCompat_of_map_eq T H' κ φ _ ?_
  have : F.map v = φ.hom ≫ ι[Z] ≫ φ.inv := by
    rw [← reassoc_of% hv]; simp
  rw [← this]
  simp

end Transport

end GrpData

noncomputable section Stages

variable (k : Type u) [Field k] [NumberField k]

/-- The ring `𝓞 k[1/N]`, as a subring of `k`. -/
private abbrev locAway (N : ℤ) (hN : N ≠ 0) : Subalgebra (𝓞 k) k :=
  Localization.subalgebra k (Submonoid.powers (N : 𝓞 k))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.cast_ne_zero.mpr hN))

variable {k} in
/-- The elements of `𝓞 k[1/N]` are the `a / N ^ j` with `a ∈ 𝓞 k`. -/
private lemma mem_locAway {N : ℤ} {hN : N ≠ 0} {x : k} :
    x ∈ locAway k N hN ↔ ∃ (a : 𝓞 k) (j : ℕ), x = algebraMap (𝓞 k) k a * ((N : k) ^ j)⁻¹ := by
  rw [locAway, ← Localization.subalgebra.ofField_eq]
  change (∃ (a s : 𝓞 k) (_ : s ∈ Submonoid.powers (N : 𝓞 k)),
    x = algebraMap (𝓞 k) k a * (algebraMap (𝓞 k) k s)⁻¹) ↔ _
  constructor
  · rintro ⟨a, s, ⟨j, rfl⟩, rfl⟩
    exact ⟨a, j, by simp⟩
  · rintro ⟨a, j, rfl⟩
    exact ⟨a, _, ⟨j, rfl⟩, by simp⟩

/-- `𝓞 k[1/N] ⊆ 𝓞 k[1/M]` when `N ∣ M`. -/
private lemma locAway_mono {N M : ℤ} {hN : N ≠ 0} {hM : M ≠ 0} (h : N ∣ M) :
    locAway k N hN ≤ locAway k M hM := by
  obtain ⟨c, rfl⟩ := h
  intro x hx
  obtain ⟨a, j, rfl⟩ := mem_locAway.1 hx
  refine mem_locAway.2 ⟨a * (c : 𝓞 k) ^ j, j, ?_⟩
  have hc : (c : k) ≠ 0 := by
    rintro h0; apply hM; exact_mod_cast (show ((N * c : ℤ) : k) = 0 by push_cast; rw [h0, mul_zero])
  simp only [map_mul, map_pow, map_intCast, Int.cast_mul, mul_pow, mul_inv]
  field_simp

variable {k} in
/-- A nonzero algebraic integer has nonzero norm. -/
private lemma absNorm_span_singleton_ne_zero {a : 𝓞 k} (ha : a ≠ 0) :
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) ≠ 0 := by
  simpa [Ideal.absNorm_eq_zero_iff] using ha

variable {k} in
/-- The inverse of a nonzero `a ∈ 𝓞 k` lies in `𝓞 k[1/M]` once `M` is a multiple of the norm
of `a`, itself a multiple of `a`. -/
private lemma inv_mem_locAway {a : 𝓞 k} (ha : a ≠ 0) {M : ℤ} {hM : M ≠ 0}
    (h : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) ∣ M) :
    (algebraMap (𝓞 k) k a)⁻¹ ∈ locAway k M hM := by
  refine locAway_mono k (hN := absNorm_span_singleton_ne_zero ha) h ?_
  obtain ⟨c, hc⟩ : a ∣ (Ideal.absNorm (Ideal.span {a}) : 𝓞 k) :=
    Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)
  have hMk : (((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) : k) =
      algebraMap (𝓞 k) k a * algebraMap (𝓞 k) k c := by
    rw [← map_mul, ← hc]; simp
  have hMk0 : (((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) : k) ≠ 0 := by
    exact_mod_cast absNorm_span_singleton_ne_zero ha
  rw [hMk, mul_ne_zero_iff] at hMk0
  refine mem_locAway.2 ⟨c, 1, ?_⟩
  rw [pow_one, hMk]
  field_simp [hMk0.1, hMk0.2]

/-- Every element of `k` lies in `𝓞 k[1/M]` for some nonzero `M`: write it as `a / b` and
take for `M` the norm of `b`. -/
private lemma exists_mem_locAway (x : k) : ∃ (M : ℕ) (hM : (M : ℤ) ≠ 0), x ∈ locAway k M hM := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 k) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨_, absNorm_span_singleton_ne_zero hb0, ?_⟩
  rw [div_eq_mul_inv]
  exact mul_mem (Subalgebra.algebraMap_mem _ a) (inv_mem_locAway hb0 dvd_rfl)

/-- Factorials are nonzero integers. -/
private lemma factorial_ne_zero (n : ℕ) : ((n.factorial : ℕ) : ℤ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

/-- The rings `𝓞 k[1/n!]`, an increasing family of subrings of `k`. -/
private def stageRing : ULift.{u} ℕ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (locAway k _ (factorial_ne_zero n.down))
  map {m n} h := CommRingCat.ofHom (Subalgebra.inclusion (locAway_mono k
    (Int.natCast_dvd_natCast.2
      (Nat.factorial_dvd_factorial (show m.down ≤ n.down from h.le))))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusions `𝓞 k[1/n!] → k`. -/
private def stageCocone : Cocone (stageRing k) :=
  Cocone.mk (CommRingCat.of k)
    { app n := CommRingCat.ofHom (algebraMap (locAway k _ (factorial_ne_zero n.down)) k) }

/-- `k` is the union of the rings `𝓞 k[1/n!]`. -/
private def isColimitStageCocone : IsColimit (stageCocone k) := by
  have : ReflectsColimitsOfShape (ULift.{u} ℕ) (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨M, hM, hx⟩ := exists_mem_locAway k x
    have hle : locAway k M hM ≤ locAway k _ (factorial_ne_zero M) := by
      refine locAway_mono k (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial ?_ le_rfl))
      exact Nat.pos_of_ne_zero (by exact_mod_cast hM)
    exact ⟨ULift.up M, (⟨x, hle hx⟩ : locAway k _ (factorial_ne_zero M)), rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [show x = y from Subtype.ext h]⟩

/-- The schemes `Spec 𝓞 k[1/n!]`. -/
private def stageDiagram : (ULift.{u} ℕ)ᵒᵖ ⥤ Scheme.{u} := (stageRing k).op ⋙ Scheme.Spec

/-- `Spec k` over the schemes `Spec 𝓞 k[1/n!]`. -/
private abbrev stageCone : Cone (stageDiagram k) where
  pt := Spec (CommRingCat.of k)
  π := (Scheme.Spec.mapCone (stageCocone k).op).π

/-- `Spec k` is the limit of the schemes `Spec 𝓞 k[1/n!]`. -/
private def isLimitStageCone : IsLimit (stageCone k) :=
  isLimitOfPreserves Scheme.Spec (isColimitStageCocone k).op

end Stages

section Descent

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Base change from a stage to a later one, followed by base change to the limit, is base
change to the limit. -/
@[expose] public noncomputable def pullbackCompIso {i j : I} (e : j ⟶ i) :
    Over.pullback (D.map e) ⋙ Over.pullback (c.π.app j) ≅ Over.pullback (c.π.app i) :=
  NatIso.ofComponents (fun X ↦ overPullbackCompIso (D.map e) (c.π.app j) (c.π.app i) (c.w e) X)
    (fun f ↦ (overPullbackCompIso_naturality _ _ _ _ f).symm)

/-- The fibre product of two schemes of finite presentation over `S` is of finite presentation
over `S`. -/
lemma finitePresentation_tensor {S : Scheme.{u}} {X Y : Over S}
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    FinitePresentation (X ⊗ Y).hom := by
  obtain ⟨_, _, _⟩ := hX
  obtain ⟨_, _, _⟩ := hY
  change FinitePresentation (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The base `S` is of finite presentation over itself. -/
private lemma finitePresentation_unit (S : Scheme.{u}) :
    FinitePresentation (𝟙_ (Over S)).hom :=
  ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 S)), inferInstanceAs (QuasiCompact (𝟙 S)),
    inferInstanceAs (QuasiSeparated (𝟙 S))⟩

/-- Finite presentation is stable under base change. -/
lemma finitePresentation_pullback {S S' : Scheme.{u}} (g : S' ⟶ S) {X : Over S}
    (hX : FinitePresentation X.hom) : FinitePresentation ((Over.pullback g).obj X).hom := by
  obtain ⟨_, _, _⟩ := hX
  change FinitePresentation (Limits.pullback.snd X.hom g)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- Stacks 01ZM (2), with the canonical identifications. -/
lemma exists_map_eq (hc : IsLimit c) {i : I} {X Y : Over (D.obj i)}
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y),
      (Over.pullback (c.π.app j)).map g =
        (pullbackCompIso D c e).hom.app X ≫ f ≫ (pullbackCompIso D c e).inv.app Y := by
  obtain ⟨j, e, g, α, β, hα, hβ, h⟩ := exists_morphism_after_baseChange D c hc i X Y hX hY f
  have hα' := iso_eq_overPullbackCompIso _ _ _ (c.w e) X α hα
  have hβ' := iso_eq_overPullbackCompIso _ _ _ (c.w e) Y β hβ
  refine ⟨j, e, g, ?_⟩
  have : (Over.pullback (c.π.app j)).map g = α.hom ≫ f ≫ β.inv := by
    rw [reassoc_of% h]; simp
  rw [this, hα', hβ']
  rfl

/-- An equality of base changes to a stage persists at later stages. -/
private lemma pullback_map_eq_comp {i j j' : I} (e : j ⟶ i) (e' : j' ⟶ j) {X Y : Over (D.obj i)}
    {f g : X ⟶ Y} (h : (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g) :
    (Over.pullback (D.map (e' ≫ e))).map f = (Over.pullback (D.map (e' ≫ e))).map g := by
  have hc : D.map e' ≫ D.map e = D.map (e' ≫ e) := (D.map_comp _ _).symm
  rw [← cancel_epi (overPullbackCompIso (D.map e) (D.map e') _ hc X).hom,
    overPullbackCompIso_naturality, overPullbackCompIso_naturality, h]

/-- A property of the maps to a stage that persists at later stages. -/
private def UpClosed {i : I} (P : ∀ j : I, (j ⟶ i) → Prop) : Prop :=
  ∀ (j j' : I) (e : j ⟶ i) (e' : j' ⟶ j), P j e → P j' (e' ≫ e)

/-- Two properties persisting at later stages persist together. -/
private lemma UpClosed.and {i : I} {P Q : ∀ j : I, (j ⟶ i) → Prop} (hP : UpClosed P)
    (hQ : UpClosed Q) : UpClosed (fun j e ↦ P j e ∧ Q j e) :=
  fun j j' e e' h ↦ ⟨hP j j' e e' h.1, hQ j j' e e' h.2⟩

/-- Equality of base changes of two morphisms persists at later stages. -/
private lemma upClosed_map_eq {i : I} {X Y : Over (D.obj i)} (f g : X ⟶ Y) :
    UpClosed (fun j (e : j ⟶ i) ↦
      (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g) :=
  fun _ _ e e' h ↦ pullback_map_eq_comp D e e' h

omit [EssentiallySmall.{u} I] in
/-- In a thin cofiltered category, two properties that eventually hold eventually hold
together. -/
private lemma exists_and_of_upClosed (hthin : ∀ {a b : I} (f g : a ⟶ b), f = g)
    {i : I} {P Q : ∀ j : I, (j ⟶ i) → Prop} (hP : UpClosed P) (hQ : UpClosed Q)
    (h₁ : ∃ j e, P j e) (h₂ : ∃ j e, Q j e) : ∃ j e, P j e ∧ Q j e := by
  obtain ⟨j₁, e₁, h₁⟩ := h₁
  obtain ⟨j₂, e₂, h₂⟩ := h₂
  refine ⟨IsCofiltered.min j₁ j₂, IsCofiltered.minToLeft j₁ j₂ ≫ e₁,
    hP _ _ _ _ h₁, ?_⟩
  rw [hthin (IsCofiltered.minToLeft j₁ j₂ ≫ e₁) (IsCofiltered.minToRight j₁ j₂ ≫ e₂)]
  exact hQ _ _ _ _ h₂

/-- A property of the structure morphism of a base change can be read off the base change of
the structure morphism, seen as a morphism to the base. -/
lemma pullback_map_homMk_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S S' : Scheme.{u}} (g : S' ⟶ S) (X : Over S) :
    P ((Over.pullback g).map (Over.homMk X.hom (Category.comp_id _) : X ⟶ Over.mk (𝟙 S))).left ↔
      P ((Over.pullback g).obj X).hom := by
  rw [← Over.w ((Over.pullback g).map (Over.homMk X.hom (Category.comp_id _) : X ⟶ Over.mk (𝟙 S)))]
  have : IsIso ((Over.pullback g).obj (Over.mk (𝟙 S))).hom :=
    inferInstanceAs (IsIso (Limits.pullback.snd (𝟙 S) g))
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).symm

/-- Stacks 0C0C: smoothness of the base change to the limit is attained at a stage. -/
private lemma exists_smooth_pullback (hc : IsLimit c) {i : I} (X : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hs : Smooth ((Over.pullback (c.π.app i)).obj X).hom) :
    ∃ (j : I) (e : j ⟶ i), Smooth ((Over.pullback (D.map e)).obj X).hom := by
  obtain ⟨_, _, _⟩ := hX
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk X.hom (Category.comp_id _)
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs (LocallyOfFinitePresentation X.hom)
  have : Smooth ((Over.pullback (c.π.app i)).map f₀).left :=
    (pullback_map_homMk_iff @Smooth _ X).2 hs
  obtain ⟨j, e, h⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i X _
    f₀ hc
  exact ⟨j, e, (pullback_map_homMk_iff @Smooth _ X).1 h⟩

/-- Stacks 081F: properness of the base change to the limit is attained at a stage. -/
lemma exists_isProper_pullback (hc : IsLimit c) {i : I} (X : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hp : IsProper ((Over.pullback (c.π.app i)).obj X).hom) :
    ∃ (j : I) (e : j ⟶ i), IsProper ((Over.pullback (D.map e)).obj X).hom := by
  obtain ⟨_, _, _⟩ := hX
  have : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let f₀ : X ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk X.hom (Category.comp_id _)
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X.hom)
  have : IsProper ((Over.pullback (c.π.app i)).map f₀).left :=
    (pullback_map_homMk_iff @IsProper _ X).2 hp
  obtain ⟨j, e, h⟩ := exists_isProper_baseChange_of_isLimit D c i hc X _ f₀
  exact ⟨j, e, (pullback_map_homMk_iff @IsProper _ X).1 h⟩

variable (A : Over c.pt) [GrpObj A]

/-- A model of the group scheme `A` at the stage `i`: a scheme of finite presentation over the
stage, with group data whose base change to the limit is identified with `A`. -/
private structure Model (i : I) where
  X : Over (D.obj i)
  fp : FinitePresentation X.hom
  φ : (Over.pullback (c.π.app i)).obj X ≅ A
  mul : X ⊗ X ⟶ X
  one : 𝟙_ (Over (D.obj i)) ⟶ X
  inv : X ⟶ X
  mulCompat : MulCompat (Over.pullback (c.π.app i)) mul φ
  oneCompat : OneCompat (Over.pullback (c.π.app i)) one φ
  invCompat : InvCompat (Over.pullback (c.π.app i)) inv φ
  isGrp : IsGrpData mul one inv

variable {D c A}

/-- The base change of a model to a later stage. -/
private noncomputable def Model.baseChange {i j : I} (M : Model D c A i) (e : j ⟶ i) :
    Model D c A j where
  X := (Over.pullback (D.map e)).obj M.X
  fp := finitePresentation_pullback _ M.fp
  φ := (pullbackCompIso D c e).app M.X ≪≫ M.φ
  mul := «μ» (Over.pullback (D.map e)) M.X M.X ≫ (Over.pullback (D.map e)).map M.mul
  one := ε (Over.pullback (D.map e)) ≫ (Over.pullback (D.map e)).map M.one
  inv := (Over.pullback (D.map e)).map M.inv
  mulCompat := M.mulCompat.transport _ _ _ _
  oneCompat := M.oneCompat.transport _ _ _ _
  invCompat := M.invCompat.transport _ _ _ _
  isGrp := M.isGrp.map _

variable (D c A) in
/-- Stacks 01ZM: the group scheme `A`, of finite presentation over the limit, has a model at
some stage. -/
private lemma exists_model (hthin : ∀ {a b : I} (f g : a ⟶ b), f = g) (hc : IsLimit c)
    (hA : FinitePresentation A.hom) : ∃ i, Nonempty (Model D c A i) := by
  obtain ⟨i₀, X₀, hX₀, ⟨e₀⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc A hA
  let φ₀ : (Over.pullback (c.π.app i₀)).obj X₀ ≅ A := e₀.symm
  -- the multiplication
  obtain ⟨i₁, e₁, g₁, hg₁⟩ := exists_map_eq D c hc (finitePresentation_tensor hX₀ hX₀) hX₀
    (Functor.OplaxMonoidal.δ (Over.pullback (c.π.app i₀)) X₀ X₀ ≫ (φ₀.hom ⊗ₘ φ₀.hom) ≫ μ[A] ≫
      φ₀.inv)
  let X₁ := (Over.pullback (D.map e₁)).obj X₀
  let φ₁ : (Over.pullback (c.π.app i₁)).obj X₁ ≅ A := (pullbackCompIso D c e₁).app X₀ ≪≫ φ₀
  let m₁ : X₁ ⊗ X₁ ⟶ X₁ := «μ» (Over.pullback (D.map e₁)) X₀ X₀ ≫ g₁
  have hm₁ : MulCompat (Over.pullback (c.π.app i₁)) m₁ φ₁ :=
    mulCompat_of_map_eq _ _ (pullbackCompIso D c e₁) φ₀ g₁ hg₁
  have hX₁ : FinitePresentation X₁.hom := finitePresentation_pullback _ hX₀
  -- the unit
  obtain ⟨i₂, e₂, g₂, hg₂⟩ := exists_map_eq D c hc (finitePresentation_unit _) hX₁
    (Functor.OplaxMonoidal.η (Over.pullback (c.π.app i₁)) ≫ η[A] ≫ φ₁.inv)
  let X₂ := (Over.pullback (D.map e₂)).obj X₁
  let φ₂ : (Over.pullback (c.π.app i₂)).obj X₂ ≅ A := (pullbackCompIso D c e₂).app X₁ ≪≫ φ₁
  let m₂ : X₂ ⊗ X₂ ⟶ X₂ := «μ» (Over.pullback (D.map e₂)) X₁ X₁ ≫ (Over.pullback (D.map e₂)).map m₁
  let u₂ : 𝟙_ _ ⟶ X₂ := ε (Over.pullback (D.map e₂)) ≫ g₂
  have hm₂ : MulCompat (Over.pullback (c.π.app i₂)) m₂ φ₂ :=
    hm₁.transport _ _ (pullbackCompIso D c e₂)
  have hu₂ : OneCompat (Over.pullback (c.π.app i₂)) u₂ φ₂ :=
    oneCompat_of_map_eq _ _ (pullbackCompIso D c e₂) φ₁ g₂ hg₂
  have hX₂ : FinitePresentation X₂.hom := finitePresentation_pullback _ hX₁
  -- the inverse
  obtain ⟨i₃, e₃, g₃, hg₃⟩ := exists_map_eq D c hc hX₂ hX₂ (φ₂.hom ≫ ι[A] ≫ φ₂.inv)
  let X₃ := (Over.pullback (D.map e₃)).obj X₂
  let φ₃ : (Over.pullback (c.π.app i₃)).obj X₃ ≅ A := (pullbackCompIso D c e₃).app X₂ ≪≫ φ₂
  let m₃ : X₃ ⊗ X₃ ⟶ X₃ := «μ» (Over.pullback (D.map e₃)) X₂ X₂ ≫ (Over.pullback (D.map e₃)).map m₂
  let u₃ : 𝟙_ _ ⟶ X₃ := ε (Over.pullback (D.map e₃)) ≫ (Over.pullback (D.map e₃)).map u₂
  have hm₃ : MulCompat (Over.pullback (c.π.app i₃)) m₃ φ₃ :=
    hm₂.transport _ _ (pullbackCompIso D c e₃)
  have hu₃ : OneCompat (Over.pullback (c.π.app i₃)) u₃ φ₃ :=
    hu₂.transport _ _ (pullbackCompIso D c e₃)
  have hv₃ : InvCompat (Over.pullback (c.π.app i₃)) g₃ φ₃ :=
    invCompat_of_map_eq _ _ (pullbackCompIso D c e₃) φ₂ g₃ hg₃
  have hX₃ : FinitePresentation X₃.hom := finitePresentation_pullback _ hX₂
  -- the group axioms
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := (isGrpData_map_iff (Over.pullback (c.π.app i₃)) m₃ u₃ g₃).1
    (isGrpData_of_compat _ hm₃ hu₃ hv₃)
  have hU := finitePresentation_unit (D.obj i₃)
  obtain ⟨j, e, h⟩ := exists_and_of_upClosed hthin (upClosed_map_eq D _ _)
    ((upClosed_map_eq D _ _).and ((upClosed_map_eq D _ _).and
      ((upClosed_map_eq D _ _).and (upClosed_map_eq D _ _))))
    (eventually_eq_of_baseChange_eq D c hc i₃ _ _ (finitePresentation_tensor hU hX₃) hX₃ _ _ h₁)
    (exists_and_of_upClosed hthin (upClosed_map_eq D _ _)
      ((upClosed_map_eq D _ _).and ((upClosed_map_eq D _ _).and (upClosed_map_eq D _ _)))
      (eventually_eq_of_baseChange_eq D c hc i₃ _ _ (finitePresentation_tensor hX₃ hU) hX₃ _ _ h₂)
      (exists_and_of_upClosed hthin (upClosed_map_eq D _ _)
        ((upClosed_map_eq D _ _).and (upClosed_map_eq D _ _))
        (eventually_eq_of_baseChange_eq D c hc i₃ _ _
          (finitePresentation_tensor (finitePresentation_tensor hX₃ hX₃) hX₃) hX₃ _ _ h₃)
        (exists_and_of_upClosed hthin (upClosed_map_eq D _ _) (upClosed_map_eq D _ _)
          (eventually_eq_of_baseChange_eq D c hc i₃ _ _ hX₃ hX₃ _ _ h₄)
          (eventually_eq_of_baseChange_eq D c hc i₃ _ _ hX₃ hX₃ _ _ h₅))))
  exact ⟨j, ⟨{
    X := (Over.pullback (D.map e)).obj X₃
    fp := finitePresentation_pullback _ hX₃
    φ := (pullbackCompIso D c e).app X₃ ≪≫ φ₃
    mul := «μ» (Over.pullback (D.map e)) X₃ X₃ ≫ (Over.pullback (D.map e)).map m₃
    one := ε (Over.pullback (D.map e)) ≫ (Over.pullback (D.map e)).map u₃
    inv := (Over.pullback (D.map e)).map g₃
    mulCompat := hm₃.transport _ _ _
    oneCompat := hu₃.transport _ _ _
    invCompat := hv₃.transport _ _ _
    isGrp := (isGrpData_map_iff _ m₃ u₃ g₃).2 h }⟩⟩

/-- A property of `A`'s structure morphism holds for the base change of a model. -/
private lemma Model.prop_pullback {i : I} (M : Model D c A i) (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (h : P A.hom) : P ((Over.pullback (c.π.app i)).obj M.X).hom := by
  rw [← Over.w M.φ.hom]
  have : IsIso M.φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso M.φ).hom)
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 h

variable (D c A) in
/-- Stacks 01ZM, 0C0C, 081F: a smooth proper group scheme of finite presentation over the
limit has a smooth proper model at some stage. -/
private lemma exists_model_smooth_isProper (hthin : ∀ {a b : I} (f g : a ⟶ b), f = g)
    (hc : IsLimit c) (hA : FinitePresentation A.hom) (hs : Smooth A.hom) (hp : IsProper A.hom) :
    ∃ (i : I) (M : Model D c A i), Smooth M.X.hom ∧ IsProper M.X.hom := by
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨i, ⟨M⟩⟩ := exists_model D c A hthin hc hA
  obtain ⟨j, e, hj⟩ := exists_smooth_pullback D c hc M.X M.fp (M.prop_pullback @Smooth hs)
  let M₁ := M.baseChange e
  have : Smooth M₁.X.hom := hj
  obtain ⟨j', e', hj'⟩ := exists_isProper_pullback D c hc M₁.X M₁.fp
    (M₁.prop_pullback @IsProper hp)
  refine ⟨j', M₁.baseChange e', ?_, hj'⟩
  exact inferInstanceAs (Smooth (Limits.pullback.snd M₁.X.hom (D.map e')))

end Descent

section Irreducible

/-- Geometric irreducibility is invariant under isomorphisms. -/
private lemma respectsIso_geometricallyIrreducible :
    MorphismProperty.RespectsIso (@GeometricallyIrreducible : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- If the base change of `f : X ⟶ Spec R` to the fraction field `K` of the domain `R` is
geometrically irreducible, so is the fibre of `f` over the generic point. -/
private lemma geometricallyIrreducible_fiber_bot (R : CommRingCat.{u}) [IsDomain R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}} (f : X ⟶ Spec R)
    (h : GeometricallyIrreducible (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap R K))))) :
    GeometricallyIrreducible (f.fiberToSpecResidueField (⟨⊥, Ideal.isPrime_bot⟩ : Spec R)) := by
  have := respectsIso_geometricallyIrreducible.{u}
  let x : Spec R := ⟨⊥, Ideal.isPrime_bot⟩
  have hinj : Function.Injective (algebraMap R x.asIdeal.ResidueField) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ RingHom.ker (algebraMap R x.asIdeal.ResidueField) := ha
    rwa [Ideal.ker_algebraMap_residueField] at this
  let l : K →+* x.asIdeal.ResidueField := IsFractionRing.lift hinj
  have hfac : (Spec R).fromSpecResidueField x =
      (Spec.map (Scheme.Spec.residueFieldIso R x).inv ≫ Spec.map (CommRingCat.ofHom l)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [l, IsFractionRing.lift_algebraMap]
  change GeometricallyIrreducible (Limits.pullback.snd f ((Spec R).fromSpecResidueField x))
  rw [hfac, ← Iso.inv_hom_id_assoc (pullbackLeftPullbackSndIso f _ _) (Limits.pullback.snd f _),
    pullbackLeftPullbackSndIso_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 inferInstance

/-- Geometric irreducibility over an open `V` of the base passes to base changes along
morphisms landing in `V`. -/
private lemma geometricallyIrreducible_pullback_snd_of_range_subset {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens) [GeometricallyIrreducible (f ∣_ V)] (g : Z ⟶ Y)
    (hg : Set.range g ⊆ V) : GeometricallyIrreducible (Limits.pullback.snd f g) := by
  have := respectsIso_geometricallyIrreducible.{u}
  have hg' : Set.range g ⊆ Set.range V.ι := by simpa using hg
  let t := IsOpenImmersion.lift V.ι g hg'
  have sq := (IsPullback.of_hasPullback (f ∣_ V) t).paste_horiz
    (isPullback_morphismRestrict f V).flip
  rw [IsOpenImmersion.lift_fac] at sq
  rw [← sq.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 inferInstance

end Irreducible

section StageIrreducible

variable (k : Type u) [Field k] [NumberField k]

/-- A nonzero element of `𝓞 k[1/n!]` becomes a unit in `𝓞 k[1/m!]` for some `m ≥ n`. -/
private lemma exists_isUnit_inclusion (n : ℕ) (g : locAway k _ (factorial_ne_zero n))
    (hg : g ≠ 0) : ∃ (m : ℕ) (h : n ≤ m), IsUnit (Subalgebra.inclusion
      (locAway_mono k (Int.natCast_dvd_natCast.2 (Nat.factorial_dvd_factorial h)) :
        locAway k _ (factorial_ne_zero n) ≤ locAway k _ (factorial_ne_zero m)) g) := by
  obtain ⟨a, j, ha⟩ := mem_locAway.1 g.2
  have ha0 : a ≠ 0 := by
    rintro rfl; apply hg; ext; simpa using ha
  set M := Ideal.absNorm (Ideal.span {a})
  have hM : M ≠ 0 := by exact_mod_cast absNorm_span_singleton_ne_zero ha0
  refine ⟨n + M, Nat.le_add_right n M, ?_⟩
  have hmem : (((n.factorial : ℕ) : ℤ) : k) ^ j * (algebraMap (𝓞 k) k a)⁻¹ ∈
      locAway k _ (factorial_ne_zero (n + M)) :=
    mul_mem (pow_mem (intCast_mem _ _) _) (inv_mem_locAway ha0 (Int.natCast_dvd_natCast.2
      (Nat.dvd_factorial (Nat.pos_of_ne_zero hM) (Nat.le_add_left M n))))
  refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext ?_)
  change (g : k) * _ = 1
  have hN : (((n.factorial : ℕ) : ℤ) : k) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hak : algebraMap (𝓞 k) k a ≠ 0 := by simpa using ha0
  rw [ha]
  field_simp

/-- Stacks 0559 over the stages: geometric irreducibility of the base change to `Spec k` is
attained at a stage. -/
private lemma exists_geometricallyIrreducible_stage {n : (ULift.{u} ℕ)ᵒᵖ}
    (X : Over ((stageDiagram k).obj n)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (h : GeometricallyIrreducible ((Over.pullback ((stageCone k).π.app n)).obj X).hom) :
    ∃ (m : (ULift.{u} ℕ)ᵒᵖ) (e : m ⟶ n),
      GeometricallyIrreducible ((Over.pullback ((stageDiagram k).map e)).obj X).hom := by
  let R := CommRingCat.of (locAway k _ (factorial_ne_zero n.unop.down))
  have : IrreducibleSpace ((stageDiagram k).obj n) := inferInstanceAs (IrreducibleSpace (Spec R))
  have hgen := geometricallyIrreducible_fiber_bot R k X.hom h
  have hη : IsGenericPoint (⟨⊥, Ideal.isPrime_bot⟩ : Spec R) Set.univ := by
    rw [isGenericPoint_def]
    exact (PrimeSpectrum.closure_singleton _).trans PrimeSpectrum.zeroLocus_bot
  obtain ⟨V, ⟨p⟩, hV⟩ := geometricallyIrreducibleAfterShrinking X.hom inferInstance inferInstance
    inferInstance _ hη hgen
  obtain ⟨_, ⟨g, rfl⟩, hpg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open p.2 V.isOpen
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hpg
    exact hpg
  obtain ⟨m, hnm, hu⟩ := exists_isUnit_inclusion k n.unop.down g hg0
  let e : (op (ULift.up m) : (ULift.{u} ℕ)ᵒᵖ) ⟶ n :=
    (homOfLE (show n.unop ≤ ULift.up m from hnm)).op
  refine ⟨_, e, ?_⟩
  have : GeometricallyIrreducible (X.hom ∣_ V) := hV
  refine geometricallyIrreducible_pullback_snd_of_range_subset X.hom V _ ?_
  rintro _ ⟨q, rfl⟩
  apply hgV
  change g ∉ Ideal.comap _ q.asIdeal
  intro hq
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)

end StageIrreducible

/-- An abelian variety `A` over a number field `k` spreads out: there are a nonzero integer `N`
and an abelian scheme `𝒜` over `𝓞 k[1/N]` (a group scheme that is flat, proper and locally of
finite presentation, all of whose fibres `𝒜 ×_W Spec κ(w)` are proper and geometrically integral)
together with an isomorphism of group schemes over `k` between the generic fibre
`𝒜 ×_{𝓞 k[1/N]} Spec k` and `A`. -/
@[faltings "lem_mw_abelian_scheme_spreading_out"]
theorem exists_isAbelianScheme_localizationAway_pullback_iso (k : Type u) [Field k]
    [NumberField k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] :
    ∃ (N : ℤ) (hN : N ≠ 0),
      ∃ 𝒜 : Grp (Over (Spec (CommRingCat.of
          (Localization.subalgebra k (Submonoid.powers (N : 𝓞 k))
            (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.cast_ne_zero.mpr hN)))))),
        Flat 𝒜.X.hom ∧ IsProper 𝒜.X.hom ∧ LocallyOfFinitePresentation 𝒜.X.hom ∧
        (∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
          GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom) ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
            (Localization.subalgebra k (Submonoid.powers (N : 𝓞 k))
              (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.cast_ne_zero.mpr hN)))
            k)))).mapGrp.obj 𝒜 ≅ Grp.mk A) := by
  let D := stageDiagram k
  let c := stageCone k
  have hc : IsLimit c := isLimitStageCone k
  have : ∀ {i j : (ULift.{u} ℕ)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (Spec.map _))
  have : ∀ i, CompactSpace (D.obj i) := fun _ ↦ inferInstanceAs (CompactSpace (Spec _))
  have : ∀ i, QuasiSeparatedSpace (D.obj i) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have hthin : ∀ {a b : (ULift.{u} ℕ)ᵒᵖ} (f g : a ⟶ b), f = g :=
    fun _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hA : FinitePresentation A.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  have : GrpObj (Over.mk A.hom) := ‹GrpObj A›
  have hs : Smooth A.hom := smooth_of_grpObj A.hom
  have := respectsIso_geometricallyIrreducible.{u}
  obtain ⟨i, M, hMs, hMp⟩ := exists_model_smooth_isProper D c A hthin hc hA hs inferInstance
  obtain ⟨_, _, _⟩ := M.fp
  obtain ⟨m, e, hGI⟩ := exists_geometricallyIrreducible_stage k M.X
    (M.prop_pullback @GeometricallyIrreducible inferInstance)
  let M' := M.baseChange e
  have : Smooth M'.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd M.X.hom (D.map e)))
  have : IsProper M'.X.hom := inferInstanceAs (IsProper (Limits.pullback.snd M.X.hom (D.map e)))
  have : GeometricallyIrreducible M'.X.hom := hGI
  have : GeometricallyReduced M'.X.hom := geometricallyReduced_of_smooth _
  have : GeometricallyIntegral M'.X.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  let : GrpObj M'.X := M'.isGrp.grpObj
  let : GrpObj ((Over.pullback (c.π.app m)).obj M'.X) := Functor.grpObjObj
  have : IsMonHom M'.φ.hom := by
    refine ⟨?_, ?_⟩
    · change (ε (Over.pullback (c.π.app m)) ≫ (Over.pullback (c.π.app m)).map M'.one) ≫
        M'.φ.hom = η[A]
      rw [Category.assoc]
      exact M'.oneCompat
    · change («μ» (Over.pullback (c.π.app m)) M'.X M'.X ≫ (Over.pullback (c.π.app m)).map M'.mul) ≫
        M'.φ.hom = (M'.φ.hom ⊗ₘ M'.φ.hom) ≫ μ[A]
      rw [Category.assoc]
      exact M'.mulCompat
  refine ⟨_, factorial_ne_zero m.unop.down, Grp.mk (grp := M'.isGrp.grpObj) M'.X,
    inferInstanceAs (Flat M'.X.hom), inferInstanceAs (IsProper M'.X.hom), M'.fp.1,
    fun w ↦ ⟨?_, ?_⟩, ⟨Grp.mkIso' M'.φ⟩⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
      (inferInstanceAs (IsProper M'.X.hom))
  · exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_hasPullback _ _) (inferInstanceAs (GeometricallyIntegral M'.X.hom))

end Faltings
