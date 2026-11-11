module

public import Mathlib
public import Mordell.Attr

/-!
# Rational points and residue fields

Let `K` be a field and `X` a scheme over `K`, with structure morphism `f : X ⟶ Spec K`. A
`K`-rational point of `X` is a section `s : Spec K ⟶ X` of `f`. Each residue field `κ(x)` is a
`K`-algebra through the canonical map `K → κ(x)`, the ring map underlying the composite
`Spec κ(x) ⟶ X ⟶ Spec K`. Sending a rational point to the image of the closed point of `Spec K`
is a bijection from `X(K)` onto the points `x` with `rank_K κ(x) = 1`, i.e. those for which
`K → κ(x)` is an isomorphism.

## Main results

* `Faltings.FunctionField.bijOn_rank_residueField_eq_one`: evaluation at the closed point of
  `Spec K` is a bijection from the `K`-rational points of `X` onto the points with residue field
  of rank one over `K`.

## Implementation notes

The `K`-algebra structure on `X.residueField x` is `Spec.preimage (X.fromSpecResidueField x ≫ f)`,
the same map Mathlib's `AlgebraicGeometry.residueFieldIsoBase` inverts. The bijection is stated
as `Set.BijOn` of the evaluation map, which pins the map rather than asserting an equivalence.

## References

* [Stacks, Tag 01J6], [Stacks, Tag 01J9]
-/

public section

namespace Faltings.FunctionField

open AlgebraicGeometry CategoryTheory

universe u

/-- A field extension has rank one iff its structure map is surjective. -/
private lemma rank_eq_one_iff_surjective {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    (letI := φ.toAlgebra; Module.rank K L = 1) ↔ Function.Surjective φ := by
  letI := φ.toAlgebra
  change Module.rank K L = 1 ↔ Function.Surjective (algebraMap K L)
  rw [← Subalgebra.bot_eq_top_iff_rank_eq_one, Algebra.eq_top_iff]
  simp [Algebra.mem_bot, Function.Surjective, Set.mem_range]

/-- A ring map between fields admitting a retraction is surjective. -/
private lemma surjective_of_retraction {K L : Type*} [Field K] [Field L] {φ : K →+* L}
    {ψ : L →+* K} (h : ∀ a, ψ (φ a) = a) : Function.Surjective φ :=
  fun y ↦ ⟨ψ y, ψ.injective (h (ψ y))⟩

/-- A ring map between fields has at most one retraction. -/
private lemma retraction_unique {K L : Type*} [Field K] [Field L] {φ : K →+* L}
    {ψ₁ ψ₂ : L →+* K} (h₁ : ∀ a, ψ₁ (φ a) = a) (h₂ : ∀ a, ψ₂ (φ a) = a) : ψ₁ = ψ₂ := by
  ext y
  obtain ⟨a, rfl⟩ := surjective_of_retraction h₁ y
  rw [h₁, h₂]

/-- The morphism `Spec K ⟶ X` built from `x` and `ψ : κ(x) ⟶ K` is a section of
`f : X ⟶ Spec K` iff `ψ` is a retraction of the canonical map `K → κ(x)`. -/
private lemma isSection_iff {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (x : X) (ψ : X.residueField x ⟶ .of K) :
    (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = 𝟙 _ ↔
      ∀ a, ψ.hom ((Spec.preimage (X.fromSpecResidueField x ≫ f)).hom a) = a := by
  conv_lhs => rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField x ≫ f),
    ← Spec.map_comp, ← Spec.map_id, Spec.map_inj, CommRingCat.hom_ext_iff, RingHom.ext_iff]
  rfl

/-- Every morphism `Spec K ⟶ X` is `Spec ψ ≫ (Spec κ(x) ⟶ X)` for a point `x` and an embedding
`ψ : κ(x) ⟶ K`. -/
private lemma exists_eq_spec_map_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (s : Spec (.of K) ⟶ X) :
    ∃ x ψ, s = Spec.map ψ ≫ X.fromSpecResidueField x :=
  let ⟨⟨x, ψ⟩, h⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective s
  ⟨x, ψ, h.symm⟩

/-- For a scheme `X` over a field `K`, evaluating a `K`-rational point `s : Spec K ⟶ X` at the
closed point of `Spec K` is a bijection from the sections of the structure morphism `f` onto the
points `x` whose residue field has rank one over `K`. -/
@[faltings "lem_ff_rational_points_residue_field"]
theorem bijOn_rank_residueField_eq_one (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) :
    Set.BijOn (fun s : Spec (.of K) ⟶ X ↦ s (IsLocalRing.closedPoint K))
      {s | s ≫ f = 𝟙 _}
      {x | letI : Algebra K (X.residueField x) :=
          (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
        Module.rank K (X.residueField x) = 1} := by
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · rintro s hs
    obtain ⟨x, ψ, rfl⟩ := exists_eq_spec_map_comp s
    have hx : (Spec.map ψ ≫ X.fromSpecResidueField x) (IsLocalRing.closedPoint K) = x :=
      Scheme.fromSpecResidueField_apply x _
    dsimp only [Set.mem_setOf_eq]
    rw [hx]
    exact (rank_eq_one_iff_surjective _).2 (surjective_of_retraction ((isSection_iff f x ψ).1 hs))
  · rintro s₁ hs₁ s₂ hs₂ h
    obtain ⟨x₁, ψ₁, rfl⟩ := exists_eq_spec_map_comp s₁
    obtain ⟨x₂, ψ₂, rfl⟩ := exists_eq_spec_map_comp s₂
    obtain rfl : x₁ = x₂ := (Scheme.fromSpecResidueField_apply x₁ _).symm.trans
      (h.trans (Scheme.fromSpecResidueField_apply x₂ _))
    rw [CommRingCat.hom_ext
      (retraction_unique ((isSection_iff f x₁ ψ₁).1 hs₁) ((isSection_iff f x₁ ψ₂).1 hs₂))]
  · let e := RingEquiv.ofBijective _
      ⟨RingHom.injective _, (rank_eq_one_iff_surjective _).1 hx⟩
    exact ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x,
      (isSection_iff f x _).2 e.symm_apply_apply, Scheme.fromSpecResidueField_apply x _⟩

end Faltings.FunctionField

end
