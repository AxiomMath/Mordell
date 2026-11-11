module

public import Mordell.AlgebraicGeometry.GeometricPoint.Galois
public import Mordell.MordellWeil.Kummer.PointField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import Mordell.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# The degree of the field of definition of a Kummer point

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety of
dimension `g` over `k` and `m ≥ 1`, and assume that the `m`-torsion `A(k̄)[m]` is contained in
`A(k)`. If `Q ∈ A(k̄)` has `m Q ∈ A(k)`, then `[k(Q) : k] ≤ m ^ (2 g)`: the extension `k(Q)/k` is
Galois, and `σ ↦ σ Q - Q` embeds `Gal(k(Q)/k)` into `A(k̄)[m] ≅ (ℤ/mℤ)^(2g)`.

## Main results

* `Faltings.finrank_fieldOfDefinition_le_of_pow_mem`: `[k(Q) : k] ≤ m ^ (2 g)`.

## Implementation notes

An abelian variety over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral; its dimension is the
Krull dimension `topologicalKrullDim A.left` of the underlying space. The points `A(k̄)` are
the morphisms `Over.mk (Spec (k → k̄)) ⟶ A`, a group under `CategoryTheory.Hom.group`, written
multiplicatively, so `m Q` is `Q ^ m`. The `k`-points `A(k)` are the morphisms
`Over.mk (𝟙 (Spec k)) ⟶ A`, and `A(k) → A(k̄)` is precomposition with the morphism
`Spec k̄ ⟶ Spec k` over `Spec k`. The field `k(Q)` is `Faltings.fieldOfDefinition Q.left`,
where `A.left` is a `k`-scheme through `A.hom`, and the degree is `Module.finrank`. This is the
setup of `Faltings.kummerField`.

The bound on `A(k̄)[m]` passes through the base change `A_{k̄}`: a point of `A(k̄)` is a
`k̄`-rational point of `A_{k̄}`, injectively, the `m`-torsion of `A_{k̄}(k̄)` is `(ℤ/mℤ) ^ 2g`
([Stacks, Tag 03RP] (7)), and the dimension is unchanged under base change
([Stacks, Tag 0BY9]).

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.2
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory Limits
open scoped MonObj

universe u

namespace Faltings

/-- The `m`-torsion `A(k̄)[m]` of an abelian variety of dimension `g` over a number field `k`
injects into `(ℤ/mℤ) ^ 2g`. -/
private lemma exists_injective_setOf_pow_eq_one (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (g : ℕ) (hdim : topologicalKrullDim A.left = g)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ f : {T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A // T ^ m = 1} →
      (Fin (2 * g) → ZMod m), Function.Injective f := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety k A.hom := .mk (toIsVariety := .mk)
  have : IsAbelianVariety k A := ⟨⟩
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  have : NeZero m := ⟨by omega⟩
  obtain ⟨e⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit kbar
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))).obj A) m
    (Nat.cast_ne_zero.mpr (NeZero.ne m)).isUnit
  have hd : Stacks.Groupoids.abelianVarietyDimension
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))).obj A) = g := by
    have h := topologicalKrullDim_baseChange k kbar _ _ A.hom
      (IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
    simp only [Stacks.Groupoids.abelianVarietyDimension, Over.pullback_obj_left]
    rw [h, hdim]
    rfl
  rw [hd] at e
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
  refine ⟨fun T => e ⟨Additive.ofMul (GroupScheme.toBaseChangeHom φ A T.1), ?_⟩,
    fun T T' h => ?_⟩
  · rw [AddSubgroup.torsionBy.nsmul_iff, ← ofMul_pow, ← map_pow, T.2, map_one, ofMul_one]
  · have h' := congrArg Subtype.val (e.injective h)
    exact Subtype.ext (GroupScheme.toBaseChange_injective φ A (Additive.ofMul.injective h'))

/-- Lifts to `Gal(k̄/k)` of distinct elements of `Gal(k(Q)/k)` move a `k̄`-point `Q` to
distinct points: if `σ₁ Q = σ₂ Q` then `σ₂⁻¹ σ₁` fixes `Q`, hence fixes `k(Q)` pointwise. -/
private lemma galoisActionPoint_liftNormal_injective {k : Type u} [Field k] [NumberField k]
    {kbar : Type u} [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X) :
    letI : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
    haveI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType X.hom)
    haveI : Normal k kbar := IsAlgClosure.normal k kbar
    Function.Injective fun τ : fieldOfDefinition (k := k) Q.left (Over.w Q) ≃ₐ[k]
        fieldOfDefinition (k := k) Q.left (Over.w Q) =>
      galoisActionPoint k kbar X (τ.liftNormal kbar) Q := by
  intro τ₁ τ₂ h
  dsimp only at h
  have hfix := (galoisActionPoint_eq_self_iff X
    ((τ₂.liftNormal kbar)⁻¹ * τ₁.liftNormal kbar) Q).1 (by
      rw [← galoisActionPoint_mul, h, galoisActionPoint_mul, inv_mul_cancel,
        galoisActionPoint_one])
  ext x
  have hx := hfix _ x.2
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at hx
  change algebraMap _ kbar (τ₁ x) = algebraMap _ kbar (τ₂ x)
  rwa [← AlgEquiv.liftNormal_commutes, ← AlgEquiv.liftNormal_commutes]

/-- Let `A` be an abelian variety of dimension `g` over a number field `k` with
`A(k̄)[m] ⊆ A(k)`. If `Q ∈ A(k̄)` satisfies `m Q ∈ A(k)`, then its field of definition `k(Q)`
has degree `[k(Q) : k] ≤ m ^ (2 g)`. -/
@[faltings "lem_mw_kummer_field_degree"]
theorem finrank_fieldOfDefinition_le_of_pow_mem (k : Type u) [Field k]
    [NumberField k] (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (g : ℕ) (hdim : topologicalKrullDim A.left = g)
    (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (hQ : ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    Module.finrank k (fieldOfDefinition (k := k) Q.left (Over.w Q)) ≤ m ^ (2 * g) := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  obtain ⟨_, _⟩ :=
    finiteDimensional_and_isGalois_fieldOfDefinition_of_pow_mem k kbar A m hm htors Q hQ
  obtain ⟨P, hP⟩ := hQ
  -- `σ Q * Q⁻¹ = κ(m Q, σ)` is `m`-torsion
  have hmem (σ : kbar ≃ₐ[k] kbar) : (galoisActionPoint k kbar A σ Q * Q⁻¹) ^ m = 1 := by
    rw [← kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hP.symm]
    exact kummerPairing_pow_eq_one k kbar A m hm htors P σ
  obtain ⟨f, hf⟩ := exists_injective_setOf_pow_eq_one k kbar A g hdim m hm
  have : NeZero m := ⟨by omega⟩
  rw [← IsGalois.card_aut_eq_finrank]
  refine (Nat.card_le_card_of_injective _ (hf.comp (f := fun τ => ⟨_, hmem (τ.liftNormal kbar)⟩)
    fun τ₁ τ₂ h => galoisActionPoint_liftNormal_injective A Q
      (mul_left_injective Q⁻¹ (congrArg Subtype.val h)))).trans_eq ?_
  simp

end Faltings
