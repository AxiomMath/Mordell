module

public import Mordell.AlgebraicGeometry.GeometricPoint.Galois
public import Mordell.MordellWeil.Kummer.Pairing
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import Mordell.MordellWeil.Kummer.Field

/-!
# The left kernel of the Kummer pairing

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`, and let `κ(P, σ) = σ Q_P - Q_P` be the Kummer pairing. A point
`P ∈ A(k)` satisfies `κ(P, σ) = 0` for every `σ ∈ G_k` if and only if `P ∈ m A(k)`: if
`P = m Q` with `Q ∈ A(k)` then `Q` is Galois invariant, and conversely an `m`-th root `Q` of `P`
in `A(k̄)` fixed by every `σ` is a `k`-point.

## Main results

* `Faltings.exists_pow_eq_of_isAlgClosed`: `A(k̄)` is divisible, for any abelian variety `A` over
  a field `k` and algebraically closed `k̄`.
* `Faltings.forall_kummerPairing_eq_one_iff`: `(∀ σ, κ(P, σ) = 1) ↔ ∃ Q ∈ A(k), Q ^ m = P`, so
  the left kernel of `κ` is `m A(k)`.

## Implementation notes

The group laws of `A(k) = (Over.mk (𝟙 (Spec k)) ⟶ A)` and `A(k̄)` are `CategoryTheory.Hom.group`,
written multiplicatively: `κ(P, σ) = 0` reads `κ(P, σ) = 1` and `P ∈ m A(k)` reads
`∃ Q, Q ^ m = P`. The equality of sets of the source is stated pointwise, as an `Iff`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3, Proposition 3.1
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.2
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- Divisibility of `A(k̄)`: for an abelian variety `A` over a field `k` and an algebraically
closed extension `k̄`, every `k̄`-point of `A` is an `n`-th power for `n ≠ 0`. -/
theorem exists_pow_eq_of_isAlgClosed (k : Type u) [Field k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (n : ℕ) (hn : n ≠ 0)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :
    ∃ y, y ^ n = x := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety k A.hom := .mk (toIsVariety := .mk)
  have : IsAbelianVariety k A := ⟨⟩
  revert x
  set i₀ := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
  intro x
  set f := ((𝟙 A : A ⟶ A) ^ (n : ℤ))
  have hsurj := Stacks.Groupoids.surjective_zpow_id k A n (mod_cast hn)
  let g : pullback A.hom i₀ ⟶ pullback A.hom i₀ :=
    pullback.map A.hom i₀ A.hom i₀ f.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hg : g ≫ pullback.snd A.hom i₀ = pullback.snd A.hom i₀ := by simp [g]
  have hpb : IsPullback g (pullback.fst A.hom i₀) (pullback.fst A.hom i₀) f.left := by
    refine IsPullback.of_right (h₁₂ := pullback.snd A.hom i₀) (h₂₂ := A.hom) (v₁₃ := i₀) ?_
      (by simp [g]) (IsPullback.of_hasPullback A.hom i₀).flip
    rw [hg, Over.w f]
    exact (IsPullback.of_hasPullback A.hom i₀).flip
  have : Surjective g := MorphismProperty.of_isPullback hpb.flip hsurj
  obtain ⟨z, hz, hzg⟩ := exists_comp_eq_of_surjective_of_isAlgClosed
    (pullback.snd A.hom i₀) (pullback.snd A.hom i₀) g hg
    (pullback.lift x.left (𝟙 _) (by simp)) (by simp)
  let y : Over.mk i₀ ⟶ A := Over.homMk (z ≫ pullback.fst A.hom i₀) (by
    simp [pullback.condition, reassoc_of% hz, i₀])
  refine ⟨y, ?_⟩
  rw [← zpow_natCast, ← Category.comp_id y, ← GrpObj.comp_zpow]
  ext
  simp only [Over.comp_left, y, Over.homMk_left, Category.assoc]
  rw [← hpb.w, reassoc_of% hzg, pullback.lift_fst]

/-- The map `A(k) → A(k̄)` is injective: `Spec k̄ → Spec k` is an epimorphism. -/
private lemma homMk_comp_injective (k : Type u) [Field k] (kbar : Type u) [Field kbar]
    [Algebra k kbar] (A : Over (Spec (CommRingCat.of k))) :
    Function.Injective fun R : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ R :=
  fun _ _ h => Over.OverMorphism.ext <|
    (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))).1
      (congrArg CommaMorphism.left h)

/-- Galois descent over `k` itself: a point of `X(k̄)` fixed by every `σ ∈ Gal(k̄/k)` is the image
of a point of `X(k)`. This is `Faltings.setOf_forall_galoisActionPoint_eq_eq_range` for `K = ⊥`,
transported along `⊥ ≃ k`. -/
private lemma exists_homMk_comp_eq_of_forall_galoisActionPoint_eq (k : Type u) [Field k]
    [NumberField k] (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ X)
    (hQ : ∀ σ, galoisActionPoint k kbar X σ Q = Q) :
    ∃ R : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ R = Q := by
  have hmem : Q ∈ {Q | ∀ σ : kbar ≃ₐ[(⊥ : IntermediateField k kbar)] kbar,
      galoisActionPoint k kbar X (σ.restrictScalars k) Q = Q} := fun σ => hQ _
  rw [setOf_forall_galoisActionPoint_eq_eq_range] at hmem
  obtain ⟨R, rfl⟩ := hmem
  let φ : (⊥ : IntermediateField k kbar) →+* k := (IntermediateField.botEquiv k kbar).toRingHom
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ R.left) ?_, ?_⟩
  · simp only [Over.mk_left, Over.mk_hom, Category.assoc, Over.w R]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    ext x
    simp [φ]
  · ext1
    simp only [Over.comp_left, Over.homMk_left, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp x.2
    obtain rfl : x = algebraMap k _ y := Subtype.ext hy.symm
    simp [φ]

/-- The left kernel of the Kummer pairing is `m A(k)`: for an abelian variety `A` over a number
field `k` with `A(k̄)[m] ⊆ A(k)`, a point `P ∈ A(k)` has `Faltings.kummerPairing … P σ = 1` for
every `σ ∈ Gal(k̄/k)` if and only if `P = Q ^ m` for some `Q ∈ A(k)` (multiplicative notation). -/
@[faltings "lem_mw_kummer_pairing_left_kernel"]
theorem forall_kummerPairing_eq_one_iff (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) :
    (∀ σ : kbar ≃ₐ[k] kbar, kummerPairing k kbar A m hm htors P σ = 1) ↔
      ∃ Q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A, Q ^ m = P := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  constructor
  · intro h
    obtain ⟨Q, hQ⟩ := exists_pow_eq_of_isAlgClosed k kbar A m (by omega) _
    obtain ⟨R, rfl⟩ := exists_homMk_comp_eq_of_forall_galoisActionPoint_eq k kbar A Q fun σ =>
      (mul_inv_eq_one.mp
        ((h σ).symm.trans (kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hQ)).symm)
    exact ⟨R, homMk_comp_injective k kbar A (by simpa [MonObj.comp_pow] using hQ)⟩
  · rintro ⟨Q, rfl⟩ σ
    rw [kummerPairing_eq_of_pow_eq k kbar A m hm htors _ σ _ (MonObj.comp_pow Q m _).symm,
      galoisActionPoint_homMk_comp, mul_inv_cancel]

end Faltings


/-!
# The right kernel of the Kummer pairing

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`, let `κ(P, σ) = σ Q_P - Q_P` be the Kummer pairing and
`M = k(m⁻¹ A(k))` the Kummer field. An element `σ ∈ G_k` satisfies `κ(P, σ) = 0` for every
`P ∈ A(k)` if and only if `σ` fixes `M` pointwise, that is, `σ ∈ Gal(k̄/M)`: the field `M` is
generated by the fields of definition of the `m`-th roots of the points of `A(k)`, and `σ` fixes
such a root `Q` exactly when it fixes `k(Q)`.

## Main results

* `Faltings.forall_kummerPairing_eq_one_iff_mem_fixingSubgroup`:
  `(∀ P, κ(P, σ) = 1) ↔ σ ∈ (kummerField …).fixingSubgroup`, so the right kernel of `κ` is
  `Gal(k̄/M)`.

## Implementation notes

The group law of `A(k̄)` is `CategoryTheory.Hom.group`, written multiplicatively, so
`κ(P, σ) = 0` reads `κ(P, σ) = 1`. The subgroup `Gal(k̄/M)` of `k̄ ≃ₐ[k] k̄` is
`IntermediateField.fixingSubgroup M`. The equality of sets of the source is stated pointwise,
as an `Iff`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3, Proposition 3.1
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- `σ` fixes the Kummer field pointwise if and only if it fixes every `Q ∈ A(k̄)` with
`m Q` in the image of `A(k)`. -/
private lemma mem_fixingSubgroup_kummerField_iff (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (σ : kbar ≃ₐ[k] kbar) :
    σ ∈ (kummerField k kbar A m hm htors).fixingSubgroup ↔
      ∀ Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
        (∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
          Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
            (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
            (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m) →
          galoisActionPoint k kbar A σ Q = Q := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]
  unfold kummerField
  rw [iSup₂_le_iff]
  refine forall₂_congr fun Q _ => ?_
  rw [galoisActionPoint_eq_self_iff, IntermediateField.le_iff_le, Subgroup.zpowers_le,
    IntermediateField.mem_fixingSubgroup_iff]

/-- The right kernel of the Kummer pairing is `Gal(k̄/M)` for the Kummer field
`M = Faltings.kummerField …`: for an abelian variety `A` over a number field `k` with
`A(k̄)[m] ⊆ A(k)`, an element `σ ∈ Gal(k̄/k)` has `Faltings.kummerPairing … P σ = 1` for every
`P ∈ A(k)` if and only if `σ` fixes `M` pointwise (multiplicative notation). -/
@[faltings "lem_mw_kummer_pairing_right_kernel"]
theorem forall_kummerPairing_eq_one_iff_mem_fixingSubgroup (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (σ : kbar ≃ₐ[k] kbar) :
    (∀ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        kummerPairing k kbar A m hm htors P σ = 1) ↔
      σ ∈ (kummerField k kbar A m hm htors).fixingSubgroup := by
  refine Iff.trans ?_ (mem_fixingSubgroup_kummerField_iff k kbar A m hm htors σ).symm
  constructor
  · rintro h Q ⟨P, hP⟩
    exact mul_inv_eq_one.mp <|
      (kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hP.symm).symm.trans (h P)
  · intro h P
    by_cases hex : ∃ Q, Q ^ m = Over.homMk
        (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P
    · obtain ⟨Q, hQ⟩ := hex
      rw [kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hQ, h Q ⟨P, hQ.symm⟩,
        mul_inv_cancel]
    · obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
      simp only [kummerPairing, hex, ↓reduceDIte, ← he, map_one, inv_one, mul_one]

end Faltings
