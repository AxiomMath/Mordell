module

public import Mordell.MordellWeil.Kummer.Field
public import Mordell.MordellWeil.Kummer.Pairing
public import Mordell.MordellWeil.Kummer.Kernel
public import Mordell.MordellWeil.Kummer.PairingMulLeft
public import Mordell.MordellWeil.TorsionLifting

/-!
# The Kummer injection

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`, let `κ` be the Kummer pairing and `M = k(m⁻¹ A(k))` the Kummer
field. Then `P ↦ (σ|_M ↦ κ(P, σ))` is a well-defined group homomorphism
`A(k) → Hom(Gal(M/k), A(k̄)[m])` with kernel `m A(k)`; equivalently it induces an injective
group homomorphism `A(k) / m A(k) ↪ Hom(Gal(M/k), A(k̄)[m])`.

## Main results

* `Faltings.exists_kummerField_galois_hom_kummerPairing`: the Kummer pairing factors through
  `Gal(M/k)` as a family of monoid homomorphisms `Gal(M/k) →* A(k̄)` with values in `A(k̄)[m]`,
  multiplicative in the point and trivial exactly on `m A(k)`.

## Implementation notes

The points `A(k)` and `A(k̄)` are groups under `CategoryTheory.Hom.group`, written
multiplicatively; no commutative group structure on them is available as an instance, so neither
the quotient `A(k) / m A(k)` nor the group `Hom(Gal(M/k), A(k̄)[m])` is formed. The statement
instead gives the map `P ↦ κ(P, ·)` as a function into `(M ≃ₐ[k] M) →* A(k̄)`, together with the
facts that it lands in `A(k̄)[m]`, is multiplicative in `P`, and is trivial exactly at the
`m`-th powers; by the first isomorphism theorem this is the injective homomorphism
`A(k) / m A(k) ↪ Hom(Gal(M/k), A(k̄)[m])`. The restriction `σ|_M` is expressed by the condition
`∀ x : M, σ x = g x` on `g : M ≃ₐ[k] M`; every `g` arises so, `k̄` being algebraically closed.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

section

variable (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)

/-- The Kummer pairing only depends on the restriction of `σ` to the Kummer field `M`:
if `σ` and `σ'` agree on `M`, then `κ(P, σ) = κ(P, σ')`. -/
private lemma kummerPairing_eq_of_forall_apply_eq
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) {σ σ' : kbar ≃ₐ[k] kbar}
    (h : ∀ x : kummerField k kbar A m hm htors, σ x = σ' x) :
    kummerPairing k kbar A m hm htors P σ = kummerPairing k kbar A m hm htors P σ' := by
  have hfix : σ⁻¹ * σ' ∈ (kummerField k kbar A m hm htors).fixingSubgroup := fun x => by
    change σ.symm (σ' x) = x
    rw [← h x, σ.symm_apply_apply]
  rw [← mul_inv_cancel_left σ σ', kummerPairing_mul_right,
    (forall_kummerPairing_eq_one_iff_mem_fixingSubgroup k kbar A m hm htors _).2 hfix P,
    mul_one]

end

/-- The Kummer injection. For an abelian variety `A` over a number field `k` with
`A(k̄)[m] ⊆ A(k)` and `M = Faltings.kummerField k k̄ A m`, there is a map
`φ : A(k) → (Gal(M/k) →* A(k̄))` with `φ P (σ|_M) = Faltings.kummerPairing … P σ` for every
`σ ∈ Gal(k̄/k)`, whose values lie in `A(k̄)[m]`, which is multiplicative in `P`, and with
`φ P = 1` exactly when `P` is an `m`-th power in `A(k)`. Thus `P ↦ φ P` induces an injective
group homomorphism `A(k) / m A(k) ↪ Hom(Gal(M/k), A(k̄)[m])`. -/
@[faltings "lem_mw_kummer_injection"]
theorem exists_kummerField_galois_hom_kummerPairing (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T) :
    ∃ φ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) →
        ((kummerField k kbar A m hm htors ≃ₐ[k] kummerField k kbar A m hm htors) →*
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)),
      (∀ (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ : kbar ≃ₐ[k] kbar)
          (g : kummerField k kbar A m hm htors ≃ₐ[k] kummerField k kbar A m hm htors),
          (∀ x : kummerField k kbar A m hm htors, σ x = g x) →
            φ P g = kummerPairing k kbar A m hm htors P σ) ∧
      (∀ P g, φ P g ^ m = 1) ∧
      (∀ P P' g, φ (P * P') g = φ P g * φ P' g) ∧
      (∀ P, φ P = 1 ↔ ∃ Q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A, Q ^ m = P) := by
  have : Normal k kbar := IsAlgClosure.normal k kbar
  have : IsGalois k (kummerField k kbar A m hm htors) := isGalois_kummerField k kbar A m hm htors
  let φ P : (kummerField k kbar A m hm htors ≃ₐ[k] kummerField k kbar A m hm htors) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    MonoidHom.mk' (fun g => kummerPairing k kbar A m hm htors P (g.liftNormal kbar))
      fun g h => (kummerPairing_eq_of_forall_apply_eq k kbar A m hm htors P
        (σ' := g.liftNormal kbar * h.liftNormal kbar) fun x =>
        ((g * h).liftNormal_commutes kbar x).trans ((congrArg (g.liftNormal kbar)
          (h.liftNormal_commutes kbar x)).trans (g.liftNormal_commutes kbar (h x))).symm).trans
        (kummerPairing_mul_right k kbar A m hm htors P _ _)
  have hspec P σ g (h : ∀ x : kummerField k kbar A m hm htors, σ x = g x) :
      φ P g = kummerPairing k kbar A m hm htors P σ :=
    kummerPairing_eq_of_forall_apply_eq k kbar A m hm htors P fun x =>
      (g.liftNormal_commutes kbar x).trans (h x).symm
  refine ⟨φ, hspec, fun P g => kummerPairing_pow_eq_one k kbar A m hm htors _ _,
    fun P P' g => kummerPairing_mul k kbar A m hm htors _ _ _, fun P => ?_⟩
  rw [← forall_kummerPairing_eq_one_iff k kbar A m hm htors P, DFunLike.ext_iff]
  refine ⟨fun h σ => ?_, fun h g => h _⟩
  rw [← hspec P σ (σ.restrictNormal _) fun x => (σ.restrictNormal_commutes _ x).symm]
  exact h _

end Faltings


/-!
# A finite Kummer field gives a finite weak Mordell–Weil quotient

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. If the Kummer field `k(m⁻¹ A(k))` is a finite extension of `k`,
then the quotient `A(k) / m A(k)` is finite.

## Main results

* `Faltings.finiteIndex_closure_range_pow_of_finiteDimensional_kummerField`: if
  `Faltings.kummerField k k̄ A m` is finite-dimensional over `k`, then the subgroup `m A(k)` has
  finite index in `A(k)`.

## Implementation notes

The `k`-points `A(k)` are the morphisms `Over.mk (𝟙 (Spec k)) ⟶ A`, a group under
`CategoryTheory.Hom.group`, written multiplicatively. The subgroup `m A(k)` is the subgroup
generated by the `m`-th powers; since `A(k)` is commutative it is the set of `m`-th powers, and
finiteness of `A(k) / m A(k)` is `Subgroup.FiniteIndex`, which does not need the commutativity
of `A(k)` as an instance.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- If a multiplicative family `φ : G → (Γ →* B)` over a finite group `Γ` takes values in the
finite set `B[m]` and vanishes exactly on the `m`-th powers, then the subgroup generated by the
`m`-th powers has finite index in `G`. -/
private theorem finiteIndex_closure_range_pow {G Γ B : Type*} [Group G] [Group Γ] [Group B]
    [Finite Γ] {m : ℕ} (φ : G → Γ →* B) (hS : {Q : B | Q ^ m = 1}.Finite)
    (hpow : ∀ P g, φ P g ^ m = 1) (hmul : ∀ P P' g, φ (P * P') g = φ P g * φ P' g)
    (hker : ∀ P, φ P = 1 ↔ ∃ Q, Q ^ m = P) :
    (Subgroup.closure (Set.range fun P : G => P ^ m)).FiniteIndex := by
  let Φ : G →* (Γ → B) :=
    { toFun := fun P g => φ P g
      map_one' := by funext g; simp [(hker 1).2 ⟨1, one_pow m⟩]
      map_mul' := fun P P' => funext (hmul P P') }
  have hH : Subgroup.closure (Set.range fun P : G => P ^ m) = Φ.ker := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun P hP => ?_
    · rintro _ ⟨Q, rfl⟩
      exact funext (DFunLike.congr_fun ((hker (Q ^ m)).2 ⟨Q, rfl⟩))
    · obtain ⟨Q, rfl⟩ := (hker P).1 (MonoidHom.ext (congr_fun hP))
      exact Subgroup.subset_closure ⟨Q, rfl⟩
  have : Finite Φ.range := ((Set.Finite.pi' fun _ => hS).subset (by
    rintro _ ⟨P, rfl⟩ g
    exact hpow P g) : (Set.range Φ).Finite)
  rw [hH]
  exact Subgroup.finiteIndex_ker Φ

/-- Let `A` be an abelian variety over a number field `k` and `m ≥ 1` with `A(k̄)[m] ⊆ A(k)`.
If the Kummer field `k(m⁻¹ A(k)) = Faltings.kummerField k k̄ A m` is finite over `k`, then
`m A(k)` has finite index in `A(k)`, i.e. `A(k) / m A(k)` is finite. -/
@[faltings "lem_mw_kummer_quotient_finite"]
theorem finiteIndex_closure_range_pow_of_finiteDimensional_kummerField
    (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (hfin : FiniteDimensional k (kummerField k kbar A m hm htors)) :
    (Subgroup.closure
      (Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A => P ^ m)).FiniteIndex := by
  obtain ⟨φ, -, hpow, hmul, hker⟩ :=
    exists_kummerField_galois_hom_kummerPairing k kbar A m hm htors
  exact finiteIndex_closure_range_pow φ (finite_setOf_pow_eq_one A hm) hpow hmul hker

end Faltings
