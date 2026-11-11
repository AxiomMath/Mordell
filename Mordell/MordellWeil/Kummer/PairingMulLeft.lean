module

public import Mordell.MordellWeil.Kummer.Kernel

/-!
# The Kummer pairing is additive in the point

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. The Kummer pairing `κ(P, σ) = σ Q_P - Q_P` is additive in `P`:
`κ(P + P', σ) = κ(P, σ) + κ(P', σ)`. Indeed `Q_{P+P'}` and `Q_P + Q_{P'}` are both `m`-th roots
of `P + P'`, so they differ by a point of `A(k̄)[m] ⊆ A(k)`, which `σ` fixes.

## Main results

* `Faltings.kummerPairing_mul`: `κ(P * P', σ) = κ(P, σ) * κ(P', σ)` in the multiplicatively
  written groups `A(k)` and `A(k̄)`.

## Implementation notes

The group laws of `A(k) = (Over.mk (𝟙 (Spec k)) ⟶ A)` and `A(k̄) = (Spec k̄ ⟶ A)` are
`CategoryTheory.Hom.group`, written multiplicatively, so additivity reads as multiplicativity.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- The Kummer pairing of an abelian variety `A` over a number field `k` with `A(k̄)[m] ⊆ A(k)`
is additive in the point: `κ(P + P', σ) = κ(P, σ) + κ(P', σ)`, written multiplicatively.
Choosing `m`-th roots `Q` of `P` and `Q'` of `P'` in `A(k̄)`, `Q * Q'` is an `m`-th root of
`P * P'`, and `σ` acts on `A(k̄)` by a group automorphism, so the quotients multiply. -/
@[faltings "lem_mw_kummer_pairing_additive_left"]
theorem kummerPairing_mul (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P P' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ : kbar ≃ₐ[k] kbar) :
    kummerPairing k kbar A m hm htors (P * P') σ =
      kummerPairing k kbar A m hm htors P σ * kummerPairing k kbar A m hm htors P' σ := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let _ : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    Hom.commGroup
  obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
  obtain ⟨Q, hQ⟩ := exists_pow_eq_of_isAlgClosed k kbar A m (by omega) _
  obtain ⟨Q', hQ'⟩ := exists_pow_eq_of_isAlgClosed k kbar A m (by omega) _
  rw [kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hQ,
    kummerPairing_eq_of_pow_eq k kbar A m hm htors P' σ Q' hQ',
    kummerPairing_eq_of_pow_eq k kbar A m hm htors (P * P') σ (Q * Q')
      (by rw [mul_pow, hQ, hQ', MonObj.comp_mul]), ← he, map_mul]
  simp only [← div_eq_mul_inv, div_mul_div_comm]

end Faltings
