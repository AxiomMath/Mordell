module

public import Mordell.AlgebraicGeometry.GeometricPoint.Galois

/-!
# The Kummer pairing

Let `k` be a number field, `k̄` an algebraic closure of `k`, `G_k = Gal(k̄/k)`, `A` an abelian
variety over `k` and `m ≥ 1`, and assume that every point of `A(k̄)[m]` comes from `A(k)`. For
`P ∈ A(k)` let `Q_P ∈ A(k̄)` be a chosen point with `m Q_P = P` if one exists, and `Q_P = 0`
otherwise. The Kummer pairing is `κ : A(k) × G_k → A(k̄)`, `κ(P, σ) = σ Q_P - Q_P`.

## Main definitions

* `Faltings.kummerPairing`: the Kummer pairing `κ(P, σ) = σ Q_P - Q_P`.

## Implementation notes

A scheme over `k` is an object of `Over (Spec k)`, and an abelian variety is such an object with
a `CategoryTheory.GrpObj` structure whose structure morphism is proper and geometrically
integral. The points `A(k)` are the morphisms from the terminal object `Over.mk (𝟙 (Spec k))`
and `A(k̄)` the morphisms from `Spec k̄`; both are groups under `CategoryTheory.Hom.group`,
written multiplicatively, so `m Q = P` reads `Q ^ m = P` and `σ Q - Q` reads `σ Q * Q⁻¹`.
A point `P ∈ A(k)` is regarded in `A(k̄)` by precomposition with `Spec k̄ → Spec k`.
The choice of `Q_P` is made with `Classical.choose`; by divisibility of `A(k̄)` the second case
never occurs, and the value does not depend on the choice.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3, Definition 3.2
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

/-- The Kummer pairing `κ : A(k) × G_k → A(k̄)`, `κ(P, σ) = σ Q_P - Q_P`, of an abelian variety
`A` over a number field `k` with `A(k̄)[m] ⊆ A(k)`, where `Q_P ∈ A(k̄)` is a chosen point with
`m Q_P = P` if one exists and `Q_P = 0` otherwise. The group law of points is written
multiplicatively. -/
@[faltings "def_mw_kummer_pairing"]
noncomputable def kummerPairing (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (_hm : 1 ≤ m)
    (_htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ : kbar ≃ₐ[k] kbar) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A :=
  letI P' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A :=
    Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P
  letI Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A :=
    open Classical in if h : ∃ Q, Q ^ m = P' then h.choose else 1
  galoisActionPoint k kbar A σ Q * Q⁻¹

end Faltings


/-!
# The Kummer pairing does not depend on the chosen root

Let `A` be an abelian variety over a number field `k` and `m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. For
`P ∈ A(k)`, `σ ∈ G_k` and every `Q ∈ A(k̄)` with `m Q = P`, the Kummer pairing satisfies
`κ(P, σ) = σ Q - Q`: the value of `Faltings.kummerPairing` does not depend on the `m`-th root of
`P` chosen in its construction.

## Main results

* `Faltings.kummerPairing_eq_of_pow_eq`: `κ(P, σ) = σ Q - Q` for every `Q` with `m Q = P`.

## Implementation notes

The group law on points is written multiplicatively (`CategoryTheory.Hom.group`), so `m Q = P`
reads `Q ^ m = P` and `σ Q - Q` reads `σ Q * Q⁻¹`; `P ∈ A(k)` is regarded in `A(k̄)` by
precomposition with `Spec k̄ → Spec k`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- In a commutative group, if an endomorphism `e` fixes `Q / Q₀`, then `Q` and `Q₀` have the
same image under `x ↦ e x / x`. -/
private lemma map_mul_inv_eq_of_map_mul_inv_eq {G : Type*} [CommGroup G] (e : G →* G)
    {Q Q₀ : G} (h : e (Q * Q₀⁻¹) = Q * Q₀⁻¹) : e Q * Q⁻¹ = e Q₀ * Q₀⁻¹ := by
  rw [map_mul, map_inv] at h
  simp only [← div_eq_mul_inv] at h ⊢
  exact div_eq_div_iff_div_eq_div.mpr h

/-- The Kummer pairing is independent of the chosen root: for every `Q ∈ A(k̄)` with
`m Q = P` (written `Q ^ m = P`), `Faltings.kummerPairing` takes the value `σ Q - Q`
(written `galoisActionPoint k kbar A σ Q * Q⁻¹`). -/
@[faltings "lem_mw_kummer_pairing_well_defined"]
theorem kummerPairing_eq_of_pow_eq (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ : kbar ≃ₐ[k] kbar)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (hQ : Q ^ m = Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P) :
    kummerPairing k kbar A m hm htors P σ = galoisActionPoint k kbar A σ Q * Q⁻¹ := by
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let _ : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    Hom.commGroup
  have hex : ∃ Q', Q' ^ m = _ := ⟨Q, hQ⟩
  obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
  obtain ⟨R, hR⟩ := htors (Q * hex.choose⁻¹)
    (by rw [mul_pow, inv_pow, hQ, hex.choose_spec, mul_inv_cancel])
  simp only [kummerPairing, hex, ↓reduceDIte, ← he]
  refine (map_mul_inv_eq_of_map_mul_inv_eq e.toMonoidHom ?_).symm
  simpa [he, ← hR] using galoisActionPoint_homMk_comp k kbar A σ R

end Faltings


/-!
# The Kummer pairing takes values in the `m`-torsion

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. For `P ∈ A(k)` and `σ ∈ G_k`, the value `κ(P, σ) = σ Q_P - Q_P`
of the Kummer pairing is an `m`-torsion point of `A(k̄)`: since `m Q_P = P` is fixed by `σ`,
`m (σ Q_P - Q_P) = σ P - P = 0`.

## Main results

* `Faltings.kummerPairing_pow_eq_one`: `κ(P, σ) ^ m = 1` in the multiplicatively written group
  `A(k̄)`, i.e. `κ(P, σ) ∈ A(k̄)[m]`.

## Implementation notes

The group law of `A(k̄) = (Spec k̄ ⟶ A)` is `CategoryTheory.Hom.group`, written multiplicatively,
so membership in `A(k̄)[m]` reads `κ(P, σ) ^ m = 1`.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- The Kummer pairing `κ(P, σ) = σ Q_P - Q_P` of an abelian variety `A` over a number field `k`
with `A(k̄)[m] ⊆ A(k)` takes values in `A(k̄)[m]`: `Faltings.kummerPairing … P σ ^ m = 1`. -/
@[faltings "lem_mw_kummer_pairing_torsion_values"]
theorem kummerPairing_pow_eq_one (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ : kbar ≃ₐ[k] kbar) :
    kummerPairing k kbar A m hm htors P σ ^ m = 1 := by
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let _ : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    Hom.commGroup
  obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
  by_cases hex : ∃ Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      Q ^ m = Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P
  · obtain ⟨Q, hQ⟩ := hex
    rw [kummerPairing_eq_of_pow_eq k kbar A m hm htors P σ Q hQ, ← he, mul_pow,
      inv_pow, ← map_pow, hQ, he, galoisActionPoint_homMk_comp, mul_inv_cancel]
  · simp only [kummerPairing, hex, ↓reduceDIte, ← he, map_one, inv_one, mul_one, one_pow]

end Faltings


/-!
# The Kummer pairing is additive in the Galois element

Let `A` be an abelian variety over a number field `k` and `m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. For
`P ∈ A(k)` and `σ, τ ∈ G_k` the Kummer pairing satisfies `κ(P, στ) = κ(P, σ) + κ(P, τ)`: for
fixed `P`, `σ ↦ κ(P, σ)` is a homomorphism `G_k → A(k̄)[m]`.

Writing `κ(P, ρ) = ρ Q - Q` for a chosen `Q` with `m Q = P`, one has `(στ) Q = σ (τ Q)`; since
`τ Q - Q` is `m`-torsion it lies in `A(k)` and is fixed by `σ`, whence the identity.

## Main results

* `Faltings.kummerPairing_mul_right`: `κ(P, στ) = κ(P, σ) + κ(P, τ)`.

## Implementation notes

The group law on points is written multiplicatively (`CategoryTheory.Hom.group`), so the
conclusion reads `κ(P, σ * τ) = κ(P, σ) * κ(P, τ)`. The product `σ * τ` in `k̄ ≃ₐ[k] k̄` is the
composite `σ ∘ τ`, as in the source.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MonObj

namespace Faltings

/-- The Kummer pairing is additive in the Galois element: `κ(P, στ) = κ(P, σ) + κ(P, τ)`,
written multiplicatively as `kummerPairing … P (σ * τ) = kummerPairing … P σ *
kummerPairing … P τ`. The torsion point `κ(P, τ)` lies in `A(k)`, so `σ` fixes it. -/
@[faltings "lem_mw_kummer_pairing_additive_right"]
theorem kummerPairing_mul_right (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      T ^ m = 1 → T ∈ Set.range fun P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A =>
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (Category.comp_id _) ≫ P)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) (σ τ : kbar ≃ₐ[k] kbar) :
    kummerPairing k kbar A m hm htors P (σ * τ) =
      kummerPairing k kbar A m hm htors P σ * kummerPairing k kbar A m hm htors P τ := by
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let _ : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    Hom.commGroup
  obtain ⟨e, he⟩ := exists_mulEquiv_coe_eq_galoisActionPoint k kbar A σ
  obtain ⟨R, hR⟩ := htors _ (kummerPairing_pow_eq_one k kbar A m hm htors P τ)
  have hfix : galoisActionPoint k kbar A σ (kummerPairing k kbar A m hm htors P τ) =
      kummerPairing k kbar A m hm htors P τ := by
    rw [← hR]; exact galoisActionPoint_homMk_comp k kbar A σ R
  obtain ⟨Q, hQ⟩ : ∃ Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A,
      ∀ ρ, kummerPairing k kbar A m hm htors P ρ = galoisActionPoint k kbar A ρ Q * Q⁻¹ :=
    ⟨_, fun _ => rfl⟩
  rw [hQ τ, ← he, map_mul, map_inv] at hfix
  rw [hQ, hQ, hQ, ← galoisActionPoint_mul, ← he, ← hfix]
  simp only [← div_eq_mul_inv, mul_comm (e Q / Q), div_mul_div_cancel]

end Faltings
