module
public import Mordell.BombieriVojta.Taylor.CurveProduct
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import Mordell.BombieriVojta.Taylor.Expansion

/-!
# Taylor coefficients of a product of functions of one variable each

Let `C` and `D` be smooth curves over a field `K`, `p = (z, w)` a `K`-rational point of
`C ×_K D`, `ς` a uniformizer of `C` at `z` and `ς'` one of `D` at `w`. For a function `ũ` on `C`
regular at `z` and `ũ'` on `D` regular at `w`, put `u = ũ ∘ pr₁` and `u' = ũ' ∘ pr₂`. The
expansion of `u` in `K⟦ς, ς'⟧` is the expansion of `ũ` in `K⟦ς⟧`, a series in `ς` alone, and
likewise for `u'` in `ς'`; hence the coefficient of `ς ^ a * ς' ^ b` in `u u'` is the product
`∂_a ũ(z) · ∂'_b ũ'(w)` of the one-variable Taylor coefficients.

## Main results

* `taylorCoeff₂_stalkMap_fst_mul_stalkMap_snd`:
  `∂_a ∂'_b (u u')(p) = ∂_a ũ(z) · ∂'_b ũ'(w)`.

## Implementation notes

The `K`-point `(z, w)` is a `K`-point `p` of the fibre product `C ×_K D`, with `z = p ≫ pr₁`
and `w = p ≫ pr₂`; functions regular at a point are elements of the stalk there, and composition
with a projection is its stalk map `Scheme.Hom.stalkMap`. The statement is made for two curves
`C`, `D`; the source's case is `D = C`.

The proof avoids completions. Expanding in powers of `ς` gives, by uniqueness of expansions in the
domain `𝒪_{C,z}` (where `ς ≠ 0` since `𝒪_{C,z}` has dimension one), a ring homomorphism
`𝒪_{C,z} → K⟦X⟧` sending `ς` to `X`; likewise for `D`. Composing with the two embeddings
`K⟦X⟧ → K⟦X₀, X₁⟧` and gluing through the universal property of the fibre product and
`AlgebraicGeometry.SpecToEquivOfLocalRing` gives `Ψ : 𝒪_{C ×_K D, p} → K⟦X₀, X₁⟧` with
`Ψ (ς ∘ pr₁) = X₀` and `Ψ (ς' ∘ pr₂) = X₁`. Through `Ψ` an expansion in `ς ∘ pr₁, ς' ∘ pr₂` is
unique, and the product of the two one-variable expansions is an expansion of `u u'`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 626
-/

open AlgebraicGeometry CategoryTheory IsLocalRing Limits

universe u

namespace Faltings.BombieriVojta

/-- Let `C`, `D` be smooth curves over `K`, `p` a `K`-point of `C ×_K D` with coordinates
`z = p ≫ pr₁`, `w = p ≫ pr₂`, `ς` a uniformizer at `z` and `ς'` one at `w`. For `ũ` regular at
`z` and `ũ'` regular at `w`, the Taylor coefficient of `(ũ ∘ pr₁) (ũ' ∘ pr₂)` at `p` with
respect to `(ς ∘ pr₁, ς' ∘ pr₂)` is
`∂_a ∂'_b ((ũ ∘ pr₁) (ũ' ∘ pr₂))(p) = ∂_a ũ(z) · ∂'_b ũ'(w)`. -/
@[faltings "lem_bv_divided_leibniz_separated"]
public theorem taylorCoeff₂_stalkMap_fst_mul_stalkMap_snd {K : Type u} [Field K]
    {C D : Scheme.{u}} [C.Over (Spec (.of K))] [D.Over (Spec (.of K))]
    [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [IsCurve K (D ↘ Spec (.of K))] [Smooth (D ↘ Spec (.of K))]
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (D ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))]
    (ς ũ : C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K)))
    (ς' ũ' : D.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K)))
    (hς : maximalIdeal (C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K))) =
      Ideal.span {ς})
    (hς' : maximalIdeal (D.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))) =
      Ideal.span {ς'})
    (a b : ℕ) :
    taylorCoeff₂ p
        ((pullback.fst (C ↘ Spec (.of K)) (D ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
        ((pullback.snd (C ↘ Spec (.of K)) (D ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
        ((pullback.fst (C ↘ Spec (.of K)) (D ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ũ *
          (pullback.snd (C ↘ Spec (.of K)) (D ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ũ')
        a b =
      taylorCoeff (p ≫ pullback.fst _ _) ς ũ a * taylorCoeff (p ≫ pullback.snd _ _) ς' ũ' b := by
  have hzD : (p ≫ pullback.snd _ _) ≫ (D ↘ Spec (.of K)) = 𝟙 _ :=
    (Category.assoc _ _ _).trans (comp_over_eq_id p)
  have hzC : (p ≫ pullback.fst _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact comp_over_eq_id p
  obtain ⟨Ψ, hΨc, hΨ0, hΨ1⟩ := exists_ringHom_mvPowerSeries p hzC hzD hς hς'
  rw [taylorCoeff₂_eq_coeff Ψ hΨc hΨ0 hΨ1 (isExpansion₂_mul _ _ _ (const _) (const _)
    (fun a ↦ (const_comp (pullback.fst _ _) pullback.condition _ a).symm)
    (fun a ↦ (const_comp (pullback.snd _ _) rfl _ a).symm)
    (isExpansion_taylorCoeff _ hzC hς ũ) (isExpansion_taylorCoeff _ hzD hς' ũ'))]
  change PowerSeries.coeff _ (PowerSeries.mk (taylorCoeff _ ς ũ)) *
    PowerSeries.coeff _ (PowerSeries.mk (taylorCoeff _ ς' ũ')) = _
  simp

end Faltings.BombieriVojta
