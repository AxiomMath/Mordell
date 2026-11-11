module
public import Mordell.BombieriVojta.Admissible.Basic
public import Mordell.BombieriVojta.Taylor.Expansion

/-!
# Admissibility is intrinsic

Let `C` be a smooth curve over a field `K`, `L` a sheaf of modules on `C ×_K C`, `s` a global
section of `L` and `p` a `K`-point of `C ×_K C`. If `(i₁*, i₂*)` is admissible for `s` at `p`
(`Faltings.BombieriRoth.IsAdmissiblePair`), i.e. the coefficient condition holds for *some*
choice of local uniformizing parameters `ς, ς'` at the projections of `p` and of a local
generator `e` of `L` at `p`, then it holds for *every* such choice: writing
`s / e = ∑ c_{ij} ς^i ς'^j`, we have `c_{i₁* i₂*} ≠ 0` and `c_{i₁ i₂} = 0` for
`(i₁, i₂) ≤ (i₁*, i₂*)`, `(i₁, i₂) ≠ (i₁*, i₂*)`.

The reason is that `(i₁*, i₂*)` is admissible for a choice exactly when it is a minimal element of
the complement of `{(A, B) : σ ∈ J_{A,B}}`, where `J_{A,B} = 𝔪_z^{A+1} + 𝔪_w^{B+1}` in the
completed local ring, with `𝔪_z, 𝔪_w` the maximal ideals at the projections of `p`.
That set depends neither on the uniformizers nor on `e`, because changing `e` multiplies `σ` by a
unit.

## Main results

* `Faltings.BombieriRoth.IsAdmissiblePair.taylorCoeff₂`: an admissible pair satisfies the
  coefficient condition for every choice of uniformizers and local generator.

## Implementation notes

The source states this for the line bundle `𝒪(V)` on `C × C`, where `C` is a smooth projective
curve over `k̄`. The proof uses only that `C` is a curve over `K` (`IsCurve`): with the
uniformizer hypotheses this makes `(ς ∘ pr₁, ς' ∘ pr₂)` a system of parameters at `p` and the
expansion `Faltings.BombieriVojta.taylorCoeff₂` unique, and without it the statement fails. The
hypothesis `Smooth` is the source's and is kept.

The source works with the ideals `J_{A,B} = 𝔪_z^{A+1} 𝒪̂_p + 𝔪_w^{B+1} 𝒪̂_p` of the completion.
Here they are replaced by the conditions `σ ∈ 𝔪_z^{A+1} 𝒪_p + 𝔪_w^{B+1} 𝒪_p + 𝔪_pⁿ` for all `n`,
i.e. membership in the `𝔪_p`-adic closure of `𝔪_z^{A+1} 𝒪_p + 𝔪_w^{B+1} 𝒪_p`, and the completion is
never formed. That these conditions detect the vanishing of the coefficients on a box rests on two
facts about `𝒪_p`: its maximal ideal is `(ς ∘ pr₁, ς' ∘ pr₂)`, by the universal property of the
fibre product, and there is a ring homomorphism `𝒪_p → K⟦X₀, X₁⟧` sending `ς ∘ pr₁, ς' ∘ pr₂` to
`X₀, X₁`, glued from the one-variable expansions on the two factors.

## References

* [Bombieri, *The Mordell conjecture revisited*, §6, p. 625][bombieri1990]
-/

open AlgebraicGeometry CategoryTheory Limits IsLocalRing Faltings.BombieriVojta

namespace Faltings.BombieriRoth

universe u

section Algebra

variable {K O : Type*} [Field K] [CommRing O] {c : K →+* O} {ϖ ϖ' : O}
  (Ψ : O →+* MvPowerSeries (Fin 2) K)

/-- If `Ψ ϖ = X_i`, then `Ψ (ϖ ^ k * t)` has no coefficient whose `i`-th exponent is `< k`. -/
private theorem coeff_map_pow_mul_eq_zero {x : O} {i : Fin 2} (hx : Ψ x = MvPowerSeries.X i)
    {k : ℕ} (t : O) {e : Fin 2 →₀ ℕ} (he : e i < k) :
    MvPowerSeries.coeff e (Ψ (x ^ k * t)) = 0 :=
  (MvPowerSeries.X_pow_dvd_iff (s := i) (n := k)).1
    (by rw [map_mul, map_pow, hx]; exact dvd_mul_right _ _) e he

/-- Membership of `f` in `(ϖ^{A+1}, ϖ'^{B+1}) + (ϖ, ϖ')ⁿ` for every `n` is the vanishing of the
coefficients of `Ψ f` in the box `[0, A] × [0, B]`. -/
private theorem forall_mem_sup_pow_iff (h0 : Ψ ϖ = MvPowerSeries.X 0)
    (h1 : Ψ ϖ' = MvPowerSeries.X 1) {f : O}
    (hF : IsExpansion₂ c ϖ ϖ' (Ψ f) f) (a : ℕ × ℕ) :
    (∀ n, f ∈ Ideal.span {ϖ ^ (a.1 + 1)} ⊔ Ideal.span {ϖ' ^ (a.2 + 1)} ⊔
      Ideal.span {ϖ, ϖ'} ^ n) ↔ ∀ j ≤ a, MvPowerSeries.coeff (bidegree j) (Ψ f) = 0 := by
  refine ⟨fun h j hj => ?_, fun h n => ?_⟩
  · obtain ⟨hj1, hj2⟩ := Prod.le_def.1 hj
    obtain ⟨y, hy, r, hr, hyr⟩ := Submodule.mem_sup.1 (h (j.1 + j.2 + 1))
    obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton.1 hz
    rw [← hyr, map_add, map_add, map_add, map_add,
      coeff_map_eq_zero_of_mem_pow Ψ h0 h1 hr (by rw [degree_bidegree]; omega), add_zero,
      coeff_map_pow_mul_eq_zero Ψ h0 _ (by simp; omega),
      coeff_map_pow_mul_eq_zero Ψ h1 _ (by simp; omega), add_zero]
  · have hn := hF n
    rw [show f = (f - ∑ j ∈ Finset.range n ×ˢ Finset.range n,
        c (MvPowerSeries.coeff (bidegree j) (Ψ f)) * ϖ ^ j.1 * ϖ' ^ j.2) +
        ∑ j ∈ Finset.range n ×ˢ Finset.range n,
        c (MvPowerSeries.coeff (bidegree j) (Ψ f)) * ϖ ^ j.1 * ϖ' ^ j.2 by ring]
    refine add_mem (Ideal.mem_sup_right hn) (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => ?_))
    by_cases hj : j ≤ a
    · simp [h j hj]
    · rw [Prod.le_def, not_and_or, not_le, not_le] at hj
      rcases hj with hj | hj
      · exact Ideal.mem_sup_left (Ideal.mem_span_singleton.2
          (((pow_dvd_pow _ hj).mul_left _).mul_right _))
      · exact Ideal.mem_sup_right (Ideal.mem_span_singleton.2 ((pow_dvd_pow _ hj).mul_left _))

end Algebra

/-- A minimal element of the support is detected by the downward-closed sets
`{a | ∀ j ≤ a, c j = 0}`: if two families have the same such sets, they have the same minimal
elements of their supports. -/
private theorem minimal_of_forall_le_iff {K : Type*} [Zero K] {c₁ c₂ : ℕ × ℕ → K}
    (h : ∀ a, (∀ j ≤ a, c₁ j = 0) ↔ (∀ j ≤ a, c₂ j = 0)) {i : ℕ × ℕ}
    (hi : c₁ i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c₁ j = 0) : c₂ i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c₂ j = 0 := by
  have hlt : ∀ j ≤ i, j ≠ i → c₂ j = 0 := fun j hj hji =>
    (h j).1 (fun j' hj' => hi.2 j' (hj'.trans hj) fun e => hji (le_antisymm hj (e ▸ hj'))) j le_rfl
  refine ⟨fun h0 => hi.1 ((h i).2 (fun j hj => ?_) i le_rfl), hlt⟩
  by_cases hji : j = i
  · exact hji ▸ h0
  · exact hlt j hj hji

/-- If `e₁` and `e₂` are local generators of `L` near `x`, the quotients `σ₁ = s / e₁` and
`σ₂ = s / e₂` differ, in the local ring at `x`, by a unit. -/
private theorem exists_isUnit_germ_eq_germ_mul {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))
    {x : X} {U₁ U₂ : X.Opens} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) {e₁ : Γ(L, U₁)} {e₂ : Γ(L, U₂)}
    (he₁ : ∀ (V : X.Opens) (hV : V ≤ U₁),
      Function.Bijective fun a : Γ(X, V) => a • L.presheaf.map (homOfLE hV).op e₁)
    (he₂ : ∀ (V : X.Opens) (hV : V ≤ U₂),
      Function.Surjective fun a : Γ(X, V) => a • L.presheaf.map (homOfLE hV).op e₂)
    {σ₁ : Γ(X, U₁)} {σ₂ : Γ(X, U₂)} (hσ₁ : σ₁ • e₁ = L.presheaf.map (homOfLE le_top).op s)
    (hσ₂ : σ₂ • e₂ = L.presheaf.map (homOfLE le_top).op s) :
    ∃ v, IsUnit v ∧ X.presheaf.germ U₁ x hx₁ σ₁ = X.presheaf.germ U₂ x hx₂ σ₂ * v := by
  set V := U₁ ⊓ U₂
  have h1 : V ≤ U₁ := inf_le_left
  have h2 : V ≤ U₂ := inf_le_right
  have hres : ∀ {W : X.Opens} (hW : V ≤ W) (t : Γ(L, ⊤)),
      L.presheaf.map (homOfLE hW).op (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) =
        L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t := fun _ _ => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨b, hb⟩ := (he₁ V h1).2 (L.presheaf.map (homOfLE h2).op e₂)
  obtain ⟨a, ha⟩ := he₂ V h2 (L.presheaf.map (homOfLE h1).op e₁)
  dsimp only at hb ha
  have hab : a * b = 1 := (he₁ V h1).1 (by dsimp only; rw [mul_smul, hb, ha, one_smul])
  have hσV : X.presheaf.map (homOfLE h1).op σ₁ = X.presheaf.map (homOfLE h2).op σ₂ * b :=
    (he₁ V h1).1 (by
      dsimp only
      rw [← Scheme.Modules.map_smul, hσ₁, mul_smul, hb, ← Scheme.Modules.map_smul, hσ₂, hres,
        hres])
  have hxV : x ∈ V := ⟨hx₁, hx₂⟩
  refine ⟨X.presheaf.germ V x hxV b,
    (show IsUnit b from ⟨⟨b, a, (mul_comm b a).trans hab, hab⟩, rfl⟩).map _, ?_⟩
  rw [← X.presheaf.germ_res_apply (homOfLE h1) x hxV σ₁, hσV, map_mul,
    X.presheaf.germ_res_apply (homOfLE h2) x hxV σ₂]

/-- For one choice of uniformizers `ς, ς'`, the condition `f ∈ 𝔪_z^{A+1} + 𝔪_w^{B+1} + 𝔪_pⁿ`
for all `n`, which does not mention the uniformizers, says that the Taylor coefficients of `f`
in `ς ∘ pr₁, ς' ∘ pr₂` vanish on the box `[0, A] × [0, B]`. -/
private theorem forall_mem_iff_taylorCoeff₂ {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))]
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))]
    (ς : C.presheaf.stalk
      (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (ς' : C.presheaf.stalk
      (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'})
    (f : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk (p (closedPoint K)))
    (a : ℕ × ℕ) :
    (∀ n, f ∈ (maximalIdeal (C.presheaf.stalk
        (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K)))) ^ (a.1 + 1)).map
          ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K))).hom ⊔
        (maximalIdeal (C.presheaf.stalk
        (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K)))) ^ (a.2 + 1)).map
          ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K))).hom ⊔
        maximalIdeal _ ^ n) ↔
      ∀ j ≤ a, taylorCoeff₂ p
        ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
        ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
        f j.1 j.2 = 0 := by
  have hp := comp_over_eq_id p
  have hzD : (p ≫ pullback.snd _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _ :=
    (Category.assoc _ _ _).trans hp
  have hzC : (p ≫ pullback.fst _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _ := by
    rwa [Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨Ψ, hΨc, hΨ0, hΨ1⟩ := exists_ringHom_mvPowerSeries p hzC hzD hς hς'
  have hm := maximalIdeal_stalk_pullback_eq_span p hp hzC hzD hς hς'
  have hF := isExpansion₂_map Ψ hm _ (ev_const p hp) hΨc hΨ0 hΨ1 f
  have ht : ∀ j : ℕ × ℕ, taylorCoeff₂ p _ _ f j.1 j.2 =
      MvPowerSeries.coeff (bidegree j) (Ψ f) := fun j =>
    taylorCoeff₂_eq_coeff Ψ hΨc hΨ0 hΨ1 hF j.1 j.2
  simp_rw [ht]
  rw [← forall_mem_sup_pow_iff Ψ hΨ0 hΨ1 hF a, hm, hς, hς', Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, map_pow, map_pow]
  exact Iff.rfl

/-- If `i` is admissible for `s` at `p`, then for every choice of local uniformizing parameters
`ς, ς'` of `C` at the two projections of `p`, every local generator `e` of `L` on an open
`U ∋ p`, and `σ` with `σ • e = s|_U`, the Taylor coefficients `c_j` of `σ` in `ς ∘ pr₁, ς' ∘ pr₂`
satisfy `c_i ≠ 0` and `c_j = 0` for every `j ≤ i` with `j ≠ i`. -/
@[faltings "lem_bvr_admissible_intrinsic"]
public theorem IsAdmissiblePair.taylorCoeff₂ {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    {L : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Modules} {s : Γ(L, ⊤)}
    {p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))}
    [p.IsOver (Spec (.of K))] {i : ℕ × ℕ} (h : IsAdmissiblePair L s p i)
    (ς : C.presheaf.stalk
      (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (ς' : C.presheaf.stalk
      (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'})
    (U : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Opens) (hxU : p (closedPoint K) ∈ U)
    (e : Γ(L, U))
    (he : ∀ (V : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Opens) (hVU : V ≤ U),
      Function.Bijective fun a : Γ(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)), V) =>
        a • L.presheaf.map (homOfLE hVU).op e)
    (σ : Γ(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)), U))
    (hσ : σ • e = L.presheaf.map (homOfLE le_top).op s) :
    let c : ℕ × ℕ → K := fun j => BombieriVojta.taylorCoeff₂ p
      ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
      ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
      ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.germ U _ hxU σ) j.1 j.2
    c i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c j = 0 := by
  intro c
  obtain ⟨-, ς₁, ς₁', hς₁, hς₁', U₁, hxU₁, e₁, he₁, σ₁, hσ₁, hc₁⟩ := h
  obtain ⟨v, hv, hσv⟩ := exists_isUnit_germ_eq_germ_mul L s hxU₁ hxU he₁
    (fun V hV => (he V hV).2) hσ₁ hσ
  refine minimal_of_forall_le_iff (c₁ := fun j => BombieriVojta.taylorCoeff₂ p
      ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς₁)
      ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς₁')
      ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.germ U₁ _ hxU₁ σ₁) j.1 j.2)
    (c₂ := c) (fun a => ?_) hc₁
  rw [← forall_mem_iff_taylorCoeff₂ p ς₁ ς₁' hς₁ hς₁' _ a,
    ← forall_mem_iff_taylorCoeff₂ p ς ς' hς hς' _ a, hσv]
  simp only [Ideal.mul_unit_mem_iff_mem _ hv]

end Faltings.BombieriRoth
