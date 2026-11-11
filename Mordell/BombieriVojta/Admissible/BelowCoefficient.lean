module
public import Mordell.BombieriVojta.Admissible.Basic
public import Mordell.BombieriVojta.Admissible.BiorderIdeal
public import Mordell.BombieriVojta.Taylor.Expansion

/-!
# An admissible pair below a non-vanishing coefficient

Let `C` be a scheme locally of finite type over a field `K`, `L` a sheaf of modules on
`C ×_K C`, `s ≠ 0` a global section of `L` and `p` a `K`-point of `C ×_K C`, at the point `x`.
Choose local uniformizing parameters `ς`, `ς'` of `C` at the two projections of `x`, a local
generator `e` of `L` at `x`, and put `σ = s / e`. If the image of the germ of `σ` in the completed
local ring does not lie in the ideal `J_{A,B} = 𝔪_z^{A+1} 𝒪̂ + 𝔪_w^{B+1} 𝒪̂`
(`Faltings.completedStalkBiorderIdeal`), then some Taylor coefficient `c_{ij}` of `σ` in
`ς ∘ pr₁`, `ς' ∘ pr₂` (`Faltings.BombieriVojta.taylorCoeff₂`) with `i ≤ A`, `j ≤ B` is nonzero,
and a minimal such index is a pair admissible for `s` at `p`
(`Faltings.BombieriRoth.IsAdmissiblePair`) lying below `(A, B)`.

## Main results

* `Faltings.BombieriRoth.exists_isAdmissiblePair_le_of_notMem_completedStalkBiorderIdeal`: if
  `s / e` is not in `J_{A,B}`, there is an admissible pair `i ≤ (A, B)` for `s` at `p`.

## Implementation notes

The source states the lemma for the line bundle `𝒪(V)` on `C × C` of a curve over a number
field `k`, at a `k̄`-point. The statement is made in the generality of
`Faltings.BombieriRoth.IsAdmissiblePair`: any module sheaf on `C ×_K C`, at any `K`-point, for
`C` locally of finite type over `K`. Finite type makes the local rings of `C ×_K C` noetherian,
so that, by Krull's intersection theorem, a germ whose expansion has no nonzero coefficient in
the box `[0, A] × [0, B]` lies in `J_{A,B}`; this is what the source uses of its curve.

The proof has three steps. Write `ϖ = ς ∘ pr₁` and `ϖ' = ς' ∘ pr₂`.

* The maximal ideal of `𝒪_{C ×_K C, x}` is `(ϖ, ϖ')`: modulo `(ϖ, ϖ')` both projections factor
  through the `K`-points of the factors, so the quotient map factors through evaluation at `x`.
* Hence, by successive approximation, the germ has an expansion `∑ a_{ij} ϖ^i ϖ'^j` with
  `a_{ij} ∈ K`, and the Taylor coefficients are its coefficients.
* If the coefficients in the box `[0, A] × [0, B]` vanish, the germ lies in
  `(ϖ^{A+1}, ϖ'^{B+1}) + 𝔪ⁿ` for every `n`, hence in `(ϖ^{A+1}, ϖ'^{B+1})` by Krull's
  intersection theorem, whose image in the completion lies in `J_{A,B}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, §6, p. 625][bombieri1990]
-/

open AlgebraicGeometry CategoryTheory Limits IsLocalRing Faltings.BombieriVojta

namespace Faltings.BombieriRoth

universe u

section Algebra

variable {R : Type*} [CommRing R] {K : Type*} [Field K]

/-- **Krull's intersection theorem**, in the form used here: in a noetherian local ring an ideal
is closed for the `𝔪`-adic topology. -/
private theorem mem_of_forall_mem_sup_pow [IsNoetherianRing R] [IsLocalRing R] (J : Ideal R)
    {f : R} (h : ∀ n : ℕ, f ∈ J ⊔ maximalIdeal R ^ n) : f ∈ J := by
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := R ⧸ J)
    (I := maximalIdeal R) (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot R, ← key, Submodule.mem_iInf]
  intro n
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
  have : Ideal.Quotient.mk J (a + b) = b • (1 : R ⧸ J) := by
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, Algebra.smul_def, mul_one]
    rfl
  rw [this]
  exact Submodule.smul_mem_smul hb Submodule.mem_top

/-- A truncated expansion with no coefficient in the box `[0, A] × [0, B]` lies in
`(ϖ ^ (A + 1), ϖ' ^ (B + 1))`. -/
private theorem sum_mem_of_coeff_eq_zero (c : K →+* R) (ϖ ϖ' : R)
    (F : MvPowerSeries (Fin 2) K) {A B : ℕ}
    (hF : ∀ j : ℕ × ℕ, j ≤ (A, B) → MvPowerSeries.coeff (bidegree j) F = 0) (n : ℕ) :
    ∑ j ∈ Finset.range n ×ˢ Finset.range n,
        c (MvPowerSeries.coeff (bidegree j) F) * ϖ ^ j.1 * ϖ' ^ j.2 ∈
      Ideal.span {ϖ ^ (A + 1)} ⊔ Ideal.span {ϖ' ^ (B + 1)} := by
  refine Ideal.sum_mem _ fun j _ => ?_
  by_cases h1 : j.1 ≤ A
  · by_cases h2 : j.2 ≤ B
    · rw [hF j (Prod.le_def.2 ⟨h1, h2⟩)]
      simp
    · refine Ideal.mem_sup_right (Ideal.mul_mem_left _ _ ?_)
      exact Ideal.mem_span_singleton.2 (pow_dvd_pow ϖ' (show B + 1 ≤ j.2 by omega))
  · refine Ideal.mem_sup_left ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.mem_span_singleton.2 (pow_dvd_pow ϖ (show A + 1 ≤ j.1 by omega))

/-- In a noetherian local ring with maximal ideal `(ϖ, ϖ')`, an element whose expansion has no
coefficient in the box `[0, A] × [0, B]` lies in `(ϖ ^ (A + 1), ϖ' ^ (B + 1))`. -/
private theorem mem_span_pow_sup_of_coeff_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    {ϖ ϖ' : R} (hϖ : maximalIdeal R = Ideal.span {ϖ, ϖ'}) (c : K →+* R) {f : R}
    {F : MvPowerSeries (Fin 2) K}
    (hF : IsExpansion₂ c ϖ ϖ' F f) {A B : ℕ}
    (h0 : ∀ j : ℕ × ℕ, j ≤ (A, B) → MvPowerSeries.coeff (bidegree j) F = 0) :
    f ∈ Ideal.span {ϖ ^ (A + 1)} ⊔ Ideal.span {ϖ' ^ (B + 1)} :=
  mem_of_forall_mem_sup_pow _ fun n => by
    rw [← sub_add_cancel f (∑ j ∈ Finset.range n ×ˢ Finset.range n,
      c (MvPowerSeries.coeff (bidegree j) F) * ϖ ^ j.1 * ϖ' ^ j.2)]
    exact add_mem (Ideal.mem_sup_right (hϖ ▸ hF n))
      (Ideal.mem_sup_left (sum_mem_of_coeff_eq_zero c ϖ ϖ' F h0 n))

/-- Below an index at which `c` does not vanish there is a minimal such index. -/
private theorem exists_le_ne_zero_minimal {ι M : Type*} [PartialOrder ι] [WellFoundedLT ι]
    [Zero M] {c : ι → M} {a : ι} (ha : ∃ j ≤ a, c j ≠ 0) :
    ∃ i ≤ a, c i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c j = 0 := by
  obtain ⟨i, ⟨hia, hi⟩, hmin⟩ := wellFounded_lt.has_min {j | j ≤ a ∧ c j ≠ 0} ha
  exact ⟨i, hia, hi, fun j hji hne =>
    by_contra fun hj => hmin j ⟨hji.trans hia, hj⟩ (lt_of_le_of_ne hji hne)⟩

end Algebra

section Geometry

variable {K : Type u} [Field K]

/-- At a `K`-point `p` of `X`, the Taylor coefficients of `f` are the coefficients of an
expansion of `f` in `ϖ, ϖ'`, as soon as the maximal ideal of the local ring is `(ϖ, ϖ')`. -/
private theorem taylorCoeff₂_spec {X : Scheme.{u}} [X.Over (Spec (.of K))] (p : Spec (.of K) ⟶ X)
    [p.IsOver (Spec (.of K))] {ϖ ϖ' : X.presheaf.stalk (p (closedPoint K))}
    (hϖ : maximalIdeal (X.presheaf.stalk (p (closedPoint K))) = Ideal.span {ϖ, ϖ'})
    (f : X.presheaf.stalk (p (closedPoint K))) :
    ∃ F, IsExpansion₂ (const (p (closedPoint K))) ϖ ϖ' F f ∧
      ∀ i₁ i₂, taylorCoeff₂ p ϖ ϖ' f i₁ i₂ = MvPowerSeries.coeff (bidegree (i₁, i₂)) F :=
  ⟨_, Classical.epsilon_spec (exists_isExpansion₂ hϖ _ (Scheme.stalkClosedPointTo p).hom
    (ev_const p (comp_over_eq_id p)) f), fun _ _ => rfl⟩

/-- For `ς`, `ς'` in the maximal ideals of the factors at the projections of `x`, the ideal
`((ς ∘ pr₁) ^ (A + 1), (ς' ∘ pr₂) ^ (B + 1))` of the stalk at `x` maps into `J_{A,B}`. -/
private theorem span_pow_sup_le_comap_completedStalkBiorderIdeal {T X Y : Scheme.{u}}
    {f : X ⟶ T} {g : Y ⟶ T} {x : ↥(pullback f g)} {ς : X.presheaf.stalk (pullback.fst f g x)}
    {ς' : Y.presheaf.stalk (pullback.snd f g x)} (hς : ς ∈ maximalIdeal _)
    (hς' : ς' ∈ maximalIdeal _) (A B : ℕ) :
    Ideal.span {(pullback.fst f g).stalkMap x ς ^ (A + 1)} ⊔
        Ideal.span {(pullback.snd f g).stalkMap x ς' ^ (B + 1)} ≤
      (Faltings.completedStalkBiorderIdeal f g x A B).comap (algebraMap _ _) := by
  refine sup_le ?_ ?_ <;>
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  · refine Ideal.mem_sup_left ?_
    convert Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hς (A + 1)) using 1
    simp
  · refine Ideal.mem_sup_right ?_
    convert Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hς' (B + 1)) using 1
    simp

end Geometry

/-- Let `ς`, `ς'` be local uniformizing parameters of `C` at the projections of the `K`-point
`p` of `C ×_K C`, `e` a local generator of `L` on a neighbourhood `U` of `p`, and `σ = s / e`.
If the image of the germ of `σ` in the completed local ring at `p` is not in
`J_{A,B}` (`Faltings.completedStalkBiorderIdeal`), then there is a pair `i ≤ (A, B)` admissible
for `s` at `p`. -/
@[faltings "lem_bvr_admissible_below"]
public theorem exists_isAdmissiblePair_le_of_notMem_completedStalkBiorderIdeal {K : Type u}
    [Field K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
    [LocallyOfFiniteType (C ↘ Spec (.of K))]
    {L : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Modules} {s : Γ(L, ⊤)} (hs : s ≠ 0)
    {p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))}
    [p.IsOver (Spec (.of K))]
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
    (hσ : σ • e = L.presheaf.map (homOfLE le_top).op s) {A B : ℕ}
    (hJ : algebraMap _ _
        ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.germ U _ hxU σ) ∉
      completedStalkBiorderIdeal (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K)) A B) :
    ∃ i ≤ (A, B), IsAdmissiblePair L s p i := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of K))
  have hzC : (p ≫ pullback.fst _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact comp_over_eq_id p
  have hzD : (p ≫ pullback.snd _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _ :=
    (Category.assoc _ _ _).trans (comp_over_eq_id p)
  have hm : maximalIdeal ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk
        (p (closedPoint K))) =
      Ideal.span {(pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς,
        (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς'} :=
    maximalIdeal_stalk_pullback_eq_span p (comp_over_eq_id p) hzC hzD hς hς'
  obtain ⟨F, hF, hcoeff⟩ := taylorCoeff₂_spec p hm
    ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.germ U _ hxU σ)
  obtain ⟨i, hiAB, hi0, hmin⟩ := exists_le_ne_zero_minimal
      (c := fun j : ℕ × ℕ => MvPowerSeries.coeff (bidegree j) F) (a := (A, B)) <| by
    by_contra! h0
    exact hJ (span_pow_sup_le_comap_completedStalkBiorderIdeal
      (hς ▸ Ideal.mem_span_singleton_self ς) (hς' ▸ Ideal.mem_span_singleton_self ς') A B
      (mem_span_pow_sup_of_coeff_eq_zero hm _ hF h0))
  refine ⟨i, hiAB, hs, ς, ς', hς, hς', U, hxU, e, he, σ, hσ, ?_⟩
  simpa only [hcoeff] using And.intro hi0 hmin

end Faltings.BombieriRoth

