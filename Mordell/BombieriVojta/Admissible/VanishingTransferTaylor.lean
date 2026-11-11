module

public import Mordell.BombieriVojta.Admissible.BiorderIdeal
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Norm.Relation
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.Polynomial.HasseDeriv
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.BombieriVojta.Norm.SectionRatioEval
public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass

/-!
# Taylor coefficients from membership in `J_{A,B}`

At a `K`-point `(z, w)` of `C ×_K C`, if a germ lies in `J_{A,B}` then, read through an
identification of the completed local ring with `K⟦X₀, X₁⟧`, the divided derivatives `∂_I Q` vanish
at `(t₀, t₀')` for `I ≤ (A, B)` (`VanishingTransfer.Taylor.eval_hasseDeriv_eq_zero_of_mem`).
-/

universe u

namespace Faltings.BombieriRoth.VanishingTransfer

/-! ### Taylor coefficients at `(t₀, t₀')` from membership in `J_{A,B}` -/

namespace Taylor

open _root_.MvPolynomial

variable {K : Type*} [CommRing K]

private theorem C_add_X_pow_eq_sum (μ : Fin 2) (a : K) (j : ℕ) :
    (C a + X μ : MvPolynomial (Fin 2) K) ^ j =
      ∑ k ∈ Finset.range (j + 1),
        monomial (Finsupp.single μ k) (a ^ (j - k) * (j.choose k : K)) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [X_pow_eq_monomial, ← C_pow, ← map_natCast C, mul_assoc, ← map_mul, mul_comm,
    C_mul_monomial, mul_one]

private theorem single_add_single_eq_iff (k l : ℕ) (I : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) k + Finsupp.single 1 l = I ↔ k = I 0 ∧ l = I 1 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩
    ext μ; fin_cases μ <;> simp

private theorem coeff_aeval_C_add_X (Q : MvPolynomial (Fin 2) K) (x : Fin 2 → K) (I : Fin 2 →₀ ℕ) :
    (aeval (fun μ => C (x μ) + X μ) Q).coeff I = eval x (Faltings.MvPolynomial.hasseDeriv I Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, hp, hq]
  | monomial J r =>
    rw [Faltings.MvPolynomial.hasseDeriv_monomial, aeval_monomial, Finsupp.prod_fintype _ _
      (fun _ => pow_zero _), Fin.prod_univ_two, C_add_X_pow_eq_sum, C_add_X_pow_eq_sum,
      Finset.sum_mul_sum, Finset.mul_sum, coeff_sum]
    simp only [Finset.mul_sum, coeff_sum, monomial_mul, algebraMap_eq, C_mul_monomial,
      coeff_monomial, single_add_single_eq_iff]
    have hprod : (∏ μ ∈ I.support, (J μ).choose (I μ)) =
        (J 0).choose (I 0) * (J 1).choose (I 1) := by
      rw [Finset.prod_subset (Finset.subset_univ _) (fun μ _ hμ => by
        rw [Finsupp.notMem_support_iff.mp hμ, Nat.choose_zero_right]), Fin.prod_univ_two]
    rw [hprod, smul_eval, eval_monomial, Finsupp.prod_fintype _ _
      (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Finsupp.coe_tsub, Pi.sub_apply]
    rw [Finset.sum_eq_single (I 0), Finset.sum_eq_single (I 1)]
    · simp only [and_self, if_true]
      push_cast; ring
    · intro l _ hl; rw [if_neg fun h => hl h.2]
    · intro hl; rw [Finset.mem_range, not_lt] at hl
      simp [Nat.choose_eq_zero_of_lt (show J 1 < I 1 by omega)]
    · intro k _ hk; exact Finset.sum_eq_zero fun l _ => if_neg fun h => hk h.1
    · intro hk; rw [Finset.mem_range, not_lt] at hk
      simp [Nat.choose_eq_zero_of_lt (show J 0 < I 0 by omega)]

private theorem map_mem_box_of_algebraMap_mem {K O : Type*} [Field K] [CommRing O] (𝔪 : Ideal O)
    {ϖ ϖ' : O} (h𝔪 : 𝔪 = Ideal.span {ϖ, ϖ'}) (Ψ : O →+* MvPowerSeries (Fin 2) K)
    (h0 : Ψ ϖ = MvPowerSeries.X 0) (h1 : Ψ ϖ' = MvPowerSeries.X 1) (A B : ℕ) (a : O)
    (ha : algebraMap O (AdicCompletion 𝔪 O) a ∈
      (Ideal.span {ϖ ^ (A + 1)}).map (algebraMap O (AdicCompletion 𝔪 O)) ⊔
        (Ideal.span {ϖ' ^ (B + 1)}).map (algebraMap O (AdicCompletion 𝔪 O))) :
    Ψ a ∈ Ideal.span {MvPowerSeries.X 0 ^ (A + 1)} ⊔ Ideal.span {MvPowerSeries.X 1 ^ (B + 1)} := by
  set Box : Ideal (MvPowerSeries (Fin 2) K) :=
    Ideal.span {MvPowerSeries.X 0 ^ (A + 1)} ⊔ Ideal.span {MvPowerSeries.X 1 ^ (B + 1)}
  let θ : O →+* MvPowerSeries (Fin 2) K ⧸ Box := (Ideal.Quotient.mk Box).comp Ψ
  have hθ : ∀ x, θ x = 0 ↔ Ψ x ∈ Box := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hϖ : θ (ϖ ^ (A + 1)) = 0 := (hθ _).2 <| by
    rw [map_pow, h0]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hϖ' : θ (ϖ' ^ (B + 1)) = 0 := (hθ _).2 <| by
    rw [map_pow, h1]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hrad : 𝔪 ≤ (RingHom.ker θ).radical := by
    rw [h𝔪, Ideal.span_le]
    rintro _ (rfl | rfl)
    exacts [⟨A + 1, hϖ⟩, ⟨B + 1, hϖ'⟩]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (h𝔪 ▸ Submodule.fg_span (Set.toFinite _))
  let Θ : AdicCompletion 𝔪 O →+* MvPowerSeries (Fin 2) K ⧸ Box :=
    (Ideal.Quotient.lift (𝔪 ^ n) θ fun x hx => hn hx).comp (AdicCompletion.evalₐ 𝔪 n).toRingHom
  have hΘ : ∀ x, Θ (algebraMap O _ x) = θ x := by
    intro x
    change Ideal.Quotient.lift (𝔪 ^ n) θ (fun x hx => hn hx)
      (AdicCompletion.evalₐ 𝔪 n (algebraMap O _ x)) = θ x
    rw [AlgHom.commutes]
    rfl
  have hle : (Ideal.span {ϖ ^ (A + 1)}).map (algebraMap O (AdicCompletion 𝔪 O)) ⊔
      (Ideal.span {ϖ' ^ (B + 1)}).map (algebraMap O (AdicCompletion 𝔪 O)) ≤ RingHom.ker Θ := by
    refine sup_le ?_ ?_ <;> rw [Ideal.map_le_iff_le_comap, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, hΘ]
    exacts [hϖ, hϖ']
  have := hle ha
  rwa [RingHom.mem_ker, hΘ, hθ] at this

private theorem coeff_eq_zero_of_mem_box {R : Type*} [CommRing R] (A B : ℕ)
    (p : MvPowerSeries (Fin 2) R)
    (hp : p ∈ Ideal.span {MvPowerSeries.X 0 ^ (A + 1)} ⊔ Ideal.span {MvPowerSeries.X 1 ^ (B + 1)}) :
    ∀ i ≤ A, ∀ j ≤ B, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) p = 0 := by
  classical
  simp only [Submodule.mem_sup, Ideal.mem_span_singleton, MvPowerSeries.X_pow_dvd_iff] at hp
  obtain ⟨y, hy, z, hz, rfl⟩ := hp
  intro i hi j hj
  rw [map_add, hy _ (by simpa using Nat.lt_succ_of_le hi),
    hz _ (by simpa using Nat.lt_succ_of_le hj), add_zero]

open AlgebraicGeometry CategoryTheory Limits IsLocalRing Faltings.BombieriVojta in
/-- Let `(z, w)` be a `K`-point of `C ×_K C` and `ς`, `ς'` uniformizers at `z`, `w`. If
`Q(ς + t₀, ς' + t₀')` lies in `J_{A,B}` in the completed local ring at `(z, w)`, then every divided
derivative `∂_{(i₁, i₂)} Q` with `i₁ ≤ A`, `i₂ ≤ B` vanishes at `(t₀, t₀')`. -/
public theorem eval_hasseDeriv_eq_zero_of_mem {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))]
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    (hp : p ≫ (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ↘ Spec (.of K)) = 𝟙 _)
    (hzC : (p ≫ pullback.fst _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _)
    (hzD : (p ≫ pullback.snd _ _) ≫ (C ↘ Spec (.of K)) = 𝟙 _)
    {ς : C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K))}
    {ς' : C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))}
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'})
    (t₀ t₀' : K) (Q : MvPolynomial (Fin 2) K) (A B : ℕ)
    (hQ : algebraMap _ (AdicCompletion (maximalIdeal _) _)
      (MvPolynomial.eval₂ (const (p (closedPoint K)))
        ![(pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς +
            const (p (closedPoint K)) t₀,
          (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς' +
            const (p (closedPoint K)) t₀'] Q) ∈
      Faltings.completedStalkBiorderIdeal (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
        (p (closedPoint K)) A B) :
    ∀ i₁ ≤ A, ∀ i₂ ≤ B, MvPolynomial.eval ![t₀, t₀']
      (Faltings.MvPolynomial.hasseDeriv (Finsupp.single (0 : Fin 2) i₁ + Finsupp.single 1 i₂) Q)
        = 0 := by
  obtain ⟨Ψ, hΨc, hΨ0, hΨ1⟩ := exists_ringHom_mvPowerSeries p hzC hzD hς hς'
  have hm := maximalIdeal_stalk_pullback_eq_span p hp hzC hzD hς hς'
  have hJ : Faltings.completedStalkBiorderIdeal (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
      (p (closedPoint K)) A B =
      (Ideal.span {(pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς ^ (A + 1)}).map
        (algebraMap _ (AdicCompletion (maximalIdeal _) _)) ⊔
      (Ideal.span
        {(pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς' ^ (B + 1)}).map
        (algebraMap _ (AdicCompletion (maximalIdeal _) _)) := by
    simp only [Faltings.completedStalkBiorderIdeal]
    rw [← Ideal.map_map, ← Ideal.map_map]
    erw [hς, hς']
    congr 2 <;>
    · erw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
      rfl
  rw [hJ] at hQ
  have hbox := map_mem_box_of_algebraMap_mem _ hm Ψ hΨ0 hΨ1 A B _ hQ
  have hev : Ψ (MvPolynomial.eval₂ (const (p (closedPoint K)))
        ![(pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς +
            const (p (closedPoint K)) t₀,
          (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς' +
            const (p (closedPoint K)) t₀'] Q) =
      ((MvPolynomial.aeval (fun μ => MvPolynomial.C (![t₀, t₀'] μ) + MvPolynomial.X μ) Q :
        MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) := by
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def]
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext a; simp [hΨc]
    · funext μ
      fin_cases μ
      · simp [hΨc]; erw [hΨ0]; rw [add_comm]
      · simp [hΨc]; erw [hΨ1]; rw [add_comm]
  rw [hev] at hbox
  intro i₁ hi₁ i₂ hi₂
  have := coeff_eq_zero_of_mem_box A B _ hbox i₁ hi₁ i₂ hi₂
  rw [_root_.MvPolynomial.coeff_coe, coeff_aeval_C_add_X] at this
  exact this

end Taylor

end Faltings.BombieriRoth.VanishingTransfer
