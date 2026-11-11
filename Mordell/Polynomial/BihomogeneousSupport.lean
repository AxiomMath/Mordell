module

public import Mordell.BombieriVojta.Height.Basic
public import Mordell.BombieriVojta.Taylor.MonomialBound
public import Mordell.BombieriVojta.Taylor.SeparatedVariables
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Weil.Representative
public import Mordell.BombieriVojta.TripleFunction.FirstCoefficient
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.Height.Machine.IsomorphicPullbacks

/-!
# Monomials of a bihomogeneous form

The exponents of a form of bidegree `(δ₁, δ₂)` have degrees `δ₁` and `δ₂`, so such a form in
`2 (n + 1)` variables has at most `((δ₁ + 1)(δ₂ + 1))ⁿ` monomials.
-/

open Faltings (chartVal_eq_of_comp chartVal_self iota_mem_iff mem_asHomogeneousIdeal_iff_eval_chartVal)
open Faltings.BombieriVojta (const_comp const_eq ev_const exists_stalk_hom ext_of_germ ne_zero_of_maximalIdeal_eq stalkClosedPointTo_comp_over_germ stalkCongr_const)

open Faltings (chartVal coordPoint exists_mem_basicOpen toDualEquiv_apply_apply top_le_preimage_of_mem)
open Faltings.BombieriVojta (const ev_eq_zero_of_mem stalkClosedPointTo_fromSpecStalk_eq stalkClosedPointTo_germ_of_eq)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing _root_.NumberField Module
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings.BombieriVojta.HeightLowerBound

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

section Monomials

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The exponents of a bihomogeneous form of bidegree `(δ₁, δ₂)` have degrees `δ₁` and `δ₂`. -/
public lemma sum_exponents_eq {P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) R} {δ₁ δ₂ : ℕ}
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂))
    {e : Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ} (he : e ∈ P.support) :
    ∑ ν, e (Sum.inl ν) = δ₁ ∧ ∑ ν, e (Sum.inr ν) = δ₂ := by
  have h := hP (MvPolynomial.mem_support_iff.mp he)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Sum.elim_inl,
    Sum.elim_inr, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

/-- A bihomogeneous form of bidegree `(δ₁, δ₂)` in `n + 1` and `n + 1` variables has at most
`((δ₁ + 1) (δ₂ + 1))ⁿ` monomials. -/
public lemma card_support_le {P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) R} {δ₁ δ₂ : ℕ}
    (hP : P.IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂)) :
    P.support.card ≤ ((δ₁ + 1) * (δ₂ + 1)) ^ n := by
  classical
  let φ : (Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ) → (Fin n → ℕ) × (Fin n → ℕ) := fun e =>
    (fun ν => e (Sum.inl ν.castSucc), fun ν => e (Sum.inr ν.castSucc))
  have hmaps : ∀ e ∈ P.support, φ e ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (δ₁ + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin n => Finset.range (δ₂ + 1)) := by
    intro e he
    obtain ⟨h1, h2⟩ := sum_exponents_eq hP he
    simp only [φ, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    refine ⟨fun ν => ?_, fun ν => ?_⟩
    · rw [← h1]
      exact Finset.single_le_sum (f := fun ν => e (Sum.inl ν)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
    · rw [← h2]
      exact Finset.single_le_sum (f := fun ν => e (Sum.inr ν)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
  have hinj : Set.InjOn φ P.support := by
    intro e he e' he' h
    obtain ⟨h1, h2⟩ := sum_exponents_eq hP he
    obtain ⟨h1', h2'⟩ := sum_exponents_eq hP he'
    simp only [φ, Prod.mk.injEq] at h
    have hl : ∀ ν : Fin n, e (Sum.inl ν.castSucc) = e' (Sum.inl ν.castSucc) := congrFun h.1
    have hr : ∀ ν : Fin n, e (Sum.inr ν.castSucc) = e' (Sum.inr ν.castSucc) := congrFun h.2
    rw [Fin.sum_univ_castSucc] at h1 h1' h2 h2'
    simp only [hl, hr] at h1 h2
    ext σ
    rcases σ with ν | ν <;> induction ν using Fin.lastCases with
    | last => omega
    | cast i => simp [hl, hr]
  calc P.support.card ≤ ((Fintype.piFinset fun _ : Fin n => Finset.range (δ₁ + 1)) ×ˢ
        (Fintype.piFinset fun _ : Fin n => Finset.range (δ₂ + 1))).card :=
        Finset.card_le_card_of_injOn φ hmaps hinj
    _ = ((δ₁ + 1) * (δ₂ + 1)) ^ n := by simp [Finset.card_product, mul_pow]

end Monomials

end Faltings.BombieriVojta.HeightLowerBound
