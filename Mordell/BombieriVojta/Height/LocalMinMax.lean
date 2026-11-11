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
# The Vojta height as a sum of local min–max terms

`oldVojtaHeight`, a height `h_V` built from height functions on points, and its expression as a sum
over the places of a number field of `min_i max_{j,j'}` of logarithms of monomial quotients.
-/

open Faltings (chartVal_eq_of_comp chartVal_self iota_mem_iff mem_asHomogeneousIdeal_iff_eval_chartVal)
open Faltings.BombieriVojta (const_comp const_eq ev_const exists_stalk_hom ext_of_germ ne_zero_of_maximalIdeal_eq stalkClosedPointTo_comp_over_germ stalkCongr_const)

open Faltings (chartVal coordPoint exists_mem_basicOpen toDualEquiv_apply_apply top_le_preimage_of_mem)
open Faltings.BombieriVojta (const ev_eq_zero_of_mem stalkClosedPointTo_fromSpecStalk_eq stalkClosedPointTo_germ_of_eq)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing _root_.NumberField Module
open scoped LinearAlgebra.Projectivization

namespace Faltings.BombieriVojta.HeightLowerBound

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- The height `h_V(z, w) = δ₁ h_{NP}(z) + δ₂ h_{NP}(w) - d h_B(z, w)` with `δᵢ = (dᵢ + s d) / N`,
for height functions `hNP`, `hB` on points. -/
@[expose] public noncomputable def oldVojtaHeight {X : Type*} (s : ℤ) (N : ℕ) (hNP : X → ℝ)
    (hB : X × X → ℝ) (d₁ d₂ d : ℤ) (p : X × X) : ℝ :=
  ((d₁ + s * d : ℤ) : ℝ) / N * hNP p.1 + ((d₂ + s * d : ℤ) : ℝ) / N * hNP p.2 - d * hB p

section LocalExpression

open _root_.NumberField Module Real

section Local

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- `log max_i |x_i|_v` is the maximum of `log |x_j|_v` over the indices with `x_j ≠ 0`. -/
public lemma log_iSup_eq (v : AbsoluteValue K ℝ) {x : ι → K} (hx : x ≠ 0) :
    log (⨆ i, v (x i)) = ⨆ j : {j // x j ≠ 0}, log (v (x j)) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have : Nonempty {j // x j ≠ 0} := ⟨⟨i₀, hi₀⟩⟩
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i))
  have hpos : 0 < v (x j₀) := by
    rw [hj₀]
    exact (v.pos hi₀).trans_le (Finite.le_ciSup_of_le i₀ le_rfl)
  have hj₀' : x j₀ ≠ 0 := fun h ↦ by simp [h] at hpos
  rw [← hj₀]
  refine le_antisymm (Finite.le_ciSup_of_le ⟨j₀, hj₀'⟩ le_rfl) (ciSup_le fun j ↦ ?_)
  refine log_le_log (v.pos j.2) ?_
  rw [hj₀]
  exact Finite.le_ciSup_of_le j.1 le_rfl

/-- `max_{j,k} (p a_j + q b_k - c) = p max a + q max b - c` for `p, q ≥ 0`. -/
public lemma iSup_prod_add_sub {α β : Type*} [Finite α] [Finite β] [Nonempty α] [Nonempty β]
    (a : α → ℝ) (b : β → ℝ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (c : ℝ) :
    ⨆ jj : α × β, (p * a jj.1 + q * b jj.2 - c) = p * (⨆ j, a j) + q * (⨆ j, b j) - c := by
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := a)
  obtain ⟨k₀, hk₀⟩ := exists_eq_ciSup_of_finite (f := b)
  refine le_antisymm (ciSup_le fun jj ↦ ?_) (Finite.le_ciSup_of_le (j₀, k₀) (by rw [hj₀, hk₀]))
  have h1 : a jj.1 ≤ ⨆ j, a j := Finite.le_ciSup_of_le jj.1 le_rfl
  have h2 : b jj.2 ≤ ⨆ j, b j := Finite.le_ciSup_of_le jj.2 le_rfl
  gcongr

/-- `min_i (S - r c_i) = S - r max c` for `r ≥ 0`. -/
public lemma iInf_sub_mul {α : Type*} [Finite α] [Nonempty α] (c : α → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (S : ℝ) : ⨅ i, (S - r * c i) = S - r * ⨆ i, c i := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := c)
  refine le_antisymm (Finite.ciInf_le_of_le i₀ (by rw [hi₀])) (le_ciInf fun i ↦ ?_)
  have : c i ≤ ⨆ i, c i := Finite.le_ciSup_of_le i le_rfl
  gcongr

/-- The local identity at one place: the min-max of the logarithms of the monomial quotients
is `δ₁ log max |x|_v + δ₂ log max |x'|_v - d log max |y|_v`. -/
public lemma iInf_iSup_log_eq {κ : Type*} [Finite κ] (v : AbsoluteValue K ℝ) {x x' : ι → K}
    {y : κ → K} (hx : x ≠ 0) (hx' : x' ≠ 0) (hy : y ≠ 0) (δ₁ δ₂ : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
        log (v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ d)) =
      δ₁ * log (⨆ j, v (x j)) + δ₂ * log (⨆ j, v (x' j)) - d * log (⨆ i, v (y i)) := by
  have : Nonempty {j // x j ≠ 0} := let ⟨i, hi⟩ := Function.ne_iff.mp hx; ⟨⟨i, hi⟩⟩
  have : Nonempty {j // x' j ≠ 0} := let ⟨i, hi⟩ := Function.ne_iff.mp hx'; ⟨⟨i, hi⟩⟩
  have : Nonempty {i // y i ≠ 0} := let ⟨i, hi⟩ := Function.ne_iff.mp hy; ⟨⟨i, hi⟩⟩
  have key : ∀ (i : {i // y i ≠ 0}) (jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0}),
      log (v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ d)) =
        δ₁ * log (v (x jj.1)) + δ₂ * log (v (x' jj.2)) - d * log (v (y i)) := by
    intro i jj
    have h1 := v.pos jj.1.2
    have h2 := v.pos jj.2.2
    have h3 := v.pos i.2
    rw [map_div₀, map_mul, map_pow, map_pow, map_zpow₀, log_div (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_pow, log_pow, log_zpow]
  calc _ = ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
        ((δ₁ : ℝ) * log (v (x jj.1)) + δ₂ * log (v (x' jj.2)) - d * log (v (y i))) :=
        iInf_congr fun i ↦ iSup_congr fun jj ↦ key i jj
    _ = _ := ?_
  simp_rw [iSup_prod_add_sub (fun j : {j // x j ≠ 0} ↦ log (v (x j)))
    (fun j : {j // x' j ≠ 0} ↦ log (v (x' j))) (Nat.cast_nonneg δ₁) (Nat.cast_nonneg δ₂)]
  rw [iInf_sub_mul _ (by exact_mod_cast hd), log_iSup_eq v hx, log_iSup_eq v hx', log_iSup_eq v hy]

end Local

section Global

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- A linear combination `a h(x) + b h(x') - c h(y)` of logarithmic Weil heights of nonzero
tuples, as a sum over the places of the same combination of the local terms. -/
public lemma sum_places_eq_logHeight {κ : Type*} [Finite κ] {x x' : ι → K} {y : κ → K}
    (hx : x ≠ 0) (hx' : x' ≠ 0) (hy : y ≠ 0) (a b c : ℝ) :
    (∑ v : InfinitePlace K, v.mult * (a * log (⨆ j, v (x j)) + b * log (⨆ j, v (x' j)) -
        c * log (⨆ i, v (y i)))) +
      ∑ᶠ v : FinitePlace K, (a * log (⨆ j, v (x j)) + b * log (⨆ j, v (x' j)) -
        c * log (⨆ i, v (y i))) =
      a * Height.logHeight x + b * Height.logHeight x' - c * Height.logHeight y := by
  have h1 := hasFiniteSupport_log_iSup hx
  have h2 := hasFiniteSupport_log_iSup hx'
  have h3 := hasFiniteSupport_log_iSup hy
  rw [finsum_sub_distrib (by fun_prop) (by fun_prop),
    finsum_add_distrib (by fun_prop) (by fun_prop),
    ← mul_finsum' _ _ h1, ← mul_finsum' _ _ h2, ← mul_finsum' _ _ h3,
    logHeight_eq_sum_log_iSup hx, logHeight_eq_sum_log_iSup hx', logHeight_eq_sum_log_iSup hy]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    mul_left_comm]
  ring

end Global

/-- Reading `a = N δ` in `ℝ` as `a / N = δ`. -/
public lemma intCast_div_natCast_eq {a : ℤ} {N δ : ℕ} (hN : 0 < N) (h : a = N * δ) :
    (a : ℝ) / N = δ := by
  rw [h]
  push_cast
  field_simp

/-- **Local expression of `h_V`.** Let `φNP` and `φB` give nonzero representatives over a
number field `K` of points `z`, `w` and of the pair `(z, w)`, and let `h_{NP}`, `h_B` be their
absolute Weil heights. If `d ≥ 1` and `δ₁ = (d₁ + s d) / N`, `δ₂ = (d₂ + s d) / N` are positive
integers, then `Faltings.vojtaHeight` at `(z, w)` is the sum over the places `v` of `K` of
`min_{i, y_i ≠ 0} max_{j, j'} log |x_j ^ δ₁ x'_{j'} ^ δ₂ / y_i ^ d|_v`, where `x = φNP z`,
`x' = φNP w`, `y = φB (z, w)`, `j, j'` run over the indices with `x_j ≠ 0`, `x'_{j'} ≠ 0`, and
`|·|_v` is the normalised absolute value at `v`. -/
public theorem vojtaHeight_eq_sum_iInf_iSup_log (K : Type*) [Field K] [NumberField K]
    {X ι κ : Type*} [Finite ι] [Finite κ] (φNP : X → ι → K) (φB : X × X → κ → K)
    (s : ℤ) (hs : 1 ≤ s) (N : ℕ) (hN : 0 < N) (d₁ d₂ d : ℤ) (hd : 1 ≤ d) (δ₁ δ₂ : ℕ)
    (hδ₁ : d₁ + s * d = N * δ₁) (hδ₂ : d₂ + s * d = N * δ₂) (hδ₁pos : 0 < δ₁) (hδ₂pos : 0 < δ₂)
    (z w : X) (hx : φNP z ≠ 0) (hx' : φNP w ≠ 0) (hy : φB (z, w) ≠ 0) :
    oldVojtaHeight s N (fun p => Height.logHeight (φNP p) / finrank ℚ K)
        (fun p => Height.logHeight (φB p) / finrank ℚ K) d₁ d₂ d (z, w) =
      ((∑ v : InfinitePlace K, v.mult *
          ⨅ i : {i // φB (z, w) i ≠ 0},
            ⨆ jj : {j // φNP z j ≠ 0} × {j' // φNP w j' ≠ 0},
              log (v (φNP z jj.1 ^ δ₁ * φNP w jj.2 ^ δ₂ / φB (z, w) i ^ d))) +
        ∑ᶠ v : FinitePlace K,
          ⨅ i : {i // φB (z, w) i ≠ 0},
            ⨆ jj : {j // φNP z j ≠ 0} × {j' // φNP w j' ≠ 0},
              log (v (φNP z jj.1 ^ δ₁ * φNP w jj.2 ^ δ₂ / φB (z, w) i ^ d))) /
        finrank ℚ K := by
  have hloc (v : AbsoluteValue K ℝ) := iInf_iSup_log_eq v hx hx' hy δ₁ δ₂ (by omega : 0 ≤ d)
  simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply, hloc]
  simp only [← InfinitePlace.coe_apply, ← FinitePlace.coe_apply]
  rw [sum_places_eq_logHeight hx hx' hy]
  simp only [oldVojtaHeight, intCast_div_natCast_eq hN hδ₁, intCast_div_natCast_eq hN hδ₂]
  ring

end LocalExpression

end Faltings.BombieriVojta.HeightLowerBound
