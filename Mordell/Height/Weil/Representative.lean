module

public import Mordell.Height.Weil.Basic
public import Mordell.Height.Weil.FieldIndependence
public import Mordell.Height.Weil.ProductFormula

/-!
# The Weil height computed from any representative

Let `x` be a point of `ℙⁿ(ℚ̄)`, let `y = (y_0, …, y_n)` be homogeneous coordinates of `x`, and
let `F` be a number field containing `y_0, …, y_n`. Then the height of `x` is the sum of the
local heights of `y` over the places of `F`:
`h(x) = S_F(y) = ∑_{v ∈ M_F} max_j log |y_j|_v`.

## Main results

* `Faltings.weilHeight_eq_sumLocalHeight`: `h(x) = S_F(y)` for every representative `y` of `x`
  with coordinates in a number field `F ⊆ K`.
* `Faltings.BombieriVojta.HeightLowerBound.sumLocalHeight_eq_logHeight`: for a nonzero `y : ι → F`,
  `S_F(y) = Height.logHeight y / [F : ℚ]`, Mathlib's logarithmic height normalised.

## Implementation notes

The ambient field is an arbitrary algebraic extension `K / ℚ` and the index type an arbitrary
finite linear order `ι`, as for `Faltings.weilHeight`; `K = AlgebraicClosure ℚ` and
`ι = Fin (n + 1)` give `ℙⁿ(ℚ̄)`. The number field `F` "containing the coordinates" is any
number field with a ring map `algebraMap F K`, and the representative is a vector `y : ι → F`
whose image `algebraMap F K ∘ y` represents `x`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Sec. 1.2.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- Ratios of homogeneous coordinates do not depend on the representative. -/
private lemma rep_div_rep {K ι : Type*} [Field K] {x : ℙ K (ι → K)} {v : ι → K} (hv : v ≠ 0)
    (hx : Projectivization.mk K v hv = x) (i j : ι) :
    x.rep i / x.rep j = v i / v j := by
  obtain ⟨a, rfl⟩ := (Projectivization.mk_eq_mk_iff' K _ _ hv x.rep_nonzero).1
    (hx.trans x.mk_rep.symm)
  have ha : a ≠ 0 := by rintro rfl; exact hv (zero_smul _ _)
  simp [mul_div_mul_left _ _ ha]

/-- A point represented by a vector with coordinates in `F` has its field of definition
inside `F`. -/
private lemma fieldOfDefinition_le_fieldRange {K : Type*} [Field K] [Algebra ℚ K] {ι : Type*}
    {F : Type*} [Field F] [Algebra F K] {x : ℙ K (ι → K)} {y : ι → F}
    (hy : algebraMap F K ∘ y ≠ 0) (hx : Projectivization.mk K (algebraMap F K ∘ y) hy = x) :
    (pointField ℚ x).toSubfield ≤ (algebraMap F K).fieldRange := by
  rw [pointField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
  rintro r (⟨q, rfl⟩ | ⟨i, j, -, rfl⟩)
  · exact ⟨(q : F), by simp⟩
  · exact ⟨y i / y j, by simp [rep_div_rep hy hx]⟩

/-- The sum of local heights of the normalized vector `x̃ = x_{j₀}⁻¹ • x`, for an arbitrary
number field structure on `ℚ(x)` and an arbitrary index `j₀` with `x_{j₀} ≠ 0`, is that of `y`:
viewed in `F`, `x̃` is `y_{j₀}⁻¹ • y`, and the sum of local heights is invariant under change
of number field and under rescaling. -/
private lemma sumLocalHeight_normalized_eq {K : Type*} [Field K] [Algebra ℚ K]
    {ι : Type*} [Fintype ι] {F : Type*} [Field F] [NumberField F] [Algebra F K]
    {x : ℙ K (ι → K)} {y : ι → F} (hy : algebraMap F K ∘ y ≠ 0)
    (hx : Projectivization.mk K (algebraMap F K ∘ y) hy = x)
    (_ : NumberField (pointField ℚ x)) (j₀ : ι) (hj₀ : x.rep j₀ ≠ 0)
    (hmem : ∀ i, x.rep i / x.rep j₀ ∈ pointField ℚ x) :
    sumLocalHeight (fun i => (⟨x.rep i / x.rep j₀, hmem i⟩ : pointField ℚ x)) =
      sumLocalHeight y := by
  set f := algebraMap F K
  let e := f.rangeRestrictFieldEquiv
  letI : Algebra (pointField ℚ x) F :=
    (e.symm.toRingHom.comp (Subfield.inclusion (fieldOfDefinition_le_fieldRange hy hx))).toAlgebra
  have hyj : y j₀ ≠ 0 := fun h => by simpa [h, div_self hj₀] using rep_div_rep hy hx j₀ j₀
  have hne : (fun i => (⟨x.rep i / x.rep j₀, hmem i⟩ : pointField ℚ x)) ≠ 0 :=
    fun h => by simpa [div_self hj₀] using congrArg (fun v => (v j₀ : K)) h
  have hvec : algebraMap (pointField ℚ x) F ∘
      (fun i => (⟨x.rep i / x.rep j₀, hmem i⟩ : pointField ℚ x)) = (y j₀)⁻¹ • y := by
    funext i
    apply f.injective
    refine (congrArg Subtype.val (e.apply_symm_apply (Subfield.inclusion _ ⟨_, hmem i⟩))).trans ?_
    simp [rep_div_rep hy hx, div_eq_inv_mul, f]
    rfl
  rw [← sumLocalHeight_algebraMap (L := F) hne, hvec,
    sumLocalHeight_smul (fun h => hy (by simp [h])) (inv_ne_zero hyj)]

/-- The height `Faltings.weilHeight x` of a point `x` of `ℙ K (ι → K)` may be computed from any
representative: if `y : ι → F` has coordinates in a number field `F ⊆ K` and
`algebraMap F K ∘ y` is a set of homogeneous coordinates of `x`, then
`h(x) = Faltings.sumLocalHeight y = ∑_{v ∈ M_F} max_j log |y_j|_v`. -/
@[faltings "lem_ht_weil_height_any_representative"]
theorem weilHeight_eq_sumLocalHeight {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι] [LinearOrder ι] {F : Type*} [Field F]
    [NumberField F] [Algebra F K] {x : ℙ K (ι → K)} {y : ι → F}
    (hy : algebraMap F K ∘ y ≠ 0) (hx : Projectivization.mk K (algebraMap F K ∘ y) hy = x) :
    weilHeight x = sumLocalHeight y := by
  unfold weilHeight
  classical
  dsimp only
  exact sumLocalHeight_normalized_eq hy hx _ _
    (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun j => x.rep j ≠ 0) _)).2 _

/-! ### Sums of local heights and Mathlib's logarithmic height -/

namespace BombieriVojta.HeightLowerBound

open _root_.NumberField Module Real

/-- The maximum of the absolute values of the entries of a nonzero tuple is positive. -/
private lemma iSup_abv_pos {K : Type*} [Field K] {ι : Type*} [Finite ι] (v : AbsoluteValue K ℝ)
    {x : ι → K} (hx : x ≠ 0) : 0 < ⨆ i, v (x i) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  exact (v.pos hi₀).trans_le (Finite.le_ciSup_of_le i₀ le_rfl)

section Global

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- For a nonzero tuple, `log max_i |x_i|_v` vanishes at all but finitely many finite places. -/
lemma hasFiniteSupport_log_iSup {x : ι → K} (hx : x ≠ 0) :
    Function.HasFiniteSupport fun v : FinitePlace K ↦ log (⨆ i, v (x i)) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  refine (Set.finite_iUnion fun i : {i // x i ≠ 0} ↦
    FinitePlace.hasFiniteMulSupport (K := K) i.2).subset fun v hv ↦ ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  have h1 : ⨆ i, v (x i) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le i₀ (h ⟨i₀, hi₀⟩).ge)
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h ⟨i, hi⟩).le
  exact hv (by simp [h1])

/-- The logarithmic Weil height of a nonzero tuple as a sum of local terms. -/
lemma logHeight_eq_sum_log_iSup {x : ι → K} (hx : x ≠ 0) :
    Height.logHeight x = (∑ v : InfinitePlace K, v.mult * log (⨆ i, v (x i))) +
      ∑ᶠ v : FinitePlace K, log (⨆ i, v (x i)) := by
  have hi (v : InfinitePlace K) : 0 < ⨆ i, v (x i) := iSup_abv_pos v.1 hx
  have hf (v : FinitePlace K) : 0 < ⨆ i, v (x i) := iSup_abv_pos v.1 hx
  rw [Height.logHeight_eq_log_mulHeight, NumberField.mulHeight_eq hx,
    log_mul (Finset.prod_pos fun v _ ↦ pow_pos (hi v) _).ne'
      (finprod_induction (0 < ·) one_pos (fun _ _ ↦ mul_pos) hf).ne',
    log_prod fun v _ ↦ (pow_pos (hi v) _).ne', log_finprod hf]
  simp [log_pow]

end Global

/-- `log max_j f_j^e = e log max_j f_j` for nonnegative `f` and `e > 0`. -/
lemma log_iSup_rpow {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hpos : 0 < ⨆ j, f j) {e : ℝ} (he : 0 < e) :
    Real.log (⨆ j, f j ^ e) = e * Real.log (⨆ j, f j) := by
  obtain ⟨j₀, hj₀⟩ := exists_eq_ciSup_of_finite (f := f)
  have hmax : ∀ j, f j ≤ f j₀ := fun j => hj₀ ▸ Finite.le_ciSup_of_le j le_rfl
  have h1 : (⨆ j, f j ^ e) = f j₀ ^ e :=
    le_antisymm (ciSup_le fun j => Real.rpow_le_rpow (hf j) (hmax j) he.le)
      (Finite.le_ciSup_of_le j₀ le_rfl)
  rw [h1, ← hj₀, Real.log_rpow (hj₀ ▸ hpos)]

/-- A finitely supported sum over a sum type with finite right summand. -/
lemma finsum_sum_of_fintype_right {α β M : Type*} [AddCommMonoid M] [Fintype β]
    (f : α ⊕ β → M) (hf : (Function.support fun a => f (.inl a)).Finite) :
    ∑ᶠ x, f x = (∑ᶠ a, f (.inl a)) + ∑ b, f (.inr b) := by
  classical
  let t := hf.toFinset
  have hsub : Function.support f ⊆ ((t.disjSum (Finset.univ : Finset β)) : Finset _) := by
    rintro (a | b) h
    · simpa [t] using h
    · simp
  rw [finsum_eq_sum_of_support_subset f hsub, Finset.sum_disjSum,
    finsum_eq_sum_of_support_subset (s := t) _ (by simp [t])]

/-- **Bombieri's sum of local heights is Mathlib's logarithmic height, normalised.** -/
lemma sumLocalHeight_eq_logHeight {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
    {a : ι → K} (ha : a ≠ 0) :
    sumLocalHeight a = Height.logHeight a / finrank ℚ K := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := Function.ne_iff.mp ha
  have : Nonempty ι := ⟨j₀⟩
  have hN : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have he : (0 : ℝ) < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr hN
  have hposF : ∀ w : FinitePlace K, 0 < ⨆ j, w (a j) := fun w =>
    (w.pos_iff.mpr hj₀).trans_le (Finite.le_ciSup_of_le j₀ le_rfl)
  have hposI : ∀ w : InfinitePlace K, 0 < ⨆ j, w (a j) := fun w =>
    (w.pos_iff.mpr hj₀).trans_le (Finite.le_ciSup_of_le j₀ le_rfl)
  have hF : ∀ w : FinitePlace K, NumberFieldPlace.localHeight (.inl w) a =
      (finrank ℚ K : ℝ)⁻¹ * Real.log (⨆ j, w (a j)) := fun w => by
    simp only [NumberFieldPlace.localHeight, NumberFieldPlace.vectorAbv,
      NumberFieldPlace.normalizedAbv_inl]
    exact log_iSup_rpow _ (fun j => (w.1).nonneg _) (hposF w) he
  have hI : ∀ w : InfinitePlace K, NumberFieldPlace.localHeight (.inr w) a =
      (finrank ℚ K : ℝ)⁻¹ * (w.mult * Real.log (⨆ j, w (a j))) := fun w => by
    simp only [NumberFieldPlace.localHeight, NumberFieldPlace.vectorAbv,
      NumberFieldPlace.normalizedAbv_inr]
    have hm : (0 : ℝ) < w.mult := by exact_mod_cast w.mult_pos
    rw [log_iSup_rpow _ (fun j => by positivity) _ he]
    · congr 1
      have := log_iSup_rpow (fun j => w (a j)) (fun j => (w.1).nonneg _) (hposI w) hm
      simpa [Real.rpow_natCast] using this
    · obtain ⟨j₁, hj₁⟩ := exists_eq_ciSup_of_finite (f := fun j => w (a j))
      exact (pow_pos (hposI w) _).trans_le (by
        rw [← hj₁]; exact Finite.le_ciSup_of_le j₁ le_rfl)
  unfold sumLocalHeight
  rw [finsum_sum_of_fintype_right _ ((hasFiniteSupport_log_iSup ha).subset fun w hw => by
      simp only [Function.mem_support, hF] at hw ⊢
      exact right_ne_zero_of_mul hw)]
  simp only [hF, hI]
  rw [← mul_finsum' _ _ (hasFiniteSupport_log_iSup ha), ← Finset.mul_sum,
    logHeight_eq_sum_log_iSup ha]
  field_simp
  ring

end BombieriVojta.HeightLowerBound

end Faltings
