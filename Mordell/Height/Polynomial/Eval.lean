module

public import Mordell.Height.Polynomial.Basic
public import Mordell.Height.Polynomial.Local.Eval
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Weil.LinearMapLower

/-!
# The height of the value of a family of homogeneous polynomials

Let `F_0, …, F_M` be homogeneous polynomials of degree `e` in `x_0, …, x_n` over an algebraic
extension `K` of `ℚ`, not all zero, each with at most `N` monomials. If `x ∈ ℙⁿ(K)` is a point at
which not all `F_i` vanish, then the point `F(x) = (F_0(x) : ⋯ : F_M(x))` satisfies
`h(F(x)) ≤ e h(x) + h(F_0, …, F_M) + log N`.

## Main results

* `Faltings.weilHeight_eval_le`: the bound `h(F(x)) ≤ e h(x) + h(F) + log N`.

## Implementation notes

The source takes `K = ℚ̄`, variables `x_0, …, x_n` and the index set `{0, …, M}`; here `K / ℚ` is
any algebraic extension and the variables and the family are indexed by arbitrary finite
linearly ordered types `ι` and `ι'`. The value `F(x)` is computed on the representative
`x.rep`; since the `F_i` are homogeneous of the same degree, the resulting projective point does
not depend on the representative.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

section NumberField

variable {L : Type*} [Field L] [NumberField L]

omit [NumberField L] in
private lemma algebraMap_comp_ne_zero {K : Type*} [Field K] [Algebra L K] {κ : Type*}
    {c : κ → L} (hc : c ≠ 0) : algebraMap L K ∘ c ≠ 0 := fun h =>
  hc (funext fun p => (algebraMap L K).injective (by simpa using congrFun h p))

/-- The local size of a polynomial is bounded by that of any vector listing its coefficients. -/
private lemma mvPolynomialAbv_le_vectorAbv {ι : Type*} (w : NumberFieldPlace L)
    (G : MvPolynomial ι L) {κ : Type*} [Finite κ] (c : κ → L)
    (hc : ∀ I ∈ G.support, ∃ k, c k = G.coeff I) (hc0 : c ≠ 0) :
    w.mvPolynomialAbv (fun _ : Unit => G) ≤ w.vectorAbv c := by
  rw [NumberFieldPlace.mvPolynomialAbv, ciSup_unique]
  refine ciSup_le fun I => ?_
  by_cases hI : I ∈ G.support
  · obtain ⟨k, hk⟩ := hc I hI
    exact hk ▸ w.normalizedAbv_le_vectorAbv c k
  · rw [MvPolynomial.notMem_support_iff.1 hI]
    obtain ⟨a, ha⟩ := w.exists_absoluteValue_coe_eq_normalizedAbv
    rw [← ha, map_zero]
    exact (w.vectorAbv_pos hc0).le

/-- The local bound at one place, in logarithmic form:
`h_w(F(y)) ≤ ε_w log |N|_w + h_w(coefficients) + e h_w(y)`. -/
private lemma localHeight_eval_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e N : ℕ}
    (hN1 : 1 ≤ N) (G : ι' → MvPolynomial ι L) (hG : ∀ i, (G i).IsHomogeneous e)
    (hN : ∀ i, (G i).support.card ≤ N) {κ : Type*} [Finite κ] (c : κ → L)
    (hc : ∀ i I, I ∈ (G i).support → ∃ k, c k = (G i).coeff I) (hc0 : c ≠ 0)
    (y : ι → L) (hy : y ≠ 0) (hv : (fun i => (G i).eval y) ≠ 0) (w : NumberFieldPlace L) :
    w.localHeight (fun i => (G i).eval y) ≤
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (N : L)) +
        w.localHeight c + e * w.localHeight y := by
  have hNpos : 0 < w.normalizedAbv (N : L) :=
    w.normalizedAbv_pos (Nat.cast_ne_zero.2 (by omega))
  have hcpos := w.vectorAbv_pos hc0
  have hypos := w.vectorAbv_pos hy
  have hbound : w.vectorAbv (fun i => (G i).eval y) ≤
      w.normalizedAbv (N : L) ^ w.archimedeanIndicator * w.vectorAbv c * w.vectorAbv y ^ e := by
    obtain ⟨i₀, -⟩ := Function.ne_iff.mp hv
    have : Nonempty ι' := ⟨i₀⟩
    refine ciSup_le fun i => ?_
    refine (NumberFieldPlace.normalizedAbv_eval_le_of_isHomogeneous w hN1 (hG i) (hN i) y).trans ?_
    gcongr
    exact mvPolynomialAbv_le_vectorAbv w (G i) c (hc i) hc0
  unfold NumberFieldPlace.localHeight
  rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul (by positivity) hcpos.ne',
    ← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (w.vectorAbv_pos hv) hbound

/-- The theorem over a number field: summing `localHeight_eval_le` over all places, the
archimedean terms `ε_w log |N|_w` add up to `log N`. -/
private lemma sumLocalHeight_eval_le {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e N : ℕ}
    (hN1 : 1 ≤ N) (G : ι' → MvPolynomial ι L) (hG : ∀ i, (G i).IsHomogeneous e)
    (hN : ∀ i, (G i).support.card ≤ N) {κ : Type*} [Finite κ] (c : κ → L)
    (hc : ∀ i I, I ∈ (G i).support → ∃ k, c k = (G i).coeff I) (hc0 : c ≠ 0)
    (y : ι → L) (hy : y ≠ 0) (hv : (fun i => (G i).eval y) ≠ 0) :
    sumLocalHeight (fun i => (G i).eval y) ≤
      e * sumLocalHeight y + sumLocalHeight c + Real.log N := by
  have hlog := NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := L)
    (r := (N : ℤ)) (by exact_mod_cast hN1)
  simp only [Int.cast_natCast] at hlog
  have hfey : (Function.support fun w : NumberFieldPlace L => (e : ℝ) * w.localHeight y).Finite :=
    (NumberFieldPlace.finite_support_localHeight hy).subset (Function.support_mul_subset_right _ _)
  have hfc := NumberFieldPlace.finite_support_localHeight hc0
  have hfN : (Function.support fun w : NumberFieldPlace L =>
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (N : L))).Finite := by
    refine (Set.finite_range Sum.inr).subset ?_
    rintro (w | w) hw
    · simp at hw
    · exact ⟨w, rfl⟩
  have hfyc := (hfey.union hfc).subset (Function.support_add _ _)
  unfold sumLocalHeight
  rw [← hlog, mul_finsum, ← finsum_add_distrib hfey hfc, ← finsum_add_distrib hfyc hfN]
  refine finsum_le_finsum' (NumberFieldPlace.finite_support_localHeight hv)
    ((hfyc.union hfN).subset (Function.support_add _ _)) fun w => ?_
  exact (localHeight_eval_le hN1 G hG hN c hc hc0 y hy hv w).trans_eq (by ring)

end NumberField

/-- For homogeneous polynomials `F_i`, `i ∈ ι'`, of degree `e` over an algebraic extension `K` of
`ℚ`, not all zero and each with at most `N` monomials, and a point `x` of projective space at
which not all `F_i` vanish, the Weil height of `F(x) = (F_i(x))_i` is at most
`e h(x) + h(F) + log N`, where `h(F)` is `Faltings.polynomialFamilyHeight`. -/
@[faltings "lem_ht_height_of_value"]
public theorem weilHeight_eval_le {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {ι ι' : Type*} [Fintype ι] [LinearOrder ι] [Fintype ι'] [LinearOrder ι']
    {e N : ℕ} (F : ι' → MvPolynomial ι K) (hF : ∀ i, (F i).IsHomogeneous e)
    (hF0 : ∃ i, F i ≠ 0) (hN : ∀ i, (F i).support.card ≤ N)
    (x : ℙ K (ι → K)) (hx : (fun i => (F i).eval x.rep) ≠ 0) :
    weilHeight (Projectivization.mk K (fun i => (F i).eval x.rep) hx) ≤
      e * weilHeight x + polynomialFamilyHeight F hF0 + Real.log N := by
  classical
  let S : Set K := Set.range x.rep ∪ ⋃ i, ((F i).coeffs : Set K)
  have hSfin : S.Finite :=
    (Set.finite_range _).union (Set.finite_iUnion fun i => Finset.finite_toSet _)
  let L := IntermediateField.adjoin ℚ S
  have hfin : FiniteDimensional ℚ L := by
    have := hSfin.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  let : NumberField L :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  let y : ι → L := fun j => ⟨x.rep j, IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩)⟩
  have hy : algebraMap L K ∘ y = x.rep := rfl
  have hy0 : y ≠ 0 := fun h => x.rep_nonzero (by rw [← hy, h]; ext; simp)
  have hlift : ∀ i, ∃ G : MvPolynomial ι L, MvPolynomial.map (algebraMap L K) G = F i :=
    fun i => MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun c hc =>
      ⟨⟨c, IntermediateField.subset_adjoin ℚ _ (Or.inr (Set.mem_iUnion.2 ⟨i, hc⟩))⟩, rfl⟩
  choose G hG using hlift
  have hcoeff : ∀ i I, algebraMap L K ((G i).coeff I) = (F i).coeff I := fun i I => by
    rw [← hG, MvPolynomial.coeff_map]
  have hsupp : ∀ i, (G i).support = (F i).support := fun i => by
    rw [← hG, MvPolynomial.support_map_of_injective _ (algebraMap L K).injective]
  have hGhom : ∀ i, (G i).IsHomogeneous e := fun i I hI =>
    hF i (by rwa [← hcoeff, map_ne_zero])
  have hN1 : 1 ≤ N := by
    obtain ⟨i, hi⟩ := hF0
    exact (Finset.card_pos.2 (MvPolynomial.support_nonempty.2 hi)).trans_le (hN i)
  -- the value `F(y)` over `L`
  let v : ι' → L := fun i => (G i).eval y
  have hv : algebraMap L K ∘ v = fun i => (F i).eval x.rep := by
    funext i; simp only [Function.comp_apply, v, MvPolynomial.map_eval, hG, hy]
  have hv0 : v ≠ 0 := fun h => hx (by rw [← hv, h]; ext; simp)
  -- the coefficient vector over `L`
  let c : (Σ i, (F i).support) → L := fun p => (G p.1).coeff p.2.1
  have hc : algebraMap L K ∘ c = fun p : Σ i, (F i).support => (F p.1).coeff p.2.1 :=
    funext fun _ => hcoeff _ _
  have hc0 : c ≠ 0 := by
    obtain ⟨i, hi⟩ := hF0
    obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hi
    refine Function.ne_iff.mpr ⟨⟨i, I, MvPolynomial.mem_support_iff.mpr hI⟩, fun h => hI ?_⟩
    rw [← hcoeff]
    exact (congrArg (algebraMap L K) h).trans (map_zero _)
  have hPF : polynomialFamilyHeight F hF0 = sumLocalHeight c := by
    let : LinearOrder (Σ i, (F i).support) := IsWellOrder.linearOrder WellOrderingRel
    exact weilHeight_eq_sumLocalHeight (algebraMap_comp_ne_zero hc0) (mk_congr hc _ _)
  rw [weilHeight_eq_sumLocalHeight (y := v) (algebraMap_comp_ne_zero hv0) (mk_congr hv _ _),
    weilHeight_eq_sumLocalHeight (y := y) (algebraMap_comp_ne_zero hy0)
      ((mk_congr hy _ _).trans x.mk_rep), hPF]
  exact sumLocalHeight_eval_le hN1 G hGhom (fun i => hsupp i ▸ hN i) c
    (fun i I hI => ⟨⟨i, I, hsupp i ▸ hI⟩, rfl⟩) hc0 y hy0 hv0

end Faltings
