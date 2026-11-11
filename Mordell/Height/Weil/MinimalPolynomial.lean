module

public import Mordell.Height.Weil.AffineLocal
public import Mordell.Height.Weil.Galois
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue
public import Mordell.NumberField.NormalizedAbv.Integer

/-!
# The height of the coefficient point of a minimal polynomial

Let `α` be algebraic over `ℚ` of degree `d`, with minimal polynomial
`∏ᵢ (T - αᵢ) = ∑_{r=0}^d (-1)^r s_r T^{d-r}`, `s_0 = 1`, `s_r ∈ ℚ`. The height of the coefficient
point `(1 : s_1 : … : s_d) ∈ ℙ^d(ℚ)` is bounded in terms of the height of `α`:
`h(1 : s_1 : … : s_d) ≤ d h(α) + d log 2`.

## Main results

* `Faltings.affineWeilHeight_minpoly_coeff_le`: the bound
  `h(1 : s_1 : … : s_d) ≤ d h(α) + d log 2`.

## Implementation notes

`α` lies in an arbitrary algebraic extension `K / ℚ` (`K = AlgebraicClosure ℚ` is the source's
`ℚ̄`). The degree `d = [ℚ(α) : ℚ]` is written `(minpoly ℚ α).natDegree`, and
`s_r = (-1)^r · (minpoly ℚ α).coeff (d - r)`. The coefficient point has rational coordinates and
is taken in `ℙ^d(ℚ)`, as `Faltings.affineWeilHeight` over the field `ℚ`; the height is absolute,
so this is the height of the same point in `ℙ^d(K)`. The height of `α` is
`Faltings.affineWeilHeight ![α] = h(1 : α)`.

The proof works over a splitting field `L` of `minpoly ℚ α`, a number field, where the `s_r` are
the elementary symmetric functions of the conjugates `α₁, …, α_d`. At each place `w` of `L` the
local triangle inequality bounds `|s_r|_w` by `|2^d|_w^{ε_w} ∏ᵢ max(1, |αᵢ|_w)`; summing over the
places gives the bound, since every conjugate has the height of `α`.

## References

* [Z. Gao, *Heights*][gao2022], proof of Thm. 1.2.5.
* [E. Bombieri, W. Gubler, *Heights in Diophantine geometry*][bombieri2006], 1.6.7.
-/

@[expose] public section

open NumberField Polynomial Finset IntermediateField

namespace Faltings

/-- The height of an affine point is invariant under `ℚ`-embeddings. -/
private theorem affineWeilHeight_comp_algHom {K L : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (τ : K →ₐ[ℚ] L) {n : ℕ} (ξ : Fin n → K) :
    affineWeilHeight (τ ∘ ξ) = affineWeilHeight ξ := by
  unfold affineWeilHeight
  rw [← weilHeight_mk_map τ]
  congr 2
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

section Places

variable {L : Type*} [Field L] [NumberField L]

/-- At every place, `|binom n r|_w ^ ε_w ≤ |2^n|_w ^ ε_w` for `r ≤ n`. -/
private theorem normalizedAbv_choose_pow_le (w : NumberFieldPlace L) {n r : ℕ} (hr : r ≤ n) :
    w.normalizedAbv ((n.choose r : ℕ) : L) ^ w.archimedeanIndicator ≤
      w.normalizedAbv ((2 ^ n : ℕ) : L) ^ w.archimedeanIndicator := by
  rcases w with w | w
  · simp
  · rw [NumberFieldPlace.archimedeanIndicator_inr, pow_one, pow_one]
    have h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace L)
        (.inr (w.comap (algebraMap ℚ L)) : NumberFieldPlace ℚ) := ⟨rfl⟩
    rw [(NumberFieldPlace.normalizedAbv_natCast_inr w _ h (Nat.choose_pos hr)).1,
      (NumberFieldPlace.normalizedAbv_natCast_inr w _ h Nat.one_le_two_pow).1]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.choose_le_two_pow n r)
      (by positivity)

/-- `1 ≤ |2^n|_w ^ ε_w`. -/
private theorem one_le_normalizedAbv_two_pow (w : NumberFieldPlace L) (n : ℕ) :
    1 ≤ w.normalizedAbv ((2 ^ n : ℕ) : L) ^ w.archimedeanIndicator := by
  rcases w with w | w
  · simp
  · rw [NumberFieldPlace.archimedeanIndicator_inr, pow_one]
    have h : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace L)
        (.inr (w.comap (algebraMap ℚ L)) : NumberFieldPlace ℚ) := ⟨rfl⟩
    exact (NumberFieldPlace.normalizedAbv_natCast_inr w _ h Nat.one_le_two_pow).2

/-- The local bound for an elementary symmetric function:
`|e_r(β)|_w ≤ |2^n|_w^{ε_w} ∏ᵢ max(1, |βᵢ|_w)` for `r ≤ n`. -/
private theorem normalizedAbv_esymm_le (w : NumberFieldPlace L) {n : ℕ} (β : Fin n → L) {r : ℕ}
    (hrn : r ≤ n) :
    w.normalizedAbv (∑ t ∈ powersetCard r (univ : Finset (Fin n)), t.prod β) ≤
      w.normalizedAbv ((2 ^ n : ℕ) : L) ^ w.archimedeanIndicator *
        ∏ i, max 1 (w.normalizedAbv (β i)) := by
  have hne : (powersetCard r (univ : Finset (Fin n))).Nonempty :=
    powersetCard_nonempty.2 (by simpa using hrn)
  refine (NumberFieldPlace.normalizedAbv_sum_le w hne _).trans ?_
  rw [card_powersetCard, card_univ, Fintype.card_fin]
  refine mul_le_mul (normalizedAbv_choose_pow_le w hrn) ?_
    (le_sup'_of_le _ hne.choose_spec (NumberFieldPlace.normalizedAbv_nonneg _ _))
    (pow_nonneg (NumberFieldPlace.normalizedAbv_nonneg _ _) _)
  refine sup'_le _ _ fun t _ => ?_
  rw [NumberFieldPlace.normalizedAbv_prod]
  calc ∏ i ∈ t, w.normalizedAbv (β i) ≤ ∏ i ∈ t, max 1 (w.normalizedAbv (β i)) :=
        prod_le_prod₀ (fun i _ => NumberFieldPlace.normalizedAbv_nonneg _ _) fun i _ =>
          le_max_right _ _
    _ ≤ ∏ i, max 1 (w.normalizedAbv (β i)) :=
        prod_le_prod_of_subset_of_one_le₀ (subset_univ t)
          (fun i _ => zero_le_one.trans (le_max_left _ _)) fun i _ _ => le_max_left _ _

/-- `w ↦ log⁺ |b|_w` has finite support. -/
private theorem hasFiniteSupport_posLog_normalizedAbv (b : L) :
    Function.HasFiniteSupport fun w : NumberFieldPlace L => Real.posLog (w.normalizedAbv b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [Function.HasFiniteSupport]
  refine (NumberFieldPlace.finite_support_localHeight (x := fun _ : Unit => b)
    (by simpa [funext_iff])).subset fun w hw => ?_
  have h1 : 1 < w.normalizedAbv b := by
    by_contra h
    exact hw ((Real.posLog_eq_zero_iff _).2
      (by rw [abs_of_nonneg (NumberFieldPlace.normalizedAbv_nonneg _ _)]; exact not_lt.1 h))
  simp only [Function.mem_support, NumberFieldPlace.localHeight, NumberFieldPlace.vectorAbv,
    ciSup_const]
  exact (Real.log_pos h1).ne'

/-- `w ↦ ε_w log |x|_w` has finite support (it vanishes at finite places). -/
private theorem hasFiniteSupport_archimedeanIndicator_mul (x : L) :
    Function.HasFiniteSupport fun w : NumberFieldPlace L =>
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv x) := by
  refine (Set.finite_range (Sum.inr : InfinitePlace L → NumberFieldPlace L)).subset fun w hw => ?_
  rcases w with w | w
  · simp at hw
  · exact ⟨w, rfl⟩

/-- The local inequality: for `ξ_r = e_{r+1}(β)`,
`log⁺ |ξ|_w ≤ ε_w log |2^n|_w + ∑ᵢ log⁺ |βᵢ|_w`. -/
private theorem posLog_vectorAbv_esymm_le (w : NumberFieldPlace L) {n : ℕ} (β : Fin n → L) :
    Real.posLog (w.vectorAbv fun r : Fin n =>
        ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin n)), t.prod β) ≤
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv ((2 ^ n : ℤ) : L)) +
        ∑ i, Real.posLog (w.normalizedAbv (β i)) := by
  set A := w.normalizedAbv ((2 ^ n : ℕ) : L) ^ w.archimedeanIndicator
  set P := ∏ i, max 1 (w.normalizedAbv (β i))
  have hA : 1 ≤ A := one_le_normalizedAbv_two_pow w n
  have hP : 1 ≤ P := Finset.one_le_prod₀ fun i _ => le_max_left _ _
  have hv : w.vectorAbv (fun r : Fin n =>
      ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin n)), t.prod β) ≤ A * P :=
    Real.iSup_le (fun r => normalizedAbv_esymm_le w β r.2) (by positivity)
  have hAlog : Real.posLog A =
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv ((2 ^ n : ℤ) : L)) := by
    rw [Real.posLog_eq_log_max_one (zero_le_one.trans hA), max_eq_right hA, Real.log_pow]
    push_cast
    rfl
  have hPlog : Real.posLog P ≤ ∑ i, Real.posLog (w.normalizedAbv (β i)) := by
    refine (Real.posLog_prod _ _).trans (sum_le_sum fun i _ => ?_)
    have h0 := NumberFieldPlace.normalizedAbv_nonneg w (β i)
    rw [Real.posLog_eq_log_max_one (zero_le_one.trans (le_max_left _ _)),
      Real.posLog_eq_log_max_one h0, max_eq_right (le_max_left _ _)]
  have hv0 : 0 ≤ w.vectorAbv (fun r : Fin n =>
      ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin n)), t.prod β) :=
    Real.iSup_nonneg fun _ => NumberFieldPlace.normalizedAbv_nonneg _ _
  calc _ ≤ Real.posLog (A * P) := Real.posLog_le_posLog (by linarith) hv
    _ ≤ Real.posLog A + Real.posLog P := Real.posLog_mul
    _ ≤ _ := by rw [hAlog]; linarith

/-- The global inequality over a number field `L`: for `ξ_r = e_{r+1}(β)`,
`∑_w log⁺ |ξ|_w ≤ n log 2 + ∑ᵢ ∑_w log⁺ |βᵢ|_w`. -/
private theorem finsum_posLog_vectorAbv_esymm_le {n : ℕ} (β : Fin n → L) :
    ∑ᶠ w : NumberFieldPlace L, Real.posLog (w.vectorAbv fun r : Fin n =>
        ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin n)), t.prod β) ≤
      n * Real.log 2 + ∑ i, ∑ᶠ w : NumberFieldPlace L, Real.posLog (w.normalizedAbv (β i)) := by
  set g : NumberFieldPlace L → ℝ := fun w =>
    (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv ((2 ^ n : ℤ) : L)) +
      ∑ i, Real.posLog (w.normalizedAbv (β i))
  have hsum : Function.HasFiniteSupport fun w : NumberFieldPlace L =>
      ∑ i, Real.posLog (w.normalizedAbv (β i)) :=
    ((Set.finite_univ (α := Fin n)).biUnion fun i _ =>
      hasFiniteSupport_posLog_normalizedAbv (β i)).subset
      ((Finset.support_sum _ _).trans (by simp))
  have hg : Function.HasFiniteSupport g :=
    ((hasFiniteSupport_archimedeanIndicator_mul _).union hsum).subset
      (Function.support_add _ _)
  have hf : Function.HasFiniteSupport fun w : NumberFieldPlace L => Real.posLog (w.vectorAbv
      fun r : Fin n => ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin n)), t.prod β) :=
    hg.subset fun w hw h =>
      hw (le_antisymm (h ▸ posLog_vectorAbv_esymm_le w β) Real.posLog_nonneg)
  refine (finsum_le_finsum' hf hg fun w => posLog_vectorAbv_esymm_le w β).trans_eq ?_
  rw [finsum_add_distrib (hasFiniteSupport_archimedeanIndicator_mul _) hsum,
    NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast
      (one_le_pow₀ (by norm_num)),
    finsum_sum_comm _ _ fun i _ => hasFiniteSupport_posLog_normalizedAbv (β i)]
  push_cast
  rw [Real.log_pow]

/-- The height of a single algebraic number as a sum of local terms. -/
private theorem affineWeilHeight_singleton (b : L) :
    affineWeilHeight ![b] = ∑ᶠ w : NumberFieldPlace L, Real.posLog (w.normalizedAbv b) := by
  change affineWeilHeight (algebraMap L L ∘ ![b]) = _
  rw [affineWeilHeight_eq_finsum_posLog]
  refine finsum_congr fun w => ?_
  simp [NumberFieldPlace.vectorAbv]

end Places

/-- A conjugate of `α`, i.e. a root of its minimal polynomial, has the height of `α`. -/
private theorem affineWeilHeight_conj {K L : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] [Field L] [NumberField L] {α : K} {β : L}
    (hβ : β ∈ (minpoly ℚ α).aroots L) : affineWeilHeight ![β] = affineWeilHeight ![α] := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  -- the `IntermediateField` `ℚ`-algebra on `ℚ⟮α⟯` is not defeq to `DivisionRing.toRatAlgebra`,
  -- which instance search finds; re-bundle both embeddings over the latter
  set σ : ℚ⟮α⟯ →ₐ[ℚ] L :=
    ((algHomAdjoinIntegralEquiv ℚ hint).symm ⟨β, hβ⟩ : ℚ⟮α⟯ →+* L).toRatAlgHom
  set ι : ℚ⟮α⟯ →ₐ[ℚ] K := ((val ℚ⟮α⟯ : ℚ⟮α⟯ →+* K)).toRatAlgHom
  have : Algebra.IsAlgebraic ℚ ℚ⟮α⟯ :=
    ⟨fun _ => (isAlgebraic_algHom_iff ι Subtype.val_injective).1
      (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h1 : (σ ∘ ![AdjoinSimple.gen ℚ α]) = algebraMap L L ∘ ![β] := by
    funext j
    fin_cases j
    simp [σ, algHomAdjoinIntegralEquiv_symm_apply_gen]
  have h2 : (ι ∘ ![AdjoinSimple.gen ℚ α]) = ![α] := by
    funext j
    fin_cases j
    simp [ι]
  rw [← h2, affineWeilHeight_comp_algHom ι, ← affineWeilHeight_comp_algHom σ, h1]
  rfl

/-- The roots of a split polynomial, enumerated by `Fin` of its degree. -/
private theorem exists_univ_map_eq_roots {F L : Type*} [Field F] [Field L] [Algebra F L]
    {p : F[X]} (hs : (p.map (algebraMap F L)).Splits) :
    ∃ β : Fin p.natDegree → L, univ.val.map β = (p.map (algebraMap F L)).roots := by
  obtain ⟨n, β, hβ⟩ : ∃ (n : ℕ) (β : Fin n → L), univ.val.map β = (p.map (algebraMap F L)).roots :=
    ⟨_, _, by rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩
  obtain rfl : n = p.natDegree := by
    rw [← natDegree_map (algebraMap F L), ← splits_iff_card_roots.1 hs, ← hβ, Multiset.card_map,
      card_val, card_univ, Fintype.card_fin]
  exact ⟨β, hβ⟩

/-- Vieta: the signed coefficients of a monic split polynomial are the elementary symmetric
functions of its roots. -/
private theorem neg_one_pow_mul_coeff_eq_esymm {F L : Type*} [Field F] [Field L] [Algebra F L]
    {p : F[X]} (hp : p.Monic) (hs : (p.map (algebraMap F L)).Splits) {β : Fin p.natDegree → L}
    (hβ : univ.val.map β = (p.map (algebraMap F L)).roots) (r : Fin p.natDegree) :
    algebraMap F L ((-1) ^ ((r : ℕ) + 1) * p.coeff (p.natDegree - ((r : ℕ) + 1))) =
      ∑ t ∈ powersetCard ((r : ℕ) + 1) (univ : Finset (Fin p.natDegree)), t.prod β := by
  have hcard : (p.map (algebraMap F L)).roots.card = p.natDegree := by
    rw [splits_iff_card_roots.1 hs, natDegree_map]
  rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, hs.eq_prod_roots_of_monic (hp.map _),
    Multiset.prod_X_sub_C_coeff _ (by omega), hcard, show p.natDegree - (p.natDegree - (r + 1)) =
      r + 1 by omega, ← hβ, Finset.esymm_map_val, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]

/-- For `α` algebraic over `ℚ` of degree `d = (minpoly ℚ α).natDegree`, write
`minpoly ℚ α = ∑_{r=0}^d (-1)^r s_r T^{d-r}`. The height of the coefficient point
`(1 : s_1 : … : s_d)`, i.e. `Faltings.affineWeilHeight` of `(s_1, …, s_d) ∈ ℚ^d`, is at most
`d · h(α) + d · log 2`, where `h(α) = Faltings.affineWeilHeight ![α]`. -/
@[faltings "lem_ht_height_minimal_polynomial"]
public theorem affineWeilHeight_minpoly_coeff_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] (α : K) :
    affineWeilHeight (K := ℚ) (fun r : Fin (minpoly ℚ α).natDegree =>
        (-1) ^ ((r : ℕ) + 1) * (minpoly ℚ α).coeff ((minpoly ℚ α).natDegree - ((r : ℕ) + 1))) ≤
      (minpoly ℚ α).natDegree * affineWeilHeight ![α] +
        (minpoly ℚ α).natDegree * Real.log 2 := by
  classical
  let L := (minpoly ℚ α).SplittingField
  have : NumberField L := { }
  have hs : ((minpoly ℚ α).map (algebraMap ℚ L)).Splits := SplittingField.splits _
  obtain ⟨β, hβ⟩ := exists_univ_map_eq_roots hs
  have hconj (i) : ∑ᶠ w : NumberFieldPlace L, Real.posLog (w.normalizedAbv (β i)) =
      affineWeilHeight ![α] := by
    rw [← affineWeilHeight_singleton, affineWeilHeight_conj (α := α)]
    rw [aroots, ← hβ]
    exact Multiset.mem_map_of_mem _ (mem_univ i)
  rw [← affineWeilHeight_comp_algHom (Algebra.ofId ℚ L), show Algebra.ofId ℚ L ∘ _ =
      algebraMap L L ∘ _ from funext fun r =>
        neg_one_pow_mul_coeff_eq_esymm (minpoly.monic (Algebra.IsIntegral.isIntegral α)) hs hβ r,
    affineWeilHeight_eq_finsum_posLog]
  refine (finsum_posLog_vectorAbv_esymm_le β).trans_eq ?_
  simp only [hconj, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Faltings
