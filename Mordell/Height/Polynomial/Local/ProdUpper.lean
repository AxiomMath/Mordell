module

public import Mordell.NumberField.NormalizedAbv.Basic
public import Mordell.Polynomial.SupNormProd
public import Mordell.Height.Polynomial.Local.GaussLemma
public import Mordell.NumberField.NormalizedAbv.Explicit

/-!
# An upper bound for the local size of a product of polynomials

Let `K` be a number field, `w` a place of `K`, and `P_1, …, P_k ∈ K[x_1, …, x_m]` nonzero
polynomials. Put `P = P_1 ⋯ P_k` and let `d'` be the total of the partial degrees
`∑_μ deg_{x_μ}(P_1 ⋯ P_{k-1})` of the product of all factors but one. Then
`|P|_w ≤ |2^{d'}|_w^{ε_w} ∏_j |P_j|_w`, where `|·|_w` is the local size
`Faltings.NumberFieldPlace.mvPolynomialAbv` and `ε_w` is
`Faltings.NumberFieldPlace.archimedeanIndicator w`. Each coefficient of `P` is a sum of at most
`∏_μ (deg_{x_μ}(P_1 ⋯ P_{k-1}) + 1) ≤ 2^{d'}` products of a coefficient of `P_1 ⋯ P_{k-1}` and one
of `P_k`; at a finite place the ultrametric inequality and Gauss' lemma give the bound with
`ε_w = 0`.

## Main results

* `Faltings.NumberFieldPlace.mvPolynomialAbv_prod_le`: the bound
  `|∏_{j ∈ s} P_j|_w ≤ |2^{d'}|_w^{ε_w} ∏_{j ∈ s} |P_j|_w`.
* `Faltings.NumberFieldPlace.mvPolynomialAbv_inr_eq`: at an infinite place, the local size of a
  polynomial is a power of the largest norm of a coefficient of its image in `ℂ`.

## Implementation notes

The factors are a family `P : ι → MvPolynomial σ K` indexed by a `Finset` `s` of an arbitrary
type, with an arbitrary type `σ` of variables, and the omitted factor is any `j₀ ∈ s`; the
source's case is `s = {1, …, k}`, `j₀ = k`, `σ = Fin m`. The number
`∑_μ deg_{x_μ} Q` is written `Multiset.card Q.degrees`: the multiplicity of `μ` in
`MvPolynomial.degrees Q` is `MvPolynomial.degreeOf μ Q`, so this is the same sum, and it makes
sense for any type of variables. When `s = {j₀}` the product over `s.erase j₀` is `1` and
`d' = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
-/

@[expose] public section

namespace Faltings

namespace NumberFieldPlace

open NumberField _root_.MvPolynomial Faltings.MvPolynomial

/-- Renaming the variables along an injective map preserves `ℓ^∞`. -/
private lemma supNorm_rename {τ υ : Type*} {f : τ → υ} (hf : Function.Injective f)
    (q : _root_.MvPolynomial τ ℂ) : supNorm (rename f q) = supNorm q := by
  apply le_antisymm
  · refine (supNorm_le_iff (supNorm_nonneg q)).2 fun I => ?_
    by_cases h : ∃ u, Finsupp.mapDomain f u = I
    · obtain ⟨u, rfl⟩ := h
      rw [coeff_rename_mapDomain f hf]
      exact norm_coeff_le_supNorm q u
    · rw [coeff_rename_eq_zero f q I fun u hu => absurd ⟨u, hu⟩ h, norm_zero]
      exact supNorm_nonneg q
  · refine (supNorm_le_iff (supNorm_nonneg _)).2 fun I => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact norm_coeff_le_supNorm _ _

/-- At an infinite place `w` with `|x|_w = ‖τ x‖ ^ t` for a ring hom `τ : K →+* ℂ` and `t ≥ 0`,
the local size of a polynomial `Q` is `‖τ Q‖_∞ ^ t`, where `‖·‖_∞` is
`Faltings.MvPolynomial.supNorm`, the largest norm of a coefficient. -/
theorem mvPolynomialAbv_inr_eq {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (w : InfinitePlace K) {τ : K →+* ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hx : ∀ x : K, NumberFieldPlace.normalizedAbv (.inr w) x = ‖τ x‖ ^ t)
    (Q : _root_.MvPolynomial σ K) :
    NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => Q) = supNorm (map τ Q) ^ t := by
  have hc : ∀ I, NumberFieldPlace.normalizedAbv (.inr w) (Q.coeff I) =
      ‖(map τ Q).coeff I‖ ^ t := fun I => by rw [hx, coeff_map]
  have hle : ∀ I, NumberFieldPlace.normalizedAbv (.inr w) (Q.coeff I) ≤ supNorm (map τ Q) ^ t :=
    fun I => by
      rw [hc]
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_coeff_le_supNorm _ _) ht
  obtain ⟨I, hI⟩ := exists_norm_coeff_eq_supNorm (map τ Q)
  unfold NumberFieldPlace.mvPolynomialAbv
  rw [ciSup_unique]
  refine le_antisymm (ciSup_le hle) ?_
  rw [← hI, ← hc]
  exact le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ I

/-- The bound at an infinite place, for a finite type of variables: this is
`Faltings.MvPolynomial.supNorm_prod_le_two_pow_mul_prod_supNorm` for the `σ P_j`, raised to the
power `t = n_w / [K : ℚ]`. -/
private lemma mvPolynomialAbv_inr_prod_le {K : Type*} [Field K] [NumberField K] {τ ι : Type*}
    [Fintype τ] [DecidableEq ι] (w : InfinitePlace K) (s : Finset ι) {j₀ : ι} (hj₀ : j₀ ∈ s)
    (Q : ι → _root_.MvPolynomial τ K) (hQ : ∀ j ∈ s, Q j ≠ 0) :
    NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => ∏ j ∈ s, Q j) ≤
      NumberFieldPlace.normalizedAbv (.inr w) ((2 : K) ^ Multiset.card (∏ j ∈ s.erase j₀, Q j).degrees) *
        ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => Q j) := by
  obtain ⟨-, -, hx⟩ := NumberFieldPlace.localDegree_inr_eq_mult_and_normalizedAbv_inr_eq w w.embedding
    w.mk_embedding (w.comap (algebraMap ℚ K)) ⟨rfl⟩
  set t : ℝ := _ / _
  have ht : 0 ≤ t := by positivity
  have hbound := supNorm_prod_le_two_pow_mul_prod_supNorm s (fun j => map w.embedding (Q j))
    (fun j hj => by simpa using (map_injective _ w.embedding.injective).ne (hQ j hj)) hj₀
  rw [← map_prod, ← map_prod] at hbound
  rw [← degrees_map_of_injective _ w.embedding.injective, card_degrees_eq_sum_degreeOf]
  simp only [mvPolynomialAbv_inr_eq w ht hx, hx, map_pow, map_ofNat, norm_pow,
    Complex.norm_ofNat]
  rw [Real.finset_prod_rpow _ _ fun j _ => supNorm_nonneg _,
    ← Real.mul_rpow (by positivity) (Finset.prod_nonneg fun j _ => supNorm_nonneg _)]
  exact Real.rpow_le_rpow (supNorm_nonneg _) hbound ht

/-- The local size `Faltings.NumberFieldPlace.mvPolynomialAbv` of a product of nonzero polynomials
at a place `w` of a number field is at most `|2^{d'}|_w^{ε_w}` times the product of the local sizes
of the factors, where `ε_w = Faltings.NumberFieldPlace.archimedeanIndicator w` and
`d' = ∑_μ deg_{x_μ} (∏_{j ∈ s, j ≠ j₀} P_j)` is the sum of the partial degrees of the product of
all factors but `P_{j₀}`. -/
@[faltings "lem_ht_local_product_upper"]
public theorem mvPolynomialAbv_prod_le {K : Type*} [Field K] [NumberField K] {σ ι : Type*}
    [DecidableEq ι]
    (w : NumberFieldPlace K) (s : Finset ι) {j₀ : ι} (hj₀ : j₀ ∈ s) (P : ι → MvPolynomial σ K)
    (hP : ∀ j ∈ s, P j ≠ 0) :
    NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => ∏ j ∈ s, P j) ≤
      w.normalizedAbv ((2 : K) ^ Multiset.card (∏ j ∈ s.erase j₀, P j).degrees) ^
          w.archimedeanIndicator *
        ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv w (fun _ : Unit => P j) := by
  rcases w with w | w
  · rw [NumberFieldPlace.archimedeanIndicator_inl, pow_zero, one_mul,
      NumberFieldPlace.mvPolynomialAbv_prod w s ⟨j₀, hj₀⟩ P]
  classical
  obtain ⟨-, -, hx⟩ := NumberFieldPlace.localDegree_inr_eq_mult_and_normalizedAbv_inr_eq w w.embedding
    w.mk_embedding (w.comap (algebraMap ℚ K)) ⟨rfl⟩
  -- the finitely many variables occurring in the `P j`
  set S : Finset σ := s.biUnion fun j => (P j).vars
  have habv (q : _root_.MvPolynomial S K) :
      NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => rename Subtype.val q) =
        NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => q) := by
    rw [mvPolynomialAbv_inr_eq w (by positivity) hx, mvPolynomialAbv_inr_eq w (by positivity) hx,
      map_rename, supNorm_rename Subtype.val_injective]
  have hex (j : ι) : ∃ q : _root_.MvPolynomial S K, j ∈ s → rename Subtype.val q = P j := by
    by_cases hj : j ∈ s
    · obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range (P j) (Subtype.val : S → σ)
        Subtype.val_injective fun x hx => ⟨⟨x, Finset.mem_biUnion.2 ⟨j, hj, hx⟩⟩, rfl⟩
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, hj.elim⟩
  choose Q hQ using hex
  have hprod {u : Finset ι} (hu : u ⊆ s) : ∏ j ∈ u, P j = rename Subtype.val (∏ j ∈ u, Q j) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun j hj => (hQ j (hu hj)).symm
  have hR : ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => P j) =
      ∏ j ∈ s, NumberFieldPlace.mvPolynomialAbv (.inr w) (fun _ : Unit => Q j) :=
    Finset.prod_congr rfl fun j hj => by rw [← hQ j hj, habv]
  rw [hprod subset_rfl, hprod (s.erase_subset j₀), habv, hR,
    degrees_rename_of_injective Subtype.val_injective, Multiset.card_map,
    NumberFieldPlace.archimedeanIndicator_inr, pow_one]
  refine mvPolynomialAbv_inr_prod_le w s hj₀ Q fun j hj h => hP j hj ?_
  rw [← hQ j hj, h, map_zero]

end NumberFieldPlace

end Faltings
