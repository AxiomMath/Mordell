module

public import Mordell.NumberField.Place.LocalDegree

/-!
# Sum of local degrees

Let `k ⊆ K` be number fields and `v` a place of `k`. The places `w` of `K` lying over `v` are
finitely many, and their local degrees `[K_w : k_v]` add up to the global degree `[K : k]`. This
comes from the isomorphism of `k_v`-algebras `K ⊗_k k_v ≅ ∏_{w ∣ v} K_w`.

## Main results

* `Faltings.NumberFieldPlace.finsum_localDegree_eq_finrank`: `∑_{w ∣ v} [K_w : k_v] = [K : k]`.
* `Faltings.denseRange_embedding_pi`: approximation theorem, `K` is dense in `∏_i K_{P_i}` for
  finitely many distinct primes `P_i` of `𝓞 K`.

## Implementation notes

The sum over `w ∣ v` is a `finsum` over the subtype of places of `K` lying over `v`. The
statement implies that this subtype is finite: a `finsum` with infinite support is `0`, while
`Module.finrank k K` is positive.

## References

* [Z. Gao, *Heights*][gao2022], Lemma 1.1.10.
* [J. Neukirch, *Algebraic Number Theory*][neukirch1999], Ch. II, Prop. 8.3.
-/

@[expose] public section

namespace Faltings

open NumberField IsDedekindDomain HeightOneSpectrum
open scoped Valued

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- For `P ∣ p`, the continuous embedding `k_p → K_P` of adic completions extending `k → K`. -/
private noncomputable def completionMap (p : HeightOneSpectrum (𝓞 k)) (P : HeightOneSpectrum (𝓞 K))
    [h : P.asIdeal.LiesOver p.asIdeal] : p.adicCompletion k →+* P.adicCompletion K :=
  (adicCompletion.equiv K P).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (p.valuation k)) (WithVal (P.valuation K)))
      (uniformContinuous_algebraMap_liesOver k K p P).continuous).comp
      (adicCompletion.equiv k p).toRingHom)

private theorem continuous_completionMap (p : HeightOneSpectrum (𝓞 k)) (P : HeightOneSpectrum (𝓞 K))
    [h : P.asIdeal.LiesOver p.asIdeal] : Continuous (completionMap p P) :=
  (adicCompletion.continuous_ofCompletion K P).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion k p))

private theorem completionMap_algebraMap (p : HeightOneSpectrum (𝓞 k)) (P : HeightOneSpectrum (𝓞 K))
    [h : P.asIdeal.LiesOver p.asIdeal] (x : k) :
    completionMap p P (algebraMap k (p.adicCompletion k) x) =
      FinitePlace.embedding P (algebraMap k K x) := by
  simp only [completionMap, RingHom.comp_apply]
  apply adicCompletion.ext
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, UniformSpace.Completion.mapRingHom_apply,
    adicCompletion.equiv_apply, algebraMap_adicCompletion_toCompletion]
  rw [show (algebraMap k (p.valuation k).Completion) x =
      ((algebraMap k (WithVal (p.valuation k)) x : WithVal (p.valuation k)) :
        (p.valuation k).Completion) from rfl,
    UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver k K p P)]
  rfl

/-- `|x|_P = |x|_p ^ (e f)` for `x ∈ k`. -/
private theorem norm_embedding_algebraMap (p : HeightOneSpectrum (𝓞 k))
    (P : HeightOneSpectrum (𝓞 K))
    [h : P.asIdeal.LiesOver p.asIdeal] (x : k) :
    ‖FinitePlace.embedding P (algebraMap k K x)‖ =
      ‖FinitePlace.embedding p x‖ ^
        (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) := by
  rw [← FinitePlace.equivHeightOneSpectrum_symm_apply,
    ← FinitePlace.equivHeightOneSpectrum_symm_apply,
    FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap p P x]

private theorem degree_pos (p : HeightOneSpectrum (𝓞 k)) (P : HeightOneSpectrum (𝓞 K))
    [P.asIdeal.LiesOver p.asIdeal] :
    0 < P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k) :=
  mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 k)) (P.asIdeal.inertiaDeg_pos (𝓞 k))

/-- `‖ψ c‖ = ‖c‖ ^ (e f)` for the embedding `ψ : k_p → K_P`, by density of `k` in `k_p`. -/
private theorem norm_completionMap (p : HeightOneSpectrum (𝓞 k)) (P : HeightOneSpectrum (𝓞 K))
    [h : P.asIdeal.LiesOver p.asIdeal] (c : p.adicCompletion k) :
    ‖completionMap p P c‖ =
      ‖c‖ ^ (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) := by
  induction c using (denseRange_algebraMap k p).induction_on with
  | hp => exact isClosed_eq ((continuous_completionMap p P).norm) (continuous_norm.pow _)
  | ih x =>
    rw [completionMap_algebraMap, norm_embedding_algebraMap p P]
    rfl

/-- `N(P)⁻¹`, the absolute value at `P` of a uniformizer at `P`, so that
`x ∈ P ^ n ↔ |x|_P ≤ rad P ^ n` for `x ∈ 𝓞 K` (`mem_pow_iff_norm_le`). -/
private noncomputable def rad (P : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P)
    (WithZero.exp (-1)) : ℝ)

private theorem rad_pos (P : HeightOneSpectrum (𝓞 K)) : 0 < rad P := by
  unfold rad
  exact_mod_cast WithZeroMulInt.toNNReal_pos _ (by simp)

private theorem rad_lt_one (P : HeightOneSpectrum (𝓞 K)) : rad P < 1 := by
  unfold rad
  exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)).2 (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)

private theorem mem_pow_iff_norm_le (P : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (n : ℕ) :
    x ∈ P.asIdeal ^ n ↔ ‖FinitePlace.embedding P (algebraMap (𝓞 K) K x)‖ ≤ rad P ^ n := by
  rw [FinitePlace.norm_embedding_int, ← intValuation_le_pow_iff_mem, rad, ← NNReal.coe_pow,
    ← map_pow, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)).le_iff_le,
    ← WithZero.exp_nsmul]
  simp

/-- Approximation theorem: `K` is dense in `∏_i K_{P_i}` for finitely many distinct primes
`P_i` of `𝓞 K`. -/
theorem denseRange_embedding_pi {ι : Type*} [Finite ι] {P : ι → HeightOneSpectrum (𝓞 K)}
    (hP : Function.Injective P) :
    DenseRange (fun x : K => fun i => FinitePlace.embedding (P i) x) := by
  classical
  have := Fintype.ofFinite ι
  rw [Metric.denseRange_iff]
  intro x r hr
  have hr2 : 0 < r / 2 := half_pos hr
  have hu : ∀ i, ∃ u : K, dist (x i) (FinitePlace.embedding (P i) u) < r / 2 := fun i =>
    Metric.denseRange_iff.1 (denseRange_algebraMap K (P i)) (x i) _ hr2
  choose u hu using hu
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) u
  choose m hm using hD
  have hD0 : (algebraMap (𝓞 K) K D) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors D.2
  have hN : ∀ᶠ N in Filter.atTop, ∀ i,
      rad (P i) ^ N / ‖FinitePlace.embedding (P i) (algebraMap (𝓞 K) K D)‖ < r / 2 := by
    rw [Filter.eventually_all]
    intro i
    have h0 : Filter.Tendsto
        (fun N : ℕ => rad (P i) ^ N / ‖FinitePlace.embedding (P i) (algebraMap (𝓞 K) K D)‖)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (rad_pos (P i)).le
        (rad_lt_one (P i))).div_const ‖FinitePlace.embedding (P i) (algebraMap (𝓞 K) K D)‖
    exact h0.eventually (gt_mem_nhds hr2)
  obtain ⟨N, hN⟩ := hN.exists
  obtain ⟨z, hz⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun i => (P i).asIdeal) (fun _ => N) (fun i _ => (P i).prime)
    (fun _ _ _ _ hij h => hij (hP (HeightOneSpectrum.ext h))) (fun i => m i.1)
  refine ⟨algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K D, ?_⟩
  rw [dist_pi_lt_iff hr]
  intro i
  have hzP : z - m i ∈ (P i).asIdeal ^ N := hz i (Finset.mem_univ i)
  have hu' : u i = algebraMap (𝓞 K) K (m i) / algebraMap (𝓞 K) K D := by
    rw [eq_div_iff hD0, hm i, Algebra.smul_def, mul_comm]
  have key : dist (FinitePlace.embedding (P i) (u i))
      (FinitePlace.embedding (P i) (algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K D)) ≤
      rad (P i) ^ N / ‖FinitePlace.embedding (P i) (algebraMap (𝓞 K) K D)‖ := by
    rw [dist_eq_norm, ← map_sub, hu', div_sub_div_same, ← map_sub, map_div₀, norm_div]
    gcongr
    rw [← norm_neg, ← map_neg, ← map_neg, neg_sub]
    exact (mem_pow_iff_norm_le (P i) _ N).1 hzP
  linarith [dist_triangle (x i) (FinitePlace.embedding (P i) (u i))
    (FinitePlace.embedding (P i) (algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K D)), hu i, hN i]

/-- If `b` reduces to an `𝓞 k ⧸ p`-linearly independent family in `𝓞 K ⧸ p 𝓞 K`, then a
`k`-combination `∑ aᵢ bᵢ` is large at some `P ∣ p` in terms of its largest `p`-adic coefficient. -/
private theorem exists_le_norm_sum (p : HeightOneSpectrum (𝓞 k)) {ι : Type*} [Fintype ι]
    (b : ι → 𝓞 K)
    (hb : LinearIndependent (𝓞 k ⧸ p.asIdeal)
      (fun i => Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p.asIdeal) (b i)))
    (a : ι → k) (j : ι) (hj : a j ≠ 0)
    (hmax : ∀ i, ‖FinitePlace.embedding p (a i)‖ ≤ ‖FinitePlace.embedding p (a j)‖) :
    ∃ (P : HeightOneSpectrum (𝓞 K)) (_ : P.asIdeal.LiesOver p.asIdeal),
      ‖FinitePlace.embedding p (a j)‖ ^
          (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) *
          rad P ^ P.asIdeal.ramificationIdx (𝓞 k) ≤
        ‖FinitePlace.embedding P (∑ i, algebraMap k K (a i) * algebraMap (𝓞 K) K (b i))‖ := by
  classical
  set a' : ι → k := fun i => a i / a j with ha'_def
  have ha' : ∀ i, p.valuation k (a' i) ≤ 1 := by
    intro i
    have h1 : ‖FinitePlace.embedding p (a' i)‖ ≤ 1 := by
      rw [ha'_def, map_div₀, norm_div]
      exact div_le_one_of_le₀ (hmax i) (norm_nonneg _)
    rw [FinitePlace.norm_embedding'] at h1
    exact (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)).1 (by exact_mod_cast h1)
  choose n d hnd using fun i => p.exists_primeCompl_mul_eq_of_integer (a' i) (ha' i)
  set s : 𝓞 k := ∏ i, (d i : 𝓞 k) with hs_def
  have hs : s ∉ p.asIdeal := by
    have := (∏ i, d i).2
    rwa [Submonoid.coe_finsetProd] at this
  set α : ι → 𝓞 k := fun i => n i * ∏ l ∈ Finset.univ.erase i, (d l : 𝓞 k) with hα_def
  have hα : ∀ i, algebraMap (𝓞 k) k (α i) = a' i * algebraMap (𝓞 k) k s := by
    intro i
    rw [hα_def, hs_def, map_mul, ← hnd i, map_prod, map_prod,
      ← Finset.mul_prod_erase Finset.univ (fun l => algebraMap (𝓞 k) k (d l : 𝓞 k))
        (Finset.mem_univ i)]
    ring
  have hαj : α j = s := by
    apply IsFractionRing.injective (𝓞 k) k
    rw [hα, ha'_def]
    simp [hj]
  set z : 𝓞 K := ∑ i, algebraMap (𝓞 k) (𝓞 K) (α i) * b i with hz_def
  have hz : z ∉ Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p.asIdeal := by
    intro hz
    have h0 : ∑ i, Ideal.Quotient.mk p.asIdeal (α i) •
        Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p.asIdeal) (b i) = 0 := by
      simp_rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← map_sum]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hz
    have := Fintype.linearIndependent_iff.1 hb _ h0 j
    rw [Ideal.Quotient.eq_zero_iff_mem, hαj] at this
    exact hs this
  rw [Ideal.map_algebraMap_eq_finsetProd_pow p.ne_bot,
    ← IsDedekindDomain.inf_pow_eq_prod_of_prime _ (fun P => P) _
      (fun P hP => Ideal.prime_of_isPrime
        (Ideal.ne_bot_of_mem_primesOver p.ne_bot (Set.mem_toFinset.1 hP))
        (Set.mem_toFinset.1 hP).1)
      (fun _ _ _ _ h => h)] at hz
  simp only [Submodule.mem_finsetInf, not_forall] at hz
  obtain ⟨P, hP, hzP⟩ := hz
  have hPmem : P ∈ p.asIdeal.primesOver (𝓞 K) := Set.mem_toFinset.1 hP
  let Q : HeightOneSpectrum (𝓞 K) :=
    ⟨P, hPmem.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hPmem⟩
  have hQ : Q.asIdeal.LiesOver p.asIdeal := hPmem.2
  refine ⟨Q, hQ, ?_⟩
  have hzQ : rad Q ^ Q.asIdeal.ramificationIdx (𝓞 k) <
      ‖FinitePlace.embedding Q (algebraMap (𝓞 K) K z)‖ :=
    lt_of_not_ge fun h => hzP ((mem_pow_iff_norm_le Q z _).2 h)
  have hy : ∑ i, algebraMap k K (a i) * algebraMap (𝓞 K) K (b i) =
      algebraMap k K (a j) / algebraMap k K (algebraMap (𝓞 k) k s) *
        algebraMap (𝓞 K) K z := by
    have hs0 : algebraMap k K (algebraMap (𝓞 k) k s) ≠ 0 := by
      rw [map_ne_zero, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
      intro h0
      exact hs (h0 ▸ zero_mem _)
    rw [hz_def, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 k) k K, hα i, map_mul, ha'_def]
    have haj : algebraMap k K (a j) ≠ 0 := (map_ne_zero _).2 hj
    simp only [map_div₀]
    field_simp
  have hsQ : ‖FinitePlace.embedding Q (algebraMap k K (algebraMap (𝓞 k) k s))‖ = 1 := by
    rw [norm_embedding_algebraMap p Q, (FinitePlace.norm_eq_one_iff_notMem k p s).2 hs, one_pow]
  rw [hy, map_mul, map_div₀, norm_mul, norm_div, hsQ, div_one, norm_embedding_algebraMap p Q]
  exact mul_le_mul_of_nonneg_left hzQ.le (by positivity)

omit [NumberField K] in
/-- Some prime of `𝓞 K` lies over a prime `p` of `𝓞 k`. -/
private theorem nonempty_liesOver (p : HeightOneSpectrum (𝓞 k)) :
    Nonempty {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver p.asIdeal} := by
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hPm.isPrime, hP⟩⟩, hP⟩⟩

/-- A family `b` of integers of `K` that is linearly independent modulo `p 𝓞 K` over `𝓞 k ⧸ p`
stays linearly independent over `k_p` in `∏_{P ∣ p} K_P`: approximate the coefficients by
elements of `k` and compare `exists_le_norm_sum` with the ultrametric inequality. -/
private theorem eq_zero_of_forall_sum_completionMap_eq_zero (p : HeightOneSpectrum (𝓞 k))
    {ι : Type*} [Fintype ι] (b : ι → 𝓞 K)
    (hb : LinearIndependent (𝓞 k ⧸ p.asIdeal)
      (fun i => Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p.asIdeal) (b i)))
    (c : ι → p.adicCompletion k)
    (hc : ∀ (P : HeightOneSpectrum (𝓞 K)) (_ : P.asIdeal.LiesOver p.asIdeal),
      ∑ i, completionMap p P (c i) * FinitePlace.embedding P (algebraMap (𝓞 K) K (b i)) = 0) :
    c = 0 := by
  classical
  by_contra hc0
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hc0
  have : Nonempty ι := ⟨i0⟩
  have := nonempty_liesOver (K := K) p
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖c i‖
  have hM : 0 < ‖c j‖ := (norm_pos_iff.2 hi0).trans_le (hj i0)
  obtain ⟨P1, hP1⟩ := Finite.exists_min
    fun P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver p.asIdeal} =>
      rad P.1 ^ P.1.asIdeal.ramificationIdx (𝓞 k)
  set γ := rad P1.1 ^ P1.1.asIdeal.ramificationIdx (𝓞 k)
  have hγ0 : 0 < γ := pow_pos (rad_pos _) _
  have hγ1 : γ ≤ 1 := pow_le_one₀ (rad_pos _).le (rad_lt_one _).le
  set ε := ‖c j‖ * γ with hε_def
  have hε : 0 < ε := mul_pos hM hγ0
  have happrox : ∀ i, ∃ a : k, dist (c i) (algebraMap k (p.adicCompletion k) a) < ε :=
    fun i => Metric.denseRange_iff.1 (denseRange_algebraMap k p) (c i) ε hε
  choose a ha using happrox
  have hεM : ε ≤ ‖c j‖ := mul_le_of_le_one_right hM.le hγ1
  have hsub : ∀ i, ‖algebraMap k (p.adicCompletion k) (a i) - c i‖ < ε := fun i => by
    rw [← dist_eq_norm, dist_comm]
    exact ha i
  have haj : ‖FinitePlace.embedding p (a j)‖ = ‖c j‖ := by
    change ‖algebraMap k (p.adicCompletion k) (a j)‖ = _
    have h1 := (hsub j).trans_le hεM
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le] at this
  have hai : ∀ i, ‖FinitePlace.embedding p (a i)‖ ≤ ‖FinitePlace.embedding p (a j)‖ := by
    intro i
    rw [haj]
    change ‖algebraMap k (p.adicCompletion k) (a i)‖ ≤ _
    calc ‖algebraMap k (p.adicCompletion k) (a i)‖ =
          ‖(algebraMap k (p.adicCompletion k) (a i) - c i) + c i‖ := by rw [sub_add_cancel]
      _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖c j‖ := max_le ((hsub i).trans_le hεM).le (hj i)
  have haj0 : a j ≠ 0 := by
    intro h0
    rw [h0, map_zero, norm_zero] at haj
    exact hM.ne haj
  obtain ⟨P, hP, hlow⟩ := exists_le_norm_sum p b hb a j haj0 hai
  obtain ⟨i1, hi1⟩ := Finite.exists_max fun i => ‖algebraMap k (p.adicCompletion k) (a i) - c i‖
  have hup : ‖FinitePlace.embedding P (∑ i, algebraMap k K (a i) * algebraMap (𝓞 K) K (b i))‖ ≤
      ‖algebraMap k (p.adicCompletion k) (a i1) - c i1‖ ^
        (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) := by
    have heq : FinitePlace.embedding P (∑ i, algebraMap k K (a i) * algebraMap (𝓞 K) K (b i)) =
        ∑ i, completionMap p P (algebraMap k (p.adicCompletion k) (a i) - c i) *
          FinitePlace.embedding P (algebraMap (𝓞 K) K (b i)) := by
      simp only [map_sum, map_mul, map_sub, sub_mul, Finset.sum_sub_distrib, hc P hP, sub_zero,
        completionMap_algebraMap]
    rw [heq]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i _ => ?_
    rw [norm_mul, norm_completionMap]
    exact (mul_le_of_le_one_right (by positivity) (FinitePlace.norm_le_one K P (b i))).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hi1 i) _)
  have hd := degree_pos p P
  have h2 := pow_lt_pow_left₀ (hsub i1) (norm_nonneg _) hd.ne'
  have h3 : ε ^ (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) ≤
      ‖c j‖ ^ (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) * γ := by
    rw [hε_def, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hγ0.le hγ1 hd.ne') (by positivity)
  have h4 : ‖c j‖ ^ (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) * γ ≤
      ‖c j‖ ^ (P.asIdeal.ramificationIdx (𝓞 k) * P.asIdeal.inertiaDeg (𝓞 k)) *
        rad P ^ P.asIdeal.ramificationIdx (𝓞 k) :=
    mul_le_mul_of_nonneg_left (hP1 ⟨P, hP⟩) (by positivity)
  rw [haj] at hlow
  linarith [hlow.trans hup]

/-- `∑_{P ∣ p} [K_P : k_p] = [K : k]`: the map `k_p ⊗_k K → ∏_{P ∣ p} K_P` is bijective. -/
private theorem sum_finrank_completion (p : HeightOneSpectrum (𝓞 k)) :
    ∑ᶠ P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver p.asIdeal},
      @Module.finrank (p.adicCompletion k) (P.1.adicCompletion K) _ _
        (completionMap p P.1 (h := P.2)).toAlgebra.toModule = Module.finrank k K := by
  classical
  set ι := {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver p.asIdeal}
  have : Finite ι := NumberFieldPlace.finite_heightOneSpectrum_liesOver p
  let : Fintype ι := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  let inst (P : ι) : Algebra (p.adicCompletion k) (P.1.adicCompletion K) :=
    (completionMap p P.1 (h := P.2)).toAlgebra
  have (P : ι) : ContinuousSMul (p.adicCompletion k) (P.1.adicCompletion K) :=
    ⟨((continuous_completionMap p P.1 (h := P.2)).comp continuous_fst).mul continuous_snd⟩
  have (P : ι) : IsScalarTower k (p.adicCompletion k) (P.1.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun x => (completionMap_algebraMap p P.1 (h := P.2) x).symm
  let Φ : TensorProduct k (p.adicCompletion k) K →ₗ[p.adicCompletion k]
      ((P : ι) → P.1.adicCompletion K) :=
    LinearMap.pi fun P => (Algebra.TensorProduct.lift (Algebra.ofId _ (P.1.adicCompletion K))
      (IsScalarTower.toAlgHom k K (P.1.adicCompletion K)) fun _ _ => Commute.all _ _).toLinearMap
  have hΦ (c : p.adicCompletion k) (x : K) (P : ι) :
      Φ (c ⊗ₜ x) P = completionMap p P.1 (h := P.2) c * FinitePlace.embedding P.1 x := by
    simp [Φ]
    rfl
  have hsurj : Function.Surjective Φ := by
    have hdense : DenseRange Φ := by
      refine (denseRange_embedding_pi (K := K) (P := fun P : ι => P.1)
        Subtype.val_injective).mono ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨1 ⊗ₜ x, funext fun P => ?_⟩
      rw [hΦ, map_one, one_mul]
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact hdense.closure_range
  have hinj : Function.Injective Φ := by
    have := p.isMaximal
    let := Ideal.Quotient.field p.asIdeal
    set Q := Ideal.map (algebraMap (𝓞 k) (𝓞 K)) p.asIdeal
    let bq := Module.Free.chooseBasis (𝓞 k ⧸ p.asIdeal) (𝓞 K ⧸ Q)
    let b' : Module.Free.ChooseBasisIndex (𝓞 k ⧸ p.asIdeal) (𝓞 K ⧸ Q) → 𝓞 K :=
      fun i => (Ideal.Quotient.mk_surjective (bq i)).choose
    have hb' : LinearIndependent (𝓞 k ⧸ p.asIdeal) (fun i => Ideal.Quotient.mk Q (b' i)) := by
      simp_rw [b', (Ideal.Quotient.mk_surjective _).choose_spec]
      exact bq.linearIndependent
    have hli : LinearIndependent k (fun i => algebraMap (𝓞 K) K (b' i)) :=
      Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial k (S := 𝓞 k ⧸ p.asIdeal)
        (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact p.isMaximal.ne_top)
        ((Algebra.linearMap (𝓞 K) K).restrictScalars (𝓞 k)) (IsFractionRing.injective (𝓞 K) K)
        ((Submodule.mkQ Q).restrictScalars (𝓞 k)) hb'
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex (𝓞 k ⧸ p.asIdeal) (𝓞 K ⧸ Q)) =
        Module.finrank k K := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, Ideal.finrank_quotient_map p.asIdeal k K]
    have : Nonempty (Module.Free.ChooseBasisIndex (𝓞 k ⧸ p.asIdeal) (𝓞 K ⧸ Q)) :=
      Fintype.card_pos_iff.1 (hcard ▸ Module.finrank_pos)
    let bK := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hbK : ∀ i, bK i = algebraMap (𝓞 K) K (b' i) := fun i =>
      congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) i
    let bE := Algebra.TensorProduct.basis (p.adicCompletion k) bK
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxc : x = ∑ i, bE.repr x i ⊗ₜ[k] bK i := by
      conv_lhs => rw [← bE.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hc := eq_zero_of_forall_sum_completionMap_eq_zero p b' hb' (bE.repr x) fun P hP => by
      have := congrFun hx ⟨P, hP⟩
      rw [hxc, map_sum, Finset.sum_apply, Pi.zero_apply] at this
      simpa only [hΦ, hbK] using this
    exact bE.repr.map_eq_zero_iff.1 (Finsupp.ext (congrFun hc))
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have : Module.Finite (p.adicCompletion k) ((P : ι) → P.1.adicCompletion K) :=
    Module.Finite.equiv eΦ
  have (P : ι) : Module.Finite (p.adicCompletion k) (P.1.adicCompletion K) :=
    Module.Finite.of_surjective (LinearMap.proj (R := p.adicCompletion k)
      (φ := fun P : ι => P.1.adicCompletion K) P) (Function.surjective_eval P)
  rw [← Module.finrank_pi_fintype, ← eΦ.finrank_eq, Module.finrank_baseChange]

private theorem localDegree_inl (v : FinitePlace k) (w : FinitePlace K)
    (h : NumberFieldPlace.LiesOver (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k)) :
    NumberFieldPlace.localDegree (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k) h =
      @Module.finrank ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w).adicCompletion K) _ _
        (completionMap (FinitePlace.maximalIdeal v) (FinitePlace.maximalIdeal w)
          (h := (NumberFieldPlace.liesOver_inl_inl w v).1 h)).toAlgebra.toModule := by
  have h' := (NumberFieldPlace.liesOver_inl_inl w v).1 h
  have hex : ∃ φ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
      (FinitePlace.maximalIdeal w).adicCompletion K, Continuous φ ∧
        ∀ x : k, φ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
          FinitePlace.embedding (FinitePlace.maximalIdeal w) (algebraMap k K x) :=
    ⟨completionMap _ _ (h := h'), continuous_completionMap _ _ (h := h'),
      completionMap_algebraMap _ _ (h := h')⟩
  have huniq : hex.choose = completionMap _ _ (h := h') := by
    have hs := hex.choose_spec
    exact DFunLike.coe_injective ((denseRange_algebraMap k _).equalizer hs.1
      (continuous_completionMap _ _ (h := h'))
      (funext fun x => (hs.2 x).trans (completionMap_algebraMap _ _ (h := h') x).symm))
  rw [NumberFieldPlace.localDegree, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg (fun φ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
      (FinitePlace.maximalIdeal w).adicCompletion K =>
    @Module.finrank ((FinitePlace.maximalIdeal v).adicCompletion k)
      ((FinitePlace.maximalIdeal w).adicCompletion K) _ _ φ.toAlgebra.toModule) huniq

private theorem finsum_localDegree_inl (v : FinitePlace k) :
    ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver (.inl v : NumberFieldPlace k)},
      w.1.localDegree (.inl v) w.2 = Module.finrank k K := by
  let E2 : {w : FinitePlace K //
      (FinitePlace.maximalIdeal w).asIdeal.LiesOver (FinitePlace.maximalIdeal v).asIdeal} ≃
      {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.LiesOver (FinitePlace.maximalIdeal v).asIdeal} :=
    FinitePlace.equivHeightOneSpectrum.subtypeEquiv fun _ => Iff.rfl
  rw [← finsum_comp_equiv (NumberFieldPlace.finitePlaceLiesOverEquiv v),
    ← sum_finrank_completion (FinitePlace.maximalIdeal v),
    ← finsum_comp_equiv E2]
  exact finsum_congr fun w => localDegree_inl v w.1 w.2

private theorem finsum_localDegree_inr (v : InfinitePlace k) :
    ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver (.inr v : NumberFieldPlace k)},
      w.1.localDegree (.inr v) w.2 = Module.finrank k K := by
  classical
  rw [← finsum_comp_equiv (NumberFieldPlace.infinitePlaceLiesOverEquiv v),
    ← InfinitePlace.sum_inertiaDeg_eq_finrank k K v,
    finsum_eq_sum_of_fintype,
    Finset.sum_subtype (InfinitePlace.placesOver K v).toFinset (p := fun w => w.LiesOver v)
      (fun _ => Set.mem_toFinset)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : w.1.LiesOver v := w.2
  rw [InfinitePlace.inertiaDeg_eq_finrank]
  rfl

/-- For number fields `k ⊆ K` and a place `v` of `k`, the local degrees `[K_w : k_v]` of the
places `w` of `K` lying over `v` sum to `[K : k]`. -/
@[faltings "lem_ht_local_degrees"]
theorem NumberFieldPlace.finsum_localDegree_eq_finrank {k K : Type*} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] (v : NumberFieldPlace k) :
    ∑ᶠ w : {w : NumberFieldPlace K // w.LiesOver v}, w.1.localDegree v w.2 =
      Module.finrank k K := by
  rcases v with v | v
  · exact finsum_localDegree_inl v
  · exact finsum_localDegree_inr v

end Faltings
