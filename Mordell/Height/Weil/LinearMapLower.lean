module

public import Mordell.NumberField.NormalizedAbv.AbsoluteValue
public import Mordell.NumberField.NormalizedAbv.Integer
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Polynomial.Local.Size

/-!
# Lower bound for the height under a linear map on a closed subvariety

Let `A = (a_{ji})` be a nonzero matrix over `ℚ̄`, with rows indexed by `ι'` and columns by `ι`,
let `L_j(x) = ∑_i a_{ji} x_i` and let `Z ⊆ ℙ(ℚ̄^ι)` be the common zero locus of the `L_j`, so that
`φ = (L_j)_j : ℙ(ℚ̄^ι) ∖ Z → ℙ(ℚ̄^{ι'})`. If `X ⊆ ℙ(ℚ̄^ι)` is Zariski closed and `X ∩ Z = ∅`, then
there is a constant `C` with `h(φ(x)) ≥ h(x) - C` for every `x ∈ X`. The proof writes, by the
Nullstellensatz, a power `x_i^t` of every coordinate as `∑_j G_{ji} L_j` modulo the ideal of `X`,
and bounds `|x|_v` place by place.

## Main results

* `Faltings.weilHeight_le_weilHeight_linearMap_apply_add`: the bound above, for
  `Faltings.weilHeight`.

## Implementation notes

The closed set `X` is the common zero set of a family `S` of homogeneous polynomials in
`MvPolynomial ι K`, every closed subset of `ℙ(K^ι)` having this form; a point of `X` is given by
a nonzero representative `v : ι → K` at which every member of `S` vanishes. The condition
`X ∩ Z = ∅` says that `(∑_i a_{ji} v_i)_j ≠ 0` for every such `v`. The field `K` is an
algebraically closed algebraic extension of `ℚ`, that is, an algebraic closure of `ℚ`; over a
field that is not algebraically closed, disjointness of the `K`-points does not suffice (the
conic `x₁² + x₂² = 2x₀²` over `ℚ` has no rational point on `x₀ = 0`, but rational points of
unbounded height). The product `ι' × ι` carries no linear order of its own; none is needed here.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

namespace Faltings

open scoped LinearAlgebra.Projectivization
open MvPolynomial

section Graded

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma coe_decompose_homogeneousSubmodule {K σ : Type*} [Field K]
    (φ : MvPolynomial σ K) (i : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ K) φ i : MvPolynomial σ K) =
      homogeneousComponent i φ :=
  decomposition.decompose'_apply φ i

private lemma homogeneousComponent_mem_span {K σ : Type*} [Field K] {S : Set (MvPolynomial σ K)}
    (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d) {y : MvPolynomial σ K} (hy : y ∈ Ideal.span S)
    (n : ℕ) : homogeneousComponent n y ∈ Ideal.span S := by
  have := Ideal.homogeneous_span (homogeneousSubmodule σ K) S fun F hF => by
    obtain ⟨d, hd⟩ := hS F hF; exact ⟨d, hd⟩
  simpa only [coe_decompose_homogeneousSubmodule] using this n hy

private lemma homogeneousComponent_mul_of_isHomogeneous_one {K σ : Type*} [Field K]
    {L : MvPolynomial σ K} (hL : L.IsHomogeneous 1) (G : MvPolynomial σ K) {t : ℕ} (ht : 1 ≤ t) :
    homogeneousComponent t (G * L) = homogeneousComponent (t - 1) G * L := by
  have := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ K) t (a := G)
    (b := L) (i := 1) hL
  rwa [ite_eq_left ht, coe_decompose_homogeneousSubmodule, coe_decompose_homogeneousSubmodule] at this

/-- The Nullstellensatz step: powers of the coordinates are combinations of the linear forms,
with homogeneous coefficients, on the zero set of `S`. -/
private lemma exists_pow_eq_sum_mul {K : Type*} [Field K] [IsAlgClosed K] {ι ι' : Type*}
    [Fintype ι] [Fintype ι'] (A : ι' × ι → K) (S : Set (MvPolynomial ι K))
    (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d)
    (hXZ : ∀ v : ι → K, v ≠ 0 → (∀ F ∈ S, MvPolynomial.eval v F = 0) →
      (fun j => ∑ i, A (j, i) * v i) ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ ∃ G : ι' → ι → MvPolynomial ι K, (∀ j i, (G j i).IsHomogeneous (t - 1)) ∧
      ∀ v : ι → K, (∀ F ∈ S, MvPolynomial.eval v F = 0) →
        ∀ i, v i ^ t = ∑ j, MvPolynomial.eval v (G j i) * ∑ i', A (j, i') * v i' := by
  classical
  set L : ι' → MvPolynomial ι K := fun j => ∑ i, C (A (j, i)) * X i with hLdef
  have hL : ∀ j, (L j).IsHomogeneous 1 := fun j =>
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_C_mul_X _ i)
  have hLeval : ∀ v j, eval v (L j) = ∑ i, A (j, i) * v i := fun v j => by simp [hLdef]
  set I : Ideal (MvPolynomial ι K) := Ideal.span S ⊔ Ideal.span (Set.range L)
  -- every coordinate vanishes on the zero locus of `I`
  have hrad : ∀ i, X i ∈ I.radical := by
    intro i
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have hS0 : ∀ F ∈ S, eval x F = 0 := fun F hF => by
      simpa [coe_aeval_eq_eval] using hx F (Ideal.mem_sup_left (Ideal.subset_span hF))
    have hL0 : (fun j => ∑ i, A (j, i) * x i) = 0 := by
      funext j
      rw [← hLeval]
      simpa [coe_aeval_eq_eval] using
        hx (L j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))
    simp [show x = 0 from of_not_not fun h0 => hXZ x h0 hS0 hL0]
  choose n hn using hrad
  refine ⟨∑ i, n i + 1, by omega, ?_⟩
  have hmem : ∀ i, X i ^ (∑ i, n i + 1) ∈ I := fun i => by
    have hle : n i ≤ ∑ i, n i + 1 :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by omega)
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact I.mul_mem_left _ (hn i)
  set t := ∑ i, n i + 1
  have hdec : ∀ i, ∃ y ∈ Ideal.span S, ∃ G' : ι' → MvPolynomial ι K,
      y + ∑ j, G' j * L j = X i ^ t := by
    intro i
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hmem i)
    obtain ⟨G', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hz
    exact ⟨y, hy, G', hyz⟩
  choose y hy G' hG' using hdec
  refine ⟨fun j i => homogeneousComponent (t - 1) (G' i j), fun j i =>
    homogeneousComponent_isHomogeneous _ _, ?_⟩
  intro v hv i
  have hX : X i ^ t = homogeneousComponent t (y i) +
      ∑ j, homogeneousComponent (t - 1) (G' i j) * L j := by
    have := congrArg (homogeneousComponent t) (hG' i)
    rw [homogeneousComponent_of_mem (isHomogeneous_X_pow i t), ite_eq_left rfl, map_add,
      map_sum] at this
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun j _ =>
      homogeneousComponent_mul_of_isHomogeneous_one (hL j) _ (by omega)
  have hy0 : eval v (homogeneousComponent t (y i)) = 0 := by
    have hle : Ideal.span S ≤ RingHom.ker (eval v) :=
      Ideal.span_le.2 fun F hF => (RingHom.mem_ker).2 (hv F hF)
    exact (RingHom.mem_ker).1 (hle (homogeneousComponent_mem_span hS (hy i) t))
  simpa [hy0, hLeval] using congrArg (eval v) hX

end Graded

section Local

open NumberFieldPlace

variable {F : Type*} [Field F] [NumberField F]

/-- The local bound for values of forms
(`Faltings.NumberFieldPlace.normalizedAbv_eval_le_of_isHomogeneous`), with the local size of `G`
replaced by that of a vector `c` containing its coefficients:
`|G(x)|_w ≤ |N|_w ^ ε_w |c|_w |x|_w ^ e`. -/
private lemma normalizedAbv_eval_le {σ κ : Type*} [Fintype σ] [Finite κ] (w : NumberFieldPlace F)
    {N e : ℕ} (hN : 1 ≤ N) {G : MvPolynomial σ F} (hG : G.IsHomogeneous e)
    (hGN : G.support.card ≤ N) {c : κ → F} (hc : ∀ I, G.coeff I ≠ 0 → ∃ k, c k = G.coeff I)
    (x : σ → F) :
    w.normalizedAbv (eval x G) ≤
      w.normalizedAbv (N : F) ^ w.archimedeanIndicator * w.vectorAbv c * w.vectorAbv x ^ e := by
  have hN0 := pow_nonneg (normalizedAbv_nonneg w (N : F)) w.archimedeanIndicator
  rcases G.support.eq_empty_or_nonempty with h0 | hs
  · rw [support_eq_empty.1 h0, map_zero, normalizedAbv_zero]
    exact mul_nonneg (mul_nonneg hN0 (w.vectorAbv_nonneg c)) (pow_nonneg (w.vectorAbv_nonneg x) e)
  rw [eval_eq', mul_assoc]
  exact (normalizedAbv_sum_le w hs _).trans <| mul_le_mul
    (normalizedAbv_natCast_pow_le w hs.card_pos hGN)
    (Finset.sup'_le _ _ fun I hI => (normalizedAbv_coeff_mul_prod_le w hG x hI).trans <|
      mul_le_mul_of_nonneg_right (by
        obtain ⟨k, hk⟩ := hc I (mem_support_iff.1 hI)
        exact hk ▸ w.normalizedAbv_le_vectorAbv c k) (pow_nonneg (w.vectorAbv_nonneg x) e))
    (Finset.le_sup'_of_le _ hs.choose_spec (normalizedAbv_nonneg _ _)) hN0

/-- The local estimate: from `y_i ^ t = ∑_j G_{ji}(y) ℓ_j` with `G_{ji}` forms of degree `t - 1`
having at most `N` monomials and coefficients among the entries of `c`, one gets
`|y|_w ≤ |m N|_w ^ ε_w |c|_w |ℓ|_w`, with `m` the number of forms. -/
private lemma vectorAbv_le_of_pow_eq_sum {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Nonempty ι']
    [Finite κ] (w : NumberFieldPlace F) {t N : ℕ} (ht : 1 ≤ t) (hN : 1 ≤ N)
    (G : ι' → ι → MvPolynomial ι F) (hG : ∀ j i, (G j i).IsHomogeneous (t - 1))
    (hGN : ∀ j i, (G j i).support.card ≤ N) (c : κ → F)
    (hc : ∀ j i I, (G j i).coeff I ≠ 0 → ∃ k, c k = (G j i).coeff I) {y : ι → F} (hy : y ≠ 0)
    (ℓ : ι' → F) (h : ∀ i, y i ^ t = ∑ j, eval y (G j i) * ℓ j) :
    w.vectorAbv y ≤ w.normalizedAbv ((Fintype.card ι' * N : ℕ) : F) ^ w.archimedeanIndicator *
      w.vectorAbv c * w.vectorAbv ℓ := by
  obtain ⟨v, hv⟩ := w.exists_absoluteValue_coe_eq_normalizedAbv
  have : Nonempty ι := let ⟨i, _⟩ := Function.ne_iff.1 hy; ⟨i⟩
  set a := w.vectorAbv y
  have ha : 0 < a := w.vectorAbv_pos hy
  set P := w.normalizedAbv (Fintype.card ι' : F) ^ w.archimedeanIndicator
  set Q := w.normalizedAbv (N : F) ^ w.archimedeanIndicator
  have hP : 0 ≤ P := pow_nonneg (normalizedAbv_nonneg _ _) _
  have hQ : 0 ≤ Q := pow_nonneg (normalizedAbv_nonneg _ _) _
  have hbound : ∀ i, w.normalizedAbv (y i) ^ t ≤
      P * Q * w.vectorAbv c * a ^ (t - 1) * w.vectorAbv ℓ := by
    intro i
    have h1 := normalizedAbv_sum_le w (Finset.univ_nonempty (α := ι'))
      (fun j => eval y (G j i) * ℓ j)
    rw [← h i, Finset.card_univ] at h1
    rw [← hv, ← map_pow, hv]
    refine h1.trans ?_
    rw [mul_assoc P, mul_assoc P, mul_assoc P]
    refine mul_le_mul_of_nonneg_left (Finset.sup'_le _ _ fun j _ => ?_) hP
    rw [← hv, map_mul, hv]
    exact mul_le_mul (normalizedAbv_eval_le w hN (hG j i) (hGN j i) (hc j i) y)
      (w.normalizedAbv_le_vectorAbv ℓ j) (normalizedAbv_nonneg _ _)
      (mul_nonneg (mul_nonneg hQ (w.vectorAbv_nonneg c)) (pow_nonneg ha.le _))
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => w.normalizedAbv (y i))
  have hat : a * a ^ (t - 1) ≤ (P * Q * w.vectorAbv c * w.vectorAbv ℓ) * a ^ (t - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel ht]
    calc a ^ t = w.normalizedAbv (y i) ^ t := by rw [hi]; rfl
      _ ≤ _ := hbound i
      _ = _ := by ring
  rw [Nat.cast_mul, ← hv, map_mul, hv, mul_pow]
  exact le_of_mul_le_mul_right hat (pow_pos ha _)

/-- The global estimate: summing the local estimate `vectorAbv_le_of_pow_eq_sum` over all places
gives `S(y) ≤ S(ℓ) + S(c) + log (m N)` for the sums of local heights. -/
private lemma sumLocalHeight_le_of_pow_eq_sum {ι ι' κ : Type*} [Fintype ι] [Fintype ι']
    [Nonempty ι'] [Finite κ] {t N : ℕ} (ht : 1 ≤ t) (hN : 1 ≤ N)
    (G : ι' → ι → MvPolynomial ι F) (hG : ∀ j i, (G j i).IsHomogeneous (t - 1))
    (hGN : ∀ j i, (G j i).support.card ≤ N) (c : κ → F)
    (hc : ∀ j i I, (G j i).coeff I ≠ 0 → ∃ k, c k = (G j i).coeff I) {y : ι → F} (hy : y ≠ 0)
    (ℓ : ι' → F) (h : ∀ i, y i ^ t = ∑ j, eval y (G j i) * ℓ j) :
    sumLocalHeight y ≤
      sumLocalHeight ℓ + sumLocalHeight c + Real.log ((Fintype.card ι' * N : ℕ) : ℝ) := by
  have hloc := fun w : NumberFieldPlace F => vectorAbv_le_of_pow_eq_sum w ht hN G hG hGN c hc hy ℓ h
  set r : ℕ := Fintype.card ι' * N
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Fintype.card_ne_zero (by omega))
  have hrF : (r : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let w₀ : NumberFieldPlace F := Sum.inr (Classical.arbitrary _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa [NumberFieldPlace.vectorAbv] using (w₀.vectorAbv_pos hy).trans_le (hloc w₀)
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simpa [NumberFieldPlace.vectorAbv] using (w₀.vectorAbv_pos hy).trans_le (hloc w₀)
  set f₁ : NumberFieldPlace F → ℝ := fun w =>
    (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (r : F))
  have hw : ∀ w : NumberFieldPlace F,
      w.localHeight y ≤ w.localHeight ℓ + w.localHeight c + f₁ w := by
    intro w
    have hP : 0 < w.normalizedAbv (r : F) ^ w.archimedeanIndicator :=
      pow_pos (w.normalizedAbv_pos hrF) _
    unfold NumberFieldPlace.localHeight
    have hc := w.vectorAbv_pos hc0
    refine (Real.log_le_log (w.vectorAbv_pos hy) (hloc w)).trans_eq ?_
    rw [Real.log_mul (mul_pos hP hc).ne' (w.vectorAbv_pos hℓ0).ne',
      Real.log_mul hP.ne' hc.ne', Real.log_pow]
    ring
  have hf₁ : (Function.support f₁).Finite := by
    refine (Set.finite_range (Sum.inr : NumberField.InfinitePlace F → NumberFieldPlace F)).subset ?_
    rintro (w | w) hw
    · simp [f₁] at hw
    · exact ⟨w, rfl⟩
  have hfy := NumberFieldPlace.finite_support_localHeight hy
  have hfc := NumberFieldPlace.finite_support_localHeight hc0
  have hfℓ := NumberFieldPlace.finite_support_localHeight hℓ0
  have hsum : (Function.support fun w : NumberFieldPlace F =>
      w.localHeight ℓ + w.localHeight c + f₁ w).Finite :=
    ((hfℓ.union hfc).union hf₁).subset fun w hw => by
      simp only [Function.mem_support, Set.mem_union] at hw ⊢
      by_contra hcon
      simp only [not_or, not_not] at hcon
      exact hw (by rw [hcon.1.1, hcon.1.2, hcon.2]; ring)
  have hf₁sum : ∑ᶠ w, f₁ w = Real.log (r : ℝ) := by
    simpa only [Int.cast_natCast] using finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast
      (K := F) (r := (r : ℤ)) (by exact_mod_cast hr)
  unfold sumLocalHeight
  calc ∑ᶠ w : NumberFieldPlace F, w.localHeight y
      ≤ ∑ᶠ w : NumberFieldPlace F, (w.localHeight ℓ + w.localHeight c + f₁ w) :=
        finsum_le_finsum' hfy hsum hw
    _ = _ := by
      rw [finsum_add_distrib ((hfℓ.union hfc).subset (Function.support_add _ _)) hf₁,
        finsum_add_distrib hfℓ hfc, hf₁sum]

end Local

/-- `Projectivization.mk` along an equality of representatives. -/
theorem mk_congr {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {v w : V}
    (h : v = w) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw := by
  subst h
  rfl

/-- Let `K` be an algebraically closed algebraic extension of `ℚ`, `A : ι' × ι → K` a nonzero
matrix, and `X ⊆ ℙ(K^ι)` the common zero set of a family `S` of homogeneous polynomials. If no
point of `X` is a common zero of the linear forms `L_j = ∑_i A (j, i) x_i`, there is a constant
`C` such that `h(x) ≤ h(φ(x)) + C` for every `x ∈ X`, where `φ(x) = (L_j(x))_j` and `h` is
`Faltings.weilHeight`. -/
@[faltings "lem_ht_linear_map_on_subvariety"]
public theorem weilHeight_le_weilHeight_linearMap_apply_add {K : Type*} [Field K]
    [IsAlgClosed K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {ι ι' : Type*} [Fintype ι]
    [LinearOrder ι] [Fintype ι'] [LinearOrder ι'] (A : ι' × ι → K) (hA : A ≠ 0)
    (S : Set (MvPolynomial ι K)) (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d)
    (hXZ : ∀ v : ι → K, v ≠ 0 → (∀ F ∈ S, MvPolynomial.eval v F = 0) →
      (fun j => ∑ i, A (j, i) * v i) ≠ 0) :
    ∃ C : ℝ, ∀ (v : ι → K) (hv : v ≠ 0) (hAv : (fun j => ∑ i, A (j, i) * v i) ≠ 0),
      (∀ F ∈ S, MvPolynomial.eval v F = 0) →
      weilHeight (Projectivization.mk K v hv) ≤
        weilHeight (Projectivization.mk K (fun j => ∑ i, A (j, i) * v i) hAv) + C := by
  classical
  obtain ⟨t, ht, G, hG, hid⟩ := exists_pow_eq_sum_mul A S hS hXZ
  have : Nonempty ι' := by
    obtain ⟨p, -⟩ := Function.ne_iff.1 hA
    exact ⟨p.1⟩
  -- the coefficient vector of the family `G`, with an extra entry `1`
  set s : Finset (ι →₀ ℕ) := Finset.univ.biUnion fun p : ι' × ι => (G p.1 p.2).support
  have hs : ∀ j i, (G j i).support ⊆ s := fun j i =>
    Finset.subset_biUnion_of_mem (fun p : ι' × ι => (G p.1 p.2).support) (Finset.mem_univ (j, i))
  let cK : Option (ι' × ι × s) → K := fun o => o.elim 1 fun k => (G k.1 k.2.1).coeff k.2.2
  have hcK : cK ≠ 0 := Function.ne_iff.2 ⟨none, one_ne_zero⟩
  let : LinearOrder (Option (ι' × ι × s)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  set N := s.card + 1
  refine ⟨weilHeight (Projectivization.mk K cK hcK) +
    Real.log ((Fintype.card ι' * N : ℕ) : ℝ), ?_⟩
  intro v hv hAv hvS
  -- a number field containing the coordinates of `v`, the entries of `A` and the coefficients
  set T : Set K := Set.range v ∪ Set.range A ∪ Set.range cK
  have : Finite T := ((Set.finite_range v).union (Set.finite_range A)).union
    (Set.finite_range cK) |>.to_subtype
  set E := IntermediateField.adjoin ℚ T
  have : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin fun r _ =>
    (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  have : NumberField E :=
    { to_finiteDimensional := by convert ‹FiniteDimensional ℚ E›; exact Subsingleton.elim _ _ }
  have hvE : ∀ i, v i ∈ E := fun i =>
    IntermediateField.subset_adjoin ℚ T (Or.inl (Or.inl ⟨i, rfl⟩))
  have hAE : ∀ p, A p ∈ E := fun p =>
    IntermediateField.subset_adjoin ℚ T (Or.inl (Or.inr ⟨p, rfl⟩))
  have hcE : ∀ o, cK o ∈ E := fun o =>
    IntermediateField.subset_adjoin ℚ T (Or.inr ⟨o, rfl⟩)
  set f := algebraMap E K
  have hf : Function.Injective f := f.injective
  let y : ι → E := fun i => ⟨v i, hvE i⟩
  let ℓ : ι' → E := fun j => ∑ i, (⟨A (j, i), hAE _⟩ : E) * y i
  let cE : Option (ι' × ι × s) → E := fun o => ⟨cK o, hcE o⟩
  have hGE : ∀ j i, ∃ g : MvPolynomial ι E, map f g = G j i := by
    intro j i
    refine (mem_range_map_iff_coeffs_subset).2 fun x hx => ?_
    obtain ⟨I, hI, rfl⟩ : ∃ I, ¬(G j i).coeff I = 0 ∧ (G j i).coeff I = x := by
      simpa [coeffs] using hx
    exact ⟨cE (some (j, i, ⟨I, hs j i (mem_support_iff.2 hI)⟩)), rfl⟩
  choose GE hGE using hGE
  have hfy : f ∘ y = v := rfl
  have hfℓ : f ∘ ℓ = fun j => ∑ i, A (j, i) * v i := by
    funext j
    simp [f, ℓ, y]
  have hfc : f ∘ cE = cK := rfl
  have hy0 : y ≠ 0 := fun h0 => hv (by rw [← hfy, h0]; funext; simp)
  have key := sumLocalHeight_le_of_pow_eq_sum (F := E) ht (Nat.le_add_left 1 s.card) GE
    (fun j i d hd => hG j i (by rw [← hGE, coeff_map]; exact (map_ne_zero f).2 hd))
    (fun j i => by
      rw [← support_map_of_injective _ hf, hGE]
      exact (Finset.card_le_card (hs j i)).trans (Nat.le_succ _))
    cE (fun j i I hI => by
      have hI' : I ∈ s := hs j i (by
        rw [← hGE, mem_support_iff, coeff_map]; exact (map_ne_zero f).2 hI)
      refine ⟨some (j, i, ⟨I, hI'⟩), Subtype.ext ?_⟩
      change (G j i).coeff I = f ((GE j i).coeff I)
      rw [← hGE, coeff_map])
    hy0 ℓ (fun i => hf (by
      rw [map_pow, map_sum]
      refine (hid v hvS i).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_mul, map_eval, hGE, hfy, ← congrFun hfℓ j]
      rfl))
  have hℓ0 : f ∘ ℓ ≠ 0 := by rw [hfℓ]; exact hAv
  have hc0 : f ∘ cE ≠ 0 := by rw [hfc]; exact hcK
  have h₁ := weilHeight_eq_sumLocalHeight (K := K) (F := E) (y := y)
    (x := Projectivization.mk K v hv) hv rfl
  have h₂ := weilHeight_eq_sumLocalHeight (K := K) (F := E) (y := ℓ)
    (x := Projectivization.mk K _ hAv) hℓ0 (mk_congr hfℓ _ _)
  have h₃ := weilHeight_eq_sumLocalHeight (K := K) (F := E) (y := cE)
    (x := Projectivization.mk K cK hcK) hc0 (mk_congr hfc _ _)
  linarith

end Faltings
