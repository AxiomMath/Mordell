module
public import Mordell.Roth.Wronskian.OneVariable
public import Mordell.Polynomial.HasseDeriv

/-!
# Non-vanishing of a generalized Wronskian

Let `K` be a field of characteristic `0` and let `φ₀, …, φₛ ∈ K[ς₁, …, ςₗ]` be linearly
independent over `K`. Then there are multi-indices `I'₀, …, I'ₛ ∈ ℕˡ` with `|I'_μ| ≤ μ ≤ s`,
where `|I|` is the sum of the entries of `I`, such that the generalized Wronskian
`Wr_{I'₀,…,I'ₛ}(φ₀, …, φₛ)` is a nonzero polynomial.

## Main results

* `Faltings.exists_generalizedWronskian_ne_zero`: a `K`-linearly independent family
  `φ : Fin (s + 1) → MvPolynomial (Fin l) K` has a nonzero generalized Wronskian
  `Faltings.generalizedWronskian I φ` for some multi-indices `I` with `∑ k, I μ k ≤ μ`.

## Implementation notes

Multi-indices are functions `Fin l → ℕ`, and the family of multi-indices is indexed by
`μ : Fin (s + 1)`, so the bound `μ ≤ s` is automatic and only `|I_μ| ≤ μ` is stated.

The proof follows the source. Choose `D` larger than every partial degree of the `φ_j` and put
`Φ_j(τ) = φ_j(τ, τ^D, …, τ^{D^{l-1}})` (the Kronecker substitution). Distinct monomials of
partial degrees `< D` go to distinct powers of `τ`, so the `Φ_j` are linearly independent and
their one-variable Wronskian is nonzero. By the chain rule, `f ↦ (d/dτ)^ν (f(τ, …))` lies in the
`K[τ]`-span of the operators `f ↦ (∂_I f)(τ, …)` with `|I| ≤ ν`; expanding the one-variable
Wronskian multilinearly in its rows writes it as a `K[τ]`-combination of specialisations of
generalized Wronskians `Wr_{I₀,…,Iₛ}(φ)` with `|I_ν| ≤ ν`, so one of these is nonzero.
The chain-rule coefficients are never written down: they are read off from membership in the
span, which is shown stable under `d/dτ` (raising the level by one) by induction on the span.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9, Lemma on generalized
  Wronskians.
-/

open MvPolynomial

namespace Faltings

section Monoid

variable {M : Type*} [Monoid M] {l : ℕ}

/-- An ordered product over `Fin l` of pairwise commuting factors is their `noncommProd`. -/
private lemma prod_ofFn_eq_noncommProd (f : Fin l → M)
    (hc : (↑(Finset.univ : Finset (Fin l)) : Set (Fin l)).Pairwise (Function.onFun Commute f)) :
    (List.ofFn f).prod = Finset.univ.noncommProd f hc := by
  rw [Finset.noncommProd]
  simp only [Fin.univ_val_map, Multiset.noncommProd_coe]

/-- Multiplying an ordered product of powers of commuting elements by one more factor. -/
private lemma mul_prod_ofFn_pow (A : Fin l → M) (hA : ∀ i j, Commute (A i) (A j))
    (n : Fin l → ℕ) (k : Fin l) :
    A k * (List.ofFn fun i => A i ^ n i).prod =
      (List.ofFn fun i => A i ^ (n + Pi.single k 1 : Fin l → ℕ) i).prod := by
  have hc : ∀ m : Fin l → ℕ, (↑(Finset.univ : Finset (Fin l)) : Set (Fin l)).Pairwise
      (Function.onFun Commute fun i => A i ^ m i) :=
    fun m i _ j _ _ => (hA i j).pow_pow _ _
  rw [prod_ofFn_eq_noncommProd _ (hc n), prod_ofFn_eq_noncommProd _ (hc _),
    ← Finset.mul_noncommProd_erase _ (Finset.mem_univ k) _ (hc n),
    ← Finset.mul_noncommProd_erase _ (Finset.mem_univ k) _ (hc _), ← mul_assoc]
  congr 1
  · simp [pow_succ']
  · refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
    have : i ≠ k := Finset.ne_of_mem_erase hi
    simp [Pi.single_apply, this]

end Monoid

section Poly

variable {K : Type*} [Field K] {l : ℕ}

/-- Partial derivatives of multivariate polynomials commute. -/
private lemma commute_pderiv (i j : Fin l) :
    Commute (pderiv i : Derivation K (MvPolynomial (Fin l) K) _).toLinearMap
      (pderiv j).toLinearMap := by
  refine LinearMap.ext fun p => ?_
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    change pderiv i (pderiv j (monomial u a)) = pderiv j (pderiv i (monomial u a))
    rw [pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial]
    by_cases h : i = j
    · subst h; rfl
    · have h1 : (u - Finsupp.single j 1 : Fin l →₀ ℕ) i = u i := by
        simp [Finsupp.single_apply, Ne.symm h]
      have h2 : (u - Finsupp.single i 1 : Fin l →₀ ℕ) j = u j := by
        simp [Finsupp.single_apply, h]
      rw [h1, h2, tsub_right_comm]
      congr 1
      ring
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The undivided differential operator `∏ₖ ∂^{I k}/∂ςₖ^{I k}`, in the order of the definition
of `generalizedWronskian`. -/
private noncomputable def pd (I : Fin l → ℕ) : Module.End K (MvPolynomial (Fin l) K) :=
  (List.ofFn fun k : Fin l => (pderiv k).toLinearMap ^ I k).prod

private lemma pd_zero : (pd 0 : Module.End K (MvPolynomial (Fin l) K)) = 1 := by
  simp [pd, List.ofFn_const]

private lemma pderiv_comp_pd (I : Fin l → ℕ) (k : Fin l) :
    (pderiv k : Derivation K (MvPolynomial (Fin l) K) _).toLinearMap * pd I =
      pd (I + Pi.single k 1) :=
  mul_prod_ofFn_pow (M := Module.End K (MvPolynomial (Fin l) K)) (fun k => (pderiv k).toLinearMap)
    (fun i j => commute_pderiv i j) I k

/-- The Kronecker substitution `ςₖ ↦ τ ^ (D ^ k)`. -/
private noncomputable abbrev kron (D : ℕ) :
    MvPolynomial (Fin l) K →ₐ[K] MvPolynomial (Fin 1) K :=
  aeval fun k => X 0 ^ (D ^ (k : ℕ))

/-- The chain rule for the Kronecker substitution. -/
private lemma pderiv_kron (D : ℕ) (g : MvPolynomial (Fin l) K) :
    pderiv 0 (kron D g) =
      ∑ k : Fin l,
        pderiv 0 (X 0 ^ (D ^ (k : ℕ)) : MvPolynomial (Fin 1) K) * kron D (pderiv k g) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, map_add, pderiv_mul, hp, pderiv_X, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, Ne.symm hk]) (by simp),
        Pi.single_eq_same, map_one, mul_one, kron, aeval_X]
      ring

end Poly

section Span

variable {K : Type*} [Field K] [CharZero K] {l : ℕ}

/-- The divided derivative `∂_I` is `(∏ₖ (I k)!)⁻¹ ∏ₖ ∂^{I k}/∂ςₖ^{I k}`. -/
private lemma hasseDeriv_eq_smul_pd (I : Fin l → ℕ) :
    (MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm I) :
      Module.End K (MvPolynomial (Fin l) K)) = (∏ k, ((I k).factorial : K))⁻¹ • pd I := by
  rw [MvPolynomial.hasseDeriv_eq_inv_prod_factorial_smul]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
  rfl

private lemma prod_factorial_ne_zero (I : Fin l → ℕ) : (∏ k, ((I k).factorial : K)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast Nat.factorial_ne_zero _

/-- The `K[τ]`-span of the operators `f ↦ (∂_I f)(τ, τ^D, …)` with `|I| ≤ ν`. -/
private noncomputable def opSpan (D ν : ℕ) :
    Submodule (MvPolynomial (Fin 1) K) (MvPolynomial (Fin l) K →ₗ[K] MvPolynomial (Fin 1) K) :=
  Submodule.span _ ((fun I : Fin l → ℕ => (kron D).toLinearMap ∘ₗ
    MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm I)) '' {I | ∑ k, I k ≤ ν})

private lemma opSpan_mono (D : ℕ) {ν ν' : ℕ} (h : ν ≤ ν') :
    (opSpan D ν : Submodule _ (MvPolynomial (Fin l) K →ₗ[K] MvPolynomial (Fin 1) K)) ≤
      opSpan D ν' :=
  Submodule.span_mono (Set.image_mono fun _ hI => le_trans hI h)

private lemma kron_comp_pd_mem (D : ℕ) {ν : ℕ} (J : Fin l → ℕ) (hJ : ∑ k, J k ≤ ν) :
    (kron D).toLinearMap ∘ₗ (pd J : Module.End K (MvPolynomial (Fin l) K)) ∈ opSpan D ν := by
  have : (kron D).toLinearMap ∘ₗ (pd J : Module.End K (MvPolynomial (Fin l) K)) =
      (C (∏ k, ((J k).factorial : K)) : MvPolynomial (Fin 1) K) •
        ((kron D).toLinearMap ∘ₗ MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm J)) := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, hasseDeriv_eq_smul_pd,
      AlgHom.toLinearMap_apply, map_smul]
    rw [smul_eq_C_mul (kron D _), smul_eq_mul, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ (prod_factorial_ne_zero (K := K) J), C_1, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, hJ, rfl⟩)

private lemma pderiv_comp_mem (D : ℕ) {ν : ℕ}
    {L : MvPolynomial (Fin l) K →ₗ[K] MvPolynomial (Fin 1) K} (hL : L ∈ opSpan D ν) :
    (pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ∘ₗ L ∈ opSpan D (ν + 1) := by
  induction hL using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    have : (pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ∘ₗ
        ((kron D).toLinearMap ∘ₗ MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm I)) =
        ∑ k : Fin l, (C (∏ k, ((I k).factorial : K))⁻¹ *
          pderiv 0 (X 0 ^ (D ^ (k : ℕ)) : MvPolynomial (Fin 1) K)) •
          ((kron D).toLinearMap ∘ₗ (pd (I + Pi.single k 1) :
            Module.End K (MvPolynomial (Fin l) K))) := by
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, hasseDeriv_eq_smul_pd, LinearMap.smul_apply,
        AlgHom.toLinearMap_apply, map_smul, Derivation.coeFn_coe, pderiv_kron, Finset.smul_sum,
        LinearMap.sum_apply, ← pderiv_comp_pd, Module.End.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_C_mul, smul_eq_mul, mul_assoc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (kron_comp_pd_mem D _ ?_)
    simp only [Set.mem_setOf_eq] at hI
    simpa [Finset.sum_add_distrib] using hI
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.comp_add]; exact add_mem hx hy
  | smul a x hx' hx =>
    have : (pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ∘ₗ (a • x) =
        pderiv 0 a • x +
          a • ((pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ∘ₗ x) := by
      refine LinearMap.ext fun f => ?_
      simp [pderiv_mul]
      ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (opSpan_mono D (Nat.le_succ ν) hx'))
      (Submodule.smul_mem _ _ hx)

private lemma pderiv_pow_comp_kron_mem (D ν : ℕ) :
    ((pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ^ ν) ∘ₗ
      (kron D : MvPolynomial (Fin l) K →ₐ[K] _).toLinearMap ∈ opSpan D ν := by
  induction ν with
  | zero =>
    have := kron_comp_pd_mem (K := K) (l := l) D (ν := 0) 0 (by simp)
    rw [pd_zero, Module.End.one_eq_id, LinearMap.comp_id] at this
    rwa [pow_zero, Module.End.one_eq_id, LinearMap.id_comp]
  | succ ν ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]
    exact pderiv_comp_mem D ih

private lemma kron_generalizedWronskian {s : ℕ} (D : ℕ) (I : Fin (s + 1) → Fin l → ℕ)
    (φ : Fin (s + 1) → MvPolynomial (Fin l) K) :
    kron D (generalizedWronskian I φ) =
      (Matrix.of fun ν j =>
        ((kron D).toLinearMap ∘ₗ
          MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (I ν))) (φ j)).det := by
  rw [generalizedWronskian, AlgHom.map_det]
  simp only [hasseDeriv_eq_smul_pd]
  rfl

/-- If every generalized Wronskian with `|I_μ| ≤ μ` vanishes, so does every determinant whose
`ν`-th row comes from an operator in `opSpan D ν`. -/
private lemma det_eq_zero_of_mem_opSpan {s : ℕ} (D : ℕ)
    (φ : Fin (s + 1) → MvPolynomial (Fin l) K)
    (hW : ∀ I : Fin (s + 1) → Fin l → ℕ, (∀ μ, ∑ k, I μ k ≤ (μ : ℕ)) →
      generalizedWronskian I φ = 0)
    (L : Fin (s + 1) → (MvPolynomial (Fin l) K →ₗ[K] MvPolynomial (Fin 1) K))
    (hL : ∀ ν : Fin (s + 1), L ν ∈ opSpan D (ν : ℕ)) :
    (Matrix.of fun ν j => L ν (φ j)).det = 0 := by
  classical
  choose n c g hg using fun ν => Submodule.mem_span_set'.1 (hL ν)
  choose J hJ hJg using fun ν i => (g ν i).2
  have hrow : (Matrix.of fun ν j => L ν (φ j)) =
      fun ν : Fin (s + 1) =>
        ∑ i, c ν i • fun j =>
          ((kron D).toLinearMap ∘ₗ
            MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J ν i))) (φ j) := by
    funext ν j
    rw [Matrix.of_apply, ← hg ν]
    simp [← hJg, Finset.sum_apply, LinearMap.sum_apply]
  rw [hrow]
  change (Matrix.detRowAlternating : (Fin (s + 1) → MvPolynomial (Fin 1) K)
    [⋀^Fin (s + 1)]→ₗ[MvPolynomial (Fin 1) K] _).toMultilinearMap _ = 0
  rw [MultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  have : (Matrix.detRowAlternating : (Fin (s + 1) → MvPolynomial (Fin 1) K)
      [⋀^Fin (s + 1)]→ₗ[MvPolynomial (Fin 1) K] _).toMultilinearMap
      (fun (ν : Fin (s + 1)) j =>
        ((kron D).toLinearMap ∘ₗ
          MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J ν (r ν)))) (φ j)) = 0 := by
    change (Matrix.of fun (ν : Fin (s + 1)) j =>
      ((kron D).toLinearMap ∘ₗ
        MvPolynomial.hasseDeriv (Finsupp.equivFunOnFinite.symm (J ν (r ν)))) (φ j)).det = 0
    rw [← kron_generalizedWronskian, hW _ fun μ => hJ μ (r μ), map_zero]
  rw [this, smul_zero]

/-- **The chain-rule step.** If every generalized Wronskian `Wr_I(φ)` with `|I_μ| ≤ μ` vanishes,
then so does the one-variable Wronskian of the Kronecker substitutions `φ_j(τ, τ^D, …)`. -/
private lemma generalizedWronskian_kron_eq_zero {s : ℕ} (D : ℕ)
    (φ : Fin (s + 1) → MvPolynomial (Fin l) K)
    (hW : ∀ I : Fin (s + 1) → Fin l → ℕ, (∀ μ, ∑ k, I μ k ≤ (μ : ℕ)) →
      generalizedWronskian I φ = 0) :
    generalizedWronskian (fun ν _ => (ν : ℕ)) (fun j => kron D (φ j)) = 0 := by
  rw [← det_eq_zero_of_mem_opSpan D φ hW
    (fun ν => (((ν : ℕ).factorial : K))⁻¹ •
      (((pderiv 0 : Derivation K (MvPolynomial (Fin 1) K) _).toLinearMap ^ (ν : ℕ)) ∘ₗ
        (kron D).toLinearMap))
    (fun ν => Submodule.smul_of_tower_mem _ _ (pderiv_pow_comp_kron_mem _ _)),
    generalizedWronskian]
  congr 1
  ext1 ν j
  simp [List.ofFn_succ]

end Span

section Kronecker

variable {K : Type*} [Field K] {l : ℕ}

/-- Base-`D` expansions with digits `< D` are unique. -/
private lemma eq_of_sum_mul_pow_eq {D : ℕ} :
    ∀ {l : ℕ} (a b : Fin l → ℕ), (∀ i, a i < D) → (∀ i, b i < D) →
      ∑ i, a i * D ^ (i : ℕ) = ∑ i, b i * D ^ (i : ℕ) → a = b
  | 0, a, b, _, _, _ => funext fun i => i.elim0
  | l + 1, a, b, ha, hb, h => by
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      ← mul_assoc, ← Finset.sum_mul] at h
    have h0 : a 0 = b 0 := by
      have := congrArg (· % D) h
      simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (hb 0)]
        using this
    rw [h0, Nat.add_left_cancel_iff] at h
    have ht := eq_of_sum_mul_pow_eq (fun i => a i.succ) (fun i => b i.succ) (fun i => ha _)
      (fun i => hb _) (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt (ha 0)) h)
    funext i
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun ht i

private lemma kron_monomial (D : ℕ) (u : Fin l →₀ ℕ) (a : K) :
    kron D (monomial u a) = monomial (Finsupp.single 0 (∑ i, u i * D ^ (i : ℕ))) a := by
  rw [kron, aeval_monomial, algebraMap_eq, Finsupp.prod]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, X_pow_eq_monomial, C_mul_monomial, mul_one]
  congr 2
  rw [Finset.sum_subset u.support.subset_univ fun i _ hi => by
    simp [Finsupp.notMem_support_iff.1 hi]]
  exact congrArg (Finsupp.single 0) (Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _)

private lemma coeff_kron (m : ℕ) {p : MvPolynomial (Fin l) K}
    (hp : p ∈ restrictDegree (Fin l) K m)
    (n : Fin l →₀ ℕ) (hn : ∀ i, n i ≤ m) :
    (kron (m + 1) p).coeff (Finsupp.single 0 (∑ i, n i * (m + 1) ^ (i : ℕ))) = p.coeff n := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [kron_monomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro u hu hne
    rw [if_neg]
    intro heq
    apply hne
    have hu' := (mem_restrictDegree _ p m).1 hp u hu
    exact DFunLike.coe_injective (eq_of_sum_mul_pow_eq (D := m + 1) _ _
      (fun i => Nat.lt_succ_of_le (hu' i)) (fun i => Nat.lt_succ_of_le (hn i))
      (Finsupp.single_injective _ heq))
  · intro hn'
    simp [notMem_support_iff.1 hn']

private lemma eq_zero_of_kron_eq_zero (m : ℕ) {p : MvPolynomial (Fin l) K}
    (hp : p ∈ restrictDegree (Fin l) K m) (h : kron (m + 1) p = 0) : p = 0 := by
  ext n
  by_cases hn : ∀ i, n i ≤ m
  · simp only [← coeff_kron m hp n hn, h, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
  · simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact hn ((mem_restrictDegree _ p m).1 hp n (mem_support_iff.2 hne))

/-- A Kronecker substitution with base exceeding every partial degree keeps a linearly
independent family linearly independent. -/
private lemma exists_linearIndependent_kron {ι : Type*} [Fintype ι]
    {φ : ι → MvPolynomial (Fin l) K} (hφ : LinearIndependent K φ) :
    ∃ D, LinearIndependent K fun j => kron D (φ j) := by
  set m := Finset.univ.sup fun j => (φ j).totalDegree
  have hmem : ∀ j, φ j ∈ restrictDegree (Fin l) K m := fun j =>
    (mem_restrictDegree _ _ _).2 fun u hu i =>
      ((Finsupp.le_degree i u).trans (le_totalDegree hu)).trans
        (Finset.le_sup (f := fun j => (φ j).totalDegree) (Finset.mem_univ j))
  refine ⟨m + 1, hφ.map (f := (kron (m + 1)).toLinearMap)
    (Submodule.disjoint_def.2 fun x hx hker => ?_)⟩
  exact eq_zero_of_kron_eq_zero m (Submodule.span_le.2 (Set.range_subset_iff.2 hmem) hx) hker

end Kronecker

/-- If `φ₀, …, φₛ ∈ K[ς₁, …, ςₗ]` are linearly independent over a field `K` of characteristic `0`,
then some generalized Wronskian `Wr_{I₀,…,Iₛ}(φ₀, …, φₛ)` with `|I_μ| ≤ μ` for every `μ` is
nonzero. -/
@[faltings "lem_bvr_generalized_wronskian"]
public theorem exists_generalizedWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {l s : ℕ} {φ : Fin (s + 1) → MvPolynomial (Fin l) K} (hφ : LinearIndependent K φ) :
    ∃ I : Fin (s + 1) → Fin l → ℕ, (∀ μ, ∑ k, I μ k ≤ (μ : ℕ)) ∧
      generalizedWronskian I φ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨D, hD⟩ := exists_linearIndependent_kron hφ
  exact (generalizedWronskian_ne_zero_iff_linearIndependent _).2 hD
    (generalizedWronskian_kron_eq_zero D φ hcon)

end Faltings
