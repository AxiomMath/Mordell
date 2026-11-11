module
public import Mordell.Roth.Wronskian.Basic

/-!
# Non-vanishing of the one-variable Wronskian

Let `K` be a field of characteristic `0` and `ψ₀, …, ψₛ ∈ K[τ]`. The Wronskian
`Wr(ψ₀, …, ψₛ) = det (∂_ν ψ_j)_{ν, j}`, with `∂_ν = (1/ν!) d^ν/dτ^ν`, is nonzero if and only if
`ψ₀, …, ψₛ` are linearly independent over `K`.

## Main results

* `Faltings.generalizedWronskian_ne_zero_iff_linearIndependent`: the one-variable Wronskian
  `Faltings.generalizedWronskian (fun ν _ => ν) ψ` is nonzero iff `ψ` is linearly independent.
* `Faltings.uniqueAlgEquiv_divided_pderiv`: under `MvPolynomial (Fin 1) K ≃ K[X]`, the divided
  derivative `(ν!)⁻¹ • (pderiv 0) ^ ν` is the Hasse derivative `Polynomial.hasseDeriv ν`.

## Implementation notes

Polynomials in one variable are `MvPolynomial (Fin 1) K`, the ring in which
`Faltings.generalizedWronskian` is defined; the classical Wronskian is its instance at the
multi-indices `I ν = ν`.

The proof transports the problem to `K[X]` along `MvPolynomial.uniqueAlgEquiv`, where the
divided derivative `∂_ν` becomes the Hasse derivative `Polynomial.hasseDeriv ν`. A linear
relation among the `ψ_j` is a relation among the columns. Conversely, in place of Gaussian
elimination, a dimension count shows that the span of independent `ψ_j` contains `s + 1` nonzero
polynomials `φ_j` of distinct degrees `e_j`; the Wronskian of the `φ_j` is a multiple of that of
the `ψ_j`, and after multiplying row `ν` by `X ^ ν` its coefficient in degree `∑ e_j` is
`(∏ lc φ_j) · det (binom (e_j) ν)`, a nonzero multiple of a Vandermonde determinant.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
-/

open Polynomial Matrix

namespace Faltings

section Poly

variable {R : Type*} [CommRing R]

/-- The coefficient of a product in the degree given by the sum of degree bounds. -/
private lemma coeff_prod_sum_of_natDegree_le {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (n : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    exact (natDegree_prod_le s f).trans
      (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If the entries of column `j` of `B` have degree at most `e j`, the coefficient of `det B`
in degree `∑ e j` is the determinant of the matrix of top coefficients. -/
private lemma coeff_det_of_natDegree_le {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n R[X]) (e : n → ℕ) (h : ∀ i j, (B i j).natDegree ≤ e j) :
    B.det.coeff (∑ j, e j) = (Matrix.of fun i j => (B i j).coeff (e j)).det := by
  rw [det_apply', det_apply', finsetSum_coeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_intCast_mul, coeff_prod_sum_of_natDegree_le _ _ _ fun i _ => h _ _]
  rfl

/-- `X ^ ν * hasseDeriv ν` multiplies the coefficient in degree `m` by `m.choose ν`. -/
private lemma coeff_X_pow_mul_hasseDeriv (ν m : ℕ) (f : R[X]) :
    (X ^ ν * hasseDeriv ν f).coeff m = m.choose ν * f.coeff m := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [hasseDeriv_coeff, Nat.sub_add_cancel h]
  · rw [Nat.choose_eq_zero_of_lt (not_le.1 h), Nat.cast_zero, zero_mul]

end Poly

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The matrix `(binom (e_j) ν)_{ν, j}` is invertible for distinct `e_j`. -/
private lemma det_choose_ne_zero {n : ℕ} (e : Fin n → ℕ) (he : Function.Injective e) :
    (Matrix.of fun (ν j : Fin n) => ((e j).choose ν : K)).det ≠ 0 := by
  rw [← det_transpose]
  have h : (Matrix.of fun (ν j : Fin n) => ((e j).choose ν : K))ᵀ =
      Matrix.of fun (i ν : Fin n) => ((ν : ℕ).factorial : K)⁻¹ *
        (descPochhammer K ν).eval (e i : K) := by
    ext i ν
    rw [transpose_apply, of_apply, of_apply, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, inv_mul_cancel_left₀]
    exact_mod_cast (Nat.factorial_ne_zero _)
  have hrow := det_mul_row (fun ν : Fin n => ((ν : ℕ).factorial : K)⁻¹)
    (Matrix.of fun (i ν : Fin n) => (descPochhammer K ν).eval (e i : K))
  simp only [of_apply] at hrow
  rw [h, hrow, ← det_eval_matrixOfPolynomials_eq_det_vandermonde _ _
    (fun i => descPochhammer_natDegree K i) (fun i => monic_descPochhammer K i)]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_) ?_
  · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
  · exact det_vandermonde_ne_zero_iff.2 (Nat.cast_injective.comp he)

/-- The Wronskian matrix `(∂_ν f_j)_{ν, j}` in `K[X]`, with `∂_ν` the Hasse derivative. -/
private noncomputable abbrev wrMatrix {s : ℕ} (f : Fin (s + 1) → K[X]) :
    Matrix (Fin (s + 1)) (Fin (s + 1)) K[X] :=
  Matrix.of fun ν j => hasseDeriv ν (f j)

/-- The Wronskian of nonzero polynomials of distinct degrees is nonzero. -/
private lemma det_wrMatrix_ne_zero_of_injective {s : ℕ} (φ : Fin (s + 1) → K[X])
    (hφ : ∀ j, φ j ≠ 0) (hinj : Function.Injective fun j => (φ j).natDegree) :
    (wrMatrix φ).det ≠ 0 := by
  intro h0
  set B : Matrix (Fin (s + 1)) (Fin (s + 1)) K[X] :=
    Matrix.of fun ν j => (X : K[X]) ^ (ν : ℕ) * wrMatrix φ ν j with hB
  have hdet : B.det = 0 := by rw [hB, det_mul_column, h0, mul_zero]
  have hcoeff := coeff_det_of_natDegree_le B (fun j => (φ j).natDegree) fun ν j => by
    refine natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    simp only [hB, of_apply, coeff_X_pow_mul_hasseDeriv, coeff_eq_zero_of_natDegree_lt hm,
      mul_zero]
  rw [hdet, coeff_zero] at hcoeff
  have hM : (Matrix.of fun ν j => (B ν j).coeff (φ j).natDegree) =
      Matrix.of fun (ν j : Fin (s + 1)) =>
        (φ j).leadingCoeff * (((φ j).natDegree).choose (ν : ℕ) : K) := by
    ext ν j
    simp only [hB, of_apply, coeff_X_pow_mul_hasseDeriv, leadingCoeff, mul_comm]
  have hrow := det_mul_row (fun j => (φ j).leadingCoeff)
    (Matrix.of fun (ν j : Fin (s + 1)) => (((φ j).natDegree).choose (ν : ℕ) : K))
  simp only [of_apply] at hrow
  rw [hM, hrow] at hcoeff
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => leadingCoeff_ne_zero.2 (hφ j))
    (det_choose_ne_zero _ hinj) hcoeff.symm

omit [CharZero K] in
/-- The Wronskian of a family in the span of `ψ` is a multiple of that of `ψ`. -/
private lemma det_wrMatrix_dvd {s : ℕ} (ψ φ : Fin (s + 1) → K[X])
    (hφ : ∀ j, φ j ∈ Submodule.span K (Set.range ψ)) :
    (wrMatrix ψ).det ∣ (wrMatrix φ).det := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hφ j)
  have : wrMatrix φ = wrMatrix ψ * Matrix.of fun i j => C (c j i) := by
    ext ν j
    simp only [of_apply, mul_apply, ← hc j, map_sum, map_smul]
    simp only [smul_eq_C_mul, mul_comm]
  rw [this, det_mul]
  exact dvd_mul_right _ _

omit [CharZero K] in
/-- The span of `s + 1` independent polynomials contains `s + 1` nonzero polynomials of distinct
degrees. -/
private lemma exists_injective_natDegree {s : ℕ} (ψ : Fin (s + 1) → K[X])
    (hψ : LinearIndependent K ψ) :
    ∃ φ : Fin (s + 1) → K[X], (∀ j, φ j ∈ Submodule.span K (Set.range ψ)) ∧
      (∀ j, φ j ≠ 0) ∧ Function.Injective fun j => (φ j).natDegree := by
  classical
  set V := Submodule.span K (Set.range ψ)
  set N := Finset.univ.sup fun i => (ψ i).natDegree
  have hV : V ≤ degreeLE K N := Submodule.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    exact mem_degreeLE.2 <| (degree_le_natDegree).trans
      (WithBot.coe_le_coe.2 (Finset.le_sup (f := fun i => (ψ i).natDegree) (Finset.mem_univ i)))
  set T := (Finset.range (N + 1)).filter fun d => ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = d
  let L : V →ₗ[K] (T → K) := LinearMap.pi fun d => (lcoeff K (d : ℕ)).comp V.subtype
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    by_contra hne
    have hne' : (f : K[X]) ≠ 0 := by simpa using hne
    have hmem : (f : K[X]).natDegree ∈ T := by
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le ?_), f, f.2, hne', rfl⟩
      exact natDegree_le_iff_degree_le.2 (mem_degreeLE.1 (hV f.2))
    have := congr_fun (LinearMap.mem_ker.1 hf) ⟨_, hmem⟩
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      lcoeff_apply, Pi.zero_apply] at this
    exact leadingCoeff_ne_zero.2 hne' this
  have hcard : s + 1 ≤ Fintype.card T := by
    have := LinearMap.finrank_le_finrank_of_injective hL
    rwa [finrank_span_eq_card hψ, Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
  let g : Fin (s + 1) → T := fun j => T.equivFin.symm (Fin.castLE (by simpa using hcard) j)
  have hg : Function.Injective g := fun a b hab =>
    Fin.castLE_injective _ (T.equivFin.symm.injective hab)
  have hT : ∀ j, ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = g j := fun j => (Finset.mem_filter.1 (g j).2).2
  choose φ hφV hφ0 hφd using hT
  refine ⟨φ, hφV, hφ0, fun a b hab => hg (Subtype.ext ?_)⟩
  simpa [hφd] using hab

/-- The polynomial form of the theorem. -/
private lemma det_wrMatrix_ne_zero_iff {s : ℕ} (ψ : Fin (s + 1) → K[X]) :
    (wrMatrix ψ).det ≠ 0 ↔ LinearIndependent K ψ := by
  refine ⟨fun h => ?_, fun hψ h0 => ?_⟩
  · by_contra hli
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    refine h (exists_mulVec_eq_zero_iff.1 ⟨fun i => C (g i), fun h' => hi ?_, ?_⟩)
    · simpa using congr_fun h' i
    · ext1 ν
      have := congr_arg (hasseDeriv (ν : ℕ)) hg
      simp only [map_sum, map_smul, map_zero] at this
      simpa [mulVec, dotProduct, smul_eq_C_mul, mul_comm] using this
  · obtain ⟨φ, hφV, hφ0, hinj⟩ := exists_injective_natDegree ψ hψ
    exact det_wrMatrix_ne_zero_of_injective φ hφ0 hinj
      (zero_dvd_iff.1 (h0 ▸ det_wrMatrix_dvd ψ φ hφV))

omit [CharZero K] in
/-- Under `MvPolynomial (Fin 1) K ≃ K[X]`, the partial derivative is the derivative. -/
public lemma uniqueAlgEquiv_pderiv (p : MvPolynomial (Fin 1) K) :
    MvPolynomial.uniqueAlgEquiv K (Fin 1) (MvPolynomial.pderiv 0 p) =
      derivative (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    obtain rfl := Subsingleton.elim n 0
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp]
    simp [derivative_mul, mul_comm]

/-- Under `MvPolynomial (Fin 1) K ≃ K[X]`, the divided derivative `(ν!)⁻¹ • (pderiv 0) ^ ν` is
the Hasse derivative `hasseDeriv ν`. -/
public lemma uniqueAlgEquiv_divided_pderiv (ν : ℕ) (p : MvPolynomial (Fin 1) K) :
    MvPolynomial.uniqueAlgEquiv K (Fin 1) (((ν.factorial : K))⁻¹ •
      ((MvPolynomial.pderiv (0 : Fin 1)).toLinearMap ^ ν) p) =
      hasseDeriv ν (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) := by
  have hiter : ∀ (n : ℕ) p, MvPolynomial.uniqueAlgEquiv K (Fin 1)
      (((MvPolynomial.pderiv (0 : Fin 1)).toLinearMap ^ n) p) =
      derivative^[n] (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro p
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', ← ih]
      exact uniqueAlgEquiv_pderiv _
  rw [map_smul, hiter, ← factorial_smul_hasseDeriv, LinearMap.smul_apply,
    ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ν), one_smul]

/-- The one-variable `generalizedWronskian` is the Wronskian `wrMatrix` in `K[X]`. -/
private lemma uniqueAlgEquiv_generalizedWronskian {s : ℕ}
    (ψ : Fin (s + 1) → MvPolynomial (Fin 1) K) :
    MvPolynomial.uniqueAlgEquiv K (Fin 1) (generalizedWronskian (fun ν _ => (ν : ℕ)) ψ) =
      (wrMatrix fun j => MvPolynomial.uniqueAlgEquiv K (Fin 1) (ψ j)).det := by
  refine (AlgEquiv.map_det _ _).trans (congrArg det (Matrix.ext fun ν j => ?_))
  simpa [List.ofFn_succ] using uniqueAlgEquiv_divided_pderiv ν (ψ j)

end Field

/-- The one-variable Wronskian `Wr(ψ₀, …, ψₛ) = det (∂_ν ψ_j)` of polynomials over a field of
characteristic `0` is nonzero if and only if `ψ₀, …, ψₛ` are linearly independent over `K`. -/
@[faltings "lem_bvr_wronskian_one_variable"]
public theorem generalizedWronskian_ne_zero_iff_linearIndependent {K : Type*} [Field K]
    [CharZero K] {s : ℕ} (ψ : Fin (s + 1) → MvPolynomial (Fin 1) K) :
    generalizedWronskian (fun ν _ => (ν : ℕ)) ψ ≠ 0 ↔ LinearIndependent K ψ := by
  set e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  rw [← map_ne_zero_iff e e.injective, uniqueAlgEquiv_generalizedWronskian,
    det_wrMatrix_ne_zero_iff]
  exact LinearMap.linearIndependent_iff e.toLinearMap (LinearMap.ker_eq_bot.2 e.injective)

end Faltings
