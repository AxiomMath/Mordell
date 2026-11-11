module
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Norm.FormNormHeight
public import Mordell.Height.Polynomial.Gelfond

/-!
# The height of `T_i`

Let `k` be a number field (more generally an algebraic extension of `ℚ`), `K = k(C)` and
`L = k(C × C)` with the two projections `pr₁^*, pr₂^* : K → L`, `x = (x_ν)` the coordinates of
`C ⊆ ℙⁿ`, `x_j` the distinguished coordinate, `ξ_ν = x_ν / x_j` and `ξ'_ν = pr₂^* ξ_ν`. For a
non-zero section of `𝒪(V)` with representative `F = (F_i)` of bidegree `(δ₁, δ₂)` and with
coefficients in `k`, and reduced representations `(U_i, V_i)` in `R = k[ξ_a, ξ'_b]` of the norms
of the `η_i`, Bombieri's polynomial `T_i = G_0 / V_i^d` divides `G_0`. Bombieri's bound says that
if `h(F) ≤ c₁₀ (d₁ + d₂) / γ + o(d₁ + d₂)`, then for `i ≠ 0`
`h(T_i) ≤ c₁₅ N² (d₁ + d₂) / γ + 2 N (d₁ + d₂ + 2 s d) + o(d₁ + d₂)`, with the constant `c₁₅` of
`Faltings.BombieriRoth.exists_logHeight_formNorm_le`.

## Main results

* `Faltings.BombieriRoth.exists_mvPolynomialHeight_polynomialT_le`: the height bound for `T_i`.

## Implementation notes

The setting is that of `Faltings.BombieriRoth.exists_logHeight_formNorm_le`: the statement is
made in the function fields `K`, `L` over `k` with `pr₁ pr₂ : K →ₐ[k] L`, and the geometry of
`C × C` enters through the field-theoretic facts the bound uses (integrality of every `ξ_ν` over
`k[ξ_a]` and over `k[ξ_b]`, algebraic independence of `ξ_a, ξ'_b`, `[L : k(ξ_a, ξ'_b)] ≤ N²`).
The ring `R` is `k[X₀, X₁] = MvPolynomial (Fin 2) k`, mapped to `k⟮ξ_a, ξ'_b⟯` by
`X₀ ↦ ξ_a`, `X₁ ↦ ξ'_b`. "`h(T_i)`" is the height `Faltings.mvPolynomialHeight` of a polynomial
`T ∈ k[X₀, X₁]` with `T(ξ_a, ξ'_b) = T_i`, unique by algebraic independence.

Each `o(d₁ + d₂)` is a function `ℕ → ℝ` of `d₁ + d₂` that is `o(n)` as `n → ∞`, and the bound
is uniform: for each error term `ε` of the hypothesis there is one error term `ε'` of the
conclusion serving all `a, b, γ, d₁, d₂, d`, all representatives and all `i`.

The proof follows Bombieri. With `t = ξ_a`, `u = ξ'_b` and `G_0 = T_i V_i^d` in `k[t, u]`,
Gelfond's inequality in Bombieri's form
(`Faltings.sum_mvPolynomialHeight_le_mvPolynomialHeight_prod_add`) bounds
`h(T_i)` by `h(G_0)` plus twice the sum of the partial degrees of `G_0`, and
`Faltings.BombieriRoth.exists_logHeight_formNorm_le` bounds `h(G_0)`. The partial degrees of `G_0`
are bounded by integrality: if every `ξ_ν` is integral over `k[ξ_a]`, then for some `q` every
`ξ_ν ξ_a^{-q}` is integral over `k[ξ_a⁻¹]`, so `F_0(ξ, ξ') t^{-q δ₁}` is integral over
`k[t⁻¹, u]` and the norm `G_0` has degree at most `[L : k(t, u)] q δ₁ ≤ N² q δ₁` in `t`. This
is weaker than Bombieri's `deg G_0 ≤ N² δ₁`, which is a statement about the curve; the extra
factor `q` is absorbed into the constant in front of `N² (d₁ + d₂) / γ`.

## References

* [Bombieri1990], Sec. 9, p. 633.
-/

namespace Faltings.BombieriRoth

open _root_.MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

/-- Raising the power of `w⁻¹` preserves integrality over `k[w⁻¹]`. -/
private theorem isIntegral_mul_inv_pow_mono {k K : Type*} [Field k] [Field K] [Algebra k K]
    {w y : K} {q q' : ℕ} (hqq : q ≤ q')
    (h : IsIntegral (Algebra.adjoin k {w⁻¹}) (y * w⁻¹ ^ q)) :
    IsIntegral (Algebra.adjoin k {w⁻¹}) (y * w⁻¹ ^ q') := by
  have hw : IsIntegral (Algebra.adjoin k {w⁻¹}) w⁻¹ :=
    isIntegral_algebraMap (x := (⟨w⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin k {w⁻¹}))
  have : y * w⁻¹ ^ q' = y * w⁻¹ ^ q * w⁻¹ ^ (q' - q) := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hqq]
  rw [this]
  exact h.mul (hw.pow _)

/-- **Integrality at `w = ∞`.** If `y` is integral over `k[w]` with `w ≠ 0`, then
`y w^{-q}` is integral over `k[w⁻¹]` for some `q`. -/
private theorem exists_isIntegral_mul_inv_pow {k K : Type*} [Field k] [Field K] [Algebra k K]
    {w : K} (hw : w ≠ 0) {y : K} (hy : IsIntegral (Algebra.adjoin k {w}) y) :
    ∃ q : ℕ, IsIntegral (Algebra.adjoin k {w⁻¹}) (y * w⁻¹ ^ q) := by
  set B := Algebra.adjoin k ({w⁻¹} : Set K)
  have hwi : IsIntegral B w⁻¹ :=
    isIntegral_algebraMap (x := (⟨w⁻¹, Algebra.subset_adjoin rfl⟩ : B))
  have hS : ∀ z ∈ Algebra.adjoin k ({w} : Set K), ∃ q : ℕ, IsIntegral B (z * w⁻¹ ^ q) := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.mp hz]
      exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hw]; exact isIntegral_one⟩
    | algebraMap r =>
      refine ⟨0, ?_⟩
      rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply k B K]
      exact isIntegral_algebraMap
    | add z z' _ _ hz hz' =>
      obtain ⟨q, hq⟩ := hz
      obtain ⟨q', hq'⟩ := hz'
      refine ⟨q + q', ?_⟩
      have : (z + z') * w⁻¹ ^ (q + q') = z * w⁻¹ ^ q * w⁻¹ ^ q' + z' * w⁻¹ ^ q' * w⁻¹ ^ q := by
        ring
      rw [this]
      exact (hq.mul (hwi.pow _)).add (hq'.mul (hwi.pow _))
    | mul z z' _ _ hz hz' =>
      obtain ⟨q, hq⟩ := hz
      obtain ⟨q', hq'⟩ := hz'
      refine ⟨q + q', ?_⟩
      have : z * z' * w⁻¹ ^ (q + q') = z * w⁻¹ ^ q * (z' * w⁻¹ ^ q') := by ring
      rw [this]
      exact hq.mul hq'
  obtain ⟨p, hpm, hpy⟩ := hy
  set A := Algebra.adjoin k ({w} : Set K)
  set n := p.natDegree
  choose qf hqf using fun i : ℕ => hS (p.coeff i : K) (p.coeff i).2
  set Q := ∑ i ∈ Finset.range n, qf i
  refine ⟨Q, ?_⟩
  set p' := (p.map (algebraMap A K)).scaleRoots (w⁻¹ ^ Q)
  have hmap : (p.map (algebraMap A K)).Monic := hpm.map _
  have hdeg : (p.map (algebraMap A K)).natDegree = n := hpm.natDegree_map _
  have hn : n ≠ 0 := by
    intro h0
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hpm h0
    rw [hp1, Polynomial.eval₂_one] at hpy
    exact one_ne_zero hpy
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := p')
    ((Polynomial.monic_scaleRoots_iff _).mpr hmap) ?_ ?_ ?_
  · rwa [Polynomial.natDegree_scaleRoots, hdeg]
  · have : p'.eval (w⁻¹ ^ Q * y) = 0 := by
      rw [Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hpy, mul_zero]
    rw [mul_comm, this]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_scaleRoots, hdeg, Polynomial.coeff_map]
    rcases lt_trichotomy i n with hi | hi | hi
    · have hle : qf i ≤ Q * (n - i) :=
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)).trans
          (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hi))
      rw [← pow_mul]
      exact isIntegral_mul_inv_pow_mono hle (hqf i)
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one, hpm.coeff_natDegree, map_one]
      exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
      exact isIntegral_zero

/-- Integrality over `k[w]` is carried by a `k`-algebra map `f` to integrality over any
`k`-subalgebra containing `f(w)`. -/
private theorem isIntegral_map_of_mem {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (f : K →ₐ[k] L) {w : K} {T : Subalgebra k L}
    (hw : f w ∈ T) {y : K} (hy : IsIntegral (Algebra.adjoin k {w}) y) :
    IsIntegral T (f y) := by
  have hle : Algebra.adjoin k {w} ≤ T.comap f := Algebra.adjoin_le (Set.singleton_subset_iff.2 hw)
  let φ : Algebra.adjoin k {w} →ₐ[k] T :=
    (f.comp (Algebra.adjoin k {w}).val).codRestrict T fun z => hle z.2
  exact hy.map_of_comp_eq φ.toRingHom f.toRingHom (RingHom.ext fun _ => rfl)

/-- Replacing the first member of an algebraically independent pair by its inverse keeps it
algebraically independent. -/
private theorem algebraicIndependent_inv_cons {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t u : L} (h : AlgebraicIndependent k ![t, u]) : AlgebraicIndependent k ![t⁻¹, u] := by
  have e : ∀ v : L, ![v, u] = (fun o : Option (Fin 1) => o.elim v ![u]) ∘ finSuccEquiv 1 := by
    intro v; funext i; fin_cases i <;> rfl
  rw [e, algebraicIndependent_equiv] at h ⊢
  obtain ⟨hu, ht⟩ := AlgebraicIndependent.option_iff.mp h
  exact AlgebraicIndependent.option_iff.mpr ⟨hu, fun ha => ht (IsAlgebraic.inv_iff.mp ha)⟩

/-- Algebraic independence of a pair does not depend on the order. -/
private theorem algebraicIndependent_swap {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t u : L} (h : AlgebraicIndependent k ![t, u]) : AlgebraicIndependent k ![u, t] := by
  have : ![u, t] = ![t, u] ∘ Equiv.swap (0 : Fin 2) 1 := by
    funext i; fin_cases i <;> rfl
  rwa [this, algebraicIndependent_equiv]

/-- An affine evaluation of a form of bidegree `δ` is the value of the form at the affine
co-ordinates `ξ_ν = x_ν / x_j`, `ξ'_ν`. -/
private theorem affineEvaluation_eq_aeval {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ) :
    Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j δ F =
      aeval (Sum.elim (fun ν => pr₁ (x ν / x j)) (fun ν => pr₂ (x ν / x j)))
        (F : MvPolynomial (ι ⊕ ι) k) := by
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
  have h := Faltings.BombieriRoth.aeval_sumElim_mul_of_isWeightedHomogeneous (L := L) hF
    (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)) (pr₁ (x j))⁻¹ (pr₂ (x j))⁻¹
  have e₁ : (fun ν => pr₁ (x ν / x j)) = fun ν => (pr₁ (x j))⁻¹ * pr₁ (x ν) := by
    funext ν; rw [map_div₀, div_eq_inv_mul]
  have e₂ : (fun ν => pr₂ (x ν / x j)) = fun ν => (pr₂ (x j))⁻¹ * pr₂ (x ν) := by
    funext ν; rw [map_div₀, div_eq_inv_mul]
  rw [e₁, e₂, h]
  change aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) (F : MvPolynomial (ι ⊕ ι) k) /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2) = _
  rw [div_eq_inv_mul, mul_inv, inv_pow, inv_pow]

/-- Scaling the first set of affine co-ordinates by `c` multiplies the value of a form of
bidegree `δ` by `c ^ δ.1`. -/
private theorem aeval_mul_left_eq {k L ι : Type*} [Field k] [Field L] [Algebra k L] {δ : ℕ × ℕ}
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (α β : ι → L) (c : L) :
    aeval (Sum.elim (fun ν => α ν * c) β) (F : MvPolynomial (ι ⊕ ι) k) =
      aeval (Sum.elim α β) (F : MvPolynomial (ι ⊕ ι) k) * c ^ δ.1 := by
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
  have h := Faltings.BombieriRoth.aeval_sumElim_mul_of_isWeightedHomogeneous (L := L) hF α β c 1
  simp only [one_mul, one_pow, mul_one] at h
  simp_rw [mul_comm (α _) c]
  rw [h, mul_comm]

/-- Scaling the second set of affine co-ordinates by `c` multiplies the value of a form of
bidegree `δ` by `c ^ δ.2`. -/
private theorem aeval_mul_right_eq {k L ι : Type*} [Field k] [Field L] [Algebra k L]
    {δ : ℕ × ℕ}
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (α β : ι → L) (c : L) :
    aeval (Sum.elim α (fun ν => β ν * c)) (F : MvPolynomial (ι ⊕ ι) k) =
      aeval (Sum.elim α β) (F : MvPolynomial (ι ⊕ ι) k) * c ^ δ.2 := by
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
  have h := Faltings.BombieriRoth.aeval_sumElim_mul_of_isWeightedHomogeneous (L := L) hF α β 1 c
  simp only [one_mul, one_pow] at h
  simp_rw [mul_comm (β _) c]
  rw [h, mul_comm]

/-- An evaluation `Sum.elim α β` with every coordinate integral over `S` is integral. -/
private theorem isIntegral_aeval_sumElim {k L ι : Type*} [Field k] [Field L] [Algebra k L]
    (S : Subalgebra k L) {α β : ι → L} (hα : ∀ ν, IsIntegral S (α ν))
    (hβ : ∀ ν, IsIntegral S (β ν)) (F : MvPolynomial (ι ⊕ ι) k) :
    IsIntegral S (aeval (Sum.elim α β) F) :=
  isIntegral_aeval (A := S) (fun i => by cases i with | inl ν => exact hα ν | inr ν => exact hβ ν) F

/-- **Gelfond's inequality for one factor.** For non-zero `T, W` in two variables, the height of
`T` is at most the height of `T W` plus twice the sum of the partial degrees of `T W`. -/
private theorem mvPolynomialHeight_le_mul_add {k : Type*} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {T W : MvPolynomial (Fin 2) k} (hT : T ≠ 0) (hW : W ≠ 0) :
    Faltings.mvPolynomialHeight T hT ≤ Faltings.mvPolynomialHeight (T * W) (mul_ne_zero hT hW) +
      2 * (((T * W).degreeOf 0 + (T * W).degreeOf 1 : ℕ) : ℝ) := by
  have hne : ∀ l, (![T, W] : Fin 2 → MvPolynomial (Fin 2) k) l ≠ 0 := by
    intro l; fin_cases l
    exacts [hT, hW]
  have hgel := Faltings.sum_mvPolynomialHeight_le_mvPolynomialHeight_prod_add ![T, W] hne
    ![T.degreeOf 0 + T.degreeOf 1, W.degreeOf 0 + W.degreeOf 1]
    (by intro l μ; fin_cases l <;> fin_cases μ <;> simp)
  rw [Fin.sum_univ_two, mvPolynomialHeight_congr (P := ∏ l, ![T, W] l)
    (by simp [Fin.prod_univ_two]) _ (mul_ne_zero hT hW)] at hgel
  have hT' : Faltings.mvPolynomialHeight (![T, W] 0) (hne 0) = Faltings.mvPolynomialHeight T hT :=
    rfl
  have hW' : Faltings.mvPolynomialHeight (![T, W] 1) (hne 1) = Faltings.mvPolynomialHeight W hW :=
    rfl
  rw [hT', hW'] at hgel
  simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hgel
  rw [degreeOf_mul_eq hT hW, degreeOf_mul_eq hT hW]
  push_cast at hgel ⊢
  linarith [mvPolynomialHeight_nonneg W hW]

/-- **The degree term.** Under the standing inequalities on the parameters, a degree bounded by
`N² q (δ₁ + δ₂)` contributes at most `2 q (1 + 2s) N² (d₁ + d₂) / γ`. -/
private theorem two_mul_le_of_le_mul_add {N s g q d₁ d₂ d δ₁ δ₂ D : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hδ₁ : N * δ₁ = d₁ + s * d) (hδ₂ : N * δ₂ = d₂ + s * d)
    (hgd : g * d ^ 2 < d₁ * d₂) (hgd' : d₁ * d₂ < g ^ 2 * d ^ 2)
    (hγd : γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - g * d ^ 2) (hd₂₁ : d₂ ≤ d₁)
    (hD : D ≤ N ^ 2 * q * (δ₁ + δ₂)) :
    2 * (D : ℝ) ≤ 2 * q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) / γ := by
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hδ₁; omega
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hgd'
  have hdd : d ≤ d₁ := by
    by_contra! hlt
    have : d₁ * d₂ < g * d ^ 2 := calc
      d₁ * d₂ ≤ d₁ * d₁ := Nat.mul_le_mul_left _ hd₂₁
      _ < d * d := Nat.mul_lt_mul'' hlt hlt
      _ ≤ g * d ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ hg
    omega
  have hγ1 : γ ≤ 1 := by
    have hpos : (0 : ℝ) < d₁ * d₂ := by positivity
    nlinarith [(by positivity : (0 : ℝ) ≤ g * d ^ 2)]
  have hsum : D ≤ q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) := calc
    D ≤ N ^ 2 * q * (δ₁ + δ₂) := hD
    _ = N * q * (d₁ + d₂ + 2 * s * d) := by
      rw [show N ^ 2 * q * (δ₁ + δ₂) = N * q * (N * δ₁ + N * δ₂) by ring, hδ₁, hδ₂]; ring
    _ ≤ N * q * ((1 + 2 * s) * (d₁ + d₂)) :=
      Nat.mul_le_mul_left _ (by nlinarith [Nat.mul_le_mul_left (2 * s) (by omega : d ≤ d₁ + d₂)])
    _ = q * (1 + 2 * s) * (d₁ + d₂) * N := by ring
    _ ≤ q * (1 + 2 * s) * (d₁ + d₂) * N * N := Nat.le_mul_of_pos_right _ hN
    _ = q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) := by ring
  rw [le_div_iff₀ hγ]
  have hsumR : (D : ℝ) ≤ q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) := by exact_mod_cast hsum
  have : (0 : ℝ) ≤ q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) := by positivity
  nlinarith

/-- **The height of `T_i`** (Bombieri). In the setting of
`Faltings.BombieriRoth.exists_logHeight_formNorm_le`, let `R = k[X₀, X₁]` map to
`k⟮ξ_a, ξ'_b⟯` by `X₀ ↦ ξ_a = pr₁ (x a) / pr₁ (x j)`, `X₁ ↦ ξ'_b = pr₂ (x b) / pr₂ (x j)`.
For every `c₁₀` there is `c₁₅` such that for every error term `ε = o(n)` there is an error term
`ε' = o(n)` with the following property. Let `γ > 0`, let `d₁, d₂, d` be positive integers with
`N δ₁ = d₁ + s d`, `N δ₂ = d₂ + s d`, `g d² < d₁ d₂ < g² d²`, `d₁ d₂ - g d² > γ d₁ d₂` and
`d₂ ≤ d₁`, let `F = (F_i)` be forms of bidegree `(δ₁, δ₂)` over `k` with `F_i(ξ, ξ') = G η_i^d`,
`G ≠ 0`, `η_0 = 1`, and `h(F) ≤ c₁₀ (d₁ + d₂) / γ + ε (d₁ + d₂)`, and let `(U, V)` be a family
of reduced representations in `R` of the norms of the `η_i`. Then for `i ≠ 0`, a non-zero
polynomial `T` with `T(ξ_a, ξ'_b) = T_i = polynomialT pr₁ pr₂ x j a b (δ₁, δ₂) F η U V hUV d i`
has `h(T) ≤ c₁₅ N² (d₁ + d₂) / γ + 2 N (d₁ + d₂ + 2 s d) + ε' (d₁ + d₂)`. -/
@[faltings "lem_bvr_polynomial_t_summary"]
public theorem exists_mvPolynomialHeight_polynomialT_le {k K L ι : Type*} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Finite ι] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (N s g : ℕ) (c₁₀ : ℝ) :
    ∃ c₁₅ : ℝ, ∀ ε : ℕ → ℝ, ε =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) →
      ∃ ε' : ℕ → ℝ, ε' =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ (a b : ι), a ≠ j → b ≠ j →
      (∀ ν, IsIntegral (Algebra.adjoin k {x a / x j}) (x ν / x j)) →
      (∀ ν, IsIntegral (Algebra.adjoin k {x b / x j}) (x ν / x j)) →
      AlgebraicIndependent k ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] →
      Module.finrank
        (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) L ≤ N ^ 2 →
      ∀ [Algebra (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})],
      (∀ r : MvPolynomial (Fin 2) k,
        (algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) r : L) =
          MvPolynomial.aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] r) →
      ∀ (γ : ℝ) (d₁ d₂ d δ₁ δ₂ : ℕ), 0 < γ → 0 < d₁ → 0 < d₂ → 0 < d →
      N * δ₁ = d₁ + s * d → N * δ₂ = d₂ + s * d →
      g * d ^ 2 < d₁ * d₂ → d₁ * d₂ < g ^ 2 * d ^ 2 →
      γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - g * d ^ 2 → d₂ ≤ d₁ →
      ∀ {m : ℕ} (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          ι ⊕ ι → ℕ × ℕ) (δ₁, δ₂))
        (G : L) (η : Fin (m + 1) → L), G ≠ 0 → η 0 = 1 →
      (∀ i, Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j (δ₁, δ₂) (F i) = G * η i ^ d) →
      ∀ (hF : ∃ i, (F i : MvPolynomial (ι ⊕ ι) k) ≠ 0),
      polynomialFamilyHeight (fun i => (F i : MvPolynomial (ι ⊕ ι) k)) hF ≤
        c₁₀ * (d₁ + d₂) / γ + ε (d₁ + d₂) →
      ∀ (U V : Fin (m + 1) → MvPolynomial (Fin 2) k)
        (hUV : IsReducedNormRepresentation
          (K := IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})
          (MvPolynomial (Fin 2) k) η U V)
        (i : Fin (m + 1)), i ≠ 0 →
      ∀ (T : MvPolynomial (Fin 2) k) (hT : T ≠ 0),
      MvPolynomial.aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] T =
        (polynomialT pr₁ pr₂ x j a b (δ₁, δ₂) F η U V hUV d i : L) →
      mvPolynomialHeight T hT ≤
        c₁₅ * N ^ 2 * (d₁ + d₂) / γ + 2 * N * (d₁ + d₂ + 2 * s * d) + ε' (d₁ + d₂) := by
  obtain ⟨c₁₅, hc₁₅⟩ := exists_logHeight_formNorm_le pr₁ pr₂ x j N s g c₁₀
  -- a uniform order `q` of the poles of the `ξ_ν` at `ξ_a = ∞`
  obtain ⟨q, hq⟩ := (Filter.eventually_all.2 fun (aν : ι × ι) =>
    Filter.eventually_atTop.2 <| show ∃ q₀ : ℕ, ∀ q ≥ q₀, x aν.1 / x j ≠ 0 →
        IsIntegral (Algebra.adjoin k {x aν.1 / x j}) (x aν.2 / x j) →
        IsIntegral (Algebra.adjoin k {(x aν.1 / x j)⁻¹}) (x aν.2 / x j * (x aν.1 / x j)⁻¹ ^ q) by
      by_cases h : x aν.1 / x j ≠ 0 ∧ IsIntegral (Algebra.adjoin k {x aν.1 / x j}) (x aν.2 / x j)
      · obtain ⟨q₀, hq₀⟩ := exists_isIntegral_mul_inv_pow h.1 h.2
        exact ⟨q₀, fun q hq _ _ => isIntegral_mul_inv_pow_mono hq hq₀⟩
      · exact ⟨0, fun _ _ h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩).exists
  refine ⟨c₁₅ + 2 * q * (1 + 2 * s), fun ε hε => ?_⟩
  obtain ⟨ε', hε', hG₀'⟩ := hc₁₅ ε hε
  refine ⟨ε', hε', ?_⟩
  intro a b haj hbj hia hib hind hrank _ hR γ d₁ d₂ d δ₁ δ₂ hγ hd₁ hd₂ hd hδ₁ hδ₂ hgd hgd' hγd
    hd₂₁ m F G η hG hη hFη hF hFh U V hUV i hi T hT hTeq
  -- `T V_i^d` evaluates to the norm `G₀` of the value of `F 0`
  have hVi : V i ^ d ≠ 0 := pow_ne_zero _ (hUV.ne_zero i)
  have hPeq : aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] (T * V i ^ d) =
      (formNorm pr₁ pr₂ x j a b (δ₁, δ₂) (F 0) : L) := by
    have hv : (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) (V i) : L) ≠
          0 := by
      rw [hR]; exact fun h => hUV.ne_zero i (hind (by rw [h, map_zero]))
    rw [map_mul, map_pow, hTeq, ← hR]
    unfold polynomialT
    rw [IntermediateField.coe_div, IntermediateField.coe_pow, div_mul_cancel₀ _ (pow_ne_zero _ hv)]
  have hH := hG₀' a b haj hbj hia hib hind hrank γ d₁ d₂ d δ₁ δ₂ hγ hd₁ hd₂ hd hδ₁ hδ₂ hgd hgd'
    hγd hd₂₁ F G η hG hη hFη hF hFh (T * V i ^ d) (mul_ne_zero hT hVi) hPeq
  set t := pr₁ (x a) / pr₁ (x j)
  set u := pr₂ (x b) / pr₂ (x j)
  have ht0 : t ≠ 0 := by simpa using hind.ne_zero 0
  have hu0 : u ≠ 0 := by simpa using hind.ne_zero 1
  have hta : pr₁ (x a / x j) = t := map_div₀ _ _ _
  have hub : pr₂ (x b / x j) = u := map_div₀ _ _ _
  have hwa : x a / x j ≠ 0 := fun h => ht0 (by rw [← hta, h, map_zero])
  have hwb : x b / x j ≠ 0 := fun h => hu0 (by rw [← hub, h, map_zero])
  set α : ι → L := fun ν => pr₁ (x ν / x j)
  set β : ι → L := fun ν => pr₂ (x ν / x j)
  set z := Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j (δ₁, δ₂) (F 0)
  have hz : z = aeval (Sum.elim α β) (F 0 : MvPolynomial (ι ⊕ ι) k) :=
    affineEvaluation_eq_aeval pr₁ pr₂ x j (δ₁, δ₂) (F 0)
  -- integrality of the affine co-ordinates over `k[t, u]`, `k[t⁻¹, u]` and `k[t, u⁻¹]`
  have hα {s : Set L} (hs : t ∈ s) ν : IsIntegral (Algebra.adjoin k s) (α ν) :=
    isIntegral_map_of_mem pr₁ (by rw [hta]; exact Algebra.subset_adjoin hs) (hia ν)
  have hβ {s : Set L} (hs : u ∈ s) ν : IsIntegral (Algebra.adjoin k s) (β ν) :=
    isIntegral_map_of_mem pr₂ (by rw [hub]; exact Algebra.subset_adjoin hs) (hib ν)
  have hα' ν : IsIntegral (Algebra.adjoin k {t⁻¹, u}) (α ν * t⁻¹ ^ q) := by
    have := isIntegral_map_of_mem pr₁ (T := Algebra.adjoin k {t⁻¹, u})
      (by rw [map_inv₀, hta]; exact Algebra.subset_adjoin (by simp)) (hq (a, ν) hwa (hia ν))
    rwa [map_mul, map_pow, map_inv₀, hta] at this
  have hβ' ν : IsIntegral (Algebra.adjoin k {t, u⁻¹}) (β ν * u⁻¹ ^ q) := by
    have := isIntegral_map_of_mem pr₂ (T := Algebra.adjoin k {t, u⁻¹})
      (by rw [map_inv₀, hub]; exact Algebra.subset_adjoin (by simp)) (hq (b, ν) hwb (hib ν))
    rwa [map_mul, map_pow, map_inv₀, hub] at this
  have hz₀ : IsIntegral (Algebra.adjoin k {t, u}) z :=
    hz ▸ isIntegral_aeval_sumElim _ (hα (by simp)) (hβ (by simp)) _
  have hz₁ : IsIntegral (Algebra.adjoin k {t⁻¹, u}) (z * t⁻¹ ^ (q * δ₁)) := by
    rw [hz, pow_mul, ← aeval_mul_left_eq (F 0) α β]
    exact isIntegral_aeval_sumElim _ hα' (hβ (by simp)) _
  have hz₂ : IsIntegral (Algebra.adjoin k {t, u⁻¹}) (z * u⁻¹ ^ (q * δ₂)) := by
    rw [hz, pow_mul, ← aeval_mul_right_eq (F 0) α β]
    exact isIntegral_aeval_sumElim _ (hα (by simp)) hβ' _
  -- the norm `G₀` is a polynomial of degree at most `[L : E] q δᵢ` in each variable
  obtain ⟨G₀, hdeg₀, hdeg₁, hG₀⟩ := exists_degreeOf_le_aeval_eq_norm ht0 hu0 hind
    (algebraicIndependent_inv_cons hind)
    (algebraicIndependent_swap (algebraicIndependent_inv_cons (algebraicIndependent_swap hind)))
    (q * δ₁) (q * δ₂) hz₀ hz₁ hz₂
  have hdeg : (T * V i ^ d).degreeOf 0 + (T * V i ^ d).degreeOf 1 ≤ N ^ 2 * q * (δ₁ + δ₂) := by
    rw [hind (hPeq.trans hG₀.symm)]
    nlinarith [hdeg₀.trans (Nat.mul_le_mul_right (q * δ₁) hrank),
      hdeg₁.trans (Nat.mul_le_mul_right (q * δ₂) hrank)]
  have hsplit : (c₁₅ + 2 * q * (1 + 2 * s)) * N ^ 2 * (d₁ + d₂) / γ =
      c₁₅ * N ^ 2 * (d₁ + d₂) / γ + 2 * q * (1 + 2 * s) * N ^ 2 * (d₁ + d₂) / γ := by ring
  rw [hsplit]
  linarith [mvPolynomialHeight_le_mul_add hT hVi, hH, (by positivity :
      (0 : ℝ) ≤ 2 * N * (d₁ + d₂ + 2 * s * d)),
    two_mul_le_of_le_mul_add hγ hd₁ hd₂ hδ₁ hδ₂ hgd hgd' hγd hd₂₁ hdeg]

end Faltings.BombieriRoth
