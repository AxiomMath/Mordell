module

public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import Mordell.Height.Polynomial.Gelfond
public import Mordell.Height.Polynomial.Basic
public import Mordell.Height.Polynomial.VectorProduct
public import Mordell.Height.Weil.Nonneg

/-!
# The height of `G_0`

Let `k` be a number field (more generally an algebraic extension of `ℚ`), `K = k(C)` and
`L = k(C × C)` with the two projections `pr₁^*, pr₂^* : K → L`, `x = (x_ν)` the coordinates of
`C ⊆ ℙⁿ`, `x_j` the distinguished coordinate, `ξ_ν = x_ν / x_j` and `ξ'_ν = pr₂^* ξ_ν`. For a
non-zero section of `𝒪(V)` with representative `F = (F_i)` of bidegree `(δ₁, δ₂)` and with
coefficients in `k`, the norm `G_0 = Norm_{L / k(ξ_a, ξ'_b)} F_0(ξ, ξ')` is a polynomial in
`ξ_a, ξ'_b`. Bombieri's height bound says that if `h(F) ≤ c₁₀ (d₁ + d₂) / γ + o(d₁ + d₂)`, then
`h(G_0) ≤ c₁₅ N² (d₁ + d₂) / γ + o(d₁ + d₂)`, with `c₁₅` depending only on the curve data and
`c₁₀`.

## Main results

* `Faltings.BombieriRoth.exists_logHeight_formNorm_le`: the height bound for `G_0`.

## Implementation notes

The statement is made in the function fields, as for `Faltings.BombieriRoth.formNorm`: `K`, `L`
are fields over `k`, `pr₁ pr₂ : K →ₐ[k] L`, and the coordinates are `x : ι → K` with a
distinguished index `j`; the indices `1 ≤ a, b ≤ n` are `a ≠ j`, `b ≠ j`. The geometry of
`C × C` enters through the properties of these fields that the bound uses: every `ξ_ν` is
integral over `k[ξ_a]` and over `k[ξ_b]`, the functions `ξ_a, ξ'_b` are algebraically
independent over `k`, and `[L : k(ξ_a, ξ'_b)] ≤ N²`. The section `s` and its representative
are recorded as for `Faltings.BombieriRoth.IsReducedNormRepresentation.formNorm_mul_num_pow_eq`:
`F_i(ξ, ξ') = G η_i^d` with `G ≠ 0` and `η_0 = 1`.

Each `o(d₁ + d₂)` is a function `ℕ → ℝ` of `d₁ + d₂` that is `o(n)` as `n → ∞`. The bound
holds uniformly: for each error term `ε` of the hypothesis there is one error term `ε'` of
the conclusion that serves for all `a, b, γ, d₁, d₂, d` and all representatives. `h(G_0)` is
the height `Faltings.mvPolynomialHeight` of the polynomial `P ∈ k[X₀, X₁]` with
`P(ξ_a, ξ'_b) = G_0`, unique by algebraic independence.

The bound is proved in a general form. Let `L` be a field over `k` with elements `ξ_a, ξ'_b`
algebraically independent over `k`, and `E = k(ξ_a, ξ'_b) ⊆ L`. Suppose that finitely many
elements `θ_ν ∈ L` satisfy monic equations `Q_ν(θ_ν) = 0` with coefficients in `k[ξ_a, ξ'_b]`,
and let `y = Y(θ)` for a polynomial `Y` over `k` of total degree at most `δ`. Then the norm
`G = Norm_{L/E} y` is `P(ξ_a, ξ'_b)` for a polynomial `P`, and
`h(P) ≤ A h(Y) + B (δ + 1)` with `A, B` depending only on the `Q_ν` and on `[L : E]`.

The proof is algebraic. Let `C_ν` be the companion matrix of `Q_ν` and `M` the matrix of
multiplication by `Y` on `⊗_ν k[ξ_a, ξ'_b][X_ν]/(Q_ν)` in the monomial basis, so that its entries
are `∑_m Y_m ∏_ν (C_ν^{m_ν})_{g_ν g'_ν}`. The vector `(∏_ν θ_ν^{g_ν})_g` is an eigenvector of `M`
with eigenvalue `y`, so `y` is a root of the characteristic polynomial `χ` of `M`. Since
`k[ξ_a, ξ'_b]` is integrally closed, the minimal polynomial `μ` of `y` over `E` has coefficients
in `k[ξ_a, ξ'_b]` and divides `χ`, and `G = ((-1)^{deg μ} μ(0))^e` with `e = [L : E(y)]`.

The height of `χ`, as a polynomial in `ξ_a, ξ'_b` and the variable `Z`, is bounded place by
place: at a finite place the sup norm of coefficients is submultiplicative and ultrametric, at an
infinite place the `ℓ¹` norm of coefficients is submultiplicative, and the expansion of
`det (Z - M)` gives `|χ|_v ≤ |B|_v^{ε_v} (|Y|_v |Q|_v^δ)^r` with an integer `B` whose logarithm
is linear in `δ`, `r` the size of `M` and `|Q|_v` the local size of the coefficients of the
`Q_ν`. Summing over the places, after normalizing `Y` to have a coefficient `1`, gives
`h(χ) ≤ log B + r h(Y) + r δ h(Q)`. Gelfond's inequality bounds `h(μ)` by `h(χ)` up to a
multiple of the degree, and `h(μ(0)^e) ≤ e h(μ(0)) + O(e deg μ(0))`.

For the curve, `θ` is `(ξ, ξ')`, the `Q_ν` come from the integrality of `ξ_ν` over `k[ξ_a]` and of
`ξ'_ν` over `k[ξ'_b]`, `Y = F_0` and `δ = δ₁ + δ₂`. With `δ₁ + δ₂ + 1 ≤ (2 + 2s)(d₁ + d₂)/γ`
(from `d < d₁` and `γ < 1`) and `h(F_0) ≤ h(F)` this is the bound
`h(G_0) ≤ c₁₅ N² (d₁ + d₂)/γ + o(d₁ + d₂)`.

The source bounds `|G_0|_v` through the values of `F_0` at the points of the fibres of
`π_{ab}` over the unit polydisc and Cauchy's root bound. Here the fibre over `(t, t')` is replaced
by the algebra `⊗_ν k[ξ_a, ξ'_b][X_ν]/(Q_ν)`: the characteristic polynomial of multiplication by
`F_0` is a universal multiple of the minimal polynomial of `F_0(ξ, ξ')`, and its coefficients are
bounded from those of `F_0` and of the `Q_ν` by expanding a determinant. The root bound `R_v`
becomes the local size of the coefficients of the `Q_ν`, whose logarithms sum to the height
`h(Q)` of their coefficient vector; it is the constant `c_R`.

## References

* [Bombieri1990], Sec. 9, p. 633.
-/

namespace Faltings.BombieriRoth

open Polynomial Finset

section Companion

variable {R : Type*} [CommRing R]

/-- The companion matrix of `q` (of size `natDegree q`): row `i` is `e_{i+1}` for
`i + 1 < n` and `-(q_0, …, q_{n-1})` for `i + 1 = n`. -/
private noncomputable def companion (q : R[X]) : Matrix (Fin q.natDegree) (Fin q.natDegree) R :=
  fun i i' => if (i : ℕ) + 1 = i' then 1 else if (i : ℕ) + 1 = q.natDegree then -q.coeff i' else 0

variable {L : Type*} [CommRing L]

private lemma sum_companion_mul_pow (f : R →+* L) {q : R[X]} (hq : q.Monic) {θ : L}
    (hθ : q.eval₂ f θ = 0) (i : Fin q.natDegree) :
    ∑ i' : Fin q.natDegree, f (companion q i i') * θ ^ (i' : ℕ) = θ * θ ^ (i : ℕ) := by
  classical
  by_cases h : (i : ℕ) + 1 < q.natDegree
  · rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, h⟩ : Fin q.natDegree)]
    · simp [companion, pow_succ, mul_comm]
    · intro b _ hb
      have : ¬ ((i : ℕ) + 1 = b) := fun h' => hb (Fin.ext h'.symm)
      simp [companion, this, h.ne]
    · simp
  · have hn : (i : ℕ) + 1 = q.natDegree := by omega
    have hsum := hθ
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hsum
    have hrest : ∑ i' : Fin q.natDegree, f (companion q i i') * θ ^ (i' : ℕ) =
        -∑ x ∈ Finset.range q.natDegree, f (q.coeff x) * θ ^ x := by
      rw [Finset.sum_range (fun x => f (q.coeff x) * θ ^ x), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i' _ => ?_
      have : ¬ ((i : ℕ) + 1 = i') := by omega
      simp only [companion]
      rw [ite_eq_right this, ite_eq_left hn, map_neg, neg_mul]
    rw [hrest, ← pow_succ', hn]
    linear_combination -hsum

private lemma sum_companion_pow_mul_pow (f : R →+* L) {q : R[X]} (hq : q.Monic) {θ : L}
    (hθ : q.eval₂ f θ = 0) (m : ℕ) (i : Fin q.natDegree) :
    ∑ i' : Fin q.natDegree, f ((companion q ^ m) i i') * θ ^ (i' : ℕ) = θ ^ m * θ ^ (i : ℕ) := by
  induction m generalizing i with
  | zero =>
    classical
    rw [Finset.sum_eq_single i]
    · simp
    · exact fun b _ hb => by simp [Ne.symm hb]
    · simp
  | succ m ih =>
    rw [pow_succ']
    simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ih, ← mul_assoc, mul_comm _ (θ ^ m), mul_assoc,
      ← Finset.mul_sum, sum_companion_mul_pow f hq hθ, pow_succ]
    ring

end Companion

section Kronecker

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] {κ : Type*} [Fintype κ]
  [DecidableEq κ]

/-- The matrix of multiplication by `Y(X)` on `⊗_ν R[X_ν]/(Q_ν)`, in the monomial basis. -/
private noncomputable def kronMatrix (Y : MvPolynomial κ A) (Q : κ → R[X]) :
    Matrix (∀ ν, Fin (Q ν).natDegree) (∀ ν, Fin (Q ν).natDegree) R :=
  fun g g' => ∑ m ∈ Y.support,
    algebraMap A R (Y.coeff m) * ∏ ν, (companion (Q ν) ^ (m ν)) (g ν) (g' ν)

variable {L : Type*} [CommRing L] [Algebra A L]

private lemma kronMatrix_mulVec (f : R →ₐ[A] L) (Y : MvPolynomial κ A) {Q : κ → R[X]}
    (hQ : ∀ ν, (Q ν).Monic) {θ : κ → L} (hθ : ∀ ν, (Q ν).eval₂ (f : R →+* L) (θ ν) = 0) :
    ((kronMatrix Y Q).map f).mulVec (fun g => ∏ ν, θ ν ^ (g ν : ℕ)) =
      MvPolynomial.aeval θ Y • (fun g => ∏ ν, θ ν ^ (g ν : ℕ)) := by
  funext g
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, kronMatrix, map_sum, map_mul,
    map_prod, AlgHom.commutes, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun ν (s : Fin (Q ν).natDegree) =>
    f ((companion (Q ν) ^ (m ν)) (g ν) s) * θ ν ^ (s : ℕ))]
  exact Finset.prod_congr rfl fun ν _ =>
    sum_companion_pow_mul_pow (f : R →+* L) (hQ ν) (hθ ν) (m ν) (g ν)

private lemma one_le_natDegree_of_eval₂_eq_zero [Nontrivial L] {f : R →+* L} {q : R[X]}
    (hq : q.Monic)
    {θ : L} (hθ : q.eval₂ f θ = 0) : 1 ≤ q.natDegree := by
  by_contra h
  have h0 : q.natDegree = 0 := by omega
  rw [(Monic.natDegree_eq_zero hq).mp h0, eval₂_one] at hθ
  exact one_ne_zero hθ

private lemma eval₂_charpoly_kronMatrix {L : Type*} [Field L] [Algebra A L] (f : R →ₐ[A] L)
    (Y : MvPolynomial κ A) {Q : κ → R[X]} (hQ : ∀ ν, (Q ν).Monic) {θ : κ → L}
    (hθ : ∀ ν, (Q ν).eval₂ (f : R →+* L) (θ ν) = 0) :
    (kronMatrix Y Q).charpoly.eval₂ (f : R →+* L) (MvPolynomial.aeval θ Y) = 0 := by
  rw [← eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun g => ∏ ν, θ ν ^ (g ν : ℕ), ?_, ?_⟩
  · intro h
    simpa using congrFun h (fun ν => ⟨0, one_le_natDegree_of_eval₂_eq_zero (hQ ν) (hθ ν)⟩)
  · rw [Matrix.sub_mulVec]
    have := kronMatrix_mulVec f Y hQ hθ
    simp only [RingHom.coe_coe] at this ⊢
    rw [this, Matrix.scalar_apply]
    funext g
    simp

end Kronecker

section ThreeVariables

variable {A : Type*} [CommRing A] {σ : Type*}

private lemma optionEquivLeft_symm_C (p : MvPolynomial σ A) :
    (MvPolynomial.optionEquivLeft A σ).symm (Polynomial.C p) = MvPolynomial.rename some p := by
  rw [MvPolynomial.optionEquivLeft_symm_apply, aevalTower_C]

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- The characteristic matrix `Z - M` of a matrix over `A[X_σ]`, with `Z = X none`. -/
private noncomputable def charMatrixOption (M : Matrix ρ ρ (MvPolynomial σ A)) :
    Matrix ρ ρ (MvPolynomial (Option σ) A) :=
  fun i j => (if i = j then MvPolynomial.X none else 0) - MvPolynomial.rename some (M i j)

private lemma optionEquivLeft_symm_charpoly (M : Matrix ρ ρ (MvPolynomial σ A)) :
    (MvPolynomial.optionEquivLeft A σ).symm M.charpoly = (charMatrixOption M).det := by
  rw [Matrix.charpoly, ← AlgEquiv.coe_ringEquiv, ← RingEquiv.coe_toRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, map_sub, charMatrixOption,
    optionEquivLeft_symm_C, Matrix.diagonal_apply]
  split_ifs <;> simp

end ThreeVariables

/-- A local size on a commutative ring: nonnegative, submultiplicative, `N 0 = 0`, `N 1 ≤ 1`,
even, subadditive, and ultrametric when `ε = 0`. -/
private structure IsLocalSize {S : Type*} [CommRing S] (N : S → ℝ) (ε : ℕ) : Prop where
  nonneg : ∀ a, 0 ≤ N a
  zero : N 0 = 0
  one : N 1 ≤ 1
  neg : ∀ a, N (-a) = N a
  mul : ∀ a b, N (a * b) ≤ N a * N b
  add : ∀ a b, N (a + b) ≤ N a + N b
  add_max : ε = 0 → ∀ a b, N (a + b) ≤ max (N a) (N b)
  le_one : ε ≤ 1

namespace IsLocalSize

variable {S : Type*} [CommRing S] {N : S → ℝ} {ε : ℕ}

private lemma comp {S' : Type*} [CommRing S'] (h : IsLocalSize N ε) (f : S' →+* S) :
    IsLocalSize (N ∘ f) ε where
  nonneg a := h.nonneg _
  zero := by simp [h.zero]
  one := by simpa using h.one
  neg a := by simp [h.neg]
  mul a b := by simpa using h.mul _ _
  add a b := by simpa using h.add _ _
  add_max he a b := by simpa using h.add_max he _ _
  le_one := h.le_one

private lemma sum_le (h : IsLocalSize N ε) {ι : Type*} (s : Finset ι) (f : ι → S) {B : ℝ}
    (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, N (f i) ≤ B) : N (∑ i ∈ s, f i) ≤ (s.card : ℝ) ^ ε * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, h.zero, Finset.card_empty, Nat.cast_zero]; positivity
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h.le_one with he | he
    · subst he
      simp only [pow_zero, one_mul] at h2 ⊢
      exact (h.add_max rfl _ _).trans (max_le h1 h2)
    · subst he
      simp only [pow_one, Nat.cast_add, Nat.cast_one] at h2 ⊢
      linarith [h.add (f a) (∑ i ∈ s, f i)]

private lemma prod_le (h : IsLocalSize N ε) {ι : Type*} (s : Finset ι) (f : ι → S) :
    N (∏ i ∈ s, f i) ≤ ∏ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h.mul _ _).trans (mul_le_mul_of_nonneg_left ih (h.nonneg _))

private lemma smul_units_int (h : IsLocalSize N ε) (u : ℤˣ) (a : S) : N (u • a) = N a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [h.neg]

private lemma mul_apply_le (h : IsLocalSize N ε) {ρ : Type*} [Fintype ρ] (A B : Matrix ρ ρ S)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : ∀ i j, N (A i j) ≤ a) (hB : ∀ i j, N (B i j) ≤ b)
    (i k : ρ) : N ((A * B) i k) ≤ (Fintype.card ρ : ℝ) ^ ε * (a * b) := by
  rw [Matrix.mul_apply]
  exact h.sum_le _ _ (mul_nonneg ha hb) fun j _ =>
    (h.mul _ _).trans (mul_le_mul (hA i j) (hB j k) (h.nonneg _) ha)

private lemma pow_apply_le (h : IsLocalSize N ε) {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (C : Matrix ρ ρ S) {b : ℝ} (hb : 0 ≤ b) (hC : ∀ i j, N (C i j) ≤ b) (m : ℕ) (i j : ρ) :
    N ((C ^ m) i j) ≤ ((Fintype.card ρ : ℝ) ^ ε * b) ^ m := by
  induction m generalizing i j with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs
    · exact h.one
    · exact h.zero.le.trans zero_le_one
  | succ m ih =>
    rw [pow_succ']
    refine (h.mul_apply_le C (C ^ m) hb (by positivity) hC ih i j).trans (le_of_eq ?_)
    ring

private lemma det_le (h : IsLocalSize N ε) {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (A : Matrix ρ ρ S) {b : ℝ} (hb : 0 ≤ b) (hA : ∀ i j, N (A i j) ≤ b) :
    N A.det ≤ ((Fintype.card ρ).factorial : ℝ) ^ ε * b ^ Fintype.card ρ := by
  rw [Matrix.det_apply]
  have := h.sum_le (Finset.univ : Finset (Equiv.Perm ρ))
    (fun σ => Equiv.Perm.sign σ • ∏ i, A (σ i) i) (pow_nonneg hb (Fintype.card ρ)) fun σ _ => by
      rw [h.smul_units_int]
      refine (h.prod_le _ _).trans ?_
      calc ∏ i, N (A (σ i) i) ≤ ∏ _i : ρ, b :=
            Finset.prod_le_prod₀ (fun i _ => h.nonneg _) fun i _ => hA _ _
        _ = b ^ Fintype.card ρ := by simp
  simpa [Finset.card_univ, Fintype.card_perm] using this

end IsLocalSize

section Bound

variable {A : Type*} [CommRing A] {σ κ : Type*} [Fintype κ] [DecidableEq κ] {ε : ℕ}

private lemma IsLocalSize.sub_le {S : Type*} [CommRing S] {N : S → ℝ}
    (h : IsLocalSize N ε) {a x : S}
    {B : ℝ} (ha : N a ≤ 1) (hx : N x ≤ B) (hB : 1 ≤ B) : N (a - x) ≤ 2 ^ ε * B := by
  rw [sub_eq_add_neg]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h.le_one with he | he
  · subst he
    rw [pow_zero, one_mul]
    exact (h.add_max rfl _ _).trans (max_le (ha.trans hB) ((h.neg x).le.trans hx))
  · subst he
    linarith [h.add a (-x), h.neg x]

omit [DecidableEq κ] in
/-- Entries of `kronMatrix Y Q`, seen in `A[X_{Option σ}]`, have size at most
`#supp(Y)^ε · Yb · (nmax^ε b)^δ`. -/
private lemma kronMatrix_apply_le (N : MvPolynomial (Option σ) A → ℝ) (h : IsLocalSize N ε)
    (Y : MvPolynomial κ A) (Q : κ → (MvPolynomial σ A)[X])
    {Yb b : ℝ} (hYb : 0 ≤ Yb) (hb : 1 ≤ b) {nmax δ : ℕ} (hnmax : 1 ≤ nmax)
    (hn : ∀ ν, (Q ν).natDegree ≤ nmax)
    (hY : ∀ m ∈ Y.support, N (MvPolynomial.C (Y.coeff m)) ≤ Yb)
    (hC : ∀ ν i i', N (MvPolynomial.rename some (companion (Q ν) i i')) ≤ b)
    (hδ : Y.totalDegree ≤ δ) (g g' : ∀ ν, Fin (Q ν).natDegree) :
    N (MvPolynomial.rename some (kronMatrix Y Q g g')) ≤
      (Y.support.card : ℝ) ^ ε * (Yb * ((nmax : ℝ) ^ ε * b) ^ δ) := by
  set β : ℝ := (nmax : ℝ) ^ ε * b with hβ
  have hβ1 : 1 ≤ β := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by exact_mod_cast hnmax)) hb
  have h' := h.comp (MvPolynomial.rename some : MvPolynomial σ A →ₐ[A] _).toRingHom
  refine h'.sum_le _ _ (by positivity) fun m hm => ?_
  refine (h'.mul _ _).trans ?_
  have h1 : (N ∘ ⇑(MvPolynomial.rename some : MvPolynomial σ A →ₐ[A] _).toRingHom)
      (algebraMap A (MvPolynomial σ A) (Y.coeff m)) ≤ Yb := by
    simpa [MvPolynomial.algebraMap_eq] using hY m hm
  refine mul_le_mul h1 ?_ (h'.nonneg _) hYb
  refine (h'.prod_le _ _).trans ?_
  calc ∏ ν, (N ∘ ⇑(MvPolynomial.rename some : MvPolynomial σ A →ₐ[A] _).toRingHom)
        ((companion (Q ν) ^ m ν) (g ν) (g' ν))
      ≤ ∏ ν, β ^ m ν := by
        refine Finset.prod_le_prod₀ (fun ν _ => h'.nonneg _) fun ν _ => ?_
        refine (h'.pow_apply_le _ (by linarith) (fun i j => hC ν i j) _ _ _).trans ?_
        refine pow_le_pow_left₀ (by positivity) ?_ _
        rw [Fintype.card_fin, hβ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn ν) _) (by linarith)
    _ = β ^ (∑ ν, m ν) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ β ^ δ := by
        refine pow_le_pow_right₀ hβ1 ?_
        refine le_trans ?_ hδ
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

private lemma det_charMatrixOption_kronMatrix_le (N : MvPolynomial (Option σ) A → ℝ)
    (h : IsLocalSize N ε) (hX : N (MvPolynomial.X none) ≤ 1)
    (Y : MvPolynomial κ A) (hY0 : Y ≠ 0) (Q : κ → (MvPolynomial σ A)[X])
    {Yb b : ℝ} (hYb : 1 ≤ Yb) (hb : 1 ≤ b) {nmax δ : ℕ} (hnmax : 1 ≤ nmax)
    (hn : ∀ ν, (Q ν).natDegree ≤ nmax)
    (hY : ∀ m ∈ Y.support, N (MvPolynomial.C (Y.coeff m)) ≤ Yb)
    (hC : ∀ ν i i', N (MvPolynomial.rename some (companion (Q ν) i i')) ≤ b)
    (hδ : Y.totalDegree ≤ δ) :
    N (charMatrixOption (kronMatrix Y Q)).det ≤
      ((Fintype.card (∀ ν, Fin (Q ν).natDegree)).factorial : ℝ) ^ ε *
        (2 ^ ε * ((Y.support.card : ℝ) ^ ε * (Yb * ((nmax : ℝ) ^ ε * b) ^ δ))) ^
          Fintype.card (∀ ν, Fin (Q ν).natDegree) := by
  have hβ1 : 1 ≤ (nmax : ℝ) ^ ε * b := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by exact_mod_cast hnmax)) hb
  have hsupp : (1 : ℝ) ≤ (Y.support.card : ℝ) ^ ε :=
    one_le_pow₀ (by exact_mod_cast Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hY0))
  have hbM1 : 1 ≤ (Y.support.card : ℝ) ^ ε * (Yb * ((nmax : ℝ) ^ ε * b) ^ δ) :=
    one_le_mul_of_one_le_of_one_le hsupp
      (one_le_mul_of_one_le_of_one_le hYb (one_le_pow₀ hβ1))
  refine (h.det_le _ (by positivity) fun i j => ?_).trans (le_of_eq rfl)
  simp only [charMatrixOption]
  refine h.sub_le ?_ (kronMatrix_apply_le N h Y Q (by linarith) hb hnmax hn hY hC hδ i j) hbM1
  split_ifs
  · exact hX
  · exact h.zero.le.trans zero_le_one

end Bound

section Sizes

variable {F : Type*} [Field F] {τ : Type*}

/-- The `ℓ¹` size of a polynomial with respect to an absolute value. -/
private noncomputable def l1Size (u : AbsoluteValue F ℝ) (p : MvPolynomial τ F) : ℝ :=
  ∑ I ∈ p.support, u (p.coeff I)

private lemma l1Size_eq_sum (u : AbsoluteValue F ℝ) {p : MvPolynomial τ F} {T : Finset (τ →₀ ℕ)}
    (hT : p.support ⊆ T) : l1Size u p = ∑ I ∈ T, u (p.coeff I) := by
  refine Finset.sum_subset hT fun I _ hI => ?_
  rw [MvPolynomial.notMem_support_iff.mp hI, map_zero]

private lemma l1Size_sum_le (u : AbsoluteValue F ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial τ F) : l1Size u (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Size u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1Size]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    set g := ∑ i ∈ s, f i
    have hT : (f a + g).support ⊆ (f a).support ∪ g.support := MvPolynomial.support_add
    calc l1Size u (f a + g) ≤ l1Size u (f a) + l1Size u g := by
          rw [l1Size_eq_sum u hT, l1Size_eq_sum u (p := f a) Finset.subset_union_left,
            l1Size_eq_sum u (p := g) Finset.subset_union_right, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun I _ => by rw [MvPolynomial.coeff_add]; exact u.add_le _ _
      _ ≤ l1Size u (f a) + ∑ i ∈ s, l1Size u (f i) := add_le_add_right ih _

private lemma l1Size_monomial (u : AbsoluteValue F ℝ) (I : τ →₀ ℕ) (c : F) :
    l1Size u (MvPolynomial.monomial I c) = u c := by
  classical
  by_cases hc : c = 0
  · simp [hc, l1Size]
  · rw [l1Size, MvPolynomial.support_monomial, ite_eq_right hc, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, ite_eq_left rfl]

private lemma isLocalSize_l1Size (u : AbsoluteValue F ℝ) :
    IsLocalSize (l1Size (τ := τ) u) 1 where
  nonneg p := Finset.sum_nonneg fun I _ => u.nonneg _
  zero := by simp [l1Size]
  one := by
    rw [← MvPolynomial.C_1, MvPolynomial.C_apply, l1Size_monomial, map_one]
  neg p := by simp [l1Size, MvPolynomial.support_neg]
  mul p q := by
    classical
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p,
      ← MvPolynomial.support_sum_monomial_coeff q, Finset.sum_mul_sum]
    refine (l1Size_sum_le u _ _).trans ?_
    rw [l1Size, l1Size, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun I _ => (l1Size_sum_le u _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MvPolynomial.monomial_mul_monomial, l1Size_monomial, map_mul]
  add p q := by
    simpa [Fin.sum_univ_two] using l1Size_sum_le u (Finset.univ : Finset (Fin 2)) ![p, q]
  add_max h := absurd h one_ne_zero
  le_one := le_rfl

/-- The sup size of a polynomial with respect to a function on the coefficients. -/
private noncomputable def supSize (v : F → ℝ) (p : MvPolynomial τ F) : ℝ :=
  ⨆ I, v (p.coeff I)

private lemma le_supSize (v : AbsoluteValue F ℝ) (p : MvPolynomial τ F) (I : τ →₀ ℕ) :
    v (p.coeff I) ≤ supSize v p := by
  classical
  refine le_ciSup (f := fun I => v (p.coeff I)) ?_ I
  refine ⟨∑ J ∈ p.support, v (p.coeff J), ?_⟩
  rintro _ ⟨J, rfl⟩
  by_cases hJ : J ∈ p.support
  · exact Finset.single_le_sum (f := fun J => v (p.coeff J)) (fun _ _ => v.nonneg _) hJ
  · change v (p.coeff J) ≤ _
    rw [MvPolynomial.notMem_support_iff.mp hJ, map_zero]
    exact Finset.sum_nonneg fun _ _ => v.nonneg _

private lemma supSize_le (v : AbsoluteValue F ℝ) (p : MvPolynomial τ F) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ I, v (p.coeff I) ≤ B) : supSize v p ≤ B :=
  Real.iSup_le h hB

private lemma supSize_nonneg (v : AbsoluteValue F ℝ) (p : MvPolynomial τ F) : 0 ≤ supSize v p :=
  Real.iSup_nonneg fun _ => v.nonneg _

private lemma isLocalSize_supSize (v : AbsoluteValue F ℝ) (hv : IsNonarchimedean v) :
    IsLocalSize (supSize (τ := τ) v) 0 where
  nonneg p := supSize_nonneg v p
  zero := by simp [supSize]
  one := supSize_le v _ zero_le_one fun I => by
    classical
    rw [MvPolynomial.coeff_one]; split_ifs <;> simp
  neg p := by simp [supSize]
  mul p q := by
    classical
    refine supSize_le v _ (mul_nonneg (supSize_nonneg v p) (supSize_nonneg v q)) fun I => ?_
    rw [MvPolynomial.coeff_mul]
    rcases (Finset.HasAntidiagonal.antidiagonal I).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, map_zero]
      exact mul_nonneg (supSize_nonneg v p) (supSize_nonneg v q)
    refine (hv.apply_sum_le_sup hne).trans (Finset.sup'_le _ _ fun x _ => ?_)
    rw [map_mul]
    exact mul_le_mul (le_supSize v p _) (le_supSize v q _) (v.nonneg _) (supSize_nonneg v p)
  add p q := by
    refine supSize_le v _ (add_nonneg (supSize_nonneg v p) (supSize_nonneg v q)) fun I => ?_
    rw [MvPolynomial.coeff_add]
    exact (v.add_le _ _).trans (add_le_add (le_supSize v p _) (le_supSize v q _))
  add_max _ p q := by
    refine supSize_le v _ ((supSize_nonneg v p).trans (le_max_left _ _)) fun I => ?_
    rw [MvPolynomial.coeff_add]
    exact (hv _ _).trans (max_le_max (le_supSize v p _) (le_supSize v q _))
  le_one := zero_le_one

end Sizes

section SizeLemmas

variable {F : Type*} [Field F] {τ : Type*}

private lemma l1Size_C (u : AbsoluteValue F ℝ) (c : F) : l1Size u
    (MvPolynomial.C c : MvPolynomial τ F) = u c := by
  rw [MvPolynomial.C_apply, l1Size_monomial]

private lemma l1Size_X (u : AbsoluteValue F ℝ) (i : τ) : l1Size u
    (MvPolynomial.X i : MvPolynomial τ F) = 1 := by
  classical
  rw [l1Size, MvPolynomial.support_X, Finset.sum_singleton, MvPolynomial.coeff_X]
  simp

private lemma le_l1Size (u : AbsoluteValue F ℝ) (p : MvPolynomial τ F) (I : τ →₀ ℕ) :
    u (p.coeff I) ≤ l1Size u p := by
  by_cases hI : I ∈ p.support
  · exact Finset.single_le_sum (f := fun J => u (p.coeff J)) (fun _ _ => u.nonneg _) hI
  · rw [MvPolynomial.notMem_support_iff.mp hI, map_zero]
    exact Finset.sum_nonneg fun _ _ => u.nonneg _

private lemma l1Size_le_card_mul (u : AbsoluteValue F ℝ) (p : MvPolynomial τ F) {B : ℝ}
    (h : ∀ I, u (p.coeff I) ≤ B) : l1Size u p ≤ p.support.card * B := by
  simpa [l1Size, nsmul_eq_mul] using
    Finset.sum_le_card_nsmul p.support (fun I => u (p.coeff I)) B fun I _ => h I

private lemma l1Size_rename_some {σ : Type*} (u : AbsoluteValue F ℝ) (p : MvPolynomial σ F) :
    l1Size u (MvPolynomial.rename some p) = l1Size u p := by
  classical
  rw [l1Size, MvPolynomial.support_rename_of_injective (Option.some_injective σ),
    Finset.sum_image fun _ _ _ _ h => Finsupp.mapDomain_injective (Option.some_injective σ) h]
  simp_rw [MvPolynomial.coeff_rename_mapDomain _ (Option.some_injective σ)]
  rfl

private lemma supSize_C (v : AbsoluteValue F ℝ) (c : F) :
    supSize v (MvPolynomial.C c : MvPolynomial τ F) = v c := by
  classical
  refine le_antisymm (supSize_le v _ (v.nonneg _) fun I => ?_) ?_
  · rw [MvPolynomial.coeff_C]; split_ifs <;> simp [v.nonneg]
  · simpa using le_supSize v (MvPolynomial.C c : MvPolynomial τ F) 0

private lemma supSize_X_le (v : AbsoluteValue F ℝ) (i : τ) :
    supSize v (MvPolynomial.X i : MvPolynomial τ F) ≤ 1 := by
  classical
  refine supSize_le v _ zero_le_one fun I => ?_
  rw [MvPolynomial.coeff_X]; split_ifs <;> simp

private lemma supSize_rename_some_le {σ : Type*} (v : AbsoluteValue F ℝ) (p : MvPolynomial σ F) :
    supSize v (MvPolynomial.rename some p) ≤ supSize v p := by
  classical
  refine supSize_le v _ (supSize_nonneg v p) fun I => ?_
  by_cases hI : ∃ J, Finsupp.mapDomain some J = I
  · obtain ⟨J, rfl⟩ := hI
    rw [MvPolynomial.coeff_rename_mapDomain _ (Option.some_injective σ)]
    exact le_supSize v p J
  · push Not at hI
    rw [MvPolynomial.coeff_rename_eq_zero _ _ _ fun J hJ => absurd hJ (hI J), map_zero]
    exact supSize_nonneg v p

private lemma IsLocalSize.companion_le {S R : Type*} [CommRing S] [CommRing R] {N : S → ℝ} {ε : ℕ}
    (h : IsLocalSize N ε) (f : R →+* S) (q : R[X]) {b : ℝ} (hb : 1 ≤ b)
    (hq : ∀ i, N (f (q.coeff i)) ≤ b) (i i' : Fin q.natDegree) :
    N (f (companion q i i')) ≤ b := by
  simp only [companion]
  split_ifs
  · rw [map_one]; exact h.one.trans hb
  · rw [map_neg, h.neg]; exact hq _
  · rw [map_zero, h.zero]; linarith

end SizeLemmas

section Degree

variable {A : Type*} [CommRing A] {τ : Type*}

open Classical in
/-- `2 ^ totalDegree p` for `p ≠ 0`, and `0` at `p = 0`: an ultrametric local size. -/
private noncomputable def degSize
    (p : MvPolynomial τ A) : ℝ := if p = 0 then 0 else 2 ^ p.totalDegree

private lemma degSize_le_iff {p : MvPolynomial τ A} (hp : p ≠ 0) (D : ℕ) :
    degSize p ≤ 2 ^ D ↔ p.totalDegree ≤ D := by
  rw [degSize, ite_eq_right hp]
  exact pow_le_pow_iff_right₀ one_lt_two

private lemma degSize_le_of_totalDegree_le {p : MvPolynomial τ A} {D : ℕ} (h : p.totalDegree ≤ D) :
    degSize p ≤ 2 ^ D := by
  unfold degSize
  split_ifs
  · positivity
  · exact pow_le_pow_right₀ one_le_two h

private lemma isLocalSize_degSize : IsLocalSize (degSize (A := A) (τ := τ)) 0 := by
  have nonneg : ∀ a : MvPolynomial τ A, 0 ≤ degSize a := fun a => by
    unfold degSize; split_ifs <;> positivity
  have add_max : ∀ a b : MvPolynomial τ A, degSize (a + b) ≤ max (degSize a) (degSize b) := by
    intro a b
    by_cases hab : a + b = 0
    · rw [degSize, ite_eq_left hab]; exact (nonneg a).trans (le_max_left _ _)
    by_cases ha : a = 0
    · subst ha; rw [zero_add]; exact le_max_right _ _
    by_cases hb : b = 0
    · subst hb; rw [add_zero]; exact le_max_left _ _
    rw [degSize, ite_eq_right hab, degSize, ite_eq_right ha, degSize, ite_eq_right hb]
    refine (pow_le_pow_right₀ one_le_two (MvPolynomial.totalDegree_add a b)).trans ?_
    rcases le_total a.totalDegree b.totalDegree with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  exact
  { nonneg := nonneg
    zero := by simp [degSize]
    one := by
      unfold degSize
      split_ifs
      · exact zero_le_one
      · rw [MvPolynomial.totalDegree_one, pow_zero]
    neg := fun a => by
      unfold degSize
      by_cases ha : a = 0
      · rw [ite_eq_left (neg_eq_zero.mpr ha), ite_eq_left ha]
      · rw [ite_eq_right (neg_ne_zero.mpr ha), ite_eq_right ha, MvPolynomial.totalDegree_neg]
    mul := fun a b => by
      by_cases hab : a * b = 0
      · rw [degSize, ite_eq_left hab]; exact mul_nonneg (nonneg a) (nonneg b)
      have ha : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
      have hb : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
      rw [degSize, ite_eq_right hab, degSize, ite_eq_right ha, degSize, ite_eq_right hb, ← pow_add]
      exact pow_le_pow_right₀ one_le_two (MvPolynomial.totalDegree_mul a b)
    add := fun a b => (add_max a b).trans (max_le_add_of_nonneg (nonneg a) (nonneg b))
    add_max := fun _ => add_max
    le_one := zero_le_one }

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ]

private lemma totalDegree_det_charMatrixOption_le (Y : MvPolynomial κ A)
    (Q : κ → (MvPolynomial σ A)[X]) {q₀ δ : ℕ}
    (hq : ∀ ν i, ((Q ν).coeff i).totalDegree ≤ q₀) (hδ : Y.totalDegree ≤ δ) :
    (charMatrixOption (kronMatrix Y Q)).det.totalDegree ≤
      Fintype.card (∀ ν, Fin (Q ν).natDegree) * (1 + q₀ * δ) := by
  classical
  set r := Fintype.card (∀ ν, Fin (Q ν).natDegree)
  have h := isLocalSize_degSize (A := A) (τ := Option σ)
  by_cases h0 : (charMatrixOption (kronMatrix Y Q)).det = 0
  · rw [h0, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
  have hnmax : ∀ ν, (Q ν).natDegree ≤ ∑ μ, (Q μ).natDegree + 1 := fun ν =>
    (Finset.single_le_sum (f := fun μ => (Q μ).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ν)).trans (Nat.le_succ _)
  have hM := kronMatrix_apply_le degSize h Y Q zero_le_one (one_le_pow₀ one_le_two :
      (1 : ℝ) ≤ 2 ^ q₀)
    (Nat.le_add_left 1 _) hnmax
    (fun m _ => degSize_le_of_totalDegree_le (D := 0)
        (by simp [MvPolynomial.totalDegree_C]) |>.trans
      (by norm_num))
    (fun ν i i' => h.companion_le _ (Q ν) (one_le_pow₀ one_le_two) (fun i =>
      degSize_le_of_totalDegree_le ((MvPolynomial.totalDegree_rename_le _ _).trans (hq ν i))) i i')
    hδ
  have hdet := h.det_le (charMatrixOption (kronMatrix Y Q)) (b := 2 ^ (1 + q₀ * δ))
    (by positivity) fun i j => by
      simp only [charMatrixOption, sub_eq_add_neg]
      refine (h.add_max rfl _ _).trans (max_le ?_ ?_)
      · split_ifs
        · refine (degSize_le_of_totalDegree_le (D := 1) ?_).trans
            (pow_le_pow_right₀ one_le_two (Nat.le_add_right _ _))
          change (MvPolynomial.monomial (Finsupp.single none 1) (1 : A)).totalDegree ≤ 1
          exact (MvPolynomial.totalDegree_monomial_le _ _).trans (by simp)
        · rw [h.zero]; positivity
      · rw [h.neg]
        refine (hM i j).trans ?_
        simp only [pow_zero, one_mul, ← pow_mul]
        exact pow_le_pow_right₀ one_le_two (by omega)
  rw [pow_zero, one_mul, ← pow_mul, mul_comm] at hdet
  exact (degSize_le_iff h0 _).mp hdet

end Degree

section Place

open NumberField

variable {F : Type*} [Field F] [NumberField F] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The integer constant of the local bound. -/
private def placeConst (r c nmax s₀ δ : ℕ) : ℕ := r.factorial * (2 * c) ^ r * (nmax * s₀) ^ (δ * r)

private lemma supSize_det_le (w : NumberFieldPlace F) (Y : MvPolynomial κ F) (hY0 : Y ≠ 0)
    (Q : κ → (MvPolynomial (Fin 2) F)[X]) {n : ℕ} (ξ : Fin n → F) {nmax s₀ δ : ℕ}
    (hnmax : 1 ≤ nmax) (hn : ∀ ν, (Q ν).natDegree ≤ nmax) (hs₀ : 1 ≤ s₀)
    (hs : ∀ ν i, ((Q ν).coeff i).support.card ≤ s₀)
    (hξ1 : ∃ l, ξ l = 1) (hξ : ∀ ν i J, ∃ l, ξ l = ((Q ν).coeff i).coeff J)
    (hδ : Y.totalDegree ≤ δ)
    (hY1 : 1 ≤ supSize w.normalizedAbv Y) :
    supSize w.normalizedAbv (charMatrixOption (kronMatrix Y Q)).det ≤
      w.normalizedAbv (placeConst (Fintype.card (∀ ν, Fin (Q ν).natDegree)) Y.support.card
          nmax s₀ δ : F) ^ w.archimedeanIndicator *
        (supSize w.normalizedAbv Y * w.vectorAbv ξ ^ δ) ^
          Fintype.card (∀ ν, Fin (Q ν).natDegree) := by
  set r := Fintype.card (∀ ν, Fin (Q ν).natDegree)
  set K := w.vectorAbv ξ with hK
  have hK1 : 1 ≤ K := by
    obtain ⟨l, hl⟩ := hξ1
    have := NumberFieldPlace.normalizedAbv_le_vectorAbv w ξ l
    rwa [hl, NumberFieldPlace.normalizedAbv_one] at this
  have hcoeff : ∀ ν i J, w.normalizedAbv (((Q ν).coeff i).coeff J) ≤ K := by
    intro ν i J
    obtain ⟨l, hl⟩ := hξ ν i J
    rw [← hl]
    exact NumberFieldPlace.normalizedAbv_le_vectorAbv w ξ l
  rcases w with w | w
  · -- a finite place
    obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv
      (.inl w : NumberFieldPlace F)
    have hna : IsNonarchimedean v := hv ▸ NumberFieldPlace.isNonarchimedean_normalizedAbv_inl w
    rw [← hv] at hY1 hcoeff ⊢
    have h := isLocalSize_supSize (τ := Option (Fin 2)) v hna
    have := det_charMatrixOption_kronMatrix_le _ h (supSize_X_le v none) Y hY0 Q hY1 hK1 hnmax hn
      (fun m _ => by rw [supSize_C]; exact le_supSize v Y m)
      (fun ν i i' => h.companion_le _ (Q ν) hK1 (fun i => (supSize_rename_some_le v _).trans
        (supSize_le v _ (by linarith) fun J => hcoeff ν i J)) i i') hδ
    simpa only [NumberFieldPlace.archimedeanIndicator_inl, pow_zero, one_mul] using this
  · -- an infinite place
    obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv
      (.inr w : NumberFieldPlace F)
    set u : AbsoluteValue F ℝ := w.1
    set t : ℝ := (w.mult : ℝ) / (Module.finrank ℚ F : ℝ) with ht_def
    have ht : 0 < t := div_pos (Nat.cast_pos.2 InfinitePlace.mult_pos)
      (Nat.cast_pos.2 Module.finrank_pos)
    have hvt : ∀ x, v x = u x ^ t := by
      intro x
      rw [hv, NumberFieldPlace.normalizedAbv_inr]
      change (u x ^ w.mult) ^ _ = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (u.nonneg x), ht_def, div_eq_mul_inv]
    rw [← hv] at hY1 hcoeff ⊢
    have hle : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → (x ≤ y ^ t⁻¹ ↔ x ^ t ≤ y) := fun hx hy =>
      Real.le_rpow_inv_iff_of_pos hx hy ht
    set Yv := supSize v Y
    set Yb := Yv ^ t⁻¹
    set Ku := K ^ t⁻¹
    have hYb : 1 ≤ Yb := Real.one_le_rpow hY1 (inv_nonneg.2 ht.le)
    have hKu : 1 ≤ Ku := Real.one_le_rpow hK1 (inv_nonneg.2 ht.le)
    have hb : 1 ≤ (s₀ : ℝ) * Ku := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hs₀) hKu
    have hcu : ∀ ν i J, u (((Q ν).coeff i).coeff J) ≤ Ku := by
      intro ν i J
      refine (hle (u.nonneg _) (by linarith)).2 ?_
      rw [← hvt]; exact hcoeff ν i J
    have h := isLocalSize_l1Size (τ := Option (Fin 2)) u
    have hdet := det_charMatrixOption_kronMatrix_le _ h (le_of_eq (l1Size_X u none)) Y hY0 Q hYb
      hb hnmax hn
      (fun m _ => by
        rw [l1Size_C]
        refine (hle (u.nonneg _) (supSize_nonneg v Y)).2 ?_
        rw [← hvt]; exact le_supSize v Y m)
      (fun ν i i' => h.companion_le _ (Q ν) hb (fun i => by
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, l1Size_rename_some]
        exact (l1Size_le_card_mul u _ (fun J => hcu ν i J)).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hs ν i) (by linarith))) i i') hδ
    have hl1 : supSize v (charMatrixOption (kronMatrix Y Q)).det ≤
        l1Size u (charMatrixOption (kronMatrix Y Q)).det ^ t :=
      supSize_le v _ (Real.rpow_nonneg (h.nonneg _) _) fun I => by
        rw [hvt]; exact Real.rpow_le_rpow (u.nonneg _) (le_l1Size u _ I) ht.le
    refine hl1.trans ((Real.rpow_le_rpow (h.nonneg _) hdet ht.le).trans (le_of_eq ?_))
    have hB : ((r.factorial : ℝ) ^ 1 * (2 ^ 1 * ((Y.support.card : ℝ) ^ 1 *
        (Yb * ((nmax : ℝ) ^ 1 * ((s₀ : ℝ) * Ku)) ^ δ))) ^ r) =
        (placeConst r Y.support.card nmax s₀ δ : ℝ) * (Yb * Ku ^ δ) ^ r := by
      simp only [placeConst]; push_cast; ring
    have hBnn : (0 : ℝ) ≤ placeConst r Y.support.card nmax s₀ δ := Nat.cast_nonneg _
    have hYbnn : 0 ≤ Yb := by positivity
    have hKunn : 0 ≤ Ku := by positivity
    rw [hB, Real.mul_rpow hBnn (by positivity), ← Real.rpow_pow_comm (by positivity),
      Real.mul_rpow hYbnn (by positivity), ← Real.rpow_pow_comm hKunn,
      Real.rpow_inv_rpow (supSize_nonneg v Y) ht.ne', Real.rpow_inv_rpow (by linarith) ht.ne',
      hvt, NumberFieldPlace.archimedeanIndicator_inr, pow_one]
    congr 2
    exact (InfinitePlace.map_natCast w _).symm

end Place

section Global

open NumberField

variable {F : Type*} [Field F] [NumberField F]

private lemma le_supSize_normalizedAbv {σ : Type*} (w : NumberFieldPlace F) (p : MvPolynomial σ F)
    (I : σ →₀ ℕ) : w.normalizedAbv (p.coeff I) ≤ supSize w.normalizedAbv p := by
  obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv w
  rw [← hv]; exact le_supSize v p I

/-- At a place, the sup size of `p` is the local size `NumberFieldPlace.mvPolynomialAbv` of the
one-element family `p`. -/
private lemma supSize_normalizedAbv {σ : Type*} (w : NumberFieldPlace F) (p : MvPolynomial σ F) :
    supSize w.normalizedAbv p = w.mvPolynomialAbv (fun _ : Unit => p) := by
  simp only [supSize, NumberFieldPlace.mvPolynomialAbv, ciSup_const]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private lemma one_le_placeConst {r c nmax s₀ δ : ℕ} (hc : 1 ≤ c) (hn : 1 ≤ nmax) (hs : 1 ≤ s₀) :
    1 ≤ placeConst r c nmax s₀ δ := by
  unfold placeConst
  exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos r) (pow_pos (by omega) _))
    (pow_pos (Nat.mul_pos hn hs) _)

/-- **The height of the characteristic polynomial.** For `Y` with a coefficient `1`, the
polynomial `χ = det (Z - kronMatrix Y Q)` over `k` has `h(χ) ≤ log B + r h(Y) + r δ h(ξ)`, where
`r` is the size of the matrix, `B = placeConst r #supp(Y) nmax s₀ δ`, and `ξ` is a vector
containing `1` and every coefficient of the `Q_ν`. -/
private lemma mvPolynomialHeight_det_le {k : Type*} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ
    k]
    [Algebra F k] (Y : MvPolynomial κ F) (hY0 : Y ≠ 0) (hY1 : ∃ m, Y.coeff m = 1)
    (Q : κ → (MvPolynomial (Fin 2) F)[X]) {n : ℕ} (ξ : Fin n → F) {nmax s₀ δ : ℕ}
    (hnmax : 1 ≤ nmax) (hn : ∀ ν, (Q ν).natDegree ≤ nmax) (hs₀ : 1 ≤ s₀)
    (hs : ∀ ν i, ((Q ν).coeff i).support.card ≤ s₀)
    (hξ1 : ∃ l, ξ l = 1) (hξ : ∀ ν i J, ∃ l, ξ l = ((Q ν).coeff i).coeff J)
    (hδ : Y.totalDegree ≤ δ)
    (hχ : MvPolynomial.map (algebraMap F k) (charMatrixOption (kronMatrix Y Q)).det ≠ 0)
    (hYk : MvPolynomial.map (algebraMap F k) Y ≠ 0) (hξk : algebraMap F k ∘ ξ ≠ 0) :
    mvPolynomialHeight _ hχ ≤
      Real.log (placeConst (Fintype.card (∀ ν, Fin (Q ν).natDegree)) Y.support.card
          nmax s₀ δ) +
        Fintype.card (∀ ν, Fin (Q ν).natDegree) * mvPolynomialHeight _ hYk +
        Fintype.card (∀ ν, Fin (Q ν).natDegree) * δ *
          weilHeight (Projectivization.mk k (algebraMap F k ∘ ξ) hξk) := by
  set r := Fintype.card (∀ ν, Fin (Q ν).natDegree)
  set B := placeConst r Y.support.card nmax s₀ δ
  set χ := (charMatrixOption (kronMatrix Y Q)).det
  have hχ0 : χ ≠ 0 := fun h => hχ (by rw [h, map_zero])
  have hB1 : 1 ≤ B := one_le_placeConst
    (Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hY0)) hnmax hs₀
  have hξ0 : ξ ≠ 0 := fun h => hξk (by rw [h]; funext; simp)
  rw [mvPolynomialHeight_eq_finsum _ _ χ rfl, mvPolynomialHeight_eq_finsum _ _ Y rfl,
    weilHeight_eq_sumLocalHeight (y := ξ) hξk rfl, sumLocalHeight]
  have hlogB := NumberFieldPlace.finsum_archimedeanIndicator_mul_log_normalizedAbv_intCast (K := F)
    (r := (B : ℤ)) (by exact_mod_cast hB1)
  simp only [Int.cast_natCast] at hlogB
  rw [← hlogB, mul_finsum, mul_finsum]
  have hf1 := finite_support_log_mvPolynomialAbv χ hχ0
  have hf2 := finite_support_log_mvPolynomialAbv Y hY0
  have hf3 := NumberFieldPlace.finite_support_localHeight hξ0
  have hf4 : (Function.support fun w : NumberFieldPlace F =>
      (w.archimedeanIndicator : ℝ) * Real.log (w.normalizedAbv (B : F))).Finite := by
    refine (Set.finite_range (Sum.inr : InfinitePlace F → NumberFieldPlace F)).subset ?_
    rintro (w | w) hw
    · simp [NumberFieldPlace.archimedeanIndicator_inl] at hw
    · exact ⟨w, rfl⟩
  have hsub : ∀ (c : ℝ) (f : NumberFieldPlace F → ℝ),
      Function.support (fun w => c * f w) ⊆ Function.support f :=
    fun c f w hw h0 => hw (by simp [h0])
  have hf2' := hf2.subset (hsub r _)
  have hf3' := hf3.subset (hsub (r * δ) _)
  have hf5 := (hf4.union hf2').subset (Function.support_add _ _)
  rw [← finsum_add_distrib hf4 hf2', ← finsum_add_distrib hf5 hf3']
  refine finsum_le_finsum' hf1 ((hf5.union hf3').subset (Function.support_add _ _)) fun w => ?_
  obtain ⟨m, hm⟩ := hY1
  have hY1' : 1 ≤ supSize w.normalizedAbv Y := by
    have := le_supSize_normalizedAbv w Y m
    rwa [hm, NumberFieldPlace.normalizedAbv_one] at this
  have hb := supSize_det_le w Y hY0 Q ξ hnmax hn hs₀ hs hξ1 hξ hδ hY1'
  rw [supSize_normalizedAbv, supSize_normalizedAbv] at hb
  have hK1 : 1 ≤ w.vectorAbv ξ := by
    obtain ⟨l, hl⟩ := hξ1
    have := NumberFieldPlace.normalizedAbv_le_vectorAbv w ξ l
    rwa [hl, NumberFieldPlace.normalizedAbv_one] at this
  have hvB : 0 < w.normalizedAbv (B : F) :=
    NumberFieldPlace.normalizedAbv_pos w (Nat.cast_ne_zero.2 (by omega))
  have hY := mvPolynomialAbv_pos w Y hY0
  have h1 := Real.log_le_log (mvPolynomialAbv_pos w χ hχ0) hb
  rw [Real.log_mul (pow_pos hvB _).ne' (pow_pos (by positivity) _).ne', Real.log_pow,
    Real.log_pow, Real.log_mul hY.ne' (pow_pos (by positivity) _).ne', Real.log_pow] at h1
  simp only [NumberFieldPlace.localHeight]
  nlinarith [h1]

end Global

section Norm

open scoped IntermediateField.algebraAdjoinAdjoin in
private lemma exists_norm_eq {k L : Type*} [Field k] [Field L] [Algebra k L] {α β : L}
    (hinj : Function.Injective (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L))
    {y : L} (χ : (MvPolynomial (Fin 2) k)[X]) (hχ : χ.Monic)
    (hχy : χ.eval₂ (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L).toRingHom y = 0) :
    ∃ μ : (MvPolynomial (Fin 2) k)[X], μ.Monic ∧ μ ∣ χ ∧ ∃ d e : ℕ,
      e ≤ Module.finrank (IntermediateField.adjoin k {α, β}) L ∧
      (Algebra.norm (IntermediateField.adjoin k {α, β}) y : L) =
        MvPolynomial.aeval ![α, β] (((-1) ^ d * μ.coeff 0) ^ e) := by
  set E := IntermediateField.adjoin k ({α, β} : Set L)
  by_cases hfin : FiniteDimensional E L
  swap
  · refine ⟨χ, hχ, dvd_rfl, 0, 0, Nat.zero_le _, ?_⟩
    rw [Algebra.norm_eq_one_of_not_module_finite hfin, pow_zero, map_one]
    rfl
  set A := Algebra.adjoin k ({α, β} : Set L)
  have hA : A = (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty]
    rfl
  let e : MvPolynomial (Fin 2) k ≃ₐ[k] A :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hA.symm)
  have he : ∀ p, ((e p : A) : L) = MvPolynomial.aeval ![α, β] p := fun p => rfl
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set χ' : A[X] := χ.map (e : MvPolynomial (Fin 2) k →+* A)
  have hχ'y : aeval y χ' = 0 := by
    rw [Polynomial.aeval_def, eval₂_map]
    convert hχy using 2
    exact RingHom.ext he
  have hyA : IsIntegral A y := ⟨χ', hχ.map _, hχ'y⟩
  have hdvd : minpoly A y ∣ χ' := minpoly.isIntegrallyClosed_dvd hyA hχ'y
  have hmin : minpoly E y = (minpoly A y).map (algebraMap A E) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' E hyA
  set μ := (minpoly A y).map (e.symm : A →+* MvPolynomial (Fin 2) k)
  have hμχ : μ ∣ χ := by
    have : χ = χ'.map (e.symm : A →+* MvPolynomial (Fin 2) k) := by
      rw [Polynomial.map_map]
      refine (Polynomial.map_id).symm.trans ?_
      congr 1
      exact RingHom.ext fun x => (e.symm_apply_apply x).symm
    rw [this]
    exact Polynomial.map_dvd _ hdvd
  have hyE : IsIntegral E y := .of_finite E y
  refine ⟨μ, (minpoly.monic hyA).map _, hμχ, (minpoly E y).natDegree,
    Module.finrank (IntermediateField.adjoin E {y}) L, ?_, ?_⟩
  · have := IntermediateField.adjoin.finiteDimensional hyE
    have h1 := Module.finrank_mul_finrank E (IntermediateField.adjoin E {y}) L
    have h2 : 0 < Module.finrank E (IntermediateField.adjoin E {y}) := Module.finrank_pos
    rw [← h1]
    exact Nat.le_mul_of_pos_left _ h2
  · have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hyE)
    rw [IntermediateField.adjoin.powerBasis_dim, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen] at hpb
    rw [Algebra.norm_eq_norm_adjoin E y, hpb]
    simp only [map_pow, map_mul, map_neg, map_one, μ, Polynomial.coeff_map, ← he, hmin]
    have hc : e ((e.symm : A →+* MvPolynomial (Fin 2) k) ((minpoly A y).coeff 0)) =
        (minpoly A y).coeff 0 := e.apply_symm_apply _
    rw [hc]
    push_cast
    rfl

end Norm

section Heights

open NumberField

variable {k : Type*} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]

private lemma polynomialFamilyHeight_congr {σ ι : Type*} [Fintype ι] {P Q : ι → MvPolynomial σ k}
    (h : P = Q) (hP : ∃ i, P i ≠ 0) (hQ : ∃ i, Q i ≠ 0) :
    polynomialFamilyHeight P hP = polynomialFamilyHeight Q hQ := by
  subst h; rfl

/-- A finite subset of `k` lies in a subfield of `k` that is a number field. -/
private lemma exists_numberField (S : Set k) (hS : S.Finite) :
    ∃ F : IntermediateField ℚ k, FiniteDimensional ℚ F ∧ S ⊆ F :=
  ⟨IntermediateField.adjoin ℚ S, by
    have : Finite S := hS.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral,
    IntermediateField.subset_adjoin ℚ S⟩

omit [Algebra.IsAlgebraic ℚ k] in
private lemma numberField_of_finiteDimensional (F : IntermediateField ℚ k)
    (hF : FiniteDimensional ℚ F) :
    NumberField F :=
  { to_finiteDimensional := by convert hF; exact Subsingleton.elim _ _ }

omit [Algebra.IsAlgebraic ℚ k] in
private lemma exists_map_eq_of_coeffs_subset {σ : Type*} (F : IntermediateField ℚ k)
    (Q : MvPolynomial σ k) (hQ : (Q.coeffs : Set k) ⊆ F) :
    ∃ Q' : MvPolynomial σ F, MvPolynomial.map (algebraMap F k) Q' = Q :=
  MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun c hc => ⟨⟨c, hQ hc⟩, rfl⟩

private lemma supSize_C_mul {F : Type*} [Field F] {σ : Type*} (v : AbsoluteValue F ℝ) (a : F)
    (Q : MvPolynomial σ F) : supSize v (MvPolynomial.C a * Q) = v a * supSize v Q := by
  simp only [supSize, MvPolynomial.coeff_C_mul, map_mul]
  exact (Real.mul_iSup_of_nonneg (v.nonneg a) _).symm

private lemma mvPolynomialHeight_C_mul {σ : Type*} {a : k} (ha : a ≠ 0) (Q : MvPolynomial σ k)
    (hQ : Q ≠ 0) (haQ : MvPolynomial.C a * Q ≠ 0) :
    mvPolynomialHeight (MvPolynomial.C a * Q) haQ = mvPolynomialHeight Q hQ := by
  classical
  obtain ⟨F, hF, hSF⟩ := exists_numberField (insert a (Q.coeffs : Set k))
    ((Q.coeffs.finite_toSet).insert a)
  have := numberField_of_finiteDimensional F hF
  obtain ⟨Q', hQ'⟩ := exists_map_eq_of_coeffs_subset F Q
    (fun c hc => hSF (Set.mem_insert_of_mem _ hc))
  set a' : F := ⟨a, hSF (Set.mem_insert _ _)⟩
  have ha' : a' ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have hQ'0 : Q' ≠ 0 := by rintro rfl; exact hQ (by simp [← hQ'])
  rw [mvPolynomialHeight_eq_finsum _ _ (MvPolynomial.C a' * Q')
      (by rw [map_mul, MvPolynomial.map_C, hQ']; rfl),
    mvPolynomialHeight_eq_finsum _ _ Q' hQ']
  have hsplit : ∀ w : NumberFieldPlace F,
      Real.log (w.mvPolynomialAbv fun _ : Unit => MvPolynomial.C a' * Q') =
        Real.log (w.normalizedAbv a') + Real.log (w.mvPolynomialAbv fun _ : Unit => Q') := by
    intro w
    have h1 := mvPolynomialAbv_pos w Q' hQ'0
    rw [← supSize_normalizedAbv] at h1
    rw [← supSize_normalizedAbv, ← supSize_normalizedAbv]
    obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv w
    rw [← hv] at h1 ⊢
    rw [supSize_C_mul, Real.log_mul (v.pos ha').ne' h1.ne']
  simp_rw [hsplit]
  rw [finsum_add_distrib (finite_support_log_normalizedAbv ha')
    (finite_support_log_mvPolynomialAbv Q' hQ'0), finsum_log_normalizedAbv ha', zero_add]

/-- `h(1) = 0`, from Gelfond's inequality `2 h(1) ≤ h(1 · 1)`. -/
private lemma mvPolynomialHeight_one {σ : Type*} [Finite σ] (h : (1 : MvPolynomial σ k) ≠ 0) :
    mvPolynomialHeight (1 : MvPolynomial σ k) h = 0 := by
  have := Fintype.ofFinite σ
  have := sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod (σ := σ)
    (fun _ : Fin 2 => (1 : MvPolynomial σ k)) fun _ => h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.prod_const_one,
    MvPolynomial.degreeOf_one, smul_zero, Nat.cast_zero, zero_mul, sub_zero, nsmul_eq_mul,
    Nat.cast_ofNat] at this
  linarith [mvPolynomialHeight_nonneg (1 : MvPolynomial σ k) h]

private lemma mvPolynomialHeight_pow_le {σ : Type*} [Fintype σ] (Q : MvPolynomial σ k) (hQ : Q ≠ 0)
    {e : ℕ} (he : 1 ≤ e) (hQe : Q ^ e ≠ 0) :
    mvPolynomialHeight (Q ^ e) hQe ≤
      e * mvPolynomialHeight Q hQ + ((e - 1) * (Fintype.card σ * Q.totalDegree) : ℕ) *
        Real.log 2 := by
  classical
  let P : Unit → Fin e → MvPolynomial σ k := fun _ _ => Q
  have hP : ∀ j, ∃ a, P a j ≠ 0 := fun _ => ⟨(), hQ⟩
  have hprod : ∃ a, ∏ j, P a j ≠ 0 := ⟨(), by simpa [P] using hQe⟩
  have key := polynomialFamilyHeight_prod_le P hP hprod ⟨0, he⟩
    (((e - 1) * (Fintype.card σ * Q.totalDegree) : ℕ) : ℝ) fun a _ => by
      have h1 : ∏ j ∈ Finset.univ.erase (⟨0, he⟩ : Fin e), P a j = Q ^ (e - 1) := by
        simp [P, Finset.prod_const, Finset.card_erase_of_mem]
      rw [h1]
      norm_cast
      calc ∑ μ : σ, (Q ^ (e - 1)).degreeOf μ ≤ ∑ _μ : σ, (e - 1) * Q.totalDegree :=
            Finset.sum_le_sum fun μ _ => (MvPolynomial.degreeOf_le_totalDegree _ μ).trans
              (MvPolynomial.totalDegree_pow _ _)
        _ = (e - 1) * (Fintype.card σ * Q.totalDegree) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
  have hL : polynomialFamilyHeight (fun a => ∏ j, P a j) hprod = mvPolynomialHeight (Q ^ e) hQe :=
    polynomialFamilyHeight_congr (funext fun _ => by simp [P]) _ _
  have hR : ∀ j, polynomialFamilyHeight (fun a => P a j) (hP j) = mvPolynomialHeight Q hQ :=
    fun j => rfl
  rw [hL] at key
  simpa only [hR, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using key

/-- The height of the coefficient of `Z ^ 0` is at most the height of the polynomial. -/
private lemma mvPolynomialHeight_coeff_zero_le {σ : Type*} (Q : MvPolynomial (Option σ) k)
    (hQ : Q ≠ 0)
    (h0 : (MvPolynomial.optionEquivLeft k σ Q).coeff 0 ≠ 0) :
    mvPolynomialHeight ((MvPolynomial.optionEquivLeft k σ Q).coeff 0) h0 ≤
      mvPolynomialHeight Q hQ := by
  classical
  set c := (MvPolynomial.optionEquivLeft k σ Q).coeff 0
  have hc : ∀ I, c.coeff I = Q.coeff (Finsupp.optionElim 0 I) := fun I =>
    MvPolynomial.optionEquivLeft_coeff_coeff k Q 0 I
  unfold mvPolynomialHeight polynomialFamilyHeight
  let : LinearOrder (Σ _ : Unit, Q.support) := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (Σ _ : Unit, c.support) := IsWellOrder.linearOrder WellOrderingRel
  let v : (Σ _ : Unit, Q.support) → k := fun p => Q.coeff p.2.1
  let f : (Σ _ : Unit, c.support) → (Σ _ : Unit, Q.support) := fun p =>
    ⟨(), Finsupp.optionElim 0 p.2.1, by
      rw [MvPolynomial.mem_support_iff, ← hc]; exact MvPolynomial.mem_support_iff.mp p.2.2⟩
  have hvf : (fun p : Σ _ : Unit, c.support => c.coeff p.2.1) = v ∘ f :=
    funext fun p => hc _
  have hne : v ∘ f ≠ 0 := by
    rw [← hvf]
    obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp h0
    exact Function.ne_iff.mpr ⟨⟨(), I, MvPolynomial.mem_support_iff.mpr hI⟩, hI⟩
  convert weilHeight_mk_comp_le v f hne using 3

/-- Gelfond's inequality for a factor. -/
private lemma mvPolynomialHeight_le_of_mul_eq {σ : Type*} [Fintype σ] {A B C : MvPolynomial σ k}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (h : A * B = C) :
    mvPolynomialHeight A hA ≤
      mvPolynomialHeight C hC + (Fintype.card σ * C.totalDegree : ℕ) * Real.log 2 := by
  have key := sum_mvPolynomialHeight_sub_le_mvPolynomialHeight_prod (σ := σ) ![A, B]
    (fun j => by fin_cases j <;> simpa)
  have hprod : ∏ j, ![A, B] j = C := by rw [Fin.prod_univ_two]; simpa using h
  rw [mvPolynomialHeight_congr hprod _ hC, Fin.sum_univ_two] at key
  have hB0 := mvPolynomialHeight_nonneg B hB
  have hdeg : ((∑ μ : σ, (∏ j, ![A, B] j).degreeOf μ : ℕ) : ℝ) ≤
      (Fintype.card σ * C.totalDegree : ℕ) := by
    rw [hprod]
    norm_cast
    calc ∑ μ : σ, C.degreeOf μ ≤ ∑ _μ : σ, C.totalDegree :=
          Finset.sum_le_sum fun μ _ => MvPolynomial.degreeOf_le_totalDegree _ μ
      _ = Fintype.card σ * C.totalDegree := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have : mvPolynomialHeight (![A, B] 0) (by simpa) = mvPolynomialHeight A hA := rfl
  have : mvPolynomialHeight (![A, B] 1) (by simpa) = mvPolynomialHeight B hB := rfl
  nlinarith [mul_le_mul_of_nonneg_right hdeg hl2]

private lemma totalDegree_coeff_optionEquivLeft_le {R σ : Type*} [CommSemiring R]
    (Q : MvPolynomial (Option σ) R) (n : ℕ) :
    ((MvPolynomial.optionEquivLeft R σ Q).coeff n).totalDegree ≤ Q.totalDegree := by
  refine Finset.sup_le fun I hI => ?_
  have hI' : Finsupp.optionElim n I ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff, ← MvPolynomial.optionEquivLeft_coeff_coeff]
    exact MvPolynomial.mem_support_iff.mp hI
  refine le_trans ?_ (MvPolynomial.le_totalDegree hI')
  rw [Finsupp.sum_option_index _ _ (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
  exact Nat.le_add_left _ _

private lemma totalDegree_map_of_injective {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {f : R →+* S} (hf : Function.Injective f) (p : MvPolynomial σ R) :
    (MvPolynomial.map f p).totalDegree = p.totalDegree := by
  classical
  simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective _ hf]

/-- The polynomial part of the argument: the height of `((-1) ^ d μ(0)) ^ e` for a monic
divisor `μ` of a monic `χ`. -/
private lemma mvPolynomialHeight_pow_coeff_zero_le (χ μ : (MvPolynomial (Fin 2) k)[X])
    (hχ : χ.Monic)
    (hμ : μ.Monic) (hμχ : μ ∣ χ) (d e : ℕ) (hP : ((-1) ^ d * μ.coeff 0) ^ e ≠ 0)
    (hχ' : (MvPolynomial.optionEquivLeft k (Fin 2)).symm χ ≠ 0) :
    mvPolynomialHeight _ hP ≤
      e * (mvPolynomialHeight _ hχ' +
        (3 * ((MvPolynomial.optionEquivLeft k (Fin 2)).symm χ).totalDegree : ℕ) * Real.log 2) +
      (2 * e * ((MvPolynomial.optionEquivLeft k (Fin 2)).symm χ).totalDegree : ℕ) *
        Real.log 2 := by
  set Φ := (MvPolynomial.optionEquivLeft k (Fin 2)).symm
  set T := (Φ χ).totalDegree
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hH := mvPolynomialHeight_nonneg _ hχ'
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [mvPolynomialHeight_congr (pow_zero _) hP one_ne_zero, mvPolynomialHeight_one]
    simp
  set c₀ := μ.coeff 0
  have hc₀ : c₀ ≠ 0 := fun h => hP (by rw [h, mul_zero, zero_pow he.ne'])
  have hsign : ((-1) ^ d * c₀) ^ e = MvPolynomial.C ((-1) ^ (d * e)) * c₀ ^ e := by
    rw [mul_pow, ← pow_mul, map_pow, map_neg, map_one]
  have hce : c₀ ^ e ≠ 0 := pow_ne_zero _ hc₀
  rw [mvPolynomialHeight_congr hsign hP (by rw [← hsign]; exact hP),
    mvPolynomialHeight_C_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) _ hce]
  have h1 := mvPolynomialHeight_pow_le c₀ hc₀ he hce
  obtain ⟨ρ, hρ⟩ := hμχ
  have hμ0 : Φ μ ≠ 0 := fun h => hμ.ne_zero (Φ.injective (h.trans (map_zero Φ).symm))
  have hρ0 : Φ ρ ≠ 0 := by
    intro h
    have : ρ = 0 := Φ.injective (h.trans (map_zero Φ).symm)
    exact hχ.ne_zero (by rw [hρ, this, mul_zero])
  have hmul : Φ μ * Φ ρ = Φ χ := by rw [hρ, map_mul]
  have h2 := mvPolynomialHeight_le_of_mul_eq hμ0 hρ0 hχ' hmul
  have hc₀' : (MvPolynomial.optionEquivLeft k (Fin 2) (Φ μ)).coeff 0 = c₀ := by
    simp only [Φ, AlgEquiv.apply_symm_apply]; rfl
  have h3 := mvPolynomialHeight_coeff_zero_le (Φ μ) hμ0 (by rw [hc₀']; exact hc₀)
  rw [mvPolynomialHeight_congr hc₀' _ hc₀] at h3
  have hdeg : c₀.totalDegree ≤ T := by
    have := totalDegree_coeff_optionEquivLeft_le (Φ μ) 0
    rw [hc₀'] at this
    refine this.trans ?_
    change _ ≤ (Φ χ).totalDegree
    rw [← hmul, MvPolynomial.totalDegree_mul_of_isDomain hμ0 hρ0]
    exact Nat.le_add_right _ _
  simp only [Fintype.card_fin, Fintype.card_option] at h1 h2
  have hdeg' : (((e - 1) * (2 * c₀.totalDegree) : ℕ) : ℝ) ≤ ((2 * e * T : ℕ) : ℝ) := by
    norm_cast
    calc (e - 1) * (2 * c₀.totalDegree) ≤ e * (2 * T) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul_left _ hdeg)
      _ = 2 * e * T := by ring
  have he' : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  calc mvPolynomialHeight (c₀ ^ e) hce
      ≤ e * mvPolynomialHeight c₀ hc₀ + (((e - 1) *
          (2 * c₀.totalDegree) : ℕ) : ℝ) * Real.log 2 := h1
    _ ≤ e * (mvPolynomialHeight _ hχ' + ((3 * T : ℕ) : ℝ) * Real.log 2) +
          ((2 * e * T : ℕ) : ℝ) * Real.log 2 := by
        gcongr
        exact h3.trans h2

end Heights

section Aux

private lemma charMatrixOption_map {A B σ ρ : Type*} [CommRing A] [CommRing B]
    [DecidableEq ρ]
    (f : A →+* B) (M : Matrix ρ ρ (MvPolynomial σ A)) :
    charMatrixOption (M.map (MvPolynomial.map f)) =
      (charMatrixOption M).map (MvPolynomial.map f) := by
  ext i j
  simp only [charMatrixOption, Matrix.map_apply, map_sub, MvPolynomial.map_rename]
  split_ifs <;> simp

private lemma card_support_le_of_totalDegree_le {R κ : Type*} [CommSemiring R] [Fintype κ]
    (Y : MvPolynomial κ R) {δ : ℕ} (hδ : Y.totalDegree ≤ δ) :
    Y.support.card ≤ (δ + 1) ^ Fintype.card κ := by
  classical
  have hsub : Y.support ⊆ Finset.univ.image (fun f : κ → Fin (δ + 1) =>
      Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ))) := by
    intro m hm
    have hle : ∀ i, m i ≤ δ := fun i => by
      refine le_trans ?_ (le_trans (MvPolynomial.le_totalDegree hm) hδ)
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine Finset.mem_image.mpr ⟨fun i => ⟨m i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩
    ext i
    simp
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

private lemma weilHeight_congr {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {ι : Type*} [Fintype ι] [LinearOrder ι] {v w : ι → K} (h : v = w) (hv : v ≠ 0) (hw : w ≠ 0) :
    Faltings.weilHeight (Projectivization.mk K v hv) = Faltings.weilHeight
        (Projectivization.mk K w hw) := by
  subst h; rfl

end Aux

section Core

variable {k L : Type*} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [Field L] [Algebra k L]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The finite set of coefficients of the coefficients of the `Q ν`, together with `0` and `1`. -/
private noncomputable def coeffSet (Q : κ → (MvPolynomial (Fin 2) k)[X]) : Finset k := by
  classical
  exact insert 0 (insert 1 (Finset.univ.biUnion fun ν =>
    (Finset.range ((Q ν).natDegree + 1)).biUnion fun i => ((Q ν).coeff i).coeffs))

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma coeff_mem_coeffSet (Q : κ → (MvPolynomial (Fin 2) k)[X]) (ν : κ) (i : ℕ)
    (J : Fin 2 →₀ ℕ) : ((Q ν).coeff i).coeff J ∈ coeffSet Q := by
  classical
  unfold coeffSet
  by_cases h : ((Q ν).coeff i).coeff J = 0
  · rw [h]; exact Finset.mem_insert_self _ _
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  have hi : (Q ν).coeff i ≠ 0 := fun h' => h (by rw [h', MvPolynomial.coeff_zero, Finsupp.zero_apply])
  refine Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hi))
  · exact MvPolynomial.coeff_mem_coeffs _ h

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma one_mem_coeffSet (Q : κ → (MvPolynomial (Fin 2) k)[X]) : (1 : k) ∈ coeffSet Q := by
  classical
  unfold coeffSet
  exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The vector of elements of `coeffSet Q`. -/
private noncomputable def coeffVec (Q : κ → (MvPolynomial (Fin 2) k)[X]) : Fin
    (coeffSet Q).card → k :=
  fun l => ((coeffSet Q).equivFin.symm l : k)

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma exists_coeffVec_eq {Q : κ → (MvPolynomial (Fin 2) k)[X]} {x : k}
    (hx : x ∈ coeffSet Q) :
    ∃ l, coeffVec Q l = x :=
  ⟨(coeffSet Q).equivFin ⟨x, hx⟩, by simp [coeffVec]⟩

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma coeffVec_ne_zero (Q : κ → (MvPolynomial (Fin 2) k)[X]) : coeffVec Q ≠ 0 :=
  fun h => one_ne_zero <| (exists_coeffVec_eq (one_mem_coeffSet Q)).choose_spec.symm.trans
    (congrFun h _)

/-- A bound `∑_ν deg Q_ν + 1 ≥ 1` for the degrees of the `Q_ν`. -/
private noncomputable def nmaxQ (Q : κ → (MvPolynomial (Fin 2) k)[X]) : ℕ :=
  ∑ ν, (Q ν).natDegree + 1

/-- A bound `≥ 1` for the number of monomials of every coefficient of every `Q_ν`. -/
private noncomputable def s0Q (Q : κ → (MvPolynomial (Fin 2) k)[X]) : ℕ :=
  ∑ ν, ∑ i ∈ Finset.range ((Q ν).natDegree + 1), ((Q ν).coeff i).support.card + 1

/-- A bound for the total degrees of the coefficients of the `Q_ν`. -/
private noncomputable def q0Q (Q : κ → (MvPolynomial (Fin 2) k)[X]) : ℕ :=
  ∑ ν, ∑ i ∈ Finset.range ((Q ν).natDegree + 1), ((Q ν).coeff i).totalDegree

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma natDegree_le_nmaxQ (Q : κ → (MvPolynomial (Fin 2) k)[X]) (ν : κ) :
    (Q ν).natDegree ≤ nmaxQ Q :=
  (Finset.single_le_sum (f := fun μ => (Q μ).natDegree) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ν)).trans (Nat.le_succ _)

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma le_double_sum {Q : κ → (MvPolynomial (Fin 2) k)[X]} (f : κ → ℕ → ℕ) (hf : ∀ ν i,
    (Q ν).natDegree < i → f ν i = 0) (ν : κ) (i : ℕ) :
    f ν i ≤ ∑ μ, ∑ j ∈ Finset.range ((Q μ).natDegree + 1), f μ j := by
  by_cases hi : i ≤ (Q ν).natDegree
  · refine le_trans ?_ (Finset.single_le_sum (f := fun μ =>
      ∑ j ∈ Finset.range ((Q μ).natDegree + 1), f μ j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ν))
    exact Finset.single_le_sum (f := fun j => f ν j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · exact (hf ν i (by omega)).le.trans (Nat.zero_le _)

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma card_support_coeff_le_s0Q (Q : κ → (MvPolynomial (Fin 2) k)[X]) (ν : κ) (i : ℕ) :
    ((Q ν).coeff i).support.card ≤ s0Q Q :=
  (le_double_sum (Q := Q) (fun ν i => ((Q ν).coeff i).support.card) (fun ν i hi => by
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]) ν i).trans (Nat.le_succ _)

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] [DecidableEq κ] in
private lemma totalDegree_coeff_le_q0Q (Q : κ → (MvPolynomial (Fin 2) k)[X]) (ν : κ) (i : ℕ) :
    ((Q ν).coeff i).totalDegree ≤ q0Q Q :=
  le_double_sum (Q := Q) (fun ν i => ((Q ν).coeff i).totalDegree) (fun ν i hi => by
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]) ν i

omit [DecidableEq κ] in
/-- The estimate for a normalized `Y`. -/
private lemma height_norm_le_of_coeff_eq_one {α β : L}
    (hinj : Function.Injective (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (θ : κ → L) (Q : κ → (MvPolynomial (Fin 2) k)[X]) (hQ : ∀ ν, (Q ν).Monic)
    (hθ : ∀ ν, (Q ν).eval₂ (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L).toRingHom
      (θ ν) = 0)
    (Y : MvPolynomial κ k) (hY : Y ≠ 0) {m₀ : κ →₀ ℕ} (hm₀ : Y.coeff m₀ = 1) (δ : ℕ)
    (hδ : Y.totalDegree ≤ δ) (P : MvPolynomial (Fin 2) k) (hP : P ≠ 0)
    (hPeq : MvPolynomial.aeval ![α, β] P =
        (Algebra.norm (IntermediateField.adjoin k {α, β}) (MvPolynomial.aeval θ Y) : L)) :
    mvPolynomialHeight P hP ≤
      Module.finrank (IntermediateField.adjoin k {α, β}) L *
        (Real.log (placeConst (∏ ν, (Q ν).natDegree) Y.support.card (nmaxQ Q) (s0Q Q) δ) +
          (∏ ν, (Q ν).natDegree : ℕ) * mvPolynomialHeight Y hY +
          (∏ ν, (Q ν).natDegree : ℕ) * δ *
            weilHeight (Projectivization.mk k (coeffVec Q) (coeffVec_ne_zero Q)) +
          ((5 * ((∏ ν, (Q ν).natDegree) * (1 + q0Q Q * δ)) : ℕ) : ℝ) * Real.log 2) := by
  classical
  set φ := (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L)
  -- a number field containing all the coefficients
  obtain ⟨F, hF, hSF⟩ := exists_numberField ((Y.coeffs : Set k) ∪ (coeffSet Q : Set k))
    (Y.coeffs.finite_toSet.union (coeffSet Q).finite_toSet)
  have := numberField_of_finiteDimensional F hF
  obtain ⟨YF, hYF⟩ := exists_map_eq_of_coeffs_subset F Y (fun c hc => hSF (Or.inl hc))
  have hlift : ∀ ν, Q ν ∈ Polynomial.lifts (MvPolynomial.map (algebraMap F k)) := fun ν => by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨J, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact ⟨⟨_, hSF (Or.inr (coeff_mem_coeffSet Q ν i J))⟩, rfl⟩
  choose QF hQFmap hQFdeg hQFmonic using fun ν =>
    Polynomial.lifts_and_natDegree_eq_and_monic (hlift ν) (hQ ν)
  set ψ : MvPolynomial (Fin 2) F →ₐ[F] L := MvPolynomial.aeval ![α, β]
  have hψ' : (φ : MvPolynomial (Fin 2) k →+* L).comp (MvPolynomial.map (algebraMap F k)) =
      (ψ : MvPolynomial (Fin 2) F →+* L) :=
    RingHom.ext fun p => MvPolynomial.aeval_map_algebraMap k ![α, β] p
  have hθF : ∀ ν, (QF ν).eval₂ (ψ : MvPolynomial (Fin 2) F →+* L) (θ ν) = 0 := by
    intro ν
    rw [← hψ', ← Polynomial.eval₂_map, hQFmap]
    exact hθ ν
  have hy : MvPolynomial.aeval θ YF = MvPolynomial.aeval θ Y := by
    rw [← hYF, MvPolynomial.aeval_map_algebraMap]
  set M := kronMatrix YF QF
  have hχF := eval₂_charpoly_kronMatrix ψ YF hQFmonic hθF
  set χ := M.charpoly.map (MvPolynomial.map (algebraMap F k))
  have hχmon : χ.Monic := (Matrix.charpoly_monic M).map _
  have hχy : χ.eval₂ φ.toRingHom (MvPolynomial.aeval θ Y) = 0 := by
    rw [Polynomial.eval₂_map, ← hy, AlgHom.toRingHom_eq_coe, hψ']
    exact hχF
  obtain ⟨μ, hμ, hμχ, d, e, he, hnorm⟩ := exists_norm_eq hinj χ hχmon hχy
  have hPμ : P = ((-1) ^ d * μ.coeff 0) ^ e := hinj (hPeq.trans hnorm)
  have hP' : ((-1) ^ d * μ.coeff 0) ^ e ≠ 0 := hPμ ▸ hP
  rw [mvPolynomialHeight_congr hPμ hP hP']
  set Φ := (MvPolynomial.optionEquivLeft k (Fin 2)).symm
  have hχ' : Φ χ = MvPolynomial.map (algebraMap F k) (charMatrixOption M).det := by
    rw [show χ = (M.map (MvPolynomial.map (algebraMap F k))).charpoly from
      (Matrix.charpoly_map _ _).symm, optionEquivLeft_symm_charpoly, charMatrixOption_map,
      RingHom.map_det]
    rfl
  have hχ'0 : Φ χ ≠ 0 := fun h => hχmon.ne_zero (Φ.injective (h.trans (map_zero _).symm))
  have hdet0 : MvPolynomial.map (algebraMap F k) (charMatrixOption M).det ≠ 0 := hχ' ▸ hχ'0
  have key := mvPolynomialHeight_pow_coeff_zero_le χ μ hχmon hμ hμχ d e hP' hχ'0
  set r := ∏ ν, (Q ν).natDegree
  have hr : Fintype.card (∀ ν, Fin (QF ν).natDegree) = r := by
    simp [Fintype.card_pi, hQFdeg, r]
  have hinjF := (algebraMap F k).injective
  have hYF0 : YF ≠ 0 := by rintro rfl; exact hY (by rw [← hYF, map_zero])
  have hm₀F : YF.coeff m₀ = 1 :=
    hinjF (by rw [← MvPolynomial.coeff_map, hYF, hm₀, map_one])
  have hδF : YF.totalDegree ≤ δ := by
    rwa [← totalDegree_map_of_injective hinjF, hYF]
  have hsuppF : YF.support.card = Y.support.card := by
    rw [← hYF, MvPolynomial.support_map_of_injective _ hinjF]
  have hmemS : ∀ l, coeffVec Q l ∈ F := fun l =>
    hSF (Or.inr ((coeffSet Q).equivFin.symm l).2)
  let ξF : Fin (coeffSet Q).card → F := fun l => ⟨coeffVec Q l, hmemS l⟩
  have hξF : algebraMap F k ∘ ξF = coeffVec Q := rfl
  have hξF1 : ∃ l, ξF l = 1 := by
    obtain ⟨l, hl⟩ := exists_coeffVec_eq (one_mem_coeffSet Q)
    exact ⟨l, Subtype.ext hl⟩
  have hQc : ∀ ν i J, algebraMap F k (((QF ν).coeff i).coeff J) = ((Q ν).coeff i).coeff J := by
    intro ν i J
    rw [← hQFmap ν, Polynomial.coeff_map, MvPolynomial.coeff_map]
  have hξFc : ∀ ν i J, ∃ l, ξF l = ((QF ν).coeff i).coeff J := by
    intro ν i J
    obtain ⟨l, hl⟩ := exists_coeffVec_eq (coeff_mem_coeffSet Q ν i J)
    exact ⟨l, Subtype.ext (hl.trans (hQc ν i J).symm)⟩
  have hQcoeff : ∀ ν i, (Q ν).coeff i = MvPolynomial.map (algebraMap F k) ((QF ν).coeff i) := by
    intro ν i
    rw [← hQFmap ν, Polynomial.coeff_map]
  have hsF : ∀ ν i, ((QF ν).coeff i).support.card ≤ s0Q Q := by
    intro ν i
    have := card_support_coeff_le_s0Q Q ν i
    rwa [hQcoeff, MvPolynomial.support_map_of_injective _ hinjF] at this
  have hqF : ∀ ν i, ((QF ν).coeff i).totalDegree ≤ q0Q Q := by
    intro ν i
    have := totalDegree_coeff_le_q0Q Q ν i
    rwa [hQcoeff, totalDegree_map_of_injective hinjF] at this
  have hnF : ∀ ν, (QF ν).natDegree ≤ nmaxQ Q := fun ν => (hQFdeg ν).symm ▸ natDegree_le_nmaxQ Q ν
  have hH := mvPolynomialHeight_det_le (k := k) YF hYF0 ⟨m₀, hm₀F⟩ QF ξF (nmax := nmaxQ Q)
    (s₀ := s0Q Q) (Nat.le_add_left _ _) hnF (Nat.le_add_left _ _) hsF hξF1 hξFc hδF hdet0
    (by rw [hYF]; exact hY) (by rw [hξF]; exact coeffVec_ne_zero Q)
  rw [hr, hsuppF, mvPolynomialHeight_congr hYF _ hY,
    weilHeight_congr hξF _ (coeffVec_ne_zero Q)] at hH
  have hT := totalDegree_det_charMatrixOption_le YF QF hqF hδF
  rw [hr] at hT
  have hT' : (Φ χ).totalDegree ≤ r * (1 + q0Q Q * δ) := by
    rw [hχ', totalDegree_map_of_injective hinjF]; exact hT
  rw [mvPolynomialHeight_congr hχ' hχ'0 hdet0] at key
  have hH0 := mvPolynomialHeight_nonneg _ hdet0
  have hl2 := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have heD : (e : ℝ) ≤ Module.finrank (IntermediateField.adjoin k {α, β}) L := by
    exact_mod_cast he
  have hT'' : ((5 * (Φ χ).totalDegree : ℕ) : ℝ) ≤ ((5 * (r * (1 + q0Q Q * δ)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 5 hT'
  push_cast at key hT''
  calc _ ≤ _ := key
    _ = (e : ℝ) * (mvPolynomialHeight _ hdet0 + 5 * ((Φ χ).totalDegree : ℝ) * Real.log 2) := by
        ring
    _ ≤ (e : ℝ) * (Real.log (placeConst r Y.support.card (nmaxQ Q) (s0Q Q) δ) +
          r * mvPolynomialHeight Y hY +
          r * δ * weilHeight (Projectivization.mk k (coeffVec Q) (coeffVec_ne_zero Q)) +
          5 * (r * (1 + q0Q Q * δ) : ℝ) * Real.log 2) := by
        gcongr
    _ ≤ _ := by
        push_cast
        refine mul_le_mul_of_nonneg_right heD ?_
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) (Nat.cast_nonneg
          (r * (1 + q0Q Q * δ)))) hl2
        push_cast at this
        linarith

/-- `log c ≤ m δ` for `1 ≤ c ≤ (δ + 1) ^ m`. -/
private lemma log_le_mul_of_le_pow {c δ m : ℕ} (hc : 1 ≤ c) (h : c ≤ (δ + 1) ^ m) :
    Real.log (c : ℝ) ≤ m * δ := by
  have h1 : Real.log (c : ℝ) ≤ Real.log (((δ + 1) ^ m : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hc) (by exact_mod_cast h)
  rw [Nat.cast_pow, Real.log_pow] at h1
  have h2 : Real.log ((δ + 1 : ℕ) : ℝ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (x := ((δ + 1 : ℕ) : ℝ)) (by positivity)
    push_cast at this ⊢
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))

/-- The logarithm of `placeConst r c nmax s₀ δ`, expanded. -/
private lemma log_placeConst_le {r c nmax s₀ δ : ℕ} (hc : 1 ≤ c) (hns : 1 ≤ nmax * s₀) :
    Real.log (placeConst r c nmax s₀ δ : ℝ) ≤
      Real.log (r.factorial : ℝ) + r * Real.log 2 + r * Real.log c +
        δ * r * Real.log ((nmax * s₀ : ℕ) : ℝ) := by
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hns' : ((nmax * s₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : nmax * s₀ ≠ 0)
  have hpc : (placeConst r c nmax s₀ δ : ℝ) = (r.factorial : ℝ) * ((2 : ℝ) * c) ^ r *
      ((nmax * s₀ : ℕ) : ℝ) ^ (δ * r) := by
    unfold placeConst; push_cast; ring
  have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
  rw [hpc, Real.log_mul (mul_ne_zero hf (pow_ne_zero _ h2c)) (pow_ne_zero _ hns'),
    Real.log_mul hf (pow_ne_zero _ h2c), Real.log_pow, Real.log_pow,
    Real.log_mul two_ne_zero hc0]
  push_cast
  linarith

omit [Fintype κ] [DecidableEq κ] in
/-- **The core estimate.** -/
private lemma exists_height_norm_le [Finite κ] {α β : L}
    (hinj : Function.Injective (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (θ : κ → L) (Q : κ → (MvPolynomial (Fin 2) k)[X]) (hQ : ∀ ν, (Q ν).Monic)
    (hθ : ∀ ν, (Q ν).eval₂ (MvPolynomial.aeval ![α, β] : MvPolynomial (Fin 2) k →ₐ[k] L).toRingHom
      (θ ν) = 0)
    (D₀ : ℕ) (hD₀ : Module.finrank (IntermediateField.adjoin k {α, β}) L ≤ D₀) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (Y : MvPolynomial κ k) (hY : Y ≠ 0) (δ : ℕ),
      Y.totalDegree ≤ δ → ∀ (P : MvPolynomial (Fin 2) k) (hP : P ≠ 0),
      MvPolynomial.aeval ![α, β] P =
        (Algebra.norm (IntermediateField.adjoin k {α, β}) (MvPolynomial.aeval θ Y) : L) →
      mvPolynomialHeight P hP ≤ A * mvPolynomialHeight Y hY + B * (δ + 1) := by
  classical
  have := Fintype.ofFinite κ
  set E := IntermediateField.adjoin k ({α, β} : Set L)
  set r := ∏ ν, (Q ν).natDegree
  set cQ := weilHeight (Projectivization.mk k (coeffVec Q) (coeffVec_ne_zero Q))
  have hcQ : 0 ≤ cQ := weilHeight_nonneg _
  have hl2 := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hfact : 0 ≤ Real.log (r.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r))
  have hns1 : 1 ≤ nmaxQ Q * s0Q Q :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by simp [nmaxQ]) (by simp [s0Q]))
  have hns : 0 ≤ Real.log ((nmaxQ Q * s0Q Q : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hns1)
  set B₀ : ℝ := Real.log (r.factorial : ℝ) + r * Real.log 2 + r * Fintype.card κ +
    r * Real.log ((nmaxQ Q * s0Q Q : ℕ) : ℝ) + r * cQ + 5 * (r * (1 + q0Q Q)) * Real.log 2
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨D₀ * r, D₀ * B₀, by positivity, by positivity, ?_⟩
  intro Y hY δ hδ P hP hPeq
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.mp hY
  set c := Y.coeff m₀
  set Y' := MvPolynomial.C c⁻¹ * Y
  have hc : c⁻¹ ≠ 0 := inv_ne_zero hm₀
  have hY' : Y' ≠ 0 := mul_ne_zero (by simpa using hc) hY
  have hm₀' : Y'.coeff m₀ = 1 := by
    rw [MvPolynomial.coeff_C_mul]
    exact inv_mul_cancel₀ hm₀
  have hδ' : Y'.totalDegree ≤ δ :=
    (MvPolynomial.totalDegree_mul _ _).trans (by rwa [MvPolynomial.totalDegree_C, zero_add])
  have hhY : mvPolynomialHeight Y' hY' = mvPolynomialHeight Y hY :=
    mvPolynomialHeight_C_mul hc Y hY hY'
  set D := Module.finrank E L
  have hYY' : Y = MvPolynomial.C c * Y' := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hm₀, map_one, one_mul]
  have hnormY : (Algebra.norm E (MvPolynomial.aeval θ Y) : L) =
      algebraMap k L c ^ D * (Algebra.norm E (MvPolynomial.aeval θ Y') : L) := by
    rw [hYY', map_mul, MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply k E L, map_mul,
      Algebra.norm_algebraMap]
    push_cast
    rfl
  set P' := MvPolynomial.C (c⁻¹ ^ D) * P
  have hP' : P' ≠ 0 := mul_ne_zero (by simpa using pow_ne_zero D hc) hP
  have hP'eq : MvPolynomial.aeval ![α, β] P' =
      (Algebra.norm E (MvPolynomial.aeval θ Y') : L) := by
    rw [map_mul, MvPolynomial.aeval_C, hPeq, hnormY, ← mul_assoc, ← map_pow, ← map_mul,
      ← mul_pow, inv_mul_cancel₀ hm₀, one_pow, map_one, one_mul]
  have hhP : mvPolynomialHeight P' hP' = mvPolynomialHeight P hP :=
    mvPolynomialHeight_C_mul (pow_ne_zero D hc) P hP hP'
  have key := height_norm_le_of_coeff_eq_one hinj θ Q hQ hθ Y' hY' hm₀' δ hδ' P' hP' hP'eq
  rw [hhP, hhY] at key
  replace key : mvPolynomialHeight P hP ≤ (D : ℝ) *
      (Real.log (placeConst r Y'.support.card (nmaxQ Q) (s0Q Q) δ) +
        (r : ℝ) * mvPolynomialHeight Y hY + r * δ * cQ +
        ((5 * (r * (1 + q0Q Q * δ)) : ℕ) : ℝ) * Real.log 2) := key
  -- the logarithm of the integer constant
  set cs := Y'.support.card
  have hcs1 : 1 ≤ cs := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hY')
  have hcs : cs ≤ (δ + 1) ^ Fintype.card κ := card_support_le_of_totalDegree_le Y' hδ'
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hlogc := log_le_mul_of_le_pow hcs1 hcs
  have hlogB : Real.log (placeConst r cs (nmaxQ Q) (s0Q Q) δ : ℝ) ≤
      Real.log (r.factorial : ℝ) + r * Real.log 2 + r * (Fintype.card κ * δ) +
        δ * r * Real.log ((nmaxQ Q * s0Q Q : ℕ) : ℝ) :=
    (log_placeConst_le hcs1 hns1).trans (by gcongr)
  have hpc1 : 1 ≤ placeConst r cs (nmaxQ Q) (s0Q Q) δ :=
    one_le_placeConst hcs1 (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  have hlogB0 : 0 ≤ Real.log (placeConst r cs (nmaxQ Q) (s0Q Q) δ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpc1)
  have hhY0 := mvPolynomialHeight_nonneg Y hY
  have hq0 : (0 : ℝ) ≤ q0Q Q := Nat.cast_nonneg _
  have hinner0 : 0 ≤ Real.log (placeConst r cs (nmaxQ Q) (s0Q Q) δ : ℝ) +
      (r : ℝ) * mvPolynomialHeight Y hY + r * δ * cQ +
      ((5 * (r * (1 + q0Q Q * δ)) : ℕ) : ℝ) * Real.log 2 := by positivity
  have hD : (D : ℝ) ≤ D₀ := by exact_mod_cast hD₀
  refine key.trans ((mul_le_mul_of_nonneg_right hD hinner0).trans ?_)
  push_cast
  have hX1 : 0 ≤ Real.log (r.factorial : ℝ) + r * Real.log 2 := by positivity
  have hX4 : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hD0 : (0 : ℝ) ≤ D₀ := Nat.cast_nonneg _
  have hinner : Real.log (placeConst r cs (nmaxQ Q) (s0Q Q) δ : ℝ) +
      (r : ℝ) * mvPolynomialHeight Y hY + r * δ * cQ +
      5 * (r * (1 + q0Q Q * δ)) * Real.log 2 ≤ r * mvPolynomialHeight Y hY + B₀ * (δ + 1) := by
    simp only [B₀]
    nlinarith [mul_nonneg hδ0 hX1, mul_nonneg hδ0 hX4, mul_nonneg hq0 hX4,
      mul_nonneg (mul_nonneg hδ0 hq0) hX4, mul_nonneg hr0 hcQ, mul_nonneg hr0 hns,
      mul_nonneg (mul_nonneg hδ0 hr0) hns, mul_nonneg hr0 (Nat.cast_nonneg (Fintype.card κ) :
          (0:ℝ) ≤ _)]
  nlinarith [mul_le_mul_of_nonneg_left hinner hD0]

end Core

section Curve

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- An element integral over `k[t]` gives a monic equation over `k[X₀, X₁]`, with `X i ↦ t`. -/
private lemma exists_monic_eval₂_eq_zero (ψ : K →ₐ[k] L) {t z : K}
    (hz : IsIntegral (Algebra.adjoin k {t}) z) (φ : MvPolynomial (Fin 2) k →ₐ[k] L) (i : Fin 2)
    (hφ : φ (MvPolynomial.X i) = ψ t) :
    ∃ Q : (MvPolynomial (Fin 2) k)[X], Q.Monic ∧ Q.eval₂ φ.toRingHom (ψ z) = 0 := by
  classical
  obtain ⟨p, hp, hpz⟩ := hz
  have hcoeff : ∀ n, ∃ g : k[X], Polynomial.aeval t g = (p.coeff n : K) := by
    intro n
    have : (p.coeff n : K) ∈ (Polynomial.aeval t : k[X] →ₐ[k] K).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (p.coeff n).2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  choose g hg using hcoeff
  set N := p.natDegree
  refine ⟨Polynomial.X ^ N + ∑ n ∈ Finset.range N,
    Polynomial.C (Polynomial.aeval (MvPolynomial.X i) (g n)) * Polynomial.X ^ n, ?_, ?_⟩
  · refine Polynomial.monic_X_pow_add ?_
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe N)).mpr fun n hn => ?_
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hn)
  · have h1 : ∀ n, φ (Polynomial.aeval (MvPolynomial.X i) (g n)) = ψ (p.coeff n : K) := by
      intro n
      rw [← Polynomial.aeval_algHom_apply, hφ, Polynomial.aeval_algHom_apply, hg]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1]
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree] at hpz
    have := congrArg ψ hpz
    simp only [map_add, map_sum, map_mul, map_pow, map_zero, map_one, one_mul] at this
    rw [← this, add_comm]
    rfl

end Curve

section Forms

variable {k K L ι : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

private lemma aeval_eq_affineEvaluation (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ) :
    MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν) / pr₁ (x j)) (fun ν => pr₂ (x ν) / pr₂ (x j)))
        (F : MvPolynomial (ι ⊕ ι) k) =
      Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j δ F := by
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
  have h := Faltings.BombieriRoth.aeval_sumElim_mul_of_isWeightedHomogeneous hF
    (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)) (pr₁ (x j))⁻¹ (pr₂ (x j))⁻¹
  have hθ : (Sum.elim (fun ν => pr₁ (x ν) / pr₁ (x j)) (fun ν => pr₂ (x ν) / pr₂ (x j)) :
      ι ⊕ ι → L) = Sum.elim (fun ν => (pr₁ (x j))⁻¹ * pr₁ (x ν))
        (fun ν => (pr₂ (x j))⁻¹ * pr₂ (x ν)) := by
    funext ν; rcases ν with ν | ν <;> simp [div_eq_inv_mul]
  rw [hθ, h]
  change _ = MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) F.1 /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2)
  rw [div_eq_inv_mul, mul_inv, inv_pow, inv_pow]

private lemma totalDegree_le_of_mem_weightedHomogeneousSubmodule {δ₁ δ₂ : ℕ}
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ)
        (δ₁, δ₂)) :
    (F : MvPolynomial (ι ⊕ ι) k).totalDegree ≤ δ₁ + δ₂ := by
  classical
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
  refine Finset.sup_le fun m hm => ?_
  have hw := hF (MvPolynomial.mem_support_iff.mp hm)
  have key : (Finsupp.weight (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ)))
      (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) m).1 +
      (Finsupp.weight (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ)))
      (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) m).2 = m.sum fun _ e => e := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases i with i | i <;> simp
  rw [← key, hw]

end Forms

section Assembly

/-- The core estimate for the curve: `θ = (ξ, ξ')`, with the monic equations given by the
integrality of `ξ_ν` over `k[ξ_a]` and of `ξ'_ν` over `k[ξ'_b]`. -/
private lemma exists_height_norm_le_of_isIntegral {k K L ι : Type*} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Finite ι]
    (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) {D₀ : ℕ}
    (h₁ : ∀ ν, IsIntegral (Algebra.adjoin k {x a / x j}) (x ν / x j))
    (h₂ : ∀ ν, IsIntegral (Algebra.adjoin k {x b / x j}) (x ν / x j))
    (hind : AlgebraicIndependent k ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)])
    (hD₀ : Module.finrank
      (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) L ≤ D₀) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (Y : MvPolynomial (ι ⊕ ι) k) (hY : Y ≠ 0) (δ : ℕ),
      Y.totalDegree ≤ δ → ∀ (P : MvPolynomial (Fin 2) k) (hP : P ≠ 0),
      MvPolynomial.aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] P =
        (Algebra.norm (IntermediateField.adjoin k
          {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})
          (MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν) / pr₁ (x j))
            (fun ν => pr₂ (x ν) / pr₂ (x j))) Y) : L) →
      mvPolynomialHeight P hP ≤ A * mvPolynomialHeight Y hY + B * (δ + 1) := by
  set φ := (MvPolynomial.aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] :
    MvPolynomial (Fin 2) k →ₐ[k] L)
  have hQ : ∀ ν : ι ⊕ ι, ∃ q : (MvPolynomial (Fin 2) k)[X], q.Monic ∧
      q.eval₂ φ.toRingHom (Sum.elim (fun ν => pr₁ (x ν) / pr₁ (x j))
        (fun ν => pr₂ (x ν) / pr₂ (x j)) ν) = 0 := by
    rintro (ν | ν)
    · simpa only [Sum.elim_inl, map_div₀] using
        exists_monic_eval₂_eq_zero pr₁ (h₁ ν) φ 0 (by simp [φ, map_div₀])
    · simpa only [Sum.elim_inr, map_div₀] using
        exists_monic_eval₂_eq_zero pr₂ (h₂ ν) φ 1 (by simp [φ, map_div₀])
  choose Q hQm hQ using hQ
  exact exists_height_norm_le hind _ Q hQm hQ D₀ hD₀

/-- Constants that exist under a hypothesis exist uniformly, with the hypothesis moved inside. -/
private lemma exists_nonneg_imp {p : Prop} {q : ℝ → ℝ → Prop}
    (h : p → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ q A B) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ (p → q A B) := by
  by_cases hp : p
  · obtain ⟨A, B, hA, hB, hq⟩ := h hp
    exact ⟨A, B, hA, hB, fun _ => hq⟩
  · exact ⟨0, 0, le_rfl, le_rfl, fun h => absurd h hp⟩

private lemma le_sum_sum {ι : Type*} [Fintype ι] {f : ι → ι → ℝ} (hf : ∀ a b, 0 ≤ f a b)
    (a b : ι) : f a b ≤ ∑ a, ∑ b, f a b :=
  (Finset.single_le_sum (fun b _ => hf a b) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, f a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hf a b) (Finset.mem_univ a))

/-- The degree of `G_0` against the parameters: `δ₁ + δ₂ + 1 ≤ (2 + 2s)(d₁ + d₂)/γ`. -/
private lemma natCast_add_add_one_le {N s g d₁ d₂ d δ₁ δ₂ : ℕ} {γ : ℝ} (hγ : 0 < γ) (hN : 0 < N)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hN₁ : N * δ₁ = d₁ + s * d) (hN₂ : N * δ₂ = d₂ + s * d)
    (hg₁ : g * d ^ 2 < d₁ * d₂) (hg₂ : d₁ * d₂ < g ^ 2 * d ^ 2)
    (hγd : γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - g * d ^ 2) (hd₂₁ : d₂ ≤ d₁) :
    ((δ₁ + δ₂ : ℕ) : ℝ) + 1 ≤ (2 + 2 * s) * ((d₁ + d₂) / γ) := by
  have hg : 1 ≤ g := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hg₂)
  have hdd : d ≤ d₁ := by
    by_contra hcon
    push Not at hcon
    have : d₁ * d₂ ≤ d * d := Nat.mul_le_mul hcon.le (hd₂₁.trans hcon.le)
    have : d * d ≤ g * d ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ hg
    omega
  have : δ₁ ≤ N * δ₁ := Nat.le_mul_of_pos_left _ hN
  have : δ₂ ≤ N * δ₂ := Nat.le_mul_of_pos_left _ hN
  have : s * d ≤ s * d₁ := Nat.mul_le_mul_left _ hdd
  have hδsum : δ₁ + δ₂ + 1 ≤ (2 + 2 * s) * (d₁ + d₂) := by nlinarith
  have hγ1 : γ ≤ 1 := by
    have : (0 : ℝ) < d₁ * d₂ := by positivity
    have : (0 : ℝ) ≤ g * d ^ 2 := by positivity
    nlinarith
  calc ((δ₁ + δ₂ : ℕ) : ℝ) + 1 ≤ (2 + 2 * s) * ((d₁ : ℝ) + d₂) := by exact_mod_cast hδsum
    _ ≤ (2 + 2 * s) * ((d₁ + d₂) / γ) := by gcongr; exact le_div_self (by positivity) hγ hγ1

end Assembly

/-- **The height of `G_0`** (Bombieri). Let `ξ_ν = x_ν / x_j` in `K` and
`ξ'_ν = pr₂ ξ_ν` in `L`; assume `ι` is finite, and for `a, b ≠ j` that every `ξ_ν` is integral
over `k[ξ_a]` and over `k[ξ_b]`, that `pr₁ ξ_a, ξ'_b` are algebraically independent over `k`, and
that `[L : k⟮pr₁ ξ_a, ξ'_b⟯] ≤ N²`. For every `c₁₀` there is `c₁₅` such that for every error term
`ε = o(n)` there is an error term `ε' = o(n)` with the following property. Let `γ > 0`, let
`d₁, d₂, d` be positive integers with `N δ₁ = d₁ + s d`, `N δ₂ = d₂ + s d`,
`g d² < d₁ d₂ < g² d²`, `d₁ d₂ - g d² > γ d₁ d₂` and `d₂ ≤ d₁`, and let `F = (F_i)` be forms of
bidegree `(δ₁, δ₂)` over `k` with `F_i(ξ, ξ') = G η_i^d`, `G ≠ 0`, `η_0 = 1`, and
`h(F) ≤ c₁₀ (d₁ + d₂) / γ + ε (d₁ + d₂)`. Then the polynomial `P` with
`P(pr₁ ξ_a, ξ'_b) = G_0 = formNorm pr₁ pr₂ x j a b (δ₁, δ₂) (F 0)` has
`h(P) ≤ c₁₅ N² (d₁ + d₂) / γ + ε' (d₁ + d₂)`. -/
@[faltings "lem_bvr_height_g0"]
public theorem exists_logHeight_formNorm_le {k K L ι : Type*} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Finite ι]
    (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (N s g : ℕ) (c₁₀ : ℝ) :
    ∃ c₁₅ : ℝ, ∀ ε : ℕ → ℝ, ε =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) →
      ∃ ε' : ℕ → ℝ, ε' =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ (a b : ι), a ≠ j → b ≠ j →
      (∀ ν, IsIntegral (Algebra.adjoin k {x a / x j}) (x ν / x j)) →
      (∀ ν, IsIntegral (Algebra.adjoin k {x b / x j}) (x ν / x j)) →
      AlgebraicIndependent k ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] →
      Module.finrank
        (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) L ≤ N ^ 2 →
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
      ∀ (P : MvPolynomial (Fin 2) k) (hP : P ≠ 0),
      MvPolynomial.aeval ![pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)] P =
        (formNorm pr₁ pr₂ x j a b (δ₁, δ₂) (F 0) : L) →
      mvPolynomialHeight P hP ≤ c₁₅ * N ^ 2 * (d₁ + d₂) / γ + ε' (d₁ + d₂) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose A B hA hB hbound using fun a b => exists_nonneg_imp fun h : _ ∧ _ ∧ _ ∧ _ =>
    exists_height_norm_le_of_isIntegral pr₁ pr₂ x j a b h.1 h.2.1 h.2.2.1 h.2.2.2
  set As : ℝ := ∑ a, ∑ b, A a b
  set Bs : ℝ := ∑ a, ∑ b, B a b
  have hAs0 : 0 ≤ As := (hA j j).trans (le_sum_sum hA j j)
  have hBs0 : 0 ≤ Bs := (hB j j).trans (le_sum_sum hB j j)
  refine ⟨(As * c₁₀ + Bs * (2 + 2 * s)) / N ^ 2, fun ε hε =>
    ⟨fun n => As * ε n, hε.const_mul_left As, ?_⟩⟩
  intro a b _ _ h1 h2 h3 h4 γ d₁ d₂ d δ₁ δ₂ hγ hd₁ hd₂ _ hN₁ hN₂ hg₁ hg₂ hγd hd₂₁ m F G η
    hG hη hF hF0 hFh P hP hPeq
  have hy : Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j (δ₁, δ₂) (F 0) = G := by
    rw [hF 0, hη, one_pow, mul_one]
  have hY : (F 0 : MvPolynomial (ι ⊕ ι) k) ≠ 0 := fun h =>
    hG (by rw [← hy, show F 0 = 0 from Subtype.ext h, map_zero])
  have hb := hbound a b ⟨h1, h2, h3, h4⟩ _ hY (δ₁ + δ₂)
    (totalDegree_le_of_mem_weightedHomogeneousSubmodule (F 0)) P hP
    (by rw [hPeq, aeval_eq_affineEvaluation]; rfl)
  have hYF : mvPolynomialHeight _ hY ≤ polynomialFamilyHeight _ hF0 :=
    polynomialFamilyHeight_comp_le (fun i => (F i : MvPolynomial (ι ⊕ ι) k))
      (fun _ : Unit => (0 : Fin (m + 1))) ⟨(), hY⟩
  have hN : N ≠ 0 := by rintro rfl; omega
  have hδR := natCast_add_add_one_le hγ (Nat.pos_of_ne_zero hN) hd₁ hd₂ hN₁ hN₂ hg₁ hg₂ hγd hd₂₁
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (Nat.cast_ne_zero.2 hN))]
  calc mvPolynomialHeight P hP
      ≤ A a b * mvPolynomialHeight _ hY + B a b * (((δ₁ + δ₂ : ℕ) : ℝ) + 1) := hb
    _ ≤ As * polynomialFamilyHeight _ hF0 + Bs * ((2 + 2 * s) * ((d₁ + d₂) / γ)) :=
        add_le_add (mul_le_mul (le_sum_sum hA a b) hYF (mvPolynomialHeight_nonneg _ hY) hAs0)
          (mul_le_mul (le_sum_sum hB a b) hδR (by positivity) hBs0)
    _ ≤ As * (c₁₀ * (d₁ + d₂) / γ + ε (d₁ + d₂)) + Bs * ((2 + 2 * s) * ((d₁ + d₂) / γ)) := by
        gcongr
    _ = (As * c₁₀ + Bs * (2 + 2 * s)) * (d₁ + d₂) / γ + As * ε (d₁ + d₂) := by ring

end Faltings.BombieriRoth
