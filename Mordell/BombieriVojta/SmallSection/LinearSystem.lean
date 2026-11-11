module
public import Mordell.BombieriVojta.SmallSection.U2
public import Mordell.BombieriVojta.Projection.MonomialIndependence
public import Mordell.BombieriVojta.SmallSection.DimU1

/-!
# The basic system on `U₁` as a linear system of small height

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one, `N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of `L(NP)` satisfying
(G1) and (G2). Write `ξ_ν = x_ν / x₀`, and `ξ_ν`, `ξ'_ν` for its pull-backs to `C × C`. Fix
polynomials `P_i, Q_i ∈ k[X₀, X₁, X₂, X₃]` (`i ∈ σ`), evaluated at `(ξ₁, ξ₂, ξ'₁, ξ'₂)`, with
`Q_i(ξ, ξ') ≠ 0`. For a bidegree `(δ₁, δ₂)` the elements of `U₁` are the tuples
`F_t = ∑ f_{t,l,l',μ} ξ₁^l ξ'₁^{l'} b_μ` (`t ∈ σ`, `l + μ₁ ≤ δ₁`, `l' + μ₂ ≤ δ₂`), and the
coefficients `f` are coordinates on `U₁`, by
`Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`.

There are `c₁₃ ≥ 0` and `ε₁₃ ≥ 0` with `ε₁₃(d) → 0`, independent of `δ₁, δ₂` and `d`, such that
for every bidegree `(δ₁, δ₂)` and every `d ≥ 1` the basic system
`(P_i Q_j)^d F_j = (P_j Q_i)^d F_i` (the condition defining `U₂`) holds on the tuple with
coordinates `f` if and only if `f` is a solution of a finite family of linear forms with
coefficients in `k`, each of absolute height at most `c₁₃ d + ε₁₃(d) d`.

## Main results

* `Faltings.BombieriVojta.exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le`: the linear
  system and its height bound.
* `BombieriVojta.exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le_of_linearIndependent`:
  the same for any `pr₁, pr₂ : K →ₐ[k] L`, any `P_i, Q_i ∈ L`, and any `ξ_a, ξ_b` for which the
  `ξ_a^l ξ'_a^{l'} b_ν` are independent over `k` and the `b_ν` span `L` over `k(ξ_a, ξ'_a)`.

## Implementation notes

As in `Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`, sections of `𝒪(NP)`
are rational functions, `P` is a divisor `P₁ : C →₀ ℤ` of degree one supported on closed points,
`NP` is `(N : ℤ) • P₁`, and the function field of `C × C` is a field
`L` with `IsFractionRing (k(C) ⊗[k] k(C)) L`, with projections `g ↦ g ⊗ 1` and `g ↦ 1 ⊗ g`.
The source's `ξ₁, ξ₂` are `ξ_a, ξ_b` for distinct nonzero indices `a, b`, and the tuple is
indexed by a finite type `σ` (the source's case is `σ = Fin (m + 1)`).

The coordinates of `U₁` are indexed by `σ × M`, where `M` is the finite type of triples
`(l, l', μ) ∈ Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N)` with `l + μ₁ ≤ δ₁` and
`l' + μ₂ ≤ δ₂`. The linear forms `L_{ijaa'ν}` are the rows of a matrix `A` with columns `σ × M`,
indexed by a finite type, and a form vanishes on `f` when `A *ᵥ f = 0`; this is the shape taken by
`Faltings.exists_ne_zero_mulVec_eq_zero_logHeight_le`. The height of a form is the absolute
height `Height.logHeight / [k : ℚ]` of its coefficient vector. The equivalence is stated for every
coordinate vector `f`, so it also covers the membership of the tuple in `U₀`.

The curve enters only through two facts: the `ξ_a^l ξ'_a^{l'} b_ν` are linearly independent over
`k` (`Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`), and the `b_ν` span
`k(C × C)` over `k(ξ_a, ξ'_a)`
(`Faltings.BombieriSiegel.linearIndependent_and_span_monomial_eq_top`). The general statement
takes these as hypotheses. The general statement holds for all `P_i, Q_i ∈ L`, without
`Q_i(ξ, ξ') ≠ 0`.

For the proof write `y₁ = ξ_a`, `y₂ = ξ'_a` and `b_ν = ξ_b^{ν₁} ξ'_b^{ν₂}`
(`ν ∈ {0, …, N - 1}²`). The `b_ν` are a basis of `k(C × C)` over `k(y₁, y₂)`, so multiplication
by `G_{ij} = P_i Q_j` has a matrix over `k(y₁, y₂)`; clearing one common denominator
`s(y₁, y₂) ≠ 0` gives `s G_{ij} b_μ = ∑_ν m_{ij,μν}(y₁, y₂) b_ν` with polynomials
`m_{ij,μν} ∈ k[X, Y]`, fixed once and for all. Then
`s^d G_{ij}^d b_μ = ∑_ν (m_{ij}^d)_{μν}(y₁, y₂) b_ν`, and for `F ∈ U₁`,
`s^d ((P_i Q_j)^d F_j - (P_j Q_i)^d F_i)` is `∑_ν R_{ijν}(y₁, y₂) b_ν`, with `R_{ijν}` linear in
the coordinates. By the independence of the `y₁^l y₂^{l'} b_ν` the basic system holds iff every
coefficient of every `R_{ijν}` vanishes; these coefficients are the linear forms.

Every coefficient of a linear form is a coefficient of an entry of `m_{ij}^d` (or its negative, or
a difference of two). At a place `v`, a coefficient of an entry of a product of polynomial
matrices is bounded by the number of terms times the product of the bounds (at a finite place, by
the product of the bounds alone), so the coefficients of the entries of `m_{ij}^d` have
`|·|_v ≤ Y_v^d` with `Y_v` independent of `d`, and `Y_v = max(1, |coefficients of m|_v)` at almost
all places. This gives the height bound
`h(L) ≤ c₁₃ d`.

The source clears denominators only in the products `b_λ b_μ` and reduces the monomials of
`(P_i Q_j)^d` with the minimal polynomial of `ξ_b` over `k(ξ_a)`; here the denominator is cleared
once in the matrix of multiplication by `P_i Q_j`, and `(P_i Q_j)^d` acts by the `d`-th power of
that matrix. The local bounds are then submultiplicative in `d` and give `ε₁₃ = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 631
-/

open AlgebraicGeometry TensorProduct Filter Topology Matrix

universe u

namespace Faltings.BombieriVojta

section LocalBounds

variable {K : Type*} [Field K]

/-- The triangle inequality for a finite sum of terms of size at most `B`. -/
private lemma abv_sum_le (v : AbsoluteValue K ℝ) {α : Type} (s : Finset α) (f : α → K) (B : ℝ)
    (_ : 0 ≤ B) (h : ∀ t ∈ s, v (f t) ≤ B) : v (∑ t ∈ s, f t) ≤ (s.card : ℝ) ^ 1 * B := by
  calc v (∑ t ∈ s, f t) ≤ ∑ t ∈ s, v (f t) := v.sum_le _ _
    _ ≤ s.card • B := Finset.sum_le_card_nsmul _ _ _ h
    _ = _ := by rw [nsmul_eq_mul, pow_one]

/-- The ultrametric inequality for a finite sum of terms of size at most `B`. -/
private lemma abv_sum_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {α : Type} (s : Finset α) (f : α → K) (B : ℝ) (hB : 0 ≤ B) (h : ∀ t ∈ s, v (f t) ≤ B) :
    v (∑ t ∈ s, f t) ≤ (s.card : ℝ) ^ 0 * B := by
  classical
  rw [pow_zero, one_mul]
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hv _ _).trans (max_le (h a (by simp)) (ih fun t ht => h t (by simp [ht])))

/-- A coefficient of `q * r` is bounded by the number of terms of `r` (to the power `ε`) times
the bounds on the coefficients of `q` and `r`. -/
private lemma abv_coeff_mul_le (v : AbsoluteValue K ℝ) (ε : ℕ)
    (hsum : ∀ {α : Type} (s : Finset α) (f : α → K) (B : ℝ), 0 ≤ B → (∀ t ∈ s, v (f t) ≤ B) →
      v (∑ t ∈ s, f t) ≤ (s.card : ℝ) ^ ε * B)
    {q r : MvPolynomial (Fin 2) K} {X β : ℝ} {T : ℕ} (hX : 0 ≤ X) (hβ : 0 ≤ β)
    (hq : ∀ a, v (q.coeff a) ≤ X) (hr : ∀ a, v (r.coeff a) ≤ β) (hT : r.support.card ≤ T)
    (a : Fin 2 →₀ ℕ) : v ((q * r).coeff a) ≤ (T : ℝ) ^ ε * (X * β) := by
  classical
  rw [r.as_sum, Finset.mul_sum, MvPolynomial.coeff_sum]
  refine (hsum _ _ _ (mul_nonneg hX hβ) fun b _ => ?_).trans ?_
  · rw [MvPolynomial.coeff_mul_monomial']
    split_ifs
    · rw [map_mul]; exact mul_le_mul (hq _) (hr _) (v.nonneg _) hX
    · simpa using mul_nonneg hX hβ
  · gcongr

/-- The coefficients of the entries of `m ^ d` are bounded by `(#ι ^ ε T ^ ε β) ^ d`, where `β`
bounds the coefficients of the entries of `m` and `T` their numbers of terms. -/
private lemma abv_coeff_pow_le {ι : Type} [Fintype ι] [DecidableEq ι] (v : AbsoluteValue K ℝ)
    (ε : ℕ)
    (hsum : ∀ {α : Type} (s : Finset α) (f : α → K) (B : ℝ), 0 ≤ B → (∀ t ∈ s, v (f t) ≤ B) →
      v (∑ t ∈ s, f t) ≤ (s.card : ℝ) ^ ε * B)
    (m : Matrix ι ι (MvPolynomial (Fin 2) K)) {β : ℝ} {T : ℕ} (hβ : 1 ≤ β)
    (hm : ∀ μ ν a, v ((m μ ν).coeff a) ≤ β) (hT : ∀ μ ν, (m μ ν).support.card ≤ T) (d : ℕ)
    (μ ν : ι) (a : Fin 2 →₀ ℕ) :
    v (((m ^ d) μ ν).coeff a) ≤ ((Fintype.card ι : ℝ) ^ ε * (T : ℝ) ^ ε * β) ^ d := by
  induction d generalizing ν a with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs
    · rw [MvPolynomial.coeff_one]; split_ifs <;> simp
    · simp
  | succ d ih =>
    have hX : 0 ≤ ((Fintype.card ι : ℝ) ^ ε * (T : ℝ) ^ ε * β) ^ d := by positivity
    rw [pow_succ, Matrix.mul_apply, MvPolynomial.coeff_sum]
    refine (hsum _ _ _ (by positivity) fun ρ _ =>
      abv_coeff_mul_le v ε hsum hX (by linarith) (ih ρ) (hm ρ ν) (hT ρ ν) a).trans (le_of_eq ?_)
    rw [Finset.card_univ]
    ring

end LocalBounds

section Height

open Height Height.AdmissibleAbsValues

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- If at every archimedean `v` the entries of `x` have size at most `Ya v ^ d`, and at every
nonarchimedean `v` at most `Yn v ^ d` (with `Yn = 1` almost everywhere), then
`H(x) ≤ (∏ Ya ∏ Yn) ^ d`. -/
private lemma mulHeight_le_pow {ι : Type*} [Finite ι] (x : ι → K) (d : ℕ)
    (Ya Yn : AbsoluteValue K ℝ → ℝ) (hYa : ∀ v, 1 ≤ Ya v) (hYn : ∀ v, 1 ≤ Yn v)
    (hfin : Function.HasFiniteMulSupport fun v : nonarchAbsVal (K := K) => Yn v.val)
    (ha : ∀ v ∈ archAbsVal (K := K), ∀ i, v (x i) ≤ Ya v ^ d)
    (hn : ∀ v ∈ nonarchAbsVal (K := K), ∀ i, v (x i) ≤ Yn v ^ d) :
    mulHeight x ≤ ((archAbsVal.map Ya).prod * ∏ᶠ v : nonarchAbsVal (K := K), Yn v.val) ^ d := by
  have h1 : 1 ≤ (archAbsVal.map Ya).prod * ∏ᶠ v : nonarchAbsVal (K := K), Yn v.val :=
    one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun v _ => hYa v)
      (one_le_finprod fun v => hYn _)
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_pow₀ h1
  have : Nonempty ι := by
    by_contra h
    exact hx (funext fun i => (h ⟨i⟩).elim)
  rw [mulHeight_eq hx, mul_pow, ← Multiset.prod_map_pow, finprod_pow hfin]
  refine mul_le_mul ?_ ?_
    (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
    (Multiset.prod_map_nonneg fun v _ => by have := hYa v; positivity)
  · exact Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _) fun v hv => ciSup_le fun i => ha v hv i
  · by_cases hf : Function.HasFiniteMulSupport fun v : nonarchAbsVal (K := K) => ⨆ i, v.val (x i)
    · exact finprod_le_finprod₀ hf (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
        (hfin.subset (Function.mulSupport_pow _ d)) fun v => ciSup_le fun i => hn v.val v.prop i
    · rw [finprod_of_not_hasFiniteMulSupport hf]
      exact one_le_finprod fun v => one_le_pow₀ (hYn _)

/-- A finite family of polynomials over `K` has, at every place `v`, a bound `β v ≥ 1` on the
sizes of all its coefficients, with `β v = 1` at almost all nonarchimedean places, and a bound `T`
on its numbers of terms. -/
private lemma exists_abv_coeff_le {α τ : Type*} [Finite α] (g : α → MvPolynomial τ K) :
    ∃ β : AbsoluteValue K ℝ → ℝ, ∃ T : ℕ, (∀ v, 1 ≤ β v) ∧ (∀ v i a, v ((g i).coeff a) ≤ β v) ∧
      (∀ i, (g i).support.card ≤ T) ∧
      Function.HasFiniteMulSupport fun v : nonarchAbsVal (K := K) => β v.val := by
  classical
  have := Fintype.ofFinite α
  let F : Finset K := Finset.univ.biUnion fun i => (g i).support.image (g i).coeff
  refine ⟨fun v => ∏ z ∈ F, max (v z) 1, ∑ i, (g i).support.card,
    fun v => Finset.one_le_prod₀ fun z _ => le_max_right _ _, fun v i a => ?_,
    fun i => Finset.single_le_sum (f := fun i => (g i).support.card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i), ?_⟩
  · by_cases ha : a ∈ (g i).support
    · have hz : (g i).coeff a ∈ F :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ ha⟩
      change _ ≤ ∏ z ∈ F, max (v z) 1
      rw [← Finset.mul_prod_erase F _ hz]
      exact (le_max_left _ 1).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_right _ _))
        (Finset.one_le_prod₀ fun _ _ => le_max_right _ _))
    · rw [MvPolynomial.notMem_support_iff.mp ha, map_zero]
      exact zero_le_one.trans (Finset.one_le_prod₀ fun z _ => le_max_right _ _)
  · refine Set.Finite.subset (Set.Finite.biUnion F.finite_toSet fun z _ => ?_)
      (Finset.mulSupport_prod F fun z (v : nonarchAbsVal (K := K)) => max (v.val z) 1)
    by_cases hz : z = 0
    · simp [hz]
    · refine (AdmissibleAbsValues.hasFiniteMulSupport hz).subset fun v hv => ?_
      simp only [Function.mem_mulSupport] at hv ⊢
      contrapose! hv
      simp [hv]

end Height

section Algebra

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- Finitely many elements of `k(y)` have a common denominator: some `s(y) ≠ 0` with every
`s(y) c_a` a polynomial in `y`. -/
private lemma exists_aeval_mul_eq_aeval {τ : Type*} (y : τ → L) {α : Type*} [Finite α]
    (c : α → L) (hc : ∀ i, c i ∈ IntermediateField.adjoin k (Set.range y)) :
    ∃ s : MvPolynomial τ k, MvPolynomial.aeval y s ≠ 0 ∧
      ∃ p : α → MvPolynomial τ k, ∀ i,
        MvPolynomial.aeval y s * c i = MvPolynomial.aeval y (p i) := by
  classical
  have := Fintype.ofFinite α
  suffices h : ∀ S : Finset α, ∃ s : MvPolynomial τ k, MvPolynomial.aeval y s ≠ 0 ∧
      ∀ i ∈ S, ∃ p : MvPolynomial τ k, MvPolynomial.aeval y s * c i = MvPolynomial.aeval y p by
    obtain ⟨s, hs, hp⟩ := h Finset.univ
    choose p hp using hp
    exact ⟨s, hs, fun i => p i (Finset.mem_univ i), fun i => hp i _⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i S hi ih =>
    obtain ⟨s, hs, hp⟩ := ih
    obtain ⟨r, hr, t, ht, hrt⟩ := IntermediateField.mem_adjoin_iff_div.mp (hc i)
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨pr, rfl⟩ := hr
    obtain ⟨pt, rfl⟩ := ht
    by_cases h0 : MvPolynomial.aeval y pt = 0
    · refine ⟨s, hs, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨0, by simp [hrt, h0]⟩
      · exact hp j hj
    · refine ⟨s * pt, by simp [hs, h0], fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine ⟨s * pr, ?_⟩
        simp only [map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hrt ⊢
        rw [hrt]
        field_simp
      · obtain ⟨p, hp⟩ := hp j hj
        exact ⟨pt * p, by rw [map_mul, map_mul, ← hp]; ring⟩

/-- If `e` spans `L` over `k(y)`, every finite family `g` of elements of `L` acts on `e` by
matrices with polynomial entries, after clearing one common denominator `s(y) ≠ 0`. -/
private lemma exists_matrix {τ : Type*} (y : τ → L) {ι : Type*} [Fintype ι] (e : ι → L)
    (he : Submodule.span (IntermediateField.adjoin k (Set.range y)) (Set.range e) = ⊤)
    {β : Type*} [Finite β] (g : β → L) :
    ∃ s : MvPolynomial τ k, MvPolynomial.aeval y s ≠ 0 ∧
      ∃ m : β → Matrix ι ι (MvPolynomial τ k), ∀ b μ,
        MvPolynomial.aeval y s * g b * e μ = ∑ ν, MvPolynomial.aeval y (m b μ ν) * e ν := by
  have hmem (b : β) (μ : ι) : g b * e μ ∈
      Submodule.span (IntermediateField.adjoin k (Set.range y)) (Set.range e) := by
    rw [he]; trivial
  choose c hc using fun b μ => (Submodule.mem_span_range_iff_exists_fun _).mp (hmem b μ)
  obtain ⟨s, hs, p, hp⟩ := exists_aeval_mul_eq_aeval y
    (fun q : β × ι × ι => (c q.1 q.2.1 q.2.2 : L)) fun q => (c q.1 q.2.1 q.2.2).2
  refine ⟨s, hs, fun b μ ν => p (b, μ, ν), fun b μ => ?_⟩
  rw [mul_assoc, ← hc b μ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← hp (b, μ, ν)]
  change _ * ((c b μ ν : L) * e ν) = _
  ring

/-- Powers: if `r g e_μ = ∑_ν m_{μν}(y) e_ν` then `r^d g^d e_μ = ∑_ν (m^d)_{μν}(y) e_ν`. -/
private lemma pow_mul_eq_sum {τ : Type*} (y : τ → L) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → L) (r g : L) (m : Matrix ι ι (MvPolynomial τ k))
    (h : ∀ μ, r * g * e μ = ∑ ν, MvPolynomial.aeval y (m μ ν) * e ν) (d : ℕ) (μ : ι) :
    r ^ d * g ^ d * e μ = ∑ ν, MvPolynomial.aeval y ((m ^ d) μ ν) * e ν := by
  induction d with
  | zero =>
    simp [Matrix.one_apply]
  | succ d ih =>
    calc r ^ (d + 1) * g ^ (d + 1) * e μ = r * g * (r ^ d * g ^ d * e μ) := by ring
      _ = ∑ ν, MvPolynomial.aeval y ((m ^ d) μ ν) * (r * g * e ν) := by
        rw [ih, Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by ring
      _ = ∑ ρ, MvPolynomial.aeval y ((m ^ (d + 1)) μ ρ) * e ρ := by
        simp_rw [h, Finset.mul_sum, pow_succ, Matrix.mul_apply, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ν _ => by
          rw [map_mul]; ring

/-- If the `y₀^l y₁^{l'} e_ν` are linearly independent over `k`, then `∑_ν R_ν(y) e_ν = 0` forces
every `R_ν = 0`. -/
private lemma eq_zero_of_sum_aeval_mul_eq_zero (y : Fin 2 → L) {ι : Type*} [Fintype ι]
    (e : ι → L)
    (hind : LinearIndependent k fun t : ℕ × ℕ × ι => y 0 ^ t.1 * y 1 ^ t.2.1 * e t.2.2)
    (R : ι → MvPolynomial (Fin 2) k) (h : ∑ ν, MvPolynomial.aeval y (R ν) * e ν = 0) :
    R = 0 := by
  classical
  set S : Finset (Fin 2 →₀ ℕ) := Finset.univ.biUnion fun ν => (R ν).support
  let φ : (Fin 2 →₀ ℕ) × ι → ℕ × ℕ × ι := fun q => (q.1 0, q.1 1, q.2)
  have hφ : Function.Injective φ := by
    rintro ⟨a, ν⟩ ⟨a', ν'⟩ hq
    simp only [φ, Prod.mk.injEq] at hq
    obtain ⟨h0, h1, rfl⟩ := hq
    refine Prod.ext (Finsupp.ext fun i => ?_) rfl
    fin_cases i
    exacts [h0, h1]
  have hw := hind.comp φ hφ
  have hR (ν : ι) : MvPolynomial.aeval y (R ν) =
      ∑ a ∈ S, (R ν).coeff a • (y 0 ^ a 0 * y 1 ^ a 1) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_subset (Finset.subset_biUnion_of_mem (fun ν => (R ν).support)
      (Finset.mem_univ ν)) (fun a _ ha => by simp [MvPolynomial.notMem_support_iff.mp ha])
      |>.symm.trans ?_ |>.symm
    exact Finset.sum_congr rfl fun a _ => by
      simp [Fin.prod_univ_two, Algebra.smul_def]
  have hsum : ∑ q ∈ S ×ˢ (Finset.univ : Finset ι), (R q.2).coeff q.1 •
      ((fun t : ℕ × ℕ × ι => y 0 ^ t.1 * y 1 ^ t.2.1 * e t.2.2) ∘ φ) q = 0 := by
    rw [← h, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hR, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by simp [φ]
  funext ν
  ext a
  by_cases ha : a ∈ S
  · exact linearIndependent_iff'.mp hw _ _ hsum (a, ν) (Finset.mem_product.mpr ⟨ha, by simp⟩)
  · have : a ∉ (R ν).support := fun h' => ha (Finset.mem_biUnion.mpr ⟨ν, by simp, h'⟩)
    simpa using MvPolynomial.notMem_support_iff.mp this

end Algebra

section Coefficients

variable {K : Type*} [Field K]

/-- Multiplying by the monomial `X₀^l X₁^{l'}` only shifts the coefficients. -/
private lemma abv_coeff_mul_X_pow_le (v : AbsoluteValue K ℝ) {q : MvPolynomial (Fin 2) K} {B : ℝ}
    (hB : 0 ≤ B) (hq : ∀ a, v (q.coeff a) ≤ B) (l l' : ℕ) (a : Fin 2 →₀ ℕ) :
    v ((q * (MvPolynomial.X 0 ^ l * MvPolynomial.X 1 ^ l')).coeff a) ≤ B := by
  rw [show (MvPolynomial.X 0 ^ l * MvPolynomial.X 1 ^ l' : MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (Finsupp.single 0 l + Finsupp.single 1 l') 1 by
    simp [MvPolynomial.X_pow_eq_monomial],
    MvPolynomial.coeff_mul_monomial']
  split_ifs
  · simpa using hq _
  · simpa using hB

/-- A coefficient of `[P] q` is bounded by the bound for `q`. -/
private lemma abv_coeff_ite_le {τ : Type*} (v : AbsoluteValue K ℝ) {q : MvPolynomial τ K} {B : ℝ}
    (hB : 0 ≤ B) (hq : ∀ a, v (q.coeff a) ≤ B) (P : Prop) [Decidable P] (a : τ →₀ ℕ) :
    v ((if P then q else 0).coeff a) ≤ B := by
  split_ifs
  · exact hq a
  · simpa using hB

/-- A coefficient of `[P] q - [P'] q'` is bounded by the sum of the bounds for `q` and `q'`. -/
private lemma abv_coeff_ite_sub_ite_le {τ : Type*} (v : AbsoluteValue K ℝ)
    {q q' : MvPolynomial τ K} {B : ℝ} (hB : 0 ≤ B) (hq : ∀ a, v (q.coeff a) ≤ B)
    (hq' : ∀ a, v (q'.coeff a) ≤ B) (P P' : Prop) [Decidable P] [Decidable P'] (a : τ →₀ ℕ) :
    v (((if P then q else 0) - if P' then q' else 0).coeff a) ≤ B + B := by
  rw [MvPolynomial.coeff_sub]
  exact (v.sub_le_add _ _).trans
    (add_le_add (abv_coeff_ite_le v hB hq P a) (abv_coeff_ite_le v hB hq' P' a))

/-- At a nonarchimedean place, a coefficient of `[P] q - [P'] q'` is bounded by the common bound
for `q` and `q'`. -/
private lemma abv_coeff_ite_sub_ite_le_of_isNonarchimedean {τ : Type*} {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {q q' : MvPolynomial τ K} {B : ℝ} (hB : 0 ≤ B)
    (hq : ∀ a, v (q.coeff a) ≤ B) (hq' : ∀ a, v (q'.coeff a) ≤ B) (P P' : Prop) [Decidable P]
    [Decidable P'] (a : τ →₀ ℕ) :
    v (((if P then q else 0) - if P' then q' else 0).coeff a) ≤ B := by
  rw [MvPolynomial.coeff_sub, sub_eq_add_neg]
  refine (hv _ _).trans (max_le (abv_coeff_ite_le v hB hq P a) ?_)
  rw [AbsoluteValue.map_neg]
  exact abv_coeff_ite_le v hB hq' P' a

end Coefficients

section LinearSystem

variable {k : Type*} [Field k]

/-- The conditions `∑_i c_i B_{ip} = 0` (for all `p`) on `c ∈ k^ι`, for a finite family of
polynomials `B_{ip}`, are a finite linear system whose rows are coefficients of the `B_{ip}`. -/
private lemma exists_mulVec_eq_zero_iff {ι π τ : Type*} [Fintype ι] [Finite π]
    (B : ι → π → MvPolynomial τ k) :
    ∃ (κ : Type) (_ : Fintype κ) (A : Matrix κ ι k),
      (∀ c, A *ᵥ c = 0 ↔ ∀ p, ∑ i, c i • B i p = 0) ∧
        ∀ r, ∃ p a, ∀ i, A r i = (B i p).coeff a := by
  classical
  have := Fintype.ofFinite π
  let E : Finset (τ →₀ ℕ) := Finset.univ.biUnion fun q : ι × π => (B q.1 q.2).support
  let κ := ↥((Finset.univ : Finset π) ×ˢ E)
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fin (Fintype.card κ), inferInstance, fun r i => (B i (e r).1.1).coeff (e r).1.2,
    fun c => ?_, fun r => ⟨_, _, fun i => rfl⟩⟩
  have hcoeff (p : π) (a : τ →₀ ℕ) :
      (∑ i, c i • B i p).coeff a = ∑ i, (B i p).coeff a * c i := by
    simp [MvPolynomial.coeff_sum, mul_comm]
  refine ⟨fun h p => ?_, fun h => funext fun r =>
    (hcoeff _ _).symm.trans (by rw [h, MvPolynomial.coeff_zero]; rfl)⟩
  ext a
  rw [hcoeff, MvPolynomial.coeff_zero]
  by_cases ha : a ∈ E
  · have := congrFun h ((Fintype.equivFin κ) ⟨(p, a), Finset.mem_product.mpr ⟨by simp, ha⟩⟩)
    simpa [e, Matrix.mulVec, dotProduct] using this
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.notMem_support_iff.mp fun h' =>
      ha (Finset.mem_biUnion.mpr ⟨(i, p), Finset.mem_univ _, h'⟩), zero_mul]

end LinearSystem

open Height Height.AdmissibleAbsValues in
/-- **The basic system as a linear system of small height, from the independence of the
monomials.** Let `k` be a number field, `pr₁, pr₂ : K →ₐ[k] L` two embeddings of fields,
`ξ_a = x_a / x_{j₀}`, `ξ_b = x_b / x_{j₀}` with `x_{j₀} ≠ 0`, and `b_ν = basisB pr₁ pr₂ ξ_b ν`.
Suppose that the `(pr₁ ξ_a)^l (pr₂ ξ_a)^{l'} b_ν` are linearly independent over `k` and that the
`b_ν` span `L` over `k(pr₁ ξ_a, pr₂ ξ_a)`. Then for any `P_i, Q_i ∈ L` (`i ∈ σ`) there are
`c₁₃ ≥ 0` and `ε₁₃ ≥ 0` with `ε₁₃(d) → 0` such that for all `δ₁, δ₂` and `d ≥ 1` the tuple with
coordinates `f` lies in `affineEvaluationTuplesBasicSystem pr₁ pr₂ x j₀ (δ₁, δ₂) σ P Q d` if and
only if `A *ᵥ f = 0`, for a matrix `A` over `k` whose rows have absolute height at most
`c₁₃ d + ε₁₃(d) d`. -/
public theorem exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le_of_linearIndependent
    (k : Type*) [Field k] [NumberField k] {K L : Type*} [Field K] [Field L] [Algebra k K]
    [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) {ι : Type*} (x : ι → K) (j₀ a b : ι) (hx : x j₀ ≠ 0)
    (N : ℕ)
    (hind : LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ (x a / x j₀) ^ t.1 * pr₂ (x a / x j₀) ^ t.2.1 *
        Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j₀) t.2.2)
    (hspan : Submodule.span (IntermediateField.adjoin k {pr₁ (x a / x j₀), pr₂ (x a / x j₀)})
      (Set.range (Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j₀) (N := N))) = ⊤)
    (σ : Type*) [Fintype σ] (P Q : σ → L) :
    ∃ c₁₃ : ℝ, 0 ≤ c₁₃ ∧ ∃ ε₁₃ : ℕ → ℝ, (∀ d, 0 ≤ ε₁₃ d) ∧ Tendsto ε₁₃ atTop (𝓝 0) ∧
      ∀ δ₁ δ₂ d : ℕ, 0 < d →
        let M := {τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N) //
          (τ.1 : ℕ) + τ.2.2.1 ≤ δ₁ ∧ (τ.2.1 : ℕ) + τ.2.2.2 ≤ δ₂}
        ∃ (κ : Type) (_ : Fintype κ) (A : Matrix κ (σ × M) k),
          (∀ c : σ × M → k,
            (fun t => ∑ τ : M, algebraMap k L (c (t, τ)) *
                (pr₁ (x a / x j₀) ^ (τ.1.1 : ℕ) * pr₂ (x a / x j₀) ^ (τ.1.2.1 : ℕ) *
                  Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j₀) τ.1.2.2)) ∈
              affineEvaluationTuplesBasicSystem pr₁ pr₂ x j₀ (δ₁, δ₂) σ P Q d ↔
            A *ᵥ c = 0) ∧
          ∀ r, Height.logHeight (A r) / Module.finrank ℚ k ≤ c₁₃ * d + ε₁₃ d * d := by
  classical
  set y : Fin 2 → L := ![pr₁ (x a / x j₀), pr₂ (x a / x j₀)] with hy
  set e : Fin N × Fin N → L := Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j₀) with he_def
  have hspanE : Submodule.span (IntermediateField.adjoin k (Set.range y)) (Set.range e) = ⊤ := by
    rwa [hy, Matrix.range_cons_cons_empty]
  let G : σ × σ → L := fun q => P q.1 * Q q.2
  obtain ⟨s, hs, m, hm⟩ := exists_matrix y e hspanE G
  obtain ⟨β, T, hβ1, hβm, hT, hfin⟩ := exists_abv_coeff_le
    fun q : (σ × σ) × (Fin N × Fin N) × (Fin N × Fin N) => m q.1 q.2.1 q.2.2
  let X : AbsoluteValue k ℝ → ℝ := fun v =>
    (Fintype.card (Fin N × Fin N) : ℝ) ^ 1 * (T : ℝ) ^ 1 * β v
  have hX (v : AbsoluteValue k ℝ) : 0 ≤ X v := by have := hβ1 v; positivity
  let Ya : AbsoluteValue k ℝ → ℝ := fun v => 2 * X v + 1
  have hYa (v : AbsoluteValue k ℝ) : 1 ≤ Ya v := by linarith [hX v]
  let H : ℝ := (archAbsVal.map Ya).prod * ∏ᶠ v : nonarchAbsVal (K := k), β v.val
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le
    (Multiset.one_le_prod_map fun v _ => hYa v) (one_le_finprod fun v => hβ1 _)
  refine ⟨Real.log H / Module.finrank ℚ k, div_nonneg (Real.log_nonneg hH) (Nat.cast_nonneg _),
    fun _ => 0, fun _ => le_rfl, tendsto_const_nhds, fun δ₁ δ₂ d hd => ?_⟩
  intro M
  -- the polynomials whose coefficients are the linear forms
  let Z : σ × σ → M → Fin N × Fin N → MvPolynomial (Fin 2) k := fun q τ ν =>
    (m q ^ d) τ.1.2.2 ν * (MvPolynomial.X 0 ^ (τ.1.1 : ℕ) * MvPolynomial.X 1 ^ (τ.1.2.1 : ℕ))
  let B : σ × M → σ × σ × (Fin N × Fin N) → MvPolynomial (Fin 2) k := fun τ p =>
    (if τ.1 = p.2.1 then Z (p.1, p.2.1) τ.2 p.2.2 else 0) -
      (if τ.1 = p.1 then Z (p.2.1, p.1) τ.2 p.2.2 else 0)
  obtain ⟨κ, _, A, hA, hrow⟩ := exists_mulVec_eq_zero_iff B
  refine ⟨κ, inferInstance, A, fun c => ?_, fun r => ?_⟩
  · set u : σ → L := fun t => ∑ τ : M, algebraMap k L (c (t, τ)) *
        (pr₁ (x a / x j₀) ^ (τ.1.1 : ℕ) * pr₂ (x a / x j₀) ^ (τ.1.2.1 : ℕ) * e τ.1.2.2) with hu
    have hU0 : u ∈ affineEvaluationTuples pr₁ pr₂ x j₀ (δ₁, δ₂) σ := by
      rw [affineEvaluationTuples, Submodule.mem_pi]
      intro t _
      refine Submodule.sum_mem _ fun τ _ => ?_
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (mem_range_affineEvaluation pr₁ pr₂ x j₀ a b hx
        (δ₁, δ₂) _ _ _ _ τ.2.1 τ.2.2)
    have hexp (q : σ × σ) (t : σ) : MvPolynomial.aeval y s ^ d * (G q ^ d * u t) =
        ∑ ν, MvPolynomial.aeval y (∑ τ : M, c (t, τ) • Z q τ ν) * e ν := by
      simp only [hu, map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      calc _ = algebraMap k L (c (t, τ)) *
            (pr₁ (x a / x j₀) ^ (τ.1.1 : ℕ) * pr₂ (x a / x j₀) ^ (τ.1.2.1 : ℕ)) *
            (MvPolynomial.aeval y s ^ d * G q ^ d * e τ.1.2.2) := by ring
        _ = _ := by
          rw [pow_mul_eq_sum y e (MvPolynomial.aeval y s) (G q) (m q) (hm q) d τ.1.2.2,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun ν _ => ?_
          simp only [Z, map_mul, map_pow, MvPolynomial.aeval_X, Algebra.smul_def, hy,
            Matrix.cons_val_zero, Matrix.cons_val_one, AlgHom.commutes]
          ring
    have hRc (p : σ × σ × (Fin N × Fin N)) : ∑ τ, c τ • B τ p =
        ∑ τ : M, c (p.2.1, τ) • Z (p.1, p.2.1) τ p.2.2 -
          ∑ τ : M, c (p.1, τ) • Z (p.2.1, p.1) τ p.2.2 := by
      simp only [B, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, Fintype.sum_prod_type]
      rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => if x = p.1 then _ else _)]
      simp
    have hR (i i' : σ) : ∑ ν, MvPolynomial.aeval y (∑ τ, c τ • B τ (i, i', ν)) * e ν =
        MvPolynomial.aeval y s ^ d * (G (i, i') ^ d * u i' - G (i', i) ^ d * u i) := by
      rw [mul_sub, hexp, hexp, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hRc, map_sub, sub_mul]
    rw [affineEvaluationTuplesBasicSystem, Submodule.mem_inf, hA]
    refine (and_iff_right hU0).trans ?_
    change (∀ i i' : σ,
      (P i * Q i') ^ d * u i' = (P i' * Q i) ^ d * u i) ↔ _
    constructor
    · rintro h ⟨i, i', ν⟩
      refine congrFun (eq_zero_of_sum_aeval_mul_eq_zero y e hind
        (fun ν => ∑ τ, c τ • B τ (i, i', ν)) ?_) ν
      rw [hR, sub_eq_zero.mpr (h i i'), mul_zero]
    · intro h i i'
      have h0 := hR i i'
      simp only [h, map_zero, zero_mul, Finset.sum_const_zero] at h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp h0.symm).resolve_left (pow_ne_zero _ hs))
  · have hZa (v : AbsoluteValue k ℝ) (q : σ × σ) (τ : M) (ν : Fin N × Fin N) (a' : Fin 2 →₀ ℕ) :
        v ((Z q τ ν).coeff a') ≤ X v ^ d :=
      abv_coeff_mul_X_pow_le v (pow_nonneg (hX v) d) (fun a' => abv_coeff_pow_le v 1
        (abv_sum_le v) (m q) (hβ1 v) (fun μ ν => hβm v (q, μ, ν)) (fun μ ν => hT (q, μ, ν)) d _ _
        a') _ _ a'
    have hZn (v : AbsoluteValue k ℝ) (hv : v ∈ nonarchAbsVal (K := k)) (q : σ × σ) (τ : M)
        (ν : Fin N × Fin N) (a' : Fin 2 →₀ ℕ) : v ((Z q τ ν).coeff a') ≤ β v ^ d := by
      have := hβ1 v
      simpa using abv_coeff_mul_X_pow_le v
        (B := ((Fintype.card (Fin N × Fin N) : ℝ) ^ 0 * (T : ℝ) ^ 0 * β v) ^ d) (by positivity)
        (fun a' => abv_coeff_pow_le v 0
          (abv_sum_le_of_isNonarchimedean (AdmissibleAbsValues.isNonarchimedean v hv)) (m q)
          (hβ1 v) (fun μ ν => hβm v (q, μ, ν)) (fun μ ν => hT (q, μ, ν)) d τ.1.2.2 ν a')
        (τ.1.1 : ℕ) (τ.1.2.1 : ℕ) a'
    obtain ⟨⟨i, i', ν⟩, a', hr⟩ := hrow r
    have hlog : Height.logHeight (A r) ≤ d * Real.log H := by
      rw [Height.logHeight_eq_log_mulHeight, ← Real.log_pow]
      refine Real.log_le_log (Height.mulHeight_pos _)
        (mulHeight_le_pow _ d Ya β hYa hβ1 hfin (fun v _ τ => ?_) (fun v hv τ => ?_))
      · rw [hr]
        calc _ ≤ X v ^ d + X v ^ d := abv_coeff_ite_sub_ite_le v (pow_nonneg (hX v) d)
              (hZa v _ τ.2 ν) (hZa v _ τ.2 ν) _ _ a'
          _ ≤ 2 ^ d * X v ^ d := by
            rw [← two_mul]
            exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) hd.ne')
              (pow_nonneg (hX v) d)
          _ = (2 * X v) ^ d := (mul_pow _ _ _).symm
          _ ≤ Ya v ^ d :=
            pow_le_pow_left₀ (by linarith [hX v]) (le_add_of_nonneg_right zero_le_one) d
      · rw [hr]
        have := hβ1 v
        exact abv_coeff_ite_sub_ite_le_of_isNonarchimedean
          (AdmissibleAbsValues.isNonarchimedean v hv) (by positivity) (hZn v hv _ τ.2 ν)
          (hZn v hv _ τ.2 ν) _ _ a'
    calc Height.logHeight (A r) / Module.finrank ℚ k ≤ d * Real.log H / Module.finrank ℚ k :=
          div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _)
      _ = _ := by ring

open Height Height.AdmissibleAbsValues in
/-- **The basic system on `U₁` is a linear system of small height.** Let `C` be a smooth
projective geometrically integral curve of genus `g ≥ 2` over a number field `k`, `P` a divisor
of degree one supported on closed points, `N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of `L(NP)`
satisfying (G1) for `NP` and (G2), with
`ξ_ν = x_ν / x₀`. Let `L` be a field of fractions of `k(C) ⊗[k] k(C)`, with `pr₁ g = g ⊗ 1` and
`pr₂ g = 1 ⊗ g`, let `a ≠ b` be nonzero indices, and let `P_i, Q_i ∈ k[X₀, …, X₃]` (`i ∈ σ`), with
values `P_i(ξ, ξ'), Q_i(ξ, ξ')` at `(pr₁ ξ_a, pr₁ ξ_b, pr₂ ξ_a, pr₂ ξ_b)` and `Q_i(ξ, ξ') ≠ 0`.
Then there are `c₁₃ ≥ 0` and `ε₁₃ : ℕ → ℝ`, `ε₁₃ ≥ 0`, `ε₁₃(d) → 0`, such that for all `δ₁, δ₂`
and `d ≥ 1` there is a matrix `A` over `k` with columns the coordinates `(t, l, l', μ)` of `U₁`
(`l + μ₁ ≤ δ₁`, `l' + μ₂ ≤ δ₂`) such that the tuple
`t ↦ ∑ f (t, l, l', μ) (pr₁ ξ_a)^l (pr₂ ξ_a)^{l'} b_μ` lies in
`affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) σ P Q d` if and only if `A *ᵥ f = 0`, and
every row of `A` has absolute height at most `c₁₃ d + ε₁₃(d) d`. -/
@[faltings "lem_bvs_linear_system"]
public theorem exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le
    (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : Faltings.BombieriSiegel.SatisfiesG1 k f ((N : ℤ) • P₁) x)
    (hG2 : Faltings.BombieriSiegel.SatisfiesG2 k f x)
    (L : Type u) [Field L] [Algebra k L]
    [letI := functionFieldAlgebra k f; Algebra (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsScalarTower k (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsFractionRing (C.functionField ⊗[k] C.functionField) L]
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (hba : b ≠ a)
    (σ : Type*) [Fintype σ] (Pη Qη : σ → MvPolynomial (Fin 4) k) :
    letI := functionFieldAlgebra k f
    let pr₁ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeLeft
    let pr₂ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeRight
    let ev : MvPolynomial (Fin 4) k →ₐ[k] L := MvPolynomial.aeval
      ![pr₁ (x a / x 0), pr₁ (x b / x 0), pr₂ (x a / x 0), pr₂ (x b / x 0)]
    (∀ i, ev (Qη i) ≠ 0) →
    ∃ c₁₃ : ℝ, 0 ≤ c₁₃ ∧ ∃ ε₁₃ : ℕ → ℝ, (∀ d, 0 ≤ ε₁₃ d) ∧ Tendsto ε₁₃ atTop (𝓝 0) ∧
      ∀ δ₁ δ₂ d : ℕ, 0 < d →
        let M := {τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N) //
          (τ.1 : ℕ) + τ.2.2.1 ≤ δ₁ ∧ (τ.2.1 : ℕ) + τ.2.2.2 ≤ δ₂}
        ∃ (κ : Type) (_ : Fintype κ) (A : Matrix κ (σ × M) k),
          (∀ c : σ × M → k,
            (fun t => ∑ τ : M, algebraMap k L (c (t, τ)) *
                (pr₁ (x a / x 0) ^ (τ.1.1 : ℕ) * pr₂ (x a / x 0) ^ (τ.1.2.1 : ℕ) *
                  Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x 0) τ.1.2.2)) ∈
              affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) σ
                (fun i => ev (Pη i)) (fun i => ev (Qη i)) d ↔
            A *ᵥ c = 0) ∧
          ∀ r, Height.logHeight (A r) / Module.finrank ℚ k ≤ c₁₃ * d + ε₁₃ d * d := by
  let _ := functionFieldAlgebra k f
  intro pr₁ pr₂ ev _
  exact exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le_of_linearIndependent k pr₁ pr₂ x 0
    a b (hli.ne_zero 0) N
    (Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB k f hg P₁
      hP₁cl hP₁ N hN x hli hspan hG1 hG2 L a b ha hb hba)
    (Faltings.BombieriSiegel.linearIndependent_and_span_monomial_eq_top k f hg P₁
      hP₁cl hP₁ N hN x hli hspan hG1 hG2 L a a b b ha ha hb hb hba hba).2 σ _ _

end Faltings.BombieriVojta
