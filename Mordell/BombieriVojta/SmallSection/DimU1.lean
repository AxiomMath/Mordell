module
public import Mordell.BombieriVojta.SmallSection.U1
public import Mordell.BombieriVojta.Projection.MonomialIndependence

/-!
# The dimension of `U₁`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one on `C`, `N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of the
Riemann–Roch space `L(NP) = H⁰(C, 𝒪(NP))` satisfying (G1) and (G2). Write `ξ_ν = x_ν / x₀`, and
on `C × C` write `ξ_ν`, `ξ'_ν` for its pull-backs along the two projections. The space
`U₁ ⊆ k(C × C)^{m+1}` consists of the tuples each of whose entries is a `k`-linear combination of
the functions `ξ_a^l ξ_a'^{l'} b_ν`, `b_ν = ξ_b^i ξ_b'^{i'}` for `ν = (i, i') ∈ {0, …, N - 1}²`,
with `l + i ≤ δ₁` and `l' + i' ≤ δ₂`. If `δ₁, δ₂ ≥ N - 1`, then
`dim U₁ = (m + 1)(N²δ₁δ₂ - N²(N - 3)/2 · (δ₁ + δ₂) + (N(N - 3)/2)²)`.

Indeed these functions are evaluations of monomials of bidegree `(δ₁, δ₂)`, so lie in `U₀`, and
they are linearly independent over `k`
(`Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`); for `ν = (i, i')` there are
`(δ₁ - i + 1)(δ₂ - i' + 1)` admissible pairs `(l, l')`, and
`∑_{i = 0}^{N - 1} (δ₁ - i + 1) = Nδ₁ - N(N - 3)/2`.

## Main results

* `Faltings.BombieriVojta.finrank_affineEvaluationTuplesMonomial_of_linearIndependent`: for any
  `k`-algebra maps `pr₁ pr₂ : K →ₐ[k] L`, the dimension of `U₁` once the monomials are linearly
  independent.
* `Faltings.BombieriVojta.finrank_affineEvaluationTuplesMonomial`: the dimension of `U₁`.
* `Faltings.BombieriVojta.MonomialIndex`, `Faltings.BombieriVojta.card_monomialIndex`,
  `Faltings.BombieriVojta.mem_range_affineEvaluation`: the exponents of the monomials spanning
  `U₁`, their number, and the monomials as affine evaluations of forms.

## Implementation notes

As in `Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`, sections of `𝒪(NP)`
are rational functions, `P` is a divisor `P₁ : C →₀ ℤ` of degree one supported on closed points,
`NP` is `(N : ℤ) • P₁`, and the function field of `C × C` is an
arbitrary field `L` with `IsFractionRing (k(C) ⊗[k] k(C)) L`, the two projections being
`g ↦ g ⊗ 1` and `g ↦ 1 ⊗ g`. The tuple is indexed by an arbitrary finite type `σ`; the source's
case is `σ = Fin (m + 1)`, of cardinality `m + 1`. The coordinates `ξ₁`, `ξ₂` of the source are
`ξ_a`, `ξ_b` for arbitrary distinct nonzero indices `a`, `b`. The formula is an identity in `ℚ`,
since `N(N - 3)/2` need not be a natural number.

The count itself needs none of the curve:
`finrank_affineEvaluationTuplesMonomial_of_linearIndependent` holds for arbitrary `k`-algebra
maps `pr₁ pr₂ : K →ₐ[k] L` and takes the independence of the monomials as a hypothesis, so that
it also applies to the projections into `k(C ×_k C)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 631
-/

open AlgebraicGeometry TensorProduct

universe u

namespace Faltings.BombieriVojta

/-- `∑_{i < N} (δ - i + 1) = Nδ - N(N - 3)/2` for `N - 1 ≤ δ`. -/
public lemma sum_sub_add_one (δ : ℕ) :
    ∀ N : ℕ, N - 1 ≤ δ → (∑ i : Fin N, ((δ - (i : ℕ) + 1 : ℕ) : ℚ)) = N * δ - N * ((N - 3) / 2)
  | 0, _ => by simp
  | N + 1, h => by
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
      sum_sub_add_one δ N (by omega)]
    push_cast [show N ≤ δ by omega]
    ring

/-- The exponents `(l, l', ν)` with `l + ν.1 ≤ δ₁` and `l' + ν.2 ≤ δ₂`, as a finite type. -/
public abbrev MonomialIndex (N δ₁ δ₂ : ℕ) :=
  Σ ν : Fin N × Fin N, Fin (δ₁ - ν.1 + 1) × Fin (δ₂ - ν.2 + 1)

/-- The exponent triple `(l, l', ν)` of an index. -/
@[expose] public def MonomialIndex.exponents {N δ₁ δ₂ : ℕ} (t : MonomialIndex N δ₁ δ₂) :
    ℕ × ℕ × (Fin N × Fin N) :=
  ((t.2.1 : ℕ), (t.2.2 : ℕ), t.1)

/-- There are `(Nδ₁ - N(N - 3)/2)(Nδ₂ - N(N - 3)/2)` exponents when `N - 1 ≤ δ₁, δ₂`. -/
public lemma card_monomialIndex (N δ₁ δ₂ : ℕ) (h₁ : N - 1 ≤ δ₁) (h₂ : N - 1 ≤ δ₂) :
    (Fintype.card (MonomialIndex N δ₁ δ₂) : ℚ) =
      (N * δ₁ - N * ((N - 3) / 2)) * (N * δ₂ - N * ((N - 3) / 2)) := by
  rw [← sum_sub_add_one δ₁ N h₁, ← sum_sub_add_one δ₂ N h₂, Finset.sum_mul_sum,
    ← Fintype.sum_prod_type']
  simp [MonomialIndex]

/-- The monomial `ξ_a^l ξ_a'^{l'} ξ_b^i ξ_b'^{i'}` with `l + i ≤ δ₁`, `l' + i' ≤ δ₂` is the
evaluation `F(ξ, ξ')` of the form
`F = x_j^{δ₁ - l - i} x_a^l x_b^i x_j'^{δ₂ - l' - i'} x_a'^{l'} x_b'^{i'}` of bidegree `δ`. -/
public lemma mem_range_affineEvaluation {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) (hj : x j ≠ 0)
    (δ : ℕ × ℕ) (l l' i i' : ℕ) (h₁ : l + i ≤ δ.1) (h₂ : l' + i' ≤ δ.2) :
    pr₁ (x a / x j) ^ l * pr₂ (x a / x j) ^ l' * (pr₁ (x b / x j) ^ i * pr₂ (x b / x j) ^ i') ∈
      LinearMap.range (affineEvaluation pr₁ pr₂ x j δ) := by
  set w : ι ⊕ ι → ℕ × ℕ := Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))
  set F : MvPolynomial (ι ⊕ ι) k :=
    MvPolynomial.X (.inl j) ^ (δ.1 - l - i) * MvPolynomial.X (.inl a) ^ l *
      MvPolynomial.X (.inl b) ^ i * (MvPolynomial.X (.inr j) ^ (δ.2 - l' - i') *
        MvPolynomial.X (.inr a) ^ l' * MvPolynomial.X (.inr b) ^ i')
  have hX : ∀ v, MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.X (R := k) v) (w v) :=
    MvPolynomial.isWeightedHomogeneous_X k w
  have hF : MvPolynomial.IsWeightedHomogeneous w F δ := by
    have := ((((hX (.inl j)).pow (δ.1 - l - i)).mul ((hX (.inl a)).pow l)).mul
      ((hX (.inl b)).pow i)).mul ((((hX (.inr j)).pow (δ.2 - l' - i')).mul
        ((hX (.inr a)).pow l')).mul ((hX (.inr b)).pow i'))
    convert this using 1
    ext <;> simp [w] <;> omega
  refine ⟨⟨F, hF⟩, ?_⟩
  have h0₁ : pr₁ (x j) ≠ 0 := by simpa using hj
  have h0₂ : pr₂ (x j) ≠ 0 := by simpa using hj
  have e₁ : pr₁ (x j) ^ δ.1 = pr₁ (x j) ^ (δ.1 - l - i) * pr₁ (x j) ^ l * pr₁ (x j) ^ i := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have e₂ : pr₂ (x j) ^ δ.2 =
      pr₂ (x j) ^ (δ.2 - l' - i') * pr₂ (x j) ^ l' * pr₂ (x j) ^ i' := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  simp only [affineEvaluation, LinearMap.coe_mk, AddHom.coe_mk, F, map_mul, map_pow,
    MvPolynomial.aeval_X, Sum.elim_inl, Sum.elim_inr, map_div₀]
  rw [e₁, e₂]
  simp only [div_pow]
  field_simp

/-- `Submodule.pi Set.univ (fun _ => W)` is linearly equivalent to `σ → W`. -/
private def piUnivEquiv {k M : Type*} [Semiring k] [AddCommMonoid M] [Module k M]
    (σ : Type*) (W : Submodule k M) :
    (Submodule.pi Set.univ fun _ : σ => W) ≃ₗ[k] (σ → W) where
  toFun y i := ⟨y.1 i, y.2 i trivial⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dimension of `Submodule.pi Set.univ (fun _ : σ => W)` is `|σ| · dim W`. -/
private lemma finrank_pi_univ_const {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (σ : Type*) [Fintype σ] (W : Submodule k M) [FiniteDimensional k W] :
    Module.finrank k (Submodule.pi Set.univ fun _ : σ => W) =
      Fintype.card σ * Module.finrank k W := by
  rw [(piUnivEquiv σ W).finrank_eq, Module.finrank_pi_fintype]
  simp

private lemma MonomialIndex.exponents_injective {N δ₁ δ₂ : ℕ} :
    Function.Injective (MonomialIndex.exponents (N := N) (δ₁ := δ₁) (δ₂ := δ₂)) := by
  rintro ⟨ν, p, q⟩ ⟨ν', p', q'⟩ h
  simp only [MonomialIndex.exponents, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  obtain rfl := Fin.ext h1
  obtain rfl := Fin.ext h2
  rfl

/-- The monomials `(pr₁ ξ₁)^l (pr₂ ξ₁)^{l'} b_ν`, `b_ν = (pr₁ ξ₂)^i (pr₂ ξ₂)^{i'}`, indexed by
`MonomialIndex N δ₁ δ₂`. -/
private def monomials {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (pr₁ pr₂ : K →ₐ[k] L) (ξ₁ ξ₂ : K) (N δ₁ δ₂ : ℕ) (t : MonomialIndex N δ₁ δ₂) : L :=
  pr₁ ξ₁ ^ t.exponents.1 * pr₂ ξ₁ ^ t.exponents.2.1 *
    Faltings.BombieriSiegel.basisB pr₁ pr₂ ξ₂ t.exponents.2.2

/-- For `N - 1 ≤ δ₁, δ₂`, the range of `monomials` is the generating set of `U₁`. -/
private lemma range_monomials {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (ξ₁ ξ₂ : K) {N δ₁ δ₂ : ℕ} (h₁ : N - 1 ≤ δ₁)
    (h₂ : N - 1 ≤ δ₂) :
    Set.range (monomials pr₁ pr₂ ξ₁ ξ₂ N δ₁ δ₂) =
      {f | ∃ (l l' : ℕ) (ν : Fin N × Fin N), l + ν.1 ≤ δ₁ ∧ l' + ν.2 ≤ δ₂ ∧
        f = pr₁ ξ₁ ^ l * pr₂ ξ₁ ^ l' * Faltings.BombieriSiegel.basisB pr₁ pr₂ ξ₂ ν} := by
  ext y
  constructor
  · rintro ⟨⟨ν, p, q⟩, rfl⟩
    exact ⟨p, q, ν, by omega, by omega, rfl⟩
  · rintro ⟨l, l', ν, h1, h2, rfl⟩
    exact ⟨⟨ν, ⟨l, by omega⟩, ⟨l', by omega⟩⟩, rfl⟩

/-- For `x j ≠ 0` and `N - 1 ≤ δ₁, δ₂`, every generator of `U₁` is an affine evaluation, so `U₁`
is the full product of the span of the monomials `ξ_a^l ξ_a'^{l'} b_ν`. -/
private lemma affineEvaluationTuplesMonomial_eq_pi {k K L ι : Type*} [Field k] [Field K]
    [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι)
    (hj : x j ≠ 0) {N δ₁ δ₂ : ℕ} (h₁ : N - 1 ≤ δ₁) (h₂ : N - 1 ≤ δ₂) (σ : Type*) :
    affineEvaluationTuplesMonomial pr₁ pr₂ x j a b N (δ₁, δ₂) σ =
      Submodule.pi Set.univ fun _ : σ => Submodule.span k
        (Set.range (monomials pr₁ pr₂ (x a / x j) (x b / x j) N δ₁ δ₂)) := by
  rw [affineEvaluationTuplesMonomial, range_monomials _ _ _ _ h₁ h₂]
  refine inf_eq_right.mpr (Submodule.pi_mono fun _ _ => Submodule.span_le.mpr ?_)
  rintro y ⟨l, l', ν, h1, h2, rfl⟩
  exact mem_range_affineEvaluation pr₁ pr₂ x j a b hj (δ₁, δ₂) l l' ν.1 ν.2 h1 h2

/-- **The dimension of `U₁`, from the independence of the monomials.** For `k`-algebra maps
`pr₁ pr₂ : K →ₐ[k] L`, `x j ≠ 0` and `N - 1 ≤ δ₁, δ₂`, if the monomials
`(pr₁ ξ)^l (pr₂ ξ)^{l'} b_ν`, `ξ = x a / x j`, `b_ν = basisB pr₁ pr₂ (x b / x j) ν`, are linearly
independent over `k`, then `affineEvaluationTuplesMonomial pr₁ pr₂ x j a b N (δ₁, δ₂) σ` has
dimension `|σ| (Nδ₁ - N(N - 3)/2)(Nδ₂ - N(N - 3)/2)` over `k`. -/
public theorem finrank_affineEvaluationTuplesMonomial_of_linearIndependent {k K L ι : Type*}
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K)
    (j a b : ι) (hj : x j ≠ 0) {N δ₁ δ₂ : ℕ} (hδ₁ : N - 1 ≤ δ₁) (hδ₂ : N - 1 ≤ δ₂)
    (hli : LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ (x a / x j) ^ t.1 * pr₂ (x a / x j) ^ t.2.1 *
        Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j) t.2.2)
    (σ : Type*) [Fintype σ] :
    (Module.finrank k (affineEvaluationTuplesMonomial pr₁ pr₂ x j a b N (δ₁, δ₂) σ) : ℚ) =
      Fintype.card σ * ((N * δ₁ - N * ((N - 3) / 2)) * (N * δ₂ - N * ((N - 3) / 2))) := by
  have hv : LinearIndependent k (monomials pr₁ pr₂ (x a / x j) (x b / x j) N δ₁ δ₂) :=
    hli.comp _ MonomialIndex.exponents_injective
  have := FiniteDimensional.span_of_finite k (Set.finite_range
    (monomials pr₁ pr₂ (x a / x j) (x b / x j) N δ₁ δ₂))
  rw [affineEvaluationTuplesMonomial_eq_pi pr₁ pr₂ x j a b hj hδ₁ hδ₂,
    finrank_pi_univ_const, finrank_span_eq_card hv]
  push_cast
  rw [card_monomialIndex N δ₁ δ₂ hδ₁ hδ₂]

/-- **The dimension of `U₁`.** Let `C` be a smooth projective geometrically integral curve of
genus `g ≥ 2` over a number field `k`, `P` a divisor of degree one supported on closed points,
`N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of `L(NP)` satisfying (G1) for `NP` and (G2). Let `L`
be a field of fractions of `k(C) ⊗[k] k(C)`, with projections `pr₁ g = g ⊗ 1`, `pr₂ g = 1 ⊗ g`.
For distinct nonzero `a, b` and `δ₁, δ₂ ≥ N - 1`, the space
`affineEvaluationTuplesMonomial pr₁ pr₂ x 0 a b N (δ₁, δ₂) σ` has dimension
`|σ| (N²δ₁δ₂ - N²(N - 3)/2 · (δ₁ + δ₂) + (N(N - 3)/2)²)` over `k`. -/
@[faltings "lem_bvs_dim_u1"]
public theorem finrank_affineEvaluationTuplesMonomial (k : Type u) [Field k] [NumberField k]
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
    (δ₁ δ₂ : ℕ) (hδ₁ : N - 1 ≤ δ₁) (hδ₂ : N - 1 ≤ δ₂) (σ : Type*) [Fintype σ] :
    letI := functionFieldAlgebra k f
    let pr₁ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeLeft
    let pr₂ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeRight
    (Module.finrank k (affineEvaluationTuplesMonomial pr₁ pr₂ x 0 a b N (δ₁, δ₂) σ) : ℚ) =
      Fintype.card σ * ((N : ℚ) ^ 2 * δ₁ * δ₂ - N ^ 2 * ((N - 3) / 2) * (δ₁ + δ₂) +
        (N * (N - 3) / 2) ^ 2) := by
  letI := functionFieldAlgebra k f
  intro pr₁ pr₂
  rw [finrank_affineEvaluationTuplesMonomial_of_linearIndependent pr₁ pr₂ x 0 a b (hli.ne_zero 0)
    hδ₁ hδ₂ (Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB k f hg P₁ hP₁cl hP₁
      N hN x hli hspan hG1 hG2 L a b ha hb hba)]
  ring

end Faltings.BombieriVojta
