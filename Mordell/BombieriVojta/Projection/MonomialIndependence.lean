module
public import Mordell.BombieriVojta.SmallSection.BasisB
public import Mordell.BombieriVojta.Projection.MonomialBasis

/-!
# Independence of the monomials `ξ_a^l ξ'_a^{l'} b_ν`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one on `C`, `N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of the
Riemann–Roch space `L(NP) = H⁰(C, 𝒪(NP))` inside `k(C)` satisfying (G1) and (G2). Write
`ξ_a = x_a / x₀ ∈ k(C)`, and on `C × C` write `ξ_a` for its pull-back along the first projection
and `ξ'_a` for its pull-back along the second. For `a ≠ j` in `{1, …, n}`, the functions
`ξ_a^l ξ'_a^{l'} b_ν`, where `l, l' ≥ 0`, `ν ∈ {0, …, N - 1}²` and `b_ν = ξ_j^i ξ'_j^{i'}` for
`ν = (i, i')`, are linearly independent over `k`. Bombieri uses the case `a = 1`, `j = 2`.

## Main results

* `Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB`: the family
  `(l, l', ν) ↦ ξ_a^l ξ'_a^{l'} b_ν` indexed by `ℕ × ℕ × (Fin N × Fin N)` is linearly independent
  over `k`.

## Implementation notes

As in `Faltings.BombieriSiegel.linearIndependent_and_span_monomial_eq_top`, sections of `𝒪(NP)`
are rational functions, `P` is a divisor `P₁ : C →₀ ℤ` of degree one supported on closed points,
`NP` is `(N : ℤ) • P₁`, and `k(C)` is a `k`-algebra through
`AlgebraicGeometry.functionFieldAlgebra k f`. Since `C` is geometrically integral over `k`, the
function field of `C × C` is the field of fractions of the domain `k(C) ⊗_k k(C)`, so it is an
arbitrary field `L` with `IsFractionRing (k(C) ⊗[k] k(C)) L`; the two projections are the
`k`-algebra maps `g ↦ g ⊗ 1` and `g ↦ 1 ⊗ g` followed by `k(C) ⊗[k] k(C) → L`, which are the
maps `Faltings.BombieriSiegel.basisB` takes.

The `b_ν` form a basis of `L` over `F = k(ξ_a, ξ'_a)`
(`Faltings.BombieriSiegel.linearIndependent_and_span_monomial_eq_top`), so it suffices that the
monomials `ξ_a^l ξ'_a^{l'}` are linearly independent over `k`. This is proved directly: `ξ_a` is
transcendental over `k` (a non-constant function on a geometrically irreducible curve in
characteristic zero), so `k[X] ⊗_k k[X] → k(C) ⊗_k k(C) → L` is injective, and it sends the
monomial basis `X^l ⊗ X^{l'}` to `ξ_a^l ξ'_a^{l'}`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 631
-/

open CategoryTheory AlgebraicGeometry IntermediateField TensorProduct

universe u

namespace Faltings.BombieriSiegel

/-- If `ξ, η` are transcendental over `k` and `K₁ ⊗_k K₂ → L` is injective, the monomials
`(ξ ⊗ 1)^l (1 ⊗ η)^{l'}` are linearly independent over `k` in `L`. -/
private lemma linearIndependent_pow_mul_pow {k K₁ K₂ L : Type*} [Field k] [CommRing K₁]
    [CommRing K₂] [CommRing L] [Algebra k K₁] [Algebra k K₂] [Algebra k L]
    (ψ : K₁ ⊗[k] K₂ →ₐ[k] L) (hψ : Function.Injective ψ) {ξ : K₁} {η : K₂}
    (hξ : Transcendental k ξ) (hη : Transcendental k η) :
    LinearIndependent k fun p : ℕ × ℕ => ψ (ξ ⊗ₜ 1) ^ p.1 * ψ (1 ⊗ₜ η) ^ p.2 := by
  have hmap := TensorProduct.map_injective_of_flat_flat (Polynomial.aeval (R := k) ξ).toLinearMap
    (Polynomial.aeval (R := k) η).toLinearMap (transcendental_iff_injective.mp hξ)
    (transcendental_iff_injective.mp hη)
  have := (((Polynomial.basisMonomials k).tensorProduct
    (Polynomial.basisMonomials k)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hmap)).map'
    ψ.toLinearMap (LinearMap.ker_eq_bot.mpr hψ)
  convert this using 1 <;> try rfl
  funext p
  simp [Module.Basis.tensorProduct_apply', ← map_pow, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- If the `b_ν` are linearly independent over `F = k⟮pr₁ ξ_a, pr₂ ξ_a⟯`, then the
`(pr₁ ξ_a)^l (pr₂ ξ_a)^{l'} b_ν` are linearly independent over `k`. -/
private lemma linearIndependent_pow_mul_pow_mul_basisB_of_linearIndependent (k : Type u)
    [Field k] [CharZero k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [GeometricallyIntegral f] {N n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (L : Type u) [Field L] [Algebra k L]
    [letI := functionFieldAlgebra k f; Algebra (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsScalarTower k (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsFractionRing (C.functionField ⊗[k] C.functionField) L]
    (a j : Fin (n + 1)) (ha : a ≠ 0) :
    letI := functionFieldAlgebra k f
    let pr₁ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeLeft
    let pr₂ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeRight
    LinearIndependent k⟮pr₁ (x a / x 0), pr₂ (x a / x 0)⟯ (basisB pr₁ pr₂ (x j / x 0) (N := N)) →
    LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ (x a / x 0) ^ t.1 * pr₂ (x a / x 0) ^ t.2.1 * basisB pr₁ pr₂ (x j / x 0) t.2.2 := by
  let := functionFieldAlgebra k f
  intro pr₁ pr₂ hB
  set ξ := x a / x 0
  set F := k⟮pr₁ ξ, pr₂ ξ⟯
  have hT : Transcendental k ξ :=
    FunctionField.transcendental_of_notMem_range f (div_notMem_range_algebraMap hli ha)
  have h₁ : pr₁ ξ ∈ F := IntermediateField.subset_adjoin k _ (by simp)
  have h₂ : pr₂ ξ ∈ F := IntermediateField.subset_adjoin k _ (by simp)
  let wF : ℕ × ℕ → F := fun p => ⟨pr₁ ξ ^ p.1 * pr₂ ξ ^ p.2,
    mul_mem (pow_mem h₁ p.1) (pow_mem h₂ p.2)⟩
  have hwF : LinearIndependent k wF :=
    .of_comp (IsScalarTower.toAlgHom k F L).toLinearMap <| linearIndependent_pow_mul_pow
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L)
      (IsFractionRing.injective (C.functionField ⊗[k] C.functionField) L) hT hT
  have : IsScalarTower k F L := IntermediateField.isScalarTower_mid' F
  convert (linearIndependent_smul hwF hB).comp _
    (Equiv.prodAssoc ℕ ℕ (Fin N × Fin N)).symm.injective using 1
  funext t
  simp [wF, basisB, Algebra.smul_def, mul_assoc]

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `P` a divisor of degree one supported on closed points, `N ≥ 2g + 1`, and `x₀, …, xₙ` a
`k`-basis of `L(NP)` satisfying (G1) for `NP` and (G2), with `ξ_ν = x_ν / x₀`. Let `L` be a field
of fractions of `k(C) ⊗[k] k(C)`, the function field of `C × C`, with projections `pr₁ g = g ⊗ 1`
and `pr₂ g = 1 ⊗ g`. For distinct nonzero `a, j`, the functions `(pr₁ ξ_a)^l (pr₂ ξ_a)^{l'} b_ν`,
with `b_ν = basisB pr₁ pr₂ ξ_j ν`, indexed by `(l, l', ν) ∈ ℕ × ℕ × (Fin N × Fin N)`, are linearly
independent over `k`. -/
@[faltings "lem_bvs_monomials_independent"]
public theorem linearIndependent_pow_mul_pow_mul_basisB (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (L : Type u) [Field L] [Algebra k L]
    [letI := functionFieldAlgebra k f; Algebra (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsScalarTower k (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsFractionRing (C.functionField ⊗[k] C.functionField) L]
    (a j : Fin (n + 1)) (ha : a ≠ 0) (hj : j ≠ 0) (hja : j ≠ a) :
    letI := functionFieldAlgebra k f
    let pr₁ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeLeft
    let pr₂ : C.functionField →ₐ[k] L :=
      (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) L).comp
        Algebra.TensorProduct.includeRight
    LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ (x a / x 0) ^ t.1 * pr₂ (x a / x 0) ^ t.2.1 * basisB pr₁ pr₂ (x j / x 0) t.2.2 :=
  linearIndependent_pow_mul_pow_mul_basisB_of_linearIndependent k f x hli L a j ha
    (linearIndependent_and_span_monomial_eq_top k f hg P₁ hP₁cl hP₁ N hN x hli
      hspan hG1 hG2 L a a j j ha ha hj hj hja hja).1

end Faltings.BombieriSiegel
