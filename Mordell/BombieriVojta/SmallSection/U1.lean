module
public import Mordell.BombieriVojta.SmallSection.BasisB
public import Mordell.BombieriVojta.SmallSection.U0

/-!
# The space `U₁`

Let `k` be a field, `C ⊆ ℙⁿ` a curve over `k` with coordinates `x = (x_ν)` in `k(C)`, and write
`ξ_a = x_a / x₀` for the affine co-ordinates, `ξ_a` and `ξ'_a` for their pull-backs to `C × C`
along the two projections. For `ν ↔ (i, i') ∈ {0, …, N - 1}²` let `b_ν = ξ₂^i ξ'₂^{i'}`
(`Faltings.BombieriSiegel.basisB`). The space `U₁ ⊆ U₀ ⊆ k(C × C)^{m+1}` is the `k`-subspace of
tuples in `U₀` (`Faltings.BombieriVojta.affineEvaluationTuples`) each of whose entries is a
`k`-linear combination of the functions `ξ₁^l ξ₁'^{l'} b_ν` with `ν ∈ {0, …, N - 1}²`,
`0 ≤ l ≤ δ₁ - deg_{ξ₂} b_ν` and `0 ≤ l' ≤ δ₂ - deg_{ξ'₂} b_ν`.

## Main definitions

* `Faltings.BombieriVojta.affineEvaluationTuplesMonomial`: the space `U₁`.

## Implementation notes

As for `Faltings.BombieriVojta.affineEvaluationTuples`, `k(C)` and `k(C × C)` are arbitrary
fields `K`, `L` over `k` with `k`-algebra maps `pr₁ pr₂ : K →ₐ[k] L`, the distinguished
coordinate `x₀` is `x j`, and the tuple is indexed by an arbitrary type `σ`. The coordinates
`ξ₁` and `ξ₂` are `x a / x j` and `x b / x j` for indices `a`, `b`; the source's case is
`j = 0`, `a = 1`, `b = 2`. The bounds `l ≤ δ₁ - i`, `l' ≤ δ₂ - i'` are written
`l + i ≤ δ₁`, `l' + i' ≤ δ₂`, so that no triple occurs when `i > δ₁` (the source's subtraction
is in `ℤ`). `U₁` is the intersection of `U₀` with the product over `σ` of copies of the span of
these functions.

## References

* [Bombieri1990], Sec. 8, pp. 630–631.
-/

namespace Faltings.BombieriVojta

/-- The space `U₁`: the `k`-subspace of tuples in `U₀ = affineEvaluationTuples pr₁ pr₂ x j δ σ`
each of whose entries is a `k`-linear combination of the functions
`(pr₁ ξ₁)^l (pr₂ ξ₁)^{l'} b_ν`, where `ξ₁ = x a / x j`, `b_ν = basisB pr₁ pr₂ (x b / x j) ν`,
`ν ∈ Fin N × Fin N`, `l + ν.1 ≤ δ.1` and `l' + ν.2 ≤ δ.2`. -/
@[expose, faltings "def_bvs_space_u1"]
public noncomputable def affineEvaluationTuplesMonomial {k K L ι : Type*} [Field k] [Field K]
    [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι)
    (N : ℕ) (δ : ℕ × ℕ) (σ : Type*) : Submodule k (σ → L) :=
  affineEvaluationTuples pr₁ pr₂ x j δ σ ⊓
    Submodule.pi Set.univ fun _ : σ => Submodule.span k
      {f | ∃ (l l' : ℕ) (ν : Fin N × Fin N), l + ν.1 ≤ δ.1 ∧ l' + ν.2 ≤ δ.2 ∧
        f = pr₁ (x a / x j) ^ l * pr₂ (x a / x j) ^ l' *
          Faltings.BombieriSiegel.basisB pr₁ pr₂ (x b / x j) ν}

end Faltings.BombieriVojta
