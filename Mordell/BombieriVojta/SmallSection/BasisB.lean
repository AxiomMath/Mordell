module
public import Mathlib
public import Mordell.Attr

/-!
# The functions `b_ν` on `C × C`

Let `k` be a field, `C` a curve over `k` with function field `k(C)`, and `k(C × C)` the function
field of the surface `C × C`, with the two `k`-embeddings `pr₁^*, pr₂^* : k(C) → k(C × C)` given by
the projections. For the affine co-ordinate function `ξ₂ = (x₂ / x₀)|_C ∈ k(C)` write `ξ₂` also for
`pr₁^* ξ₂` and `ξ'₂ = pr₂^* ξ₂`. For `ν ↔ (i, i') ∈ {0, …, N - 1}²` Bombieri puts
`b_ν = ξ₂^i ξ'₂^{i'} ∈ k(C × C)`, and writes `deg_{ξ₂} b_ν = i`, `deg_{ξ'₂} b_ν = i'`.

## Main definitions

* `Faltings.BombieriSiegel.basisB`: the monomial `b_ν = (pr₁ ξ)^i (pr₂ ξ)^{i'}` for
  `ν = (i, i') : Fin N × Fin N`.

## Implementation notes

As for `Faltings.BombieriVojta.aevalAffineFunctions`, only the field structure is used: `k(C)` and
`k(C × C)` are arbitrary fields `K`, `L` over `k`, and the two projections are arbitrary
`k`-algebra homomorphisms `pr₁ pr₂ : K →ₐ[k] L`. The function `ξ₂` is an argument `ξ : K`; in the
application it is `x 2 / x 0` for the basis `x` of `H⁰(C, 𝒪(N P))`. The index `ν` is the pair
`(i, i') : Fin N × Fin N` itself, so the degrees `deg_{ξ₂} b_ν` and `deg_{ξ'₂} b_ν` are the
components `ν.1` and `ν.2`, and need no declaration of their own.

## References

* [Bombieri1990], Sec. 8, pp. 630–631.
-/

namespace Faltings.BombieriSiegel

/-- The function `b_ν = ξ₂^i ξ'₂^{i'}` on `C × C` for `ν = (i, i') ∈ {0, …, N - 1}²`, where
`ξ₂` is pulled back along the first projection `pr₁` and `ξ'₂` along the second projection
`pr₂`. Its degrees in `ξ₂` and `ξ'₂` are `ν.1` and `ν.2`. -/
@[expose, faltings "def_bvs_basis_b"]
public def basisB {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (ξ : K) {N : ℕ} (ν : Fin N × Fin N) : L :=
  pr₁ ξ ^ (ν.1 : ℕ) * pr₂ ξ ^ (ν.2 : ℕ)

end Faltings.BombieriSiegel
