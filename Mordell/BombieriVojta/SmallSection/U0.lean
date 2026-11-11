module
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation

/-!
# The space `U₀`

Let `k` be a field, `C ⊆ ℙⁿ` a curve over `k` with coordinates `x = (x_ν)` in `k(C)`, and
`F ↦ F(ξ, ξ')` the `k`-linear evaluation of bihomogeneous forms of bidegree `(δ₁, δ₂)` over `k`
at the affine coordinates of `C × C` (`Faltings.BombieriVojta.affineEvaluation`). The space
`U₀ ⊆ k(C × C)^{m+1}` is the `k`-subspace of tuples `(F_i(ξ, ξ'))_{i=0}^m`, where
`F_0, …, F_m` range over the bihomogeneous forms of bidegree `(δ₁, δ₂)` over `k`.

## Main definitions

* `Faltings.BombieriVojta.affineEvaluationTuples`: the space `U₀`.

## Implementation notes

As for `Faltings.BombieriVojta.affineEvaluation`, `k(C)` and `k(C × C)` are arbitrary fields
`K`, `L` over `k` with `k`-algebra maps `pr₁ pr₂ : K →ₐ[k] L`. The index set `{0, …, m}` of the
tuple is an arbitrary type `σ`; the source's `U₀` is the case `σ = Fin (m + 1)`. Since the `F_i`
are chosen independently, `U₀` is the product over `σ` of copies of the image of the evaluation
map, `Submodule.pi Set.univ (fun _ => LinearMap.range (affineEvaluation pr₁ pr₂ x j δ))`.

## References

* [Bombieri1990], Sec. 8, pp. 630–631.
-/

namespace Faltings.BombieriVojta

/-- The space `U₀`: the `k`-subspace of `σ → L` of tuples `(F_i(ξ, ξ'))_{i ∈ σ}`, where each
`F_i` is a bihomogeneous form of bidegree `δ` over `k` and `F ↦ F(ξ, ξ')` is
`Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j δ`. -/
@[expose, faltings "def_bvs_space_u0"]
public noncomputable def affineEvaluationTuples {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (δ : ℕ × ℕ)
    (σ : Type*) : Submodule k (σ → L) :=
  Submodule.pi Set.univ fun _ : σ => LinearMap.range (affineEvaluation pr₁ pr₂ x j δ)

end Faltings.BombieriVojta
