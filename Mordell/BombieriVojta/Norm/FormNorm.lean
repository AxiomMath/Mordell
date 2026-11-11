module
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation

/-!
# The norms `G_i`

Let `k` be a field, `C ⊆ ℙⁿ` a curve over `k` with coordinates `x = (x_0, …, x_n)`, and
`k(C × C)` the function field of `C × C` with its two projections `pr₁^*, pr₂^*`. On `C × C`
put `ξ_ν = x_ν / x_0` and `ξ'_ν = x'_ν / x'_0`. For a representative `{F_i}` of a section of
`𝒪(V)` and indices `1 ≤ a, b ≤ n`, the norms are
`G_i = Norm_{k(C × C) / k(ξ_a, ξ'_b)} F_i(ξ, ξ') ∈ k(ξ_a, ξ'_b)`,
where `F_i(ξ, ξ')` is the affine evaluation `Faltings.BombieriVojta.affineEvaluation`.

## Main definitions

* `Faltings.BombieriRoth.formNorm`: the norm `Norm_{L / k(ξ_a, ξ'_b)} F(ξ, ξ')` of the affine
  evaluation of a bihomogeneous form `F`, an element of the intermediate field `k⟮ξ_a, ξ'_b⟯`.

## Implementation notes

As for `Faltings.BombieriVojta.affineEvaluation`, the function fields `k(C)` and `k(C × C)` are
arbitrary fields `K`, `L` over `k`, the projections are `k`-algebra homomorphisms
`pr₁ pr₂ : K →ₐ[k] L`, and `x_0` is `x j` for a distinguished index `j`. The subfield
`k(ξ_a, ξ'_b)` is the intermediate field `k⟮ξ_a, ξ'_b⟯` of `L / k` and the norm is
`Algebra.norm`. The definition is made for a single bihomogeneous form `F`; the norms of a
representative `{F_i}` are `formNorm pr₁ pr₂ x j a b δ (F i)`. That the `F_i` form a
representative of a section of `𝒪(V)` plays no role in the definition and is a hypothesis of
the results about the `G_i`.

## References

* [Bombieri1990], Sec. 9, p. 632.
-/

namespace Faltings.BombieriRoth

/-- The norm `G = Norm_{L / k(ξ_a, ξ'_b)} F(ξ, ξ')` of the affine evaluation
`F(ξ, ξ') = Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j δ F` of a bihomogeneous form `F`
of bidegree `δ`, where `ξ_a = pr₁ (x a) / pr₁ (x j)` and `ξ'_b = pr₂ (x b) / pr₂ (x j)`; it lies
in the intermediate field `k⟮ξ_a, ξ'_b⟯` of `L / k`. For a representative `{F_i}` these are the
norms `G_i`. -/
@[expose, faltings "def_bvr_norms_g"]
public noncomputable def formNorm {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ) :
    IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)} :=
  Algebra.norm _ (Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x j δ F)

end Faltings.BombieriRoth
