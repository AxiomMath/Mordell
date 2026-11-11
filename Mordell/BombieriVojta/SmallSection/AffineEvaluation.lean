module
public import Mathlib
public import Mordell.Attr

/-!
# Forms in affine coordinates

Let `k` be a field, `C` a curve over `k` with function field `k(C)`, and `k(C × C)` the function
field of `C × C`, with the two `k`-embeddings `pr₁^*, pr₂^* : k(C) → k(C × C)`. Let
`x = (x_ν)` be the coordinates of `C ⊆ ℙⁿ`, viewed as elements of `k(C)` (after a choice of
trivialisation), and `x'_ν = pr₂^* x_ν`. A bihomogeneous form `F(x, x')` of bidegree `(δ₁, δ₂)`
with coefficients in `k` gives the rational function
`F(ξ, ξ') = (F(x, x') / (x₀^{δ₁} x₀'^{δ₂}))|_{C × C} ∈ k(C × C)`;
it is well defined because the quotient is bihomogeneous of bidegree `(0, 0)`, so it does not
depend on the trivialisation, and it is `F` evaluated at the affine coordinates
`ξ_ν = x_ν / x₀`, `ξ'_ν = x'_ν / x₀'`.

## Main definitions

* `Faltings.BombieriVojta.affineEvaluation`: the `k`-linear map `F ↦ F(ξ, ξ')` on the
  bihomogeneous forms of bidegree `(δ₁, δ₂)`.

## Implementation notes

Only the field structure enters: `k(C)` and `k(C × C)` are arbitrary fields `K`, `L` over `k`
and the projections are arbitrary `k`-algebra homomorphisms `pr₁ pr₂ : K →ₐ[k] L`. The variables
`x_ν`, `x'_ν` are `Sum.inl ν`, `Sum.inr ν` in `MvPolynomial (ι ⊕ ι) k`, as for
`Faltings.BombieriVojta.aevalAffineFunctions`, and the bihomogeneous forms of bidegree
`(δ₁, δ₂)` are `MvPolynomial.weightedHomogeneousSubmodule` for the `ℕ × ℕ`-valued weight giving
`x_ν` the weight `(1, 0)` and `x'_ν` the weight `(0, 1)`. The distinguished coordinate `x₀` is
`x j` for an arbitrary index `j`.

## References

* [Bombieri1990], Sec. 8, p. 629.
-/

namespace Faltings.BombieriVojta

/-- `F ↦ F(ξ, ξ') = F(x, x') / (x₀^{δ₁} x₀'^{δ₂})` on `C × C`: for a bihomogeneous form `F` of
bidegree `δ = (δ₁, δ₂)` in the variables `x_ν` (`Sum.inl ν`, weight `(1, 0)`) and `x'_ν`
(`Sum.inr ν`, weight `(0, 1)`), the quotient of `F` evaluated at `x_ν ↦ pr₁ (x ν)`,
`x'_ν ↦ pr₂ (x ν)` by `pr₁ (x j) ^ δ₁ * pr₂ (x j) ^ δ₂`. -/
@[expose, faltings "def_bvs_affine_evaluation"]
public noncomputable def affineEvaluation {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι) (δ : ℕ × ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ
      →ₗ[k] L where
  toFun F := MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) F.1 /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2)
  map_add' F G := by simp [add_div]
  map_smul' c F := by simp [Algebra.smul_def, mul_div_assoc]

end Faltings.BombieriVojta
