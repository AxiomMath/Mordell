module
public import Mathlib
public import Mordell.Attr

/-!
# The affine functions `ξ_{νj}`, `ξ'_{νj}`, `η_{ij}` on `C × C`

Let `k` be a field, `C` a curve over `k` with function field `k(C)`, and `k(C × C)` the function
field of the surface `C × C`, with the two `k`-embeddings `pr₁^*, pr₂^* : k(C) → k(C × C)` given by
the projections. A basis `x = (x_ν)` of the Riemann–Roch space of `NP`, viewed inside `k(C)`,
gives the affine functions `ξ_{νj} = x_ν / x_j ∈ k(C)`, and the vector `ξ_j = (ξ_{νj})_ν`. On
`C × C` one writes `ξ_{νj}` for `pr₁^* ξ_{νj}` and `ξ'_{νj} = pr₂^* ξ_{νj}`. Likewise a basis
`y = (y_i)` of the sections of `𝒪(B)`, viewed inside `k(C × C)`, gives `η_{ij} = y_i / y_j`.
For a form `F(x, x')` in two sets of variables, `F(ξ_j, ξ'_{j'}) ∈ k(C × C)` is `F` evaluated at
`x_ν ↦ pr₁^* ξ_{νj}` and `x'_ν ↦ pr₂^* ξ_{νj'}`.

## Main definitions

* `Faltings.BombieriVojta.aevalAffineFunctions`: the `k`-algebra homomorphism
  `F ↦ F(ξ_j, ξ'_{j'})` from polynomials in the variables `x_ν, x'_ν` to `k(C × C)`.
* `Faltings.BombieriVojta.affineFunctionEta`: the function `η_{ij} = y_i / y_j` in `k(C × C)`,
  for the coordinates `y = (y_i)` of the embedding `φ_B` given by the sections of `𝒪(B)`.

## Implementation notes

The construction only uses the field structure: `k(C)` and `k(C × C)` are arbitrary fields `K`, `L`
over `k`, and the two projections are arbitrary `k`-algebra homomorphisms `pr₁ pr₂ : K →ₐ[k] L`.
The functions `ξ_{νj}` are the quotients `x ν / x j` in `K` and enter only through the
evaluation; `η_{ij}` is the quotient `y i / y j` in `L`, with `y : κ → L` the coordinates of `φ_B`
viewed as elements of the function field of `C × C`. The variables `x_ν` and `x'_ν` are indexed by
`Sum.inl ν` and `Sum.inr ν` in `MvPolynomial (ι ⊕ ι) k`. The evaluation is defined on all
polynomials; for a bihomogeneous form of bidegree `(δ₁, δ₂)` it is the source's `F(ξ_j, ξ'_{j'})`.

## References

* [Bombieri1990], Sec. 6, p. 625.
-/

namespace Faltings.BombieriVojta

public section

/-- `F ↦ F(ξ_j, ξ'_{j'})`: evaluation of a polynomial in the variables `x_ν` (`Sum.inl ν`) and
`x'_ν` (`Sum.inr ν`) at `x_ν ↦ pr₁ (x ν / x j)` and `x'_ν ↦ pr₂ (x ν / x j')`, i.e. at the affine
functions `ξ_{νj} ∘ pr₁` and `ξ'_{νj'} = ξ_{νj'} ∘ pr₂` on `C × C`. -/
@[expose, faltings "def_bv_affine_functions"]
public noncomputable def aevalAffineFunctions {k K L ι : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j j' : ι) :
    MvPolynomial (ι ⊕ ι) k →ₐ[k] L :=
  MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν / x j)) (fun ν => pr₂ (x ν / x j')))

/-- The function `η_{ij} = (y_i / y_j)|_{C × C}` in the function field `L = k(C × C)`, where
`y = (y_i)` are the coordinates of the embedding `φ_B` given by a basis of the sections of `𝒪(B)`,
viewed as elements of `L`. -/
@[expose, faltings "def_bv_affine_functions"]
public def affineFunctionEta {L κ : Type*} [Field L] (y : κ → L) (i j : κ) : L :=
  y i / y j

end

end Faltings.BombieriVojta
