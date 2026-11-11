module
public import Mordell.BombieriVojta.Norm.FormNorm
public import Mordell.BombieriVojta.Norm.ReducedRepresentation

/-!
# The polynomials `T_i`

Let `L = k(C × C)` with affine co-ordinate functions `ξ_ν = x_ν / x_0`, `ξ'_ν = x'_ν / x'_0` and
affine functions `η_0 = 1, η_1, …, η_m`, let `𝓕 = {F_i}` be a representative of a global section
of `𝒪(V)`, and let `1 ≤ a, b ≤ n`. With `G_0 = Norm_{L/k(ξ_a, ξ'_b)} F_0(ξ, ξ')` and `(U_i, V_i)`
reduced representations of the norms `Norm_{L/k(ξ_a, ξ'_b)} η_i` in `R = k[ξ_a, ξ'_b]`, set
`T_i = G_0 / V_i^d ∈ k(ξ_a, ξ'_b)`. Since `G_0 U_i^d = G_i V_i^d` and `U_i, V_i` are coprime in
the factorial ring `R`, `T_i` is a polynomial dividing `G_0`.

## Main definitions

* `Faltings.BombieriRoth.polynomialT`: the element `T_i = G_0 / V_i^d` of `k⟮ξ_a, ξ'_b⟯`.

## Implementation notes

The setting is that of `Faltings.BombieriRoth.formNorm`: the function fields `k(C)` and `k(C × C)`
are fields `K`, `L` over `k`, the projections are `k`-algebra maps `pr₁ pr₂ : K →ₐ[k] L`, and `x_0`
is `x j`. The ring `R` is any commutative ring with an algebra map to `k⟮ξ_a, ξ'_b⟯`, as in
`Faltings.IsReducedNormRepresentation`; in Bombieri's setting it is `k[ξ_a, ξ'_b]`. The quotient
`G_0 / V_i^d` is taken in the field `k⟮ξ_a, ξ'_b⟯`, so no divisibility is needed to define it.
Bombieri writes `T_i = G_i / U_i^d`; the two agree by the norm relation `G_0 U_i^d = G_i V_i^d`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*, §9, p. 632][bombieri1990]
-/

namespace Faltings.BombieriRoth

/-- Bombieri's polynomial `T_i = G_0 / V_i^d ∈ k(ξ_a, ξ'_b)`, where
`ξ_a = pr₁ (x a) / pr₁ (x j)`, `ξ'_b = pr₂ (x b) / pr₂ (x j)`,
`G_0 = formNorm pr₁ pr₂ x j a b δ (F 0)` is the norm of the affine evaluation of the form `F_0`,
and `(U_i, V_i)` is a family of reduced representations of the norms of `η_i` down to
`k⟮ξ_a, ξ'_b⟯`. -/
@[expose, faltings "def_bvr_polynomial_t"]
public noncomputable def polynomialT {k K L ι R : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [CommRing R] {m : ℕ}
    (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) (δ : ℕ × ℕ)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    [Algebra R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})]
    (η : Fin (m + 1) → L) (U V : Fin (m + 1) → R)
    (_hUV : IsReducedNormRepresentation
      (K := IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) R η U V)
    (d : ℕ) (i : Fin (m + 1)) :
    IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)} :=
  formNorm pr₁ pr₂ x j a b δ (F 0) /
    algebraMap R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})
      (V i) ^ d

end Faltings.BombieriRoth
