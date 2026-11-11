module
public import Mordell.BombieriVojta.Norm.FormNorm
public import Mordell.BombieriVojta.Norm.ReducedRepresentation

/-!
# The norm relation `G₀ U_iᵈ = G_i V_iᵈ`

Let `k(C)` and `k(C × C)` be fields `K`, `L` over `k` with the two projections
`pr₁ pr₂ : K →ₐ[k] L`, and let `x` be the co-ordinates of `C`, with `x₀ = x j`. Let
`η₀ = 1, η₁, …, η_m ∈ L` and let `F₀, …, F_m` be bihomogeneous forms of bidegree `(δ₁, δ₂)` over
`k` whose affine evaluations satisfy `F_i(ξ, ξ') = g · η_iᵈ` for one `g ≠ 0`. For the forms of a
representative of a section `s ≠ 0` of `𝒪(V)`, `g` is the ratio of `s` by
`x₀^{δ₁} x₀'^{δ₂} / y₀ᵈ` and `η_i = y_i / y₀`. Let `G_i = Faltings.BombieriRoth.formNorm` be the
norm of `F_i(ξ, ξ')` down to `k(ξ_a, ξ'_b)`, and `(U_i, V_i)` reduced representations of the
norms of the `η_i`. The norm is multiplicative, so `G_i = Norm g · (U_i / V_i)ᵈ` and
`G₀ = Norm g`; hence `G₀ U_iᵈ = G_i V_iᵈ` for every `i`.

## Main results

* `Faltings.IsReducedNormRepresentation.formNorm_mul_num_pow_eq`: `G₀ U_iᵈ = G_i V_iᵈ`.

## Implementation notes

The section `s` and its representative enter only through the identities
`F_i(ξ, ξ') = g · η_iᵈ`, which is the form in which they are hypotheses here; `s ≠ 0` becomes
`g ≠ 0`, `g` being the ratio of `s` by a local generator. The ring `R` holding `U_i, V_i` is any
ring embedded in `k⟮ξ_a, ξ'_b⟯` (in the source, `k[ξ_a, ξ'_b]`), and the relation is stated in
`k⟮ξ_a, ξ'_b⟯`, where the `G_i` live.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

namespace Faltings

open BombieriRoth BombieriVojta

/-- Let `F i` be bihomogeneous forms of bidegree `δ` over `k` whose affine evaluations are
`g · η iᵈ` for some `g ≠ 0`, where `η 0 = 1`, and let `(U, V)` be reduced representations of the
norms of the `η i` down to `k⟮ξ_a, ξ'_b⟯`, `ξ_a = pr₁ (x a) / pr₁ (x j)`,
`ξ'_b = pr₂ (x b) / pr₂ (x j)`, `a, b ≠ j`. Then the norms `G_i = formNorm pr₁ pr₂ x j a b δ (F i)`
satisfy `G₀ · U_iᵈ = G_i · V_iᵈ` for every `i`. -/
@[faltings "lem_bvr_norm_relation"]
public theorem IsReducedNormRepresentation.formNorm_mul_num_pow_eq
    {k K L ι R : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [CommRing R]
    (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j a b : ι) (ha : a ≠ j) (hb : b ≠ j) (δ : ℕ × ℕ)
    {m d : ℕ}
    [Algebra R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})]
    [FaithfulSMul R (IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)})]
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (g : L) (hg : g ≠ 0) (η : Fin (m + 1) → L) (hη₀ : η 0 = 1)
    (hF : ∀ i, affineEvaluation pr₁ pr₂ x j δ (F i) = g * η i ^ d)
    {U V : Fin (m + 1) → R}
    (hUV : IsReducedNormRepresentation R
      (K := IntermediateField.adjoin k {pr₁ (x a) / pr₁ (x j), pr₂ (x b) / pr₂ (x j)}) η U V)
    (i : Fin (m + 1)) :
    formNorm pr₁ pr₂ x j a b δ (F 0) * algebraMap R _ (U i) ^ d =
      formNorm pr₁ pr₂ x j a b δ (F i) * algebraMap R _ (V i) ^ d := by
  simp only [formNorm, hF, hη₀, one_pow, mul_one, map_mul, map_pow, hUV.algebraNorm_eq_div i,
    div_pow]
  rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero d <|
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R _)).mpr (hUV.ne_zero i))]

end Faltings
