module

public import Mordell.Height.Class.Basic
public import Mordell.Height.Machine.EmbeddingClassSurjective

/-!
# Existence of heights associated to divisor classes

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), with structure morphism `f : X ⟶ Spec k`. Every class `c ∈ Pic(X) ⊗ ℚ` has an
associated height: a function `h : X(k) → ℝ` with `Faltings.IsHeightOfClass f c h`.

## Main results

* `Faltings.exists_isHeightOfClass`: every `c ∈ Pic(X) ⊗ ℚ` has an associated height.

## Implementation notes

The base field is an algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`. The proof
writes `m c = c₀ ⊗ 1` with `c₀ ∈ Pic(X)` and `c₀ = cl(ψ) - cl(φ)` for projective embeddings
`φ, ψ`; then `(1/m) h_{ψ - φ}` is a height associated to `c`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

/-- Every element of `M ⊗[ℤ] ℚ` has a positive integer multiple of the form `c₀ ⊗ 1`: this is
surjectivity onto `ℚ ⊗[ℤ] M` as the localization of `M` at the nonzero integers. -/
private theorem exists_nsmul_eq_tmul_one {M : Type*} [AddCommGroup M] (c : M ⊗[ℤ] ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ c₀ : M, c₀ ⊗ₜ[ℤ] (1 : ℚ) = m • c := by
  obtain ⟨⟨c₀, s, hs⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ M 1) (TensorProduct.comm ℤ _ _ c)
  refine ⟨s.natAbs, Int.natAbs_pos.2 (nonZeroDivisors.ne_zero hs), s.sign • c₀, ?_⟩
  apply (TensorProduct.comm ℤ M ℚ).injective
  simp only [Submonoid.smul_def] at h
  rw [map_nsmul, ← natCast_zsmul, Int.natCast_natAbs, ← Int.sign_mul_self_eq_abs, mul_smul, h]
  simp [TensorProduct.tmul_smul]

/-- Every class `c ∈ Pic(X) ⊗ ℚ` on a smooth projective variety `X` over a field algebraic
over `ℚ` has an associated height: writing `m • c = c₀ ⊗ 1` and `c₀ = cl(ψ) - cl(φ)`, the
function `(1/m) h_{ψ - φ}` is one. -/
@[faltings "lem_ht_height_class_exists"]
public theorem exists_isHeightOfClass {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [Smooth f] (c : X.picardGroup ⊗[ℤ] ℚ) :
    ∃ h : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ, IsHeightOfClass f c h := by
  obtain ⟨m, hm, c₀, hc₀⟩ := exists_nsmul_eq_tmul_one c
  obtain ⟨a, b, φ, ψ, hcl⟩ := exists_embeddingClass_sub_eq f c₀
  set γ : EmbeddingGroup f := FreeAbelianGroup.of ⟨b, ψ⟩ - FreeAbelianGroup.of ⟨a, φ⟩
  refine ⟨fun x => (m : ℝ)⁻¹ * EmbeddingGroup.height f γ x, m, γ, hm, ?_, 0, fun x => by simp⟩
  rw [map_sub, hcl, hc₀]

end Faltings
