module

public import Mordell.Height.Class.Basic
public import Mordell.Height.Machine.ClassZero

/-!
# Uniqueness of heights associated to a divisor class

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` and
`c ∈ Pic(X) ⊗ ℚ`. Any two heights associated to `c` differ by a bounded function on `X(k)`.

If `(m, γ)` and `(m', γ')` witness the two heights, then `cl(m'γ - mγ') ⊗ 1 = 0`, so
`cl(m'γ - mγ')` is torsion, killed by some `e ≥ 1`; Weil's theorem bounds
`h_{e(m'γ - mγ')} = e(m' h_γ - m h_{γ'})`, hence `h_γ / m - h_{γ'} / m'` is bounded.

## Main results

* `Faltings.IsHeightOfClass.exists_abs_sub_le`: if `h₁` and `h₂` are heights associated to
  `c`, then `|h₁ - h₂|` is bounded on `X(k)`.

## Implementation notes

Boundedness is stated as the existence of a uniform bound `C` on `|h₁ x - h₂ x|`. The base field
is an algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Hindry, Silverman, *Diophantine Geometry*, B.3][hindrysilverman2000]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

/-- An element of an abelian group whose image `x ⊗ 1` in `M ⊗ ℚ` vanishes is torsion. -/
public lemma exists_nsmul_eq_zero_of_tmul_one_eq_zero {M : Type*} [AddCommGroup M] {x : M}
    (h : x ⊗ₜ[ℤ] (1 : ℚ) = 0) : ∃ e : ℕ, 0 < e ∧ e • x = 0 := by
  have hl : IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (TensorProduct.isBaseChange ℤ M ℚ)
  have h' : TensorProduct.mk ℤ ℚ M 1 x = 0 := by
    simpa using congrArg (TensorProduct.comm ℤ M ℚ) h
  obtain ⟨⟨a, ha⟩, hax⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1)).mp h'
  refine ⟨a.natAbs, Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero ha), ?_⟩
  simp only [Submonoid.mk_smul] at hax
  rcases Int.natAbs_eq a with h'' | h'' <;> rw [h''] at hax <;> simpa using hax

/-- **The core of uniqueness.** If `cl(γ) ⊗ 1 = m c` and `cl(γ') ⊗ 1 = m' c`, then
`h_γ / m - h_{γ'} / m'` is bounded: `cl(m'γ - mγ')` is torsion, killed by some `e ≥ 1`, and
Weil's theorem bounds `h_{e(m'γ - mγ')} = e (m' h_γ - m h_{γ'})`. -/
public lemma exists_abs_inv_mul_height_sub_le {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {c : X.picardGroup ⊗[ℤ] ℚ} {m m' : ℕ} {γ γ' : EmbeddingGroup f}
    (hm : 0 < m) (hm' : 0 < m') (hγ : embeddingClass f γ ⊗ₜ[ℤ] (1 : ℚ) = m • c)
    (hγ' : embeddingClass f γ' ⊗ₜ[ℤ] (1 : ℚ) = m' • c) :
    ∃ C : ℝ, ∀ x, |(m : ℝ)⁻¹ * EmbeddingGroup.height f γ x -
      (m' : ℝ)⁻¹ * EmbeddingGroup.height f γ' x| ≤ C := by
  obtain ⟨e, he, he0⟩ := exists_nsmul_eq_zero_of_tmul_one_eq_zero
    (x := embeddingClass f (m' • γ - m • γ')) <| by
      rw [map_sub, map_nsmul, map_nsmul, sub_tmul, ← smul_tmul', ← smul_tmul', hγ, hγ',
        smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨C, hC⟩ := EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero
    (f := f) (γ := e • (m' • γ - m • γ')) (by rw [map_nsmul, he0])
  refine ⟨C / ((e : ℝ) * m * m'), fun x => ?_⟩
  rw [le_div_iff₀ (by positivity), ← abs_of_pos (by positivity : (0 : ℝ) < e * m * m'),
    ← abs_mul]
  refine le_of_eq_of_le ?_ (hC x)
  simp only [map_nsmul, map_sub, nsmul_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply]
  congr 1
  field_simp

/-- Two heights associated to the same class `c ∈ Pic(X) ⊗ ℚ` differ by a bounded function on
the `k`-points of `X`. -/
@[faltings "lem_ht_height_class_unique"]
public theorem IsHeightOfClass.exists_abs_sub_le {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {c : X.picardGroup ⊗[ℤ] ℚ} {h₁ h₂ : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ}
    (h₁c : IsHeightOfClass f c h₁) (h₂c : IsHeightOfClass f c h₂) :
    ∃ C : ℝ, ∀ x, |h₁ x - h₂ x| ≤ C := by
  obtain ⟨m, γ, hm, hγ, C₁, hC₁⟩ := h₁c
  obtain ⟨m', γ', hm', hγ', C₂, hC₂⟩ := h₂c
  obtain ⟨C, hC⟩ := exists_abs_inv_mul_height_sub_le hm hm' hγ hγ'
  refine ⟨C₁ + (C + C₂), fun x => (abs_sub_le _ _ _).trans <| add_le_add (hC₁ x) <|
    (abs_sub_le _ _ _).trans <| add_le_add (hC x) ?_⟩
  rw [abs_sub_comm]
  exact hC₂ x

end Faltings
