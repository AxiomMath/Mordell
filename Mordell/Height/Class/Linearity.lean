module

public import Mordell.Height.Class.Basic

/-!
# Linearity of heights associated to divisor classes

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), with structure morphism `f : X ⟶ Spec k`. If `h_c` and `h_{c'}` are heights
associated to classes `c, c' ∈ Pic(X) ⊗ ℚ` and `a, a' ∈ ℚ`, then `a h_c + a' h_{c'}` is a
height associated to `a c + a' c'`.

The statement splits into two closure properties, each proved by exhibiting a witness and using
the additivity of `γ ↦ cl(γ)` and of `γ ↦ h_γ`:

* sums: if `(m, γ)` and `(m', γ')` are witnesses for `h` and `h'`, then
  `(m m', m' γ + m γ')` is a witness for `h + h'`;
* rational multiples: if `(m, γ)` is a witness for `h` and `a = A / D` in lowest terms, then
  `(D m, A γ)` is a witness for `a h`.

## Main results

* `Faltings.IsHeightOfClass.linearCombination`: heights associated to divisor classes
  combine linearly with rational coefficients.
* `Faltings.isHeightOfClass_ratMul`: the case of a single rational multiple.

## Implementation notes

`Pic(X) ⊗ ℚ` is `X.picardGroup ⊗[ℤ] ℚ`. Mathlib puts no `ℚ`-module instance on it (the
scalars act on the right factor), so `a c` is written `(id ⊗ (a · ·)) c`, that is
`LinearMap.lTensor _ (LinearMap.mulLeft ℤ a) c`.
The base field is an algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

/-- Multiplying the `ℚ` factor of `P ⊗[ℤ] ℚ` by `n * q` is the `ℤ`-action of `n` after
multiplying by `q`. -/
private lemma lTensor_mulLeft_intCast_mul {P : Type*} [AddCommGroup P] (n : ℤ) (q : ℚ)
    (x : P ⊗[ℤ] ℚ) :
    LinearMap.lTensor P (LinearMap.mulLeft ℤ ((n : ℚ) * q)) x =
      n • LinearMap.lTensor P (LinearMap.mulLeft ℤ q) x := by
  have : LinearMap.mulLeft ℤ ((n : ℚ) * q) = n • LinearMap.mulLeft ℤ q := by
    ext r; simp
  rw [this, LinearMap.lTensor_smul, LinearMap.smul_apply]

/-- Multiplying the `ℚ` factor of `P ⊗[ℤ] ℚ` by `1` is the identity. -/
private lemma lTensor_mulLeft_one {P : Type*} [AddCommGroup P] (x : P ⊗[ℤ] ℚ) :
    LinearMap.lTensor P (LinearMap.mulLeft ℤ (1 : ℚ)) x = x := by
  rw [LinearMap.mulLeft_one, LinearMap.lTensor_id, LinearMap.id_apply]

section Closure

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f] {c c' : X.picardGroup ⊗[ℤ] ℚ}
  {h h' : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ}

/-- Heights associated to divisor classes are closed under sums. -/
private lemma isHeightOfClass_add (hc : IsHeightOfClass f c h)
    (hc' : IsHeightOfClass f c' h') :
    IsHeightOfClass f (c + c') (fun x ↦ h x + h' x) := by
  obtain ⟨m, γ, hm, hγ, C, hC⟩ := hc
  obtain ⟨m', γ', hm', hγ', C', hC'⟩ := hc'
  refine ⟨m * m', m' • γ + m • γ', by positivity, ?_, C + C', fun x ↦ ?_⟩
  · rw [map_add, map_nsmul, map_nsmul, add_tmul, ← smul_tmul', ← smul_tmul', hγ, hγ',
      smul_add, smul_smul, smul_smul, mul_comm m' m]
  · have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hm0' : (m' : ℝ) ≠ 0 := by positivity
    have : h x + h' x - ((m * m' : ℕ) : ℝ)⁻¹ * EmbeddingGroup.height f (m' • γ + m • γ') x =
        (h x - (m : ℝ)⁻¹ * EmbeddingGroup.height f γ x) +
          (h' x - (m' : ℝ)⁻¹ * EmbeddingGroup.height f γ' x) := by
      simp only [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add (hC x) (hC' x))

/-- Heights associated to divisor classes are closed under rational multiples: if `h` is a
height associated to `c`, then `a h` is a height associated to `a c` for `a ∈ ℚ`. -/
lemma isHeightOfClass_ratMul (hc : IsHeightOfClass f c h) (a : ℚ) :
    IsHeightOfClass f (LinearMap.lTensor _ (LinearMap.mulLeft ℤ a) c)
      (fun x ↦ (a : ℝ) * h x) := by
  obtain ⟨m, γ, hm, hγ, C, hC⟩ := hc
  refine ⟨a.den * m, a.num • γ, by positivity, ?_, |(a : ℝ)| * C, fun x ↦ ?_⟩
  · rw [map_zsmul, ← smul_tmul', hγ, mul_comm, mul_nsmul, ← natCast_zsmul _ a.den,
      smul_comm (a.den : ℤ) m, ← lTensor_mulLeft_intCast_mul, Int.cast_natCast,
      Rat.den_mul_eq_num,
      ← mul_one (a.num : ℚ), lTensor_mulLeft_intCast_mul, lTensor_mulLeft_one, smul_comm]
  · have hd : (a.den : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have ha : (a : ℝ) = a.num / a.den := by exact_mod_cast (Rat.num_div_den a).symm
    have : (a : ℝ) * h x - ((a.den * m : ℕ) : ℝ)⁻¹ * EmbeddingGroup.height f (a.num • γ) x =
        (a : ℝ) * (h x - (m : ℝ)⁻¹ * EmbeddingGroup.height f γ x) := by
      simp only [map_zsmul, Pi.smul_apply, zsmul_eq_mul]
      rw [ha]
      push_cast
      field_simp
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

end Closure

/-- If `h` and `h'` are heights associated to `c, c' ∈ Pic(X) ⊗ ℚ`, then for `a, a' ∈ ℚ`,
`a h + a' h'` is a height associated to `a c + a' c'`. -/
@[faltings "lem_ht_height_class_linear"]
public theorem IsHeightOfClass.linearCombination {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] {c c' : X.picardGroup ⊗[ℤ] ℚ}
    {h h' : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ}
    (hc : IsHeightOfClass f c h) (hc' : IsHeightOfClass f c' h') (a a' : ℚ) :
    IsHeightOfClass f
      (LinearMap.lTensor _ (LinearMap.mulLeft ℤ a) c +
        LinearMap.lTensor _ (LinearMap.mulLeft ℤ a') c')
      (fun x ↦ (a : ℝ) * h x + (a' : ℝ) * h' x) :=
  isHeightOfClass_add (isHeightOfClass_ratMul hc a) (isHeightOfClass_ratMul hc' a')

end Faltings
