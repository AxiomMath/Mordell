module

public import Mordell.NeronTate.Uniqueness
public import Mordell.NeronTate.Existence
public import Mordell.Height.Class.Linearity

/-!
# Additivity of the Néron–Tate height in the class

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field), `c, c' ∈ Pic(A) ⊗ ℚ` and `a, a' ∈ ℚ`. Then
`ĥ_{ac + a'c'} = a ĥ_c + a' ĥ_{c'}`.

If `h, h'` are heights associated to `c, c'`, then `a h + a' h'` is a height associated to
`a c + a' c'` (`Faltings.IsHeightOfClass.linearCombination`). The function `a ĥ_c + a' ĥ_{c'}` is
again a symmetric quadratic form plus an additive function on `A(k)` and differs from
`a h + a' h'` by a bounded function, so it is a Néron–Tate height of `a c + a' c'`, and it equals
`ĥ_{ac + a'c'}` by uniqueness.

## Main results

* `Faltings.IsNeronTateHeight.smul_add_smul`: if `f, f'` are Néron–Tate heights of `c, c'`, then
  `a f + a' f'` is a Néron–Tate height of `a c + a' c'`.
* `Faltings.IsNeronTateHeight.epsilon_smul_add_smul`: `ĥ_{ac + a'c'} = a ĥ_c + a' ĥ_{c'}`.

## Implementation notes

As in `Faltings.neronTateBilinear`, the Néron–Tate height `ĥ_c` is
`Classical.epsilon (Faltings.IsNeronTateHeight A c)`. The coefficients are rational, as in the
source, acting on real functions through `ℚ → ℝ` and on `ℚ ⊗[ℤ] Pic(A)` through the left factor.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- Swapping the factors of `ℚ ⊗ P` carries `a • c` to `c` with its `ℚ`-factor multiplied by
`a`. -/
private lemma comm_smul {P : Type*} [AddCommGroup P] (a : ℚ) (c : ℚ ⊗[ℤ] P) :
    TensorProduct.comm ℤ ℚ P (a • c) =
      LinearMap.lTensor P (LinearMap.mulLeft ℤ a) (TensorProduct.comm ℤ ℚ P c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- `comm_smul` for a linear combination. -/
private lemma comm_smul_add_smul {P : Type*} [AddCommGroup P] (a a' : ℚ) (c c' : ℚ ⊗[ℤ] P) :
    TensorProduct.comm ℤ ℚ P (a • c + a' • c') =
      LinearMap.lTensor P (LinearMap.mulLeft ℤ a) (TensorProduct.comm ℤ ℚ P c) +
        LinearMap.lTensor P (LinearMap.mulLeft ℤ a') (TensorProduct.comm ℤ ℚ P c') := by
  rw [map_add, comm_smul, comm_smul]

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
  {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]

/-- A rational linear combination of Néron–Tate heights of `c` and `c'` is a Néron–Tate height
of the same linear combination of `c` and `c'`. -/
theorem IsNeronTateHeight.smul_add_smul {c c' : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    {f f' : {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ}
    (hf : IsNeronTateHeight A c f) (hf' : IsNeronTateHeight A c' f') (a a' : ℚ) :
    IsNeronTateHeight A (a • c + a' • c') (fun x ↦ (a : ℝ) * f x + (a' : ℝ) * f' x) := by
  let : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  let : Smooth A.hom := smooth_of_isAbelianVariety k A
  obtain ⟨⟨h, hh, C, hC⟩, b, hb, ℓ, hfx⟩ := hf
  obtain ⟨⟨h', hh', C', hC'⟩, b', hb', ℓ', hfx'⟩ := hf'
  refine ⟨⟨fun x ↦ (a : ℝ) * h x + (a' : ℝ) * h' x, ?_, |(a : ℝ)| * C + |(a' : ℝ)| * C',
    fun x ↦ ?_⟩, (a : ℝ) • b + (a' : ℝ) • b', fun x y ↦ by simp [hb x y, hb' x y],
    (a : ℝ) • ℓ + (a' : ℝ) • ℓ', fun p ↦ by simp [hfx, hfx']; ring⟩
  · have e := comm_smul_add_smul a a' c c'
    rw [e]
    exact hh.linearCombination hh' a a'
  · calc |(a : ℝ) * f x + (a' : ℝ) * f' x - ((a : ℝ) * h x + (a' : ℝ) * h' x)|
        = |(a : ℝ) * (f x - h x) + (a' : ℝ) * (f' x - h' x)| := by ring_nf
      _ ≤ |(a : ℝ)| * C + |(a' : ℝ)| * C' := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hC' x) (abs_nonneg _)

/-- **Additivity of the Néron–Tate height in the class.** For an abelian variety `A`, classes
`c, c' ∈ Pic(A) ⊗ ℚ` and `a, a' ∈ ℚ`, `ĥ_{ac + a'c'} = a ĥ_c + a' ĥ_{c'}`, where `ĥ_c` is the
Néron–Tate height of `c` (`Faltings.IsNeronTateHeight`). -/
@[faltings "lem_nt_neron_tate_additive"]
theorem IsNeronTateHeight.epsilon_smul_add_smul (c c' : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (a a' : ℚ) :
    Classical.epsilon (IsNeronTateHeight A (a • c + a' • c')) = fun x ↦
      (a : ℝ) * Classical.epsilon (IsNeronTateHeight A c) x +
        (a' : ℝ) * Classical.epsilon (IsNeronTateHeight A c') x :=
  (Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A (a • c + a' • c'))).unique
    ((Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)).smul_add_smul
      (Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c')) a a')

end Faltings

end
