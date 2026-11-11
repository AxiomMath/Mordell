module

public import Mordell.AlgebraicGeometry.Ample
public import Mordell.Height.Class.Uniqueness
public import Mordell.Height.Weil.Nonneg
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower

/-!
# Heights associated to ample classes are bounded below

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ`, and let
`c ∈ Pic(X) ⊗ ℚ` be an ample class. Every height `h` associated to `c` is bounded below on the
`k`-points of `X`.

Write `e • c = [L] ⊗ 1` with `L^{⊗ e'} ≅ φ^* 𝒪(1)` for a projective embedding `φ`. Then
`cl(φ) ⊗ 1 = (e e') • c`, so `(e e')⁻¹ h_φ` is a height associated to `c`, and it is nonnegative
since the Weil height is. Any height of `c` differs from it by a bounded function.

## Main results

* `Faltings.IsHeightOfClass.exists_le_of_isAmpleClass`: if `c` is ample and `h` is a height
  associated to `c`, then there is a real `C` with `C ≤ h x` for every `k`-point `x`.

## Implementation notes

Boundedness below is stated as the existence of a uniform lower bound `C`. The base field is an
algebraic extension `k / ℚ`; the source's case is `k = ℚ̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Hindry, Silverman, *Diophantine Geometry*, B.3][hindrysilverman2000]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The class of the tensor power `L^{⊗ d}` is `d • [L]`. -/
private lemma picardClass_tensorPowModule (L : X.Modules)
    [hL : Stacks.Ample.IsInvertibleModule X L] (d : ℤ) :
    X.picardClass (Stacks.Ample.tensorPowModule X L d) inferInstance =
      d • X.picardClass L hL := by
  refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_schemeTensorPower X L hL d)
  exact (X.picardClass_eq_iff _ _ _ _).2
    ⟨(Stacks.PowerFamilyBridge.tensorPowerModuleIso X L d).symm⟩

/-- An ample class `c` has a nonnegative height: if `e • c = [L] ⊗ 1` and `L^{⊗ e'} ≅ φ^* 𝒪(1)`,
then `cl(φ) ⊗ 1 = (e e') • c`, so `(e e')⁻¹ h_φ` is a height of `c`, and `h_φ ≥ 0`. -/
private lemma exists_isHeightOfClass_nonneg_of_isAmpleClass [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f]
    {c : X.picardGroup ⊗[ℤ] ℚ} (hc : IsAmpleClass f c) :
    ∃ g, IsHeightOfClass f c g ∧ ∀ x, 0 ≤ g x := by
  obtain ⟨e, L, hL, he, ⟨e', he', n, φ, ⟨ι⟩⟩, hec⟩ := hc
  have hcl : embeddingClass f (FreeAbelianGroup.of ⟨n, φ⟩) = e' • X.picardClass L hL := by
    rw [embeddingClass_apply_of, ← picardClass_tensorPowModule]
    exact (X.picardClass_eq_iff _ _ _ _).2 ⟨ι.symm⟩
  have hm : (((e * e').toNat : ℕ) : ℤ) = e * e' := Int.toNat_of_nonneg (by positivity)
  refine ⟨fun x => (((e * e').toNat : ℕ) : ℝ)⁻¹ *
      EmbeddingGroup.height f (FreeAbelianGroup.of ⟨n, φ⟩) x,
    ⟨(e * e').toNat, FreeAbelianGroup.of ⟨n, φ⟩, Int.lt_toNat.2 (by positivity), ?_, 0,
      fun x => by simp⟩, fun x => ?_⟩
  · rw [hcl, ← natCast_zsmul, hm, mul_comm, mul_smul, hec, TensorProduct.smul_tmul']
  · simp only [EmbeddingGroup.height, FreeAbelianGroup.lift_apply_of]
    exact mul_nonneg (by positivity) (weilHeight_nonneg _)

end

/-- A height associated to an ample class `c ∈ Pic(X) ⊗ ℚ` is bounded below on the `k`-points
of `X`: it differs by a bounded function from a nonnegative height of `c`. -/
@[faltings "lem_ht_height_class_ample_bounded_below"]
theorem IsHeightOfClass.exists_le_of_isAmpleClass {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {c : X.picardGroup ⊗[ℤ] ℚ} {h : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ}
    (hh : IsHeightOfClass f c h) (hc : IsAmpleClass f c) :
    ∃ C : ℝ, ∀ x, C ≤ h x := by
  obtain ⟨g, hg, hg0⟩ := exists_isHeightOfClass_nonneg_of_isAmpleClass hc
  obtain ⟨C, hC⟩ := hh.exists_abs_sub_le hg
  exact ⟨-C, fun x => by linarith [(abs_le.1 (hC x)).1, hg0 x]⟩

end Faltings
