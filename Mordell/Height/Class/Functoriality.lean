module

public import Mordell.Analysis.AbsSubBound
public import Mordell.Height.Class.Basic
public import Mordell.Height.Machine.EmbeddingClassSurjective
public import Mordell.Height.Machine.Functoriality

/-!
# Functoriality of heights associated to divisor classes

Let `g : X ⟶ Y` be a morphism of smooth projective varieties over a field `k` algebraic over
`ℚ` (in the source, `k = ℚ̄`), compatible with the structure morphisms `fX` and `fY`, and let
`c ∈ Pic(Y) ⊗ ℚ`. If `h` is a height associated to `c`, then `h ∘ g` is a height associated to
`g^* c ∈ Pic(X) ⊗ ℚ`; that is, `h_{g^* c} = h_c ∘ g + O(1)`.

## Main results

* `Faltings.IsHeightOfClass.comp`: functoriality of heights associated to divisor classes.

## Implementation notes

A `k`-point of `X` is a section `p` of `fX`, and its image under `g` is the section `p ≫ g` of
`fY`. The pullback `g^* : Pic(Y) ⊗ ℚ → Pic(X) ⊗ ℚ` is the base change
`LinearMap.rTensor ℚ` of the pullback homomorphism `Stacks.SheafOfModules.pullbackPicardHom g`
on Picard groups.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Hindry, Silverman, *Diophantine Geometry*, B.3][hindrysilverman2000]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Faltings

/-- **Functoriality of heights of divisor classes.** If `g : X ⟶ Y` is a `k`-morphism of smooth
projective varieties and `h` is a height associated to `c ∈ Pic(Y) ⊗ ℚ`, then `h ∘ g` is a
height associated to `g^* c ∈ Pic(X) ⊗ ℚ`. -/
@[faltings "thm_ht_divisor_class_heights"]
public theorem IsHeightOfClass.comp {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    [IsProjectiveVariety k fX] [Smooth fX] [IsProjectiveVariety k fY] [Smooth fY]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) {c : Y.picardGroup ⊗[ℤ] ℚ}
    {h : {p : Spec (.of k) ⟶ Y // p ≫ fY = 𝟙 _} → ℝ} (hh : IsHeightOfClass fY c h) :
    IsHeightOfClass fX
      (LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom g).toIntLinearMap c)
      (fun x => h ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩) := by
  obtain ⟨m, γ, hm, hγ, C, hC⟩ := hh
  obtain ⟨γ', hcl⟩ := embeddingClass_surjective fX
    (Stacks.SheafOfModules.pullbackPicardHom g (embeddingClass fY γ))
  obtain ⟨C', hC'⟩ := EmbeddingGroup.exists_abs_height_sub_height_comp_le g hg γ γ' hcl
  refine ⟨m, γ', hm, ?_, C + (m : ℝ)⁻¹ * C', fun x =>
    abs_sub_mul_le_add_mul (by positivity) (hC _) (hC' x)⟩
  rw [hcl, ← map_nsmul, ← hγ]
  rfl

end Faltings
