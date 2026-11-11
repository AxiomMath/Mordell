module

public import Mordell.NeronTate.Uniqueness
public import Mordell.NeronTate.Existence
public import Mordell.Height.Class.Functoriality

/-!
# Functoriality of Néron–Tate heights

Let `A`, `A'` be abelian varieties over a field `k` algebraic over `ℚ` (in the source, an
algebraic closure `k̄` of a number field), `φ : A' → A` a homomorphism and
`c ∈ Pic(A) ⊗ ℚ`. Then `ĥ_{φ^* c} = ĥ_c ∘ φ`.

If `f = ½ b(x, x) + ℓ(x)` is a Néron–Tate height of `c` with `f - h` bounded for a height `h`
associated to `c`, then `f ∘ φ = ½ b(φ x, φ x) + ℓ(φ x)` is again quadratic plus linear, since
`φ` is additive on points, and `f ∘ φ - h ∘ φ` is bounded, where `h ∘ φ` is a height associated
to `φ^* c` (`Faltings.IsHeightOfClass.comp`). So `f ∘ φ` is a Néron–Tate height of `φ^* c`, and it
equals `ĥ_{φ^* c}` by uniqueness.

## Main results

* `Faltings.IsNeronTateHeight.comp`: if `f` is a Néron–Tate height of `c`, then `f ∘ φ` is a
  Néron–Tate height of `φ^* c`.
* `Faltings.IsNeronTateHeight.epsilon_pullback`: `ĥ_{φ^* c} = ĥ_c ∘ φ`.

## Implementation notes

A homomorphism `φ : A' → A` is a morphism of group objects over `Spec k`, i.e. a morphism
`φ : A' ⟶ A` over `Spec k` with `[IsMonHom φ]`; on `k`-points it is `p ↦ p ≫ φ.left`, and on the
groups `A'(k) → A(k)` it is the additive map `IsMonHom.monoidHom φ`. The pull-back
`φ^* : Pic(A) ⊗ ℚ → Pic(A') ⊗ ℚ` is the base change to `ℚ` of
`Stacks.Picard.schemePullbackClassHom φ.left`, as in `Faltings.IsEvenClass`. As in
`Faltings.neronTateBilinear`, `ĥ_c` is `Classical.epsilon (Faltings.IsNeronTateHeight A c)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
  {A A' : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
  [GrpObj A'] [IsAbelianVariety k A']

/-- Pulling back along a homomorphism `φ : A' → A` preserves Néron–Tate heights: if `f` is a
Néron–Tate height of `c`, then `f ∘ φ` is a Néron–Tate height of `φ^* c`. -/
theorem IsNeronTateHeight.comp (φ : A' ⟶ A) [IsMonHom φ]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    {f : {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ} (hf : IsNeronTateHeight A c f) :
    IsNeronTateHeight A'
      ((Stacks.Picard.schemePullbackClassHom φ.left).toIntLinearMap.baseChange ℚ c)
      (fun x ↦ f ⟨x.1 ≫ φ.left, by rw [Category.assoc, Over.w φ, x.2]⟩) := by
  let : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  let : Smooth A.hom := smooth_of_isAbelianVariety k A
  let : IsProjectiveVariety k A'.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A'.hom)
      (isProjective_of_isAbelianVariety k A')⟩
  let : Smooth A'.hom := smooth_of_isAbelianVariety k A'
  obtain ⟨⟨h, hh, C, hC⟩, b, hb, ℓ, hfx⟩ := hf
  let ψ := (IsMonHom.monoidHom φ (Over.mk (𝟙 (Spec (.of k))))).toAdditive
  refine ⟨⟨fun x ↦ h ⟨x.1 ≫ φ.left, by rw [Category.assoc, Over.w φ, x.2]⟩, ?_, C,
    fun x ↦ hC _⟩, (b.compl₂ ψ).comp ψ, fun x y ↦ by simpa using hb (ψ x) (ψ y), ℓ.comp ψ,
    fun p ↦ ?_⟩
  · rw [schemePullbackClassHom_eq_pullbackPicardHom, comm_baseChange]
    exact hh.comp φ.left (Over.w φ)
  · exact (hfx _).trans rfl

/-- **Functoriality of Néron–Tate heights.** For a homomorphism `φ : A' → A` of abelian varieties
and `c ∈ Pic(A) ⊗ ℚ`, `ĥ_{φ^* c} = ĥ_c ∘ φ`, where `ĥ_c` is the Néron–Tate height of `c`
(`Faltings.IsNeronTateHeight`). -/
@[faltings "lem_nt_neron_tate_functorial"]
theorem IsNeronTateHeight.epsilon_pullback (φ : A' ⟶ A) [IsMonHom φ]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) :
    Classical.epsilon (IsNeronTateHeight A'
      ((Stacks.Picard.schemePullbackClassHom φ.left).toIntLinearMap.baseChange ℚ c)) =
      fun x ↦ Classical.epsilon (IsNeronTateHeight A c)
        ⟨x.1 ≫ φ.left, by rw [Category.assoc, Over.w φ, x.2]⟩ :=
  (Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A' _)).unique
    ((Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)).comp φ)

end Faltings

end


/-!
# The Néron–Tate height of the inverse class

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field), `c ∈ Pic(A) ⊗ ℚ` and `c⁻ = [-1]^* c`. Then
`ĥ_{c⁻}(x) = ĥ_c(-x)` for `x ∈ A(k)`.

`A` is commutative, so the inversion `[-1]` is a homomorphism, and this is the functoriality
`ĥ_{φ^* c} = ĥ_c ∘ φ` (`Faltings.IsNeronTateHeight.epsilon_pullback`) for `φ = [-1]`.

## Main results

* `Faltings.IsNeronTateHeight.epsilon_inv_apply`: `ĥ_{c⁻}(x) = ĥ_c(-x)`.

## Implementation notes

As in `Faltings.IsEvenClass`, `c⁻` is the base change to `ℚ` of the pull-back
`Stacks.Picard.schemePullbackClassHom` along the inversion `(GrpObj.inv (X := A)).left`. As in
`Faltings.neronTateLinear`, `ĥ_c` is `Classical.epsilon (Faltings.IsNeronTateHeight A c)`, a
function on sections, and a point `z` of the group `A(k)` (written additively through
`Additive`) is read as the section `z.left`. That `[-1]` is a homomorphism uses the
commutativity of `A` (`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2 and Sec. 5.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- **The Néron–Tate height of the inverse class.** For an abelian variety `A`,
`c ∈ Pic(A) ⊗ ℚ` and `x ∈ A(k)`, `ĥ_{c⁻}(x) = ĥ_c(-x)`, where `c⁻ = [-1]^* c` and `ĥ_c` is the
Néron–Tate height of `c` (`Faltings.IsNeronTateHeight`). -/
@[faltings "lem_nt_neron_tate_inverse_class"]
theorem IsNeronTateHeight.epsilon_inv_apply {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) :
    Classical.epsilon (IsNeronTateHeight A
        ((Stacks.Picard.schemePullbackClassHom (GrpObj.inv (X := A)).left).toIntLinearMap.baseChange
          ℚ c))
        ⟨x.toMul.left, Over.w x.toMul⟩ =
      Classical.epsilon (IsNeronTateHeight A c) ⟨(-x).toMul.left, Over.w (-x).toMul⟩ := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  exact congrFun (IsNeronTateHeight.epsilon_pullback (GrpObj.inv (X := A)) c) _

end Faltings

end
