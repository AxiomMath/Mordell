module

public import Mordell.NeronTate.Basic
public import Mordell.Height.Class.Uniqueness
public import Mordell.Algebra.Quadratic.Bounded

/-!
# Uniqueness of the Néron–Tate height

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ Pic(A) ⊗ ℚ`. Any two Néron–Tate heights `f, f'` of `c`
are equal: if `f - h` and `f' - h'` are bounded for heights `h, h'` associated to `c`, then
`h - h'` is bounded, so `f - f' = ½ (b - b')(x, x) + (ℓ - ℓ')(x)` is a bounded function of the
form quadratic plus linear on the group `A(k)`, hence zero.

## Main results

* `Faltings.eq_of_abs_sub_le_of_eq_half_add`: on an abelian group, two functions of the form
  `½ b(x, x) + ℓ(x)` whose difference is bounded are equal.
* `Faltings.IsNeronTateHeight.unique`: two Néron–Tate heights of the same class are equal.

## Implementation notes

The Néron–Tate heights are functions on the sections `p : Spec k ⟶ A` of the structure morphism,
while the forms `b, ℓ` live on the group `A(k)`, the morphisms `Over.mk (𝟙 (Spec k)) ⟶ A` written
additively through `Additive`; this group is commutative because `A` is proper and geometrically
integral (`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- On an abelian group, two functions `f = ½ b(x, x) + ℓ(x)` and `f' = ½ b'(x, x) + ℓ'(x)`, with
`b, b'` symmetric biadditive and `ℓ, ℓ'` additive, whose difference is bounded are equal. -/
theorem eq_of_abs_sub_le_of_eq_half_add {M : Type*} [AddCommGroup M] {f f' : M → ℝ}
    (b b' : M →+ M →+ ℝ) (hb : ∀ x y, b x y = b y x) (hb' : ∀ x y, b' x y = b' y x)
    (ℓ ℓ' : M →+ ℝ) (hf : ∀ x, f x = b x x / 2 + ℓ x) (hf' : ∀ x, f' x = b' x x / 2 + ℓ' x)
    {C : ℝ} (hC : ∀ x, |f x - f' x| ≤ C) : f = f' := by
  have hdiff (x : M) : f x - f' x = (b - b') x x / 2 + (ℓ - ℓ') x := by
    simp only [hf, hf', AddMonoidHom.sub_apply]; ring
  have hbs : ∀ x y, (b - b') x y = (b - b') y x := fun x y => by simp [hb x y, hb' x y]
  have hℓ := addMonoidHom_eq_zero_of_bounded_quadratic_add (b - b') hbs _ (fun _ => rfl)
    (ℓ - ℓ') ⟨C, fun x => hdiff x ▸ hC x⟩
  have hq := eq_zero_of_isBounded_range_add (b - b') hbs _ (fun _ => rfl) (ℓ - ℓ') <|
    isBounded_iff_forall_norm_le.2 ⟨C, by
      rintro _ ⟨y, rfl⟩
      rw [Real.norm_eq_abs, Pi.add_apply, ← hdiff]
      exact hC y⟩
  funext x
  rw [← sub_eq_zero, hdiff, hℓ]
  simpa using congrFun hq x

/-- **Uniqueness of the Néron–Tate height.** Two Néron–Tate heights of the same class
`c ∈ Pic(A) ⊗ ℚ` on an abelian variety `A` are equal. -/
@[faltings "lem_nt_neron_tate_height_unique"]
theorem IsNeronTateHeight.unique {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    {f f' : {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ}
    (hf : IsNeronTateHeight A c f) (hf' : IsNeronTateHeight A c f') : f = f' := by
  let : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  let : Smooth A.hom := smooth_of_isAbelianVariety k A
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨⟨h, hh, C₁, hC₁⟩, b, hb, ℓ, hfx⟩ := hf
  obtain ⟨⟨h', hh', C₂, hC₂⟩, b', hb', ℓ', hfx'⟩ := hf'
  obtain ⟨C₃, hC₃⟩ := hh.exists_abs_sub_le hh'
  let pt : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →
      {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} := fun z => ⟨z.toMul.left, Over.w z.toMul⟩
  have hpt : ∀ z, (Additive.ofMul (Over.homMk (pt z).1 (pt z).2 :
      Over.mk (𝟙 (Spec (.of k))) ⟶ A)) = z := fun _ =>
    Additive.toMul.injective (Over.OverMorphism.ext rfl)
  have key := eq_of_abs_sub_le_of_eq_half_add (f := f ∘ pt) (f' := f' ∘ pt) b b' hb hb' ℓ ℓ'
    (fun z => by simp only [Function.comp_apply, hfx, hpt])
    (fun z => by simp only [Function.comp_apply, hfx', hpt]) (C := C₁ + (C₃ + C₂))
    (fun z => (abs_sub_le _ (h (pt z)) _).trans <| add_le_add (hC₁ _) <|
      (abs_sub_le _ (h' (pt z)) _).trans <| add_le_add (hC₃ _) <|
        abs_sub_comm (f' (pt z)) _ ▸ hC₂ _)
  funext p
  exact congrFun key (.ofMul (Over.homMk p.1 p.2))

end Faltings

end
