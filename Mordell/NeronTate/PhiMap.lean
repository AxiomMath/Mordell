module
public import Mordell.NeronTate.Bilinear
public import Mordell.NeronTate.Existence
public import Mordell.NeronTate.Translate

/-!
# The Néron–Tate height of `φ_c(y)`

Let `A` be an abelian variety over a field `k` algebraic over `ℚ`, `c ∈ Pic(A) ⊗ ℚ` and
`y ∈ A(k)`. Write `τ_y : A → A` for translation by `y` and `φ_c(y) = τ_y^* c - c`. Then the
Néron–Tate height of `φ_c(y)` is `x ↦ B_c(x, y)`, where `B_c` is the bilinear form of the
Néron–Tate height of `c`.

## Main results

* `Faltings.neronTateBilinear_isNeronTateHeight_phi`: the function `x ↦ B_c(x, y)` is a
  Néron–Tate height of `τ_y^* c - c`.

## Implementation notes

The setting is that of `Faltings.neronTateBilinear`: `A` is a group object of `Over (Spec k)`
which is an abelian variety, its `k`-points are the morphisms `Over.mk (𝟙 (Spec k)) ⟶ A`, a
group written multiplicatively, and the source's `A(k̄)` is the case `k = k̄`. Translation by
`y` is the morphism `𝟙 A * (Over.homMk A.hom ≫ y) : A ⟶ A` of the group `A ⟶ A`, and the
pull-back on `ℚ ⊗ Pic(A)` is the base change to `ℚ` of `Stacks.Picard.schemePullbackClassHom`.

The Néron–Tate height of a class is characterised by `Faltings.IsNeronTateHeight` (it exists
and is unique), so the identity `ĥ_{φ_c(y)}(x) = B_c(x, y)` is stated as: `x ↦ B_c(x, y)`
satisfies `Faltings.IsNeronTateHeight` for `τ_y^* c - c`. The class `c` is allowed in
`ℚ ⊗ Pic(A)`; the source's `c ∈ Pic(A)` is the case `1 ⊗ c`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- The polar form of `x ↦ ½ b(x, x) + ℓ(x)`, for `b` symmetric biadditive and `ℓ` additive,
is `b`. -/
private lemma polar_half_add_linear {M : Type*} [AddCommGroup M] (b : M →+ M →+ ℝ)
    (hb : ∀ x y, b x y = b y x) (ℓ : M →+ ℝ) (x y : M) :
    (b (x + y) (x + y) / 2 + ℓ (x + y)) - (b x x / 2 + ℓ x) - (b y y / 2 + ℓ y) = b x y := by
  simp only [map_add, AddMonoidHom.add_apply, hb y x]
  ring

/-- If `h` is a height of `c` and `g` an endomorphism of `X` over `k`, then `x ↦ h(g x) - h(x)`
is a height of `g^* c - c`. -/
private lemma isHeightOfClass_comp_sub {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] (g : X ⟶ X) (hg : g ≫ f = f)
    {c : X.picardGroup ⊗[ℤ] ℚ} {h : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} → ℝ}
    (hh : IsHeightOfClass f c h) :
    IsHeightOfClass f
      (LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom g).toIntLinearMap c - c)
      (fun p ↦ h ⟨p.1 ≫ g, by rw [Category.assoc, hg, p.2]⟩ - h p) := by
  have hneg : LinearMap.mulLeft ℤ (-1 : ℚ) = -LinearMap.id := by ext; simp
  have := (hh.comp g hg).linearCombination hh 1 (-1)
  rw [LinearMap.mulLeft_one, hneg, LinearMap.lTensor_neg, LinearMap.lTensor_id,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.id_apply, ← sub_eq_add_neg] at this
  simpa only [Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul, ← sub_eq_add_neg] using this

/-- For an abelian variety `A` over `k`, `c ∈ Pic(A) ⊗ ℚ` and `y ∈ A(k)`, the function
`x ↦ B_c(x, y)` (`Faltings.neronTateBilinear`) is the Néron–Tate height of `φ_c(y) = τ_y^* c - c`,
where `τ_y` is translation by `y`. -/
@[faltings "lem_nt_neron_tate_phi"]
theorem neronTateBilinear_isNeronTateHeight_phi {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) (y : Over.mk (𝟙 (Spec (.of k))) ⟶ A) :
    IsNeronTateHeight A
      ((Stacks.Picard.schemePullbackClassHom
          (𝟙 A * (Over.homMk A.hom ≫ y : A ⟶ A)).left).toIntLinearMap.baseChange ℚ c - c)
      (fun p => neronTateBilinear A c (.ofMul (Over.homMk p.1 p.2)) (.ofMul y)) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  let : Smooth A.hom := smooth_of_isAbelianVariety k A
  set τ : A ⟶ A := 𝟙 A * (Over.homMk A.hom ≫ y)
  set f := Classical.epsilon (IsNeronTateHeight A c)
  obtain ⟨⟨h, hh, C, hC⟩, b, hb, ℓ, hfx⟩ : IsNeronTateHeight A c f :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)
  let pt (P : Over.mk (𝟙 (Spec (.of k))) ⟶ A) :
      {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} := ⟨P.left, by simp [Over.w P]⟩
  have hpt (Q : Over.mk (𝟙 (Spec (.of k))) ⟶ A) : Over.homMk (pt Q).1 (pt Q).2 = Q := by ext; rfl
  -- `B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)`, with `x + y` the translate `τ_y x`
  have hB (p : {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _}) :
      neronTateBilinear A c (.ofMul (Over.homMk p.1 p.2)) (.ofMul y) =
        f ⟨p.1 ≫ τ.left, by rw [Category.assoc, Over.w τ, p.2]⟩ - f p - f (pt y) := by
    rw [neronTateBilinear_apply]
    refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg f (Subtype.ext ?_)) rfl) rfl
    exact (congrArg Over.Hom.left (comp_translate (C := Over (Spec (.of k))) _ y)).symm
  -- `B_c(x, y) = b(x, y)`
  have hBb (P : Over.mk (𝟙 (Spec (.of k))) ⟶ A) :
      neronTateBilinear A c (.ofMul P) (.ofMul y) = b (.ofMul P) (.ofMul y) := by
    rw [neronTateBilinear_apply, ← polar_half_add_linear b hb ℓ, ← ofMul_mul]
    simp only [Function.comp_apply]
    rw [← hpt (P * y), ← hpt P, ← hpt y, ← hfx, ← hfx, ← hfx]
    rfl
  refine ⟨⟨fun p ↦ h ⟨p.1 ≫ τ.left, by rw [Category.assoc, Over.w τ, p.2]⟩ - h p, ?_,
    2 * C + |f (pt y)|, fun p ↦ ?_⟩, 0, fun _ _ ↦ rfl, b.flip (.ofMul y), fun p ↦ by simp [hBb]⟩
  · rw [map_sub, comm_baseChange, schemePullbackClassHom_eq_pullbackPicardHom]
    exact isHeightOfClass_comp_sub τ.left (Over.w τ) hh
  -- `|B_c(x, y) - (h(x + y) - h(x))| ≤ 2C + |ĥ_c(y)|`
  have e1 := abs_le.1 (hC ⟨p.1 ≫ τ.left, by rw [Category.assoc, Over.w τ, p.2]⟩)
  have e2 := abs_le.1 (hC p)
  dsimp only
  rw [hB, abs_le]
  constructor <;> cases abs_cases (f (pt y)) <;> linarith [e1.1, e1.2, e2.1, e2.2]

end Faltings

end
