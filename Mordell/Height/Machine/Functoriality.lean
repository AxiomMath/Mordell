module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
public import Mordell.Height.Machine.ClassZero

/-!
# Functoriality of the Weil height

Let `g : X ⟶ Y` be a morphism of smooth projective varieties over a field `k` algebraic over
`ℚ` (in the source, `k = ℚ̄`), compatible with the structure morphisms `fX` and `fY`. If
`γ ∈ Emb(Y)` and `γ' ∈ Emb(X)` satisfy `cl(γ') = g^* cl(γ)` in `Pic(X)`, then the difference
`h_{γ'} - h_γ ∘ g` is a bounded function on the `k`-points of `X`.

## Main results

* `Faltings.EmbeddingGroup.exists_abs_height_sub_height_comp_le`: the functoriality of the
  Weil height machine.

## Implementation notes

A `k`-point of `X` is a section `p` of `fX`, and its image under `g` is the section `p ≫ g`
of `fY`. The pullback `g^* : Pic(Y) → Pic(X)` is `Stacks.SheafOfModules.pullbackPicardHom g`.
Boundedness is stated as the existence of a uniform bound on the absolute value.

The proof follows the source. Fix a projective embedding `ι` of `X`. For a projective embedding
`φ` of `Y`, the Segre product `(φ ∘ g) ⊗ ι` is a projective embedding of `X` with height
`h_φ ∘ g + h_ι` and class `g^* cl(φ) + cl(ι)`. The additive map `φ ↦ (φ ∘ g) ⊗ ι - ι` from
`Emb(Y)` to `Emb(X)` therefore sends `γ` to an element `γ''` with `h_{γ''} = h_γ ∘ g` and
`cl(γ'') = g^* cl(γ) = cl(γ')`, and Weil's theorem for classes of zero
(`Faltings.EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero`), applied to
`γ' - γ''`, bounds `h_{γ'} - h_γ ∘ g`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

section Functoriality

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
  [IsProjectiveVariety k fX] [Smooth fX] [IsProjectiveVariety k fY] [Smooth fY]

/-- `g^*` of the class `[φ^* L]` is the class `[(φ ∘ g)^* L]`. -/
private theorem pullbackPicardHom_pullbackPicardClass {Z : Scheme.{u}} (g : X ⟶ Y) (φ : Y ⟶ Z)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatIsSheaf L) :
    Stacks.SheafOfModules.pullbackPicardHom g (Stacks.SheafOfModules.pullbackPicardClass φ L hL) =
      Stacks.SheafOfModules.pullbackPicardClass (g ≫ φ) L hL :=
  have := hL
  (Stacks.SheafOfModules.pullbackPicardHom_picardClass g _
    (Stacks.RingedSpace.modulePullback_isInvertible _ L)).trans
    (Stacks.SheafOfModules.pullbackPicardClass_comp g φ L hL _).symm

/-- **The Segre product `(φ ∘ g) ⊗ ι`.** For a `k`-morphism `g : X ⟶ Y`, a projective embedding
`ι` of `X` and a projective embedding `φ` of `Y`, there is a projective embedding `Φ` of `X` with
`h_Φ = h_φ ∘ g + h_ι` and `cl(Φ) = g^* cl(φ) + cl(ι)`. -/
private theorem exists_height_eq_embeddingClass_eq_segreProduct_comp (g : X ⟶ Y)
    (hg : g ≫ fY = fX) {m : ℕ} (ι : ProjectiveEmbedding fX m) {n : ℕ}
    (φ : ProjectiveEmbedding fY n) :
    ∃ Φ : ProjectiveEmbedding fX (n * m + n + m),
      (∀ p, Φ.height p = φ.height ⟨p.1 ≫ g, by rw [Category.assoc, hg, p.2]⟩ + ι.height p) ∧
      embeddingClass fX (FreeAbelianGroup.of ⟨_, Φ⟩) =
        Stacks.SheafOfModules.pullbackPicardHom g
            (embeddingClass fY (FreeAbelianGroup.of ⟨_, φ⟩)) +
          embeddingClass fX (FreeAbelianGroup.of ⟨_, ι⟩) := by
  have h : (g ≫ φ.hom) ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) =
      ι.hom ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k) := by
    rw [Category.assoc, φ.hom_over, hg, ι.hom_over]
  obtain ⟨Φ, hΦ⟩ := ProjectiveEmbedding.exists_hom_eq_segreProduct (g ≫ φ.hom) ι h
  refine ⟨Φ, fun p => ?_, ?_⟩
  · simp only [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization]
    have hy : (p.1 ≫ segreProduct (g ≫ φ.hom) ι.hom h) ≫
        projectiveSpaceOver (n * m + n + m) (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ := by
      rw [← hΦ, Category.assoc, Φ.hom_over, p.2]
    have hy₁ : (p.1 ≫ g ≫ φ.hom) ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) =
        𝟙 _ := by
      rw [Category.assoc, Category.assoc, φ.hom_over, hg, p.2]
    rw [kPointProjectivization_congr (congrArg (p.1 ≫ ·) hΦ) _ hy,
      kPointProjectivization_congr (Category.assoc p.1 g φ.hom) _ hy₁]
    obtain ⟨P, Q, hP, hQ, hPQ, h1, h2, h3⟩ := exists_kPointProjectivization_segreProduct
      (g ≫ φ.hom) ι.hom h p.1 hy hy₁ (by rw [Category.assoc, ι.hom_over, p.2])
    rw [h1, h2, h3]
    exact weilHeight_mk_mul_comp_equiv _ P Q hP hQ hPQ
  · rw [embeddingClass_apply_of, embeddingClass_apply_of, embeddingClass_apply_of]
    erw [pullbackPicardHom_pullbackPicardClass]
    obtain ⟨α⟩ := nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso
      (g ≫ φ.hom) ι.hom h
    rw [← hΦ] at α
    have h1 := Stacks.RingedSpace.modulePullback_isInvertible (g ≫ φ.hom).toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1)
    have h2 := Stacks.RingedSpace.modulePullback_isInvertible ι.hom.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver m (Spec (.of k)) 1)
    exact ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ h1 h2)).mpr ⟨α⟩).trans
      (Stacks.SheafOfModules.picardClass_schemeTensor X _ _ h1 h2)

/-- **The transfer `Emb(Y) → Emb(X)` along `g`.** Fixing a projective embedding `ι` of `X`, the
additive map `φ ↦ (φ ∘ g) ⊗ ι - ι` sends every `δ ∈ Emb(Y)` to an element of `Emb(X)` with
height `h_δ ∘ g` and class `g^* cl(δ)`. -/
private theorem exists_addMonoidHom_height_eq_embeddingClass_eq (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    ∃ T : EmbeddingGroup fY →+ EmbeddingGroup fX,
      (∀ δ x, EmbeddingGroup.height fX (T δ) x =
        EmbeddingGroup.height fY δ ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩) ∧
      ∀ δ, embeddingClass fX (T δ) =
        Stacks.SheafOfModules.pullbackPicardHom g (embeddingClass fY δ) := by
  obtain ⟨m, i, hi, hio⟩ := (inferInstance : IsProjectiveVariety k fX).isProjective
  let ι : ProjectiveEmbedding fX m := ⟨i, hi, hio⟩
  choose Φ hΦh hΦc using fun e : Σ n, ProjectiveEmbedding fY n =>
    exists_height_eq_embeddingClass_eq_segreProduct_comp g hg ι e.2
  let T : EmbeddingGroup fY →+ EmbeddingGroup fX :=
    FreeAbelianGroup.lift fun e => FreeAbelianGroup.of ⟨_, Φ e⟩ - FreeAbelianGroup.of ⟨_, ι⟩
  refine ⟨T, fun δ x => ?_, fun δ => ?_⟩
  · let ev : ({p : Spec (.of k) ⟶ X // p ≫ fX = 𝟙 _} → ℝ) →+ ℝ := Pi.evalAddMonoidHom _ x
    let ev' : ({p : Spec (.of k) ⟶ Y // p ≫ fY = 𝟙 _} → ℝ) →+ ℝ :=
      Pi.evalAddMonoidHom _ ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩
    refine DFunLike.congr_fun (FreeAbelianGroup.lift_ext
      (ev.comp ((EmbeddingGroup.height fX).comp T))
      (ev'.comp (EmbeddingGroup.height fY)) fun e => ?_) δ
    simp [ev, ev', T, EmbeddingGroup.height, hΦh]
  · refine DFunLike.congr_fun (FreeAbelianGroup.lift_ext ((embeddingClass fX).comp T)
      ((Stacks.SheafOfModules.pullbackPicardHom g).comp (embeddingClass fY))
      fun e => ?_) δ
    simp only [AddMonoidHom.comp_apply, T, FreeAbelianGroup.lift_apply_of]
    rw [map_sub, hΦc]
    exact add_sub_cancel_right _ _

end Functoriality

/-- **Functoriality of the Weil height.** Let `g : X ⟶ Y` be a `k`-morphism of smooth
projective varieties, `γ ∈ Emb(Y)` and `γ' ∈ Emb(X)` with
`embeddingClass fX γ' = pullbackPicardHom g (embeddingClass fY γ)`. Then
`h_{γ'} - h_γ ∘ g` is bounded on the `k`-points of `X`. -/
@[faltings "thm_ht_weil_functoriality"]
public theorem EmbeddingGroup.exists_abs_height_sub_height_comp_le {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    [IsProjectiveVariety k fX] [Smooth fX] [IsProjectiveVariety k fY] [Smooth fY]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (γ : EmbeddingGroup fY) (γ' : EmbeddingGroup fX)
    (hcl : embeddingClass fX γ' =
      Stacks.SheafOfModules.pullbackPicardHom g (embeddingClass fY γ)) :
    ∃ C : ℝ, ∀ x : {p : Spec (.of k) ⟶ X // p ≫ fX = 𝟙 _},
      |EmbeddingGroup.height fX γ' x -
        EmbeddingGroup.height fY γ ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩| ≤ C := by
  obtain ⟨T, hTh, hTc⟩ := exists_addMonoidHom_height_eq_embeddingClass_eq g hg
  obtain ⟨C, hC⟩ := EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero
    (γ := γ' - T γ) (by rw [map_sub, hTc, hcl, sub_self])
  exact ⟨C, fun x => by simpa only [map_sub, Pi.sub_apply, hTh] using hC x⟩

end Faltings
