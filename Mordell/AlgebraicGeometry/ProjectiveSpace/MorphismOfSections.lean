module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# Morphisms to projective space defined by sections

Let `X` be a projective variety over a field `k`, `L` a line bundle on `X` and
`t₀, …, tᵣ ∈ H⁰(X, L)` global sections without common zero. Then there is a morphism of
`k`-schemes `t = (t₀ : ⋯ : tᵣ) : X ⟶ ℙʳ_k` together with an isomorphism `t^* 𝒪(1) ≅ L` carrying
the pulled-back homogeneous coordinate `t^* xⱼ` to `tⱼ` for every `j`. On a `k`-rational point
`p` this says that `t(p) = (t₀(p) : ⋯ : tᵣ(p))`.

## Main results

* `Faltings.exists_hom_and_iso_pullback_projectiveSpaceTwistingSheaf`: the morphism defined by a
  family of global sections of a line bundle without common zero, with the isomorphism
  `t^* 𝒪(1) ≅ L` matching `t^* xⱼ` with `tⱼ`.

## Implementation notes

A line bundle is an `L : X.Modules` with `Stacks.Ample.IsInvertibleModule X L`; a global section
is an element of `Γ(L, ⊤)`, and `tⱼ` does not vanish at `x` when `x` lies in
`Stacks.Ample.nonvanishingLocus L tⱼ` (the germ is not in `𝔪ₓ Lₓ`). Projective space `ℙʳ_k` is
`AlgebraicGeometry.projectiveSpaceOver r (Spec k)`, its hyperplane sheaf `𝒪(1)` is
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec k)`, and the coordinate
`xⱼ ∈ Γ(ℙʳ_k, 𝒪(1))` is the pullback, along the projection
`projectiveSpaceOver.toIntegralAtUniverse` to `ℙʳ_ℤ`, of the degree-one section
`Stacks.TwistPullbackPinned.coordGlobalSection r j` defined by the variable `Tⱼ`. Sections are
pulled back by `AlgebraicGeometry.pullbackGlobalSections`.

The pointwise description `t(p) = (t₀(p) : ⋯ : tᵣ(p))` is not a separate clause: the isomorphism
`α : t^* 𝒪(1) ≅ L` with `α (t^* xⱼ) = tⱼ` identifies, at every point `x`, the vanishing of `xⱼ`
at `t(x)` with that of `tⱼ` at `x`, and on the chart where `tᵢ` does not vanish it identifies the
pullback of the coordinate ratio `xⱼ / xᵢ` with `tⱼ / tᵢ`. Over a `k`-point these ratios are the
homogeneous coordinates of `t(p)`, and they determine `t` [Stacks, Tag 01NE].

## References

* [Hartshorne, *Algebraic Geometry*, II.7.1][hartshorne1977]
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- Sections of a module without common zero generate every stalk. -/
private theorem generatesStalks_of_forall_exists_mem_nonvanishingLocus {X : Scheme.{u}}
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {ι : Type*} (s : ι → Γ(L, ⊤))
    (hs : ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus L (s j)) :
    Stacks.ProjectiveFromSections.GeneratesStalks s := by
  classical
  intro x w
  obtain ⟨i, hi⟩ := hs x
  obtain ⟨c, hc⟩ := Stacks.SectionProduct.exists_smul_Γgerm L (s i) hi w
  refine ⟨{i}, fun j => if j = i then c else 0, ?_⟩
  simpa using hc

/-- **Morphisms defined by sections.** Let `X` be a projective variety over a field `k`, with
structure morphism `f`, `L` a line bundle on `X` and `t₀, …, tᵣ` global sections of `L` without
common zero. Then there are a morphism of `k`-schemes `t : X ⟶ ℙʳ_k` and an isomorphism
`α : t^* 𝒪(1) ≅ L` with `α (t^* xⱼ) = tⱼ` for every `j`, where `xⱼ` is the `j`-th homogeneous
coordinate of `ℙʳ_k`. -/
@[faltings "lem_ht_morphism_from_sections"]
theorem exists_hom_and_iso_pullback_projectiveSpaceTwistingSheaf {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {r : ℕ} (s : Fin (r + 1) → Γ(L, ⊤))
    (hs : ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus L (s j)) :
    ∃ t : X ⟶ projectiveSpaceOver r (Spec (.of k)),
      t ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) = f ∧
      ∃ α : (Scheme.Modules.pullback t).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ L,
        ∀ j, α.hom.app ⊤ (pullbackGlobalSections t _
          (pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)))
            (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse r)
            (Stacks.TwistPullbackPinned.coordGlobalSection r j))) = s j := by
  obtain ⟨p, hp, α, _, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse s
      (generatesStalks_of_forall_exists_mem_nonvanishingLocus s hs) f
  refine ⟨p, hp, (Scheme.Modules.pullbackComp p _).app _ ≪≫ asIso α, fun j => ?_⟩
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Iso.app_hom,
    SectionsEqualizer.pullbackGlobalSections_comp]
  exact hα j

end Faltings
