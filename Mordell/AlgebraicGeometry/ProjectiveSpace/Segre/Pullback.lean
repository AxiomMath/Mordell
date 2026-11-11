module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# Pullback of `𝒪(1)` under the Segre morphism

Let `S` be a scheme and `s : ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` the Segre morphism
`Faltings.segreMorphism`, given by the forms `z_{ij} = x_i y_j`. The pullback of the hyperplane
sheaf along `s` is the external tensor product of the hyperplane sheaves of the two factors,
`s^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`: the morphism `s` is the one defined by the invertible
module `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` and its global sections `pr₁^* x_i ⊗ pr₂^* y_j`, and the
pullback of `z_{ij}` is `pr₁^* x_i ⊗ pr₂^* y_j`.

## Main results

* `Faltings.nonempty_pullback_segreMorphism_projectiveSpaceTwistingSheaf_iso`:
  `s^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` as modules on `ℙⁿ_S ×_S ℙᵐ_S`.

## Implementation notes

The hyperplane sheaf on `ℙⁿ_S` is `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`,
the pullback of `𝒪(1)` on the integral model, and `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` is
`AlgebraicGeometry.externalTensorProduct` of the two structure morphisms. The statement is over an
arbitrary base scheme `S`; the source's case is `S = Spec Q̄`.

Over a base `S` the Segre morphism is the base change of the Segre morphism of the integral
models, which is the morphism defined by sections; the twist comparison of [Stacks, Tag 01NE]
identifies the pullback of `𝒪(1)` there, and the identification is pulled back along
`ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, pullback of modules being pseudofunctorial and commuting with
tensor products [Stacks, Tag 01CD]. The morphism defined by sections exists in two
constructions gluing the same chart morphisms of the ratio families; the twist comparison is
stated for one, and the other restricts on every chart to the chart morphism of the first, the
two ratios being the unique solutions of the same equation.

## References

* [Hartshorne, *Algebraic Geometry*, II Ex. 5.11][hartshorne1977]
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

open AlgebraicGeometry CategoryTheory Limits Stacks.AmpleProjectiveImmersion

universe u

namespace Faltings

/-- For a commutative square `f ≫ g = f' ≫ g'`, the iterated pullbacks `f^* g^* M` and
`f'^* g'^* M` are isomorphic. -/
private noncomputable def pullbackPullbackIsoOfComm {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (M : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g').obj M) :=
  (Scheme.Modules.pullbackComp f g).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp f' g').app M).symm

open Opposite in
private theorem ratio_eq {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → L.sections)
    (i k : Fin (n + 1)) :
    Stacks.ProjectiveFromSections.ratio (fun k => (s k).eval (op ⊤)) i k =
      Stacks.SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) le_rfl
        ((s k).eval (op _)) := by
  symm
  refine Stacks.ProjectiveFromSections.eq_div _ _ ?_
  have h1 := Stacks.SheafOfModules.smul_divBySection (X := X.toRingedSpace) L (s i)
    (le_rfl : Stacks.ProjectiveSpaceSections.nonvanishingChart L (s i) ≤ _) ((s k).eval (op _))
  have h2 : ∀ j, Stacks.ProjectiveFromSections.resT
      (Stacks.ProjectiveSpaceSections.nonvanishingChart L (s i)) ((s j).eval (op ⊤)) =
      (s j).eval (op _) := fun j =>
    Stacks.SheafOfModules.secRestr_sections_eval (X := X.toRingedSpace) L (s j) le_top
  exact (congrArg (fun t => Stacks.SheafOfModules.divBySection (X := X.toRingedSpace) L (s i)
    (le_rfl : Stacks.ProjectiveSpaceSections.nonvanishingChart L (s i) ≤ _)
      ((s k).eval (op _)) • t) (h2 i)).trans (h1.trans (h2 k).symm)

open Opposite in
private theorem chartRatio_eq {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → L.sections)
    (i : Fin (n + 1)) :
    Stacks.ProjectiveFromSections.chartRatio (fun k => (s k).eval (op ⊤)) i =
      Stacks.ProjectiveSpaceSections.chartRatio L s i := by
  funext k
  exact congrArg _ (ratio_eq L s i k)

open Opposite in
private theorem ι_morphismAtUniverse {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → L.sections)
    (hs : (⨆ i, Stacks.ProjectiveSpaceSections.nonvanishingChart L (s i)) = ⊤)
    (i : Fin (n + 1)) :
    (Stacks.ProjectiveFromSections.nvCover (fun k => (s k).eval (op ⊤)) i).ι ≫
        Stacks.ProjectiveSpaceSections.morphismAtUniverse L s hs =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (Stacks.ProjectiveFromSections.chartRatio (fun k => (s k).eval (op ⊤)) i)
        (Stacks.ProjectiveFromSections.span_range_chartRatio _ i) := by
  refine (Stacks.ProjectiveSpaceSections.nonvanishingChart_ι_morphismAtUniverse L s hs i).trans ?_
  unfold Stacks.ProjectiveSpaceSections.chartMorphism
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
  have h : Stacks.ProjectiveSpaceSections.chartHom L s i =
      Stacks.SectionsToProjectiveSpace.sectionsHom
        (Stacks.ProjectiveFromSections.chartRatio (fun k => (s k).eval (op ⊤)) i) := by
    rw [chartRatio_eq]
    rfl
  simp only [h]
  rfl

open Opposite in
private theorem nonempty_pullback_morphismAtUniverse_iso {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {n : ℕ} (s : Fin (n + 1) → L.sections)
    (hs : (⨆ i, Stacks.ProjectiveSpaceSections.nonvanishingChart L (s i)) = ⊤) :
    Nonempty ((Scheme.Modules.pullback
      (Stacks.ProjectiveSpaceSections.morphismAtUniverse L s hs)).obj
        (twistingSheafAtUniverse.{u} n) ≅ L) := by
  obtain ⟨α, _, -⟩ := Stacks.TwistPullbackPinned.exists_iso_pullback_twistingSheafAtUniverse
    (fun k => (s k).eval (op ⊤)) (Stacks.ProjectiveSpaceSections.morphismAtUniverse L s hs)
    hs (ι_morphismAtUniverse L s hs)
  exact ⟨asIso α⟩

private theorem nonempty_pullback_segreMorphism_iso (n m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (Segre.segreMorphism.{u} n m)).obj
        (twistingSheafAtUniverse.{u} (n * m + n + m)) ≅ Segre.segreModule.{u} n m) := by
  haveI : Stacks.Ample.IsInvertibleModule _ (Segre.segreModule.{u} n m) :=
    Segre.isInvertible_segreModule.{u} n m
  exact nonempty_pullback_morphismAtUniverse_iso _ _ _

/-- **Segre pullback of `𝒪(1)`**: for the Segre morphism `s : ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S`,
`s^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`. -/
@[faltings "lem_ht_segre_pullback"]
public theorem nonempty_pullback_segreMorphism_projectiveSpaceTwistingSheaf_iso
    (n m : ℕ) (S : Scheme.{u}) :
    Nonempty ((Scheme.Modules.pullback (segreMorphism n m S)).obj
        (projectiveSpaceTwistingSheaf (n * m + n + m) S) ≅
      externalTensorProduct (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S)
        (projectiveSpaceTwistingSheaf n S) (projectiveSpaceTwistingSheaf m S)) := by
  let ρ : pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ⟶
      Segre.segreProduct.{u} n m :=
    pullback.lift (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
      (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m S) (terminal.hom_ext _ _)
  have hσ : Faltings.segreMorphism n m S ≫
      projectiveSpaceOver.toIntegralAtUniverse (n * m + n + m) S =
      ρ ≫ Segre.segreMorphism.{u} n m :=
    projectiveSpaceOver.liftAtUniverse_toIntegralAtUniverse _ _ _
  have h1 : ρ ≫ Segre.segreFst.{u} n m =
      pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S :=
    pullback.lift_fst _ _ _
  have h2 : ρ ≫ Segre.segreSnd.{u} n m =
      pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m S :=
    pullback.lift_snd _ _ _
  obtain ⟨α⟩ := nonempty_pullback_segreMorphism_iso.{u} n m
  exact ⟨pullbackPullbackIsoOfComm hσ _ ≪≫ (Scheme.Modules.pullback ρ).mapIso α ≪≫
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso ρ _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      (pullbackPullbackIsoOfComm h1 _)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso (pullbackPullbackIsoOfComm h2 _)⟩

end Faltings
