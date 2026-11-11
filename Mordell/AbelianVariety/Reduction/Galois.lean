module

public import Mathlib
public import Mordell.AbelianVariety.AbelianScheme.BaseChange
public import Mordell.AbelianVariety.Reduction.Basic

/-!
# Reduction commutes with automorphisms of the base

Let `R` be a discrete valuation ring with fraction field `L` and residue field `κ(s)`, let
`R₀ → R` be a ring map, `𝒜₀` an abelian scheme over `R₀` and `𝒜 = 𝒜₀ ×_{R₀} R`, with generic
fibre `A`. An automorphism `τ` of the `R₀`-algebra `R` induces automorphisms `τ_L` of `L` and
`τ̄` of `κ(s)`. Viewing points as `R₀`-morphisms into `𝒜₀`, the reduction map
`Faltings.reductionMap` satisfies `red (P ∘ Spec τ_L) = red P ∘ Spec τ̄` for `P ∈ A(L)`.

## Main results

* `Faltings.reductionMap_comp_spec_map_residueFieldMapEquiv`: reduction commutes with the
  automorphisms induced by `τ`.

## Implementation notes

The base change `𝒜` is `(Over.pullback (Spec.map (algebraMap R₀ R))).mapGrp.obj 𝒜₀`. A point of
`A(L)` (resp. of `𝒜(κ(s))`) is viewed as a morphism of schemes into `𝒜₀` by composing its
underlying morphism with the first projections of the fibre products. Since `P ∘ Spec τ_L` is
not a morphism over `Spec L`, the statement takes a second point `P'` whose underlying
`R₀`-morphism into `𝒜₀` is `P ∘ Spec τ_L`; such a `P'` exists and is unique by the universal
property of the fibre product. The automorphisms `τ_L` and `τ̄` are
`IsFractionRing.ringEquivOfRingEquiv` and `IsLocalRing.ResidueField.mapEquiv` applied to `τ`.
That `𝒜` is flat, proper, locally of finite presentation, with proper and geometrically integral
fibres, follows from the same properties of `𝒜₀` by stability under base change: `𝒜₀` is
geometrically integral over `R₀` since its fibres are
(`AlgebraicGeometry.GeometricallyIntegral.iff_geometricallyIntegral_fiber`).

## References

* [J. H. Silverman, *The arithmetic of elliptic curves*][silvermanAEC], §VII.2
* [J. S. Milne, *Abelian varieties*][milneAV], proof of Theorem IV.3.5
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

/-- The reduction of `P` is the restriction to the closed point of any section `Q` extending
`P`. -/
private lemma reductionMap_left_eq (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj 𝒜.X)
    (Q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X)
    (hQ : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Q.left = P.left ≫ pullback.fst _ _) :
    (reductionMap R L 𝒜 hfib P).left =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ Q.left := by
  rw [reductionMap_eq_of_extension R L 𝒜 hfib (Q := Q) (Over.OverMorphism.ext ?_)]
  · rfl
  · simp only [Over.map_obj_left, Over.tensorUnit_left, Over.comp_left, Over.toUnit_left,
      Over.map_obj_hom, Over.tensorUnit_hom, Category.id_comp]
    exact hQ

/-- Let `R` be a discrete valuation ring with fraction field `L`, `R₀ → R` a ring map, `𝒜₀` an
abelian scheme over `R₀`, `𝒜 = 𝒜₀ ×_{R₀} R` and `A` its generic fibre, and let `τ` be an
`R₀`-algebra automorphism of `R`, with induced automorphisms `τ_L` of `L` and `τ̄` of `κ(s)`. If
`P, P' ∈ A(L)` are such that `P'`, viewed as a morphism `Spec L ⟶ 𝒜₀`, is `P ∘ Spec τ_L`, then
`Faltings.reductionMap` of `P'`, viewed as a morphism `Spec κ(s) ⟶ 𝒜₀`, is
`Faltings.reductionMap P ∘ Spec τ̄`. -/
@[faltings "lem_mw_reduction_galois_compatible"]
theorem reductionMap_comp_spec_map_residueFieldMapEquiv (R₀ R L : Type u) [CommRing R₀]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R₀ R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜₀ : Grp (Over (Spec (CommRingCat.of R₀))))
    [Flat 𝒜₀.X.hom] [IsProper 𝒜₀.X.hom] [LocallyOfFinitePresentation 𝒜₀.X.hom]
    (hfib₀ : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜₀.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜₀.X).hom)
    (τ : R ≃ₐ[R₀] R)
    (P P' : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀).X)
    (hP : P'.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
          (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.toRingEquiv).toRingHom) ≫
        P.left ≫ pullback.fst _ _ ≫ pullback.fst _ _) :
    haveI := flat_mapGrp_obj (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
    haveI := isProper_mapGrp_obj (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
    haveI := locallyOfFinitePresentation_mapGrp_obj
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
    (reductionMap R L ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
        𝒜₀) (fibres_mapGrp_obj _ 𝒜₀ hfib₀) P').left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
          (IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv).toRingHom) ≫
        (reductionMap R L ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R₀ R)))).mapGrp.obj 𝒜₀) (fibres_mapGrp_obj _ 𝒜₀ hfib₀) P).left ≫
          pullback.fst _ _ := by
  have := flat_mapGrp_obj (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
  have := isProper_mapGrp_obj (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
  have := locallyOfFinitePresentation_mapGrp_obj
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀
  have hfib := fibres_mapGrp_obj (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀ hfib₀
  obtain ⟨e, he⟩ := exists_mulEquiv_points_fractionRing R L
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀) hfib
  obtain ⟨Q, hQ⟩ := e.surjective (Over.homMk (P.left ≫ pullback.fst _ _) (by
    have h := Over.w P
    simp only [Over.pullback_obj_hom] at h
    simp [pullback.condition, reassoc_of% h]))
  replace hQ : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Q.left =
      P.left ≫ pullback.fst _ _ := by
    rw [← he, hQ]; rfl
  let q : Spec (CommRingCat.of R) ⟶
      pullback 𝒜₀.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) := Q.left
  have hq : q ≫ pullback.snd _ _ = 𝟙 _ := Over.w Q
  have hq' : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ q =
      (P.left ≫ pullback.fst _ _ :
        _ ⟶ pullback 𝒜₀.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))) := hQ
  let Q' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀).X :=
    Over.homMk (pullback.lift
      (Spec.map (CommRingCat.ofHom τ.toRingEquiv.toRingHom) ≫ q ≫ pullback.fst _ _)
      (𝟙 _) (by
        rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hq,
          Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact τ.toAlgHom.comp_algebraMap)) (pullback.lift_snd _ _ _)
  rw [reductionMap_left_eq R L _ hfib P Q hQ, reductionMap_left_eq R L _ hfib P' Q' ?_]
  · change Spec.map _ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ =
      Spec.map _ ≫ Spec.map _ ≫ q ≫ pullback.fst _ _
    rw [pullback.lift_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
  · obtain ⟨p', hp'⟩ : ∃ p' : Spec (CommRingCat.of L) ⟶
        pullback 𝒜₀.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))),
        p' = P'.left ≫ pullback.fst _ _ := ⟨_, rfl⟩
    have h₁ : p' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom
        (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.toRingEquiv).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ q ≫ pullback.fst _ _ := by
      rw [hp', reassoc_of% hq']
      exact hP
    have h₂ : p' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      have hP' : P'.left ≫ pullback.snd _ _ = 𝟙 _ := Over.w P'
      rw [hp']
      change P'.left ≫ (pullback.fst _ _ ≫
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀).X.hom) = _
      rw [pullback.condition, reassoc_of% hP']
    refine (?_ : Spec.map _ ≫ pullback.lift _ _ _ = p').trans hp'
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, h₁, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      simp
    · rw [Category.assoc, pullback.lift_snd, h₂]
      rfl

end Faltings
