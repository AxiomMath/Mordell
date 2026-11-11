module

public import Mordell.AbelianVariety.Reduction.Basic
public import Mordell.AbelianVariety.AbelianScheme.Torsion

/-!
# Torsion prime to the residue characteristic injects under reduction

Let `R` be a discrete valuation ring with fraction field `L` and closed point `s`, let `𝒜` be an
abelian scheme over `R` with generic fibre `A`, and let `n ≥ 1` be an integer invertible in `R`.
Then the reduction map `Faltings.reductionMap : A(L) → 𝒜(κ(s))` is injective on the
`n`-torsion `A(L)[n]`.

Two `n`-torsion points of `A(L)` extend to `R`-points of `𝒜` which are again `n`-torsion, hence
sections of the torsion subscheme `𝒜[n] → Spec R`; this morphism is unramified because
`n ∈ R^×`. The diagonal of an unramified morphism is an open immersion, so the locus where the
two sections agree is open in `Spec R`. If the points have the same reduction it contains the
closed point, and an open subset of the spectrum of a local ring containing the closed point is
everything.

## Main results

* `Faltings.injOn_reductionMap_torsion`: `red` is injective on `{P ∈ A(L) | P ^ n = 1}`.

## Implementation notes

The group structure on `A(L)` is that of the base change `(Over.pullback _).mapGrp.obj 𝒜`, as in
`Faltings.reductionMap_mul`, and is written multiplicatively, so `A(L)[n]` is the set
`{P | P ^ n = 1}`. Injectivity on a subset is `Set.InjOn`.

## References

* [J. H. Silverman, *The arithmetic of elliptic curves*][silvermanAEC], Proposition VII.3.1
* [J. S. Milne, *Abelian varieties*][milneAV], proof of Theorem IV.3.5
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings

section

/-- Two morphisms `a b : Spec R ⟶ X` from the spectrum of a local ring into a scheme unramified
over `S`, which agree over `S` and agree after some `t : T ⟶ Spec R` hitting the closed point,
are equal. -/
private lemma eq_of_comp_eq_of_closedPoint_mem_range {R : CommRingCat.{u}} [IsLocalRing R]
    {X S T : Scheme.{u}} (g : X ⟶ S) [FormallyUnramified g] [LocallyOfFiniteType g]
    {a b : Spec R ⟶ X} (hab : a ≫ g = b ≫ g) (t : T ⟶ Spec R)
    (ht : IsLocalRing.closedPoint R ∈ Set.range t) (h : t ≫ a = t ≫ b) : a = b := by
  have hp : t ≫ pullback.lift a b hab = (t ≫ a) ≫ pullback.diagonal g :=
    pullback.hom_ext (by simp [pullback.lift_fst]) (by simp [pullback.lift_snd, h])
  have hrange : Set.range (pullback.lift a b hab) ⊆ Set.range (pullback.diagonal g) := by
    have : pullback.lift a b hab ⁻¹ᵁ (pullback.diagonal g).opensRange = ⊤ := by
      apply Scheme.preimage_eq_top_of_closedPoint_mem
      obtain ⟨y, hy⟩ := ht
      rw [← hy, ← Scheme.Hom.comp_apply, hp]
      exact ⟨_, rfl⟩
    rintro _ ⟨x, rfl⟩
    exact this.ge trivial
  calc a = pullback.lift a b hab ≫ pullback.fst g g := (pullback.lift_fst a b hab).symm
    _ = pullback.lift a b hab ≫ pullback.snd g g := by
      rw [← IsOpenImmersion.lift_fac _ _ hrange, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    _ = b := pullback.lift_snd a b hab

variable (R L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field L]
  [Algebra R L] [IsFractionRing R L] (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
  [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]

/-- Restriction of `R`-points of an abelian scheme to the generic point `Spec L` is bijective. -/
private lemma toUnit_comp_bijective
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom) :
    Function.Bijective (toUnit ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj
        (𝟙_ (Over (Spec (CommRingCat.of L))))) ≫ · :
      (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X) → _) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points_fractionRing R L 𝒜 hfib
  refine ⟨fun Q₁ Q₂ h ↦ e.injective ?_, fun P ↦ ?_⟩
  · ext1
    simpa [he] using congrArg CommaMorphism.left h
  · refine ⟨e.symm (Over.homMk P.left (by simp)), ?_⟩
    ext1
    have h1 := he (e.symm (Over.homMk P.left (by simp)))
    simp only [MulEquiv.apply_symm_apply, Over.homMk_left] at h1
    conv_rhs => rw [h1]
    simp

/-- An `n`-torsion `L`-point of the generic fibre extends to an `R`-point of `𝒜` which lies in
the `n`-torsion: it satisfies the equation `P' ≫ [n] = e` cutting out `𝒜[n]`. -/
private lemma comp_zpow_eq_of_pow_eq_one
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    {n : ℕ} {P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj 𝒜).X}
    (hP : P ^ n = 1) {P' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ 𝒜.X}
    (hP' : toUnit _ ≫ P' = (mapPullbackAdjMulEquiv _ 𝒜 _).symm P) :
    P' ≫ 𝟙 𝒜.X ^ (n : ℤ) = 𝟙 _ ≫ η[𝒜.X] := by
  have hPn : P' ^ n = 1 := by
    apply (toUnit_comp_bijective R L 𝒜 hfib).1
    simp only
    rw [MonObj.comp_pow, hP', ← map_pow, hP, map_one, MonObj.comp_one]
  rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast, hPn, toUnit_unique (𝟙 _) (toUnit _)]
  rfl

end

/-- Let `R` be a discrete valuation ring with fraction field `L`, `𝒜` an abelian scheme over `R`
with generic fibre `A`, and `n ≥ 1` an integer invertible in `R`. Then the reduction map
`Faltings.reductionMap` is injective on the `n`-torsion `A(L)[n] = {P | P ^ n = 1}`. -/
@[faltings "lem_mw_torsion_injects_under_reduction"]
theorem injOn_reductionMap_torsion (R L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) :
    Set.InjOn (reductionMap R L 𝒜 hfib)
      {P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj 𝒜).X |
        P ^ n = 1} := by
  intro P hP Q hQ hPQ
  obtain ⟨P', hP'⟩ := (toUnit_comp_bijective R L 𝒜 hfib).2 ((mapPullbackAdjMulEquiv _ 𝒜 _).symm P)
  obtain ⟨Q', hQ'⟩ := (toUnit_comp_bijective R L 𝒜 hfib).2 ((mapPullbackAdjMulEquiv _ 𝒜 _).symm Q)
  beta_reduce at hP' hQ'
  rw [reductionMap_eq_of_extension R L 𝒜 hfib (P := P) hP',
    reductionMap_eq_of_extension R L 𝒜 hfib (P := Q) hQ'] at hPQ
  -- the extensions are sections of the torsion subscheme `𝒜[n] → Spec R`
  let P'' := pullback.lift P' (𝟙 _) (comp_zpow_eq_of_pow_eq_one R L 𝒜 hfib hP hP')
  let Q'' := pullback.lift Q' (𝟙 _) (comp_zpow_eq_of_pow_eq_one R L 𝒜 hfib hQ hQ')
  have hunit' : IsUnit ((n : ℤ) : Γ(Spec (CommRingCat.of R), ⊤)) := by
    rw [Int.cast_natCast, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom]
    exact hunit.map _
  obtain ⟨_, _⟩ := locallyOfFiniteType_and_formallyUnramified_torsion 𝒜 hfib (n : ℤ)
    (by exact_mod_cast hn) hunit'
  let κ := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
  have hred : toUnit κ ≫ P'' = toUnit κ ≫ Q'' := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hPQ
    · exact toUnit_unique _ _
  have : IsLocalHom (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hPQ'' : P'' = Q'' := by
    refine Over.OverMorphism.ext ?_
    exact eq_of_comp_eq_of_closedPoint_mem_range (R := CommRingCat.of R)
      (pullback (𝟙 𝒜.X ^ (n : ℤ)) η[𝒜.X]).hom ((Over.w P'').trans (Over.w Q'').symm)
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
      ⟨IsLocalRing.closedPoint _, Spec_closedPoint⟩ (congrArg CommaMorphism.left hred)
  have := congrArg (· ≫ pullback.fst _ _) hPQ''
  simp only [P'', Q'', pullback.lift_fst] at this
  subst this
  exact (mapPullbackAdjMulEquiv _ 𝒜 _).symm.injective (hP'.symm.trans hQ')

end Faltings
