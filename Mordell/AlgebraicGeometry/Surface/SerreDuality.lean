module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentials
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SerreDualityLocallyFree
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.AlgebraicGeometry.Curves.DualizingInvertibleDimensionDuality
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import Mordell.AlgebraicGeometry.Cohomology.SheafCohomologyFinrank

/-!
# Serre duality on a smooth projective surface

Let `X` be a smooth projective geometrically integral surface over a field `k`, with structure
morphism `f : X ⟶ Spec k`, and let `K_X = ⋀² Ω_{X/k}` be its canonical sheaf. For every
invertible `𝒪_X`-module `𝓛` and every integer `i`,
`dim_k H^i(X, 𝓛) = dim_k H^{2-i}(X, K_X ⊗ 𝓛^{-1})`,
where cohomology in negative degrees is zero.

The surface `X` is Cohen--Macaulay and equidimensional of dimension `2`, so Serre duality for
locally free modules ([Stacks, Tag 0FW0]) gives perfect pairings
`H^{2-i}(X, ω_X ⊗ 𝓛^∨) × H^i(X, 𝓛) → k` for every `i : ℤ`. Since `X` is smooth of relative
dimension `2`, `ω_X ≅ ⋀² Ω_{X/k}` ([Stacks, Tag 0FVV (7)], [Stacks, Tag 0BRT]), and
`𝓛^∨ ≅ 𝓛^{⊗ -1}` ([Stacks, Tag 0B8K]); comparing dimensions gives the result.

## Main results

* `Faltings.finrank_cohomologyOverField_eq_finrank_cohomologyOverField_canonical_twist`:
  the equality of dimensions above, for every `i : ℤ`.

## Implementation notes

Cohomology is `AlgebraicGeometry.cohomologyOverField`, indexed by `ℕ`; the statement is made
for every `i : ℤ` by reading the dimension of `H^i` as `0` when `i < 0`. For `i > 2` the
statement therefore says that `H^i(X, 𝓛)` vanishes (and dually for `i < 0`). The twist
`K_X ⊗ 𝓛^{-1}` is `AlgebraicGeometry.twistedSheaf` of `K_X` by the single invertible module
`𝓛` with exponent `-1`, and `K_X` is `AlgebraicGeometry.Scheme.Modules.exteriorPower` of the
sheaf of relative differentials `AlgebraicGeometry.Scheme.Hom.relativeDifferentials f` in
degree `2`.

The pairing is stated on the `ℤ`-indexed cohomology `Stacks.Duality.sheafCohomology` of the
derived cup-product framework; `Faltings.finrank_sheafCohomology_eq_ite` compares its dimensions
with those of `cohomologyOverField`.

## References

* [Stacks Project, Tag 0FW0], [Stacks Project, Tag 0BRT], [Stacks Project, Tag 0FVV],
  [Stacks Project, Tag 0B8K]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- **Serre duality on a smooth projective surface.** For a smooth projective geometrically
integral surface `f : X ⟶ Spec k`, with canonical sheaf `K_X = ⋀² Ω_{X/k}`, and an invertible
`𝒪_X`-module `L`, `dim_k H^i(X, L) = dim_k H^{2-i}(X, K_X ⊗ L^{-1})` for every `i : ℤ`
(cohomology in negative degrees being zero). The proof compares dimensions across the
perfect Serre pairing `H^{2-i}(X, ω_X ⊗ L^∨) × H^i(X, L) → k`, after identifying
`ω_X ⊗ L^∨` with `K_X ⊗ L^{-1}`. -/
@[faltings "lem_nt_serre_duality_surface"]
theorem finrank_cohomologyOverField_eq_finrank_cohomologyOverField_canonical_twist
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 2 f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (i : ℤ) :
    (if 0 ≤ i then Module.finrank k (cohomologyOverField k f L i.toNat) else 0) =
      if 0 ≤ 2 - i then
        Module.finrank k (cohomologyOverField k f
          (twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
            (fun _ : Fin 1 => L) (fun _ => -1)) (2 - i).toNat)
      else 0 := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hequi : TopologicalSpace.Equidimensional X := by
    intro Z hZ W hW
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ hW
    rw [hZ, hW]
  -- the perfect pairing `H^{2-i}(ω ⊗ 𝓛^∨) × H^i(𝓛) → k`
  have hP := Stacks.Duality.serrePairing_isPerfPair f
    (isCohenMacaulay_of_isRegular (isRegular_of_smooth_over_field f)) hequi 2
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 f) L
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1) (2 - i) i
    (by push_cast; ring)
  -- `ω_X ≅ ⋀² Ω_{X/k}`
  have eω :=
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f 2).2.some
  -- `K_X ⊗ 𝓛^{-1} ≅ ω_X ⊗ 𝓛^∨`
  have eT : twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
        (fun _ : Fin 1 => L) (fun _ => -1) ≅
      Stacks.Duality.tensorModule (Stacks.Duality.dualizingModule f)
        (Stacks.Duality.dualModule L) :=
    Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf X.ringCatSheaf.property
      eω.symm
      (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
        X.ringCatSheaf.property L _
        (Stacks.SheafOfModules.Invertible.mulNegOneIso X.presheaf X.ringCatSheaf.property L))
  rw [finrank_cohomologyOverField_eq_of_iso k f eT, ← finrank_sheafCohomology_eq_ite,
    ← finrank_sheafCohomology_eq_ite]
  exact ((LinearEquiv.ofBijective _ hP.bijective_left).finrank_eq.trans
    Subspace.dual_finrank_eq).symm

end Faltings
