module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DerivedGlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The long exact cohomology sequence of a ringed space

Let `(X, 𝒪_X)` be a ringed space. The cohomology `Hⁿ(X, ℱ)` of an `𝒪_X`-module `ℱ` is the `n`-th
right derived functor of the global sections functor
`Γ(X, -) : Mod(𝒪_X) ⥤ Mod(Γ(X, 𝒪_X))`, so it is a `Γ(X, 𝒪_X)`-module and every map it induces is
`Γ(X, 𝒪_X)`-linear. A short exact sequence `0 ⟶ ℱ' ⟶ ℱ ⟶ ℱ'' ⟶ 0` of `𝒪_X`-modules gives
`Γ(X, 𝒪_X)`-linear connecting maps `Hⁿ(X, ℱ'') ⟶ Hⁿ⁺¹(X, ℱ')` for which
`0 ⟶ H⁰(X, ℱ') ⟶ H⁰(X, ℱ) ⟶ H⁰(X, ℱ'') ⟶ H¹(X, ℱ') ⟶ H¹(X, ℱ) ⟶ ⋯` is exact.

## Main results

* `Faltings.exists_rightDerived_moduleGlobalSections_longExactSequence`: the long exact sequence
  of `Γ(X, 𝒪_X)`-modules attached to a short exact sequence of `𝒪_X`-modules.

## Implementation notes

The global sections functor is `Stacks.Cohomology.moduleGlobalSections X`, valued in modules over
`Γ(X, 𝒪_X)`, and `Hⁿ(X, -)` is its right derived functor `Functor.rightDerived n`. The exactness
is that of the cohomological δ-functor
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, whose parts are these right
derived functors; it is stated here on elements, as linear maps of `Γ(X, 𝒪_X)`-modules.

## References

* [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

public section

open CategoryTheory Stacks.Cohomology

namespace Faltings

universe u

attribute [local instance] HasDerivedCategory.standard in
/-- **The long exact cohomology sequence.** Let `(X, 𝒪_X)` be a ringed space. For a short exact
sequence `0 ⟶ ℱ' ⟶ ℱ ⟶ ℱ'' ⟶ 0` of `𝒪_X`-modules there are `Γ(X, 𝒪_X)`-linear connecting maps
`δ n : Hⁿ(X, ℱ'') ⟶ Hⁿ⁺¹(X, ℱ')` for which
`0 ⟶ H⁰(X, ℱ') ⟶ H⁰(X, ℱ) ⟶ H⁰(X, ℱ'') ⟶ H¹(X, ℱ') ⟶ H¹(X, ℱ) ⟶ ⋯` is exact, where `Hⁿ(X, -)` is
the `n`-th right derived functor of `Stacks.Cohomology.moduleGlobalSections X`. The connecting
maps and the exactness are those of the δ-functor
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (moduleGlobalSections X)`. -/
@[faltings "lem_ff_cohomology_tools"]
theorem exists_rightDerived_moduleGlobalSections_longExactSequence
    (X : AlgebraicGeometry.RingedSpace.{u})
    {S : ShortComplex (Modules X)} (hS : S.ShortExact) :
    ∃ δ : ∀ n : ℕ,
        ((moduleGlobalSections X).rightDerived n).obj S.X₃ ⟶
          ((moduleGlobalSections X).rightDerived (n + 1)).obj S.X₁,
      Function.Injective (((moduleGlobalSections X).rightDerived 0).map S.f).hom ∧
      (∀ n, Function.Exact (((moduleGlobalSections X).rightDerived n).map S.f).hom
        (((moduleGlobalSections X).rightDerived n).map S.g).hom) ∧
      (∀ n, Function.Exact (((moduleGlobalSections X).rightDerived n).map S.g).hom
        (δ n).hom) ∧
      ∀ n, Function.Exact (δ n).hom
        (((moduleGlobalSections X).rightDerived (n + 1)).map S.f).hom := by
  let E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (moduleGlobalSections X)
  exact ⟨E.δ hS, (ModuleCat.mono_iff_injective _).1 (E.mono_map_f hS),
    fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (E.exact_map hS n),
    fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (E.exact_δ₁ hS n),
    fun n => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (E.exact_δ₂ hS n)⟩

end Faltings

end
