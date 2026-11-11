module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-!
# Intersecting with an effective Cartier divisor on a surface

Let `X` be a proper scheme of dimension `2` over a field `k`, let `𝓛` be an invertible
`𝓞_X`-module and let `E ⊆ X` be an effective Cartier divisor. Then the intersection number
`(𝓛 · 𝓞_X(E))` equals the degree of the restriction `𝓛|_E` on the curve `E`.

## Main results

* `Faltings.intersectionNumber_eq_invertibleCurveDegree_of_isEffectiveCartierDivisor`:
  `(𝓛 · 𝓜) = deg(𝓛|_E)` for every invertible `𝓜 ≅ 𝓞_X(E)`.

## Implementation notes

The intersection number `(𝓛 · 𝓜)` is `AlgebraicGeometry.intersectionNumber` with `Z = X`
(the identity closed immersion) and `d = 2`, applied to the family `![𝓛, 𝓜]`; the degree of
an invertible module on a proper scheme of dimension `≤ 1` is
`AlgebraicGeometry.invertibleCurveDegree`. The divisor `E` is an ideal sheaf `E` on `X` with
`Stacks.Divisors.IsEffectiveCartierDivisor E`, its closed subscheme is `E.subscheme` with
inclusion `E.subschemeι`, and `𝓞_X(E)` is `Stacks.Divisors.invertibleSheaf E`. Since the
library records no invertibility instance on `Stacks.Divisors.invertibleSheaf E`, the second
module is an invertible `𝓜` together with an isomorphism `𝓜 ≅ 𝓞_X(E)`; this is the same
statement for `𝓜 = 𝓞_X(E)` and is invariant under isomorphism. That `E` has dimension `≤ 1`
is `AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper`.

The proof swaps the two modules (`AlgebraicGeometry.intersectionNumber_comp_perm`), so that
[Stacks, Tag 0BEU] (`AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor'`)
turns `(𝓞_X(E) · 𝓛)` into `(𝓛 · E)`, which is `deg(𝓛|_E)` by [Stacks, Tag 0BEY]
(`AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree`).

## References

* [Stacks] The Stacks project, Tags 0BEP, 0BEU, 0BEY.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Faltings

/-- [Stacks, Tag 0BEY] along a closed immersion `j` equal to `E.subschemeι`: the intersection
number of `L` with the curve `E` is the degree of `L|_E`. Stating it for an arbitrary `j` lets
it absorb the composite `E.subschemeι ≫ 𝟙 X` that [Stacks, Tag 0BEU] produces. -/
private theorem intersectionNumber_eq_invertibleCurveDegree_of_eq_subschemeι (k : Type*)
    [Field k] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (E : X.IdealSheafData) (j : E.subscheme ⟶ X) [IsClosedImmersion j]
    (hj : j = E.subschemeι) (h₁ : topologicalKrullDim E.subscheme ≤ (1 : ℕ))
    (h₂ : topologicalKrullDim E.subscheme ≤ 1) :
    intersectionNumber k f j 1 h₁ (fun _ => L) =
      invertibleCurveDegree k (E.subschemeι ≫ f) h₂
        ((Scheme.Modules.pullback E.subschemeι).obj L) := by
  subst hj
  exact intersectionNumber_one_eq_invertibleCurveDegree k f _ h₂ L

/-- On a proper surface `X` over a field `k`, the intersection number of an invertible module
`L` with an invertible module `M ≅ 𝓞_X(E)`, `E` an effective Cartier divisor, is the degree of
the restriction of `L` to the curve `E`. -/
@[faltings "lem_nt_intersection_restriction"]
theorem intersectionNumber_eq_invertibleCurveDegree_of_isEffectiveCartierDivisor
    (k : Type*) [Field k] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hX : topologicalKrullDim X = 2) (L M : X.Modules)
    [hLinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [hMinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (E : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hM : M ≅ Stacks.Divisors.invertibleSheaf E) :
    @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![L, M]
        (Fin.forall_fin_two.2 ⟨hLinv, hMinv⟩) =
      @invertibleCurveDegree k _ E.subscheme (E.subschemeι ≫ f) _
        (by
          simpa using topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
            k f (𝟙 X) 1 (by simp [hX]) E)
        ((Scheme.Modules.pullback E.subschemeι).obj L)
        (isInvertible_pullbackObj E.subschemeι L) := by
  have hd : topologicalKrullDim X ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) := by simp [hX]
  have : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (![M, L] t) :=
    Fin.forall_fin_two.2 ⟨hMinv, hLinv⟩
  have hE :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f (𝟙 X) 1 hd E
  -- swap the two modules, cut down to `E` by 0BEU, then compute on `E` by 0BEY
  rw [← intersectionNumber_eq_invertibleCurveDegree_of_eq_subschemeι k f L E _
    (Category.comp_id _) hE (by simpa using hE)]
  convert (intersectionNumber_comp_perm k f (𝟙 X) 2 hd ![M, L] (Equiv.swap 0 1)).trans
    (intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 1 hd ![M, L] E
      ((Scheme.Modules.pullbackId X).app M ≪≫ hM)) using 2
  · funext i; fin_cases i <;> rfl
  · funext t; fin_cases t; rfl

end Faltings
