module

public import Mordell.AlgebraicGeometry.Surface.IntersectionCartierDivisor
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism

/-!
# Ample invertible modules meet curves positively

Let `X` be a proper scheme of dimension `2` over a field `k`, let `𝓗` be an ample invertible
`𝓞_X`-module and let `E ⊆ X` be a nonempty effective Cartier divisor of dimension `1`. Then
the intersection number `(𝓗 · 𝓞_X(E))` is positive.

By `Faltings.intersectionNumber_eq_invertibleCurveDegree_of_isEffectiveCartierDivisor` the
intersection number `(𝓗 · 𝓞_X(E))` is the degree of `𝓗|_E` on the curve `E`. The restriction
`𝓗|_E` is ample, and an ample invertible module on a proper scheme of dimension one over `k` has
positive degree: the degree is the sum over the one-dimensional irreducible components, weighted
by positive multiplicities, of the positive degrees there, and such a component exists.

## Main results

* `Faltings.intersectionNumber_pos_of_isAmple_of_isEffectiveCartierDivisor`:
  `0 < (𝓗 · 𝓜)` for every invertible `𝓜 ≅ 𝓞_X(E)`.

## Implementation notes

The intersection number `(𝓗 · 𝓜)` is `AlgebraicGeometry.intersectionNumber` with `Z = X`
(the identity closed immersion) and `d = 2`, applied to the family `![𝓗, 𝓜]`. Ampleness is
`AlgebraicGeometry.Scheme.Modules.IsAmple`. The divisor `E` is an ideal sheaf on `X` with
`Stacks.Divisors.IsEffectiveCartierDivisor E`, and `𝓞_X(E)` is
`Stacks.Divisors.invertibleSheaf E`; since the library records no invertibility instance on the
latter, the second module is an invertible `𝓜` with an isomorphism `𝓜 ≅ 𝓞_X(E)`, which is the
same statement for `𝓜 = 𝓞_X(E)`.

Unlike `AlgebraicGeometry.C1590Private.invertibleCurveDegree_pos_of_isAmple`, the positivity of
the degree on `E` assumes no equidimensionality of `E`, only `dim E = 1`.

## References

* [Stacks] The Stacks project, Tags 0AYW, 0B5Y, 0BEP, 0BEU, 0BEV, 0BEW, 0BEY, 01PU.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry.ComponentDegrees

namespace Faltings

/-- A scheme of dimension one has a generic point with one-dimensional closure: otherwise every
point is closed in a scheme of dimension at most one, and the dimension would be at most zero. -/
private theorem nonempty_genericPointsOne_of_dim_eq_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 1) : Nonempty (genericPointsOne X) := by
  by_contra hne
  have h0 := topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne
    hdim.le isClosed_univ fun x _ hx => hne ⟨⟨x, hx⟩⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph, hdim] at h0
  exact absurd h0 (by decide)

/-- An ample invertible module on a proper scheme of dimension one over a field has positive
degree. No equidimensionality is assumed: the degree is a sum over the one-dimensional
components of positive multiplicities times positive degrees, and such a component exists. -/
private theorem invertibleCurveDegree_pos_of_isAmple_of_dim_eq_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim.le L := by
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  let : Fintype (genericPointsOne X) := (finite_genericPointsOne X).fintype
  obtain ⟨ξ⟩ := nonempty_genericPointsOne_of_dim_eq_one hdim
  rw [invertibleCurveDegree_eq_curveDegree_one,
    Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree k f
      hdim.le L 1, finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun η _ => mul_pos ?_ ?_) ⟨ξ, Finset.mem_univ _⟩
  · have hpos : 0 < Module.length (X.presheaf.stalk η.1) (X.presheaf.stalk η.1) :=
      Module.length_pos
    rw [← componentMultiplicity_cast k f η] at hpos
    exact_mod_cast hpos
  · have h := invertibleCurveDegree_reducedComponent_pos_of_isAmple k f hdim.le L hL η
    rwa [invertibleCurveDegree_eq_curveDegree_one] at h

/-- On a proper surface `X` over a field `k`, an ample invertible module `H` has positive
intersection number with `𝓞_X(E)` for every nonempty effective Cartier divisor `E` of
dimension `1`. -/
@[faltings "lem_nt_intersection_ample_positive"]
theorem intersectionNumber_pos_of_isAmple_of_isEffectiveCartierDivisor
    (k : Type*) [Field k] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hX : topologicalKrullDim X = 2) (H M : X.Modules)
    [hHinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property H]
    [hMinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (hH : Scheme.Modules.IsAmple X H)
    (E : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hEne : Nonempty E.subscheme) (hE : topologicalKrullDim E.subscheme = 1)
    (hM : M ≅ Stacks.Divisors.invertibleSheaf E) :
    0 < @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![H, M]
        (Fin.forall_fin_two.2 ⟨hHinv, hMinv⟩) := by
  rw [intersectionNumber_eq_invertibleCurveDegree_of_isEffectiveCartierDivisor k f hX H M E hM]
  exact @invertibleCurveDegree_pos_of_isAmple_of_dim_eq_one k _ E.subscheme (E.subschemeι ≫ f) _
    hE _ (isInvertible_pullbackObj E.subschemeι H)
    (Scheme.Modules.isAmple_pullback_of_isClosedImmersion E.subschemeι H hH)

end Faltings
