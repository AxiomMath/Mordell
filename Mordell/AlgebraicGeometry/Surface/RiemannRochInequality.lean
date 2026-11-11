module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentials
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import Mordell.AlgebraicGeometry.Surface.SerreDuality
public import Mordell.AlgebraicGeometry.Surface.RiemannRoch

/-!
# The easy Riemann–Roch inequality on a surface

Let `X` be a smooth projective geometrically integral surface over a field `k`, with structure
morphism `f : X ⟶ Spec k`, canonical sheaf `K_X = ⋀² Ω_{X/k}`, and let `𝓛 = 𝒪_X(D)` be an
invertible `𝒪_X`-module. Then
`h⁰(𝓛) + h⁰(K_X ⊗ 𝓛⁻¹) ≥ ½ (𝓛 · 𝓛) - ½ (𝓛 · K_X) + χ(𝒪_X)`,
where `h⁰(𝓜) = dim_k H⁰(X, 𝓜)`. It follows from Riemann–Roch on the surface, since
`χ(𝓛) ≤ h⁰(𝓛) + h²(𝓛)`, and `h²(𝓛) = h⁰(K_X ⊗ 𝓛⁻¹)` by Serre duality.

## Main results

* `Faltings.riemannRoch_inequality_surface`: the inequality above.

## Implementation notes

A divisor `D` enters only through its invertible sheaf `𝒪_X(D)`, so the statement is made for
an arbitrary invertible module `L`, and `K_X - D` is the twist `K_X ⊗ L⁻¹`, i.e.
`AlgebraicGeometry.twistedSheaf` of `K_X` by `L` with exponent `-1`. The intersection pairing is
`AlgebraicGeometry.intersectionNumber` on `Z = X` with `d = 2`; it needs `K_X` invertible, which
holds because `Ω_{X/k}` is finite locally free of rank `2`
(`Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials`), so that its top exterior
power is invertible (`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`). The
Euler characteristic of `𝒪_X` is `AlgebraicGeometry.eulerCharacteristic`, with coherence from
properness. The inequality is stated in `ℚ` to accommodate the halves.

## References

* [Bombieri, *The Mordell conjecture revisited*, §1]
* [Beauville, *Complex algebraic surfaces*, I.12]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- On a proper scheme over `k` whose cohomology of `F` vanishes from degree `3` on, the Euler
characteristic of `F` is `h⁰ - h¹ + h²`. -/
private theorem eulerCharacteristic_eq_of_finrank_eq_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsCoherent] (h : ∀ n, 3 ≤ n → Module.finrank k (cohomologyOverField k f F n) = 0) :
    eulerCharacteristic k f F =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f F 1) +
        Module.finrank k (cohomologyOverField k f F 2) := by
  rw [eulerCharacteristic_eq_finsum, finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp [Finset.sum_range_succ]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hn'
    exact hn (by rw [h n (by omega)]; simp)

/-- On a smooth projective surface, Serre duality bounds the Euler characteristic of an invertible
module: `χ(𝓛) ≤ h⁰(𝓛) + h⁰(K_X ⊗ 𝓛⁻¹)`. -/
private theorem eulerCharacteristic_le_finrank_add_finrank_canonical_twist
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 2 f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] [L.IsCoherent] :
    eulerCharacteristic k f L ≤
      (Module.finrank k (cohomologyOverField k f L 0) : ℤ) +
        Module.finrank k (cohomologyOverField k f
          (twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
            (fun _ : Fin 1 => L) (fun _ => -1)) 0) := by
  have S := Faltings.finrank_cohomologyOverField_eq_finrank_cohomologyOverField_canonical_twist
    k f L
  have h2 := S 2
  simp at h2
  rw [eulerCharacteristic_eq_of_finrank_eq_zero k f L fun n hn => by
    simpa [show ¬n ≤ 2 by omega] using S n, h2]
  omega

/-- **The easy Riemann–Roch inequality on a surface.** For a smooth projective geometrically
integral surface `f : X ⟶ Spec k` with canonical sheaf `K_X = ⋀² Ω_{X/k}` and an invertible
`𝒪_X`-module `L`,
`dim_k H⁰(X, L) + dim_k H⁰(X, K_X ⊗ L⁻¹) ≥ ½ (L · L) - ½ (L · K_X) + χ(𝒪_X)`. -/
@[faltings "thm_nt_riemann_roch_inequality_surface"]
theorem riemannRoch_inequality_surface
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 2 f]
    (hX : topologicalKrullDim X = 2)
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f 2
    haveI hK : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Scheme.Modules.exteriorPower f.relativeDifferentials 2) :=
      (Scheme.Modules.isInvertible_exteriorPower_self f.relativeDifferentials 2).toAlgebraicGeometry
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
    (1 / 2 : ℚ) * (@intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![L, L]
          (Fin.forall_fin_two.2 ⟨hL, hL⟩) : ℚ) -
        (1 / 2 : ℚ) * (@intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX])
          ![L, Scheme.Modules.exteriorPower f.relativeDifferentials 2]
          (Fin.forall_fin_two.2 ⟨hL, hK⟩) : ℚ) +
        (eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) : ℚ) ≤
      (Module.finrank k (cohomologyOverField k f L 0) : ℚ) +
        (Module.finrank k (cohomologyOverField k f
          (twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
            (fun _ : Fin 1 => L) (fun _ => -1)) 0) : ℚ) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have RR := Faltings.eulerCharacteristic_eq_of_smoothOfRelativeDimension_two k f L
  have := eulerCharacteristic_le_finrank_add_finrank_canonical_twist k f L
  simp only at RR
  have : ((eulerCharacteristic k f L : ℤ) : ℚ) ≤ _ := Int.cast_le.2 this
  push_cast at this
  linarith

end Faltings
