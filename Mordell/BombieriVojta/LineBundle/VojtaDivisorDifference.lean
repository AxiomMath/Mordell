module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# The Vojta divisor as a difference

Let `k` be a number field, `C` a smooth projective geometrically integral curve of genus
`g ≥ 2` over `k` with a divisor `P` of degree one, `X = C × C` with projections `pr₁, pr₂`,
`P × C = pr₁^* P`, `C × P = pr₂^* P`, `Δ` the diagonal and `Δ' = Δ - P × C - C × P`. Fix an
integer `s ≥ 1`, put `B = s (P × C) + s (C × P) - Δ'`, and fix an integer `N ≥ 2g + 1`. For
integers `d₁, d₂, d`, suppose `δ₁ = (d₁ + s d) / N` and `δ₂ = (d₂ + s d) / N` are integers. Then,
as divisors on `X`,
`V = d₁ (P × C) + d₂ (C × P) + d Δ' = δ₁ (N P) × C + δ₂ C × (N P) - d B`.

## Main results

* `Faltings.BombieriVojta.vojta_eq_sub`: the identity above, in the group of `1`-cycles on
  `C ×_k C`.

## Implementation notes

Divisors on the curve `C` are its `0`-cycles and divisors on the surface `C ×_k C` its `1`-cycles,
for the Chow situation `Stacks.Chow.fieldChowSituation k` (base `Spec k`, zero dimension
function). The degree of `P` is `Stacks.Chow.cycleDegree`, read at the point of `Spec k`. The
divisors `P × C` and `C × P` are the flat pullbacks `Stacks.Chow.flatPullback` along the two
projections, which are flat of relative dimension one; that relative dimension is the
hypothesis `hpr₁`, `hpr₂` the flat pullback is formed with. The diagonal `Δ` is the cycle
`Stacks.Chow.cycleAssociatedToClosedSubscheme` of the closed immersion `pullback.diagonal f`. The
divisors `Δ'` and `B` are given by their defining equations `hΔ'` and `hB`. The integrality of
`δᵢ = (dᵢ + s d) / N` is expressed as `N * δᵢ = dᵢ + s * d` with `δᵢ : ℤ`, which for `N ≥ 1` is
the same.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 619
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Faltings.BombieriVojta

/-- **The Vojta divisor as a difference** (Bombieri). Let `C` be a smooth projective
geometrically integral curve of genus `g ≥ 2` over a number field `k`, `P` a divisor of degree
one on `C`, `P × C = pr₁^* P`, `C × P = pr₂^* P`, `Δ` the diagonal of `C ×_k C`,
`Δ' = Δ - P × C - C × P`, `s ≥ 1`, `B = s (P × C) + s (C × P) - Δ'` and `N ≥ 2g + 1`. If
`N δ₁ = d₁ + s d` and `N δ₂ = d₂ + s d`, then
`d₁ (P × C) + d₂ (C × P) + d Δ' = δ₁ (N P) × C + δ₂ C × (N P) - d B`. -/
@[faltings "lem_bv_vojta_difference"]
public theorem vojta_eq_sub (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (hg : 2 ≤ genus f)
    (hpr₁ : AlgebraicGeometry.RelativeDimension (pullback.fst f f) 1)
    (hpr₂ : AlgebraicGeometry.RelativeDimension (pullback.snd f f) 1)
    (P : CycleGroup (fieldChowSituation k) f 0)
    (hP : ∀ x : Spec (.of k), cycleDegree (fieldChowSituation k) f x P = 1)
    (Δ' B : CycleGroup (fieldChowSituation k) (pullback.fst f f ≫ f) (0 + ((1 : ℕ) : ℤ)))
    (hΔ' : Δ' = cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst f f ≫ f)
        (pullback.diagonal f) (0 + ((1 : ℕ) : ℤ)) -
      flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.fst f f) rfl 1
        hpr₁ 0 P -
      flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.snd f f)
        pullback.condition.symm 1 hpr₂ 0 P)
    (s : ℤ) (hs : 1 ≤ s)
    (hB : B = s • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f
        (pullback.fst f f) rfl 1 hpr₁ 0 P +
      s • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.snd f f)
        pullback.condition.symm 1 hpr₂ 0 P - Δ')
    (N : ℤ) (hN : 2 * (genus f : ℤ) + 1 ≤ N) (d₁ d₂ d δ₁ δ₂ : ℤ)
    (hδ₁ : N * δ₁ = d₁ + s * d) (hδ₂ : N * δ₂ = d₂ + s * d) :
    d₁ • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.fst f f) rfl 1
        hpr₁ 0 P +
      d₂ • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.snd f f)
        pullback.condition.symm 1 hpr₂ 0 P + d • Δ' =
    δ₁ • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.fst f f) rfl 1
        hpr₁ 0 (N • P) +
      δ₂ • flatPullback (fieldChowSituation k) (pullback.fst f f ≫ f) f (pullback.snd f f)
        pullback.condition.symm 1 hpr₂ 0 (N • P) - d • B := by
  subst hB
  rw [map_zsmul, map_zsmul, smul_smul, smul_smul, mul_comm δ₁, mul_comm δ₂, hδ₁, hδ₂]
  module

end Faltings.BombieriVojta
