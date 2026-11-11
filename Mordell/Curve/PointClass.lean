module
public import Mordell.Curve.DegreeOneDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom

/-!
# The degree of the class of a closed point

Let `f : C ⟶ Spec K` be a smooth proper curve over a field `K`. Each closed point `x` of `C` is an
effective Cartier divisor, with class `[𝒪_C(x)] ∈ Pic(C)` of degree `[κ(x) : K]`; so a divisor
`D = ∑ nₓ x` has class `∑ nₓ [𝒪_C(x)]` of degree `deg D = ∑ nₓ [κ(x) : K]`. For a curve with a
divisor `P` of degree one this gives the class `[𝒪_C(P)]`, of degree one.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.classP`: the class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`.

## Main results

* `Faltings.degree_pointIdeal_of_isCurve`: `deg 𝒪_C(x) = [κ(x) : K]` for a closed point `x`.
* `Faltings.degree_divisorClass`: `deg (∑ nₓ [𝒪_C(x)]) = ∑ nₓ [κ(x) : K]`.
* `Faltings.CurveWithDegreeOneDivisor.invertibleCurveDegreeHom_classP`: `deg 𝒪_C(P) = 1`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- `deg 𝒪(x) = [κ(x) : K]` for a closed point `x` of a curve over a field `K`. -/
public lemma degree_pointIdeal_of_isCurve {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [Smooth f] [IsProper f] [IsCurve K f] (hdimC : topologicalKrullDim C ≤ 1)
    (x : {x : C // IsClosed ({x} : Set C)}) :
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
    invertibleCurveDegreeHom K f hdimC
      (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) = f.residueDegree x.1 := by
  have := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
  rw [invertibleCurveDegreeHom_picardClass K f hdimC
    (Stacks.Divisors.invertibleSheaf' _) (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)]
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x.1}, x.2⟩ : TopologicalSpace.Closeds C)) :=
    ‹Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Zeta.pointIdeal x)›
  refine
    (invertibleCurveDegree_modulesInvertibleSheaf_vanishingIdeal_singleton f hdimC x.2).trans ?_
  rw [Stacks.Chow.residueDegree_eq_finrank_residueField]
  rfl

/-- `deg 𝒪(D) = deg D = ∑ nₓ [κ(x) : K]` for a divisor `D = ∑ nₓ x` on a curve over `K`. -/
public lemma degree_divisorClass {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [Smooth f] [IsProper f] [IsCurve K f] (hdimC : topologicalKrullDim C ≤ 1)
    (D : {x : C // IsClosed ({x} : Set C)} →₀ ℤ) :
    invertibleCurveDegreeHom K f hdimC (D.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) =
      D.sum fun x n => n * (f.residueDegree x.1 : ℤ) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_zsmul, degree_pointIdeal_of_isCurve f hdimC, smul_eq_mul]

namespace CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)` of the degree-one divisor `P = ∑ nₓ x`,
each closed point of the smooth curve `C` being an effective Cartier divisor. -/
@[expose] public noncomputable def classP (X : CurveWithDegreeOneDivisor k) :
    Stacks.Picard.ofScheme X.C :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  X.P.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)

/-- `deg 𝒪_C(x) = [κ(x) : k]` for a closed point `x` of `C`. -/
public lemma invertibleCurveDegreeHom_picardClass_pointIdeal (X : CurveWithDegreeOneDivisor k)
    (hdim : topologicalKrullDim X.C ≤ 1) (x : {x : X.C // IsClosed ({x} : Set X.C)}) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    invertibleCurveDegreeHom k X.f hdim
      (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) = X.f.residueDegree x.1 :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  degree_pointIdeal_of_isCurve X.f hdim x

/-- `deg 𝒪_C(P) = deg P = 1`. -/
public lemma invertibleCurveDegreeHom_classP (X : CurveWithDegreeOneDivisor k)
    (hdim : topologicalKrullDim X.C ≤ 1) : invertibleCurveDegreeHom k X.f hdim X.classP = 1 := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  rw [← X.degree_P, classP, degree_divisorClass]

end CurveWithDegreeOneDivisor

end Faltings
