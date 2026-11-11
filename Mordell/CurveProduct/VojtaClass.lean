module

public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Curve.PointClass
public import Mordell.CurveProduct.Diagonal
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower

/-!
# Divisor classes on `C × C`

Let `(C, P)` be a curve over a field `k` with a divisor `P = ∑ nₓ x` of degree one, let
`X = C ×_k C` and let `pr₁, pr₂ : X ⟶ C` be the projections. The divisors `P × C = pr₁^* P`
and `C × P = pr₂^* P` have classes `pr₁^*[𝒪_C(P)]` and `pr₂^*[𝒪_C(P)]` in `Pic(X)`. Let
`Δ ⊆ X` be the diagonal, the image of the closed immersion `Δ_{C/k}`, an effective Cartier
divisor, and put `Δ' = Δ - P × C - C × P`, so that
`[𝒪_X(Δ')] = [𝒪_X(Δ)] - pr₁^*[𝒪_C(P)] - pr₂^*[𝒪_C(P)]`. For integers `d₁, d₂, d` the divisor
`V = d₁ (P × C) + d₂ (C × P) + d Δ'` has class
`[𝒪_X(V)] = d₁ pr₁^*[𝒪_C(P)] + d₂ pr₂^*[𝒪_C(P)] + d [𝒪_X(Δ')]`.
When `d₁, d₂, d > 0` and `g d² < d₁ d₂ < g² d²`, with `g` the genus of `C`, this is the class
of Bombieri's Vojta divisor.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.vojtaClass`: the class `[𝒪_X(V)] ∈ Pic(C ×_k C)` of
  `V = d₁ (P × C) + d₂ (C × P) + d Δ'`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.vojtaClass_eq`: `vojtaClass` written with
  `Faltings.CurveWithDegreeOneDivisor.classP`.
* `Faltings.CurveWithDegreeOneDivisor.vojtaClass_one_zero_zero`,
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass_zero_one_zero`,
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass_zero_zero_one`,
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass_one_one_one`: `P × C`, `C × P` and `Δ'` as
  pulled-back classes and their combination, and `Δ` as the class of the diagonal.
* `Faltings.CurveWithDegreeOneDivisor.vojtaClass_eq_coords`: `vojtaClass` in terms of its
  values at `(1,0,0)`, `(0,1,0)` and `(1,1,1)`.

## Implementation notes

Divisors on `X` enter only through their classes in the Picard group
`Stacks.Picard.ofScheme X`, written additively, so the tensor products and tensor powers of
the source are sums and integer multiples. The class `[𝒪_C(P)]` is
`∑ nₓ [𝒪_C(x)]`, with `𝒪_C(x)` the invertible sheaf of the effective Cartier divisor of the
closed point `x`; the pull-backs are `Stacks.Picard.schemePullbackClassHom` along
`pullback.fst` and `pullback.snd`. The diagonal `Δ` is the closed subscheme cut out by the
kernel of `pullback.diagonal X.f`, which is an effective Cartier divisor by
`Faltings.isEffectiveCartierDivisor_ker_diagonal`.

The individual classes are the values on the coordinate triples:
`P × C` is `vojtaClass 1 0 0`, `C × P` is `vojtaClass 0 1 0`, `Δ'` is `vojtaClass 0 0 1`, and
`Δ` is `vojtaClass 1 1 1`. The canonical sheaf `K_X = ⋀² Ω_{X/k}` is not a divisor class
introduced here; it is the second exterior power of the sheaf of relative differentials of
`X` over `k`, as the library forms it.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- The coordinate identities `V(1,0,0) = a`, `V(0,1,0) = b`, `V(1,1,1) = c` of
`V(d₁, d₂, d) = d₁ a + d₂ b + d (c - a - b)`, in an arbitrary abelian group. -/
lemma coord_identities {G : Type*} [AddCommGroup G] (a b c : G) :
    ((1 : ℤ) • a + (0 : ℤ) • b + (0 : ℤ) • (c - a - b) = a) ∧
      ((0 : ℤ) • a + (1 : ℤ) • b + (0 : ℤ) • (c - a - b) = b) ∧
      ((1 : ℤ) • a + (1 : ℤ) • b + (1 : ℤ) • (c - a - b) = c) :=
  ⟨by simp, by simp, by simp⟩

/-- The coordinate identity `V(0,0,1) = c` of `V(d₁, d₂, d) = d₁ a + d₂ b + d c`. -/
private lemma coord_identity_zero_zero_one {G : Type*} [AddCommGroup G] (a b c : G) :
    (0 : ℤ) • a + (0 : ℤ) • b + (1 : ℤ) • c = c := by
  simp

end Faltings

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The class `[𝒪_X(V)] ∈ Pic(C ×_k C)` of the divisor `V = d₁ (P × C) + d₂ (C × P) + d Δ'` on
`X = C ×_k C`, where `P × C = pr₁^* P`, `C × P = pr₂^* P`, `Δ` is the diagonal and
`Δ' = Δ - P × C - C × P`:
`d₁ pr₁^*[𝒪_C(P)] + d₂ pr₂^*[𝒪_C(P)] + d ([𝒪_X(Δ)] - pr₁^*[𝒪_C(P)] - pr₂^*[𝒪_C(P)])`. -/
@[faltings "def_nt_divisors_c_times_c_classes"]
noncomputable def vojtaClass (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ) :
    Stacks.Picard.ofScheme (pullback X.f X.f) :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  /- The class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`. -/
  let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
  /- `[𝒪_X(P × C)]` and `[𝒪_X(C × P)]`. -/
  let PC := Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) classP
  let CP := Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) classP
  /- `[𝒪_X(Δ')] = [𝒪_X(Δ)] - [𝒪_X(P × C)] - [𝒪_X(C × P)]`. -/
  let Δ' := Stacks.Divisors.picardClass (pullback.diagonal X.f).ker - PC - CP
  d₁ • PC + d₂ • CP + d • Δ'

/-- `V(d₁, d₂, d) = d₁ (P × C) + d₂ (C × P) + d (Δ - P × C - C × P)`, written with
`CurveWithDegreeOneDivisor.classP`. -/
lemma vojtaClass_eq (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI := (isEffectiveCartierDivisor_ker_diagonal k X.f).1
    X.vojtaClass d₁ d₂ d =
      d₁ • Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) X.classP +
      d₂ • Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) X.classP +
      d • (Stacks.Divisors.picardClass (pullback.diagonal X.f).ker -
        Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) X.classP -
        Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) X.classP) :=
  rfl

/-- `V(1, 0, 0) = P × C`. -/
lemma vojtaClass_one_zero_zero (X : CurveWithDegreeOneDivisor k) :
    X.vojtaClass 1 0 0 = Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) X.classP :=
  (vojtaClass_eq X 1 0 0).trans (coord_identities _ _ _).1

/-- `V(0, 1, 0) = C × P`. -/
lemma vojtaClass_zero_one_zero (X : CurveWithDegreeOneDivisor k) :
    X.vojtaClass 0 1 0 = Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) X.classP :=
  (vojtaClass_eq X 0 1 0).trans (coord_identities _ _ _).2.1

/-- `V(0, 0, 1) = Δ' = Δ - P × C - C × P`. -/
lemma vojtaClass_zero_zero_one (X : CurveWithDegreeOneDivisor k) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI := (isEffectiveCartierDivisor_ker_diagonal k X.f).1
    X.vojtaClass 0 0 1 = Stacks.Divisors.picardClass (pullback.diagonal X.f).ker -
      Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) X.classP -
      Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) X.classP :=
  (vojtaClass_eq X 0 0 1).trans (coord_identity_zero_zero_one _ _ _)

/-- `V(1, 1, 1) = Δ`. -/
lemma vojtaClass_one_one_one (X : CurveWithDegreeOneDivisor k) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI := (isEffectiveCartierDivisor_ker_diagonal k X.f).1
    X.vojtaClass 1 1 1 = Stacks.Divisors.picardClass (pullback.diagonal X.f).ker :=
  (vojtaClass_eq X 1 1 1).trans (coord_identities _ _ _).2.2

/-- The class of `V` in terms of `P × C = V(1, 0, 0)`, `C × P = V(0, 1, 0)` and
`Δ = V(1, 1, 1)`. -/
lemma vojtaClass_eq_coords (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ) :
    X.vojtaClass d₁ d₂ d = d₁ • X.vojtaClass 1 0 0 + d₂ • X.vojtaClass 0 1 0 +
      d • (X.vojtaClass 1 1 1 - X.vojtaClass 1 0 0 - X.vojtaClass 0 1 0) := by
  rw [vojtaClass_one_zero_zero, vojtaClass_zero_one_zero, vojtaClass_one_one_one]
  exact vojtaClass_eq X d₁ d₂ d

end Faltings.CurveWithDegreeOneDivisor
