module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup

/-!
# The class of a divisor

Let `X` be a smooth projective variety over a field `k` and `D` a Weil divisor on `X`. The
local rings of `X` are regular, hence unique factorization domains, so every prime divisor of
`X` is an effective Cartier divisor and `D` defines an invertible sheaf `𝒪_X(D)`. Its class
`cl(D) = [𝒪_X(D)]` in the Picard group `Pic(X)` is the *class of `D`*.

## Main definitions

* `Faltings.picardClassOfWeilDivisor`: the class `cl(D) = [𝒪_X(D)] ∈ Pic(X)` of a Weil
  divisor `D`.

## Implementation notes

A Weil divisor `D` is written `D = D⁺ - D⁻` with `D⁺` and `D⁻ = (-D)⁺` effective. On a scheme
with factorial local rings the ideal sheaf `AlgebraicGeometry.positiveWeilIdeal D` of `D⁺`
(the locally finite product of the powers `𝓘_Z ^ D_Z` over the prime divisors with `D_Z > 0`)
is an effective Cartier divisor, and `𝒪_X(D⁺)` is its invertible sheaf. Then `𝒪_X(D)` is
`𝒪_X(D⁺) ⊗ 𝒪_X(D⁻)⁻¹`, so its class is `[𝒪_X(D⁺)] - [𝒪_X(D⁻)]`, which is the definition
used. Factoriality of the local rings is supplied by smoothness over `k`
(`AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_smooth`). The base field is an arbitrary
field `k`; the case of the source is `k = \bar{ℚ}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.6][hartshorne1977]
* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- The class `cl(D) = [𝒪_X(D)]` in `Pic(X)` of a Weil divisor `D` on a smooth projective
variety `X` over a field `k`, computed as `[𝒪_X(D⁺)] - [𝒪_X(D⁻)]` where `D = D⁺ - D⁻` with
`D⁺, D⁻` effective. -/
@[expose, faltings "def_ht_class_of_divisor"]
public def picardClassOfWeilDivisor {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [Smooth f] (D : WeilDivisor X) : X.picardGroup :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
    positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) D
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal (-D)) :=
    positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) (-D)
  X.picardClass (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal D))
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf _) -
    X.picardClass (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal (-D)))
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf _)

end Faltings


/-!
# The complete linear system of a divisor

Let `X` be a smooth projective variety over a field `k`, with function field `K(X)`, and let `A`
be a Weil divisor on `X`. The invertible sheaf `𝒪_X(A)` is the subsheaf of the constant sheaf
`K(X)` whose sections over `U` are the rational functions `f` with `f = 0` or
`(div(f) + A)|_U ≥ 0`. So a nonzero global section `s ∈ H⁰(X, 𝒪_X(A))` is a nonzero rational
function `f` with `div(f) + A ≥ 0`, and the divisor of zeros of `s`, viewed as a section of
`𝒪_X(A)`, is `div(s) = div(f) + A`. The *complete linear system* `|A|` is the set of the
divisors `div(s)` for nonzero `s ∈ H⁰(X, 𝒪_X(A))`. Equivalently, it is the set of effective
divisors linearly equivalent to `A`.

## Main definitions

* `Faltings.completeLinearSystemOfWeilDivisor`: the complete linear system `|A|` of a Weil
  divisor `A`, as a set of Weil divisors.

## Implementation notes

The global sections of `𝒪_X(A)` are taken in the model `𝒪_X(A) ⊆ K(X)` above, where
`H⁰(X, 𝒪_X(A)) = {f ∈ K(X) | f = 0 ∨ div(f) + A ≥ 0}` and a nonzero section `f` has divisor
`div(f) + A`. So `|A|` is written as the set of divisors `div(f) + A`, for `f` an invertible
rational function (`AlgebraicGeometry.principalDivisor`) with `div(f) + A ≥ 0`. The order on
Weil divisors is the coefficientwise one, so `0 ≤ D` says that `D` is effective. When `A` is
an effective Cartier divisor, `Stacks.Divisors.completeLinearSystem` is the corresponding set
of effective Cartier divisors linearly equivalent to `A`; it is not used here because a
divisor `A` need not be effective. The base field is an arbitrary field `k`; the source takes
`k = \bar{ℚ}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.7][hartshorne1977]
* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Faltings

/-- The complete linear system `|A|` of a Weil divisor `A` on a smooth projective variety `X`
over a field `k`: the divisors `div(s) = div(f) + A` of the nonzero global sections `s = f` of
`𝒪_X(A) ⊆ K(X)`, where `f` ranges over the nonzero rational functions with
`div(f) + A ≥ 0`. -/
@[expose, faltings "def_ht_complete_linear_system"]
public def completeLinearSystemOfWeilDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f] (A : WeilDivisor X) :
    Set (WeilDivisor X) :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  {D | ∃ g : (Stacks.Chow.rationalFunctions X)ˣ, principalDivisor X g + A = D ∧ 0 ≤ D}

end Faltings


/-!
# The base locus of a complete linear system

Let `X` be a smooth projective variety over a field `k` and `A` a Weil divisor on `X`. The
*base locus* of `|A|` is the set of points `p ∈ X(k)` at which every global section
`s ∈ H⁰(X, 𝒪_X(A))` vanishes. The zero section vanishes everywhere, and a nonzero section `s`
vanishes at `p` exactly when `p` lies on the support of its divisor of zeros `div(s) ∈ |A|`,
that is, on a prime divisor `Z` with positive coefficient in `div(s)`. So the base locus is the
set of `k`-points lying on the support of every member of `|A|`; in particular it is all of
`X(k)` when `|A|` is empty.

## Main definitions

* `Faltings.baseLocusOfWeilDivisor`: the base locus of `|A|`, as a set of `k`-points of `X`.

## Implementation notes

A `k`-point of `f : X ⟶ Spec k` is a morphism `p : Spec k ⟶ X` with `p ≫ f = 𝟙`, and its
underlying point of `X` is the image of the closed point of `Spec k`. Sections of `𝒪_X(A)`
are taken in the model `𝒪_X(A) ⊆ K(X)` of `Faltings.completeLinearSystemOfWeilDivisor`, so
the vanishing of a nonzero section `s` at `p` is the membership of `p` in the support of
`div(s)`. The base field is an arbitrary field `k`; the source takes `k = AlgebraicClosure ℚ`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.7][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory

namespace Faltings

/-- The base locus of the complete linear system `|A|` of a Weil divisor `A` on a smooth
projective variety `X` over a field `k`: the `k`-points `p` of `X` at which every global
section of `𝒪_X(A)` vanishes, i.e. which lie, for every `D ∈ |A|`, on some prime divisor `Z`
with positive coefficient in `D`. -/
@[expose, faltings "def_ht_base_locus"]
public def baseLocusOfWeilDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f] (A : WeilDivisor X) :
    Set (Spec (.of k) ⟶ X) :=
  {p | p ≫ f = 𝟙 _ ∧ ∀ D ∈ completeLinearSystemOfWeilDivisor f A,
    ∃ Z : PrimeDivisor X, 0 < (D : PrimeDivisor X → ℤ) Z ∧
      p.base (IsLocalRing.closedPoint k) ∈ Z.support}

end Faltings
