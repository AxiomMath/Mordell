module
public import Mordell.Jacobian.Theta.Basic

/-!
# The class `δ` on `J × J`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C`, `j = j_P` the Abel–Jacobi map and `Θ = Θ_P ⊆ J` the theta
divisor, with class `θ = cl(Θ) = [𝒪_J(Θ)] ∈ Pic(J)`. On `J × J` write `s₁, s₂` for the two
projections and `s₁₂(x, y) = x + y` for the group law. The class `δ ∈ Pic(J × J)` is
`δ = s₁^* θ + s₂^* θ - s₁₂^* θ`.

## Main definitions

* `Faltings.deltaClass X A hg j hj D hrad hsupp`: the class `δ = s₁^* θ + s₂^* θ - s₁₂^* θ` in
  `Pic(J ×_k J)`.

## Implementation notes

The class `θ` is the class `Stacks.Divisors.picardClass D` of the reduced effective Cartier
divisor `D` on `J` whose support is `Faltings.thetaDivisor`; `Θ` is a prime divisor on the
smooth variety `J`, so such a `D` exists and is unique, and it is taken as an argument with
the properties that pin it (`D.radical = D`, support `Θ`), as in `Faltings.neronPairing`.

The product `J × J` is the monoidal product `J ⊗ J` in schemes over `Spec k`, whose underlying
scheme is `J ×_k J`; `s₁, s₂` are the cartesian projections and `s₁₂` is the multiplication
`μ` of the group object `J`. The Picard group is written additively.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 6.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **The class `δ`** on `J × J`: for a curve `X = (C, P)` with a divisor of degree one, of
genus `g ≥ 1`, a Jacobian `A = (J, ι)` and the Abel–Jacobi map `j = j_P`, with
`θ = cl(Θ) ∈ Pic(J)` the class of the reduced effective Cartier divisor `D` whose support is the
theta divisor `Θ = Faltings.thetaDivisor X A hg j hj`,
`δ = s₁^* θ + s₂^* θ - s₁₂^* θ ∈ Pic(J × J)`, where `s₁, s₂` are the projections and `s₁₂` is
the group law. -/
@[expose, faltings "def_nt_delta_class"]
public noncomputable def deltaClass (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (_hrad : D.radical = D)
    (_hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj) :
    Stacks.Picard.ofScheme (A.J ⊗ A.J).left :=
  let θ := Stacks.Divisors.picardClass D
  Stacks.Picard.schemePullbackClassHom (fst A.J A.J).left θ +
    Stacks.Picard.schemePullbackClassHom (snd A.J A.J).left θ -
    Stacks.Picard.schemePullbackClassHom μ[A.J].left θ

end Faltings
