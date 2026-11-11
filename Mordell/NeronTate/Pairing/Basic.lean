module

public import Mordell.Jacobian.Theta.Basic
public import Mordell.NeronTate.Basic
public import Mordell.Height.Class.Basic

/-!
# The Néron pairing on a Jacobian

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one,
of genus `g ≥ 1`, `(J, ι)` a Jacobian of `C`, `Θ ⊆ J` the theta divisor and
`θ = cl(Θ) ∈ Pic(J)` its class. The *Néron form* on `J` is
`⟨x, y⟩ = ĥ_θ (x + y) - ĥ_θ x - ĥ_θ y` for `x, y ∈ J(k̄)`,
where `ĥ_θ : J(k̄) → ℝ` is the Néron–Tate height of `θ`.

## Main definitions

* `Faltings.neronPairing`: the Néron pairing `⟨x, y⟩` on `J(K)`, `K` an algebraic closure of
  `k`, i.e. `QuadraticMap.polar ĥ_θ`.

## Implementation notes

A point of `J(K)` is a morphism `Spec K ⟶ J` over `Spec k`; these form a group under the group
law of `J` (`CategoryTheory.GrpObj.Hom.group`), written additively through `Additive`. This
group is commutative because `J` is proper and geometrically integral
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`).

The class `θ` is the class `Stacks.Divisors.picardClass D` of the reduced effective Cartier
divisor `D` on `J` whose support is `Faltings.thetaDivisor`; `Θ` is a prime divisor on the
smooth variety `J`, so such a `D` exists and is unique, and it is taken as an argument with
the properties that pin it.

Néron–Tate heights live on the base change `J_K = (Over.pullback (Spec K ⟶ Spec k)).obj J`,
an abelian variety over `K` (`AlgebraicGeometry.isAbelianVariety_pullbackObj`, with the group
law `AlgebraicGeometry.grpObjPullbackObj`), and `K` is algebraic over `ℚ` through `k`. The
class of `θ` on `J_K` is `1 ⊗ θ_K ∈ ℚ ⊗ Pic(J_K)`, `θ_K` the pull-back of `θ` along the
projection `J_K ⟶ J`, and a point `x : Spec K ⟶ J` over `k` is the section `(x, 1)` of
`J_K ⟶ Spec K`. The Néron–Tate height `ĥ_θ` is a function on the `K`-points of `J_K` that is
a Néron–Tate height of `1 ⊗ θ_K` (`Faltings.IsNeronTateHeight`), chosen by
`Classical.epsilon`; it is unique, since two heights of a class differ by a bounded function
and a bounded quadratic-plus-linear function vanishes. The pairing is the polar
`QuadraticMap.polar` of `ĥ_θ` read on `J(K)` through `x ↦ (x, 1)`, curried as Mathlib states
it.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **The Néron pairing** on the Jacobian. Let `k` be a number field, `X = (C, P)` a curve over
`k` with a divisor of degree one, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian, `j = j_P`, and
`θ = cl(Θ)` the class of the reduced effective Cartier divisor `D` with support the theta
divisor. For `K` an algebraic closure of `k`, the Néron form on `J(K)` is
`⟨x, y⟩ = ĥ_θ (x + y) - ĥ_θ x - ĥ_θ y`, where `ĥ_θ` is the Néron–Tate height of the class of
`θ` on the abelian variety `J_K`. -/
@[faltings "def_nt_neron_pairing"]
noncomputable def neronPairing [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (_hrad : D.radical = D)
    (_hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (x y : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)) : ℝ :=
  haveI := A.isAbelianVariety
  letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
  let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
    (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)
      (Stacks.Divisors.picardClass D)
  let pt : Additive (Over.mk φK ⟶ A.J) → {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} :=
    fun z ↦ ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
  QuadraticMap.polar ((Classical.epsilon fun f ↦ IsNeronTateHeight JK θK f) ∘ pt) x y

end Faltings
