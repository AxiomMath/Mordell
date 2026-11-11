module

public import Mordell.Attr
public import Mordell.Jacobian.Autoduality.PhiTheta

/-!
# Autoduality: `φ_θ` is injective

Let `(C, P)` be a curve over a field `k` with a divisor of degree one, of genus `g ≥ 1`, let
`(J, ι)` be a Jacobian of `C`, `j = j_P` the Abel–Jacobi map, `Θ ⊆ J` the theta divisor and
`θ = cl(Θ) ∈ Pic(J)` its class. For an algebraically closed field `K ⊇ k`, the map
`φ_θ : J(K) → Pic(J_K)`, `a ↦ τ_a^* θ - θ`, is injective.

The proof is immediate from `Faltings.Jacobian.ι_app_pullback_phiMap_theta_eq_inv`: the
pull-back `j^* φ_θ(b)` along `j_K : C_K ⟶ J_K` is a degree-zero class which `ι(Spec K)` sends to
`-b`. So `φ_θ(a) = φ_θ(b)` gives `-a = -b`, hence `a = b`.

## Main results

* `Faltings.injective_phiMap_picardClass_thetaDivisor`: `φ_θ : J(K) → Pic(J_K)` is injective.

## Implementation notes

The class `θ` is the Picard class `Stacks.Divisors.picardClass D` of an effective Cartier
divisor `D` on `J` whose ideal sheaf is radical and whose support is
`Faltings.thetaDivisor X A hg j hj`; these two conditions determine `D` (it is the vanishing
ideal of `Θ`), so the statement is about `θ = cl(Θ)` and nothing else. The points of `J` over
`K` are the morphisms `Spec K ⟶ J` over `Spec k`; the source's case is `K = k̄`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Lemma 6.9 and Summary 6.11.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **Autoduality: `φ_θ` is injective** ([MilAV, III, 6.9 and 6.11]). Let `X = (C, P)` be a
curve over `k` with a divisor of degree one, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian of `C`
and `j = j_P` the Abel–Jacobi map. Let `D` be the reduced effective Cartier divisor on `J` with
support the theta divisor `Faltings.thetaDivisor X A hg j hj`, and `θ` its class in `Pic(J)`.
Then for every algebraically closed field `K ⊇ k`, the map
`φ_θ = Faltings.AbelianVariety.phiMap A.J θ : J(K) → Pic(J_K)` is injective. -/
@[faltings "lem_nt_phi_theta_injective"]
theorem injective_phiMap_picardClass_thetaDivisor (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    haveI := A.isAbelianVariety
    Function.Injective
      (AbelianVariety.phiMap (K := K) A.J (Stacks.Divisors.picardClass D)) := by
  have := A.isAbelianVariety
  have : IsReduced D.subscheme := by
    rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  intro a b hab
  obtain ⟨ha, ea⟩ := Jacobian.ι_app_pullback_phiMap_theta_eq_inv X A
    (fun T x y => A.map_add (op T) x y) hg j hj D hsupp K a
  obtain ⟨hb, eb⟩ := Jacobian.ι_app_pullback_phiMap_theta_eq_inv X A
    (fun T x y => A.map_add (op T) x y) hg j hj D hsupp K b
  simp only [hab] at ha ea
  exact inv_injective (ea.symm.trans eb)

end Faltings
