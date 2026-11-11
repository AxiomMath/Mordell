module

public import Mordell.NeronTate.Pairing.SelfHeight

/-!
# The Néron–Tate height of `θ⁻` in terms of the Néron norm

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one, of
genus `g ≥ 1`, `(J, ι)` a Jacobian of `C`, `θ = cl(Θ) ∈ Pic(J)` the class of the theta divisor
and `θ⁻ = [-1]^* θ`. For `x ∈ J(k̄)`,
`ĥ_{θ⁻}(x) = ½ |x|² - ½ ĥ_{θ - θ⁻}(x)`, where `|x|² = ⟨x, x⟩` is the Néron norm.

Indeed `ĥ_θ - ĥ_{θ⁻} = ĥ_{θ - θ⁻}` by additivity of the Néron–Tate height in the class, and
`ĥ_θ + ĥ_{θ⁻} = |x|²`; subtracting gives `2 ĥ_{θ⁻} = |x|² - ĥ_{θ - θ⁻}`.

## Main results

* `Faltings.neronTateHeight_pullbackInv_eq_half_neronPairing_sub`: the identity
  `ĥ_{θ⁻} x = ½ ⟨x, x⟩ - ½ ĥ_{θ - θ⁻} x`.

## Implementation notes

As in `Faltings.neronPairing`, heights live on the base change
`J_K = (Over.pullback (Spec K ⟶ Spec k)).obj J`, an abelian variety over `K`: a class
`c ∈ Pic(J)` enters as `1 ⊗ c_K ∈ ℚ ⊗ Pic(J_K)`, `c_K` its pull-back along the projection
`J_K ⟶ J`, and a Néron–Tate height of `c` is a function on the `K`-points of `J_K` that is a
Néron–Tate height of `1 ⊗ c_K` (`Faltings.IsNeronTateHeight`), evaluated at the section `(x, 1)`
of `J_K ⟶ Spec K` for `x ∈ J(K)`. The heights `ĥ_{θ⁻}` and `ĥ_{θ - θ⁻}` are functions
characterised by this predicate, universally quantified, rather than chosen terms; the
Néron–Tate height of a class is unique, so this is no restriction. The inversion `[-1]` of `J`
is `ι[J]`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, proof of Lemma 2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **The height of `θ⁻` via the Néron norm.** In the situation of `Faltings.neronPairing`, let
`θ = Stacks.Divisors.picardClass D` and `θ⁻ = [-1]^* θ`. If `f'` and `f''` are Néron–Tate
heights (`Faltings.IsNeronTateHeight`) of the classes of `θ⁻` and `θ - θ⁻` on the abelian
variety `J_K`, then for `x ∈ J(K)`, `f' (x, 1) = ½ ⟨x, x⟩ - ½ f'' (x, 1)`. -/
@[faltings "lem_nt_theta_minus_height"]
theorem neronTateHeight_pullbackInv_eq_half_neronPairing_sub [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let classK : A.J.left.picardGroup → ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      fun c ↦ (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) c
    let pt : Additive (Over.mk φK ⟶ A.J) → {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} :=
      fun z ↦ ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
    let θ := Stacks.Divisors.picardClass D
    let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
    ∀ f' f'' : {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} → ℝ,
      IsNeronTateHeight JK (classK θm) f' → IsNeronTateHeight JK (classK (θ - θm)) f'' → ∀ x,
        f' (pt x) = 1 / 2 * neronPairing X A hg j hj D hrad hsupp K x x - 1 / 2 * f'' (pt x) := by
  haveI := A.isAbelianVariety
  letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  intro φK JK classK pt θ θm f' f'' hf' hf'' x
  obtain ⟨f, hf⟩ := exists_isNeronTateHeight_of_isAlgebraic JK (classK θ)
  have hadd : classK (θ + θm) = (1 : ℚ) • classK θ + (1 : ℚ) • classK θm := by
    simp only [classK, one_smul, map_add, TensorProduct.tmul_add]
  have hsub : classK (θ - θm) = (1 : ℚ) • classK θ + (-1 : ℚ) • classK θm := by
    simp only [classK]
    rw [map_sub, TensorProduct.tmul_sub, neg_one_smul, one_smul, sub_eq_add_neg]
  have h1 := (neronPairing_self_eq_add_and_add_eq X A hg j hj D hrad hsupp K f f' _ hf hf'
    (hadd ▸ hf.smul_add_smul hf' 1 1) x).1
  have h2 := congrFun (hf''.unique (hsub ▸ hf.smul_add_smul hf' 1 (-1))) (pt x)
  simp only [Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul] at h2
  rw [h1, h2]
  ring

end Faltings
