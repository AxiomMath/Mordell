module

public import Mathlib
public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.NeronTate.Existence
public import Mordell.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# The Néron pairing is symmetric and biadditive

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one, of
genus `g ≥ 1`, `(J, ι)` a Jacobian of `C` and `θ = cl(Θ)` the class of the theta divisor. The
Néron pairing `⟨x, y⟩ = ĥ_θ (x + y) - ĥ_θ x - ĥ_θ y` on `J(k̄)` is the polar form of the
Néron–Tate height `ĥ_θ = ½ b(x, x) + ℓ(x)`, `b` symmetric biadditive and `ℓ` additive, hence
equals `b`, a symmetric biadditive form.

## Main results

* `Faltings.exists_addMonoidHom_eq_neronPairing`: `Faltings.neronPairing` is a symmetric
  biadditive form, i.e. it is the curried function of a symmetric `B : J(K) →+ J(K) →+ ℝ`.

## Implementation notes

Biadditivity is stated in bundled form, as the existence of `B : J(K) →+ J(K) →+ ℝ` with
`B x y = B y x` and `Faltings.neronPairing … x y = B x y`, the shape of the form in
`Faltings.IsNeronTateHeight`; the bundled form gives `map_add`, `map_sub`, `map_zsmul` and
`map_sum` in each variable. The group law on `J(K)` is the one used by
`Faltings.neronPairing`, commutative by
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`.

The Néron–Tate height lives on the `K`-points of the base change `J_K`, and a point
`x : Spec K ⟶ J` over `k` is read there as the section `(x, 1)`
(`Faltings.GroupScheme.toBaseChange`). This identification is multiplicative, so the form `b` of
`ĥ_θ` on `J_K(K)` restricts to a biadditive form on `J(K)`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

/-- The polar form of `½ b(x, x) + ℓ(x)` along an additive map is `b`, for `b` symmetric. -/
private lemma polar_comp_eq {G H : Type*} [AddCommGroup G] [AddZeroClass H]
    (b : H →+ H →+ ℝ) (hb : ∀ x y, b x y = b y x) (ℓ : H →+ ℝ) (q : G →+ H) (g : G → ℝ)
    (hg : ∀ z, g z = b (q z) (q z) / 2 + ℓ (q z)) (x y : G) :
    QuadraticMap.polar g x y = b (q x) (q y) := by
  simp only [QuadraticMap.polar, hg, map_add, AddMonoidHom.add_apply, hb (q y) (q x)]
  ring

variable {k : Type u} [Field k]

/-- **The Néron pairing is symmetric and biadditive.** In the situation of
`Faltings.neronPairing`, the Néron pairing on `J(K)` is the curried function of a symmetric
biadditive form `B : J(K) →+ J(K) →+ ℝ`. -/
@[faltings "lem_nt_neron_pairing_properties"]
theorem exists_addMonoidHom_eq_neronPairing [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
    ∃ B : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) →+
        Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) →+ ℝ,
      (∀ x y, B x y = B y x) ∧
      ∀ x y, neronPairing X A hg j hj D hrad hsupp K x y = B x y := by
  have := A.isAbelianVariety
  let : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  obtain ⟨f, hf⟩ := exists_isNeronTateHeight A.J K
    ((1 : ℚ) ⊗ₜ Stacks.Divisors.picardClass D)
  rw [LinearMap.baseChange_tmul] at hf
  obtain ⟨-, b, hb, ℓ, hbℓ⟩ := Classical.epsilon_spec ⟨f, hf⟩
  let q := (GroupScheme.toBaseChangeHom
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) A.J).toAdditive
  refine ⟨AddMonoidHom.mk' (fun x ↦ (b (q x)).comp q) (fun x y ↦ by ext; simp),
    fun x y ↦ hb _ _, fun x y ↦ ?_⟩
  unfold neronPairing
  refine polar_comp_eq b hb ℓ q _ (fun z ↦ ?_) x y
  exact hbℓ _

end Faltings
