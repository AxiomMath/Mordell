module

public import Mathlib
public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.NeronTate.Pairing.Bilinear
public import Mordell.NeronTate.Pairing.Nonneg

/-!
# Cauchy–Schwarz for the Néron form

In the situation of `Faltings.neronPairing`, write `|x| = √⟨x, x⟩` for the Néron norm of a
point `x ∈ J(K)` (with `√t = 0` for `t < 0`, which is `Real.sqrt`). The Néron form is symmetric,
biadditive and positive semidefinite, so it satisfies the Cauchy–Schwarz inequality
`|⟨x, y⟩| ≤ |x| |y|`.

The proof: for integers `m, n`, `0 ≤ ⟨m x + n y, m x + n y⟩ = m² ⟨x, x⟩ + 2 m n ⟨x, y⟩ + n² ⟨y, y⟩`
(`Faltings.exists_addMonoidHom_eq_neronPairing`, `Faltings.neronPairing_self_nonneg`), so the
real quadratic `t ↦ ⟨x, x⟩ t² + 2 ⟨x, y⟩ t + ⟨y, y⟩` is non-negative on `ℚ`, hence on `ℝ` by
density, and its discriminant is non-positive.

## Main results

* `Faltings.abs_neronPairing_le_sqrt_mul_sqrt`: `|⟨x, y⟩| ≤ √⟨x, x⟩ * √⟨y, y⟩`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- Cauchy–Schwarz for a positive semidefinite symmetric biadditive real form on an additive
group: `B x y ^ 2 ≤ B x x * B y y`. -/
private theorem sq_le_mul_of_biadditive {G : Type*} [AddGroup G] (B : G →+ G →+ ℝ)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x) (x y : G) :
    B x y ^ 2 ≤ B x x * B y y := by
  set a := B x x
  set b := B y y
  set c := B x y
  have hint : ∀ m n : ℤ, 0 ≤ m ^ 2 * a + 2 * m * n * c + n ^ 2 * b := by
    intro m n
    have h := hpos (m • x + n • y)
    simp only [map_add, AddMonoidHom.add_apply, map_zsmul, AddMonoidHom.zsmul_apply,
      zsmul_eq_mul] at h
    rw [hB y x] at h
    nlinarith [h]
  have hall : ∀ t : ℝ, 0 ≤ a * (t * t) + 2 * c * t + b := by
    intro t
    refine Rat.denseRange_cast.induction_on (p := fun t : ℝ => 0 ≤ a * (t * t) + 2 * c * t + b) t
      (isClosed_le continuous_const (by fun_prop)) ?_
    intro q
    have hn : (0 : ℝ) < q.den := by exact_mod_cast q.pos
    have h := hint q.num q.den
    have hq : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    simp only [Int.cast_natCast] at h
    rw [hq]
    have : a * ((q.num / q.den : ℝ) * (q.num / q.den)) + 2 * c * (q.num / q.den) + b =
        ((q.num : ℝ) ^ 2 * a + 2 * q.num * q.den * c + (q.den : ℝ) ^ 2 * b) / (q.den : ℝ) ^ 2 := by
      field_simp
    rw [this]
    positivity
  have hd := discrim_le_zero hall
  unfold discrim at hd
  nlinarith [hd]

/-- **Cauchy–Schwarz for the Néron form.** In the situation of `Faltings.neronPairing`,
`|⟨x, y⟩| ≤ √⟨x, x⟩ * √⟨y, y⟩` for all `x, y ∈ J(K)`. -/
@[faltings "lem_nt_neron_cauchy_schwarz"]
theorem abs_neronPairing_le_sqrt_mul_sqrt [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (x y : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)) :
    |neronPairing X A hg j hj D hrad hsupp K x y| ≤
      √(neronPairing X A hg j hj D hrad hsupp K x x) *
        √(neronPairing X A hg j hj D hrad hsupp K y y) :=
          by
  haveI := A.isAbelianVariety
  letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  obtain ⟨B, hB, hBeq⟩ := exists_addMonoidHom_eq_neronPairing X A hg j hj D hrad hsupp K
  have hpos : ∀ z, 0 ≤ B z z := fun z => by
    rw [← hBeq]; exact neronPairing_self_nonneg X A hg j hj D hrad hsupp K z
  simp only [hBeq]
  rw [← Real.sqrt_mul (hpos x)]
  exact Real.abs_le_sqrt (sq_le_mul_of_biadditive B hB hpos x y)

end Faltings
