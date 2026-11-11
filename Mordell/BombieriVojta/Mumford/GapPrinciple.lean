module

public import Mordell.BombieriVojta.Mumford.Main

/-!
# Mumford's gap principle

Let `k` be a number field, `(C, P)` a curve over `k` with a divisor `P` of degree one, of genus
`g ≥ 2`, `(J, ι)` a Jacobian of `C`, `j = j_P : C → J` the Abel–Jacobi map and `⟨x, y⟩` the
Néron pairing on `J(k̄)`. For `z, w ∈ C(k̄)` write `⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`.
The gap principle says that two distinct points of large norm in a narrow cone have norms far
apart: there is a constant `c ≥ 1` such that for all `z ≠ w` in `C(k̄)` with `c ≤ |z| ≤ |w|` and
`⟨z, w⟩ > (3/4) |z| |w|`, one has `|w| > 2 |z|`.

It follows from Mumford's theorem `Faltings.exists_pos_neronPairing_ge_of_ne`,
`(|z|² + |w|²) / 2g - ⟨z, w⟩ ≥ -c₃ (1 + |z| + |w|)` off the diagonal, together with `g ≥ 2`:
one may take `c = max 1 (16 c₃)`. Indeed, otherwise `t = |w| / |z| ∈ [1, 2]`, and
`-c₃ (1 + |z| + |w|) < |z|² (t² - 3t + 1) / 4 ≤ -|z|² / 4`, forcing `|z| < 16 c₃`.

## Main results

* `Faltings.exists_two_mul_neronNorm_lt_of_ne`: Mumford's gap principle.

## Implementation notes

A point `z ∈ C(k̄)` is a morphism `Spec k̄ ⟶ C` over `Spec k`, and `j z` is the composite
`z ≫ j`, a point of `J(k̄)`; the pairing is `Faltings.neronPairing` evaluated at `j z` and
`j w`. The class `θ` enters through the reduced effective Cartier divisor `D` with support
`Faltings.thetaDivisor`, as in `Faltings.neronPairing`. The norm is `Real.sqrt ⟨z, z⟩`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 4, p. 619, and
  Section 10, p. 639
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- The real inequality behind the gap principle: if `1 ≤ a ≤ b ≤ 2a`, `g ≥ 2`,
`p > (3/4) a b` and `-c (1 + a + b) ≤ a² / 2g + b² / 2g - p`, then `a < 16 c`. -/
private lemma lt_sixteen_mul_of_le_two_mul {a b c g p : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * a) (hg : 2 ≤ g) (hp : 3 / 4 * a * b < p)
    (h : -c * (1 + a + b) ≤ 1 / (2 * g) * a ^ 2 + 1 / (2 * g) * b ^ 2 - p) :
    a < 16 * c := by
  have hg' : 1 / (2 * g) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : a ^ 2 < 4 * c * (1 + a + b) := by
    nlinarith [mul_le_mul_of_nonneg_right hg' (by positivity : 0 ≤ a ^ 2 + b ^ 2),
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hab) (by linarith : b - 2 * a ≤ 0)]
  have hc : 0 < 4 * c := (pos_iff_pos_of_mul_pos (h3.trans' (by positivity))).2 (by linarith)
  nlinarith

/-- **Mumford's gap principle.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number
field `k` with a divisor of degree one, `A = (J, ι)` a Jacobian, `j = j_P` the Abel–Jacobi map,
`D` the reduced divisor with support the theta divisor, `K` an algebraic closure of `k`, and for
`z, w ∈ C(K)` let `⟨z, w⟩ = neronPairing (j z) (j w)` and `|z| = √⟨z, z⟩`. There is `c ≥ 1` such
that for all distinct `z ≠ w` with `c ≤ |z| ≤ |w|` and `⟨z, w⟩ > (3/4) |z| |w|`, one has
`2 |z| < |w|`. One may take `c = max 1 (16 c₃)`, with `c₃` the constant of Mumford's theorem
`Faltings.exists_pos_neronPairing_ge_of_ne`. -/
@[faltings "lem_bv_mumford_gap_principle"]
public theorem exists_two_mul_neronNorm_lt_of_ne {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp K
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ c : ℝ, 1 ≤ c ∧ ∀ z w, z ≠ w → c ≤ √(pair z z) → √(pair z z) ≤ √(pair w w) →
      3 / 4 * √(pair z z) * √(pair w w) < pair z w → 2 * √(pair z z) < √(pair w w) := by
  intro pair
  obtain ⟨c₃, -, hM⟩ := exists_pos_neronPairing_ge_of_ne X A hg j hj D hrad hsupp K
  refine ⟨max 1 (16 * c₃), le_max_left _ _, fun z w hzw hcz hzw' hang => ?_⟩
  by_contra hlt
  push Not at hlt
  have := lt_sixteen_mul_of_le_two_mul ((le_max_left _ _).trans hcz) hzw' hlt
    (by exact_mod_cast hg) hang (hM z w hzw)
  linarith [(le_max_right 1 (16 * c₃)).trans hcz]

end Faltings
