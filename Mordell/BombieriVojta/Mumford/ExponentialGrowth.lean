module

public import Mordell.BombieriVojta.Mumford.GapPrinciple

/-!
# Exponential growth of Néron norms along a narrow cone

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a rational divisor `P` of
degree one, `(J, ι)` a Jacobian of `C`, `j = j_P : C → J` the Abel–Jacobi map, `θ` the class of
the theta divisor and `⟨x, y⟩ = ĥ_θ(x + y) - ĥ_θ(x) - ĥ_θ(y)` the Néron pairing on `J(k̄)`.
For `z, w ∈ C(k̄)` write `⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`.
There is a constant `c ≥ 1` such that the norms along any chain `z₀, …, z_m` of points of
`C(k̄)`, with `c ≤ |z₀| ≤ |z₁| ≤ … ≤ |z_m|`, consecutive points distinct and
`⟨z_i, z_{i+1}⟩ > (3/4) |z_i| |z_{i+1}|`, grow at least like `2 ^ m`: `|z_m| ≥ 2^m |z₀|`.
Mumford's gap principle `Faltings.exists_two_mul_neronNorm_lt_of_ne` gives
`|z_{i+1}| > 2 |z_i|` at each step, and the claim follows by induction on `m`.

## Main results

* `Faltings.exists_two_pow_mul_neronNorm_le`: the exponential growth.

## Implementation notes

The pairing is `Faltings.neronPairing` read on `C(k̄)` through `z ↦ j z = z ≫ j`, and the
norm is `Real.sqrt` of the pairing (so `|z| = 0` when `⟨z, z⟩ < 0`). A point of `C(k̄)` is a
morphism `Spec k̄ ⟶ C` over `Spec k`. The chain is a map `z : Fin (m + 1) → C(k̄)`. Only
consecutive points are required to be distinct and only consecutive norms to be ordered, which
is all the induction uses; this is a stronger statement than the one with all points distinct.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], §4 p. 619 and §10 p. 639.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- A sequence `a 0, …, a m` with `0 ≤ a 0` and `c ≤ a 0` that more than doubles at every step
where it is `≥ c` satisfies `2 ^ i * a 0 ≤ a i`. -/
private lemma two_pow_mul_le_of_two_mul_lt {m : ℕ} {a : Fin (m + 1) → ℝ} {c : ℝ}
    (hc : c ≤ a 0) (h0 : 0 ≤ a 0)
    (hstep : ∀ i : Fin m, c ≤ a i.castSucc → 2 * a i.castSucc < a i.succ) (i : Fin (m + 1)) :
    2 ^ (i : ℕ) * a 0 ≤ a i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := hstep i (hc.trans ((le_mul_of_one_le_left h0 (one_le_pow₀ one_le_two)).trans ih))
    rw [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ]
    linarith

/-- **Exponential growth along a narrow cone.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over
a number field `k` with a rational divisor of degree one, `A = (J, ι)` a Jacobian, `j = j_P` the
Abel–Jacobi map, `D` the reduced divisor with support the theta divisor, `K = k̄`, and
`⟨z, w⟩ = neronPairing … (j z) (j w)`, `|z| = √⟨z, z⟩` on `C(k̄)`. There is `c ≥ 1` such that
for every chain `z 0, …, z m` of `k̄`-points with `c ≤ |z 0|`, non-decreasing norms,
consecutive points distinct and `⟨z i, z (i+1)⟩ > 3/4 |z i| |z (i+1)|`, one has
`2 ^ m |z 0| ≤ |z m|`. -/
@[faltings "lem_bv_exponential_growth"]
public theorem exists_two_pow_mul_neronNorm_le {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp K
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (m : ℕ)
        (z : Fin (m + 1) → (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
          Over.mk X.f)),
      c ≤ √(pair (z 0) (z 0)) →
      (∀ i : Fin m, √(pair (z i.castSucc) (z i.castSucc)) ≤ √(pair (z i.succ) (z i.succ))) →
      (∀ i : Fin m, z i.castSucc ≠ z i.succ) →
      (∀ i : Fin m, 3 / 4 * √(pair (z i.castSucc) (z i.castSucc)) *
          √(pair (z i.succ) (z i.succ)) < pair (z i.castSucc) (z i.succ)) →
      2 ^ m * √(pair (z 0) (z 0)) ≤ √(pair (z (Fin.last m)) (z (Fin.last m))) := by
  intro pair
  obtain ⟨c, hc1, hgap⟩ := exists_two_mul_neronNorm_lt_of_ne X A hg j hj D hrad hsupp K
  refine ⟨c, hc1, fun m z h0 hmono hne hcone => ?_⟩
  simpa using two_pow_mul_le_of_two_mul_lt (a := fun i => √(pair (z i) (z i))) h0
    (Real.sqrt_nonneg _) (fun i hi => hgap _ _ (hne i) hi (hmono i) (hcone i)) (Fin.last m)

end Faltings

end
