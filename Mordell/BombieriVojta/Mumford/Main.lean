module

public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Height.DiagonalLowerBound
public import Mordell.BombieriVojta.Height.Lemma2
public import Mordell.CurveProduct.Embedding.NP
public import Mordell.CurveProduct.Embedding.B
public import Mordell.CurveProduct.Intersection
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import Mordell.CurveProduct.BaseChange
public import Mordell.CurveProduct.Embedding.Existence

/-!
# Mumford's theorem

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `(J, ι)` a Jacobian of `C`, `j = j_P : C → J` the Abel–Jacobi map, `θ` the class of the
theta divisor and `⟨x, y⟩ = ĥ_θ(x + y) - ĥ_θ(x) - ĥ_θ(y)` the Néron form on `J(k̄)`. For
`z, w ∈ C(k̄)` write `⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`. Mumford's theorem says that two
distinct points of `C(k̄)` are never close to parallel in the Néron norm: there is a constant
`c₃ > 0` with
`|z|² / 2g + |w|² / 2g - ⟨z, w⟩ ≥ -c₃ (1 + |z| + |w|)`
for all `z ≠ w` in `C(k̄)`, i.e. off the diagonal `Δ ⊆ C × C`.

The proof compares the two sides through the height `h_V` of the Vojta divisor with
`d₁ = d₂ = d = 1`: Bombieri's upper bound gives
`h_V(z, w) ≤ |z|² / 2g + |w|² / 2g - ⟨z, w⟩ + c₁ (|z| + |w|) + 3 c₂`, and `h_V` is bounded
below off `Δ`.

## Main results

* `Faltings.exists_pos_neronPairing_ge_of_ne`: Mumford's theorem.

## Implementation notes

The Néron form is `Faltings.neronPairing`, on the Jacobian `A : Faltings.Jacobian k X.f`, for
the Abel–Jacobi map `j` (`Faltings.IsAbelJacobiMap`) and the reduced effective Cartier divisor
`D` whose support is `Faltings.thetaDivisor`. A point of `C(k̄)` is a morphism
`Spec k̄ ⟶ C` over `Spec k`, and `j z` is the composite `z ≫ j`. A point `(z, w)` of `C × C`
lies off the diagonal exactly when `z ≠ w`. The norm `|z| = √⟨z, z⟩` is `Real.sqrt`, and
`|z|²` is read literally as `√⟨z, z⟩ ^ 2`.

The constant `c₃` depends on the curve and on the auxiliary embeddings `φ_{NP}`, `φ_B` used in
the proof; the inequality involves neither embedding, so they do not appear in the statement.

Both bounds are statements about the height `h_V` on the `k̄`-points of a curve over `k̄`, so
the proof first builds the base change `C_{k̄} = C ×_k k̄` as a curve with a divisor of degree
one: its divisor is any divisor whose class is the pull-back of `[𝒪_C(P)]`, which exists since
every Picard class of a smooth curve is a divisor class. The embeddings `φ_{NP}` and `φ_B` are
then given by bases of the global sections of invertible sheaves of classes `N [P]` and `[B]`
on `C_{k̄}`; the classes of `P × C`, `C × P` and `Δ` on `C_{k̄} × C_{k̄}` are the pull-backs of
those on `C × C`, the last because the diagonal commutes with flat base change. A `k̄`-point of
`C` over `k` is the same as a section of `C_{k̄} ⟶ Spec k̄`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- The closing estimate: if `-κ ≤ h ≤ Q + c₁ (a + b) + 3 c₂` with `a, b ≥ 0`, then
`-c₃ (1 + a + b) ≤ Q` for `c₃ = max (max (κ + 3 c₂) c₁) 1 > 0`. -/
private lemma neg_mul_le_of_le_of_neg_le {κ c₁ c₂ a b h Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlow : -κ ≤ h) (hup : h ≤ Q + c₁ * (a + b) + 3 * c₂) :
    -(max (max (κ + 3 * c₂) c₁) 1) * (1 + a + b) ≤ Q := by
  have h1 : κ + 3 * c₂ ≤ max (max (κ + 3 * c₂) c₁) 1 :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h2 : c₁ ≤ max (max (κ + 3 * c₂) c₁) 1 := (le_max_right _ _).trans (le_max_left _ _)
  nlinarith [mul_le_mul_of_nonneg_right h2 (add_nonneg ha hb)]

/-- **Mumford's theorem.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field `k`
with a divisor of degree one, `A = (J, ι)` a Jacobian, `j = j_P` the Abel–Jacobi map, `D` the
reduced divisor with support the theta divisor, and `K = k̄`. Writing
`⟨z, w⟩ = neronPairing (j z) (j w)` and `|z| = √⟨z, z⟩` for `z, w ∈ C(K)`, there is `c₃ > 0`
such that `|z|² / 2g + |w|² / 2g - ⟨z, w⟩ ≥ -c₃ (1 + |z| + |w|)` whenever `z ≠ w`. -/
@[faltings "thm_bv_mumford"]
theorem exists_pos_neronPairing_ge_of_ne {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp K
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    let g : ℝ := genus X.f
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ z w, z ≠ w →
      -c₃ * (1 + √(pair z z) + √(pair w w)) ≤
        1 / (2 * g) * √(pair z z) ^ 2 + 1 / (2 * g) * √(pair w w) ^ 2 - pair z w := by
  intro pair g
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  obtain ⟨XK, π, hπ, hP⟩ := exists_baseChange (K := K) X
  have hgK : genus XK.f = genus X.f := genus_baseChange k K π XK.f X.f hπ
  obtain ⟨n, L, hLinv, hL, x, hx, hxi⟩ :=
    exists_basis_isClosedImmersion_np XK (2 * genus X.f + 1) (by rw [hgK])
  obtain ⟨s₀, hs₀⟩ := exists_basis_isClosedImmersion_b XK
  obtain ⟨m, M, hMinv, hM, y, hy, hyi⟩ := hs₀ (max s₀ 1) (le_max_left _ _)
  have hs : 1 ≤ max s₀ 1 := le_max_right _ _
  let : XK.C.Over (Spec (.of K)) := ⟨XK.f⟩
  let : (pullback XK.f XK.f).Over (Spec (.of K)) := ⟨pullback.fst XK.f XK.f ≫ XK.f⟩
  have : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
  have := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
  let φNP : ProjectiveEmbedding XK.f n :=
    ⟨_, hxi, Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _⟩
  let φB : ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m :=
    ⟨_, hyi, Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _⟩
  obtain ⟨c₁, c₂, -, -, hup⟩ := Faltings.BombieriVojta.exists_vojtaHeight_le_neronPairing X A
    hg j hj D hrad hsupp K XK π hπ φNP φB (2 * genus X.f + 1) le_rfl (max s₀ 1) hs L
    (hL.trans (by rw [hP, ← AddMonoidHom.map_zsmul]; rfl)) M
    (by rw [hM, schemePullbackClassHom_map_vojtaClass X XK hπ hP]) x hx rfl y hy rfl
  obtain ⟨κ, hκ⟩ := XK.exists_neg_le_vojtaHeight_one_one_one (by rw [hgK]; exact hg)
    (max s₀ 1) hs (2 * genus X.f + 1) (by rw [hgK]) L hL M hM x hx y hy φNP rfl φB rfl
  refine ⟨max (max (κ + 3 * c₂) c₁) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun z w hzw => ?_⟩
  obtain ⟨z', rfl⟩ := exists_section_homMk_eq X XK hπ z
  obtain ⟨w', rfl⟩ := exists_section_homMk_eq X XK hπ w
  have hne : z' ≠ w' := by rintro rfl; exact hzw rfl
  have hup' := hup 1 1 1 z' w'
  simp only [Int.cast_one, abs_one, one_mul] at hup'
  exact neg_mul_le_of_le_of_neg_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (hκ z' w' hne)
    (hup'.trans_eq (by ring))

end Faltings
