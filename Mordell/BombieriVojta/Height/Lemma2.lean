module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Height.Basic
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
import Mordell.BombieriVojta.Height.NeronTateExpansion
import Mordell.NeronTate.Pairing.Nonneg

/-!
# Bombieri's Lemma 2: an upper bound for the height `h_V`

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `N ≥ 2g + 1`, `φ_{NP} : C → ℙⁿ` the embedding by a basis of `H⁰(C, 𝒪(NP))`, `s ≥ 1`
and `φ_B : C × C → ℙᵐ` the embedding by a basis of `H⁰(C × C, 𝒪(B))`,
`B = s P × C + s C × P - Δ'`. For integers `d₁, d₂, d` of any sign let `h_V` be the height
attached to `V = d₁ P × C + d₂ C × P + d Δ'`. Writing `⟨z, w⟩` for the Néron pairing of the
Abel–Jacobi images of `z, w ∈ C(k̄)` and `|z| = √⟨z, z⟩`, there are constants `c₁, c₂ > 0`,
depending only on `C`, `P`, `φ_{NP}`, `φ_B`, with
`h_V(z, w) ≤ d₁ / 2g |z|² + d₂ / 2g |w|² - d ⟨z, w⟩`
`  + c₁ (|d₁| |z| + |d₂| |w|) + c₂ (|d₁| + |d₂| + |d|)`
for all `d₁, d₂, d` and all `(z, w) ∈ (C × C)(k̄)`.

It is the upper half of the expansion `Faltings.exists_abs_vojtaHeight_sub_neronPairing_le` of
`h_V`, with `c₁ = κ₃ / 2g + 1` and `c₂ = κ₁ / N + κ₂ + 1`; `|z|² = ⟨z, z⟩` holds because the
Néron form is positive semidefinite (`Faltings.neronPairing_self_nonneg`).

## Main results

* `Faltings.BombieriVojta.exists_vojtaHeight_le_neronPairing`: Bombieri's Lemma 2.

## Implementation notes

* `h_V` is `Faltings.CurveWithDegreeOneDivisor.vojtaHeight`, which is defined on the points of
  a curve over its own base field. The `k̄`-points are therefore read on a curve
  `XK : Faltings.CurveWithDegreeOneDivisor K` over a fixed algebraic closure `K` of `k`, given
  with a morphism `π : XK.C ⟶ X.C` exhibiting `XK.C` as the base change `C ×_k K`.
  The constants `c₁, c₂` depend on this choice of `K`, as on `C`, `P` and the embeddings.
* The embeddings `φNP`, `φB` are those of `XK.C` and `XK.C ×_K XK.C`, pinned as the morphisms
  `Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of `K`-bases of the global sections of
  invertible sheaves whose classes are the pullbacks along `π` (resp. `π × π`) of
  `N • [𝒪(P)]` and of `Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)` (the class
  of `B`). These are the binders of `Faltings.exists_abs_vojtaHeight_sub_neronPairing_le`.
* The pairing is `Faltings.neronPairing` on the Jacobian `A`, applied to `j ∘ z` for the
  Abel–Jacobi map `j` (`Faltings.IsAbelJacobiMap`), with the theta class given by the reduced
  effective Cartier divisor `D` supported on `Faltings.thetaDivisor`; a `K`-point `z` of `XK`
  enters as the `K`-point `z ≫ π` of `C` over `k`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5, Lemma 2, p. 621
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings.BombieriVojta

universe u

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- **Bombieri's Lemma 2.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field `k`
with a divisor of degree one, `A` a Jacobian with Abel–Jacobi map `j`, `D` the reduced divisor
with support the theta divisor, `K` an algebraic closure of `k` and `XK` a curve over `K` with
`π : XK.C ⟶ X.C` exhibiting it as `C ×_k K`. Let `φNP` and `φB` be the embeddings of `XK.C` and
`XK.C ×_K XK.C` by `K`-bases of the global sections of invertible sheaves of classes
`π^*(N • [𝒪(P)])` (`2g + 1 ≤ N`) and `(π × π)^*(vojtaClass X s s (-1))` (`1 ≤ s`). Writing
`⟨z, w⟩ = neronPairing (j z) (j w)` and `|z| = √⟨z, z⟩`, there are `c₁, c₂ > 0` such that for
all integers `d₁, d₂, d` and all `K`-points `z, w` of `XK`,
`vojtaHeight XK φNP φB s N d₁ d₂ d z w ≤ d₁ / 2g |z|² + d₂ / 2g |w|² - d ⟨z, w⟩`
`+ c₁ (|d₁| |z| + |d₂| |w|) + c₂ (|d₁| + |d₂| + |d|)`. -/
@[faltings "thm_bv_upper_bound_height_vojta"]
public theorem exists_vojtaHeight_le_neronPairing {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] [Algebra ℚ K]
    (XK : CurveWithDegreeOneDivisor K) (π : XK.C ⟶ X.C)
    (hπ : IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {n m : ℕ} (φNP : ProjectiveEmbedding XK.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) (s : ℤ) (hs : 1 ≤ s)
    (L : XK.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule XK.C L]
    (hL : Stacks.SheafOfModules.picardClass XK.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      Stacks.Picard.schemePullbackClassHom π ((N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)))
    (M : (pullback XK.f XK.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback XK.f XK.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback XK.f XK.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      Stacks.Picard.schemePullbackClassHom (pullback.map XK.f XK.f X.f X.f π π
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) hπ.w.symm hπ.w.symm)
        (X.vojtaClass s s (-1))) :
    letI : XK.C.Over (Spec (.of K)) := ⟨XK.f⟩
    letI : (pullback XK.f XK.f).Over (Spec (.of K)) := ⟨pullback.fst XK.f XK.f ≫ XK.f⟩
    haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    ∀ (x : Module.Basis (Fin (n + 1)) K Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
      φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx XK.f →
    ∀ (y : Module.Basis (Fin (m + 1)) K Γ(M, ⊤))
      (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y),
      φB.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
        (pullback.fst XK.f XK.f ≫ XK.f) →
    -- the `K`-point `z ≫ π` of `C` over `k`
    let pt : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) := fun z =>
      Over.homMk (z.1 ≫ π) (by simp [hπ.w, reassoc_of% z.2])
    -- the Néron pairing `⟨z, w⟩ = ⟨j z, j w⟩`
    let pair : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} → ℝ := fun z w =>
      neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp K
        (.ofMul (pt z ≫ j)) (.ofMul (pt w ≫ j))
    let g : ℝ := genus X.f
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (d₁ d₂ d : ℤ) (z w),
      XK.vojtaHeight φNP φB s N d₁ d₂ d z w ≤
        d₁ / (2 * g) * √(pair z z) ^ 2 + d₂ / (2 * g) * √(pair w w) ^ 2 - d * pair z w +
          c₁ * (|(d₁ : ℝ)| * √(pair z z) + |(d₂ : ℝ)| * √(pair w w)) +
          c₂ * (|(d₁ : ℝ)| + |(d₂ : ℝ)| + |(d : ℝ)|) := by
  intro x hx hφNP y hy hφB pt pair g
  obtain ⟨κ₁, κ₂, κ₃, h₁, h₂, h₃, hκ⟩ := exists_abs_vojtaHeight_sub_neronPairing_le X A hg j hj D
    hrad hsupp K XK π hπ φNP φB N hN s hs L hL M hM x hx hφNP y hy hφB
  have hg0 : (0 : ℝ) < g := Nat.cast_pos.2 (one_le_two.trans hg)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨κ₃ / (2 * g) + 1, κ₁ / N + κ₂ + 1, by positivity, by positivity,
    fun d₁ d₂ d z w => ?_⟩
  have hpair (z) : √(pair z z) ^ 2 = pair z z :=
    Real.sq_sqrt (neronPairing_self_nonneg X A (one_le_two.trans hg) j hj D hrad hsupp K _)
  rw [hpair, hpair]
  have := (abs_le.1 (hκ d₁ d₂ d z w)).2
  have : 0 ≤ |(d₁ : ℝ)| * √(pair z z) + |(d₂ : ℝ)| * √(pair w w) := by positivity
  have := abs_nonneg (d₁ : ℝ); have := abs_nonneg (d₂ : ℝ); have := abs_nonneg (d : ℝ)
  have : 0 ≤ κ₁ / N * |(d : ℝ)| := by positivity
  have : 0 ≤ κ₂ * (|(d₁ : ℝ)| + |(d₂ : ℝ)|) := by positivity
  linarith

end Faltings.BombieriVojta
