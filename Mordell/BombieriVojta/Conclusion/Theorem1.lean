module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.ThetaPolarization
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.Conclusion.AngleInequality
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSetFinite

/-!
# Bombieri's Theorem 1: points of large norm in distant shells are not close in angle

Let `C` be a smooth projective curve of genus `g ≥ 2` over a number field `k`, with a divisor
`P` of degree one, let `J` be its Jacobian, `j : C → J`, `z ↦ cl(z - P)`, the Abel–Jacobi map,
and `⟨x, y⟩ = ĥ_θ(x + y) - ĥ_θ(x) - ĥ_θ(y)` the Néron form of the theta class on `J(k̄)`, with
norm `|x| = √⟨x, x⟩`. Write `|z| = |j z|` and `⟨z, w⟩ = ⟨j z, j w⟩` for `z, w ∈ C(k̄)`. Fix the
standing data of Bombieri's Sections 9 and 10: a generic basis `x` of `H⁰(C, 𝒪(N P))`,
`N ≥ 2g + 1`, giving `φ_{NP}`, `ψ = φ_{NP} × φ_{NP}`, and a basis `y` of `H⁰(C × C, 𝒪(B))`,
`B = (s + 1)(P × C) + (s + 1)(C × P) - Δ`, generic for the projections `π_{ab}` and giving
`φ_B`. Then there is a constant `γ(C) > 1` such that for all `z, w ∈ C(k̄)` with
`γ(C) ≤ |z|` and `γ(C) |z| ≤ |w|`, `⟨z, w⟩ ≤ (3 / 4) |z| |w|`.

This is the heart of Vojta's inequality in Bombieri's proof of the Mordell conjecture: combined
with Mumford's gap principle and a covering of the unit sphere of `J(K) ⊗ ℝ` by caps, it bounds
the number of points of `C(K)` in each cone. It follows from the angle inequality
`Faltings.exists_neronPairing_div_le` by choosing `γ₀`, `ε` small.

## Main results

* `Faltings.exists_neronPairing_abelJacobi_le`: Bombieri's Theorem 1.

## Implementation notes

The setting is word for word that of `Faltings.exists_neronPairing_div_le` (the angle
inequality): the curve `X : Faltings.CurveWithDegreeOneDivisor k`, its Jacobian `A`, the
Abel–Jacobi map `j` and the class `θ` of the reduced effective Cartier divisor `D` supported on
`Faltings.thetaDivisor` define `Faltings.neronPairing` on `J(k̄)`; the standing data `x`,
`φ_{NP}`, `ψ`, `y`, `φ_B` live over `k` on `C` and `C ×_k C = pullback X.f X.f`, with `φ_{NP}`
and `φ_B` closed immersions into `ℙⁿ_k`, `ℙᵐ_k` pulling `𝒪(1)` back to the classes of `N P` and
of `B` and the co-ordinates back to `x_ν / x_j` (on every chart) and to `y`. A point
`z ∈ C(k̄)` is a morphism `Spec k̄ ⟶ C` over `k`, its image `z ≫ j`, and the norm is
`|z| = √⟨j z, j z⟩` with `Real.sqrt`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, Theorem 1,
  pp. 637–638
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Faltings

open BombieriSiegel

section

/-! ### The arithmetic of Theorem 1 -/

/-- `√(g + 1/10) / g ≤ 0.725` for `g ≥ 2`. -/
private lemma sqrt_add_div_le {g : ℝ} (hg : 2 ≤ g) : √(g + 1 / 10) / g ≤ 29 / 40 := by
  have hg0 : 0 < g := by linarith
  rw [div_le_iff₀ hg0, Real.sqrt_le_left (by positivity)]
  nlinarith

/-- The choice of `ε`: `8 N c₄ √(g + 1/10) ε ≤ 1/120`. -/
private lemma exists_eps (G N c₄ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ c₄ * √(G + 1 / 10) * (8 * N * ε) ≤ 1 / 120 := by
  set M : ℝ := |√(G + 1 / 10) * (8 * N)| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hc0 : 0 ≤ |c₄| * M := by positivity
  refine ⟨1 / (120 * (|c₄| * M + 1) + 1), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    linarith
  · have h1 : c₄ * √(G + 1 / 10) * (8 * N * (1 / (120 * (|c₄| * M + 1) + 1))) ≤
        |c₄| * M * (1 / (120 * (|c₄| * M + 1) + 1)) := by
      rw [show c₄ * √(G + 1 / 10) * (8 * N * (1 / (120 * (|c₄| * M + 1) + 1))) =
        (c₄ * (√(G + 1 / 10) * (8 * N))) * (1 / (120 * (|c₄| * M + 1) + 1)) by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hM, ← abs_mul]
      exact le_abs_self _
    have h2 : |c₄| * M * (1 / (120 * (|c₄| * M + 1) + 1)) ≤ 1 / 120 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith

/-- The choice of `γ`, and the final arithmetic of Theorem 1. -/
private lemma exists_gamma {G ε t : ℝ} (hG : 2 ≤ G) (hε : 0 < ε) (ht : t ≤ 1 / 120)
    (c₁₈ c₁₉ c₂₀ B : ℝ) :
    ∃ γ : ℝ, 1 < γ ∧ B < γ ∧ ∀ a b p : ℝ, γ ≤ a → γ * a ≤ b →
      c₂₀ / ε ≤ a ∧ a / b ≤ ε ∧ γ ≤ b ∧
      (p / (a * b) ≤ √(G + 1 / 10) / G + t + c₁₉ * (1 / a + 1 / b) + c₁₈ / (1 / 10 * a ^ 2) →
        p ≤ 3 / 4 * a * b) := by
  refine ⟨max (max 2 (1 / ε)) (max (c₂₀ / ε) (max (240 * |c₁₉| + 1)
    (max √(1200 * |c₁₈|) (B + 1)))), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_of_le_left (le_max_left _ _))
  · exact lt_of_lt_of_le (lt_add_one B)
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
  intro a b p hza hzb
  set γ := max (max 2 (1 / ε)) (max (c₂₀ / ε) (max (240 * |c₁₉| + 1)
    (max √(1200 * |c₁₈|) (B + 1))))
  have hγ2 : 2 ≤ γ := le_max_of_le_left (le_max_left _ _)
  have hγε : 1 / ε ≤ γ := le_max_of_le_left (le_max_right _ _)
  have hγc₂₀ : c₂₀ / ε ≤ γ := le_max_of_le_right (le_max_left _ _)
  have hγc₁₉ : 240 * |c₁₉| + 1 ≤ γ := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hγc₁₈ : √(1200 * |c₁₈|) ≤ γ :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have ha0 : 0 < a := by linarith
  have hab : a ≤ b := by nlinarith
  have hb0 : 0 < b := by linarith
  refine ⟨hγc₂₀.trans hza, ?_, by linarith, fun hp => ?_⟩
  · rw [div_le_iff₀ hb0]
    have : 1 ≤ ε * γ := by rwa [div_le_iff₀ hε, mul_comm] at hγε
    nlinarith
  have hterm1 : √(G + 1 / 10) / G ≤ 29 / 40 := sqrt_add_div_le hG
  have hterm3 : c₁₉ * (1 / a + 1 / b) ≤ 1 / 120 := by
    have h1 : 1 / a ≤ 1 / γ := one_div_le_one_div_of_le (by linarith) hza
    have h2 : 1 / b ≤ 1 / γ := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hs : 0 ≤ 1 / a + 1 / b := by positivity
    have h3 : c₁₉ * (1 / a + 1 / b) ≤ |c₁₉| * (2 / γ) := by
      calc c₁₉ * (1 / a + 1 / b) ≤ |c₁₉| * (1 / a + 1 / b) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hs
        _ ≤ |c₁₉| * (2 / γ) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [show 2 / γ = 1 / γ + 1 / γ by ring]
            linarith
    have h4 : |c₁₉| * (2 / γ) ≤ 1 / 120 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
      have := abs_nonneg c₁₉
      nlinarith
    linarith
  have hterm4 : c₁₈ / (1 / 10 * a ^ 2) ≤ 1 / 120 := by
    have hγ2' : 1200 * |c₁₈| ≤ γ ^ 2 := by
      calc 1200 * |c₁₈| = √(1200 * |c₁₈|) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ γ ^ 2 := by gcongr
    have ha2 : γ ^ 2 ≤ a ^ 2 := by gcongr
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := le_abs_self c₁₈
    nlinarith
  have hfin : p / (a * b) ≤ 3 / 4 := by linarith
  rw [div_le_iff₀ (by positivity)] at hfin
  linarith

end

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **Bombieri's Theorem 1.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field
`k` with a divisor `P` of degree one, `⟨ , ⟩ = Faltings.neronPairing` its Néron form on `J(k̄)`,
`⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`, with the standing data of Bombieri's Sections 9–10
over `k`: a generic basis `x` of `L(N P)` giving `φNP`, `ψ = φNP × φNP`, and a basis `y` of
`H⁰(C × C, 𝒪(B))` generic for the projections giving `φB`. There is `γ > 1` such that any
`z, w ∈ C(k̄)` with `γ ≤ |z|` and `γ |z| ≤ |w|` satisfy `⟨z, w⟩ ≤ (3 / 4) |z| |w|`. -/
@[faltings "thm_bvr_theorem1"]
public theorem exists_neronPairing_abelJacobi_le {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0) :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ γ : ℝ, 1 < γ ∧
    ∀ z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f,
      γ ≤ √(pair z z) → γ * √(pair z z) ≤ √(pair w w) →
        pair z w ≤ 3 / 4 * √(pair z z) * √(pair w w) := by
  intro pair
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  obtain ⟨c₄, c₁₈, c₁₉, hang⟩ := exists_neronPairing_div_le X A hg j hj D hrad hsupp kbar N hN hn
    x hx hxbpf Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx ψ hψ₁ hψ₂ hkC hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ DB hDB y
    hy hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3
  obtain ⟨c₂₀, hc₂₀⟩ := hang (1 / 10) (by norm_num) le_rfl
  -- the finitely many points lying in some exceptional set
  obtain ⟨Z, hZfin, hZ⟩ := exists_finite_forall_notMem_exceptionalSet k X.f
    ((N : ℤ) • X.P.mapDomain Subtype.val) x hx.linearIndependent kbar
  have hS : {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f |
      z.left ∈ Z}.Finite :=
    hZfin.preimage fun a _ b _ h => Over.OverMorphism.ext h
  obtain ⟨B, hB⟩ := (hS.image fun z => √(pair z z)).bddAbove
  have hG2 : (2 : ℝ) ≤ (genus X.f : ℝ) := by exact_mod_cast hg
  obtain ⟨ε, hε0, hε1, hc₄⟩ := exists_eps (genus X.f : ℝ) N c₄
  obtain ⟨γ, hγ1, hγB, hγ⟩ := exists_gamma hG2 hε0 hc₄ c₁₈ c₁₉ c₂₀ B
  refine ⟨γ, hγ1, fun z w hz hw => ?_⟩
  obtain ⟨hzc, hzw, hb, hfin⟩ := hγ _ _ (pair z w) hz hw
  -- `z` and `w` are not exceptional
  have hgood : ∀ v, γ ≤ √(pair v v) → v.left ∉ Z := by
    intro v hv hvZ
    have := hB ⟨v, hvZ, rfl⟩
    linarith
  have hZz := hgood z hz
  have hZw := hgood w hb
  refine hfin (hc₂₀ ε hε0 hε1 z w hzc hzw ?_)
  intro p hzp hwp K _ _ _ ι CK _ π hπ _ _ _ _ xK ιS hξ₁₀ DK hDK pK _ hpK
  have hDK' : ∀ Q, DK Q = ((N : ℤ) • X.P.mapDomain Subtype.val) (π Q) := fun Q => by
    rw [hDK, Finsupp.smul_apply, smul_eq_mul]
  have key₁ : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫
      (pK ≫ pullback.fst _ _) ≫ π = z.left := by
    rw [hzp, ← hpK]
    simp [ιS]
  have key₂ : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫
      (pK ≫ pullback.snd _ _) ≫ π = w.left := by
    rw [hwp, ← hpK]
    simp [ιS]
  exact ⟨fun hmem => hZ z.left hZz K ι CK (CK ↘ Spec (.of K)) π hπ hξ₁₀ DK hDK' _ hmem.1
      key₁ hmem,
    fun hmem => hZ w.left hZw K ι CK (CK ↘ Spec (.of K)) π hπ hξ₁₀ DK hDK' _ hmem.1 key₂ hmem⟩

end Faltings
