module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Height.Basic
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Weil.Representative
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import Mordell.BombieriVojta.Height.Lemma4

/-!
# The local expression of the height `h_V`

Let `(C, P)` be a curve over a field `k` algebraic over `ℚ` with a divisor `P` of degree one, of
genus `g`, and fix the auxiliary data of Bombieri's Section 3: `N ≥ 2g + 1` and the embedding
`φ_{NP} : C → ℙⁿ` by a basis of `H⁰(C, 𝒪(NP))`, `s ≥ 1` and the embedding `φ_B : C × C → ℙᵐ` by a
basis of `H⁰(C × C, 𝒪(B))`, `B = s P × C + s C × P - Δ'`. Let `d ≥ 1` and `d₁, d₂` be integers
with `δ₁ = (d₁ + s d) / N`, `δ₂ = (d₂ + s d) / N` positive integers. Let `z, w` be `k`-points of
`C`, `F` a number field inside `k` over which they are defined, and `x, x' ∈ Fⁿ⁺¹`, `y ∈ Fᵐ⁺¹`
representatives of `φ_{NP}(z)`, `φ_{NP}(w)`, `φ_B(z, w)`. Then the height
`h_V = δ₁ h_{NP} ⊠ 1 + δ₂ 1 ⊠ h_{NP} - d h_B` is a sum of local terms:
`h_V(z, w) = ∑_v min_{i, y_i ≠ 0} max_{j, j', x_j ≠ 0 ≠ x'_{j'}}
  log |x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d|_v`,
with `v` running over the places of `F` and `|·|_v` normalised so that the sum is independent
of `F`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.vojtaHeight_eq_sum_iInf_iSup_log`: the local expression of
  `Faltings.CurveWithDegreeOneDivisor.vojtaHeight`.

## Implementation notes

* The number field `F` is any number field with a ring map `algebraMap F k`, and a
  representative of a point `φ(p) ∈ ℙʳ(k)` is a vector `x : Fin (r + 1) → F` with
  `Projectivization.mk k (algebraMap F k ∘ x) _ = φ(p)`. The image point `φ(p)` is read through
  the same dictionary as in `Faltings.ProjectiveEmbedding.height` (the values at `φ(p)` of the
  coordinate forms `T_0, …, T_r`).
* The pair `(z, w)` is the `k`-point `pullback.lift z w` of `C ×_k C`, as in
  `Faltings.CurveWithDegreeOneDivisor.vojtaHeight`.
* The embeddings `φ_{NP}` and `φ_B` are pinned as the morphisms
  `Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of generating bases of the global
  sections of invertible sheaves of classes `N • [𝒪(P)]` and
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)`; these bases are universally
  quantified in the conclusion because their types need the `k`-structures on `C` and
  `C ×_k C`.
* The normalised absolute value `|·|_v` is `v ^ (n_v / [F : ℚ])` with `n_v = v.mult` at an
  infinite place and `n_v = 1` at a finite place, so the sum over places is written as the sum
  over `InfinitePlace F` weighted by `mult` plus the finite sum over `FinitePlace F`, divided by
  `[F : ℚ]`. The minimum and maximum over the (nonempty, finite) index sets are `⨅` and `⨆` over
  subtypes.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 623
-/

open Faltings.BombieriVojta.HeightLowerBound (logHeight_eq_sum_log_iSup sumLocalHeight_eq_logHeight sum_places_eq_logHeight)
open Faltings.BombieriVojta.HeightLowerBound (finsum_sum_of_fintype_right hasFiniteSupport_log_iSup iInf_iSup_log_eq iInf_sub_mul iSup_prod_add_sub intCast_div_natCast_eq log_iSup_eq log_iSup_rpow)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits _root_.NumberField Module Real
open scoped LinearAlgebra.Projectivization
open Faltings

universe u

@[expose] public section

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- **Local expression of `h_V`.** Let `X = (C, P)` be a curve over a field `k` algebraic over
`ℚ` with a divisor of degree one, and `φNP`, `φB` the embeddings of `C` and `C ×_k C` by bases of
the global sections of invertible sheaves of classes `N • [𝒪(P)]` (`2g + 1 ≤ N`) and
`vojtaClass X s s (-1)` (`1 ≤ s`). Let `d ≥ 1` and `δ₁ = (d₁ + s d) / N`, `δ₂ = (d₂ + s d) / N`
be positive integers. If `x, x', y` are vectors over a number field `F ⊆ k` representing the
image points `φNP(z)`, `φNP(w)`, `φB(z, w)` of `k`-points `z, w` of `C`, then
`X.vojtaHeight φNP φB s N d₁ d₂ d z w` is the sum over the places `v` of `F` of
`min_{i, y_i ≠ 0} max_{j, j'} log |x_j ^ δ₁ x'_{j'} ^ δ₂ / y_i ^ d|_v`, where `j, j'` run over the
indices with `x_j ≠ 0`, `x'_{j'} ≠ 0`, and `|·|_v` is the normalised absolute value at `v`. -/
@[faltings "lem_bv_height_vojta_local_expression"]
public theorem CurveWithDegreeOneDivisor.vojtaHeight_eq_sum_iInf_iSup_log {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    (X : CurveWithDegreeOneDivisor k) {n m : ℕ}
    (φNP : ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (s : ℤ) (hs : 1 ≤ s)
    (M : (pullback X.f X.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      X.vojtaClass s s (-1))
    (d₁ d₂ d : ℤ) (hd : 1 ≤ d) (δ₁ δ₂ : ℕ)
    (hδ₁ : d₁ + s * d = N * δ₁) (hδ₂ : d₂ + s * d = N * δ₂) (hδ₁pos : 0 < δ₁) (hδ₂pos : 0 < δ₂)
    (z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _})
    (F : Type*) [Field F] [NumberField F] [Algebra F k]
    (x x' : Fin (n + 1) → F) (y : Fin (m + 1) → F)
    (hx : algebraMap F k ∘ x ≠ 0) (hx' : algebraMap F k ∘ x' ≠ 0)
    (hy : algebraMap F k ∘ y ≠ 0) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
    haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
    -- the image `φ(p) ∈ ℙʳ(k)` of a `k`-point `p`, read as in `ProjectiveEmbedding.height`
    let image : ∀ {Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)} [IsProjectiveVariety k g] {r : ℕ},
        ProjectiveEmbedding g r → {p : Spec (.of k) ⟶ Y // p ≫ g = 𝟙 _} →
          ℙ k (Fin (r + 1) → k) := fun {Y g _ r} φ p =>
      (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
          (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _
            ⟨p.1 ≫ φ.hom ≫ (projectiveSpaceOfModuleIso (Pi.basisFun k (Fin (r + 1)))).inv, by
              simp only [Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
              rw [φ.hom_over, p.2]⟩)).map
        (Pi.basisFun k (Fin (r + 1))).toDualEquiv.symm.toLinearMap
        (Pi.basisFun k (Fin (r + 1))).toDualEquiv.symm.injective
    ∀ (b : Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
      (hb : Stacks.ProjectiveFromSections.GeneratesStalks ⇑b),
      φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑b hb X.f →
    ∀ (b' : Module.Basis (Fin (m + 1)) k Γ(M, ⊤))
      (hb' : Stacks.ProjectiveFromSections.GeneratesStalks ⇑b'),
      φB.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑b' hb'
        (pullback.fst X.f X.f ≫ X.f) →
    Projectivization.mk k (algebraMap F k ∘ x) hx = image φNP z →
    Projectivization.mk k (algebraMap F k ∘ x') hx' = image φNP w →
    Projectivization.mk k (algebraMap F k ∘ y) hy =
      image φB ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
        by rw [pullback.lift_fst_assoc, z.2]⟩ →
    X.vojtaHeight φNP φB s N d₁ d₂ d z w =
      ((∑ v : InfinitePlace F, v.mult *
          ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
            log (v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ d))) +
        ∑ᶠ v : FinitePlace F,
          ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
            log (v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ d))) / finrank ℚ F := by
  intro image b hb hφ b' hb' hφB hxz hxw hyzw
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hx0' : x' ≠ 0 := fun h => hx' (by simp [h])
  have hy0 : y ≠ 0 := fun h => hy (by simp [h])
  have hN0 : 0 < N := by omega
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
  haveI : Smooth (pullback.fst X.f X.f ≫ X.f) := SmoothOfRelativeDimension.smooth 2 _
  have h1 : φNP.height z = Height.logHeight x / finrank ℚ F := by
    rw [← sumLocalHeight_eq_logHeight hx0]
    exact weilHeight_eq_sumLocalHeight hx hxz
  have h2 : φNP.height w = Height.logHeight x' / finrank ℚ F := by
    rw [← sumLocalHeight_eq_logHeight hx0']
    exact weilHeight_eq_sumLocalHeight hx' hxw
  have h3 : φB.height ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
      by rw [pullback.lift_fst_assoc, z.2]⟩ = Height.logHeight y / finrank ℚ F := by
    rw [← sumLocalHeight_eq_logHeight hy0]
    exact weilHeight_eq_sumLocalHeight hy hyzw
  have hloc (v : AbsoluteValue F ℝ) := iInf_iSup_log_eq v hx0 hx0' hy0 δ₁ δ₂ (by omega : 0 ≤ d)
  simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply, hloc]
  simp only [← InfinitePlace.coe_apply, ← FinitePlace.coe_apply]
  rw [sum_places_eq_logHeight hx0 hx0' hy0]
  simp only [CurveWithDegreeOneDivisor.vojtaHeight]
  rw [h1, h2, h3, intCast_div_natCast_eq hN0 hδ₁, intCast_div_natCast_eq hN0 hδ₂]
  ring

end Faltings
