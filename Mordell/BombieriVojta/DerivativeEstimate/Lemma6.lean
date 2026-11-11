module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.TripleFunction.AdmissiblePair
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Taylor.CurveProduct
public import Mordell.Polynomial.PowerSeries.DividedDeriv
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.TripleFunction.AffineFunctions
public import Mordell.BombieriVojta.LineBundle.Basic
public import Mordell.BombieriVojta.TripleFunction.Basic
public import Mordell.BombieriVojta.TripleFunction.Regular
public import Mordell.BombieriVojta.Taylor.Leibniz
public import Mordell.BombieriVojta.Taylor.MonomialBound
public import Mordell.BombieriVojta.Taylor.SeparatedVariables
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma5
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkSections
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
public import StacksFrontier.RingTheory.RegularLocalRing.AssociatedGradedPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import Mordell.BombieriVojta.Height.Lemma4
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.BombieriVojta.TripleFunction.FirstCoefficient

/-!
# Bombieri's Lemma 6: the estimate for derivatives

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree one,
let `N ≥ 2g + 1`, `n = N - g`, and let `x₀, …, xₙ` be a generic basis of `L(NP) = H⁰(C, 𝒪(NP))`,
defining the embedding `φ_{NP} : C → ℙⁿ`, with `ξ_{νj} = x_ν / x_j`. Let `φ_B : C × C → ℙᵐ` be the
second auxiliary embedding, `ψ = φ_{NP} × φ_{NP}`, `s ≥ 1`, and let `d₁, d₂, d` be positive
integers with `d_i + s d = N δ_i` for integers `δ_i`. Let `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(-d)` and
`h_V(z, w) = δ₁ h_{NP}(z) + δ₂ h_{NP}(w) - d h_B(z, w)`.

Then there is a constant `c₄`, depending only on `C`, `P` and `φ_{NP}`, with the following
property. Let `K ⊇ k` be a number field, `(z, w) ∈ (C × C)(K)` with `z, w` outside the
exceptional set `Z`, let `s` be a global section of `𝒪(V)` with a representative `F = (F_i)`, and
let `(i₁*, i₂*)` be admissible for `s` at `(z, w)` with respect to the uniformizers
`ς = ξ₁₀ - ξ₁₀(z)` and `ς' = ξ'₁₀ - ξ'₁₀(w)`. Then
`h_V(z, w) ≥ -h(F) - c₄ (i₁* |z|² + i₂* |w|² + i₁* + i₂*) - (δ₁ + δ₂) - n log((δ₁ + n)(δ₂ + n))`,
where `h(F)` is the height of the vector of all coefficients of all `F_i` and `|z|` is the Néron
norm.

## Main results

* `Faltings.BombieriSiegel.exists_le_vojtaHeight_of_isAdmissiblePair`: the estimate.

## Implementation notes

* The curve is a `Faltings.CurveWithDegreeOneDivisor`, and the Néron norm is read exactly as in
  `Faltings.BombieriSiegel.exists_finsum_iSup_log_dividedDerivative_le`: on a Jacobian
  `A : Faltings.Jacobian k X.f` with Abel–Jacobi map `j` (`Faltings.IsAbelJacobiMap`) and the
  reduced effective Cartier divisor `D` whose support is `Faltings.thetaDivisor`,
  `|z| = √⟨j z, j z⟩` with `⟨·, ·⟩ = Faltings.neronPairing` on `J(k̄)`. The algebraic closure `k̄`
  is fixed before the constant, and the `K`-points `z, w` are read in `C(k̄)` through a
  `k`-embedding `K → k̄`. The constant is chosen before `d₁, d₂, d, δ₁, δ₂` and `K`.
* The basis `x` consists of rational functions (`Faltings.BombieriSiegel.IsGenericBasis`) of
  `L(N P)`, and `φ_{NP}` is the closed immersion over `k` whose chart functions `T_ν / T_j`
  restrict to `x_ν / x_j` in `k(C)`.
* `z ∉ Z` is read on the base change `C_K`, an abstract pullback square over `Spec K ⟶ Spec k`,
  as `z_K ∉ exceptionalSet K f_K D_K x_K _`, with `x_K` the pullback of `x`
  (`functionFieldMap`), `D_K` the pull-back `Q ↦ N P(π Q)` of the divisor `N P` and `z_K` the
  `K`-point over `z`.
* `C × C` over `K` is an abstract pullback square `S = (C ×_k C) ×_k K`, with
  `ψ : S ⟶ ℙⁿ_K ×_K ℙⁿ_K` and `φ : S ⟶ ℙᵐ_K` the base changes of `φ_{NP} × φ_{NP}` and `φ_B`,
  fixed by their components; `(z, w)` is a `K`-point `p` of `S`, with `z, w` its two projections.
* A section `s` with a representative with algebraic coefficients is defined, together with the
  representative, over some number field; enlarging `K` to contain it (heights are invariant
  under extension, and `c₄` does not depend on `K`), `s` is a global section of `𝒪(V)` on `S`
  and `F` has coefficients in `Γ(Spec K, 𝒪) = K`.
* `ς` is `s₁ - s₁(p)` for the germ `s₁` at `p` of `ξ₁₀ ∘ pr₁` (any element of the local ring at
  `p` whose image in `K(S)` is the pullback of `x₁ / x₀` along the first projection), and
  likewise `ς'` along the second projection.
* Heights of points are `Height.logHeight c / [K : ℚ]` for coordinates `c` of the image point in
  the integral model of projective space; `h(F)` is `Height.logHeight / [K : ℚ]` of the family of
  all non-zero coefficients of all `F_i`. With `δ_i = (d_i + s d) / N`, `h_V` is the formula of
  `Faltings.vojtaHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 6, p. 628,
  with the Errata-Corrige (1991)
-/

open Faltings.BombieriVojta (algebraMap_stalk_functionField_injective const_comp const_eq ev_const
  ext_of_germ ne_zero_of_maximalIdeal_eq stalkClosedPointTo_comp_over_germ stalkCongr_const
  taylorCoeff₂_mul_of_vanish taylorCoeff₂_zero_zero)
open Faltings.BombieriVojta.HeightLowerBound (finsum_wt_log_iSup vojtaHeight_eq_sum_iInf_iSup_log)

open Faltings.BombieriVojta (antidiag_add const eq_div_of_eq_mul ev_eq_zero_of_mem
  ne_zero_of_eq_mul sres_id sres_sres stalkClosedPointTo_fromSpecStalk_eq
  stalkClosedPointTo_germ_of_eq taylorCoeff₂_mul)
open Faltings.BombieriVojta.HeightLowerBound (IsCoordinatesOf IsCoordinatesOf.eq_mul
  IsCoordinatesOf.eq_mul_comp IsCoordinatesOf.ne_zero absV appTop_germ_eq_const archLog
  botOrZero_add botOrZero_finset_sup botOrZero_logAbsV botOrZero_partitionSup card_support_le
  chartOf exists_absV_sum_le finite_support_log finite_support_of_inr finite_support_partitionSup
  finset_sup_ne_top finsum_coe_ereal finsum_places germ_app_eq_ratioOf germ_ratio_mul_germ_ratio
  isLocalHom_comp_comp isLocalHom_const_comp isLocalHom_quotient_mk isRegularLocalRing_stalk
  isSeparable_residueField logAbsV logAbsV_le_of_le logAbsV_mul logAbsV_ne_top logAbsV_of_ne_zero
  logAbsV_sum_le logAbsV_sum_mul_le logAbsV_zero mapId_mul_mapId maximalIdeal_stalk_pullback
  multiset_sum_ne_top neg_finsum_le neg_finsum_le_localExpression oldVojtaHeight partitionSup
  partitionSup_ne_top ratioOf ratioOf_comp ratioOf_mul_ratioOf real_of_logAbsV_le
  ringKrullDim_stalk_pullback stalk_hom_ext sub_const_mem_maximalIdeal sumElim_logAbsV_two_pow
  sum_archLog sum_archLog_two_pow_le sum_exponents_eq sum_log_eq_zero sum_wt_inl sup_logAbsV_eq
  taylorCoeff₂_sum_const_mul wt wt_pos)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing _root_.NumberField Module
open Faltings Faltings.BombieriVojta Faltings.BombieriSiegel
open scoped LinearAlgebra.Projectivization

namespace Faltings.Lemma6EstimateForDerivatives

universe u

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- Taylor coefficients in two parameters are invariant under an isomorphism of `K`-schemes. -/
private theorem taylorCoeff₂_stalkMap_of_isIso {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] (e : X ⟶ Y) [IsIso e]
    (he : e ≫ (Y ↘ Spec (.of K)) = X ↘ Spec (.of K)) (p : Spec (.of K) ⟶ X)
    (ϖ ϖ' f : Y.presheaf.stalk (e (p (closedPoint K)))) (i₁ i₂ : ℕ) :
    taylorCoeff₂ p (e.stalkMap _ ϖ) (e.stalkMap _ ϖ') (e.stalkMap _ f) i₁ i₂ =
      taylorCoeff₂ (p ≫ e) ϖ ϖ' f i₁ i₂ := by
  have hi : IsIso (e.stalkMap (p (closedPoint K))) :=
    ((isIso_iff_isIso_stalkMap e).mp ‹_›).2 _
  have hbij : Function.Bijective (e.stalkMap (p (closedPoint K))).hom :=
    (asIso (e.stalkMap (p (closedPoint K)))).commRingCatIsoToRingEquiv.bijective
  have hc : ∀ a : K, ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
      X.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom a =
      (e.stalkMap (p (closedPoint K))).hom (((Scheme.ΓSpecIso (.of K)).inv ≫
        (Y ↘ Spec (.of K)).appTop ≫ Y.presheaf.germ ⊤ (e (p (closedPoint K))) trivial).hom a) := by
    intro a
    have h1 : (Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
        X.presheaf.germ ⊤ (p (closedPoint K)) trivial =
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫
          Y.presheaf.germ ⊤ (e (p (closedPoint K))) trivial) ≫ e.stalkMap (p (closedPoint K)) := by
      rw [← he, Scheme.Hom.comp_appTop]
      have := Scheme.Hom.germ_stalkMap e ⊤ (p (closedPoint K)) trivial
      simp only [Category.assoc]
      rw [this]
      rfl
    rw [h1]; rfl
  have hmem : ∀ (g : Y.presheaf.stalk (e (p (closedPoint K)))) (n : ℕ),
      (e.stalkMap (p (closedPoint K))).hom g ∈ Ideal.span {(e.stalkMap (p (closedPoint K))).hom ϖ,
        (e.stalkMap (p (closedPoint K))).hom ϖ'} ^ n ↔ g ∈ Ideal.span {ϖ, ϖ'} ^ n := by
    intro g n
    have : Ideal.span {(e.stalkMap (p (closedPoint K))).hom ϖ,
        (e.stalkMap (p (closedPoint K))).hom ϖ'} ^ n =
        (Ideal.span {ϖ, ϖ'} ^ n).map (e.stalkMap (p (closedPoint K))).hom := by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_pair]
    rw [this, ← Ideal.mem_comap, Ideal.comap_map_of_bijective _ hbij]
  unfold taylorCoeff₂
  simp only
  congr 2
  funext F
  refine propext (forall_congr' fun n => Iff.trans ?_ (hmem _ n))
  apply Eq.to_iff
  congr 1
  erw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  erw [map_mul, map_mul, map_pow, map_pow, hc]
  rfl

/-- `lem_bv_divided_leibniz_separated` on a surface `X` given with a pullback square
`X ≅ C ×_K D`. -/
private theorem taylorCoeff₂_stalkMap_mul_stalkMap {K : Type u} [Field K]
    {C D : Scheme.{u}} [C.Over (Spec (.of K))] [D.Over (Spec (.of K))]
    [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [IsCurve K (D ↘ Spec (.of K))] [Smooth (D ↘ Spec (.of K))]
    {X : Scheme.{u}} [X.Over (Spec (.of K))] {pr₁ : X ⟶ C} {pr₂ : X ⟶ D}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (D ↘ Spec (.of K)))
    (hXo : pr₁ ≫ (C ↘ Spec (.of K)) = X ↘ Spec (.of K))
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    (ς ũ : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)))
    (ς' ũ' : D.presheaf.stalk ((p ≫ pr₂) (closedPoint K)))
    (hς : maximalIdeal (C.presheaf.stalk ((p ≫ pr₁) (closedPoint K))) = Ideal.span {ς})
    (hς' : maximalIdeal (D.presheaf.stalk ((p ≫ pr₂) (closedPoint K))) = Ideal.span {ς'})
    (a b : ℕ) :
    taylorCoeff₂ p (pr₁.stalkMap (p (closedPoint K)) ς) (pr₂.stalkMap (p (closedPoint K)) ς')
        (pr₁.stalkMap (p (closedPoint K)) ũ * pr₂.stalkMap (p (closedPoint K)) ũ') a b =
      taylorCoeff (p ≫ pr₁) ς ũ a * taylorCoeff (p ≫ pr₂) ς' ũ' b := by
  obtain ⟨e, _, rfl, rfl⟩ : ∃ e : X ⟶ pullback (C ↘ Spec (.of K)) (D ↘ Spec (.of K)),
      IsIso e ∧ e ≫ pullback.fst _ _ = pr₁ ∧ e ≫ pullback.snd _ _ = pr₂ :=
    ⟨hX.isoPullback.hom, inferInstance, by simp, by simp⟩
  have he : e ≫ (pullback (C ↘ Spec (.of K)) (D ↘ Spec (.of K)) ↘ Spec (.of K)) =
      X ↘ Spec (.of K) := by
    rw [← hXo, Category.assoc]
    congr 1
    first | rfl | exact pullback.condition | exact pullback.condition.symm
  have : (p ≫ e).IsOver (Spec (.of K)) := ⟨by rw [Category.assoc, he]; exact comp_over p _⟩
  have key := taylorCoeff₂_stalkMap_fst_mul_stalkMap_snd (p ≫ e) ς ũ ς' ũ' hς hς' a b
  have h1 : ∀ {Z : Scheme.{u}} (g : pullback (C ↘ Spec (.of K)) (D ↘ Spec (.of K)) ⟶ Z) t,
      ((e ≫ g).stalkMap (p (closedPoint K))).hom t =
        (e.stalkMap (p (closedPoint K))).hom ((g.stalkMap (e (p (closedPoint K)))).hom t) := by
    intro Z g t
    rw [Scheme.Hom.stalkMap_comp]; rfl
  convert (taylorCoeff₂_stalkMap_of_isIso e he p _ _ _ a b).trans key using 2
  · exact h1 _ _
  · exact h1 _ _
  · exact ((map_mul _ _ _).trans (congrArg₂ _ (h1 _ _).symm (h1 _ _).symm)).symm
  · rfl
  · rfl

section FunctionFieldInstances

variable (X : Scheme.{u}) [IrreducibleSpace X]

private noncomputable abbrev ffCommRing : CommRing X.functionField := inferInstance
private noncomputable abbrev ffCommSemiring : CommSemiring X.functionField :=
  (ffCommRing X).toCommSemiring
private noncomputable abbrev ffSemiring : Semiring X.functionField :=
  (ffCommRing X).toCommSemiring.toSemiring
private noncomputable abbrev ffRing : Ring X.functionField := (ffCommRing X).toRing

end FunctionFieldInstances

attribute [local instance 10000] ffCommRing ffCommSemiring ffSemiring ffRing

section LocalExpression

open _root_.NumberField Module Real

section Global

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-- For a nonzero tuple, `log max_i |x_i|_v` vanishes at all but finitely many finite places. -/
private lemma LE_hasFiniteSupport_log_iSup {x : ι → K} (hx : x ≠ 0) :
    Function.HasFiniteSupport fun v : FinitePlace K ↦ log (⨆ i, v (x i)) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  refine (Set.finite_iUnion fun i : {i // x i ≠ 0} ↦
    FinitePlace.hasFiniteMulSupport (K := K) i.2).subset fun v hv ↦ ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  have h1 : ⨆ i, v (x i) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (Finite.le_ciSup_of_le i₀ (h ⟨i₀, hi₀⟩).ge)
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h ⟨i, hi⟩).le
  exact hv (by simp [h1])

end Global

end LocalExpression

section Decomposition

variable {K : Type u} [Field K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]

/-- **The Taylor coefficient `D_{ijj'}` of `F_i(ξ_j, ξ'_{j'})`.** For a polynomial `P` in the two
sets of variables `x_ν, x'_ν`, whose coefficients act through constants, the Taylor coefficient of
`P(ξ ∘ pr₁, ξ' ∘ pr₂)` at `(z, w)` is `∑_α P_α ∂_{i₁}(ξ^{α₁})(z) ∂'_{i₂}(ξ'^{α₂})(w)`. -/
private theorem taylorCoeff₂_eval₂_sumElim
    {X : Scheme.{u}} [X.Over (Spec (.of K))] {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    (hXo : pr₁ ≫ (C ↘ Spec (.of K)) = X ↘ Spec (.of K))
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    [IsRegularLocalRing (X.presheaf.stalk
        (p (closedPoint K)))]
    {ς : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K))}
    {ς' : C.presheaf.stalk ((p ≫ pr₂) (closedPoint K))}
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'})
    {R : Type*} [CommRing R] {n : ℕ} (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) R)
    (c : R →+* X.presheaf.stalk
        (p (closedPoint K))) (a : R → K) (hc : ∀ t, c t = const _ (a t))
    (ξ : Fin (n + 1) → C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)))
    (ξ' : Fin (n + 1) → C.presheaf.stalk ((p ≫ pr₂) (closedPoint K)))
    (i₁ i₂ : ℕ) :
    taylorCoeff₂ p
        (pr₁.stalkMap (p (closedPoint K)) ς)
        (pr₂.stalkMap (p (closedPoint K)) ς')
        (P.eval₂ c (Sum.elim
          (fun ν => pr₁.stalkMap
            (p (closedPoint K)) (ξ ν))
          (fun ν => pr₂.stalkMap
            (p (closedPoint K)) (ξ' ν)))) i₁ i₂ =
      ∑ e ∈ P.support, a (P.coeff e) *
        (taylorCoeff (p ≫ pr₁) ς (∏ ν, ξ ν ^ e (Sum.inl ν)) i₁ *
          taylorCoeff (p ≫ pr₂) ς' (∏ ν, ξ' ν ^ e (Sum.inr ν)) i₂) := by
  have hm := maximalIdeal_stalk_pullback hX hXo p hς hς'
  have hdim := ringKrullDim_stalk_pullback hX hXo p hς hς'
  have hP : P.eval₂ c (Sum.elim
          (fun ν => pr₁.stalkMap
            (p (closedPoint K)) (ξ ν))
          (fun ν => pr₂.stalkMap
            (p (closedPoint K)) (ξ' ν))) =
      ∑ e ∈ P.support, const (p (closedPoint K)) (a (P.coeff e)) *
        (pr₁.stalkMap (p (closedPoint K))
            (∏ ν, ξ ν ^ e (Sum.inl ν)) *
          pr₂.stalkMap (p (closedPoint K))
            (∏ ν, ξ' ν ^ e (Sum.inr ν))) := by
    rw [MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hc, Fintype.prod_sum_type]
    exact congrArg₂ _ rfl (congrArg₂ _
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun ν _ => map_pow _ _ _)).symm
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun ν _ => map_pow _ _ _)).symm)
  rw [hP, taylorCoeff₂_sum_const_mul p hdim hm]
  exact Finset.sum_congr rfl fun e _ =>
    congrArg _ (taylorCoeff₂_stalkMap_mul_stalkMap hX hXo p ς _ ς' _ hς hς' i₁ i₂)

end Decomposition

section Analysis

open Real

variable {K : Type u} [Field K] [NumberField K]

private lemma archLog_inr (w : FinitePlace K) (M : ℝ) : archLog (.inr w) M = 0 := rfl

end Analysis

section Transport

/-- `appLE` along equal morphisms. -/
private theorem appLE_congr' {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- Evaluating the germ of a section at a `K`-point. -/
private theorem stalkClosedPointTo_germ_eq' {K : Type u} [Field K] {Y : Scheme.{u}}
    (q : Spec (.of K) ⟶ Y) (W : Y.Opens)
    (hq : q (closedPoint K) ∈ W) (hp : ⊤ ≤ q ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Scheme.stalkClosedPointTo q).hom (Y.presheaf.germ W _ hq x) =
      (Scheme.ΓSpecIso (.of K)).hom (q.appLE W ⊤ hp x) := by
  have h := congr($(Scheme.germ_stalkClosedPointTo q W hq) x)
  refine h.trans ?_
  simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.comp_apply]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- At a `K`-point whose image in `ℙʳ_ℤ` has homogeneous coordinates `a` with `a_j = 1`, the
point lies on the chart `D₊(T_j)` and `T_ν / T_j` takes the value `a_ν`. -/
private theorem exists_appLE_ratio_eq {K : Type u} [Field K] {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (q : Spec (.of K) ⟶ Y)
    (a' : Fin (r + 1) → K) (ha' : Ideal.span (Set.range a') = ⊤) (j ν : Fin (r + 1))
    (h' : q ≫ f ≫ projectiveSpaceOver.toIntegralAtUniverse r _ =
      projectiveSpacePoint (R := CommRingCat.of K) a' ha') (hj : a' j = 1) :
    ∃ hp : ⊤ ≤ q ⁻¹ᵁ chartOf f j, (Scheme.ΓSpecIso (.of K)).hom (q.appLE _ ⊤ hp
      ((f ≫ projectiveSpaceOver.toIntegralAtUniverse r _).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))) = a' ν := by
  set s : Fin (r + 1) → Γ(Spec (.of K), ⊤) := fun i => (Scheme.ΓSpecIso (.of K)).inv (a' i)
    with hs_def
  have hs := span_range_ΓSpecIso_inv (R := CommRingCat.of K) a' ha'
  have hP : projectiveSpacePoint (R := CommRingCat.of K) a' ha' =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs := rfl
  have hsj : s j = 1 := by
    simp only [hs_def, hj, map_one]
  have htop : ⊤ ≤ Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j) := by
    rw [Stacks.SectionsToProjectiveSpace.preimage_basicOpen, hsj, Scheme.basicOpen_one]
  have key := Stacks.ChartDictionary.appLE_chartCoord_top s hs hsj ν htop
  have hcc : Stacks.ChartDictionary.chartCoord r j ν =
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j))
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)) := by
    rw [Stacks.ChartDictionary.chartCoord, Proj.basicOpenIsoAway_hom]
    rfl
  have hPh : q ≫ f ≫ projectiveSpaceOver.toIntegralAtUniverse r _ =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse s hs := h'.trans hP
  have htop' : ⊤ ≤ (q ≫ f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j) := hPh ▸ htop
  refine ⟨fun x hx => htop' hx, ?_⟩
  have e2 := Scheme.Hom.comp_appLE q (f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) _ ⊤ htop'
  have e3 := appLE_congr' hPh _ ⊤ htop'
  have e4 := congrArg (fun φ => (Scheme.ΓSpecIso (.of K)).hom (φ.hom
      (Stacks.ChartDictionary.chartCoord r j ν))) (e2.symm.trans e3)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e4
  rw [hcc] at e4 key
  refine e4.trans ?_
  erw [key]
  simp [hs_def]

/-- **The homogeneous coordinates `a` of the `K`-point `q ≫ f` of `ℙʳ`** (given by
`projectiveSpacePoint a`) are a coordinate vector of it on the charts. -/
private theorem isCoordinatesOf_of_comp_eq {K : Type u} [Field K] {Y : Scheme.{u}} {r : ℕ}
    (f : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (q : Spec (.of K) ⟶ Y)
    (a : Fin (r + 1) → K) (ha : Ideal.span (Set.range a) = ⊤)
    (h : q ≫ f ≫ projectiveSpaceOver.toIntegralAtUniverse r _ =
      projectiveSpacePoint (R := CommRingCat.of K) a ha) :
    IsCoordinatesOf f q a := by
  classical
  refine ⟨fun h0 => ?_, fun j hj => ?_⟩
  · subst h0
    have : Ideal.span (Set.range (0 : Fin (r + 1) → K)) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨i, rfl⟩; rfl
    exact bot_ne_top (this.symm.trans ha)
  let u : Kˣ := Units.mk0 (a j)⁻¹ (inv_ne_zero hj)
  have ha' : Ideal.span (Set.range fun i => (u : K) * a i) = ⊤ := by
    rw [Stacks.SectionsToProjectiveSpace.span_range_unit_smul]; exact ha
  have h' := h.trans (projectiveSpacePoint_unit_mul (R := CommRingCat.of K) u a ha ha').symm
  have hj1 : (u : K) * a j = 1 := inv_mul_cancel₀ hj
  obtain ⟨hp, -⟩ := exists_appLE_ratio_eq f q _ ha' j j h' hj1
  have hmem : q (closedPoint K) ∈ chartOf f j :=
    hp (show closedPoint K ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
  refine ⟨hmem, fun ν => ?_⟩
  obtain ⟨hp', hval⟩ := exists_appLE_ratio_eq f q _ ha' j ν h' hj1
  simp only [ratioOf, dite_eq_left hmem]
  refine (stalkClosedPointTo_germ_eq' q _ hmem hp' _).trans (hval.trans ?_)
  simp only [u, Units.val_mk0]
  field_simp

/-- **The base change of `C ×_k C` to `K` is `C_K ×_K C_K`.** Given the base change
`C_K = C ×_k K` and `X = (C ×_k C) ×_k K` as pullback squares, the two projections
`X ⟶ C_K` induced by those of `C ×_k C` make `X` the fibre product `C_K ×_K C_K`. -/
private theorem isPullback_baseChange_prod {C CK X S T : Scheme.{u}} {fC : C ⟶ S} {fK : CK ⟶ T}
    {π : CK ⟶ C} {b : T ⟶ S} (hπ : IsPullback π fK fC b) {ι : X ⟶ pullback fC fC}
    {πX : X ⟶ T} (hX : IsPullback ι πX (pullback.fst fC fC ≫ fC) b) {pr₁ pr₂ : X ⟶ CK}
    (h₁ : pr₁ ≫ π = ι ≫ pullback.fst fC fC) (h₁' : pr₁ ≫ fK = πX)
    (h₂ : pr₂ ≫ π = ι ≫ pullback.snd fC fC) (h₂' : pr₂ ≫ fK = πX) :
    IsPullback pr₁ pr₂ fK fK := by
  have P1 : IsPullback ι pr₂ (pullback.snd fC fC) π := by
    refine IsPullback.of_bot ?_ h₂.symm hπ
    rw [h₂', ← pullback.condition]
    exact hX
  have P3 := P1.paste_horiz (IsPullback.of_hasPullback fC fC)
  refine IsPullback.of_right ?_ (h₁'.trans h₂'.symm) hπ
  rw [h₁, ← hπ.w]
  exact P3

/-- A flat morphism from a nonempty scheme to an irreducible one is dominant: its image is closed
under generalization, so it contains the generic point. -/
private theorem isDominant_of_flat {X Y : Scheme.{u}} [IrreducibleSpace Y] [Nonempty X] (f : X ⟶ Y)
    [Flat f] : IsDominant f := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hη : genericPoint Y ⤳ f x := (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap f hη
  refine ⟨?_⟩
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨x', hx'⟩)

/-- The stalk map of a dominant morphism of integral schemes is compatible with the inclusions of
the local rings into the function fields. -/
public theorem algebraMap_stalkMap_eq_functionFieldMap' {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (h : Z ⟶ X) [IsDominant h] (z : Z) (a : X.presheaf.stalk (h z)) :
    algebraMap (Z.presheaf.stalk z) Z.functionField (h.stalkMap z a) =
      functionFieldMap h (algebraMap (X.presheaf.stalk (h z)) X.functionField a) := by
  change _ = (Scheme.Hom.functionFieldMap h).hom _
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have key : X.presheaf.germ U (h.base z) hU ≫ h.stalkMap z ≫
      Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) =
      X.presheaf.germ U (h.base z) hU ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫
          Scheme.Hom.functionFieldMap h := by
    have e1 : h.stalkMap z ≫
        Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) =
        X.presheaf.stalkSpecializes (h.base.hom.map_specializes
          ((genericPoint_spec Z).specializes trivial)) ≫ h.stalkMap (genericPoint Z) :=
      (Scheme.Hom.stalkSpecializes_stalkMap h _ _ _).symm
    rw [e1, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.functionFieldMap,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact congr($key s)

/-- Two elements of local rings matched by the function field map of a dominant morphism of
integral schemes are matched by the stalk map. -/
public theorem stalkMap_eq_of_algebraMap_eq {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (h : Z ⟶ X) [IsDominant h] (z : Z) (a : X.presheaf.stalk (h z)) (b : Z.presheaf.stalk z)
    (hab : algebraMap _ Z.functionField b =
      functionFieldMap h (algebraMap (X.presheaf.stalk (h z)) X.functionField a)) :
    h.stalkMap z a = b :=
  IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField
    ((algebraMap_stalkMap_eq_functionFieldMap' h z a).trans hab.symm)

/-- The germ of a pulled-back section, read in the function field. -/
private theorem algebraMap_germ_app {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y)
    [IsDominant h] (U : Y.Opens) (x : X) (hx : x ∈ h ⁻¹ᵁ U) (t : Γ(Y, U)) :
    haveI : Nonempty U := ⟨⟨h x, hx⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (h ⁻¹ᵁ U) x hx (h.app U t)) =
      functionFieldMap h (Y.germToFunctionField U t) := by
  have : Nonempty U := ⟨⟨h x, hx⟩⟩
  have : Nonempty (h ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  change _ = (Scheme.Hom.functionFieldMap h).hom _
  rw [Scheme.Hom.functionFieldMap_germToFunctionField h le_rfl, Scheme.Hom.app_eq_appLE]

/-- A sum over the parts of the partitions, maximised over the partitions, read in `EReal` is at
most the same expression read in `ℝ`, when this is so termwise. -/
private theorem partitionSup_le_coe {X : Type*} {n i : ℕ} (L : X → EReal) (A : X → ℝ)
    (hLA : ∀ y, L y ≤ (Real.log (A y) : EReal)) (c : ℕ → Fin (n + 1) → X) :
    (Finset.univ : Finset (Nat.Partition i)).sup (fun π =>
        (π.parts.map fun l => Finset.univ.sup fun ν : Fin (n + 1) => L (c l ν)).sum) ≤
      ((⨆ π : i.Partition, (π.parts.map fun l => ⨆ ν, Real.log (A (c l ν))).sum : ℝ) : EReal) := by
  refine Finset.sup_le fun π _ => ?_
  have h1 : ∀ l, (Finset.univ.sup fun ν : Fin (n + 1) => L (c l ν)) ≤
      (((⨆ ν, Real.log (A (c l ν))) : ℝ) : EReal) := fun l =>
    Finset.sup_le fun ν _ => (hLA _).trans (EReal.coe_le_coe_iff.mpr
      (le_ciSup (f := fun ν => Real.log (A (c l ν))) (Set.finite_range _).bddAbove ν))
  calc (π.parts.map fun l => Finset.univ.sup fun ν : Fin (n + 1) => L (c l ν)).sum
      ≤ (π.parts.map fun l => (((⨆ ν, Real.log (A (c l ν))) : ℝ) : EReal)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun l _ => h1 l
    _ = (((π.parts.map fun l => ⨆ ν, Real.log (A (c l ν))).sum : ℝ) : EReal) := by
        induction π.parts using Multiset.induction_on with
        | empty => simp
        | cons a s ih => simp [ih, EReal.coe_add]
    _ ≤ _ := EReal.coe_le_coe_iff.mpr (le_ciSup (f := fun π : i.Partition =>
        (π.parts.map fun l => ⨆ ν, Real.log (A (c l ν))).sum) (Set.finite_range _).bddAbove π)

/-- Bombieri's normalised `log |y|_v` (with `log 0 = ⊥`) is at most `log` of the normalised
absolute value (with `Real.log 0 = 0`). -/
private theorem logAbs_le_log_absV {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K ⊕ FinitePlace K) (y : K) :
    (haveI := Classical.propDecidable (y = 0)
      if y = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w y))
          (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w y)) v : ℝ) : EReal)) ≤
      ((Real.log (Sum.elim (fun w : InfinitePlace K => w y ^ ((w.mult : ℝ) / finrank ℚ K))
          (fun w : FinitePlace K => w y ^ ((1 : ℝ) / finrank ℚ K)) v) : ℝ) : EReal) := by
  split_ifs with hy
  · exact bot_le
  · refine le_of_eq ?_
    congr 1
    rcases v with w | w
    · simp only [Sum.elim_inl]
      rw [Real.log_rpow (InfinitePlace.pos_iff.mpr hy)]
    · simp only [Sum.elim_inr]
      rw [Real.log_rpow (FinitePlace.pos_iff.mpr hy)]

/-- The finite-place part of a partition term built from finitely many numbers vanishes off a
finite set of places. -/
private theorem finite_support_partitionSup_real {K : Type*} [Field K] [NumberField K] {n i : ℕ}
    (S : Finset K) (c : FinitePlace K → ℕ → Fin (n + 1) → K)
    (hc : ∀ w l ν, l ≤ i → c w l ν ∈ S) :
    (Function.support fun w : FinitePlace K => ⨆ π : i.Partition,
      (π.parts.map fun l => ⨆ ν, Real.log (w (c w l ν) ^ ((1 : ℝ) / finrank ℚ K))).sum).Finite := by
  classical
  have hfin : (⋃ y ∈ S.filter (· ≠ 0), Function.mulSupport fun w : FinitePlace K => w y).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun y hy =>
      FinitePlace.hasFiniteMulSupport (Finset.mem_filter.mp hy).2
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  have hdeg : (1 : ℝ) / finrank ℚ K ≠ 0 := by
    have : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
    positivity
  have hzero : ∀ l ν, l ≤ i → Real.log (w (c w l ν) ^ ((1 : ℝ) / finrank ℚ K)) = 0 := by
    intro l ν hl
    by_cases h0 : c w l ν = 0
    · rw [h0, map_zero, Real.zero_rpow hdeg, Real.log_zero]
    · have h1 : w (c w l ν) = 1 := by
        by_contra h1
        exact hnot (Set.mem_biUnion (x := c w l ν)
          (Finset.mem_filter.mpr ⟨hc w l ν hl, h0⟩) h1)
      rw [h1, Real.one_rpow, Real.log_one]
  have hπ : ∀ π : i.Partition,
      (π.parts.map fun l => ⨆ ν, Real.log (w (c w l ν) ^ ((1 : ℝ) / finrank ℚ K))).sum = 0 := by
    intro π
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hx
    have hli : l ≤ i := π.parts_sum ▸ Multiset.le_sum_of_mem hl
    simp only [hzero l _ hli, ciSup_const]
  simp only [hπ, ciSup_const]

/-- Functoriality of the function field maps of dominant morphisms. -/
public theorem functionFieldMap_comp_apply' {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  exact (congrArg (fun φ => φ.hom t) (Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A)
    (genericPoint B) (genericPoint C) (map_genericPoint_of_isDominant a)
    (map_genericPoint_of_isDominant b) (map_genericPoint_of_isDominant (a ≫ b)))).symm

/-- Morphisms to `ℙʳ_S` agree when they agree over `S` and on the integral model. -/
private theorem projectiveSpaceOver_hom_ext {S Y : Scheme.{u}} {r : ℕ}
    {g h : Y ⟶ projectiveSpaceOver r S}
    (h₁ : g ≫ (projectiveSpaceOver r S ↘ S) = h ≫ (projectiveSpaceOver r S ↘ S))
    (h₂ : g ≫ projectiveSpaceOver.toIntegralAtUniverse r S =
      h ≫ projectiveSpaceOver.toIntegralAtUniverse r S) : g = h :=
  pullback.hom_ext h₁ h₂

/-- **A point outside the exceptional set has the uniformizer `ξ₁₀ - ξ₁₀(z)`**: there is a germ
`g` of `ξ₁₀ = x₁ / x₀` at `z` with `g - g(z)` generating the maximal ideal. -/
public theorem exists_uniformizer_of_not_mem_exceptionalSet {K : Type u} [Field K]
    {CK : Scheme.{u}} (fK : CK ⟶ Spec (.of K)) [IsCurve K fK] [IsLocallyNoetherian CK]
    [IsIntegral CK] (D : CK →₀ ℤ) {n : ℕ} (x : Fin (n + 1) → CK.functionField)
    (ht : letI := functionFieldAlgebra K fK; Transcendental K (x 1 / x 0))
    (zK : Spec (.of K) ⟶ CK) (hzK : zK ≫ fK = 𝟙 _) (hz : zK ∉ exceptionalSet K fK D x ht) :
    ∃ g : CK.presheaf.stalk (zK (closedPoint K)), algebraMap _ CK.functionField g = x 1 / x 0 ∧
      maximalIdeal (CK.presheaf.stalk (zK (closedPoint K))) = Ideal.span {(g -
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
          CK.presheaf.germ ⊤ (zK (closedPoint K)) trivial).hom
          ((Scheme.stalkClosedPointTo zK).hom g))} := by
  classical
  simp only [exceptionalSet, Set.mem_ofPred_eq, not_and, not_or] at hz
  obtain ⟨h1, h2, -, -⟩ := hz hzK
  have hNU := h2 h1
  push Not at hNU
  obtain ⟨g, hg, a, ha⟩ := hNU
  refine ⟨g, hg, ?_⟩
  letI : CK.Over (Spec (.of K)) := ⟨fK⟩
  have hmem : g - const (K := K) (zK (closedPoint K)) a ∈
      maximalIdeal (CK.presheaf.stalk (zK (closedPoint K))) := by
    rw [ha]; exact Ideal.mem_span_singleton_self _
  have hev := ev_eq_zero_of_mem zK hmem
  rw [map_sub, ev_const zK hzK a, sub_eq_zero] at hev
  rw [hev]; exact ha

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- On a base change `π : C_K ⟶ C`, the chart functions of the base change `φNP'` of `φNP` are
the pull-backs of those of `φNP`, read in the function field. -/
private theorem algebraMap_ratioOf_baseChange {k K : Type u} [Field k] [Field K]
    {C CK : Scheme.{u}} [IsIntegral C] [IsIntegral CK] (π : CK ⟶ C) [IsDominant π] {n : ℕ}
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (φNP' : CK ⟶ projectiveSpaceOver n (Spec (.of K)))
    (hφ : φNP' ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
      π ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _)
    (y : CK) (ν j : Fin (n + 1)) (hy : y ∈ chartOf φNP' j) (ξ : C.functionField)
    (hξ : ∀ _ : Nonempty (φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X j))),
      C.germToFunctionField _ (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n _).app _
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))) = ξ) :
    algebraMap _ CK.functionField (ratioOf φNP' y ν j) = functionFieldMap π ξ := by
  set G := φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) with hG
  set B := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X j) with hB
  set T := Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
          (HomogeneousLocalization.Away.mk _
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
            (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)) with hT
  have key : ∀ (g : CK ⟶ projectiveSpaceAtUniverse.{u} n) (hg : g = π ≫ G) (hy' : y ∈ g ⁻¹ᵁ B),
      CK.presheaf.germ (g ⁻¹ᵁ B) y hy' (g.app B T) =
        CK.presheaf.germ (π ⁻¹ᵁ (G ⁻¹ᵁ B)) y (by subst hg; exact hy') (π.app _ (G.app B T)) := by
    intro g hg hy'
    subst hg
    rfl
  have hy' : y ∈ (φNP' ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ B := hy
  simp only [ratioOf, dite_eq_left hy]
  refine (congrArg (algebraMap _ CK.functionField) (key _ hφ hy')).trans ?_
  refine (algebraMap_germ_app π _ y _ (G.app B T)).trans ?_
  congr 1
  exact hξ ⟨⟨π y, by rw [hφ] at hy'; exact hy'⟩⟩

/-- For every place, an index at which a nonzero vector is largest. -/
private theorem exists_index_absV_max {K : Type u} [Field K] [NumberField K] {n : ℕ}
    (a : Fin (n + 1) → K) (ha : a ≠ 0) :
    ∃ j : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1),
      ∀ v, a (j v) ≠ 0 ∧ ∀ ν, absV v (a ν) ≤ absV v (a (j v)) := by
  have : ∀ v, ∃ j, ∀ ν, absV v (a ν) ≤ absV v (a j) := fun v => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => absV v (a j))
      Finset.univ_nonempty
    exact ⟨j, fun ν => hj ν (Finset.mem_univ _)⟩
  choose j hj using this
  refine ⟨j, fun v => ⟨fun h0 => ha (funext fun ν => ?_), hj v⟩⟩
  have := hj v ν
  rw [h0, map_zero] at this
  exact (AbsoluteValue.nonpos_iff _).mp this

/-- `log |x / y|_v ≤ 0` when `|x|_v ≤ |y|_v`. -/
private theorem logAbs_div_le_zero {K : Type u} [Field K] [NumberField K]
    (v : InfinitePlace K ⊕ FinitePlace K) {x y : K} (hy : y ≠ 0) (h : absV v x ≤ absV v y) :
    (haveI := Classical.propDecidable (x / y = 0)
      if x / y = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w (x / y)))
          (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w (x / y))) v : ℝ) : EReal)) ≤
        0 := by
  split_ifs with h0
  · exact bot_le
  · have hle : Real.log (absV v (x / y)) ≤ 0 := by
      rw [map_div₀]
      exact Real.log_nonpos (div_nonneg (by positivity) (by positivity))
        (div_le_one_of_le₀ h (by positivity))
    have hdeg : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
    refine EReal.coe_nonpos.mpr ?_
    rcases v with w | w
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hle

/-- The normalised absolute value of `x / y` is at most one when `|x|_v ≤ |y|_v`. -/
private theorem absV'_div_le_one {K : Type u} [Field K] [NumberField K]
    (v : InfinitePlace K ⊕ FinitePlace K) {x y : K} (hy : y ≠ 0) (h : absV v x ≤ absV v y) :
    Sum.elim (fun w : InfinitePlace K => w (x / y) ^ ((w.mult : ℝ) / finrank ℚ K))
      (fun w : FinitePlace K => w (x / y) ^ ((1 : ℝ) / finrank ℚ K)) v ≤ 1 := by
  have hle : absV v (x / y) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ h (by positivity)
  have hdeg : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rcases v with w | w
  · exact Real.rpow_le_one (by positivity) hle (by positivity)
  · exact Real.rpow_le_one (by positivity) hle (by positivity)

/-- At an index `j` where the coordinate vector is largest at `v`, every `T_ν / T_j` has
`log |·|_v ≤ 0` at the point. -/
private theorem logAbs_ratioOf_le_zero {K : Type u} [Field K] [NumberField K] {Y : Scheme.{u}}
    {r : ℕ} {f : Y ⟶ projectiveSpaceOver r (Spec (.of K))} {q : Spec (.of K) ⟶ Y}
    {a : Fin (r + 1) → K} (hc : IsCoordinatesOf f q a) (v : InfinitePlace K ⊕ FinitePlace K)
    {j : Fin (r + 1)} (hj : a j ≠ 0) (hmax : ∀ ν, absV v (a ν) ≤ absV v (a j)) (ν : Fin (r + 1)) :
    (haveI := Classical.propDecidable
        ((Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν j) = 0)
      if (Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν j) = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K *
            Real.log (w ((Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν j))))
          (fun w : FinitePlace K => 1 / finrank ℚ K *
            Real.log (w ((Scheme.stalkClosedPointTo q).hom (ratioOf f (q (closedPoint K)) ν j))))
          v : ℝ) : EReal)) ≤ 0 := by
  rw [(hc.2 j hj).2 ν]
  exact logAbs_div_le_zero v hj (hmax ν)

end Transport

/-- The height `h_V` of `oldVojtaHeight` with `d₁ = N δ₁ - d`, `d₂ = N δ₂ - d` and `s = 1`. -/
private lemma oldVojtaHeight_one {Y : Type*} (N : ℕ) (hN : 0 < N) (hNP : Y → ℝ)
    (hB : Y × Y → ℝ) (δ₁ δ₂ d : ℕ) (p : Y × Y) :
    oldVojtaHeight 1 N hNP hB (N * δ₁ - d) (N * δ₂ - d) d p =
      δ₁ * hNP p.1 + δ₂ * hNP p.2 - d * hB p := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [oldVojtaHeight, one_mul, sub_add_cancel, Int.cast_mul, Int.cast_natCast]
  field_simp

/-- **Bombieri's Lemma 4 for given coordinate vectors of the points**, on a surface `X` given
with a pullback square `X ≅ C ×_K C` and a morphism `ψ` whose components are `φNP ∘ prᵢ`, with
the sums over the places of the Taylor-coefficient terms bounded by real functions `T₁, T₂`. -/
private theorem bound_of_coordinates {K : Type u} [Field K] [NumberField K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))]
    [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    {X : Scheme.{u}} [X.Over (Spec (.of K))] [IrreducibleSpace X] {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    (hXo : pr₁ ≫ (C ↘ Spec (.of K)) = X ↘ Spec (.of K))
    {n m : ℕ} (φNP : C ⟶ projectiveSpaceOver n (Spec (.of K))) [φNP.IsOver (Spec (.of K))]
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
      (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP) (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of K)))
    (N : ℕ) (hN : 0 < N) (δ₁ δ₂ d : ℕ) (hd : 1 ≤ d) (hδ₁pos : 0 < δ₁) (hδ₂pos : 0 < δ₂)
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of K), ⊤))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s F)
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    (ς : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)))
    (ς' : C.presheaf.stalk ((p ≫ pr₂) (closedPoint K)))
    (hς : maximalIdeal (C.presheaf.stalk ((p ≫ pr₁) (closedPoint K))) = Ideal.span {ς})
    (hς' : maximalIdeal (C.presheaf.stalk ((p ≫ pr₂) (closedPoint K))) = Ideal.span {ς'})
    (i₁ i₂ : ℕ)
    (hadm : IsAdmissiblePair ψ φB δ₁ δ₂ d s p
      (pr₁.stalkMap (p (closedPoint K)) ς) (pr₂.stalkMap (p (closedPoint K)) ς') i₁ i₂)
    (az aw : Fin (n + 1) → K) (ap : Fin (m + 1) → K)
    (j₁ j₂ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1))
    (T₁ T₂ : InfinitePlace K ⊕ FinitePlace K → ℝ)
    (hT₁ : (Function.support fun w : FinitePlace K => T₁ (.inr w)).Finite)
    (hT₂ : (Function.support fun w : FinitePlace K => T₂ (.inr w)).Finite) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    -- Bombieri's normalised `log |x|_v`, with `log 0 = ⊥`
    let logAbs : InfinitePlace K ⊕ FinitePlace K → K → EReal := fun v x =>
      haveI := Classical.propDecidable (x = 0)
      if x = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w x))
          (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w x)) v : ℝ) : EReal)
    -- the `v`-term `max_{i_λ} ∑_λ max_ν log |∂_{i_λ} ξ_{ν j}(q)|_v` at the point `q` of `C`
    let partitionTerm : ∀ q : Spec (.of K) ⟶ C, C.presheaf.stalk (q (closedPoint K)) → ℕ →
        (InfinitePlace K ⊕ FinitePlace K → Fin (n + 1)) →
        InfinitePlace K ⊕ FinitePlace K → EReal := fun q ϖ i j v =>
      (Finset.univ : Finset (Nat.Partition i)).sup fun π =>
        (π.parts.map fun l => Finset.univ.sup fun ν : Fin (n + 1) =>
          logAbs v (taylorCoeff q ϖ (ratioOf φNP (q (closedPoint K)) ν (j v)) l)).sum
    let z := p ≫ pr₁
    let w := p ≫ pr₂
    -- `h(F)`: the absolute height of the vector of all coefficients of all `F_i`
    let hF : ℝ := Height.logHeight (fun c : Σ i, (F i).support =>
        (Scheme.ΓSpecIso (.of K)).hom ((F c.1).coeff c.2)) / finrank ℚ K
    IsCoordinatesOf φNP z az → IsCoordinatesOf φNP w aw → IsCoordinatesOf φB p ap →
    (∀ v, z (closedPoint K) ∈ chartOf φNP (j₁ v)) → (∀ v, w (closedPoint K) ∈ chartOf φNP (j₂ v)) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo z).hom
      (ratioOf φNP (z (closedPoint K)) ν (j₁ v))) ≤ 0) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo w).hom
      (ratioOf φNP (w (closedPoint K)) ν (j₂ v))) ≤ 0) →
    (∀ v, partitionTerm z ς i₁ j₁ v ≤ (T₁ v : EReal)) →
    (∀ v, partitionTerm w ς' i₂ j₂ v ≤ (T₂ v : EReal)) →
    -hF - n * Real.log ((δ₁ + n) * (δ₂ + n)) - ∑ᶠ v, T₁ v - ∑ᶠ v, T₂ v -
        ((δ₁ + δ₂ + i₁ + i₂ : ℕ) : ℝ) ≤
      δ₁ * (Height.logHeight az / finrank ℚ K) + δ₂ * (Height.logHeight aw / finrank ℚ K) -
        d * (Height.logHeight ap / finrank ℚ K) := by
  intro logAbs partitionTerm z w hFt hcz' hcw' hcp' hj₁' hj₂' hjv hjv' hTP₁ hTP₂
  classical
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hX.flip inferInstance
  have : Smooth (X ↘ Spec (.of K)) := hXo ▸ inferInstance
  have := isRegularLocalRing_stalk (X ↘ Spec (.of K)) p (comp_over_eq_id p)
  have hm := maximalIdeal_stalk_pullback hX hXo p hς hς'
  have hdim := ringKrullDim_stalk_pullback hX hXo p hς hς'
  obtain ⟨i₀, j₀, j₀', hx₀, g₀, hg₀, hb, hvanish⟩ := hadm
  have hz₀ : z (closedPoint K) ∈ chartOf φNP j₀ := by
    have := hx₀.2.1; rw [hψ₁] at this; exact this
  have hw₀ : w (closedPoint K) ∈ chartOf φNP j₀' := by
    have := hx₀.2.2; rw [hψ₂] at this; exact this
  have hp₀ : p (closedPoint K) ∈ chartOf φB i₀ := hx₀.1
  set x := az with hx_def
  set x' := aw with hx'_def
  set y := ap with hy_def
  have hy₀ : y i₀ ≠ 0 := hcp'.ne_zero hp₀
  have hx₀' : x j₀ ≠ 0 := hcz'.ne_zero hz₀
  have hx₀'' : x' j₀' ≠ 0 := hcw'.ne_zero hw₀
  let a : Γ(Spec (.of K), ⊤) → K := fun t => (Scheme.ΓSpecIso (.of K)).hom t
  let cX : Γ(Spec (.of K), ⊤) →+* X.presheaf.stalk (p (closedPoint K)) :=
    (const (p (closedPoint K))).comp (Scheme.ΓSpecIso (.of K)).hom.hom
  let A : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ) → K := fun j e =>
    taylorCoeff z ς (∏ ν, ratioOf φNP (z (closedPoint K)) ν j ^ e (Sum.inl ν)) i₁
  let B : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ) → K := fun j e =>
    taylorCoeff w ς' (∏ ν, ratioOf φNP (w (closedPoint K)) ν j ^ e (Sum.inr ν)) i₂
  let D : Fin (m + 1) → Fin (n + 1) → Fin (n + 1) → K := fun i j j' =>
    ∑ e ∈ (F i).support, a ((F i).coeff e) * (A j e * B j' e)
  have hVF : ∀ i j j', p (closedPoint K) ∈ chartOf φB i → z (closedPoint K) ∈ chartOf φNP j →
      w (closedPoint K) ∈ chartOf φNP j' →
      taylorCoeff₂ p (pr₁.stalkMap (p (closedPoint K)) ς) (pr₂.stalkMap (p (closedPoint K)) ς')
          g₀ i₁ i₂ =
        (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j₀') ^ δ₂ *
          taylorCoeff₂ p (pr₁.stalkMap (p (closedPoint K)) ς)
            (pr₂.stalkMap (p (closedPoint K)) ς')
            ((F i).eval₂ cX (Sum.elim
              (fun ν => pr₁.stalkMap (p (closedPoint K)) (ratioOf φNP (z (closedPoint K)) ν j))
              (fun ν => pr₂.stalkMap (p (closedPoint K))
                (ratioOf φNP (w (closedPoint K)) ν j')))) i₁ i₂ := by
    intro i j j' hpi hzj hwj'
    have hstruct : ψ ≫ pullback.fst (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) ≫
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) = X ↘ Spec (.of K) := by
      rw [← Category.assoc, hψ₁, Category.assoc, comp_over φNP (Spec (.of K)), hXo]
    refine (BombieriVojta.taylorCoeff₂_eq_mul_taylorCoeff₂_eval₂ _ φB δ₁ δ₂ d s F hF p hdim hm
      i₀ i j₀ j₀' j j' hx₀ ⟨hpi, by rw [hψ₁]; exact hzj, by rw [hψ₂]; exact hwj'⟩ g₀ hg₀ i₁ i₂
      hvanish x x' y ⟨hcz'.1, fun k hk ν => (hcz'.eq_mul_comp pr₁ φNP _ hψ₁ p hk ν).trans
        (congrArg _ (congrArg _ (germ_app_eq_ratioOf _ _ _ _ hk).symm))⟩
      ⟨hcw'.1, fun k hk ν => (hcw'.eq_mul_comp pr₂ φNP _ hψ₂ p hk ν).trans
        (congrArg _ (congrArg _ (germ_app_eq_ratioOf _ _ _ _ hk).symm))⟩
      ⟨hcp'.1, fun k hk ν => (hcp'.eq_mul hk ν).trans
        (congrArg _ (congrArg _ (germ_app_eq_ratioOf _ _ _ _ hk).symm))⟩).trans ?_
    refine congrArg _ (congrArg (fun t => taylorCoeff₂ p _ _ t i₁ i₂) ?_)
    congr 1
    · exact RingHom.ext fun t => appTop_germ_eq_const _ hstruct _ t
    · funext σ
      rcases σ with ν | ν
      · exact (germ_app_eq_ratioOf _ _ _ _ _).trans (ratioOf_comp _ _ _ hψ₁ _ ν j)
      · exact (germ_app_eq_ratioOf _ _ _ _ _).trans (ratioOf_comp _ _ _ hψ₂ _ ν j')
  have hval : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 →
      taylorCoeff₂ p (pr₁.stalkMap (p (closedPoint K)) ς) (pr₂.stalkMap (p (closedPoint K)) ς')
          g₀ i₁ i₂ =
        (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j₀') ^ δ₂ * D i j j' := by
    intro i j j' hi hj hj'
    rw [hVF i j j' (hcp'.2 i hi).1 (hcz'.2 j hj).1 (hcw'.2 j' hj').1]
    exact congrArg _
      (taylorCoeff₂_eval₂_sumElim hX hXo p hς hς' (F i) cX a (fun t => rfl) _ _ i₁ i₂)
  have : z.IsOver (Spec (.of K)) := ⟨by
    change (p ≫ pr₁) ≫ _ = _
    rw [Category.assoc, hXo]
    exact comp_over p (Spec (.of K))⟩
  have : w.IsOver (Spec (.of K)) := ⟨by
    change (p ≫ pr₂) ≫ _ = _
    rw [Category.assoc, ← hX.w, hXo]
    exact comp_over p (Spec (.of K))⟩
  let coef : (Σ i, (F i).support) → K := fun c =>
    (Scheme.ΓSpecIso (.of K)).hom ((F c.1).coeff c.2)
  let G : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v => wt v * Real.log (⨆ c, absV v (coef c))
  let M : ℕ := ((δ₁ + 1) * (δ₂ + 1)) ^ n
  let Pv : InfinitePlace K ⊕ FinitePlace K → EReal := fun v => partitionTerm z ς i₁ j₁ v
  let Pv' : InfinitePlace K ⊕ FinitePlace K → EReal := fun v => partitionTerm w ς' i₂ j₂ v
  let R₀ : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v =>
    archLog v M + G v + ((Pv v).toReal + archLog v ((2 : ℝ) ^ (δ₁ + i₁))) +
      ((Pv' v).toReal + archLog v ((2 : ℝ) ^ (δ₂ + i₂)))
  let R : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v =>
    archLog v M + G v + (T₁ v + archLog v ((2 : ℝ) ^ (δ₁ + i₁))) +
      (T₂ v + archLog v ((2 : ℝ) ^ (δ₂ + i₂)))
  have hPtop : ∀ v, Pv v ≠ ⊤ := fun v =>
    partitionSup_ne_top _ _ fun l => finset_sup_ne_top _ _ fun ν => logAbsV_ne_top _ _
  have hPtop' : ∀ v, Pv' v ≠ ⊤ := fun v =>
    partitionSup_ne_top _ _ fun l => finset_sup_ne_top _ _ fun ν => logAbsV_ne_top _ _
  have hx₁ : ∀ v, x (j₁ v) ≠ 0 := fun v => hcz'.ne_zero (hj₁' v)
  have hx₂ : ∀ v, x' (j₂ v) ≠ 0 := fun v => hcw'.ne_zero (hj₂' v)
  have hD0 : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 → D i j j' ≠ 0 := by
    intro i j j' hi hj hj' h
    exact hb (by rw [hval i j j' hi hj hj', h, mul_zero])
  have hcoef : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 → coef ≠ 0 := by
    intro i j j' hi hj hj' h
    apply hD0 i j j' hi hj hj'
    refine Finset.sum_eq_zero fun e he => ?_
    have : coef ⟨i, ⟨e, he⟩⟩ = 0 := congrFun h _
    change a ((F i).coeff e) * _ = 0
    rw [show a ((F i).coeff e) = coef ⟨i, ⟨e, he⟩⟩ from rfl, this, zero_mul]
  have hcoef₀ := hcoef i₀ j₀ j₀' hy₀ hx₀' hx₀''
  have key : ∀ v i, y i ≠ 0 →
      Pv v ≠ ⊥ ∧ Pv' v ≠ ⊥ ∧ wt v * Real.log (absV v (D i (j₁ v) (j₂ v))) ≤ R₀ v := by
    intro v i hi
    have hD := hD0 i _ _ hi (hx₁ v) (hx₂ v)
    have hGv : (Finset.univ.sup fun c => logAbsV v (coef c)) = ((G v : ℝ) : EReal) :=
      sup_logAbsV_eq v hcoef₀
    have hA : ∀ e ∈ (F i).support, logAbsV v (A (j₁ v) e) ≤
        Pv v + ((archLog v ((2 : ℝ) ^ (δ₁ + i₁)) : ℝ) : EReal) := by
      intro e he
      have h := logAbs_taylorCoeff_prod_pow_le z ς hς v
        (fun ν => ratioOf φNP (z (closedPoint K)) ν (j₁ v)) (fun ν => e (Sum.inl ν)) δ₁
        (sum_exponents_eq (hF.1 i) he).1 hδ₁pos i₁ (hjv v)
      rw [← sumElim_logAbsV_two_pow]
      exact h
    have hB : ∀ e ∈ (F i).support, logAbsV v (B (j₂ v) e) ≤
        Pv' v + ((archLog v ((2 : ℝ) ^ (δ₂ + i₂)) : ℝ) : EReal) := by
      intro e he
      have h := logAbs_taylorCoeff_prod_pow_le w ς' hς' v
        (fun ν => ratioOf φNP (w (closedPoint K)) ν (j₂ v)) (fun ν => e (Sum.inr ν)) δ₂
        (sum_exponents_eq (hF.1 i) he).2 hδ₂pos i₂ (hjv' v)
      rw [← sumElim_logAbsV_two_pow]
      exact h
    have hf : ∀ e ∈ (F i).support, logAbsV v (a ((F i).coeff e)) ≤ ((G v : ℝ) : EReal) := by
      intro e he
      rw [← hGv]
      exact Finset.le_sup (f := fun c => logAbsV v (coef c)) (Finset.mem_univ ⟨i, ⟨e, he⟩⟩)
    have hbound := logAbsV_sum_mul_le v (F i).support (fun e => a ((F i).coeff e))
      (A (j₁ v)) (B (j₂ v)) (M := M) (card_support_le (hF.1 i)) hf hA hB
    exact real_of_logAbsV_le v hD (hPtop v) (hPtop' v) hbound
  have hPne : ∀ v, Pv v ≠ ⊥ := fun v => (key v i₀ hy₀).1
  have hPne' : ∀ v, Pv' v ≠ ⊥ := fun v => (key v i₀ hy₀).2.1
  have hPT₁ : ∀ v, (Pv v).toReal ≤ T₁ v := fun v =>
    (EReal.toReal_le_toReal (hTP₁ v) (hPne v) (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
  have hPT₂ : ∀ v, (Pv' v).toReal ≤ T₂ v := fun v =>
    (EReal.toReal_le_toReal (hTP₂ v) (hPne' v) (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
  have key' : ∀ v i, y i ≠ 0 → wt v * Real.log (absV v (D i (j₁ v) (j₂ v))) ≤ R v := by
    intro v i hi
    refine (key v i hi).2.2.trans ?_
    simp only [R₀, R]
    linarith [hPT₁ v, hPT₂ v]
  have hGf : (Function.support fun w' : FinitePlace K => G (.inr w')).Finite :=
    Set.Finite.subset (LE_hasFiniteSupport_log_iSup hcoef₀) (Function.support_mul_subset_right _ _)
  have hAf : ∀ M' : ℝ, (Function.support fun w' : FinitePlace K =>
      archLog (.inr w') M').Finite := fun M' => by simp [archLog_inr]
  have hRf : (Function.support fun w' : FinitePlace K => R (.inr w')).Finite := by
    refine ((hGf.union hT₁).union hT₂).subset fun w' hw' => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    apply hw'
    simp only [R, archLog_inr, h.1.1, h.1.2, h.2]
    ring
  have hmain := neg_finsum_le_localExpression hcp'.1 δ₁ δ₂ d hb hy₀ hx₀' hx₀'' D hval j₁ j₂
    hx₁ hx₂ R key' hRf
  have hloc := vojtaHeight_eq_sum_iInf_iSup_log K (fun b : Bool => cond b x x')
    (fun _ : Bool × Bool => y) 1 le_rfl N hN (N * δ₁ - d) (N * δ₂ - d) d
    (by exact_mod_cast hd) δ₁ δ₂ (by ring) (by ring) hδ₁pos hδ₂pos true false hcz'.1 hcw'.1 hcp'.1
  simp only [Bool.cond_true, Bool.cond_false] at hloc
  rw [← hloc, oldVojtaHeight_one N hN] at hmain
  simp only [Bool.cond_true, Bool.cond_false] at hmain
  have fin_add : ∀ {u u' : InfinitePlace K ⊕ FinitePlace K → ℝ}, (Function.support u).Finite →
      (Function.support u').Finite → (Function.support fun v => u v + u' v).Finite :=
    fun hu hu' => (hu.union hu').subset (Function.support_add _ _)
  have h1 := finite_support_of_inr (f := fun v => archLog v (M : ℝ)) (hAf (M : ℝ))
  have h2 := finite_support_of_inr (f := G) hGf
  have h3 := finite_support_of_inr (f := T₁) hT₁
  have h4 := finite_support_of_inr (f := fun v => archLog v ((2 : ℝ) ^ (δ₁ + i₁)))
    (hAf ((2 : ℝ) ^ (δ₁ + i₁)))
  have h5 := finite_support_of_inr (f := T₂) hT₂
  have h6 := finite_support_of_inr (f := fun v => archLog v ((2 : ℝ) ^ (δ₂ + i₂)))
    (hAf ((2 : ℝ) ^ (δ₂ + i₂)))
  have hR : ∑ᶠ v, R v = ((∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v (M : ℝ)) +
        ∑ᶠ v, G v) +
      ((∑ᶠ v, T₁ v) +
        ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v ((2 : ℝ) ^ (δ₁ + i₁))) +
      ((∑ᶠ v, T₂ v) +
        ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v ((2 : ℝ) ^ (δ₂ + i₂))) := by
    rw [finsum_add_distrib (fin_add (fin_add h1 h2) (fin_add h3 h4)) (fin_add h5 h6),
      finsum_add_distrib (fin_add h1 h2) (fin_add h3 h4), finsum_add_distrib h1 h2,
      finsum_add_distrib h3 h4, finsum_add_distrib h5 h6]
  have hGs : ∑ᶠ v, G v = hFt := finsum_wt_log_iSup hcoef₀
  have hMs := sum_archLog (K := K) (M : ℝ)
  have h2s := sum_archLog_two_pow_le (K := K) (δ₁ + i₁)
  have h2s' := sum_archLog_two_pow_le (K := K) (δ₂ + i₂)
  have hlogM : Real.log (M : ℝ) ≤ n * Real.log ((δ₁ + n) * (δ₂ + n)) := by
    simp only [M, Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.log_pow]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (Nat.cast_nonneg _)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      gcongr
  push_cast at h2s h2s' ⊢
  linarith

/-- The arithmetic closing Bombieri's Lemma 6: Lemma 4 with the sums `t₁, t₂` of the
Taylor-coefficient terms bounded as in Lemma 5 gives the bound with `c₄ = max c₈ (c₉ + 1)`. -/
private theorem sub_max_mul_le_of_finsum_le {hF L t₁ t₂ δ₁ δ₂ i₁ i₂ c₈ c₉ nz nw R : ℝ}
    (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂)
    (hmain : -hF - L - t₁ - t₂ - (δ₁ + δ₂ + i₁ + i₂) ≤ R)
    (h₁ : t₁ ≤ c₈ * i₁ * nz ^ 2 + c₉ * i₁) (h₂ : t₂ ≤ c₈ * i₂ * nw ^ 2 + c₉ * i₂) :
    -hF - max c₈ (c₉ + 1) * (i₁ * nz ^ 2 + i₂ * nw ^ 2 + i₁ + i₂) - (δ₁ + δ₂) - L ≤ R := by
  have e1 := mul_le_mul_of_nonneg_right (le_max_left c₈ (c₉ + 1)) (mul_nonneg hi₁ (sq_nonneg nz))
  have e2 := mul_le_mul_of_nonneg_right (le_max_left c₈ (c₉ + 1)) (mul_nonneg hi₂ (sq_nonneg nw))
  have e3 := mul_le_mul_of_nonneg_right (le_max_right c₈ (c₉ + 1)) hi₁
  have e4 := mul_le_mul_of_nonneg_right (le_max_right c₈ (c₉ + 1)) hi₂
  have hc : max c₈ (c₉ + 1) * (i₁ * nz ^ 2 + i₂ * nw ^ 2 + i₁ + i₂) =
      max c₈ (c₉ + 1) * (i₁ * nz ^ 2) + max c₈ (c₉ + 1) * (i₂ * nw ^ 2) +
        max c₈ (c₉ + 1) * i₁ + max c₈ (c₉ + 1) * i₂ := by ring
  have h₁' : c₈ * i₁ * nz ^ 2 = c₈ * (i₁ * nz ^ 2) := by ring
  have h₂' : c₈ * i₂ * nw ^ 2 = c₈ * (i₂ * nw ^ 2) := by ring
  rw [hc]
  linarith only [hmain, h₁, h₂, h₁', h₂', e1, e2, e3, e4]

private theorem solution {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (Kbar : Type u) [Field Kbar] [Algebra k Kbar] [IsAlgClosure k Kbar]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
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
          x ν / x j) :
    ∃ c₄ : ℝ, ∀ (sB : ℕ) (_hsB : 1 ≤ sB) {m : ℕ}
      (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
      (_hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
        pullback.fst X.f X.f ≫ X.f)
      [IsClosedImmersion φB],
    ∀ (d₁ d₂ d δ₁ δ₂ : ℕ) (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂) (_hd : 0 < d)
      (_hδd₁ : d₁ + sB * d = N * δ₁) (_hδd₂ : d₂ + sB * d = N * δ₂),
    ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] Kbar)
        -- the base change `C_K` of the curve, for reading `z, w ∉ Z`
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
        (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K fK; Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        -- the surface `S = (C ×_k C)_K` and the base changes `ψ, φ` of `φNP × φNP, φB`
        (S : Scheme.{u}) (ιS : S ⟶ pullback X.f X.f) (πS : S ⟶ Spec (.of K))
        (_hS : IsPullback ιS πS (pullback.fst X.f X.f ≫ X.f)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsIntegral S] [IsDominant (ιS ≫ pullback.fst X.f X.f)]
        [IsDominant (ιS ≫ pullback.snd X.f X.f)]
        (ψ : S ⟶ pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
        (_hψπ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) = πS)
        (_hψ₁ : ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.fst _ _ ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (_hψ₂ : ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.snd _ _ ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (φ : S ⟶ projectiveSpaceOver m (Spec (.of K)))
        (_hφπ : φ ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) = πS)
        (_hφ : φ ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
          ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
        -- the section `s` and its representative `F`
        (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
        (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of K), ⊤))
        (_hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F)
        -- the point `p = (z, w)`, with `z, w` outside the exceptional set
        (p : Spec (.of K) ⟶ S) (_hp : p ≫ πS = 𝟙 _)
        (z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)
        (_hpz : p ≫ ιS ≫ pullback.fst _ _ = z.left) (_hpw : p ≫ ιS ≫ pullback.snd _ _ = w.left)
        (zK wK : Spec (.of K) ⟶ CK) (_hzK : zK ≫ fK = 𝟙 _) (_hwK : wK ≫ fK = 𝟙 _)
        (_hzC : zK ≫ π = z.left) (_hwC : wK ≫ π = w.left)
        (_hz : zK ∉ exceptionalSet K fK DK xK hξ₁₀)
        (_hw : wK ∉ exceptionalSet K fK DK xK hξ₁₀)
        -- the points of `C(k̄)` over `z` and `w`, for the Néron norm
        (zbar wbar : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Kbar))) ⟶ Over.mk X.f)
        (_hzbar : zbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ z.left)
        (_hwbar : wbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ w.left)
        -- the germs at `p` of `ξ₁₀ ∘ pr₁` and `ξ'₁₀ = ξ₁₀ ∘ pr₂`
        (s₁ s₂ : S.presheaf.stalk (p (closedPoint K)))
        (_hs₁ : algebraMap _ S.functionField s₁ =
          functionFieldMap (ιS ≫ pullback.fst _ _) (x 1 / x 0))
        (_hs₂ : algebraMap _ S.functionField s₂ =
          functionFieldMap (ιS ≫ pullback.snd _ _) (x 1 / x 0))
        (i₁ i₂ : ℕ),
      letI : S.Over (Spec (.of K)) := ⟨πS⟩
      let ev : S.presheaf.stalk (p (closedPoint K)) →+* K := (Scheme.stalkClosedPointTo p).hom
      let c : K →+* S.presheaf.stalk (p (closedPoint K)) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ πS.appTop ≫
          S.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom
      BombieriVojta.IsAdmissiblePair ψ φ δ₁ δ₂ d s p (s₁ - c (ev s₁)) (s₂ - c (ev s₂)) i₁ i₂ →
      -- coordinates of `φNP(z)`, `φNP(w)` and `φB(z, w)`
      ∀ (a b : Fin (n + 1) → K) (ha : Ideal.span (Set.range a) = ⊤)
        (hb : Ideal.span (Set.range b) = ⊤) (e : Fin (m + 1) → K)
        (he : Ideal.span (Set.range e) = ⊤),
        z.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) a ha →
        w.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) b hb →
        p ≫ ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) e he →
        let hF : ℝ := Height.logHeight (fun α : (i : Fin (m + 1)) × (F i).support =>
          (Scheme.ΓSpecIso (.of K)).hom ((F α.1).coeff α.2)) / Module.finrank ℚ K
        let normz := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
          (.ofMul (zbar ≫ j)) (.ofMul (zbar ≫ j)))
        let normw := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
          (.ofMul (wbar ≫ j)) (.ofMul (wbar ≫ j)))
        (-hF - c₄ * (i₁ * normz ^ 2 + i₂ * normw ^ 2 + i₁ + i₂) - (δ₁ + δ₂) -
            n * Real.log ((δ₁ + n) * (δ₂ + n)) ≤
          δ₁ * (Height.logHeight a / Module.finrank ℚ K) +
            δ₂ * (Height.logHeight b / Module.finrank ℚ K) -
            d * (Height.logHeight e / Module.finrank ℚ K)) := by
  classical
  obtain ⟨c₈, c₉, h5⟩ := exists_finsum_iSup_log_dividedDerivative_le X A hg j hj D hrad hsupp
    Kbar N hN x hx
  refine ⟨max c₈ (c₉ + 1), ?_⟩
  intro sB hsB m φB hφB _ d₁ d₂ d δ₁ δ₂ hd₁ hd₂ hd hδd₁ hδd₂ K _ _ _ ι CK fK π hπ _ _ _ _ xK hξ₁₀ DK
    hDK S ιS πS hS _ _ _ ψ hψπ hψ₁ hψ₂ φ hφπ hφ s F hF p hp
    z w hpz hpw zK wK hzK hwK hzC hwC hz hw zbar wbar hzbar hwbar s₁ s₂ hs₁ hs₂ i₁ i₂ ev c hadm
    a b ha hb e he hza hwb hpe hFt normz normw
  have h5K := h5 K ι CK fK π hπ hξ₁₀ DK hDK
  letI : S.Over (Spec (.of K)) := ⟨πS⟩
  letI : CK.Over (Spec (.of K)) := ⟨fK⟩
  have : IsCurve K (CK ↘ Spec (.of K)) := ‹IsCurve K fK›
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have hsm : Smooth fK := MorphismProperty.of_isPullback (P := @Smooth) hπ inferInstance
  have : Smooth (CK ↘ Spec (.of K)) := hsm
  let pr₁ : S ⟶ CK := hπ.lift (ιS ≫ pullback.fst _ _) πS (by rw [Category.assoc]; exact hS.w)
  let pr₂ : S ⟶ CK := hπ.lift (ιS ≫ pullback.snd _ _) πS
    (by rw [Category.assoc, ← pullback.condition]; exact hS.w)
  have h₁ : pr₁ ≫ π = ιS ≫ pullback.fst _ _ := hπ.lift_fst _ _ _
  have h₁' : pr₁ ≫ fK = πS := hπ.lift_snd _ _ _
  have h₂ : pr₂ ≫ π = ιS ≫ pullback.snd _ _ := hπ.lift_fst _ _ _
  have h₂' : pr₂ ≫ fK = πS := hπ.lift_snd _ _ _
  have hXpb : IsPullback pr₁ pr₂ (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) :=
    isPullback_baseChange_prod hπ hS h₁ h₁' h₂ h₂'
  have hXo : pr₁ ≫ (CK ↘ Spec (.of K)) = S ↘ Spec (.of K) := h₁'
  let φNP' : CK ⟶ projectiveSpaceOver n (Spec (.of K)) :=
    pullback.lift fK (π ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _)
      (terminal.hom_ext _ _)
  have hφ'₁ : φNP' ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) = fK :=
    pullback.lift_fst _ _ _
  have hφ'₂ : φNP' ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
      π ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _ := pullback.lift_snd _ _ _
  have : φNP'.IsOver (Spec (.of K)) := ⟨hφ'₁⟩
  have hψ₁' : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP' := projectiveSpaceOver_hom_ext
    (by rw [Category.assoc, hψπ, Category.assoc, hφ'₁, h₁'])
    (by rw [Category.assoc, hψ₁, Category.assoc, hφ'₂, ← Category.assoc pr₁ π, h₁,
      Category.assoc])
  have hψ₂' : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP' := projectiveSpaceOver_hom_ext
    (by rw [Category.assoc, ← pullback.condition, hψπ, Category.assoc, hφ'₁, h₂'])
    (by rw [Category.assoc, hψ₂, Category.assoc, hφ'₂, ← Category.assoc pr₂ π, h₂,
      Category.assoc])
  have : p.IsOver (Spec (.of K)) := ⟨hp.trans (by
    change 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])⟩
  have hzK' : zK = p ≫ pr₁ := hπ.hom_ext (by rw [hzC, ← hpz, Category.assoc, h₁])
    (by rw [hzK, Category.assoc, h₁', hp])
  have hwK' : wK = p ≫ pr₂ := hπ.hom_ext (by rw [hwC, ← hpw, Category.assoc, h₂])
    (by rw [hwK, Category.assoc, h₂', hp])
  subst hzK' hwK'
  obtain ⟨g₁, hg₁, hm₁⟩ := exists_uniformizer_of_not_mem_exceptionalSet fK _ xK hξ₁₀ _ hzK hz
  obtain ⟨g₂, hg₂, hm₂⟩ := exists_uniformizer_of_not_mem_exceptionalSet fK _ xK hξ₁₀ _ hwK hw
  have : Nonempty S := ⟨p (closedPoint K)⟩
  have : Flat pr₁ := MorphismProperty.of_isPullback (P := @Flat) hXpb.flip inferInstance
  have : Flat pr₂ := MorphismProperty.of_isPullback (P := @Flat) hXpb inferInstance
  have : IsDominant pr₁ := isDominant_of_flat pr₁
  have : IsDominant pr₂ := isDominant_of_flat pr₂
  have hst₁ : pr₁.stalkMap (p (closedPoint K)) g₁ = s₁ :=
    stalkMap_eq_of_algebraMap_eq pr₁ (p (closedPoint K)) g₁ s₁
      (hs₁.trans ((functionFieldMap_comp_apply' pr₁ π h₁ _).symm.trans
        (congrArg _ ((map_div₀ _ _ _).trans hg₁.symm))))
  have hst₂ : pr₂.stalkMap (p (closedPoint K)) g₂ = s₂ :=
    stalkMap_eq_of_algebraMap_eq pr₂ (p (closedPoint K)) g₂ s₂
      (hs₂.trans ((functionFieldMap_comp_apply' pr₂ π h₂ _).symm.trans
        (congrArg _ ((map_div₀ _ _ _).trans hg₂.symm))))
  have hς₁ : pr₁.stalkMap (p (closedPoint K)) (g₁ -
      ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
        CK.presheaf.germ ⊤ ((p ≫ pr₁) (closedPoint K)) trivial).hom
        ((Scheme.stalkClosedPointTo (p ≫ pr₁)).hom g₁)) = s₁ - c (ev s₁) := by
    refine (map_sub _ _ _).trans (congrArg₂ (· - ·) hst₁ ?_)
    refine (const_comp (K := K) pr₁ hXo (p (closedPoint K)) _).symm.trans ?_
    change const (K := K) (p (closedPoint K)) _ = const (K := K) (p (closedPoint K)) _
    congr 1
    change _ = (Scheme.stalkClosedPointTo p).hom s₁
    rw [← hst₁, Scheme.stalkClosedPointTo_comp]
    rfl
  have hς₂ : pr₂.stalkMap (p (closedPoint K)) (g₂ -
      ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
        CK.presheaf.germ ⊤ ((p ≫ pr₂) (closedPoint K)) trivial).hom
        ((Scheme.stalkClosedPointTo (p ≫ pr₂)).hom g₂)) = s₂ - c (ev s₂) := by
    refine (map_sub _ _ _).trans (congrArg₂ (· - ·) hst₂ ?_)
    refine (const_comp (K := K) pr₂ (hXpb.w.symm.trans hXo) (p (closedPoint K)) _).symm.trans ?_
    change const (K := K) (p (closedPoint K)) _ = const (K := K) (p (closedPoint K)) _
    congr 1
    change _ = (Scheme.stalkClosedPointTo p).hom s₂
    rw [← hst₂, Scheme.stalkClosedPointTo_comp]
    rfl
  have hadm' : IsAdmissiblePair ψ φ δ₁ δ₂ d s p
      (pr₁.stalkMap (p (closedPoint K)) (g₁ -
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
          CK.presheaf.germ ⊤ ((p ≫ pr₁) (closedPoint K)) trivial).hom
          ((Scheme.stalkClosedPointTo (p ≫ pr₁)).hom g₁)))
      (pr₂.stalkMap (p (closedPoint K)) (g₂ -
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
          CK.presheaf.germ ⊤ ((p ≫ pr₂) (closedPoint K)) trivial).hom
          ((Scheme.stalkClosedPointTo (p ≫ pr₂)).hom g₂))) i₁ i₂ := by
    rw [hς₁, hς₂]; exact hadm
  have hcz : IsCoordinatesOf φNP' (p ≫ pr₁) a := isCoordinatesOf_of_comp_eq φNP' _ a ha (by
    rw [hφ'₂, ← hza, ← hpz]
    simp only [Category.assoc]
    rw [← Category.assoc pr₁ π, h₁, Category.assoc])
  have hcw : IsCoordinatesOf φNP' (p ≫ pr₂) b := isCoordinatesOf_of_comp_eq φNP' _ b hb (by
    rw [hφ'₂, ← hwb, ← hpw]
    simp only [Category.assoc]
    rw [← Category.assoc pr₂ π, h₂, Category.assoc])
  have hcp : IsCoordinatesOf φ p e := isCoordinatesOf_of_comp_eq φ p e he (by rw [hφ]; exact hpe)
  obtain ⟨j₁, hj₁⟩ := exists_index_absV_max a hcz.1
  obtain ⟨j₂, hj₂⟩ := exists_index_absV_max b hcw.1
  have hc₁ : ∀ v, (p ≫ pr₁) (closedPoint K) ∈ chartOf φNP' (j₁ v) := fun v =>
    (hcz.2 _ (hj₁ v).1).1
  have hc₂ : ∀ v, (p ≫ pr₂) (closedPoint K) ∈ chartOf φNP' (j₂ v) := fun v =>
    (hcw.2 _ (hj₂ v).1).1
  have hev₁ : ∀ v ν, (Scheme.stalkClosedPointTo (p ≫ pr₁)).hom
      (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ v)) = a ν / a (j₁ v) := fun v ν =>
    (hcz.2 _ (hj₁ v).1).2 ν
  have hev₂ : ∀ v ν, (Scheme.stalkClosedPointTo (p ≫ pr₂)).hom
      (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ v)) = b ν / b (j₂ v) := fun v ν =>
    (hcw.2 _ (hj₂ v).1).2 ν
  have h5z := h5K z (p ≫ pr₁) hzK hzC hz zbar hzbar g₁ hg₁ j₁
    (fun v ν => ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ v))
    (fun v ν => by
      rw [algebraMap_ratioOf_baseChange π φNP φNP' hφ'₂ _ ν (j₁ v) (hc₁ v) (x ν / x (j₁ v))
        (fun _ => hφNPx (j₁ v) ν), map_div₀])
    (fun v ν => by rw [hev₁]; exact absV'_div_le_one v (hj₁ v).1 ((hj₁ v).2 ν)) i₁
  have h5w := h5K w (p ≫ pr₂) hwK hwC hw wbar hwbar g₂ hg₂ j₂
    (fun v ν => ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ v))
    (fun v ν => by
      rw [algebraMap_ratioOf_baseChange π φNP φNP' hφ'₂ _ ν (j₂ v) (hc₂ v) (x ν / x (j₂ v))
        (fun _ => hφNPx (j₂ v) ν), map_div₀])
    (fun v ν => by rw [hev₂]; exact absV'_div_le_one v (hj₂ v).1 ((hj₂ v).2 ν)) i₂
  simp only [Faltings.PowerSeries.constantCoeff_dividedDerivative,
    PowerSeries.coeff_mk] at h5z h5w
  set ς₁ := g₁ - ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
      CK.presheaf.germ ⊤ ((p ≫ pr₁) (closedPoint K)) trivial).hom
      ((Scheme.stalkClosedPointTo (p ≫ pr₁)).hom g₁) with hς₁_def
  set ς₂ := g₂ - ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
      CK.presheaf.germ ⊤ ((p ≫ pr₂) (closedPoint K)) trivial).hom
      ((Scheme.stalkClosedPointTo (p ≫ pr₂)).hom g₂) with hς₂_def
  let T₁ : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v => ⨆ π : i₁.Partition,
    (π.parts.map fun l => ⨆ ν, Real.log (Sum.elim
      (fun w : InfinitePlace K => w (taylorCoeff (p ≫ pr₁) ς₁
        (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ v)) l) ^ ((w.mult : ℝ) / finrank ℚ K))
      (fun w : FinitePlace K => w (taylorCoeff (p ≫ pr₁) ς₁
        (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ v)) l) ^ ((1 : ℝ) / finrank ℚ K)) v)).sum
  let T₂ : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v => ⨆ π : i₂.Partition,
    (π.parts.map fun l => ⨆ ν, Real.log (Sum.elim
      (fun w : InfinitePlace K => w (taylorCoeff (p ≫ pr₂) ς₂
        (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ v)) l) ^ ((w.mult : ℝ) / finrank ℚ K))
      (fun w : FinitePlace K => w (taylorCoeff (p ≫ pr₂) ς₂
        (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ v)) l) ^ ((1 : ℝ) / finrank ℚ K)) v)).sum
  have h5z' : ∑ᶠ v, T₁ v ≤ c₈ * i₁ * normz ^ 2 + c₉ * i₁ := h5z
  have h5w' : ∑ᶠ v, T₂ v ≤ c₈ * i₂ * normw ^ 2 + c₉ * i₂ := h5w
  have hT₁ : (Function.support fun w : FinitePlace K => T₁ (.inr w)).Finite :=
    finite_support_partitionSup_real
      ((Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (i₁ + 1)).image
        fun t : Fin (n + 1) × Fin (n + 1) × ℕ => taylorCoeff (p ≫ pr₁) ς₁
          (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) t.2.1 t.1) t.2.2)
      (fun w l ν => taylorCoeff (p ≫ pr₁) ς₁
        (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ (.inr w))) l)
      (fun w l ν hl => Finset.mem_image.mpr ⟨(j₁ (.inr w), ν, l), by
        simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]; omega, rfl⟩)
  have hT₂ : (Function.support fun w : FinitePlace K => T₂ (.inr w)).Finite :=
    finite_support_partitionSup_real
      ((Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (i₂ + 1)).image
        fun t : Fin (n + 1) × Fin (n + 1) × ℕ => taylorCoeff (p ≫ pr₂) ς₂
          (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) t.2.1 t.1) t.2.2)
      (fun w l ν => taylorCoeff (p ≫ pr₂) ς₂
        (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ (.inr w))) l)
      (fun w l ν hl => Finset.mem_image.mpr ⟨(j₂ (.inr w), ν, l), by
        simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]; omega, rfl⟩)
  have hN0 : 0 < N := by omega
  have hδ₁pos : 0 < δ₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hδd₁; omega)
  have hδ₂pos : 0 < δ₂ := Nat.pos_of_ne_zero (by rintro rfl; simp at hδd₂; omega)
  have hmain := bound_of_coordinates hXpb hXo φNP' ψ hψ₁' hψ₂' φ N hN0 δ₁ δ₂ d hd hδ₁pos hδ₂pos
    s F hF p ς₁ ς₂ hm₁ hm₂ i₁ i₂ hadm' a b e j₁ j₂ T₁ T₂ hT₁ hT₂ hcz hcw hcp hc₁ hc₂
    (fun v ν => logAbs_ratioOf_le_zero hcz v (hj₁ v).1 (hj₁ v).2 ν)
    (fun v ν => logAbs_ratioOf_le_zero hcw v (hj₂ v).1 (hj₂ v).2 ν)
    (fun v => partitionSup_le_coe _ _ (fun y => logAbs_le_log_absV v y)
      (fun l ν => taylorCoeff (p ≫ pr₁) ς₁ (ratioOf φNP' ((p ≫ pr₁) (closedPoint K)) ν (j₁ v)) l))
    (fun v => partitionSup_le_coe _ _ (fun y => logAbs_le_log_absV v y)
      (fun l ν => taylorCoeff (p ≫ pr₂) ς₂ (ratioOf φNP' ((p ≫ pr₂) (closedPoint K)) ν (j₂ v)) l))
  push_cast at hmain
  exact sub_max_mul_le_of_finsum_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hmain h5z' h5w'

end Faltings.Lemma6EstimateForDerivatives

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace Faltings.BombieriSiegel

/-- **Bombieri's Lemma 6.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field `k`
with a divisor `P` of degree one, `A` a Jacobian with Abel–Jacobi map `j`, `D` the reduced theta
divisor, `Kbar` an algebraic closure of `k`, `N ≥ 2g + 1`, `n = N - g`, `x` a generic basis of
`L(N P)` and `φNP : C ⟶ ℙⁿ_k` the closed immersion it defines. There is a constant `c₄`, depending
only on `C`, `P` and `φNP`, such that for every `sB ≥ 1`, every closed immersion
`φB : C ×_k C ⟶ ℙᵐ_k`, all positive integers `d₁, d₂, d` with `dᵢ + sB d = N δᵢ`, every number
field `K ⊇ k` with a `k`-embedding `ι : K → Kbar`, every `K`-point `p = (z, w)` of `S = (C × C)_K`
with `z, w` outside the exceptional set, every global section `s` of `vojtaLineBundle ψ φ δ₁ δ₂ d`
with a representative `F` and every pair `(i₁, i₂)` admissible for `s` at `p` with respect to
`ς = ξ₁₀ - ξ₁₀(z)` and `ς' = ξ'₁₀ - ξ'₁₀(w)`, one has
`δ₁ h(a) + δ₂ h(b) - d h(e) ≥ -h(F) - c₄ (i₁ |z|² + i₂ |w|² + i₁ + i₂) - (δ₁ + δ₂)
- n log((δ₁ + n)(δ₂ + n))`, where `a, b, e` are coordinates of `φNP(z)`, `φNP(w)`, `φB(z, w)`,
`h = Height.logHeight / [K : ℚ]`, `h(F)` is the height of the coefficients of `F`, and
`|z| = √⟨j zbar, j zbar⟩` is the Néron norm of the point `zbar ∈ C(Kbar)` over `z`. -/
@[faltings "thm_bvs_derivative_estimates"]
public theorem exists_le_vojtaHeight_of_isAdmissiblePair {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (Kbar : Type u) [Field Kbar] [Algebra k Kbar] [IsAlgClosure k Kbar]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
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
          x ν / x j) :
    ∃ c₄ : ℝ, ∀ (sB : ℕ) (_hsB : 1 ≤ sB) {m : ℕ}
      (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
      (_hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
        pullback.fst X.f X.f ≫ X.f)
      [IsClosedImmersion φB],
    ∀ (d₁ d₂ d δ₁ δ₂ : ℕ) (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂) (_hd : 0 < d)
      (_hδd₁ : d₁ + sB * d = N * δ₁) (_hδd₂ : d₂ + sB * d = N * δ₂),
    ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] Kbar)
        -- the base change `C_K` of the curve, for reading `z, w ∉ Z`
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
        (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K fK; Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        -- the surface `S = (C ×_k C)_K` and the base changes `ψ, φ` of `φNP × φNP, φB`
        (S : Scheme.{u}) (ιS : S ⟶ pullback X.f X.f) (πS : S ⟶ Spec (.of K))
        (_hS : IsPullback ιS πS (pullback.fst X.f X.f ≫ X.f)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsIntegral S] [IsDominant (ιS ≫ pullback.fst X.f X.f)]
        [IsDominant (ιS ≫ pullback.snd X.f X.f)]
        (ψ : S ⟶ pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
        (_hψπ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) = πS)
        (_hψ₁ : ψ ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.fst _ _ ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (_hψ₂ : ψ ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
          ιS ≫ pullback.snd _ _ ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (φ : S ⟶ projectiveSpaceOver m (Spec (.of K)))
        (_hφπ : φ ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) = πS)
        (_hφ : φ ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
          ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
        -- the section `s` and its representative `F`
        (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
        (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of K), ⊤))
        (_hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F)
        -- the point `p = (z, w)`, with `z, w` outside the exceptional set
        (p : Spec (.of K) ⟶ S) (_hp : p ≫ πS = 𝟙 _)
        (z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)
        (_hpz : p ≫ ιS ≫ pullback.fst _ _ = z.left) (_hpw : p ≫ ιS ≫ pullback.snd _ _ = w.left)
        (zK wK : Spec (.of K) ⟶ CK) (_hzK : zK ≫ fK = 𝟙 _) (_hwK : wK ≫ fK = 𝟙 _)
        (_hzC : zK ≫ π = z.left) (_hwC : wK ≫ π = w.left)
        (_hz : zK ∉ exceptionalSet K fK DK xK hξ₁₀)
        (_hw : wK ∉ exceptionalSet K fK DK xK hξ₁₀)
        -- the points of `C(k̄)` over `z` and `w`, for the Néron norm
        (zbar wbar : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Kbar))) ⟶ Over.mk X.f)
        (_hzbar : zbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ z.left)
        (_hwbar : wbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ w.left)
        -- the germs at `p` of `ξ₁₀ ∘ pr₁` and `ξ'₁₀ = ξ₁₀ ∘ pr₂`
        (s₁ s₂ : S.presheaf.stalk (p (closedPoint K)))
        (_hs₁ : algebraMap _ S.functionField s₁ =
          functionFieldMap (ιS ≫ pullback.fst _ _) (x 1 / x 0))
        (_hs₂ : algebraMap _ S.functionField s₂ =
          functionFieldMap (ιS ≫ pullback.snd _ _) (x 1 / x 0))
        (i₁ i₂ : ℕ),
      letI : S.Over (Spec (.of K)) := ⟨πS⟩
      let ev : S.presheaf.stalk (p (closedPoint K)) →+* K := (Scheme.stalkClosedPointTo p).hom
      let c : K →+* S.presheaf.stalk (p (closedPoint K)) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ πS.appTop ≫
          S.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom
      BombieriVojta.IsAdmissiblePair ψ φ δ₁ δ₂ d s p (s₁ - c (ev s₁)) (s₂ - c (ev s₂)) i₁ i₂ →
      -- coordinates of `φNP(z)`, `φNP(w)` and `φB(z, w)`
      ∀ (a b : Fin (n + 1) → K) (ha : Ideal.span (Set.range a) = ⊤)
        (hb : Ideal.span (Set.range b) = ⊤) (e : Fin (m + 1) → K)
        (he : Ideal.span (Set.range e) = ⊤),
        z.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) a ha →
        w.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) b hb →
        p ≫ ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) =
            projectiveSpacePoint (R := CommRingCat.of K) e he →
        let hF : ℝ := Height.logHeight (fun α : (i : Fin (m + 1)) × (F i).support =>
          (Scheme.ΓSpecIso (.of K)).hom ((F α.1).coeff α.2)) / Module.finrank ℚ K
        let normz := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
          (.ofMul (zbar ≫ j)) (.ofMul (zbar ≫ j)))
        let normw := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
          (.ofMul (wbar ≫ j)) (.ofMul (wbar ≫ j)))
        (-hF - c₄ * (i₁ * normz ^ 2 + i₂ * normw ^ 2 + i₁ + i₂) - (δ₁ + δ₂) -
            n * Real.log ((δ₁ + n) * (δ₂ + n)) ≤
          δ₁ * (Height.logHeight a / Module.finrank ℚ K) +
            δ₂ * (Height.logHeight b / Module.finrank ℚ K) -
            d * (Height.logHeight e / Module.finrank ℚ K)) :=
    Faltings.Lemma6EstimateForDerivatives.solution X A hg j hj D hrad hsupp Kbar N hN hn x hx φNP
      hφNP hφNPx

end Faltings.BombieriSiegel
