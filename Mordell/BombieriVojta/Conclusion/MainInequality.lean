module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Admissible.Basic
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.Height.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma6
public import Mordell.BombieriVojta.Height.SegreVeroneseClass
public import Mordell.Height.Weil.Representative
public import Mordell.Height.Weil.FieldIndependence
public import Mordell.BombieriVojta.Height.Lemma4
public import Mordell.BombieriVojta.SmallSection.DimU0
public import Mordell.BombieriVojta.Mumford.Main
public import Mordell.BombieriVojta.Admissible.Comparison
public import Mordell.BombieriVojta.Height.NeronTateExpansion
public import Mordell.NeronTate.Nonneg
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates

/-!
# The main inequality

Let `C` be a smooth projective curve of genus `g ≥ 2` over a number field `k`, with a divisor
`P` of degree one, Jacobian `J`, Abel–Jacobi map `j = j_P`, Néron form `⟨ , ⟩` of the theta class
on `J(k̄)` and norm `|z| = √⟨z, z⟩`, where `⟨z, w⟩ = ⟨j z, j w⟩` for `z, w ∈ C(k̄)`. Fix the
standing data of Bombieri's Sections 9 and 10: a generic basis `x` of `H⁰(C, 𝒪(N P))`,
`N ≥ 2g + 1`, giving `φ_{NP}`, `ψ = φ_{NP} × φ_{NP}`, and a basis `y` of `H⁰(C × C, 𝒪(B))`,
`B = (s + 1)(P × C) + (s + 1)(C × P) - Δ`, generic for the projections and giving `φ_B`.

There are constants `c₁, c₄, c₁₇`, depending only on these data and on the constant `c₁₀` of
the bound on `h(𝓕)`, with the following property. Let `γ > 0` and let `d₁, d₂, d` be
sufficiently large integers with `d₁ d₂ - g d² > γ d₁ d₂`, `g d² < d₁ d₂ < g² d²`,
`N ∣ dᵢ + s d` and `d₂ ≤ d₁`. Let `s ≠ 0` be a global section of
`𝒪(V) = ψ^* 𝒪(δ₁, δ₂) ⊗ φ_B^* 𝒪(d)⁻¹`, `δᵢ = (dᵢ + s d) / N`, with a representative `𝓕` with
coefficients in `k` and `h(𝓕) ≤ c₁₀ (d₁ + d₂) / γ + o(d₁ + d₂)`, let `z, w ∈ C(k̄)` lie outside
the exceptional set `Z`, and let `(i₁*, i₂*)` be admissible for `s` at `(z, w)`. Then
`-c₄ (i₁* |z|² + i₂* |w|²) - c₁₇ (d₁ + i₁* + i₂*) - c₁₇ d₁ / γ`
`  ≤ d₁ / (2g) |z|² + d₂ / (2g) |w|² - d ⟨z, w⟩ + c₁ (d₁ |z| + d₂ |w|)`.

It is obtained by combining the lower bound of Bombieri's Lemma 6 for the height `h_V(z, w)`
with the upper bound of his Lemma 2, and absorbing the lower-order terms into `c₁₇`.

## Main results

* `Faltings.BombieriRoth.exists_neg_le_neronPairing_of_isAdmissiblePair`: the main inequality.

## Implementation notes

The curve over `k` is `X : Faltings.CurveWithDegreeOneDivisor k`, with Jacobian `A`, Abel–Jacobi
map `j` and the class `θ` of the reduced effective Cartier divisor `D` supported on
`Faltings.thetaDivisor`, exactly as for `Faltings.neronPairing`. The standing data live over
`k`, as in `Faltings.BombieriSiegel.exists_le_vojtaHeight_of_isAdmissiblePair`: `x` is a generic
basis of `L(N P)` in `k(C)`, `φ_{NP} : C ⟶ ℙⁿ_k`, `ψ : C ×_k C ⟶ ℙⁿ_k ×_k ℙⁿ_k`,
`φ_B : C ×_k C ⟶ ℙᵐ_k`, the section `s` of `Faltings.vojtaLineBundle ψ φ_B δ₁ δ₂ d` and its
representative `𝓕` are over `k`. A point `(z, w)` of `(C × C)(k̄)` is a morphism
`p : Spec k̄ ⟶ C ×_k C`, and `z, w ∈ C(k̄)` are its two projections.

The exceptional set (`Faltings.BombieriSiegel.exceptionalSet`) and admissibility
(`Faltings.BombieriRoth.IsAdmissiblePair`) are notions on a curve over a field `K` at its
`K`-rational points. A point of `(C × C)(k̄)` is defined over a number field `K ⊆ k̄`, given by a
`k`-embedding `ι : K → k̄`, and both notions are read on the base change `C_K` of `C` at the
`K`-point `p_K` of `C_K ×_K C_K` through which `p` factors; there `x` becomes `π^* x` and `N P`
becomes `Q ↦ N P(π Q)` for the projection `π : C_K ⟶ C`, `ψ, φ_B` become their base changes
`ψ_K, φ_K`, and `s` becomes the section `s_K` of `vojtaLineBundle ψ_K φ_K δ₁ δ₂ d` represented
by `𝓕` (a representative determines its section). Both notions are invariant under enlarging
`K`, so the hypotheses are stated for every such `K`.

The integers `d₁, d₂, d` are natural numbers, `δᵢ` the natural numbers with `N δᵢ = dᵢ + s d`,
and "sufficiently large in terms of `γ`" is a threshold `D₀` bounding `d₁, d₂, d` from below.
The term `o(d₁ + d₂)` is a function `e` of `d₁ + d₂` with `e = o(n)`, and `D₀` depends on `γ`
and `e`. The height `h(𝓕)` is `Faltings.polynomialFamilyHeight` of the components of `𝓕`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, p. 637
-/

universe u

namespace Faltings.BombieriRoth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing BombieriSiegel

/-- The arithmetic of the main inequality: the lower bound of Bombieri's Lemma 6 and the upper
bound of his Lemma 2 for the same value `hV` of the Vojta height, with the bound on `h(𝓕)`,
give the main inequality once the lower-order terms are absorbed into
`c₁₇ = max c₄ 0 + 2 + (2 + 2 s) + n (2 + 2 s) + 2 n² + 3 c₂ + 2 max c₁₀ 0`. -/
private theorem neg_le_of_le_vojtaHeight_of_vojtaHeight_le
    {c₁₀ c₂ c₄ γ hF hV R Z W i₁ i₂ d₁ d₂ d δ₁ δ₂ n sB E : ℝ}
    (hγ : 0 < γ) (hc₂ : 0 ≤ c₂) (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂) (hn : 1 ≤ n) (hsB : 0 ≤ sB)
    (hd₁ : 1 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd21 : d₂ ≤ d₁) (hdd₁ : d ≤ d₁)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁le : δ₁ ≤ d₁ + sB * d) (hδ₂le : δ₂ ≤ d₂ + sB * d)
    (hE : E ≤ d₁ + d₂)
    (h6 : -hF - c₄ * (i₁ * Z ^ 2 + i₂ * W ^ 2 + i₁ + i₂) - (δ₁ + δ₂) -
      n * Real.log ((δ₁ + n) * (δ₂ + n)) ≤ hV)
    (hup : hV ≤ R + c₂ * (d₁ + d₂ + d))
    (hF : hF ≤ c₁₀ * (d₁ + d₂) / γ + E) :
    -c₄ * (i₁ * Z ^ 2 + i₂ * W ^ 2) -
        (max c₄ 0 + 2 + (2 + 2 * sB) + n * (2 + 2 * sB) + 2 * n ^ 2 + 3 * c₂ + 2 * max c₁₀ 0) *
          (d₁ + i₁ + i₂) -
        (max c₄ 0 + 2 + (2 + 2 * sB) + n * (2 + 2 * sB) + 2 * n ^ 2 + 3 * c₂ + 2 * max c₁₀ 0) *
          d₁ / γ ≤ R := by
  set A := max c₄ 0
  set M := max c₁₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hA4 : c₄ * (i₁ + i₂) ≤ A * (i₁ + i₂) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hi₁ hi₂)
  have hp₁ : 0 < δ₁ + n := by linarith
  have hp₂ : 0 < δ₂ + n := by linarith
  have hlog : Real.log ((δ₁ + n) * (δ₂ + n)) ≤ (δ₁ + n) + (δ₂ + n) := by
    rw [Real.log_mul hp₁.ne' hp₂.ne']
    exact add_le_add (Real.log_le_self hp₁.le) (Real.log_le_self hp₂.le)
  have hsBd : sB * d ≤ sB * d₁ := mul_le_mul_of_nonneg_left hdd₁ hsB
  have hδ : δ₁ + δ₂ ≤ (2 + 2 * sB) * d₁ := by linarith
  have hnlog : n * Real.log ((δ₁ + n) * (δ₂ + n)) ≤ (n * (2 + 2 * sB) + 2 * n ^ 2) * d₁ := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ n)
    have h2 : 2 * n ^ 2 * 1 ≤ 2 * n ^ 2 * d₁ := mul_le_mul_of_nonneg_left hd₁ (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hδ (by linarith : (0 : ℝ) ≤ n)
    linarith
  have hc₂d : c₂ * (d₁ + d₂ + d) ≤ c₂ * (3 * d₁) :=
    mul_le_mul_of_nonneg_left (by linarith) hc₂
  have hFd : c₁₀ * (d₁ + d₂) / γ ≤ 2 * M * d₁ / γ := by
    apply div_le_div_of_nonneg_right _ hγ.le
    calc c₁₀ * (d₁ + d₂) ≤ M * (d₁ + d₂) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      _ ≤ M * (2 * d₁) := mul_le_mul_of_nonneg_left (by linarith) hM
      _ = 2 * M * d₁ := by ring
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 + (2 + 2 * sB) + n * (2 + 2 * sB) + 2 * n ^ 2 + 3 * c₂ :=
    ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hC : A + B + 2 * M =
      A + 2 + (2 + 2 * sB) + n * (2 + 2 * sB) + 2 * n ^ 2 + 3 * c₂ + 2 * M := by
    rw [hBdef]; ring
  rw [← hC]
  have hC1 : A * (i₁ + i₂) + B * d₁ ≤ (A + B + 2 * M) * (d₁ + i₁ + i₂) := by
    linarith [mul_nonneg hA (by linarith : (0 : ℝ) ≤ d₁), mul_nonneg hB (add_nonneg hi₁ hi₂),
      mul_nonneg hM (by linarith : (0 : ℝ) ≤ d₁ + i₁ + i₂)]
  have hC2 : 2 * M * d₁ / γ ≤ (A + B + 2 * M) * d₁ / γ := by
    apply div_le_div_of_nonneg_right _ hγ.le
    linarith [mul_nonneg (add_nonneg hA hB) (by linarith : (0 : ℝ) ≤ d₁)]
  have hBd : B * d₁ = 2 * d₁ + (2 + 2 * sB) * d₁ + (n * (2 + 2 * sB) + 2 * n ^ 2) * d₁ +
      3 * c₂ * d₁ := by rw [hBdef]; ring
  linarith

/-- A `K`-point of `C_K ×_K C_K` over `K` has first projection a `K`-point of `C_K`. -/
private theorem comp_fst_comp_over_eq_id {K : Type u} [Field K] {CK : Scheme.{u}}
    [CK.Over (Spec (.of K))]
    (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
    [pK.IsOver (Spec (.of K))] :
    (pK ≫ pullback.fst _ _) ≫ (CK ↘ Spec (.of K)) = 𝟙 _ := by
  rw [Category.assoc, pullback.condition]
  refine ((Scheme.Hom.isOver_iff (Spec (.of K))).1 ‹_›).trans ?_
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- A `K`-point of `C_K ×_K C_K` over `K` has second projection a `K`-point of `C_K`. -/
private theorem comp_snd_comp_over_eq_id {K : Type u} [Field K] {CK : Scheme.{u}}
    [CK.Over (Spec (.of K))]
    (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
    [pK.IsOver (Spec (.of K))] :
    (pK ≫ pullback.snd _ _) ≫ (CK ↘ Spec (.of K)) = 𝟙 _ := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact comp_fst_comp_over_eq_id pK

/-- The base change `C_K` of the curve `C` along `k → K` has an integral square `C_K ×_K C_K`. -/
private theorem isIntegral_pullback_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : CurveWithDegreeOneDivisor k) {CK : Scheme.{u}} [CK.Over (Spec (.of K))] {π : CK ⟶ X.C}
    (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsIntegral (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) := by
  have : GeometricallyIntegral (CK ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hπ inferInstance
  infer_instance

/-- At a `K`-point `pK = (z, w)` of `C_K ×_K C_K` with `z, w` outside the exceptional set, the
germs `s₁, s₂` of `ξ₁₀ ∘ pr₁` and `ξ₁₀ ∘ pr₂` exist, and a pair admissible for `s` at `pK` is
admissible in the sense of `Faltings.BombieriVojta.IsAdmissiblePair` for the parameters
`sᵢ - sᵢ(pK)`. -/
private theorem exists_stalk_isAdmissiblePair {K : Type u} [Field K] {CK : Scheme.{u}}
    [CK.Over (Spec (.of K))] [IsCurve K (CK ↘ Spec (.of K))] [Smooth (CK ↘ Spec (.of K))]
    [IsLocallyNoetherian CK] [IsIntegral CK]
    [IsIntegral (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))]
    (DK : CK →₀ ℤ) {n m : ℕ} (xK : Fin (n + 1) → CK.functionField)
    (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K)); Transcendental K (xK 1 / xK 0))
    {S' : Scheme.{u}}
    (ψ : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
      pullback (projectiveSpaceOver n S' ↘ S') (projectiveSpaceOver n S' ↘ S'))
    (φ : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ projectiveSpaceOver m S')
    (δ₁ δ₂ d : ℤ) (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
    [pK.IsOver (Spec (.of K))]
    (hz : pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀)
    (hw : pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀)
    {i : ℕ × ℕ} (hadm : IsAdmissiblePair (vojtaLineBundle ψ φ δ₁ δ₂ d) s pK i) :
    ∃ s₁ s₂ : (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.stalk
        (pK (closedPoint K)),
      algebraMap _ (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).functionField s₁ =
          functionFieldMap (pullback.fst _ _) (xK 1 / xK 0) ∧
        algebraMap _ (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).functionField s₂ =
          functionFieldMap (pullback.snd _ _) (xK 1 / xK 0) ∧
        BombieriVojta.IsAdmissiblePair ψ φ δ₁ δ₂ d s pK
          (s₁ - ((Scheme.ΓSpecIso (.of K)).inv ≫
            (pullback.snd _ _ ≫ (CK ↘ Spec (.of K))).appTop ≫
            (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ ⊤
              (pK (closedPoint K)) trivial).hom ((Scheme.stalkClosedPointTo pK).hom s₁))
          (s₂ - ((Scheme.ΓSpecIso (.of K)).inv ≫
            (pullback.snd _ _ ≫ (CK ↘ Spec (.of K))).appTop ≫
            (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ ⊤
              (pK (closedPoint K)) trivial).hom ((Scheme.stalkClosedPointTo pK).hom s₂))
          i.1 i.2 := by
  obtain ⟨g₁, hg₁, hm₁⟩ := Lemma6EstimateForDerivatives.exists_uniformizer_of_not_mem_exceptionalSet
    (CK ↘ Spec (.of K)) DK xK hξ₁₀ _ (comp_fst_comp_over_eq_id pK) hz
  obtain ⟨g₂, hg₂, hm₂⟩ := Lemma6EstimateForDerivatives.exists_uniformizer_of_not_mem_exceptionalSet
    (CK ↘ Spec (.of K)) DK xK hξ₁₀ _ (comp_snd_comp_over_eq_id pK) hw
  have hadm' := IsAdmissiblePair.bombieriVojta ψ φ δ₁ δ₂ d hadm.1 hadm _ _ hm₁ hm₂
  refine ⟨(pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap _ g₁,
    (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).stalkMap _ g₂, ?_, ?_, ?_⟩
  · exact (Lemma6EstimateForDerivatives.algebraMap_stalkMap_eq_functionFieldMap'
      (pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) (pK (closedPoint K)) g₁).trans
      (congrArg _ hg₁)
  · exact (Lemma6EstimateForDerivatives.algebraMap_stalkMap_eq_functionFieldMap'
      (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) (pK (closedPoint K)) g₂).trans
      (congrArg _ hg₂)
  · convert hadm' using 1
    · refine ((map_sub _ _ _).trans (congrArg₂ (· - ·) rfl ?_)).symm
      refine (BombieriVojta.const_comp (K := K)
        (pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) pullback.condition
        (pK (closedPoint K)) _).symm.trans ?_
      change BombieriVojta.const (K := K) (pK (closedPoint K)) _ =
        BombieriVojta.const (K := K) (pK (closedPoint K)) _
      congr 1
      rw [Scheme.stalkClosedPointTo_comp]
      rfl
    · refine ((map_sub _ _ _).trans (congrArg₂ (· - ·) rfl ?_)).symm
      refine (BombieriVojta.const_comp (K := K)
        (pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) rfl
        (pK (closedPoint K)) _).symm.trans ?_
      change BombieriVojta.const (K := K) (pK (closedPoint K)) _ =
        BombieriVojta.const (K := K) (pK (closedPoint K)) _
      congr 1
      rw [Scheme.stalkClosedPointTo_comp]
      rfl

/-- The height of a family of polynomials over a number field `k`, read through the
coefficients of its image over a number field `K ⊇ k`, is at most `h(P)` (with `h = 0` for the
zero family). -/
private theorem logHeight_coeff_map_div_finrank_le {k K : Type u} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] {ι σ : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ k) [Decidable (∃ i, P i ≠ 0)] :
    Height.logHeight (fun α : (i : ι) × (MvPolynomial.map
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (P i)).support =>
        (Scheme.ΓSpecIso (.of K)).hom ((MvPolynomial.map
          ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (P α.1)).coeff α.2)) /
        Module.finrank ℚ K ≤
      (if hP : ∃ i, P i ≠ 0 then polynomialFamilyHeight P hP else 0) := by
  classical
  set φ := (Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)
  let f : ((i : ι) × (MvPolynomial.map φ (P i)).support) → ((i : ι) × (P i).support) :=
    fun α => ⟨α.1, α.2.1, MvPolynomial.support_map_subset φ (P α.1) α.2.2⟩
  have hx : (fun α : (i : ι) × (MvPolynomial.map φ (P i)).support =>
      (Scheme.ΓSpecIso (.of K)).hom ((MvPolynomial.map φ (P α.1)).coeff α.2)) =
      (fun α : (i : ι) × (P i).support => algebraMap k K ((P α.1).coeff α.2)) ∘ f := by
    funext α
    simp [f, φ, MvPolynomial.coeff_map]
  rw [hx]
  split_ifs with hP
  · refine (div_le_div_of_nonneg_right (Height.logHeight_comp_le f _)
      (Nat.cast_nonneg _)).trans_eq ?_
    have hy0 : (fun p : (i : ι) × (P i).support => (P p.1).coeff p.2.1) ≠ 0 := by
      obtain ⟨i, hi⟩ := hP
      obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hi
      exact Function.ne_iff.mpr ⟨⟨i, I, MvPolynomial.mem_support_iff.mpr hI⟩, hI⟩
    have h1 := @weilHeight_eq_sumLocalHeight k _ _ _ _ _ (IsWellOrder.linearOrder WellOrderingRel)
      k _ _ _ _ (fun p : (i : ι) × (P i).support => (P p.1).coeff p.2.1) hy0 rfl
    have h2 := sumLocalHeight_algebraMap (L := K) hy0
    have h3 := BombieriVojta.HeightLowerBound.sumLocalHeight_eq_logHeight (K := K)
      (a := algebraMap k K ∘ fun p : (i : ι) × (P i).support => (P p.1).coeff p.2.1)
      (by simpa [funext_iff] using hy0)
    exact (h3.symm.trans (h2.trans h1.symm)).trans rfl
  · push Not at hP
    have : IsEmpty ((i : ι) × (MvPolynomial.map φ (P i)).support) :=
      ⟨fun α => by simpa [hP] using α.2.2⟩
    rw [Subsingleton.elim (_ ∘ f) (0 : (i : ι) × (MvPolynomial.map φ (P i)).support → K)]
    simp

/-- The height `h_Φ(p)` of a `k̄`-point `p` whose image in `ℙⁿ_ℤ` is the `k̄`-point of the
`K`-coordinates `a`, `K ⊆ k̄` a number field, is `Height.logHeight a / [K : ℚ]`. -/
private theorem height_eq_logHeight_div_finrank {L : Type u} [Field L] [Algebra ℚ L]
    [Algebra.IsAlgebraic ℚ L] {X : Scheme.{u}} {f : X ⟶ Spec (.of L)} [IsProjectiveVariety L f]
    [Smooth f] {n : ℕ} (Φ : ProjectiveEmbedding f n) (p : {p : Spec (.of L) ⟶ X // p ≫ f = 𝟙 _})
    {K : Type u} [Field K] [NumberField K] (ι : K →+* L) (a : Fin (n + 1) → K)
    (ha : Ideal.span (Set.range a) = ⊤)
    (hp : p.1 ≫ Φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of L)) =
      Spec.map (CommRingCat.ofHom ι) ≫ projectiveSpacePoint (R := CommRingCat.of K) a ha) :
    Φ.height p = Height.logHeight a / Module.finrank ℚ K := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha0
  let : Algebra K L := ι.toAlgebra
  have hιa : algebraMap K L ∘ a ≠ 0 :=
    Function.ne_iff.mpr ⟨i₀, by simpa using (map_ne_zero ι).2 hi₀⟩
  have hspan : Ideal.span (Set.range fun i => (CommRingCat.ofHom ι) (a i)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩)
      (Ne.isUnit ((map_ne_zero ι).2 hi₀))
  rw [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization,
    kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint _ _ (algebraMap K L ∘ a) hspan hιa
      (by rw [Category.assoc, hp, specMap_comp_projectiveSpacePoint]; rfl),
    weilHeight_eq_sumLocalHeight hιa rfl,
    BombieriVojta.HeightLowerBound.sumLocalHeight_eq_logHeight ha0]

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **Bombieri's Lemma 2 for the embeddings `φ_{NP}`, `φ_B` of Sections 9–10**, read on
`K`-coordinates: for `N δᵢ = dᵢ + s d`, a `K`-point `q = (z, w)` of `C × C` over `k` and
coordinates `a, b, e` of `φ_{NP}(z)`, `φ_{NP}(w)`, `φ_B(z, w)`,
`δ₁ h(a) + δ₂ h(b) - d h(e) ≤ d₁/(2g) |z|² + d₂/(2g) |w|² - d ⟨z, w⟩ + c₁ (d₁ |z| + d₂ |w|)
+ c₂ (d₁ + d₂ + d)`. -/
private theorem exists_logHeight_le_neronPairing {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ}
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    -- the embedding `φ_{NP}` of class `N P`
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
    -- the embedding `φ_B` of `C × C` of the Vojta class `B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {m : ℕ} (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
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
      X.vojtaClass sB sB (-1)) :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      ∀ (d₁ d₂ d δ₁ δ₂ : ℕ), N * δ₁ = d₁ + sB * d → N * δ₂ = d₂ + sB * d →
      ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
        (q : Spec (.of K) ⟶ pullback X.f X.f),
        q ≫ pullback.fst X.f X.f ≫ X.f = Spec.map (CommRingCat.ofHom (algebraMap k K)) →
      ∀ (z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f),
        z.left = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ q ≫ pullback.fst X.f X.f →
        w.left = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ q ≫ pullback.snd X.f X.f →
      ∀ (a b : Fin (n + 1) → K) (ha : Ideal.span (Set.range a) = ⊤)
        (hb : Ideal.span (Set.range b) = ⊤) (e : Fin (m + 1) → K)
        (he : Ideal.span (Set.range e) = ⊤),
        q ≫ pullback.fst X.f X.f ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
          projectiveSpacePoint (R := CommRingCat.of K) a ha →
        q ≫ pullback.snd X.f X.f ≫ φNP ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
          projectiveSpacePoint (R := CommRingCat.of K) b hb →
        q ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) =
          projectiveSpacePoint (R := CommRingCat.of K) e he →
        (δ₁ : ℝ) * (Height.logHeight a / Module.finrank ℚ K) +
            δ₂ * (Height.logHeight b / Module.finrank ℚ K) -
            d * (Height.logHeight e / Module.finrank ℚ K) ≤
          d₁ / (2 * (genus X.f : ℝ)) * √(pair z z) ^ 2 +
            d₂ / (2 * (genus X.f : ℝ)) * √(pair w w) ^ 2 -
            d * pair z w + c₁ * (d₁ * √(pair z z) + d₂ * √(pair w w)) + c₂ * (d₁ + d₂ + d) := by
  intro pair
  have : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  let : Algebra ℚ kbar := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  obtain ⟨XK, π, hπ, hP⟩ := exists_baseChange (K := kbar) X
  have : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
  have := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  have := (IsSmoothProjectiveCurve.surface_pullback kbar XK.f XK.f).1
  have hβ := isPullback_map hπ
  let φNP₀ : ProjectiveEmbedding X.f n := ⟨φNP, inferInstance, hφNP⟩
  let φB₀ : ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m := ⟨φB, inferInstance, hφB⟩
  let ΦNP : ProjectiveEmbedding XK.f n := ProjectiveEmbedding.baseChange hπ φNP₀
  let ΦB : ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m :=
    ProjectiveEmbedding.baseChange hβ φB₀
  have hΦNP : ΦNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of kbar)) =
      π ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) :=
    baseChangeHom_snd (fX := XK.f) (p := π) φNP
  have hΦB : ΦB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of kbar)) =
      pullback.map XK.f XK.f X.f X.f π π _ hπ.w.symm hπ.w.symm ≫ φB ≫
        projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) :=
    baseChangeHom_snd (fX := pullback.fst XK.f XK.f ≫ XK.f) (p := pullback.map XK.f XK.f X.f X.f
      π π _ hπ.w.symm hπ.w.symm) φB
  let LNP := (Scheme.Modules.pullback φNP).obj ((Scheme.Modules.pullback
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n))
  let LB := (Scheme.Modules.pullback φB).obj ((Scheme.Modules.pullback
    (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m))
  let L := (Scheme.Modules.pullback π).obj LNP
  let M := (Scheme.Modules.pullback
    (pullback.map XK.f XK.f X.f X.f π π _ hπ.w.symm hπ.w.symm)).obj LB
  have hL : Stacks.SheafOfModules.picardClass XK.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L
        (inferInstance : Stacks.Ample.IsInvertibleModule XK.C L)) =
      Stacks.Picard.schemePullbackClassHom π ((N : ℤ) • X.P.sum fun x n =>
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) :=
    (schemePullbackClassHom_picardClass π LNP _).symm.trans (congrArg _ hφNPL)
  have hM : Stacks.SheafOfModules.picardClass (pullback XK.f XK.f).presheaf
      (Stacks.RingedSpace.structureIsSheaf (pullback XK.f XK.f).toRingedSpace) M
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M
        (inferInstance : Stacks.Ample.IsInvertibleModule (pullback XK.f XK.f) M)) =
      Stacks.Picard.schemePullbackClassHom (pullback.map XK.f XK.f X.f X.f π π
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) hπ.w.symm hπ.w.symm)
        (X.vojtaClass sB sB (-1)) :=
    (schemePullbackClassHom_picardClass _ LB _).symm.trans (congrArg _ hφBB)
  have hφL : Nonempty ((Scheme.Modules.pullback
      (ΦNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L) := by
    rw [hΦNP]
    exact ⟨((Scheme.Modules.pullbackComp π _).app _).symm ≪≫
      (Scheme.Modules.pullback π).mapIso ((Scheme.Modules.pullbackComp φNP _).app _).symm⟩
  have hφM : Nonempty ((Scheme.Modules.pullback
      (ΦB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m _)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≅ M) := by
    rw [hΦB]
    exact ⟨((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp φB _).app _).symm⟩
  obtain ⟨κ₁, κ₂, κ₃, hκ₁, hκ₂, hκ₃, hκ⟩ :=
    exists_abs_vojtaHeight_sub_neronPairing_le_of_nonempty_iso X A hg j hj D hrad hsupp kbar
      XK π hπ ΦNP ΦB N hN (sB : ℤ) (by exact_mod_cast hsB) L hL M hM hφL hφM
  have hg0 : (0 : ℝ) < genus X.f := by exact_mod_cast (show 0 < genus X.f by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨κ₃ / (2 * genus X.f), κ₁ / N + κ₂, by positivity, by positivity, ?_⟩
  intro d₁ d₂ d δ₁ δ₂ hδ₁ hδ₂ K _ _ _ ι q hq z w hz hw a b ha hb e he hza hwb hpe
  obtain ⟨z', rfl⟩ := exists_section_homMk_eq X XK hπ z
  obtain ⟨w', rfl⟩ := exists_section_homMk_eq X XK hπ w
  have hz'' : z'.1 ≫ π = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ q ≫
      pullback.fst X.f X.f := hz
  have hw'' : w'.1 ≫ π = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ q ≫
      pullback.snd X.f X.f := hw
  have hhz := height_eq_logHeight_div_finrank ΦNP z' (ι : K →+* kbar) a ha (by
    rw [hΦNP, ← Category.assoc, hz'']; simp only [Category.assoc]; rw [hza])
  have hhw := height_eq_logHeight_div_finrank ΦNP w' (ι : K →+* kbar) b hb (by
    rw [hΦNP, ← Category.assoc, hw'']; simp only [Category.assoc]; rw [hwb])
  have hlift : pullback.lift z'.1 w'.1 (z'.2.trans w'.2.symm) ≫
      pullback.map XK.f XK.f X.f X.f π π _ hπ.w.symm hπ.w.symm =
      Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hz'', Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hw'', Category.assoc]
  have hhB := height_eq_logHeight_div_finrank ΦB
    ⟨pullback.lift z'.1 w'.1 (z'.2.trans w'.2.symm), by rw [pullback.lift_fst_assoc, z'.2]⟩
    (ι : K →+* kbar) e he (by
      rw [hΦB, ← Category.assoc, hlift]; simp only [Category.assoc]; rw [hpe])
  have hV : XK.vojtaHeight ΦNP ΦB sB N d₁ d₂ d z' w' =
      (δ₁ : ℝ) * (Height.logHeight a / Module.finrank ℚ K) +
        δ₂ * (Height.logHeight b / Module.finrank ℚ K) -
        d * (Height.logHeight e / Module.finrank ℚ K) := by
    have e₁ : (((d₁ : ℤ) + (sB : ℤ) * (d : ℤ) : ℤ) : ℝ) / N = δ₁ := by
      rw [div_eq_iff hN0.ne']
      exact_mod_cast hδ₁.symm.trans (mul_comm N δ₁)
    have e₂ : (((d₂ : ℤ) + (sB : ℤ) * (d : ℤ) : ℤ) : ℝ) / N = δ₂ := by
      rw [div_eq_iff hN0.ne']
      exact_mod_cast hδ₂.symm.trans (mul_comm N δ₂)
    rw [CurveWithDegreeOneDivisor.vojtaHeight, e₁, e₂, hhz, hhw, hhB]
    push_cast
    ring
  have h := (abs_le.1 (hκ d₁ d₂ d z' w')).2
  rw [hV] at h
  have hzz := neronPairing_self_nonneg X A (one_le_two.trans hg) j hj D hrad hsupp kbar
    (.ofMul (Over.homMk (z'.1 ≫ π) (by simp [hπ.w, reassoc_of% z'.2]) ≫ j))
  have hww := neronPairing_self_nonneg X A (one_le_two.trans hg) j hj D hrad hsupp kbar
    (.ofMul (Over.homMk (w'.1 ≫ π) (by simp [hπ.w, reassoc_of% w'.2]) ≫ j))
  simp only [Int.cast_natCast, Nat.abs_cast] at h
  simp only [pair, Real.sq_sqrt hzz, Real.sq_sqrt hww]
  have h1 : κ₁ / N * ((d₁ : ℝ) + d₂) + κ₂ * d ≤ (κ₁ / N + κ₂) * (d₁ + d₂ + d) := by
    have : 0 ≤ κ₁ / N := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) d₁, Nat.cast_nonneg (α := ℝ) d₂,
      Nat.cast_nonneg (α := ℝ) d]
  linarith [h, h1]

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **The main inequality** (Bombieri). Let `X = (C, P)` be a curve of genus `g ≥ 2` over a
number field `k` with a divisor `P` of degree one, `⟨ , ⟩ = Faltings.neronPairing` its Néron
form on `J(k̄)` and `|z| = √⟨z, z⟩`, with the standing data of Bombieri's Sections 9–10 over
`k`: a generic basis `x` of `L(N P)` giving `φNP`, `ψ = φNP × φNP`, and a basis `y` of
`H⁰(C × C, 𝒪(B))` generic for the projections giving `φB`, with `φNP^* 𝒪(1)` of class
`N P` and `φB^* 𝒪(1)` of the Vojta class `B`. For every `c₁₀` there are
`c₁, c₄, c₁₇` such that for `γ > 0`, every `e = o(n)` and `d₁, d₂, d` large with
`N δᵢ = dᵢ + s d`, `d₂ ≤ d₁`, `g d² < d₁ d₂ < g² d²`, `γ d₁ d₂ < d₁ d₂ - g d²`, every section
`s ≠ 0` of `Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d` with a representative `F` over `k` with
`h(F) ≤ c₁₀ (d₁ + d₂) / γ + e (d₁ + d₂)`, every `k̄`-point `p = (z, w)` of `C × C`, and every
pair `i`, if over some number field `K ⊆ k̄` of definition of `p` the points `z, w` lie outside
`Faltings.BombieriSiegel.exceptionalSet` and `i` is admissible for `s` at `p`, then
`-c₄ (i₁ |z|² + i₂ |w|²) - c₁₇ (d₁ + i₁ + i₂) - c₁₇ d₁ / γ`
`  ≤ d₁ / (2g) |z|² + d₂ / (2g) |w|² - d ⟨z, w⟩ + c₁ (d₁ |z| + d₂ |w|)`. -/
@[faltings "lem_bvr_main_inequality"]
public theorem exists_neg_le_neronPairing_of_isAdmissiblePair {k : Type u} [Field k]
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
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0)
    -- the constant `c₁₀` of the bound on `h(𝓕)`
    (c₁₀ : ℝ) :
    let g : ℝ := genus X.f
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ c₁ c₄ c₁₇ : ℝ, ∀ γ : ℝ, 0 < γ →
    ∀ e : ℕ → ℝ, e =o[Filter.atTop] (fun t : ℕ => (t : ℝ)) →
    ∃ D₀ : ℕ, ∀ d₁ d₂ d δ₁ δ₂ : ℕ, D₀ ≤ d₁ → D₀ ≤ d₂ → D₀ ≤ d →
      N * δ₁ = d₁ + sB * d → N * δ₂ = d₂ + sB * d → d₂ ≤ d₁ →
      g * (d : ℝ) ^ 2 < d₁ * d₂ → (d₁ * d₂ : ℝ) < g ^ 2 * d ^ 2 →
      γ * (d₁ * d₂ : ℝ) < d₁ * d₂ - g * d ^ 2 →
    -- the section `s ≠ 0` of `𝒪(V)` and its representative with coefficients in `k`
    ∀ s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤), s ≠ 0 →
    ∀ F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂),
      IsVojtaRepresentative ψ φB δ₁ δ₂ d s
        (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1) →
      (if hF : ∃ i, (F i).1 ≠ 0 then polynomialFamilyHeight (fun i => (F i).1) hF else 0) ≤
        c₁₀ * (d₁ + d₂) / γ + e (d₁ + d₂) →
    -- the `k̄`-point `p = (z, w)` of `C × C` and the pair `i`
    ∀ (p : Spec (.of kbar) ⟶ pullback X.f X.f)
      (z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f),
      z.left = p ≫ pullback.fst X.f X.f → w.left = p ≫ pullback.snd X.f X.f →
    ∀ i : ℕ × ℕ,
    -- a number field `K ⊆ k̄` over which `p` is defined, and the base change `C_K`
    ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] kbar)
      (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
      (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
    let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
    let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
      pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        hπ.w.symm hπ.w.symm
    ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
        Transcendental K (xK 1 / xK 0))
      (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
      -- the base changes `ψ_K, φ_K` of `ψ, φ_B`, and the section `s_K` represented by `F`
      (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
      (_hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hψK₁ : ψK ≫ pullback.fst _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (_hψK₂ : ψK ≫ pullback.snd _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        projectiveSpaceOver m (Spec (.of K)))
      (_hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
        ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
      (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
      (_hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
      -- the `K`-point `p_K` through which `p` factors
      (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
      [pK.IsOver (Spec (.of K))]
      (_hpK : Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ pK ≫ ιS = p),
      -- `z, w ∉ Z`, and `i` admissible for `s` at `(z, w)`
      pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
      pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
      IsAdmissiblePair (vojtaLineBundle ψK φK δ₁ δ₂ d) sK pK i →
      -c₄ * (i.1 * √(pair z z) ^ 2 + i.2 * √(pair w w) ^ 2) - c₁₇ * (d₁ + i.1 + i.2) -
          c₁₇ * d₁ / γ ≤
        d₁ / (2 * g) * √(pair z z) ^ 2 + d₂ / (2 * g) * √(pair w w) ^ 2 - d * pair z w +
          c₁ * (d₁ * √(pair z z) + d₂ * √(pair w w)) := by
  intro g pair
  obtain ⟨c₄, hL6⟩ := exists_le_vojtaHeight_of_isAdmissiblePair X A hg j hj D hrad hsupp kbar
    N hN hn x hx φNP hφNP hφNPx
  obtain ⟨c₁, c₂, -, hc₂, hup⟩ := exists_logHeight_le_neronPairing X A hg j hj D hrad hsupp kbar
    N hN φNP hφNP hφNPL sB hsB φB hφB hφBB
  refine ⟨c₁, c₄, max c₄ 0 + 2 + (2 + 2 * (sB : ℝ)) + n * (2 + 2 * (sB : ℝ)) + 2 * (n : ℝ) ^ 2 +
    3 * c₂ + 2 * max c₁₀ 0, fun γ hγ e he => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ t ≥ T, e t ≤ t := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (he.bound one_pos)
    refine ⟨T, fun t ht => (le_abs_self _).trans ?_⟩
    simpa using hT t ht
  refine ⟨T + 1, ?_⟩
  intro d₁ d₂ d δ₁ δ₂ hd₁ hd₂ hd hδ₁ hδ₂ hd21 hlo hhi hγd s hs F hFrep hFh p z w hz hw i K _ _ _
    ι CK _ π hπ _ _ _ _ xK ιS hξ₁₀ DK hDK ψK hψKπ hψK₁ hψK₂ φK hφKπ hφK sK hsK pK _ hpK
    hzZ hwZ hadm
  have hS : IsPullback ιS (pullback.snd _ _ ≫ (CK ↘ Spec (.of K)))
      (pullback.fst X.f X.f ≫ X.f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have h := isPullback_map hπ
    rwa [pullback.condition (f := CK ↘ Spec (.of K)) (g := CK ↘ Spec (.of K))] at h
  have : IsIntegral (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) :=
    isIntegral_pullback_of_isPullback X hπ
  have hι₁ : ιS ≫ pullback.fst X.f X.f = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hι₂ : ιS ≫ pullback.snd X.f X.f = pullback.snd _ _ ≫ π := pullback.lift_snd _ _ _
  have : IsDominant (ιS ≫ pullback.fst X.f X.f) := by
    rw [hι₁]; infer_instance
  have : IsDominant (ιS ≫ pullback.snd X.f X.f) := by
    rw [hι₂]; infer_instance
  have hzK := comp_fst_comp_over_eq_id pK
  have hwK := comp_snd_comp_over_eq_id pK
  have hz' : (pK ≫ ιS ≫ pullback.fst X.f X.f) ≫ X.f =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hι₁, ← Category.assoc, Category.assoc, hπ.w, ← Category.assoc, hzK, Category.id_comp]
  have hw' : (pK ≫ ιS ≫ pullback.snd X.f X.f) ≫ X.f =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hι₂, ← Category.assoc, Category.assoc, hπ.w, ← Category.assoc, hwK, Category.id_comp]
  let z' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f :=
    Over.homMk (pK ≫ ιS ≫ pullback.fst X.f X.f) hz'
  let w' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f :=
    Over.homMk (pK ≫ ιS ≫ pullback.snd X.f X.f) hw'
  have hzC : (pK ≫ pullback.fst _ _) ≫ π = z'.left := by
    rw [Category.assoc, ← hι₁]; rfl
  have hwC : (pK ≫ pullback.snd _ _) ≫ π = w'.left := by
    rw [Category.assoc, ← hι₂]; rfl
  have hzbar : z.left = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ z'.left := by
    rw [hz, ← hpK, Category.assoc, Category.assoc]; rfl
  have hwbar : w.left = Spec.map (CommRingCat.ofHom (ι : K →+* kbar)) ≫ w'.left := by
    rw [hw, ← hpK, Category.assoc, Category.assoc]; rfl
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : Smooth (CK ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @Smooth) hπ inferInstance
  obtain ⟨s₁, s₂, hs₁, hs₂, hadm'⟩ :=
    exists_stalk_isAdmissiblePair DK xK hξ₁₀ ψK φK _ _ _ sK pK hzZ hwZ hadm
  have hs₁' : algebraMap _ (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).functionField s₁ =
      functionFieldMap (ιS ≫ pullback.fst _ _) (x 1 / x 0) := by
    rw [hs₁, ← Lemma6EstimateForDerivatives.functionFieldMap_comp_apply' _ _ hι₁.symm]
    exact congrArg _ (map_div₀ _ _ _).symm
  have hs₂' : algebraMap _ (pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).functionField s₂ =
      functionFieldMap (ιS ≫ pullback.snd _ _) (x 1 / x 0) := by
    rw [hs₂, ← Lemma6EstimateForDerivatives.functionFieldMap_comp_apply' _ _ hι₂.symm]
    exact congrArg _ (map_div₀ _ _ _).symm
  obtain ⟨a, ha, hza⟩ := CurveWithDegreeOneDivisor.exists_eq_projectiveSpacePoint
    (z'.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  obtain ⟨b, hb, hwb⟩ := CurveWithDegreeOneDivisor.exists_eq_projectiveSpacePoint
    (w'.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  obtain ⟨e', he', hpe⟩ := CurveWithDegreeOneDivisor.exists_eq_projectiveSpacePoint
    (pK ≫ ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
  have h6 := hL6 sB hsB φB hφB d₁ d₂ d δ₁ δ₂ (by omega) (by omega) (by omega) hδ₁.symm hδ₂.symm K ι
    CK (CK ↘ Spec (.of K)) π hπ hξ₁₀ DK hDK _ ιS (pullback.snd _ _ ≫ (CK ↘ Spec (.of K))) hS ψK
    (hψKπ.trans pullback.condition) hψK₁ hψK₂ φK (hφKπ.trans pullback.condition) hφK sK _ hsK
    pK ((Category.assoc _ _ _).symm.trans hwK) z' w' rfl rfl (pK ≫ pullback.fst _ _)
    (pK ≫ pullback.snd _ _) hzK hwK hzC hwC hzZ hwZ z w hzbar hwbar s₁ s₂ hs₁' hs₂' i.1 i.2 hadm'
    a b ha hb e' he' hza hwb hpe
  have hup' := hup d₁ d₂ d δ₁ δ₂ hδ₁ hδ₂ K ι (pK ≫ ιS) (by simpa using hz') z w
    (by simpa [z'] using hzbar) (by simpa [w'] using hwbar) a b ha hb e' he'
    (by simpa [z'] using hza) (by simpa [w'] using hwb) (by simpa using hpe)
  have hFK : Height.logHeight (fun α : (i : Fin (m + 1)) × (MvPolynomial.map
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1).support =>
        (Scheme.ΓSpecIso (.of K)).hom ((MvPolynomial.map
          ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F α.1).1).coeff α.2)) /
        Module.finrank ℚ K ≤
      (if hF : ∃ i, (F i).1 ≠ 0 then polynomialFamilyHeight (fun i => (F i).1) hF else 0) :=
    logHeight_coeff_map_div_finrank_le (K := K) (fun i => (F i).1)
  have hg2 : (2 : ℝ) ≤ g := show (2 : ℝ) ≤ (genus X.f : ℝ) by exact_mod_cast hg
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast (show 1 ≤ d₁ by omega)
  have hdd₁ : (d : ℝ) ≤ d₁ := by
    have h21 : (d₂ : ℝ) ≤ d₁ := by exact_mod_cast hd21
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ g - 1) (sq_nonneg (d : ℝ)),
      mul_le_mul_of_nonneg_left h21 (Nat.cast_nonneg (α := ℝ) d₁)]
  have hδ₁le : (δ₁ : ℝ) ≤ d₁ + sB * d := by
    exact_mod_cast (Nat.le_mul_of_pos_left δ₁ (by omega : 0 < N)).trans_eq hδ₁
  have hδ₂le : (δ₂ : ℝ) ≤ d₂ + sB * d := by
    exact_mod_cast (Nat.le_mul_of_pos_left δ₂ (by omega : 0 < N)).trans_eq hδ₂
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hE : e (d₁ + d₂) ≤ (d₁ : ℝ) + d₂ := by exact_mod_cast hT (d₁ + d₂) (by omega)
  dsimp only at h6
  exact neg_le_of_le_vojtaHeight_of_vojtaHeight_le hγ hc₂ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hn1 (Nat.cast_nonneg _) hd₁' (Nat.cast_nonneg _) (by exact_mod_cast hd21) hdd₁
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hδ₁le hδ₂le hE h6 hup'
    (hFK.trans (by exact_mod_cast hFh))

end Faltings.BombieriRoth
