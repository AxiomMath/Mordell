module

public import Mordell.Attr
public import Mordell.BombieriVojta.Norm.NumeratorZeros
public import Mordell.BombieriVojta.Norm.PolynomialTPolynomial
public import Mordell.BombieriVojta.Projection.GenericCoordinatesB
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.AlgebraicGeometry.Norm.Divisor
public import Mordell.Curve.Topology
public import Mordell.AlgebraicGeometry.RationalPoint
public import Mordell.Curve.FunctionField
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Places
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineOrders
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsTensorProduct
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.TwistedFrobeniusFixedPoints
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import Mathlib
public import Mordell.BombieriVojta.Norm.FormNormPolynomial

/-!
# The degrees of the numerators `U_i`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k`
of characteristic zero (a number field, or an algebraic extension of `ℚ` such as `ℚ̄`), with a
divisor `P` of degree one, and let `X = C ×_k C` with projections `pr₁, pr₂` and diagonal `Δ`.
Fix an integer `s ≥ 1` such that `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` is very ample. Let
`y₀, …, yₘ` be a basis of `H⁰(X, 𝒪(B))` giving the embedding `φ_B : X → ℙᵐ`, with
divisors of zeros `Dᵢ`, and put `ηᵢ = yᵢ / y₀ ∈ k(X)`. Fix `N ≥ 2g + 1`, put `n = N - g`, and
let `x₀, …, xₙ` be a generic basis of `L(N P)` giving the embedding `φ_{NP} : C → ℙⁿ`. Assume
the coordinates `y` are generic for the projections `π_{ab} = (ξ_a, ξ'_b) : X → ℙ¹ × ℙ¹`, where
`ξ_a = x_a / x₀` on the first factor and `ξ'_b = x_b / x₀` on the second. For `1 ≤ a, b ≤ n`,
write `Norm` for the field norm of `k(X)` over `k(ξ_a, ξ'_b)` and `Norm ηᵢ = Uᵢ / Vᵢ` in lowest
terms in `R = k[ξ_a, ξ'_b]`.

Then for `i ≠ 0` the numerator `Uᵢ` has degree exactly `N s` in `ξ_a` and exactly `N s` in
`ξ'_b`. Indeed the affine zero divisor of `Uᵢ` is `π_* Dᵢ`, and its intersection with a general
fibre `c × ℙ¹` is `Dᵢ · (π_a^* c × C) = N · B · (P × C) = N s`.

The fibres of the components of `P × C` and `C × P` over the closed points of the support of `P`
are handled by `Faltings.exists_isGenericPoint_preimage_singleton` (the fibre of `pr₁` over a
closed point `c` has a generic point over the generic point of `C`) and
`Faltings.residueDegree_snd_of_isGenericPoint_preimage_singleton` (its residue degree over `C` is
`[κ(c) : k]`), so that the fibre over `c` contributes `[κ(c) : k] N`, and the contributions add
up to `deg P · N = N`.

## Main results

* `Faltings.degreeOf_num_eq_of_isReducedNormRepresentation`: the numerators `U i`, `i ≠ 0`, of
  a family of reduced representations of the norms `Norm ηᵢ` have degree `N * s` in each of the
  two variables of `R = MvPolynomial (Fin 2) k`.
* `Faltings.exists_isGenericPoint_preimage_singleton`,
  `Faltings.snd_eq_genericPoint_of_isGenericPoint_preimage_singleton`,
  `Faltings.residueDegree_snd_of_isGenericPoint_preimage_singleton`: the fibre of `C ×_k C` over a
  closed point `c` of the first factor has a generic point, lying over the generic point of the
  second factor with residue degree `[κ(c) : k]`.
* `Faltings.residueDegree_genericPoint_of_isPullback`: the residue degree at the generic point of
  a base change along a morphism of spectra of fields.
* `Faltings.chart_weight`: the weight of a curve over the generic point, on an affine chart.
* `Faltings.BombieriRoth.transcendental_div`: under (G1) the affine coordinates `x_a / x₀` are
  transcendental.
* `Faltings.BombieriRoth.exists_section_of_residueDegree_eq_one`: a point of residue degree one
  is a rational point.
* `Faltings.BombieriRoth.isFractionRing_adjoin_pair`: `k⟮t, u⟯` is the fraction field of
  `k[X₀, X₁]` when `X₀ ↦ t`, `X₁ ↦ u` is injective.

## Implementation notes

The setting is that of `Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`.
The divisor `P` of degree one is `P₁ : C →₀ ℤ`, supported on closed points with
`∑ᶠ Q, P₁ Q · [κ(Q) : k] = 1`; `L(N P)` is the span of `x` in the form of
`Faltings.BombieriSiegel.IsGenericBasis.span_eq` for the divisor `N • P₁`, and the genericity of
`x` is
`Faltings.BombieriSiegel.SatisfiesG1`, `SatisfiesG2`, `SatisfiesG3`. The product is any pullback
square `IsPullback pr₁ pr₂ f f`, and `ι₁ ι₂ : k(C) →ₐ[k] k(X)` are the pull-backs of rational
functions, pinned by their values on germs. The embeddings `φ_{NP}` and `φ_B` into
`projectiveSpaceOver` are pinned at the generic point by the coordinates `x` and `y`, and
`ψ = φ_{NP} × φ_{NP}`.

Divisors are written through the order of vanishing `AlgebraicGeometry.Scheme.ord` at the
codimension-one points: a section of `𝒪(B)` is a rational function `h` with `div h + B ≥ 0`, and
its divisor of zeros is `div h + B`. `B` is written as in `Faltings.main_inequality`: the fibres
`pr₁⁻¹ c`, `pr₂⁻¹ c` over the points `c` of the support of `P₁` enter through their generic points,
with multiplicities `(s + 1) P₁(c)`, and `Δ` through its generic point. The genericity of `y`
is stated on `X` over `k`, for every pair `(a', b')`,
through the subfield `k(ξ_{a'}, ξ'_{b'})` of `k(X)`, as in
`Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`.

The ring `R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k`, with its algebra map to the subfield
`k⟮ξ_a, ξ'_b⟯` of `k(X)` pinned by `X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`. The indices `1 ≤ a, b ≤ n` are
`a.succ`, `b.succ` for `a b : Fin n`.

The degree in `ξ_a` is computed on the generic fibre of the second coordinate. Over a horizontal
prime divisor `y` of `𝔸² = Spec k[ξ_a, ξ'_b]`, the order of `Uᵢ` is the push-forward of the zero
divisor `Dᵢ = div yᵢ + B` along the finite chart `W = pr₁⁻¹ C₀ ∩ pr₂⁻¹ C₀ ⟶ 𝔸²`, where
`C₀ = φ_{NP}⁻¹ D₊(T₀)`: the norm formula for divisors gives it for `ηᵢ`, and genericity condition
(G1) separates the zeros of `yᵢ` from those of `y₀`. The degree formula on `ℙ¹` over `k(ξ'_b)`,
read on `W` and on the chart `W'` at `ξ_a = ∞` (presented by the embedding `X₀ ↦ X₀⁻¹` of
`k[X₀, X₁]` into its fraction field), turns `Σ_y [κ(y) : k(ξ'_b)] · ord_y (Norm yᵢ)` into minus
its part at infinity, where `Dᵢ` has no component by (G2). What is left is the push-forward of
`B` to the generic fibre: the fibre `c × C` maps with degree `[κ(c) : k] · [k(C) : k(ξ_b)] =
[κ(c) : k] N`, `Δ` with degree `N`, by the degree formula on `C`, and `C × c` is vertical, so the
degree is `(s + 1) Σ_c P₁(c) [κ(c) : k] N - N = (s + 1) N - N = N s`. The degree in `ξ'_b` follows
by exchanging the two factors.

The charts `D₊(T_j)` of `projectiveSpaceOver` and the ratios `T_i / T_j` are read on its integral
model through `projectiveSpaceOver.toIntegralAtUniverse`, as in
`Faltings.BombieriRoth.exists_germ_app_ratio_eq_div`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 618, and
  Section 9, pp. 632–633.
-/

open Faltings.BombieriRoth (exists_tensor_chart injective_aeval_of_transcendental)

open Faltings.BombieriRoth (exists_fst_eq_and_snd_eq linearIndependent_pow_of_transcendental)

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- The instance `IsProjectiveVariety k f → IsProperVariety k f` opens a second route to `IsVariety`
and makes instance searches with unassigned arguments (`map_mul` on stalk maps) diverge here. -/
attribute [-instance] AlgebraicGeometry.instIsProperVarietyOfIsProjectiveVariety

universe u

open Order

section AlgebraicGeometry.Proj

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- On `D₊(f) ∩ D₊(g)` for `f, g, h` of degree one, the germs of `h / f` and `f / g` multiply to
the germ of `h / g`. -/
private theorem germ_mul_germ_awayToSection_eq {f g h : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hf' : f ∈ 𝒜 (1 • 1)) (hh' : h ∈ 𝒜 (1 • 1)) (y : AlgebraicGeometry.Proj 𝒜)
    (hyf : y ∈ Proj.basicOpen 𝒜 f) (hyg : y ∈ Proj.basicOpen 𝒜 g) :
    (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hyf
        (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 h hh')) *
      (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
        (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
        (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 h hh')) := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have e₁ := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f y hyf).hom
    (Away.mk 𝒜 hf 1 h hh'))
  have e₂ := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 g y hyg).hom
    (Away.mk 𝒜 hg 1 f hf'))
  have e₃ := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 g y hyg).hom
    (Away.mk 𝒜 hg 1 h hh'))
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) y hyf
    (Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 h hh')) = _ at e₁
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
    (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 f hf')) = _ at e₂
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 g) y hyg
    (Proj.awayToSection 𝒜 g (Away.mk 𝒜 hg 1 h hh')) = _ at e₃
  rw [e₁, e₂, e₃]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  change (Proj.stalkIso' 𝒜 y).symm _ * (Proj.stalkIso' 𝒜 y).symm _ =
    (Proj.stalkIso' 𝒜 y).symm _
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [val_mul]
  change (Localization.mk h ⟨f ^ 1, _⟩ : Localization.AtPrime _) * Localization.mk f ⟨g ^ 1, _⟩ =
    Localization.mk h ⟨g ^ 1, _⟩
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Regular points lie in the chart `D₊(X_{i₀})`**, the version of
`Faltings.mem_preimage_basicOpen_of_mem_range` for any chart index. Let `φ : C ⟶ ℙⁿ` be a morphism
from a normal curve whose restriction to `φ⁻¹ D₊(X_{i₀})` has coordinate functions
`x j / x i₀`, where the `x j` are sections of `𝒪(E)` with `x i₀, x a` without common zero. If
`x a / x i₀` is regular at `c`, then `φ c ∈ D₊(X_{i₀})`. -/
private theorem mem_preimage_basicOpen_X_of_mem_range {k : Type u} [Field k] {R : Type u}
    [CommRing R] {C : Scheme.{u}} [IsLocallyNoetherian C] [IsNormal C] (f₀ : C ⟶ Spec (.of k))
    [IsCurve k f₀]
    {n : ℕ} (i₀ : Fin (n + 1)) (E : C → ℤ) (x : Fin (n + 1) → C.functionField) (hx : ∀ j, x j ≠ 0)
    (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z)
    (φ : C ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hφ_ne : ((φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i₀) : C.Opens) : Set C).Nonempty)
    (hφ : ∀ [Nonempty (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i₀))] (j : Fin (n + 1)),
      C.germToFunctionField _ (φ.app _ (Proj.awayToSection _ (MvPolynomial.X i₀)
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R i₀)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X R j)))) = x j / x i₀)
    {a : Fin (n + 1)}
    (hG1 : ∀ z, Order.coheight z = 1 → C.ord (x i₀) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    {c : C} (hc : x a / x i₀ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField)) :
    c ∈ φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i₀) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  have hgen : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  by_contra hc0
  have hcg : c ≠ genericPoint C := fun h => hc0 (h ▸ hgen _ hφ_ne)
  have hc1 : Order.coheight c = 1 := IsCurve.coheight_eq_one f₀ hcg
  have hord : 0 ≤ C.ord (x a / x i₀) c :=
    (ord_nonneg_iff hc1 (div_ne_zero (hx a) (hx i₀))).mpr hc
  rw [ord_div (hx a) (hx i₀)] at hord
  have h0 : C.ord (x i₀) c + E c = 0 := by
    rcases hG1 c hc1 with h | h
    · exact h
    · have := hxE i₀ c
      omega
  have hreg : ∀ j, x j / x i₀ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) :=
    fun j => by
      refine (ord_nonneg_iff hc1 (div_ne_zero (hx j) (hx i₀))).mp ?_
      rw [ord_div (hx j) (hx i₀)]
      have := hxE j c
      omega
  have hy0 : MvPolynomial.X i₀ ∈ (φ c).asHomogeneousIdeal := by
    by_contra h
    exact hc0 h
  obtain ⟨j, hj⟩ : ∃ j, φ c ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) :=
    TopologicalSpace.Opens.mem_iSup.1
      (by rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top R (Fin (n + 1))]; trivial)
  have hcj : c ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := hj
  have hX : ∀ i, MvPolynomial.X i ∈ 𝒜 1 := fun i =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R i)
  have hX' : ∀ i, MvPolynomial.X i ∈ 𝒜 (1 • 1) := fun i => by simpa using hX i
  have hnu : ¬ IsUnit (C.presheaf.germ _ c hcj (φ.app _ (Proj.awayToSection 𝒜 (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X i₀) (hX' i₀))))) := by
    rw [(Scheme.Hom.germ_stalkMap_apply φ _ c hcj _).symm]
    intro hu
    have hu' := isUnit_of_map_unit (φ.stalkMap c).hom _ hu
    exact ((isUnit_germ_awayToSection_iff 𝒜 (hX j) 1 _ (hX' i₀) (φ c) hj).mp hu') hy0
  have hg0 : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i₀) := hgen _ hφ_ne
  have hgj : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := hgen _ ⟨c, hcj⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i₀)) := ⟨⟨_, hg0⟩⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) := ⟨⟨_, hgj⟩⟩
  have hrel : C.germToFunctionField _ (φ.app _ (Proj.awayToSection 𝒜 (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X i₀) (hX' i₀)))) *
        (x j / x i₀) = 1 := by
    rw [← hφ j]
    change C.presheaf.germ _ (genericPoint C) hgj _ * C.presheaf.germ _ (genericPoint C) hg0 _ = 1
    rw [(Scheme.Hom.germ_stalkMap_apply φ _ _ hgj _).symm,
      (Scheme.Hom.germ_stalkMap_apply φ _ _ hg0 _).symm, ← map_mul]
    exact (congrArg (φ.stalkMap (genericPoint C))
      (germ_mul_germ_awayToSection 𝒜 (hX j) (hX i₀) (hX' j) (hX' i₀) (φ (genericPoint C)) hgj
        hg0)).trans (map_one _)
  obtain ⟨t, ht⟩ := hreg j
  apply hnu
  refine isUnit_iff_exists_inv.mpr ⟨t, ?_⟩
  apply IsFractionRing.injective (C.presheaf.stalk c) C.functionField
  rw [map_mul, ht, Scheme.algebraMap_germ_eq_germToFunctionField, hrel, map_one]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Change of chart.** If `φ : C ⟶ ℙⁿ` has coordinate functions `x j / x 0` on `φ⁻¹ D₊(X₀)`, then
for every `a` the open `φ⁻¹ D₊(X_a)` contains the generic point and the coordinate functions there
are `x j / x a`. -/
private theorem chart_change {R : Type u} [CommRing R] {C : Scheme.{u}} [IsIntegral C] {n : ℕ}
    (x : Fin (n + 1) → C.functionField) (hx : ∀ j, x j ≠ 0)
    (φ : C ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hφ_ne : ((φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) : C.Opens) : Set C).Nonempty)
    (hφ : ∀ [Nonempty (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0))] (j : Fin (n + 1)),
      C.germToFunctionField _ (φ.app _ (Proj.awayToSection _ (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R 0)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X R j)))) = x j / x 0)
    (a : Fin (n + 1)) :
    ((φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X a) : C.Opens) : Set C).Nonempty ∧
    ∀ [Nonempty (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X a))] (j : Fin (n + 1)),
      C.germToFunctionField _ (φ.app _ (Proj.awayToSection _ (MvPolynomial.X a)
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R a)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X R j)))) = x j / x a := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  have hgen : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hX : ∀ i, MvPolynomial.X i ∈ 𝒜 1 := fun i =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R i)
  have hX' : ∀ i, MvPolynomial.X i ∈ 𝒜 (1 • 1) := fun i => by simpa using hX i
  have hg0 : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) := hgen _ hφ_ne
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0)) := ⟨⟨_, hg0⟩⟩
  -- the germ of `X_a / X₀` at the generic point is a unit
  have hu : IsUnit ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X 0))
      (φ (genericPoint C)) hg0 (Proj.awayToSection 𝒜 (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk 𝒜 (hX 0) 1 (MvPolynomial.X a) (hX' a)))) := by
    refine isUnit_of_map_unit (φ.stalkMap (genericPoint C)).hom _ ?_
    rw [Scheme.Hom.germ_stalkMap_apply φ _ _ hg0]
    have h := hφ a
    change C.presheaf.germ _ (genericPoint C) hg0 _ = _ at h
    rw [h]
    exact isUnit_iff_ne_zero.mpr (div_ne_zero (hx a) (hx 0))
  have hga : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X a) :=
    (isUnit_germ_awayToSection_iff 𝒜 (hX 0) 1 _ (hX' a) (φ (genericPoint C)) hg0).mp hu
  refine ⟨⟨_, hga⟩, fun j => ?_⟩
  have hmul := congrArg (φ.stalkMap (genericPoint C)).hom
    (germ_mul_germ_awayToSection_eq 𝒜 (hX a) (hX 0) (hX' a) (hX' j) (φ (genericPoint C)) hga hg0)
  rw [map_mul, Scheme.Hom.germ_stalkMap_apply φ _ _ hga, Scheme.Hom.germ_stalkMap_apply φ _ _ hg0,
    Scheme.Hom.germ_stalkMap_apply φ _ _ hg0] at hmul
  have h1 := hφ a
  have h2 := hφ j
  change C.presheaf.germ _ (genericPoint C) hg0 _ = _ at h1 h2
  rw [h1, h2] at hmul
  change C.presheaf.germ _ (genericPoint C) hga _ = _
  rw [eq_div_iff (hx a)]
  rw [← mul_div_assoc, div_left_inj' (hx 0)] at hmul
  exact hmul

/-- The function field of `Spec R` as an `R`-algebra, for `R` a type. -/
@[instance_reducible]
private noncomputable def specAlgebra (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  haveI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)

attribute [local instance] specAlgebra

private theorem isFractionRing_functionField_spec (R : Type u) [CommRing R] [IsDomain R] :
    IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  haveI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  functionField_isFractionRing_of_affine (CommRingCat.of R)

attribute [local instance] isFractionRing_functionField_spec

section ChartNorm

/-- The order of vanishing at a point `y` of `Spec R` of an element of a fraction field of `R`,
read on the scheme `Spec R`. -/
private noncomputable def ordAt {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] (y : PrimeSpectrum R) (g : K) : ℤ :=
  (Spec (.of R)).ord (IsLocalization.algEquiv (nonZeroDivisors R) K
    (Spec (.of R)).functionField g) y

/-- An open immersion from a nonempty scheme into an integral scheme is dominant. -/
private theorem isDominant_of_isOpenImmersion {U Z : Scheme.{u}} [Nonempty U]
    [IrreducibleSpace Z] (i : U ⟶ Z) [IsOpenImmersion i] : IsDominant i := by
  rw [isDominant_iff]
  exact i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i.base

/-- On an affine open `V`, the map of function fields induced by `Spec Γ(X, V) ⟶ X` sends the
germ of a section to the image of the section in the function field of `Spec Γ(X, V)`. -/
private theorem dominantFunctionFieldMap_fromSpec_germ {X : Scheme.{u}} [IsIntegral X]
    {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V] [IsDomain Γ(X, V)]
    [IsDominant hV.fromSpec] (b : Γ(X, V)) :
    dominantFunctionFieldMap hV.fromSpec (X.germToFunctionField V b) =
      algebraMap Γ(X, V) (Spec Γ(X, V)).functionField b := by
  have hle : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    rw [hV.fromSpec_preimage_self]
  have h := congr($(Stacks.Chow.appLE_germToFunctionField_commutes hV.fromSpec V ⊤ hle) b)
  simp only [RingHom.comp_apply] at h
  rw [← h, Stacks.Chow.algebraMap_functionField_spec_eq_germ]
  change (Spec Γ(X, V)).presheaf.germ ⊤ _ trivial ((hV.fromSpec.appLE V ⊤ hle) b) =
    (Spec Γ(X, V)).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso Γ(X, V)).inv b)
  rw [Scheme.Hom.appLE, hV.fromSpec_app_self]
  simp only [← CommRingCat.comp_apply, Category.assoc]
  rw [← Functor.map_comp_assoc, show (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE hle).op =
    𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The divisor of a norm on an affine chart.** Let `V` be an affine open of an integral locally
Noetherian scheme `X` with `Γ(X, V)` a finite extension of a domain `R` of finite type over `k`,
and `K` a fraction field of `R` mapping to `k(X)` compatibly. For a nonzero rational function `h`
and a point `y` of `Spec R`, the order of `Norm_{k(X)/K} h` at `y` is the push-forward along
`Spec Γ(X, V) ⟶ Spec R` of the orders of `h`. -/
private theorem ordAt_norm_eq_finsum {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    [IsDomain Γ(X, V)] [Algebra k Γ(X, V)] [Algebra.FiniteType k Γ(X, V)]
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra k R]
    [Algebra.FiniteType k R] [Algebra R Γ(X, V)] [IsScalarTower k R Γ(X, V)]
    [Module.Finite R Γ(X, V)] (hinj : Function.Injective (algebraMap R Γ(X, V)))
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K X.functionField]
    [FiniteDimensional K X.functionField]
    (hKL : ∀ r, algebraMap K X.functionField (algebraMap R K r) =
      X.germToFunctionField V (algebraMap R Γ(X, V) r))
    {h : X.functionField} (hh : h ≠ 0) (y : PrimeSpectrum R) :
    ordAt y (Algebra.norm K h) =
      ∑ᶠ x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V)))).base ⁻¹' {y},
        X.ord h (hV.fromSpec.base x) *
          (AlgebraicCycle.mapCoeff (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))))
            coheight coheight x : ℤ) := by
  classical
  have : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing k Γ(X, V)
  let oX : (Spec Γ(X, V)).Over (Spec (.of k)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, V)))⟩
  let oY : (Spec (.of R)).Over (Spec (.of k)) := ⟨Spec.map (CommRingCat.ofHom (algebraMap k R))⟩
  have : LocallyOfFiniteType (Spec Γ(X, V) ↘ Spec (.of k)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType (Spec (.of R) ↘ Spec (.of k)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  set f : Spec Γ(X, V) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V)))
    with hfdef
  have : f.IsOver (Spec (.of k)) := ⟨by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (IsScalarTower.algebraMap_apply k R Γ(X, V) c).symm⟩
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsDominant f := isDominant_Spec_map_of_injective _ hinj
  let : Algebra (Spec (.of R)).functionField (Spec Γ(X, V)).functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  have hf : ∀ (U : (Spec (.of R)).Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
      (s : Γ(Spec (.of R), U)),
      algebraMap (Spec (.of R)).functionField (Spec Γ(X, V)).functionField
          ((Spec (.of R)).germToFunctionField U s) =
        (Spec Γ(X, V)).germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
    intro U _ _ s
    have := congr($(Stacks.Chow.appLE_germToFunctionField_commutes f U (f ⁻¹ᵁ U) le_rfl) s)
    simp only [RingHom.comp_apply, Scheme.Hom.appLE_eq_app] at this
    exact this.symm
  have : IsDominant hV.fromSpec := isDominant_of_isOpenImmersion _
  let eL : X.functionField ≃+* (Spec Γ(X, V)).functionField :=
    Stacks.Chow.functionFieldEquiv_openImmersion hV.fromSpec
  have heL : ∀ z, eL z = dominantFunctionFieldMap hV.fromSpec z := fun _ => rfl
  let eK : K ≃+* (Spec (.of R)).functionField :=
    (IsLocalization.algEquiv (nonZeroDivisors R) K (Spec (.of R)).functionField).toRingEquiv
  have hcompat : (algebraMap (Spec (.of R)).functionField (Spec Γ(X, V)).functionField).comp
      (eK : K →+* _) = (eL : X.functionField →+* _).comp (algebraMap K X.functionField) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [hKL, heL, dominantFunctionFieldMap_fromSpec_germ]
    change dominantFunctionFieldMap f (eK (algebraMap R K r)) = _
    rw [show eK (algebraMap R K r) = algebraMap (CommRingCat.of R) (Spec (.of R)).functionField r
      from AlgEquiv.commutes _ r]
    exact Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec
      (CommRingCat.ofHom (algebraMap R Γ(X, V))) r
  have hfr := Algebra.finrank_eq_of_equiv_equiv eK eL hcompat
  have : Module.Finite (Spec (.of R)).functionField (Spec Γ(X, V)).functionField :=
    Module.finite_of_finrank_pos (hfr ▸ Module.finrank_pos)
  have hh' : eL h ≠ 0 := (map_ne_zero_iff _ eL.injective).mpr hh
  have key := Faltings.ord_norm_eq_finsum_mapCoeff_mul_ord (K := k) f hf hh' y
  have hn : Algebra.norm (Spec (.of R)).functionField (eL h) = eK (Algebra.norm K h) := by
    rw [Algebra.norm_eq_of_equiv_equiv eK eL hcompat h, RingEquiv.apply_symm_apply]
  unfold ordAt
  change (Spec (.of R)).ord (eK (Algebra.norm K h)) y = _
  rw [← hn, key]
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [heL, Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion hV.fromSpec h x]

/-- **The divisor of a norm on an affine chart**, for a presentation `θ : R → K` of `K` as a
fraction field of `R` given as a ring map: the version of `ordAt_norm_eq_finsum` with the algebra
structures supplied as maps. -/
private theorem ordAt_norm_eq_finsum_of_ringHom {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    [IsDomain Γ(X, V)] [Algebra k Γ(X, V)] [Algebra.FiniteType k Γ(X, V)]
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra k R]
    [Algebra.FiniteType k R] (ψ : R →+* Γ(X, V))
    (hψk : ∀ c : k, ψ (algebraMap k R c) = algebraMap k Γ(X, V) c) (hψ : ψ.Finite)
    (hinj : Function.Injective ψ)
    {K : Type u} [Field K] (θ : R →+* K) (hθ : @IsFractionRing R _ K _ θ.toAlgebra)
    [Algebra K X.functionField] [FiniteDimensional K X.functionField]
    (hKL : ∀ r, algebraMap K X.functionField (θ r) = X.germToFunctionField V (ψ r))
    {h : X.functionField} (hh : h ≠ 0) (y : PrimeSpectrum R) :
    @ordAt R _ _ _ K _ θ.toAlgebra hθ y (Algebra.norm K h) =
      ∑ᶠ x ∈ (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' {y},
        X.ord h (hV.fromSpec.base x) *
          (AlgebraicCycle.mapCoeff (Spec.map (CommRingCat.ofHom ψ)) coheight coheight x : ℤ) := by
  let : Algebra R K := θ.toAlgebra
  let : Algebra R Γ(X, V) := ψ.toAlgebra
  have : IsScalarTower k R Γ(X, V) := IsScalarTower.of_algebraMap_eq fun c => (hψk c).symm
  have : Module.Finite R Γ(X, V) := hψ
  exact ordAt_norm_eq_finsum (k := k) hV hinj hKL hh y

/-- The residue degree of a dominant morphism of integral schemes at the generic point is the
degree of the extension of function fields. -/
private theorem residueDegree_genericPoint_eq_finrank {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (g : X ⟶ Y) [IsDominant g] :
    letI := (dominantFunctionFieldMap g).toAlgebra
    g.residueDegree (genericPoint X) = Module.finrank Y.functionField X.functionField := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap g).toAlgebra
  let : Algebra (Y.residueField (g (genericPoint X))) (X.residueField (genericPoint X)) :=
    (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  have hφ : functionFieldMap g = dominantFunctionFieldMap g :=
    (congrArg CommRingCat.Hom.hom
      (Stacks.Chow.stalkMap_cast_target g _ (map_genericPoint_of_isDominant g))).symm
  refine (Algebra.finrank_eq_of_equiv_equiv (genericResidueEquivOfDominant g)
    (genericResidueEquiv X) ?_).symm
  rw [show algebraMap Y.functionField X.functionField = functionFieldMap g from hφ.symm]
  exact residueFieldMap_comp_genericResidueEquivOfDominant g

/-- On an affine chart as in `ordAt_norm_eq_finsum`, the residue degree of
`Spec Γ(X, V) ⟶ Spec R` at the generic point is `[k(X) : K]`. -/
private theorem chartResidueDegree_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V] [IsDomain Γ(X, V)]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra R Γ(X, V)]
    (hinj : Function.Injective (algebraMap R Γ(X, V)))
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K X.functionField]
    (hKL : ∀ r, algebraMap K X.functionField (algebraMap R K r) =
      X.germToFunctionField V (algebraMap R Γ(X, V) r)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V)))).residueDegree
      (genericPoint (Spec Γ(X, V))) = Module.finrank K X.functionField := by
  have : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  set f : Spec Γ(X, V) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V)))
    with hfdef
  have : IsDominant f := isDominant_Spec_map_of_injective _ hinj
  let : Algebra (Spec (.of R)).functionField (Spec Γ(X, V)).functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  have : IsDominant hV.fromSpec := isDominant_of_isOpenImmersion _
  let eL : X.functionField ≃+* (Spec Γ(X, V)).functionField :=
    Stacks.Chow.functionFieldEquiv_openImmersion hV.fromSpec
  have heL : ∀ z, eL z = dominantFunctionFieldMap hV.fromSpec z := fun _ => rfl
  let eK : K ≃+* (Spec (.of R)).functionField :=
    (IsLocalization.algEquiv (nonZeroDivisors R) K (Spec (.of R)).functionField).toRingEquiv
  have hcompat : (algebraMap (Spec (.of R)).functionField (Spec Γ(X, V)).functionField).comp
      (eK : K →+* _) = (eL : X.functionField →+* _).comp (algebraMap K X.functionField) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [hKL, heL, dominantFunctionFieldMap_fromSpec_germ]
    change dominantFunctionFieldMap f (eK (algebraMap R K r)) = _
    rw [show eK (algebraMap R K r) = algebraMap (CommRingCat.of R) (Spec (.of R)).functionField r
      from AlgEquiv.commutes _ r]
    exact Stacks.Chow.dominantFunctionFieldMap_algebraMap_spec
      (CommRingCat.ofHom (algebraMap R Γ(X, V))) r
  rw [residueDegree_genericPoint_eq_finrank f]
  exact (Algebra.finrank_eq_of_equiv_equiv eK eL hcompat).symm

/-- A section has residue degree one, and so does the morphism it is a section of, at its
image. -/
private theorem residueDegree_eq_one_of_section {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y)
    (h : s ≫ p = 𝟙 Y) (y : Y) : p.residueDegree (s y) = 1 ∧ s.residueDegree y = 1 := by
  have hc := residueDegree_comp s p y
  rw [h, Scheme.Hom.residueDegree_id] at hc
  exact ⟨Nat.eq_one_of_mul_eq_one_right hc.symm, Nat.eq_one_of_mul_eq_one_left hc.symm⟩

end ChartNorm

section PolySide

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The order of vanishing on `Spec R` of an element of `R` is read off its order of vanishing in
the localization of `R` at the point. -/
private theorem ordAt_algebraMap_eq (y : PrimeSpectrum R)
    (hy : y.asIdeal.height = 1) {a : R} (ha : a ≠ 0) {n : ℕ}
    (hn : Ring.ord (Localization.AtPrime y.asIdeal) (algebraMap R _ a) = n) :
    ordAt y (algebraMap R K a) = n := by
  have : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  have hy' : coheight (show Spec (CommRingCat.of R) from y) = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy
  unfold ordAt
  rw [AlgEquiv.commutes]
  change (Spec (CommRingCat.of R)).ord ((Spec (CommRingCat.of R)).germToFunctionField ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) y = n
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have ht : (Scheme.ΓSpecIso (CommRingCat.of R)).inv a ≠ 0 := fun h =>
    ha (hinj (by simpa using h))
  refine Stacks.Chow.ord_eq_ringOrd_germ hy' (V := ⊤) trivial _ ht ?_
  have hgerm : ((Spec (CommRingCat.of R)).presheaf.germ ⊤ y trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)
      = (Spec.stalkIso (CommRingCat.of R) y).commRingCatIsoToRingEquiv.symm
          (algebraMap R (Localization.AtPrime y.asIdeal) a) :=
    (congrArg (fun f : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk _ => f.hom a)
      (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) y)).symm
  have : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) :=
    (Spec.stalkIso (CommRingCat.of R) y).commRingCatIsoToRingEquiv.injective.isDomain
  rw [hgerm, Stacks.Chow.ord_congr
    (Spec.stalkIso (CommRingCat.of R) y).commRingCatIsoToRingEquiv.symm
    (algebraMap R (Localization.AtPrime y.asIdeal) a)]
  exact hn

/-- `ordAt` is additive. -/
private theorem ordAt_mul (y : PrimeSpectrum R) {g h : K} (hg : g ≠ 0) (hh : h ≠ 0) :
    ordAt y (g * h) = ordAt y g + ordAt y h := by
  unfold ordAt
  rw [map_mul]
  exact Scheme.ord_mul ((map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hg)
    ((map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hh)

private theorem ordAt_one (y : PrimeSpectrum R) : ordAt y (1 : K) = 0 := by
  have h := ordAt_mul (K := K) y (one_ne_zero) (one_ne_zero)
  rw [one_mul] at h
  omega

private theorem ordAt_inv (y : PrimeSpectrum R) {g : K} (hg : g ≠ 0) :
    ordAt y g⁻¹ = - ordAt y g := by
  have h := ordAt_mul y hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, ordAt_one] at h
  omega

private theorem ordAt_div (y : PrimeSpectrum R) {g h : K} (hg : g ≠ 0) (hh : h ≠ 0) :
    ordAt y (g / h) = ordAt y g - ordAt y h := by
  rw [div_eq_mul_inv, ordAt_mul y hg (inv_ne_zero hh), ordAt_inv y hh]
  ring

/-- An element of `R` outside the prime of a codimension-one point has order zero there. -/
private theorem ordAt_algebraMap_eq_zero (y : PrimeSpectrum R)
    (hy : y.asIdeal.height = 1) {a : R} (ha : a ∉ y.asIdeal) :
    ordAt y (algebraMap R K a) = 0 := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ y.asIdeal.zero_mem)
  have hu : IsUnit (algebraMap R (Localization.AtPrime y.asIdeal) a) :=
    IsLocalization.map_units _ (⟨a, ha⟩ : y.asIdeal.primeCompl)
  exact_mod_cast ordAt_algebraMap_eq (K := K) y hy ha0 (n := 0) (Ring.ord_of_isUnit hu)

/-- The order of an element of `R` at a codimension-one point is nonnegative, and positive when
the element lies in the prime of the point. -/
private theorem ordAt_algebraMap_nonneg_and_pos (y : PrimeSpectrum R)
    (hy : y.asIdeal.height = 1) {a : R} (ha : a ≠ 0) :
    0 ≤ ordAt y (algebraMap R K a) ∧ (a ∈ y.asIdeal → 0 < ordAt y (algebraMap R K a)) := by
  have hy1 : y.asIdeal.height = 1 := hy
  have : Ring.KrullDimLE 1 (Localization.AtPrime y.asIdeal) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal]
    exact_mod_cast hy1.le
  have hmem : algebraMap R (Localization.AtPrime y.asIdeal) a ∈
      nonZeroDivisors (Localization.AtPrime y.asIdeal) :=
    mem_nonZeroDivisors_of_ne_zero fun h => ha (IsLocalization.injective _
      y.asIdeal.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hmem)
  have hval := ordAt_algebraMap_eq (K := K) y hy ha hn.symm
  refine ⟨hval ▸ Int.natCast_nonneg n, fun hay => ?_⟩
  rw [hval]
  refine Int.natCast_pos.mpr (Nat.pos_of_ne_zero fun h0 => ?_)
  subst h0
  have hz : Module.length (Localization.AtPrime y.asIdeal) (Localization.AtPrime y.asIdeal ⧸
      Ideal.span {algebraMap R (Localization.AtPrime y.asIdeal) a}) = 0 := by
    change Ring.ord _ _ = 0
    rw [← hn]; rfl
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hz
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ y.asIdeal a).mp hz hay

/-- At the point of a prime element `q`, the order of `q` is one. -/
private theorem ordAt_algebraMap_prime (y : PrimeSpectrum R)
    (hy : y.asIdeal.height = 1) {q : R} (hq : Prime q)
    (hyq : y.asIdeal = Ideal.span {q}) : ordAt y (algebraMap R K q) = 1 := by
  refine ordAt_algebraMap_eq (K := K) y hy hq.ne_zero (n := 1) ?_
  refine Stacks.Chow.ord_eq_one_of_span_eq_maximalIdeal ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal,
    congrArg (Ideal.map (algebraMap R (Localization.AtPrime y.asIdeal))) hyq, Ideal.map_span,
    Set.image_singleton]

end PolySide

section Degree

variable {k : Type u} [Field k]

/-- The inclusion `k[X₁] → k[X₀, X₁]`. -/
private noncomputable abbrev ιT (k : Type u) [Field k] :
    MvPolynomial (Fin 1) k →+* MvPolynomial (Fin 2) k :=
  (MvPolynomial.rename Fin.succ : MvPolynomial (Fin 1) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom

private theorem finSuccEquiv_ιT (a : MvPolynomial (Fin 1) k) :
    MvPolynomial.finSuccEquiv k 1 (ιT k a) = Polynomial.C a := by
  have : ((MvPolynomial.finSuccEquiv k 1 : MvPolynomial (Fin 2) k →ₐ[k] _).comp
      (MvPolynomial.rename Fin.succ)) = Polynomial.CAlgHom (A := MvPolynomial (Fin 1) k) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [MvPolynomial.finSuccEquiv_X_succ]
  exact congr($this a)

/-- **The residue degree of a horizontal prime.** For a prime `q` of `k[X₀, X₁]` meeting `k[X₁]`
only in `0`, the residue field of `(q)` has degree `deg_{X₀} q` over `k(X₁)`. -/
private theorem finrank_residueField_eq_degreeOf {q : MvPolynomial (Fin 2) k} (hq : Prime q)
    [(Ideal.span {q}).IsPrime] {I : Ideal (MvPolynomial (Fin 1) k)} [I.IsPrime]
    (hI : I = (Ideal.span {q}).comap (ιT k)) (hbot : I = ⊥) :
    letI := (Ideal.ResidueField.map I (Ideal.span {q}) (ιT k) hI).toAlgebra
    Module.finrank I.ResidueField (Ideal.span {q}).ResidueField = q.degreeOf 0 := by
  classical
  subst hbot
  have hhor := hI
  let : Algebra (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField
      (Ideal.span {q}).ResidueField :=
    (Ideal.ResidueField.map ⊥ (Ideal.span {q}) (ιT k) hhor).toAlgebra
  set q' := MvPolynomial.finSuccEquiv k 1 q with hq'
  have hq'irr : Irreducible q' :=
    (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv k 1).toMulEquiv).mpr hq.irreducible
  have hdeg : q'.natDegree = q.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv q
  have hdeg0 : q'.natDegree ≠ 0 := by
    intro h0
    have hC : q' = Polynomial.C (q'.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hqι : q = ιT k (q'.coeff 0) := by
      apply (MvPolynomial.finSuccEquiv k 1).injective
      rw [finSuccEquiv_ιT, ← hq', ← hC]
    have hmem : q'.coeff 0 ∈ (Ideal.span {q}).comap (ιT k) := by
      rw [Ideal.mem_comap, ← hqι]; exact Ideal.mem_span_singleton_self q
    rw [← hhor, Ideal.mem_bot] at hmem
    exact hq.ne_zero (by rw [hqι, hmem, map_zero])
  have hprim : q'.IsPrimitive := hq'irr.isPrimitive hdeg0
  let : GCDMonoid (MvPolynomial (Fin 1) k) :=
    UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 1) k)
  have hirr : Irreducible (q'.map (algebraMap (MvPolynomial (Fin 1) k)
      (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField)) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).mp hq'irr
  set α : (Ideal.span {q}).ResidueField :=
    algebraMap (MvPolynomial (Fin 2) k) _ (MvPolynomial.X 0) with hα
  have hres : ∀ a : MvPolynomial (Fin 1) k,
      algebraMap (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField (Ideal.span {q}).ResidueField
        (algebraMap (MvPolynomial (Fin 1) k) _ a) =
      algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField (ιT k a) := fun a =>
    Ideal.ResidueField.map_algebraMap _ _ _ hhor a
  -- the evaluation `k[X₁][X] → κ(q)` at `α`
  let ψ : Polynomial (MvPolynomial (Fin 1) k) →+* (Ideal.span {q}).ResidueField :=
    Polynomial.eval₂RingHom ((algebraMap (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField
      (Ideal.span {q}).ResidueField).comp
      (algebraMap (MvPolynomial (Fin 1) k) (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField)) α
  have hψι : ∀ a : MvPolynomial (Fin 1) k, ψ (MvPolynomial.finSuccEquiv k 1 (ιT k a)) =
      algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField (ιT k a) := by
    intro a
    rw [finSuccEquiv_ιT, ← hres]
    simp [ψ]
  have hψ : ∀ r, ψ (MvPolynomial.finSuccEquiv k 1 r) =
      algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField r := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      have := hψι (MvPolynomial.C c)
      simpa [ιT] using this
    | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, map_mul]
      congr 1
      fin_cases i
      · simp [ψ, hα, MvPolynomial.finSuccEquiv_X_zero]
      · have := hψι (MvPolynomial.X 0)
        simpa [ιT] using this
  have haeval : Polynomial.aeval α (q'.map (algebraMap (MvPolynomial (Fin 1) k)
      (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change ψ q' = 0
    rw [hq', hψ q, Ideal.algebraMap_residueField_eq_zero]
    exact Ideal.mem_span_singleton_self q
  have hq0 := hirr.ne_zero
  have hint : IsIntegral (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField α :=
    IsAlgebraic.isIntegral ⟨_, hq0, haeval⟩
  have hmin := minpoly.eq_of_irreducible hirr haeval
  have hmindeg : (minpoly (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField α).natDegree =
      q'.natDegree := by
    rw [← hmin, Polynomial.natDegree_mul_C (inv_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr hq0)),
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _)]
  have hkey : ∀ r : MvPolynomial (Fin 2) k, algebraMap (MvPolynomial (Fin 2) k)
      (Ideal.span {q}).ResidueField r ∈
        IntermediateField.adjoin (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField {α} := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      have : algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField
          (MvPolynomial.C c) = algebraMap (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField
            (Ideal.span {q}).ResidueField
            (algebraMap (MvPolynomial (Fin 1) k) _ (MvPolynomial.C c)) := by
        rw [hres]; simp [ιT]
      rw [this]
      exact IntermediateField.algebraMap_mem _ _
    | add p p' hp hp' =>
      rw [map_add]; exact add_mem hp hp'
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      fin_cases i
      · exact IntermediateField.mem_adjoin_simple_self _ _
      · have : algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField
            (MvPolynomial.X 1) = algebraMap (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField
              (Ideal.span {q}).ResidueField
              (algebraMap (MvPolynomial (Fin 1) k) _ (MvPolynomial.X 0)) := by
          rw [hres]; simp [ιT]
        simp only [Fin.mk_one, Fin.isValue]
        rw [this]
        exact IntermediateField.algebraMap_mem _ _
  have htop : IntermediateField.adjoin (⊥ : Ideal (MvPolynomial (Fin 1) k)).ResidueField {α} =
      ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, -, rfl⟩ :=
      IsFractionRing.div_surjective (A := MvPolynomial (Fin 2) k ⧸ Ideal.span {q}) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : ∀ r, algebraMap (MvPolynomial (Fin 2) k ⧸ Ideal.span {q})
        (Ideal.span {q}).ResidueField (Ideal.Quotient.mk _ r) =
          algebraMap (MvPolynomial (Fin 2) k) (Ideal.span {q}).ResidueField r := fun r => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸ Ideal.span {q}) (Ideal.span {q}).ResidueField,
        Ideal.Quotient.algebraMap_eq]
    rw [h1, h1]
    exact div_mem (hkey a) (hkey b)
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hmindeg,
    hdeg]

/-- The residue field map of `Spec.map χ`, read on the residue fields of primes, extends `χ`. -/
private theorem residueFieldIso_square {R A : CommRingCat.{u}} (χ : R ⟶ A) (z : Spec A) :
    CommRingCat.ofHom (algebraMap R _) ≫
        (Scheme.Spec.residueFieldIso R ((Spec.map χ) z)).inv ≫
          (Spec.map χ).residueFieldMap z =
      χ ≫ CommRingCat.ofHom (algebraMap A _) ≫ (Scheme.Spec.residueFieldIso A z).inv := by
  rw [reassoc_of% (show _ = (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map χ) z) from
      Scheme.Spec.algebraMap_residueFieldIso_inv R _),
    show _ = (Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation z from
      Scheme.Spec.algebraMap_residueFieldIso_inv A z,
    Scheme.Γevaluation_naturality, Scheme.ΓSpecIso_inv_naturality_assoc]

/-- The residue degree of `Spec.map χ` at `z` is the degree of the extension of residue fields of
the primes `χ⁻¹ z ⊆ z`. -/
private theorem residueDegree_SpecMap {R A : CommRingCat.{u}} (χ : R ⟶ A) (z : PrimeSpectrum A) :
    letI := (Ideal.ResidueField.map (z.asIdeal.comap χ.hom) z.asIdeal χ.hom rfl).toAlgebra
    (Spec.map χ).residueDegree z =
      Module.finrank (z.asIdeal.comap χ.hom).ResidueField z.asIdeal.ResidueField := by
  let := (Ideal.ResidueField.map (z.asIdeal.comap χ.hom) z.asIdeal χ.hom rfl).toAlgebra
  let := ((Spec.map χ).residueFieldMap z).hom.toAlgebra
  let e₁ : (Spec R).residueField ((Spec.map χ) z) ≃+* (z.asIdeal.comap χ.hom).ResidueField :=
    (Scheme.Spec.residueFieldIso R ((Spec.map χ) z)).commRingCatIsoToRingEquiv
  let e₂ : (Spec A).residueField z ≃+* z.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso A z).commRingCatIsoToRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv e₁ e₂ ?_
  have hsq := residueFieldIso_square χ z
  have key : algebraMap (z.asIdeal.comap χ.hom).ResidueField z.asIdeal.ResidueField =
      (e₂.toRingHom.comp ((Spec.map χ).residueFieldMap z).hom).comp e₁.symm.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := R ⧸ (z.asIdeal.comap χ.hom)) fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : algebraMap (R ⧸ (z.asIdeal.comap χ.hom)) (z.asIdeal.comap χ.hom).ResidueField
        (Ideal.Quotient.mk _ r) = algebraMap R (z.asIdeal.comap χ.hom).ResidueField r := by
      rw [IsScalarTower.algebraMap_apply R (R ⧸ (z.asIdeal.comap χ.hom))
        (z.asIdeal.comap χ.hom).ResidueField, Ideal.Quotient.algebraMap_eq]
    rw [h1, RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap]
    have h2 := congr($hsq r)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, e₁, e₂]
    change _ = (Scheme.Spec.residueFieldIso A z).hom
      (((Spec.map χ).residueFieldMap z).hom
        ((Scheme.Spec.residueFieldIso R ((Spec.map χ) z)).inv
          (algebraMap R (z.asIdeal.comap χ.hom).ResidueField r)))
    have h2' : ((Spec.map χ).residueFieldMap z).hom
        ((Scheme.Spec.residueFieldIso R ((Spec.map χ) z)).inv
          (algebraMap R (z.asIdeal.comap χ.hom).ResidueField r)) =
        (Scheme.Spec.residueFieldIso A z).inv (algebraMap A z.asIdeal.ResidueField (χ r)) := h2
    rw [h2']
    simp
  ext t
  have h3 := congr($key (e₁ t))
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h3
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [h3]
  rfl

/-- The projection `𝔸² ⟶ 𝔸¹` to the second coordinate. -/
private noncomputable abbrev πT (k : Type u) [Field k] :
    Spec (.of (MvPolynomial (Fin 2) k)) ⟶ Spec (.of (MvPolynomial (Fin 1) k)) :=
  Spec.map (CommRingCat.ofHom (ιT k))

/-- A point of `𝔸²` of codimension one over the generic point of `𝔸¹`. -/
private def IsHor (y : PrimeSpectrum (MvPolynomial (Fin 2) k)) : Prop :=
  y.asIdeal.height = 1 ∧ y.asIdeal.comap (ιT k) = ⊥

/-- A principal prime of `k[X₀, X₁]` has height one. -/
private theorem height_span_prime {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    {q : S} (hq : Prime q) : (Ideal.span {q}).height = 1 := by
  have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span {q}) (Ideal.span {q}) ?_) ?_
  · rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rw [Ideal.span_singleton_eq_bot]; exact hq.ne_zero

/-- A height-one prime containing a prime element is generated by it. -/
private theorem eq_span_of_mem {y : PrimeSpectrum (MvPolynomial (Fin 2) k)}
    (hy : y.asIdeal.height = 1) {q : MvPolynomial (Fin 2) k} (hq : Prime q)
    (hqy : q ∈ y.asIdeal) : y.asIdeal = Ideal.span {q} := by
  have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  refine (lt_or_eq_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hqy)).elim (fun hlt => ?_)
    Eq.symm
  exfalso
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [height_span_prime hq, hy] at h1
  exact absurd h1 (by norm_num)

private theorem degreeOf_ιT (c : MvPolynomial (Fin 1) k) : (ιT k c).degreeOf 0 = 0 := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, finSuccEquiv_ιT, Polynomial.natDegree_C]

/-- The residue degree of `𝔸² ⟶ 𝔸¹` at a horizontal principal prime is the degree in `X₀`. -/
private theorem residueDegree_πT_span {q : MvPolynomial (Fin 2) k} (hq : Prime q)
    (hhor : (Ideal.span {q}).comap (ιT k) = ⊥) :
    (πT k).residueDegree (⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).mpr hq⟩ :
      PrimeSpectrum (MvPolynomial (Fin 2) k)) = q.degreeOf 0 := by
  have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  rw [residueDegree_SpecMap]
  exact finrank_residueField_eq_degreeOf hq rfl hhor

open Classical in
/-- **The degree as a sum over the horizontal primes.** For a nonzero `a ∈ k[X₀, X₁]`,
`deg_{X₀} a = ∑_y [κ(y) : k(X₁)] · ord_y a`, the sum over the horizontal points `y` of `𝔸²` of
codimension one. -/
private theorem degreeOf_eq_finsum {K : Type u} [Field K] [Algebra (MvPolynomial (Fin 2) k) K]
    [IsFractionRing (MvPolynomial (Fin 2) k) K] {a : MvPolynomial (Fin 2) k} (ha : a ≠ 0) :
    (Function.support fun y : PrimeSpectrum (MvPolynomial (Fin 2) k) =>
        if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K a) else 0).Finite ∧
      ∑ᶠ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
        (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K a) else 0) =
          a.degreeOf 0 := by
  classical
  revert ha
  refine UniqueFactorizationMonoid.induction_on_prime a (fun h => absurd rfl h) ?_ ?_
  · intro u hu _
    have h0 : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
        (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K u) else 0)
          = 0 := by
      intro y
      split_ifs with hy
      · rw [ordAt_algebraMap_eq_zero y hy.1 (fun h => y.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ h hu)), mul_zero]
      · rfl
    simp only [h0]
    refine ⟨by simp, ?_⟩
    rw [finsum_zero, ← MvPolynomial.natDegree_finSuccEquiv,
      Polynomial.natDegree_eq_zero_of_isUnit (hu.map _)]
    rfl
  · intro b p hb0 hp ih _
    obtain ⟨hfin, hsum⟩ := ih hb0
    have hpb : algebraMap (MvPolynomial (Fin 2) k) K (p * b) =
        algebraMap _ K p * algebraMap _ K b := map_mul _ _ _
    have hpK : algebraMap (MvPolynomial (Fin 2) k) K p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hp.ne_zero
    have hbK : algebraMap (MvPolynomial (Fin 2) k) K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hb0
    -- the contribution of `p`
    set yp : PrimeSpectrum (MvPolynomial (Fin 2) k) :=
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩ with hyp
    have hfp : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
        (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K p) else 0) =
          if y = yp then (if IsHor yp then (p.degreeOf 0 : ℤ) else 0) else 0 := by
      intro y
      by_cases hyy : y = yp
      · subst hyy
        rw [ite_eq_left rfl]
        split_ifs with hh
        · rw [ordAt_algebraMap_prime _ hh.1 hp rfl, mul_one,
            residueDegree_πT_span hp hh.2]
        · rfl
      · rw [ite_eq_right hyy]
        split_ifs with hh
        · have hpy : p ∉ y.asIdeal := fun hmem =>
            hyy (PrimeSpectrum.ext (eq_span_of_mem hh.1 hp hmem))
          rw [ordAt_algebraMap_eq_zero y hh.1 hpy, mul_zero]
        · rfl
    have hfinp : (Function.support fun y : PrimeSpectrum (MvPolynomial (Fin 2) k) =>
        if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K p) else 0).Finite :=
      (Set.finite_singleton yp).subset fun y hy => by
        rw [Function.mem_support, hfp] at hy
        by_contra h
        exact hy (ite_eq_right h)
    have hsplit : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
        (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K (p * b)) else 0)
          = (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K p) else 0) +
            (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap _ K b) else 0) := by
      intro y
      split_ifs
      · rw [hpb, ordAt_mul y hpK hbK, mul_add]
      · rw [add_zero]
    refine ⟨(hfinp.union hfin).subset fun y hy => ?_, ?_⟩
    · rw [Function.mem_support, hsplit] at hy
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hy (by rw [h.1, h.2, add_zero])
    · rw [finsum_congr hsplit, finsum_add_distrib hfinp hfin, hsum,
        MvPolynomial.degreeOf_mul_eq hp.ne_zero hb0, finsum_congr hfp,
        finsum_eq_single _ yp (fun y hy => ite_eq_right hy), ite_eq_left rfl]
      split_ifs with hh
      · push_cast; ring
      · have hp0 : p.degreeOf 0 = 0 := by
          have hcomap : (Ideal.span {p}).comap (ιT k) ≠ ⊥ := fun h =>
            hh ⟨height_span_prime hp, h⟩
          obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
          obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hc
          have hinj : Function.Injective (ιT k) :=
            MvPolynomial.rename_injective _ (Fin.succ_injective 1)
          have hιc : ιT k c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc0
          have hd0 : d ≠ 0 := by rintro rfl; rw [zero_mul] at hd; exact hιc hd.symm
          have := MvPolynomial.degreeOf_mul_eq (n := 0) hd0 hp.ne_zero
          rw [hd, degreeOf_ιT] at this
          omega
        rw [hp0]; push_cast; ring

end Degree

section Infinity

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra (MvPolynomial (Fin 2) k) K]
  [IsFractionRing (MvPolynomial (Fin 2) k) K]

variable (k K) in
/-- The embedding `k[X₀, X₁] → K`, `X₀ ↦ X₀⁻¹`, `X₁ ↦ X₁`, presenting `K` as the function field of
the chart of `ℙ¹ × 𝔸¹` at `X₀ = ∞`. -/
private noncomputable def θinf : MvPolynomial (Fin 2) k →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (Fin 2) k) K).comp MvPolynomial.C)
    ![(algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0))⁻¹,
      algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 1)]

omit [IsFractionRing (MvPolynomial (Fin 2) k) K] in
private theorem θinf_X0 : θinf k K (MvPolynomial.X 0) =
    (algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0))⁻¹ := by
  simp [θinf]

omit [IsFractionRing (MvPolynomial (Fin 2) k) K] in
private theorem θinf_ιT (c : MvPolynomial (Fin 1) k) :
    θinf k K (ιT k c) = algebraMap (MvPolynomial (Fin 2) k) K (ιT k c) := by
  induction c using MvPolynomial.induction_on with
  | C a => simp [θinf, ιT]
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    fin_cases i
    simp [θinf, ιT]

/-- A ring homomorphism out of `k[X₀, X₁]`, written through `k[X₁][X₀]`. -/
private theorem eq_eval₂_finSuccEquiv {S : Type*} [CommRing S]
    (φ : MvPolynomial (Fin 2) k →+* S) (r : MvPolynomial (Fin 2) k) :
    φ r = Polynomial.eval₂ (φ.comp (ιT k)) (φ (MvPolynomial.X 0))
      (MvPolynomial.finSuccEquiv k 1 r) := by
  induction r using MvPolynomial.induction_on with
  | C a =>
    have h : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.C a) =
        Polynomial.C (MvPolynomial.C a) := by
      rw [← finSuccEquiv_ιT]; simp [ιT]
    rw [h, Polynomial.eval₂_C]
    simp [ιT]
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', Polynomial.eval₂_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, Polynomial.eval₂_mul]
    congr 1
    fin_cases i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · have h : MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X 1) =
          Polynomial.C (MvPolynomial.X 0) := by
        rw [← finSuccEquiv_ιT]; simp [ιT]
      simp only [Fin.mk_one, Fin.isValue]
      rw [h, Polynomial.eval₂_C]
      simp [ιT]

/-- The reversal of `r` in `X₀` with respect to `d`. -/
private noncomputable def revX0 (d : ℕ) (r : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k :=
  (MvPolynomial.finSuccEquiv k 1).symm (Polynomial.reflect d (MvPolynomial.finSuccEquiv k 1 r))

private theorem algebraMap_X0_ne_zero :
    algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr (MvPolynomial.X_ne_zero 0)

/-- `θ (rev r) · X₀ ^ d = r` in `K`. -/
private theorem θinf_revX0_mul {d : ℕ} {r : MvPolynomial (Fin 2) k} (hd : r.degreeOf 0 ≤ d) :
    θinf k K (revX0 d r) * algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0) ^ d =
      algebraMap (MvPolynomial (Fin 2) k) K r := by
  set x := algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0)
  let : Invertible x := invertibleOfNonzero algebraMap_X0_ne_zero
  have hi : (θinf k K).comp (ιT k) = (algebraMap (MvPolynomial (Fin 2) k) K).comp (ιT k) :=
    RingHom.ext θinf_ιT
  rw [eq_eval₂_finSuccEquiv (θinf k K), eq_eval₂_finSuccEquiv
    (algebraMap (MvPolynomial (Fin 2) k) K) r, revX0, AlgEquiv.apply_symm_apply, hi, θinf_X0,
    ← invOf_eq_inv]
  exact Polynomial.eval₂_reflect_mul_pow _ _ d _ (by rwa [MvPolynomial.natDegree_finSuccEquiv])

/-- `rev r · θ(X₀) ^ d = θ r` in `K`. -/
private theorem algebraMap_revX0_mul {d : ℕ} {r : MvPolynomial (Fin 2) k} (hd : r.degreeOf 0 ≤ d) :
    algebraMap (MvPolynomial (Fin 2) k) K (revX0 d r) *
        (algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0))⁻¹ ^ d = θinf k K r := by
  set x := algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0)
  let : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero algebraMap_X0_ne_zero)
  have hi : (θinf k K).comp (ιT k) = (algebraMap (MvPolynomial (Fin 2) k) K).comp (ιT k) :=
    RingHom.ext θinf_ιT
  rw [eq_eval₂_finSuccEquiv (θinf k K) r, eq_eval₂_finSuccEquiv
    (algebraMap (MvPolynomial (Fin 2) k) K), revX0, AlgEquiv.apply_symm_apply, hi, θinf_X0]
  have h := Polynomial.eval₂_reflect_mul_pow ((algebraMap (MvPolynomial (Fin 2) k) K).comp (ιT k))
    x⁻¹ d (MvPolynomial.finSuccEquiv k 1 r) (by rwa [MvPolynomial.natDegree_finSuccEquiv])
  rwa [invOf_eq_inv, inv_inv] at h

private theorem revX0_ne_zero {d : ℕ} {r : MvPolynomial (Fin 2) k} (hr : r ≠ 0) :
    revX0 d r ≠ 0 := by
  rw [revX0, Ne, map_eq_zero_iff _ (MvPolynomial.finSuccEquiv k 1).symm.injective,
    Polynomial.reflect_eq_zero_iff, map_eq_zero_iff _ (MvPolynomial.finSuccEquiv k 1).injective]
  exact hr

private theorem θinf_injective : Function.Injective (θinf k K) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  have h := algebraMap_revX0_mul (K := K) (le_refl (r.degreeOf 0))
  rw [hr, mul_eq_zero, pow_eq_zero_iff', inv_eq_zero] at h
  rcases h with h | ⟨h, -⟩
  · exact revX0_ne_zero h0 ((map_eq_zero_iff _ (IsFractionRing.injective _ K)).mp h)
  · exact algebraMap_X0_ne_zero h

private theorem θinf_surj (z : K) : ∃ a s : MvPolynomial (Fin 2) k, s ≠ 0 ∧
    z * θinf k K s = θinf k K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 2) k) z
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  set x := algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0)
  have hx : x ≠ 0 := algebraMap_X0_ne_zero
  have ha := θinf_revX0_mul (K := K) (le_refl (a.degreeOf 0))
  have hsr := θinf_revX0_mul (K := K) (le_refl (s.degreeOf 0))
  refine ⟨revX0 (a.degreeOf 0) a * MvPolynomial.X 0 ^ s.degreeOf 0,
    revX0 (s.degreeOf 0) s * MvPolynomial.X 0 ^ a.degreeOf 0,
    mul_ne_zero (revX0_ne_zero hs0) (pow_ne_zero _ (MvPolynomial.X_ne_zero 0)), ?_⟩
  have hsK : algebraMap (MvPolynomial (Fin 2) k) K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hs0
  have hθs : θinf k K (revX0 (s.degreeOf 0) s) ≠ 0 := by
    intro h; rw [h, zero_mul] at hsr; exact hsK hsr.symm
  simp only [map_mul, map_pow, θinf_X0]
  rw [← ha, ← hsr]
  field_simp
  simp

/-- `K` is a fraction field of `k[X₀, X₁]` through `θinf`. -/
private theorem isFractionRing_θinf :
    @IsFractionRing (MvPolynomial (Fin 2) k) _ K _ (θinf k K).toAlgebra := by
  have hmap : ∀ r, @algebraMap (MvPolynomial (Fin 2) k) K _ _ (θinf k K).toAlgebra r =
      θinf k K r := fun _ => rfl
  refine (@isLocalization_iff _ _ _ _ _ (θinf k K).toAlgebra).mpr ⟨fun s => ?_, fun z => ?_,
    fun {x y} h => ⟨1, ?_⟩⟩
  · rw [hmap]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (θinf_injective (k := k) (K := K))).mpr
      (nonZeroDivisors.ne_zero s.2))
  · obtain ⟨a, s, hs, h⟩ := θinf_surj (k := k) (K := K) z
    exact ⟨⟨a, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, by rw [hmap, hmap]; exact h⟩
  · rw [hmap, hmap] at h
    rw [θinf_injective (k := k) (K := K) h]

private theorem prime_X0 : Prime (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) :=
  MvPolynomial.X_prime

variable (k) in
/-- The point `X₀ = 0` of the chart at infinity. -/
private noncomputable def yInf : PrimeSpectrum (MvPolynomial (Fin 2) k) :=
  ⟨Ideal.span {MvPolynomial.X 0},
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).mpr prime_X0⟩

omit [IsFractionRing (MvPolynomial (Fin 2) k) K] in
variable (k) in
/-- The point at infinity is horizontal. -/
private theorem comap_ιT_yInf : (yInf k).asIdeal.comap (ιT k) = ⊥ := by
  ext c
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hc
    have h := congrArg (fun p => (MvPolynomial.finSuccEquiv k 1 p).coeff 0) hd
    simp only [map_mul, MvPolynomial.finSuccEquiv_X_zero, Polynomial.coeff_mul_X_zero,
      finSuccEquiv_ιT, Polynomial.coeff_C_zero] at h
    exact h.symm
  · rintro rfl
    rw [map_zero]
    exact Ideal.zero_mem _

omit [IsFractionRing (MvPolynomial (Fin 2) k) K] in
variable (k) in
/-- The point at infinity has residue degree one over the generic point of `𝔸¹`. -/
private theorem residueDegree_πT_yInf : (πT k).residueDegree (yInf k) = 1 := by
  have h := residueDegree_πT_span (prime_X0 (k := k)) (comap_ιT_yInf k)
  rw [MvPolynomial.degreeOf_X, ite_eq_left rfl] at h
  exact h

private theorem ordAt_pow {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {L : Type u} [Field L] [Algebra R L] [IsFractionRing R L] (y : PrimeSpectrum R) {g : L}
    (hg : g ≠ 0) (n : ℕ) : ordAt y (g ^ n) = n * ordAt y g := by
  induction n with
  | zero => simp [ordAt_one]
  | succ n ih =>
    rw [pow_succ, ordAt_mul y (pow_ne_zero _ hg) hg, ih]
    push_cast; ring

private theorem revX0_notMem {r : MvPolynomial (Fin 2) k} (hr : r ≠ 0) :
    revX0 (r.degreeOf 0) r ∉ (yInf k).asIdeal := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have h1 := congrArg (fun p => (MvPolynomial.finSuccEquiv k 1 p).coeff 0) hc
  simp only [map_mul, MvPolynomial.finSuccEquiv_X_zero, Polynomial.coeff_mul_X_zero] at h1
  rw [revX0, AlgEquiv.apply_symm_apply, Polynomial.coeff_reflect, Polynomial.revAt_le
    (Nat.zero_le _), Nat.sub_zero, ← MvPolynomial.natDegree_finSuccEquiv] at h1
  have h2 : (MvPolynomial.finSuccEquiv k 1 r).leadingCoeff = 0 := h1.symm
  rw [Polynomial.leadingCoeff_eq_zero, map_eq_zero_iff _ (MvPolynomial.finSuccEquiv k 1).injective]
    at h2
  exact hr h2

/-- **The order at infinity is minus the degree.** -/
private theorem ordAt_inf_algebraMap {a : MvPolynomial (Fin 2) k} (ha : a ≠ 0) :
    @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf (yInf k)
      (algebraMap (MvPolynomial (Fin 2) k) K a) = -(a.degreeOf 0 : ℤ) := by
  rw [← θinf_revX0_mul (K := K) (le_refl (a.degreeOf 0))]
  have hx : algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0) =
      (θinf k K (MvPolynomial.X 0))⁻¹ := by rw [θinf_X0, inv_inv]
  rw [hx]
  have hθX : θinf k K (MvPolynomial.X 0) ≠ 0 :=
    (map_ne_zero_iff _ (θinf_injective (k := k) (K := K))).mpr (MvPolynomial.X_ne_zero 0)
  have hθr : θinf k K (revX0 (a.degreeOf 0) a) ≠ 0 :=
    (map_ne_zero_iff _ (θinf_injective (k := k) (K := K))).mpr (revX0_ne_zero ha)
  have hInf1 : (yInf k).asIdeal.height = 1 := height_span_prime prime_X0
  have h1 := @ordAt_mul (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
    isFractionRing_θinf (yInf k) _ _ hθr (pow_ne_zero (a.degreeOf 0) (inv_ne_zero hθX))
  have h2 := @ordAt_pow (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
    isFractionRing_θinf (yInf k) _ (inv_ne_zero hθX) (a.degreeOf 0)
  have h3 := @ordAt_inv (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
    isFractionRing_θinf (yInf k) _ hθX
  have h4 : @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
      (yInf k) (θinf k K (revX0 (a.degreeOf 0) a)) = 0 :=
    @ordAt_algebraMap_eq_zero (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
      isFractionRing_θinf (yInf k) hInf1 _ (revX0_notMem ha)
  have h5 : @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
      (yInf k) (θinf k K (MvPolynomial.X 0)) = 1 :=
    @ordAt_algebraMap_prime (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
      isFractionRing_θinf (yInf k) hInf1 _ prime_X0 rfl
  rw [h1, h2, h3, h4, h5]
  ring

open Classical in
/-- **The degree formula on `ℙ¹` over `k(X₁)`.** For `g ∈ K^×`, the weighted orders of `g` at the
horizontal points of `𝔸²` and its order at `X₀ = ∞` add up to zero. -/
private theorem finsum_add_ordAt_inf_eq_zero {g : K} (hg : g ≠ 0) :
    (Function.support fun y : PrimeSpectrum (MvPolynomial (Fin 2) k) =>
        if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y g else 0).Finite ∧
      ∑ᶠ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
        (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y g else 0) +
        @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
          (yInf k) g = 0 := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 2) k) g
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (MvPolynomial (Fin 2) k) K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hs0
  have haK : algebraMap (MvPolynomial (Fin 2) k) K a ≠ 0 := fun h => hg (by rw [h, zero_div])
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  obtain ⟨hfa, hsa⟩ := degreeOf_eq_finsum (K := K) ha0
  obtain ⟨hfs, hss⟩ := degreeOf_eq_finsum (K := K) hs0
  have hsplit : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
      (if IsHor y then ((πT k).residueDegree y : ℤ) *
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K a / algebraMap _ K s) else 0) =
      (if IsHor y then ((πT k).residueDegree y : ℤ) *
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K a) else 0) -
      (if IsHor y then ((πT k).residueDegree y : ℤ) *
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K s) else 0) := by
    intro y
    split_ifs
    · rw [ordAt_div y haK hsK, mul_sub]
    · rw [sub_zero]
  refine ⟨(hfa.union hfs).subset fun y hy => ?_, ?_⟩
  · rw [Function.mem_support, hsplit] at hy
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hy (by rw [h.1, h.2, sub_zero])
  · have hθa := ordAt_inf_algebraMap (K := K) ha0
    have hθs := ordAt_inf_algebraMap (K := K) hs0
    have hdiv : @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra
        isFractionRing_θinf (yInf k)
        (algebraMap (MvPolynomial (Fin 2) k) K a / algebraMap _ K s) =
        @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
          (yInf k) (algebraMap (MvPolynomial (Fin 2) k) K a) -
        @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
          (yInf k) (algebraMap (MvPolynomial (Fin 2) k) K s) :=
      @ordAt_div (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
        (yInf k) _ _ haK hsK
    rw [finsum_congr hsplit, finsum_sub_distrib hfa hfs, hsa, hss, hdiv, hθa, hθs]
    ring

end Infinity

section CurveDegree

/-- On an affine open `U` of an integral scheme, a section lies in the prime of a point exactly
when its germ lies in the maximal ideal of the local ring. -/
private theorem mem_primeIdealOf_iff {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      ∃ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        algebraMap (X.presheaf.stalk x) X.functionField t = X.germToFunctionField U s := by
  rw [mem_maximalIdeal_stalk_iff hU hx]
  constructor
  · intro hs
    exact ⟨s, 1, hs, fun h => (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr h), by rw [map_one, mul_one]⟩
  · rintro ⟨a, t, ha, ht, hat⟩
    have h1 : s * t = a := X.germToFunctionField_injective U (by rwa [map_mul])
    exact ((hU.primeIdealOf ⟨x, hx⟩).isPrime.mem_or_mem (h1 ▸ ha)).resolve_right ht

/-- The point of `Spec Γ(X, U)` of a point of `U` is its prime. -/
private theorem fromSpec_mem_and_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (z : Spec Γ(X, U)) :
    ∃ hz : hU.fromSpec z ∈ U, hU.primeIdealOf ⟨hU.fromSpec z, hz⟩ = z := by
  have hz : hU.fromSpec z ∈ U := by
    change hU.fromSpec z ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨z, rfl⟩
  exact ⟨hz, hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hz⟩)⟩

/-- The point `T = 0` of `𝔸¹ = Spec k[T]`, as the prime `(T)`. -/
private noncomputable def yZero (k : Type u) [Field k] : PrimeSpectrum (MvPolynomial (Fin 1) k) :=
  ⟨Ideal.span {MvPolynomial.X 0},
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).mpr MvPolynomial.X_prime⟩

/-- `(T)` is maximal in `k[T]`. -/
private theorem yZero_isMaximal (k : Type u) [Field k] : (yZero k).asIdeal.IsMaximal := by
  have hker : RingHom.ker (MvPolynomial.eval (fun _ => (0 : k)) :
      MvPolynomial (Fin 1) k →+* k) = (yZero k).asIdeal := by
    ext p
    rw [RingHom.mem_ker]
    constructor
    · intro hp
      change p ∈ Ideal.span {MvPolynomial.X 0}
      rw [show ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 1) k)) =
        MvPolynomial.X '' {0} from by simp, MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      refine ⟨0, rfl, fun h0 => ?_⟩
      have hm0 : m = 0 := Finsupp.ext fun i => by fin_cases i; exact h0
      subst hm0
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [← MvPolynomial.constantCoeff_eq, ← hp]
      simp [MvPolynomial.constantCoeff]
    · intro hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective _ fun c => ⟨MvPolynomial.C c, by simp⟩

/-- The point `T = 0` is a `k`-point of `𝔸¹`: the residue degree of `𝔸¹ ⟶ Spec k` there is one. -/
private theorem residueDegree_yZero (k : Type u) [Field k] :
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k)))).residueDegree
      (yZero k) = 1 := by
  set ev : MvPolynomial (Fin 1) k →+* k := MvPolynomial.eval (fun _ => (0 : k))
  have hsec : Spec.map (CommRingCat.ofHom ev) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    simp [ev]
  have hpt : (Spec.map (CommRingCat.ofHom ev)).base (default : PrimeSpectrum k) = yZero k := by
    apply PrimeSpectrum.ext
    have hbot : (default : PrimeSpectrum k).asIdeal = ⊥ :=
      Ideal.eq_bot_of_prime _
    change Ideal.comap ev (default : PrimeSpectrum k).asIdeal = Ideal.span {MvPolynomial.X 0}
    rw [hbot]
    ext p
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro hp
      rw [show ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 1) k)) =
        MvPolynomial.X '' {0} from by simp, MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      refine ⟨0, rfl, fun h0 => ?_⟩
      have hm0 : m = 0 := Finsupp.ext fun i => by fin_cases i; exact h0
      subst hm0
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [← MvPolynomial.constantCoeff_eq, ← hp]
      simp [ev, MvPolynomial.constantCoeff]
    · intro hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp [ev]
  have := (residueDegree_eq_one_of_section _ _ hsec (default : PrimeSpectrum k)).1
  rwa [hpt] at this

/-- On an affine open `V` of a scheme over `k`, the residue degree over `k` of a point of
`Spec Γ(X, V)` is that of the corresponding point of `X`. -/
private theorem residueDegree_SpecMap_algebraMap {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {V : X.Opens} (hV : IsAffineOpen V) [Algebra k Γ(X, V)]
    (hκ : ∀ c : k, algebraMap k Γ(X, V) c =
      sX.appLE ⊤ V (fun _ _ => trivial) ((Scheme.ΓSpecIso (.of k)).inv c))
    (z : Spec Γ(X, V)) :
    (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, V)))).residueDegree z =
      sX.residueDegree (hV.fromSpec z) := by
  have h1 : CommRingCat.ofHom (algebraMap k Γ(X, V)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V (fun _ _ => trivial) := by
    ext c; exact hκ c
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top (Spec (.of k))) hV
    (fun _ _ => trivial)
  rw [h1, Spec.map_comp, Stacks.Chow.residueDegree_comp_isOpenImmersion,
    ← Stacks.Chow.residueDegree_comp_isOpenImmersion _
      (isAffineOpen_top (Spec (.of k))).fromSpec, hsq,
    Stacks.Chow.residueDegree_isOpenImmersion_comp]

open Classical in
/-- **The degree of a coordinate on the curve.** Let `C` be a smooth proper curve over `k`, `D` a
divisor of degree `N` supported on closed points, `x₀, x₁` sections of `𝒪(D)` without common
zero, and `C₀` an affine open containing every point where `ξ = x₁ / x₀` is regular, with
`Γ(C, C₀)` finite over `k[T]` through `T ↦ ξ`. Then `Spec Γ(C, C₀) ⟶ 𝔸¹` has residue degree `N`
at the generic point, i.e. `[k(C) : k(ξ)] = N`. -/
private theorem residueDegree_genericPoint_chart_curve {k : Type u} [Field k] {C : Scheme.{u}}
    [IsLocallyNoetherian C] (f₀ : C ⟶ Spec (.of k)) [IsProper f₀]
    [IsCurve k f₀] [Smooth f₀]
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C)) (N : ℕ)
    (hD : ∑ᶠ Q : C, D Q * (f₀.residueDegree Q : ℤ) = N) (E : C → ℤ) (hE : ∀ z, E z = D z)
    {x₀ x₁ : C.functionField} (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0)
    (hx₀E : ∀ z, 0 ≤ C.ord x₀ z + E z) (hx₁E : ∀ z, 0 ≤ C.ord x₁ z + E z)
    (hG1 : ∀ z, coheight z = 1 → C.ord x₀ z + E z = 0 ∨ C.ord x₁ z + E z = 0)
    {C₀ : C.Opens} (hC₀ : IsAffineOpen C₀) [Nonempty C₀]
    (hchart : ∀ c : C,
      x₁ / x₀ ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₀)
    [IsDomain Γ(C, C₀)] [Algebra k Γ(C, C₀)] [Algebra.FiniteType k Γ(C, C₀)]
    (hκ : ∀ c : k, algebraMap k Γ(C, C₀) c =
      f₀.appLE ⊤ C₀ (fun _ _ => trivial) ((Scheme.ΓSpecIso (.of k)).inv c))
    [Algebra (MvPolynomial (Fin 1) k) Γ(C, C₀)]
    [IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, C₀)]
    [Module.Finite (MvPolynomial (Fin 1) k) Γ(C, C₀)]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin 1) k) Γ(C, C₀)))
    (hX : C.germToFunctionField C₀
      (algebraMap (MvPolynomial (Fin 1) k) Γ(C, C₀) (MvPolynomial.X 0)) = x₁ / x₀) :
    (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 1) k) Γ(C, C₀)))).residueDegree
      (genericPoint (Spec Γ(C, C₀))) = N := by
  classical
  have : IsNormal C := isNormal_of_smooth_over_field f₀
  set ξ := x₁ / x₀ with hξ
  have hξ0 : ξ ≠ 0 := div_ne_zero hx₁ hx₀
  -- the fraction field `K₁ = k(T)` acting on `k(C)`
  set R₁ := MvPolynomial (Fin 1) k
  let K₁ := FractionRing R₁
  have hinjL : Function.Injective
      ((C.germToFunctionField C₀).hom.comp (algebraMap R₁ Γ(C, C₀))) :=
    (C.germToFunctionField_injective C₀).comp hinj
  let : Algebra K₁ C.functionField :=
    (IsFractionRing.lift (A := R₁) (K := K₁) hinjL).toAlgebra
  have hKL : ∀ r, algebraMap K₁ C.functionField (algebraMap R₁ K₁ r) =
      C.germToFunctionField C₀ (algebraMap R₁ Γ(C, C₀) r) := fun r =>
    IsFractionRing.lift_algebraMap (A := R₁) (K := K₁) hinjL r
  have : IsFractionRing Γ(C, C₀) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C C₀ hC₀
  let : Algebra R₁ C.functionField :=
    ((algebraMap Γ(C, C₀) C.functionField).comp (algebraMap R₁ Γ(C, C₀))).toAlgebra
  have : IsScalarTower R₁ Γ(C, C₀) C.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ K₁ C.functionField := IsScalarTower.of_algebraMap_eq fun r =>
    (hKL r).symm
  have : Algebra.IsIntegral R₁ Γ(C, C₀) := Algebra.IsIntegral.of_finite R₁ Γ(C, C₀)
  have : FaithfulSMul R₁ Γ(C, C₀) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : FiniteDimensional K₁ C.functionField :=
    Module.Finite.of_isLocalization R₁ Γ(C, C₀) (Rₚ := K₁) (Sₚ := C.functionField)
      (nonZeroDivisors R₁)
  -- the norm formula at `T = 0`
  have hy₀ : (yZero k).asIdeal.height = 1 := height_span_prime MvPolynomial.X_prime
  have key := ordAt_norm_eq_finsum (k := k) hC₀ hinj hKL hξ0 (yZero k)
  -- its left side is `[k(C) : k(T)]`
  have hξK : ξ = algebraMap K₁ C.functionField (algebraMap R₁ K₁ (MvPolynomial.X 0)) := by
    rw [hKL, hX]
  have hX0 : algebraMap R₁ K₁ (MvPolynomial.X 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R₁ K₁)).mpr (MvPolynomial.X_ne_zero 0)
  have hLHS : ordAt (yZero k) (Algebra.norm K₁ ξ) = Module.finrank K₁ C.functionField := by
    rw [hξK, Algebra.norm_algebraMap, ordAt_pow _ hX0,
      ordAt_algebraMap_prime _ hy₀ MvPolynomial.X_prime rfl, mul_one]
  -- the right side is the degree of the divisor of zeros of `ξ`
  set τ := Spec.map (CommRingCat.ofHom (algebraMap R₁ Γ(C, C₀))) with hτ
  set S := τ.base ⁻¹' {(yZero k : Spec (.of R₁))} with hS
  set G : C → ℤ := fun c => if coheight c = 1 then
    (C.ord x₁ c + E c) * (f₀.residueDegree c : ℤ) else 0 with hG
  have hcoh₀ : coheight (show Spec (.of R₁) from yZero k) = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy₀
  -- the residue degree of `τ` over `T = 0` is the degree of the point over `k`
  have hrd : ∀ z ∈ S, τ.residueDegree z = f₀.residueDegree (hC₀.fromSpec z) := by
    intro z hz
    have h1 := residueDegree_comp τ
      (Spec.map (CommRingCat.ofHom (algebraMap k R₁))) z
    have h2 : τ ≫ Spec.map (CommRingCat.ofHom (algebraMap k R₁)) =
        Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, C₀))) := by
      rw [hτ, ← Spec.map_comp]
      congr 1
      ext c
      exact (IsScalarTower.algebraMap_apply k R₁ Γ(C, C₀) c).symm
    rw [h2, residueDegree_SpecMap_algebraMap f₀ hC₀ hκ, (Set.mem_singleton_iff.mp hz),
      residueDegree_yZero, one_mul] at h1
    exact h1.symm
  -- membership in the fibre over `T = 0`
  have hfib : ∀ (c : C) (hc : c ∈ C₀),
      (hC₀.primeIdealOf ⟨c, hc⟩ ∈ S ↔ ∃ t ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk c),
        algebraMap (C.presheaf.stalk c) C.functionField t = ξ) := by
    intro c hc
    rw [← hX, ← mem_primeIdealOf_iff hC₀ hc]
    constructor
    · intro hz
      have h1 : (τ.base (hC₀.primeIdealOf ⟨c, hc⟩)).asIdeal = (yZero k).asIdeal :=
        congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hz)
      have h2 : MvPolynomial.X 0 ∈ (τ.base (hC₀.primeIdealOf ⟨c, hc⟩)).asIdeal := by
        rw [h1]; exact Ideal.mem_span_singleton_self _
      exact h2
    · intro hmem
      refine Set.mem_singleton_iff.mpr (PrimeSpectrum.ext ?_)
      have hle : (yZero k).asIdeal ≤ (τ.base (hC₀.primeIdealOf ⟨c, hc⟩)).asIdeal := by
        change Ideal.span {MvPolynomial.X 0} ≤ _
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      exact ((yZero_isMaximal k).eq_of_le (τ.base _).isPrime.ne_top hle).symm
  -- orders of `ξ` through the orders of `x₀, x₁`
  have hordξ : ∀ c, C.ord ξ c = (C.ord x₁ c + E c) - (C.ord x₀ c + E c) := by
    intro c; rw [hξ, ord_div hx₁ hx₀]; ring
  -- (A1) the terms of the fibre sum
  have hA1 : ∀ z ∈ S, C.ord ξ (hC₀.fromSpec z) *
      (AlgebraicCycle.mapCoeff τ coheight coheight z : ℤ) = G (hC₀.fromSpec z) := by
    intro z hz
    obtain ⟨hzC, hzP⟩ := fromSpec_mem_and_primeIdealOf hC₀ z
    by_cases hc1 : coheight (hC₀.fromSpec z) = 1
    · have hz1 : coheight z = 1 := (coheight_eq_of_isOpenImmersion hC₀.fromSpec).symm.trans hc1
      have hmc : AlgebraicCycle.mapCoeff τ coheight coheight z = τ.residueDegree z := by
        rw [AlgebraicCycle.mapCoeff, ite_eq_left]
        rw [hz1, Set.mem_singleton_iff.mp hz]
        exact hcoh₀.symm
      have hpos : 0 < C.ord ξ (hC₀.fromSpec z) := by
        refine (ord_pos_iff hc1 hξ0).mpr ?_
        rw [← hfib _ hzC, hzP]
        exact hz
      have hD₀ := hx₀E (hC₀.fromSpec z)
      have hD₁ : C.ord x₀ (hC₀.fromSpec z) + E (hC₀.fromSpec z) = 0 := by
        rcases hG1 _ hc1 with h | h
        · exact h
        · rw [hordξ] at hpos; omega
      rw [hmc, hrd z hz, hordξ, hD₁, sub_zero, hG]
      simp only [ite_eq_left hc1]
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hc1, zero_mul, hG]
      simp only [ite_eq_right hc1]
  -- (A2) the zeros of `x₁` lie in the fibre
  have hA2 : Function.support G ⊆ hC₀.fromSpec.base '' S := by
    intro c hc
    rw [Function.mem_support, hG] at hc
    by_cases hc1 : coheight c = 1
    · simp only [ite_eq_left hc1] at hc
      have hD : 0 < C.ord x₁ c + E c := by
        rcases lt_or_eq_of_le (hx₁E c) with h | h
        · exact h
        · rw [← h, zero_mul] at hc; exact absurd rfl hc
      have hD₀ : C.ord x₀ c + E c = 0 := by
        rcases hG1 c hc1 with h | h
        · exact h
        · omega
      have hpos : 0 < C.ord ξ c := by rw [hordξ, hD₀]; omega
      have hcC : c ∈ C₀ := hchart c ((ord_nonneg_iff hc1 hξ0).mp hpos.le)
      refine ⟨hC₀.primeIdealOf ⟨c, hcC⟩, (hfib c hcC).mpr ((ord_pos_iff hc1 hξ0).mp hpos),
        hC₀.fromSpec_primeIdealOf ⟨c, hcC⟩⟩
    · simp only [ite_eq_right hc1] at hc
      exact absurd rfl hc
  have hRHS : (∑ᶠ z ∈ S, C.ord ξ (hC₀.fromSpec z) *
      (AlgebraicCycle.mapCoeff τ coheight coheight z : ℤ)) = ∑ᶠ c, G c := by
    rw [finsum_mem_congr rfl hA1]
    have himg := finsum_mem_image (f := G) (s := S) (g := fun z => hC₀.fromSpec.base z)
      (hC₀.fromSpec.isOpenEmbedding.injective.injOn)
    refine himg.symm.trans ?_
    conv_rhs => rw [← finsum_mem_univ G]
    exact finsum_mem_inter_support_eq G _ Set.univ (by
      rw [Set.univ_inter]; exact Set.inter_eq_right.mpr hA2)
  -- (B) the degree formula on `C`
  have hdvr : ∀ c : C, coheight c = 1 → IsDiscreteValuationRing (C.presheaf.stalk c) :=
    fun c hc => Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hc
  have hDF := Stacks.BombieriStepanov.hasDegreeFormula_curveVal hdvr k f₀
  set G₁ : C → ℤ := fun c => if coheight c = 1 then
    (f₀.residueDegree c : ℤ) * C.ord x₁ c else 0 with hG₁
  set G₂ : C → ℤ := fun c => if coheight c = 1 then E c * (f₀.residueDegree c : ℤ) else 0
    with hG₂
  have hGsplit : ∀ c, G c = G₁ c + G₂ c := by
    intro c
    simp only [hG, hG₁, hG₂]
    split_ifs <;> ring
  have hsub : ∀ F : C → ℤ, (∑ᶠ p : Stacks.BombieriStepanov.CurvePlace C, F p.1) =
      ∑ᶠ c, if coheight c = 1 then F c else 0 := by
    intro F
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun c => ?_
    rw [finsum_eq_if]
  have hG₁sum : ∑ᶠ c, G₁ c = 0 := by
    have h := hDF.sum_eq_zero x₁ hx₁
    simp only [Stacks.BombieriStepanov.ordZ_curveVal, Stacks.BombieriStepanov.curveDeg] at h
    rw [hsub (fun c => (f₀.residueDegree c : ℤ) * C.ord x₁ c)] at h
    exact h
  have hG₁fin : (Function.support G₁).Finite := by
    have h := hDF.finite_support x₁ hx₁
    refine (h.image Subtype.val).subset fun c hc => ?_
    rw [Function.mem_support, hG₁] at hc
    by_cases hc1 : coheight c = 1
    · simp only [ite_eq_left hc1] at hc
      refine ⟨⟨c, hc1⟩, ?_, rfl⟩
      rw [Function.mem_support, Stacks.BombieriStepanov.ordZ_curveVal]
      exact fun h0 => hc (by rw [h0, mul_zero])
    · simp only [ite_eq_right hc1] at hc; exact absurd rfl hc
  have hG₂eq : ∀ c, G₂ c = D c * (f₀.residueDegree c : ℤ) := by
    intro c
    simp only [hG₂, hE]
    by_cases hc : c ∈ D.support
    · rw [ite_eq_left (Stacks.Zeta.coheight_eq_one_of_isClosed f₀ (hDcl c hc))]
    · rw [Finsupp.notMem_support_iff.mp hc, zero_mul, ite_self]
  have hG₂fin : (Function.support G₂).Finite :=
    D.support.finite_toSet.subset fun c hc => by
      rw [Function.mem_support, hG₂eq] at hc
      exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hGsum : ∑ᶠ c, G c = N := by
    rw [finsum_congr hGsplit, finsum_add_distrib hG₁fin hG₂fin, hG₁sum, zero_add,
      finsum_congr hG₂eq, hD]
  have hfr : (Module.finrank K₁ C.functionField : ℤ) = N := by
    rw [← hLHS, key, hRHS, hGsum]
  rw [chartResidueDegree_genericPoint hC₀ hinj hKL]
  exact_mod_cast hfr

end CurveDegree

section Points

/-- The generic point of the image of a morphism out of an integral scheme is the image of the
generic point. -/
private theorem eq_of_isGenericPoint_range {X Y : Scheme.{u}} [IsIntegral Y] (s : Y ⟶ X)
    {e : X} (he : IsGenericPoint e (Set.range s.base)) : e = s.base (genericPoint Y) := by
  refine he.eq ?_
  apply le_antisymm
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) he.isClosed
  · rintro _ ⟨y, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((genericPoint_spec Y).specializes (Set.mem_univ y)).map s.base.hom.continuous)

/-- The image of the generic point of an irreducible scheme-theoretic fibre over a closed point
is a generic point of the set-theoretic fibre. -/
public theorem isGenericPoint_fiberι_genericPoint {X Y : Scheme.{u}} (g : X ⟶ Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IrreducibleSpace (g.fiber y)] :
    IsGenericPoint (g.fiberι y (genericPoint (g.fiber y))) (g.base ⁻¹' {y}) := by
  have hcl : IsClosed (g.base ⁻¹' {y}) := hy.preimage g.base.hom.continuous
  have h := (genericPoint_spec (g.fiber y)).image (g.fiberι y).base.hom.continuous
  rw [Set.image_univ] at h
  have hr : Set.range (g.fiberι y).base = g.base ⁻¹' {y} := Scheme.Hom.range_fiberι g y
  rwa [hr, hcl.closure_eq] at h

/-- **The fibre over a closed point.** Let `X = C ×_k C` with projections `pr₁, pr₂`, for `C`
integral and geometrically integral over `k`, and `c` a closed point of `C`. The fibre `pr₁⁻¹(c)`
has a generic point, and `pr₂` maps it to the generic point of `C`. -/
public theorem exists_isGenericPoint_preimage_singleton {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral C] (f : C ⟶ Spec (.of k)) [GeometricallyIntegral f] {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) {c : C} (hc : IsClosed ({c} : Set C)) :
    ∃ e : X, IsGenericPoint e (pr₁.base ⁻¹' {c}) ∧ pr₂.base e = genericPoint C := by
  have : GeometricallyIntegral pr₁ :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hX.flip inferInstance
  have he := isGenericPoint_fiberι_genericPoint pr₁ hc
  refine ⟨_, he, ?_⟩
  have hgen : IsGenericPoint (pr₂.base (pr₁.fiberι c (genericPoint (pr₁.fiber c)))) ⊤ := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨x, hx₁, hx₂⟩ :=
      Scheme.exists_preimage_of_isPullback hX c y (Subsingleton.elim _ _)
    rw [← hx₂]
    exact (he.specializes (show x ∈ pr₁.base ⁻¹' {c} from hx₁)).map pr₂.base.hom.continuous
  exact hgen.eq (genericPoint_spec C)

/-- In the setting of `Faltings.exists_isGenericPoint_preimage_singleton`, every generic point of
the fibre of `pr₁` over a closed point lies over the generic point of `C` under `pr₂`. -/
public theorem snd_eq_genericPoint_of_isGenericPoint_preimage_singleton {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ Spec (.of k)) [GeometricallyIntegral f]
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) {c : C} (hc : IsClosed ({c} : Set C))
    {e : X} (he : IsGenericPoint e (pr₁.base ⁻¹' {c})) : pr₂.base e = genericPoint C := by
  obtain ⟨e', he', h⟩ := exists_isGenericPoint_preimage_singleton f hX hc
  rw [he.eq he', h]

/-- **The residue degree at the generic point of a base change along fields.** In a cartesian
square `Y = C ×_S T` of integral schemes in which `T` and `S` are one-point integral affine
schemes, i.e. spectra of fields, the residue degree of `Y ⟶ C` at the generic point of `Y` is the
residue degree of `T ⟶ S`. -/
public theorem residueDegree_genericPoint_of_isPullback {Y C T S : Scheme.{u}} [IsIntegral Y]
    [IsIntegral C] [IsIntegral T] [Subsingleton T] [IsAffine T] [IsIntegral S] [Subsingleton S]
    [IsAffine S] {q : Y ⟶ C} {p : Y ⟶ T} {f : C ⟶ S} {g : T ⟶ S} (h : IsPullback q p f g)
    (t : T) : q.residueDegree (genericPoint Y) = g.residueDegree t := by
  have : Surjective g := ⟨fun _ => ⟨t, Subsingleton.elim _ _⟩⟩
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  -- an affine chart `U` of `C` and the chart `V = q⁻¹ U` of `Y` over it
  obtain ⟨U, hU, hηU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : C.Opens)) (x := genericPoint C) trivial
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hUS : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hTS : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ⊤ := fun _ _ => trivial
  set V : Y.Opens := q ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ with hVdef
  have hVU : V ≤ q ⁻¹ᵁ U := inf_le_left
  have hVT : V ≤ p ⁻¹ᵁ ⊤ := inf_le_right
  have hV : IsAffineOpen V :=
    isAffineOpen_of_isPullback h (isAffineOpen_top S) hU (isAffineOpen_top T) hUS hTS hVdef
  have hγ : genericPoint Y ∈ V :=
    ⟨show q.base (genericPoint Y) ∈ U by rw [map_genericPoint_of_isDominant]; exact hηU, trivial⟩
  have : Nonempty V := ⟨⟨_, hγ⟩⟩
  have hpush := isPushout_appLE_of_isPullback_inter h (isAffineOpen_top S) hU
    (isAffineOpen_top T) hUS hTS hVdef hVU hVT
  -- the sections over the chart are the base change of `Γ(T)` along `Γ(S) ⟶ Γ(C, U)`
  let : Algebra Γ(S, ⊤) Γ(C, U) := (f.appLE ⊤ U hUS).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := (g.appLE ⊤ ⊤ hTS).hom.toAlgebra
  let : Algebra Γ(C, U) Γ(Y, V) := (q.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(Y, V) := (p.appLE ⊤ V hVT).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Y, V) := (f.appLE ⊤ U hUS ≫ q.appLE U V hVU).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(C, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun x => ConcreteCategory.congr_hom hpush.w x
  have hAlg : Algebra.IsPushout Γ(S, ⊤) Γ(C, U) Γ(T, ⊤) Γ(Y, V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have hinj : Function.Injective (algebraMap Γ(S, ⊤) Γ(C, U)) := by
    let := (isField_of_isIntegral_of_subsingleton S).toField
    exact RingHom.injective _
  have : FaithfulSMul Γ(S, ⊤) Γ(C, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hAB : Module.finrank Γ(C, U) Γ(Y, V) = Module.finrank Γ(S, ⊤) Γ(T, ⊤) :=
    hAlg.out.finrank_eq
  -- the degree of the function fields is the rank of the chart
  let : Algebra C.functionField Y.functionField := (dominantFunctionFieldMap q).toAlgebra
  let : Algebra Γ(C, U) Y.functionField :=
    (q.appLE U V hVU ≫ Y.germToFunctionField V).hom.toAlgebra
  have : IsScalarTower Γ(C, U) Γ(Y, V) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(C, U) C.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (dominantFunctionFieldMap_germToFunctionField_of_mem q (genericPoint Y) U
        (hVU hγ) V hγ hVU a).symm
  have : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  have : IsFractionRing Γ(Y, V) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y V hV
  rw [← Stacks.Chow.finrank_functionField_eq_residueDegree q,
    IsFractionRing.finrank_eq Γ(C, U) C.functionField Γ(Y, V) Y.functionField, hAB]
  -- the global sections of the spectra of fields are their residue fields
  have : IsIso (S.Γevaluation (g.base t)) :=
    Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton _
  have : IsIso (T.Γevaluation t) := Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton _
  have happ : g.appLE ⊤ ⊤ hTS = g.appTop := g.appLE_eq_app (U := ⊤)
  let := (g.residueFieldMap t).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (asIso (S.Γevaluation (g.base t))).commRingCatIsoToRingEquiv
    (asIso (T.Γevaluation t)).commRingCatIsoToRingEquiv ?_
  ext x
  have hn := ConcreteCategory.congr_hom (Scheme.Γevaluation_naturality g t) x
  change (g.residueFieldMap t) (S.Γevaluation (g.base t) x) =
    T.Γevaluation t ((g.appLE ⊤ ⊤ hTS) x)
  rw [happ]
  exact hn

/-- **The residue degree of the fibre over a closed point.** In the setting of
`Faltings.exists_isGenericPoint_preimage_singleton`, at a generic point `e` of the fibre of
`pr₁` over a closed point `c`, the residue degree of `pr₂` is the residue degree of `c` over `k`:
`[κ(e) : k(C)] = [κ(c) : k]`. -/
public theorem residueDegree_snd_of_isGenericPoint_preimage_singleton {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] (f : C ⟶ Spec (.of k)) [GeometricallyIntegral f]
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) {c : C} (hc : IsClosed ({c} : Set C))
    {e : X} (he : IsGenericPoint e (pr₁.base ⁻¹' {c})) :
    pr₂.residueDegree e = f.residueDegree c := by
  have : GeometricallyIntegral pr₁ :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hX.flip inferInstance
  rw [he.eq (isGenericPoint_fiberι_genericPoint pr₁ hc)]
  have hsq : IsPullback (pr₁.fiberι c ≫ pr₂) (pr₁.fiberToSpecResidueField c) f
      (C.fromSpecResidueField c ≫ f) :=
    (IsPullback.of_hasPullback pr₁ (C.fromSpecResidueField c)).paste_horiz hX.flip
  have h1 := residueDegree_comp (pr₁.fiberι c) pr₂ (genericPoint (pr₁.fiber c))
  rw [Stacks.Chow.residueDegree_eq_one_of_isPreimmersion (pr₁.fiberι c), mul_one] at h1
  rw [← h1, residueDegree_genericPoint_of_isPullback hsq
    (pr₁.fiberToSpecResidueField c (genericPoint (pr₁.fiber c))), residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isPreimmersion (C.fromSpecResidueField c), mul_one,
    Scheme.fromSpecResidueField_apply]

/-- **Charts of `C × C` are integral over the plane.** Let `W = pr₁⁻¹ C₁ ∩ pr₂⁻¹ C₀` for affine
opens `C₁, C₀` of `C` on which every section is integral over `k[s₁]`, resp. `k[s₂]`. Then
`Γ(X, W)` is integral over `k[X₀, X₁]` through `X₀ ↦ pr₁^* s₁` and `X₁ ↦ pr₂^* s₂`. -/
private theorem chart_isIntegral {k : Type u} [Field k] {C X : Scheme.{u}} [IsIntegral C]
    [IsIntegral X] [Algebra k C.functionField] [Algebra k X.functionField]
    {f₀ : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f₀ f₀)
    {C₁ C₀ : C.Opens} (hC₁ : IsAffineOpen C₁) (hC₀ : IsAffineOpen C₀) [Nonempty C₁]
    [Nonempty C₀] {W : X.Opens} (hWdef : W = pr₁ ⁻¹ᵁ C₁ ⊓ pr₂ ⁻¹ᵁ C₀) [Nonempty W]
    (h₁ : W ≤ pr₁ ⁻¹ᵁ C₁) (h₂ : W ≤ pr₂ ⁻¹ᵁ C₀)
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ t, X.germToFunctionField W (pr₁.appLE C₁ W h₁ t) = ι₁ (C.germToFunctionField C₁ t))
    (hι₂ : ∀ t, X.germToFunctionField W (pr₂.appLE C₀ W h₂ t) = ι₂ (C.germToFunctionField C₀ t))
    (s₁ : Γ(C, C₁)) (s₂ : Γ(C, C₀))
    (hint₁ : ∀ t : Γ(C, C₁), C.germToFunctionField C₁ t ∈
      integralClosure (Algebra.adjoin k {C.germToFunctionField C₁ s₁}) C.functionField)
    (hint₂ : ∀ t : Γ(C, C₀), C.germToFunctionField C₀ t ∈
      integralClosure (Algebra.adjoin k {C.germToFunctionField C₀ s₂}) C.functionField)
    (κ : k →+* Γ(X, W))
    (hκ : ∀ c, X.germToFunctionField W (κ c) = algebraMap k X.functionField c) :
    (MvPolynomial.eval₂Hom κ ![pr₁.appLE C₁ W h₁ s₁, pr₂.appLE C₀ W h₂ s₂]).IsIntegral := by
  set ψ := MvPolynomial.eval₂Hom κ ![pr₁.appLE C₁ W h₁ s₁, pr₂.appLE C₀ W h₂ s₂] with hψ
  let : Algebra (MvPolynomial (Fin 2) k) Γ(X, W) := ψ.toAlgebra
  let : Algebra (MvPolynomial (Fin 2) k) X.functionField :=
    ((X.germToFunctionField W).hom.comp ψ).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hR : ∀ c : k, algebraMap k X.functionField c ∈
      Set.range (algebraMap (MvPolynomial (Fin 2) k) X.functionField) := fun c =>
    ⟨MvPolynomial.C c, by
      change X.germToFunctionField W (ψ (MvPolynomial.C c)) = _
      rw [hψ, MvPolynomial.eval₂Hom_C]
      exact hκ c⟩
  have hint : ∀ {V : C.Opens} [Nonempty V] (ι : C.functionField →ₐ[k] X.functionField) (s : Γ(C, V))
      (j : Fin 2), X.germToFunctionField W (ψ (MvPolynomial.X j)) = ι (C.germToFunctionField V s) →
      ∀ t : Γ(C, V) → Γ(X, W), (∀ u, X.germToFunctionField W (t u) =
        ι (C.germToFunctionField V u)) →
      (∀ u : Γ(C, V), C.germToFunctionField V u ∈
        integralClosure (Algebra.adjoin k {C.germToFunctionField V s}) C.functionField) →
      ∀ u, IsIntegral (MvPolynomial (Fin 2) k) (t u) := by
    intro V _ ι s j hj t ht hintV u
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField)
      (X.germToFunctionField_injective W)).mp ?_
    change IsIntegral _ (X.germToFunctionField W (t u))
    rw [ht]
    exact isIntegral_map_of_mem_integralClosure ι _ ⟨MvPolynomial.X j, hj⟩ hR (hintV u)
  intro y
  exact mem_of_isPushout (isPushout_appLE_of_isPullback_inter hX
    (isAffineOpen_top (Spec (.of k))) hC₁ hC₀ (fun _ _ => trivial) (fun _ _ => trivial) hWdef h₁ h₂)
    (integralClosure (MvPolynomial (Fin 2) k) Γ(X, W)).toSubring
    (hint ι₁ s₁ 0 (by
      rw [hψ, MvPolynomial.eval₂Hom_X']
      exact hι₁ s₁) _ hι₁ hint₁)
    (hint ι₂ s₂ 1 (by
      rw [hψ, MvPolynomial.eval₂Hom_X']
      exact hι₂ s₂) _ hι₂ hint₂) y

/-- The restriction maps of two morphisms with the same composite to `S` agree on sections pulled
back from `S`. -/
private theorem appLE_comp_eq {X C S : Scheme.{u}} (g₁ g₂ : X ⟶ C) (f₀ : C ⟶ S)
    (h : g₁ ≫ f₀ = g₂ ≫ f₀) {U : S.Opens} {C₀ : C.Opens} {W : X.Opens} (e₁ : C₀ ≤ f₀ ⁻¹ᵁ U)
    (e₂ : W ≤ g₂ ⁻¹ᵁ C₀) (e : W ≤ (g₁ ≫ f₀) ⁻¹ᵁ U) :
    (g₁ ≫ f₀).appLE U W e = f₀.appLE U C₀ e₁ ≫ g₂.appLE C₀ W e₂ := by
  rw [Scheme.Hom.appLE_comp_appLE]
  have : ∀ {g g' : X ⟶ S} (_ : g = g') (e e'), g.appLE U W e = g'.appLE U W e' := by
    rintro g g' rfl e e'; rfl
  exact this h _ _

/-- On a chart `V ⊆ pr₂⁻¹ C₀` whose second coordinate is pulled back from `C₀`, the composite to
the second coordinate axis factors through `Spec Γ(C, C₀)`. -/
private theorem chart_comp_πT {k : Type u} [Field k] {C X : Scheme.{u}} {pr₂ : X ⟶ C}
    {C₀ : C.Opens} {V : X.Opens} (hle : V ≤ pr₂ ⁻¹ᵁ C₀) (τ : MvPolynomial (Fin 1) k →+* Γ(C, C₀))
    (ψ : MvPolynomial (Fin 2) k →+* Γ(X, V))
    (hψ : ψ.comp (ιT k) = (pr₂.appLE C₀ V hle).hom.comp τ) :
    Spec.map (CommRingCat.ofHom ψ) ≫ πT k =
      Spec.map (pr₂.appLE C₀ V hle) ≫ Spec.map (CommRingCat.ofHom τ) := by
  rw [πT, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact hψ

/-- The point of `Spec Γ(C, C₀)` under a point `z` of a chart `V ⊆ pr₂⁻¹ C₀` is that of `pr₂ z`. -/
private theorem fromSpec_SpecMap_appLE_apply {C X : Scheme.{u}} {pr₂ : X ⟶ C}
    {C₀ : C.Opens} (hC₀ : IsAffineOpen C₀) {V : X.Opens} (hV : IsAffineOpen V)
    (hle : V ≤ pr₂ ⁻¹ᵁ C₀) (z : Spec Γ(X, V)) :
    hC₀.fromSpec (Spec.map (pr₂.appLE C₀ V hle) z) = pr₂ (hV.fromSpec z) := by
  rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec pr₂ hC₀ hV hle,
    Scheme.Hom.comp_apply]

/-- **The weight of a curve over the generic point.** Let `V ⊆ pr₂⁻¹ C₀` be an affine chart of
`X` over `Spec R₂` whose composite to `Spec R₁` is pulled back from `τ : R₁ → Γ(C, C₀)`, with
`τ` injective. At a point `z` of the chart lying over the generic point of `C`, at which `pr₂` has
residue degree `d`, the image of `z` in `Spec R₂` lies over the generic point of `Spec R₁`, and the
residue degrees of `Spec R₂ ⟶ Spec R₁` and of the chart multiply to `d` times the residue degree
of `τ` at the generic point. -/
public theorem chart_weight {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (ι : R₁ →+* R₂)
    {C X : Scheme.{u}} [IsIntegral C] {pr₂ : X ⟶ C} {C₀ : C.Opens} (hC₀ : IsAffineOpen C₀)
    [IsDomain Γ(C, C₀)] {V : X.Opens} (hV : IsAffineOpen V) (hle : V ≤ pr₂ ⁻¹ᵁ C₀)
    (τ : R₁ →+* Γ(C, C₀)) (hτ : Function.Injective τ) (ψ : R₂ →+* Γ(X, V))
    (hψ : ψ.comp ι = (pr₂.appLE C₀ V hle).hom.comp τ) (z : Spec Γ(X, V))
    (hz : pr₂ (hV.fromSpec z) = genericPoint C) (d : ℕ)
    (hd : pr₂.residueDegree (hV.fromSpec z) = d) :
    (Spec.map (CommRingCat.ofHom ι)).residueDegree (Spec.map (CommRingCat.ofHom ψ) z) *
        (Spec.map (CommRingCat.ofHom ψ)).residueDegree z =
      d * (Spec.map (CommRingCat.ofHom τ)).residueDegree (genericPoint (Spec Γ(C, C₀))) ∧
    (Spec.map (CommRingCat.ofHom ψ) z).asIdeal.comap ι = ⊥ := by
  have hsq : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (pr₂.appLE C₀ V hle) ≫ Spec.map (CommRingCat.ofHom τ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact hψ
  set z₁ := Spec.map (pr₂.appLE C₀ V hle) z with hz₁def
  have hz₁ : hC₀.fromSpec z₁ = genericPoint C := by
    rw [hz₁def, ← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec pr₂ hC₀ hV hle,
      Scheme.Hom.comp_apply, hz]
  have : Nonempty (Spec Γ(C, C₀)) := ⟨z₁⟩
  have hg : z₁ = genericPoint (Spec Γ(C, C₀)) := hC₀.fromSpec.isOpenEmbedding.injective
    (hz₁.trans (genericPoint_eq_of_isOpenImmersion hC₀.fromSpec).symm)
  have hrd₁ : (Spec.map (pr₂.appLE C₀ V hle)).residueDegree z = d := by
    have h2 := residueDegree_comp (Spec.map (pr₂.appLE C₀ V hle)) hC₀.fromSpec z
    rw [IsAffineOpen.SpecMap_appLE_fromSpec pr₂ hC₀ hV hle, residueDegree_comp,
      Stacks.Chow.residueDegree_eq_one_of_isOpenImmersion hC₀.fromSpec,
      Stacks.Chow.residueDegree_eq_one_of_isOpenImmersion hV.fromSpec, hd] at h2
    simpa using h2.symm
  constructor
  · have h1 := residueDegree_comp (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom ι)) z
    rw [hsq, residueDegree_comp, hrd₁, ← hz₁def, hg] at h1
    rw [← h1, mul_comm]
  · have h1 : (Spec.map (CommRingCat.ofHom ι)) (Spec.map (CommRingCat.ofHom ψ) z) =
        Spec.map (CommRingCat.ofHom τ) z₁ := by
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    rw [hg, genericPoint_eq_bot_of_affine] at h2
    refine h2.trans ?_
    change Ideal.comap τ ⊥ = ⊥
    exact Ideal.comap_bot_of_injective τ hτ

/-- **A curve over a closed point is vertical.** In the setting of `chart_weight`, with
`Γ(C, C₀)` integral over `k[T]`, a point `z` of the chart with `pr₂ z` not the generic point of
`C` maps to a point of `𝔸²` that is not horizontal. -/
private theorem chart_not_horizontal {k : Type u} [Field k] {C X : Scheme.{u}} [IsIntegral C]
    {pr₂ : X ⟶ C} {C₀ : C.Opens} (hC₀ : IsAffineOpen C₀) [IsDomain Γ(C, C₀)] {V : X.Opens}
    (hV : IsAffineOpen V) (hle : V ≤ pr₂ ⁻¹ᵁ C₀) (τ : MvPolynomial (Fin 1) k →+* Γ(C, C₀))
    (hτ : τ.IsIntegral) (ψ : MvPolynomial (Fin 2) k →+* Γ(X, V))
    (hψ : ψ.comp (ιT k) = (pr₂.appLE C₀ V hle).hom.comp τ) (z : Spec Γ(X, V))
    (hz : pr₂ (hV.fromSpec z) ≠ genericPoint C) :
    (Spec.map (CommRingCat.ofHom ψ) z).asIdeal.comap (ιT k) ≠ ⊥ := by
  have hsq := chart_comp_πT hle τ ψ hψ
  set z₁ := Spec.map (pr₂.appLE C₀ V hle) z with hz₁def
  have hz₁ : hC₀.fromSpec z₁ = pr₂ (hV.fromSpec z) := fromSpec_SpecMap_appLE_apply hC₀ hV hle z
  have h1 : (πT k) (Spec.map (CommRingCat.ofHom ψ) z) = Spec.map (CommRingCat.ofHom τ) z₁ := by
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
  intro hbot
  have h2 : Ideal.comap τ z₁.asIdeal = ⊥ := (congrArg PrimeSpectrum.asIdeal h1).symm.trans hbot
  let := τ.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin 1) k) Γ(C, C₀) := ⟨hτ⟩
  have h3 : z₁.asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot h2
  have : Nonempty (Spec Γ(C, C₀)) := ⟨z₁⟩
  have : IsDominant hC₀.fromSpec := isDominant_of_isOpenImmersion _
  have hg : z₁ = genericPoint (Spec Γ(C, C₀)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h3
  apply hz
  rw [← hz₁, hg, map_genericPoint_of_isDominant]

end Points

section FinsumPoints

variable {Z Y W : Type*}

open Classical in
/-- A sum over a set of a function supported at one point. -/
private theorem finsum_mem_ite_eq_single (S : Set Z) (z₀ : Z) (c : ℤ) :
    ∑ᶠ z ∈ S, (if z = z₀ then c else 0) = if z₀ ∈ S then c else 0 := by
  rw [finsum_eq_single _ z₀]
  · simp [finsum_eq_if]
  · intro z hz
    simp [hz]

open Classical in
/-- **Counting a point along the fibres.** Let `F y` be the fibres of a map `π : Z → Y` and
`j : Z → W` injective. The sum over `F y` of the weights `m z` at the points with `j z = j z₀` is
`m z₀` if `π z₀ = y` and `0` otherwise; summing against a weight `w` over the `y` satisfying `H`
gives `w (π z₀) * m z₀` when `H (π z₀)`. -/
private theorem finsum_fibre_ite_eq {π : Z → Y} {j : Z → W} (hj : Function.Injective j)
    (F : Y → Set Z) (hF : ∀ y z, z ∈ F y ↔ π z = y)
    (H : Y → Prop) (w : Y → ℤ) (m : Z → ℤ) (z₀ : Z) :
    (∀ y, ∑ᶠ z ∈ F y, (if j z = j z₀ then m z else 0) = if π z₀ = y then m z₀ else 0) ∧
    ∑ᶠ y, (if H y then w y * ∑ᶠ z ∈ F y, (if j z = j z₀ then m z else 0) else 0) =
      if H (π z₀) then w (π z₀) * m z₀ else 0 := by
  have h1 : ∀ y, ∑ᶠ z ∈ F y, (if j z = j z₀ then m z else 0) =
      if π z₀ = y then m z₀ else 0 := by
    intro y
    have : ∀ z, (if j z = j z₀ then m z else 0) = if z = z₀ then m z₀ else 0 := fun z => by
      by_cases h : z = z₀
      · subst h; simp
      · rw [ite_eq_right (hj.ne h), ite_eq_right h]
    rw [finsum_mem_congr rfl fun z _ => this z, finsum_mem_ite_eq_single]
    simp only [hF y z₀]
  refine ⟨h1, ?_⟩
  simp_rw [h1]
  rw [finsum_eq_single _ (π z₀)]
  · simp
  · intro y hy
    simp [Ne.symm hy]

open Classical in
/-- The sum over the fibres of the weights at the points over a point outside the image of `j`
vanishes. -/
private theorem finsum_fibre_ite_eq_zero {j : Z → W} {e : W} (he : ∀ z, j z ≠ e)
    (F : Y → Set Z) (H : Y → Prop) (w : Y → ℤ) (m : Z → ℤ) :
    (∀ y, ∑ᶠ z ∈ F y, (if j z = e then m z else 0) = 0) ∧
    ∑ᶠ y, (if H y then w y * ∑ᶠ z ∈ F y, (if j z = e then m z else 0) else 0) = 0 := by
  have h1 : ∀ y, ∑ᶠ z ∈ F y, (if j z = e then m z else 0) = 0 := fun y => by
    simp [he]
  refine ⟨h1, ?_⟩
  simp only [h1, mul_zero, ite_self, finsum_zero]

end FinsumPoints

/-- A pointwise identity `g₁ = g₂ + (c T₁ + c T₂ - T₃)` between functions of finite support
sums to the same identity between their sums. -/
private theorem finsum_eq_add_of_forall_eq_add {Y : Type*} (g₁ g₂ T₁ T₂ T₃ : Y → ℤ) (c : ℤ)
    (h₂ : (Function.support g₂).Finite) (h₃ : (Function.support T₁).Finite)
    (h₄ : (Function.support T₂).Finite) (h₅ : (Function.support T₃).Finite)
    (h : ∀ y, g₁ y = g₂ y + (c * T₁ y + c * T₂ y - T₃ y)) :
    ∑ᶠ y, g₁ y = ∑ᶠ y, g₂ y + (c * ∑ᶠ y, T₁ y + c * ∑ᶠ y, T₂ y - ∑ᶠ y, T₃ y) := by
  classical
  set S := (h₂.union (h₃.union (h₄.union h₅))).toFinset with hS
  have hsub : ∀ g : Y → ℤ, (∀ y, y ∉ S → g y = 0) → Function.support g ⊆ S :=
    fun g hg y hy => by
      by_contra hn
      exact hy (hg y hn)
  have h0 : ∀ y, y ∉ S → g₂ y = 0 ∧ T₁ y = 0 ∧ T₂ y = 0 ∧ T₃ y = 0 := fun y hy => by
    rw [hS, Set.Finite.mem_toFinset] at hy
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hy
    exact hy
  rw [finsum_eq_sum_of_support_subset g₁ (hsub g₁ fun y hy => by
      obtain ⟨e₂, e₃, e₄, e₅⟩ := h0 y hy
      rw [h y, e₂, e₃, e₄, e₅]
      ring),
    finsum_eq_sum_of_support_subset g₂ (hsub g₂ fun y hy => (h0 y hy).1),
    finsum_eq_sum_of_support_subset T₁ (hsub T₁ fun y hy => (h0 y hy).2.1),
    finsum_eq_sum_of_support_subset T₂ (hsub T₂ fun y hy => (h0 y hy).2.2.1),
    finsum_eq_sum_of_support_subset T₃ (hsub T₃ fun y hy => (h0 y hy).2.2.2),
    Finset.sum_congr rfl fun y _ => h y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

open Classical in
/-- A sum over a finite set of points of `B · m`, for `B` the combination
`s Σ_c a c [e₁ c] + s Σ_c a c [e₂ c] - [eΔ]` of indicators, is the same combination of the sums of
`m` over the points at `e₁ c`, `e₂ c` and `eΔ`. -/
private theorem sum_mul_eq_of_forall_mul_eq {Z X Y : Type*} (S : Finset Z) (j : Z → X)
    (m : Z → ℤ) (B : X → ℤ) (s : ℤ) (T : Finset Y) (a : Y → ℤ) (e₁ e₂ : Y → X) (eΔ : X)
    (hBm : ∀ (w : X) (r : ℤ), B w * r = s * ∑ c ∈ T, a c * (if w = e₁ c then r else 0) +
      s * ∑ c ∈ T, a c * (if w = e₂ c then r else 0) - (if w = eΔ then r else 0)) :
    ∑ z ∈ S, B (j z) * m z = s * ∑ c ∈ T, a c * ∑ z ∈ S, (if j z = e₁ c then m z else 0) +
      s * ∑ c ∈ T, a c * ∑ z ∈ S, (if j z = e₂ c then m z else 0) -
      ∑ z ∈ S, (if j z = eΔ then m z else 0) := by
  simp only [hBm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := S), Finset.sum_comm (s := S)]
  simp only [← Finset.mul_sum]

open Classical in
/-- **The fibres of `C × C` over a divisor.** Let `X = C ×_k C` and `P₁` a divisor on `C`
supported on closed points, and let
`B = (s + 1) Σ_c P₁(c) (c × C) + (s + 1) Σ_c P₁(c) (C × c) - Δ`, the fibres `c × C = pr₁⁻¹ c` and
`C × c = pr₂⁻¹ c` entering through their generic points. There are points `e₁ c`, `e₂ c`, the
generic points of `pr₁⁻¹ c` and of `pr₂⁻¹ c` for `c` in the support of `P₁`, lying over `(c, η)`
and `(η, c)`, with `[κ(e₁ c) : k(C)] = [κ(c) : k]` along `pr₂`; `B` is the combination of their
indicators and of that of `Δ`, and takes the values `(s + 1) P₁(c)` at `e₁ c` and `-1` at `Δ`. -/
private theorem exists_fibrePoints {k : Type u} [Field k] {C X : Scheme.{u}}
    (f₀ : C ⟶ Spec (.of k)) [GeometricallyIntegral f₀] [IsCurve k f₀] {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f₀ f₀) (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C)) {eΔ : X}
    (heΔ : IsGenericPoint eΔ (Set.range Δ.base)) (s : ℕ) (B : X → ℤ)
    (hB : ∀ w, B w =
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0)) :
    ∃ e₁ e₂ : C → X, (∀ c ∈ P₁.support, c ≠ genericPoint C ∧ pr₁ (e₁ c) = c ∧
      pr₂ (e₁ c) = genericPoint C ∧ pr₂.residueDegree (e₁ c) = f₀.residueDegree c ∧
      pr₁ (e₂ c) = genericPoint C ∧ pr₂ (e₂ c) = c ∧ B (e₁ c) = (s + 1) * P₁ c) ∧
      pr₁ eΔ = genericPoint C ∧ pr₂ eΔ = genericPoint C ∧ B eΔ = -1 ∧
      ∀ (w : X) (r : ℤ), B w * r =
        (s + 1) * ∑ c ∈ P₁.support, P₁ c * (if w = e₁ c then r else 0) +
        (s + 1) * ∑ c ∈ P₁.support, P₁ c * (if w = e₂ c then r else 0) -
        (if w = eΔ then r else 0) := by
  have hex₁ : ∀ c : C, ∃ e : X, c ∈ P₁.support →
      IsGenericPoint e (pr₁.base ⁻¹' {c}) ∧ pr₂ e = genericPoint C := fun c => by
    by_cases hc : c ∈ P₁.support
    · obtain ⟨e, he, he'⟩ := exists_isGenericPoint_preimage_singleton f₀ hX (hP₁cl c hc)
      exact ⟨e, fun _ => ⟨he, he'⟩⟩
    · exact ⟨Δ c, fun h => absurd h hc⟩
  have hex₂ : ∀ c : C, ∃ e : X, c ∈ P₁.support →
      IsGenericPoint e (pr₂.base ⁻¹' {c}) ∧ pr₁ e = genericPoint C := fun c => by
    by_cases hc : c ∈ P₁.support
    · obtain ⟨e, he, he'⟩ := exists_isGenericPoint_preimage_singleton f₀ hX.flip (hP₁cl c hc)
      exact ⟨e, fun _ => ⟨he, he'⟩⟩
    · exact ⟨Δ c, fun h => absurd h hc⟩
  choose e₁ he₁ using hex₁
  choose e₂ he₂ using hex₂
  have hne : ∀ c ∈ P₁.support, c ≠ genericPoint C := fun c hc =>
    Stacks.Zeta.ne_genericPoint_of_isClosed f₀ (hP₁cl c hc)
  have hpr₁e₁ : ∀ c ∈ P₁.support, pr₁ (e₁ c) = c := fun c hc =>
    Set.mem_singleton_iff.mp (he₁ c hc).1.mem
  have hpr₂e₂ : ∀ c ∈ P₁.support, pr₂ (e₂ c) = c := fun c hc =>
    Set.mem_singleton_iff.mp (he₂ c hc).1.mem
  have heΔeq : eΔ = Δ (genericPoint C) := eq_of_isGenericPoint_range Δ heΔ
  have hpr₁eΔ : pr₁ eΔ = genericPoint C := by
    rw [heΔeq, ← Scheme.Hom.comp_apply, hΔ₁]; rfl
  have hpr₂eΔ : pr₂ eΔ = genericPoint C := by
    rw [heΔeq, ← Scheme.Hom.comp_apply, hΔ₂]; rfl
  have hgen₁ : ∀ w, ∀ c ∈ P₁.support, IsGenericPoint w (pr₁.base ⁻¹' {c}) ↔ w = e₁ c :=
    fun w c hc => ⟨fun h => h.eq (he₁ c hc).1, fun h => h ▸ (he₁ c hc).1⟩
  have hgen₂ : ∀ w, ∀ c ∈ P₁.support, IsGenericPoint w (pr₂.base ⁻¹' {c}) ↔ w = e₂ c :=
    fun w c hc => ⟨fun h => h.eq (he₂ c hc).1, fun h => h ▸ (he₂ c hc).1⟩
  have hBm : ∀ (w : X) (r : ℤ), B w * r =
      (s + 1) * ∑ c ∈ P₁.support, P₁ c * (if w = e₁ c then r else 0) +
      (s + 1) * ∑ c ∈ P₁.support, P₁ c * (if w = e₂ c then r else 0) -
      (if w = eΔ then r else 0) := by
    intro w r
    have h₁ : ∑ c ∈ P₁.support, (if IsGenericPoint w (pr₁.base ⁻¹' {c}) then P₁ c else 0) * r =
        ∑ c ∈ P₁.support, P₁ c * (if w = e₁ c then r else 0) :=
      Finset.sum_congr rfl fun c hc => by
        simp only [hgen₁ w c hc]
        split_ifs <;> ring
    have h₂ : ∑ c ∈ P₁.support, (if IsGenericPoint w (pr₂.base ⁻¹' {c}) then P₁ c else 0) * r =
        ∑ c ∈ P₁.support, P₁ c * (if w = e₂ c then r else 0) :=
      Finset.sum_congr rfl fun c hc => by
        simp only [hgen₂ w c hc]
        split_ifs <;> ring
    rw [hB, Finsupp.sum, Finsupp.sum, sub_mul, add_mul, mul_assoc, mul_assoc, Finset.sum_mul,
      Finset.sum_mul, h₁, h₂]
    split_ifs <;> ring
  have hne₁₁ : ∀ c ∈ P₁.support, ∀ c' ∈ P₁.support, c' ≠ c → e₁ c ≠ e₁ c' :=
    fun c hc c' hc' h h' => h (by rw [← hpr₁e₁ c hc, h', hpr₁e₁ c' hc'])
  have hne₁₂ : ∀ c ∈ P₁.support, ∀ c' ∈ P₁.support, e₁ c ≠ e₂ c' :=
    fun c hc c' hc' h => hne c hc (by rw [← hpr₁e₁ c hc, h, (he₂ c' hc').2])
  have hne₁Δ : ∀ c ∈ P₁.support, e₁ c ≠ eΔ :=
    fun c hc h => hne c hc (by rw [← hpr₁e₁ c hc, h, hpr₁eΔ])
  have hne₂Δ : ∀ c ∈ P₁.support, e₂ c ≠ eΔ :=
    fun c hc h => hne c hc (by rw [← hpr₂e₂ c hc, h, hpr₂eΔ])
  refine ⟨e₁, e₂, fun c hc => ⟨hne c hc, hpr₁e₁ c hc, (he₁ c hc).2,
    residueDegree_snd_of_isGenericPoint_preimage_singleton f₀ hX (hP₁cl c hc) (he₁ c hc).1,
    (he₂ c hc).2, hpr₂e₂ c hc, ?_⟩, hpr₁eΔ, hpr₂eΔ, ?_, hBm⟩
  · have h := hBm (e₁ c) 1
    rw [mul_one, Finset.sum_eq_single c (fun c' hc' h' => by
        rw [ite_eq_right (hne₁₁ c hc c' hc' h'), mul_zero]) (fun h' => absurd hc h'),
      Finset.sum_eq_zero (fun c' hc' => by rw [ite_eq_right (hne₁₂ c hc c' hc'), mul_zero]),
      ite_eq_left (rfl : e₁ c = e₁ c), ite_eq_right (hne₁Δ c hc)] at h
    rw [h]; ring
  · have h := hBm eΔ 1
    rw [mul_one,
      Finset.sum_eq_zero (fun c' hc' => by rw [ite_eq_right (hne₁Δ c' hc').symm, mul_zero]),
      Finset.sum_eq_zero (fun c' hc' => by rw [ite_eq_right (hne₂Δ c' hc').symm, mul_zero]),
      ite_eq_left (rfl : eΔ = eΔ)] at h
    rw [h]; ring

/-- A point at which a divisor `B` does not vanish, while the sections `f j` of `𝒪(B)` and a
separation condition between the zeros of `f i` and of `f 0` hold, has codimension one: at a point
of codimension `≠ 1` every order vanishes, so `B < 0` contradicts `div (f i) + B ≥ 0`, and
`B > 0` makes the point a common zero of `f i` and `f 0`. -/
private theorem coheight_eq_one_of_ne_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (B : X → ℤ) {m : ℕ} (f : Fin (m + 1) → X.functionField)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w) (i : Fin (m + 1))
    (hG : ∀ w, 0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w + B w → False) {w : X}
    (hw : B w ≠ 0) : Order.coheight w = 1 := by
  by_contra h
  have hord : ∀ j, X.ord (f j) w = 0 := fun j => Scheme.ord_eq_zero_of_coheight_neq_one h _
  have h0 := hD i w
  rw [hord] at h0
  exact hG w (by rw [hord]; omega) (by rw [hord]; omega)

/-- Over a field `k`, the sections over an affine open of a scheme locally of finite type over `k`
form a `k`-algebra of finite type. -/
private theorem finiteType_appLE_comp_ΓSpecIso_inv {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] {V : X.Opens} (hV : IsAffineOpen V) :
    ((g.appLE ⊤ V fun _ _ => trivial).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType := by
  have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ fun y => ⟨(Scheme.ΓSpecIso (.of k)).hom y, by simp⟩
  exact (g.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hV fun _ _ => trivial).comp h2

/-- The numerator of a reduced representation of the norm of a nonzero element is nonzero. -/
private theorem IsReducedNormRepresentation.num_ne_zero {R K L : Type*} [CommRing R] [Field K]
    [Field L] [Algebra R K] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    {η : Fin (m + 1) → L} {U V : Fin (m + 1) → R}
    (hU : IsReducedNormRepresentation (K := K) R η U V) {i : Fin (m + 1)} (hη : η i ≠ 0) :
    U i ≠ 0 := by
  intro h0
  have h1 := hU.algebraNorm_eq_div i
  rw [h0, map_zero, zero_div] at h1
  exact hη (Algebra.norm_eq_zero_iff.mp h1)

open Classical in
/-- **Summing the fibre contributions.** If `g₁ = g₂ + (s Σ_c a c T(e₁ c) + s Σ_c a c T(e₂ c) -
T(eΔ))` pointwise, for functions of finite support, and the sums of `T` along `e₁ c`, `e₂ c`,
`eΔ` are `v c`, `0`, `N`, then `Σ g₁ = Σ g₂ + (s Σ_c a c v c - N)`. -/
private theorem finsum_eq_add_of_forall_eq_add_sum {Y Z X : Type*} (g₁ g₂ : Y → ℤ)
    (T : X → Y → ℤ) (s : ℤ) (S : Finset Z) (a v : Z → ℤ) (e₁ e₂ : Z → X) (eΔ : X) (N : ℤ)
    (h₂ : (Function.support g₂).Finite) (hT : ∀ e, (Function.support (T e)).Finite)
    (h : ∀ y, g₁ y = g₂ y + (s * ∑ c ∈ S, a c * T (e₁ c) y + s * ∑ c ∈ S, a c * T (e₂ c) y -
      T eΔ y))
    (hv₁ : ∀ c ∈ S, ∑ᶠ y, T (e₁ c) y = v c) (hv₂ : ∀ c ∈ S, ∑ᶠ y, T (e₂ c) y = 0)
    (hΔ : ∑ᶠ y, T eΔ y = N) :
    ∑ᶠ y, g₁ y = ∑ᶠ y, g₂ y + (s * ∑ c ∈ S, a c * v c - N) := by
  have hfin : ∀ e : Z → X, (Function.support fun y => ∑ c ∈ S, a c * T (e c) y).Finite :=
    fun e => (S.finite_toSet.biUnion fun c _ => hT (e c)).subset fun y hy => by
      obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      exact Set.mem_biUnion hc (right_ne_zero_of_mul hne)
  have hsum : ∀ e : Z → X, ∑ᶠ y, ∑ c ∈ S, a c * T (e c) y = ∑ c ∈ S, a c * ∑ᶠ y, T (e c) y :=
    fun e => by
      rw [finsum_sum_comm _ _ fun c _ => (hT (e c)).subset fun y hy => right_ne_zero_of_mul hy]
      exact Finset.sum_congr rfl fun c _ => (mul_finsum _ _).symm
  have hs₁ : ∑ c ∈ S, a c * ∑ᶠ y, T (e₁ c) y = ∑ c ∈ S, a c * v c :=
    Finset.sum_congr rfl fun c hc => by rw [hv₁ c hc]
  have hs₂ : ∑ c ∈ S, a c * ∑ᶠ y, T (e₂ c) y = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hv₂ c hc, mul_zero]
  rw [finsum_eq_add_of_forall_eq_add g₁ g₂ _ _ (T eΔ) s h₂ (hfin e₁) (hfin e₂) (hT eΔ) h,
    hsum, hsum, hs₁, hs₂, hΔ]
  ring

open Classical in
/-- **The order of a reduced numerator on a finite chart.** Let `W` be an affine open of a normal
integral scheme `X`, finite over `R = k[X₀, X₁]`, and `K` a fraction field of `R` with `k(X) / K`
finite. Let `Norm (f i / f 0) = U i / V i` in lowest terms, where `div (f j) + B ≥ 0`, and assume
that a zero of `f i` and a zero of `f 0` are separated by a function of `K`. Then along a prime
divisor `y` of `Spec R` the order of `U i` is the push-forward of `div (f i) + B`. -/
private theorem ordAt_num_eq_finsum_chart {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {W : X.Opens} (hW : IsAffineOpen W) [Nonempty W]
    [IsDomain Γ(X, W)] [Algebra k Γ(X, W)] [Algebra.FiniteType k Γ(X, W)]
    [Algebra (MvPolynomial (Fin 2) k) Γ(X, W)] [IsScalarTower k (MvPolynomial (Fin 2) k) Γ(X, W)]
    [Module.Finite (MvPolynomial (Fin 2) k) Γ(X, W)]
    (hRB_inj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)))
    {K : Type u} [Field K] [Algebra (MvPolynomial (Fin 2) k) K]
    [IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [FiniteDimensional K X.functionField]
    (hKLW : ∀ r, algebraMap K X.functionField (algebraMap (MvPolynomial (Fin 2) k) K r) =
      X.germToFunctionField W (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r))
    {m : ℕ} (f : Fin (m + 1) → X.functionField) (hf : ∀ i, f i ≠ 0) (B : X → ℤ)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w) {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => f i / f 0) U V)
    (i : Fin (m + 1))
    (hG1 : ∀ w w', 0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w' + B w' →
      ∃ κ' : K, 0 ≤ X.ord (algebraMap K X.functionField κ') w ∧
        X.ord (algebraMap K X.functionField κ') w' < 0)
    (y : PrimeSpectrum (MvPolynomial (Fin 2) k)) (hy : y.asIdeal.height = 1) :
    ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) =
      ∑ᶠ z ∈ (Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)))).base ⁻¹' {y},
        (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff (Spec.map (CommRingCat.ofHom
            (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)))) coheight coheight z : ℤ) := by
  set πW : Spec Γ(X, W) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W))) with hπWdef
  have : IsFinite πW :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨F, hF⟩ : ∃ F : PrimeSpectrum (MvPolynomial (Fin 2) k) → Set (Spec Γ(X, W)),
      ∀ y, F y = πW.base ⁻¹' {y} := ⟨_, fun _ => rfl⟩
  have hmemF : ∀ y z, z ∈ F y ↔ πW z = y := fun y z => by rw [hF]; rfl
  have hfibW : ∀ y, (F y).Finite := fun y => by rw [hF]; exact πW.finite_preimage_singleton y
  have hcohSpec : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      Order.coheight (show Spec (.of (MvPolynomial (Fin 2) k)) from y) = 1 := fun y hy => by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy
  -- a point of a fibre of nonzero weight is a prime divisor
  have hmcW : ∀ (y : PrimeSpectrum (MvPolynomial (Fin 2) k)) (x : Spec Γ(X, W)),
      y.asIdeal.height = 1 → πW x = y →
      AlgebraicCycle.mapCoeff πW coheight coheight x ≠ 0 → coheight (hW.fromSpec x) = 1 := by
    intro y x hy hxy hmc
    rw [AlgebraicCycle.mapCoeff] at hmc
    split_ifs at hmc with hc
    · rw [coheight_eq_of_isOpenImmersion, hc, hxy]; exact hcohSpec y hy
    · exact absurd rfl hmc
  -- the norm of `η = f i / f 0`
  have hηne : f i / f 0 ≠ 0 := div_ne_zero (hf i) (hf 0)
  have hNη := hU.algebraNorm_eq_div i
  have hVne : algebraMap (MvPolynomial (Fin 2) k) K (V i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr (hU.ne_zero i)
  have hUne0 : U i ≠ 0 := hU.num_ne_zero hηne
  have hUne : algebraMap (MvPolynomial (Fin 2) k) K (U i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hUne0
  -- (G1): `Dᵢ` and `D₀` have no common component over a prime divisor of `𝔸²`
  have hG1W : ∀ x x' : Spec Γ(X, W), πW x = πW x' → (πW x).asIdeal.height = 1 →
      AlgebraicCycle.mapCoeff πW coheight coheight x ≠ 0 →
      AlgebraicCycle.mapCoeff πW coheight coheight x' ≠ 0 →
      0 < X.ord (f i) (hW.fromSpec x) + B (hW.fromSpec x) →
      0 < X.ord (f 0) (hW.fromSpec x') + B (hW.fromSpec x') → False := by
    intro x x' hxx' hy1 hmc hmc' hDi hD0
    have hw1 := hmcW _ x hy1 rfl hmc
    have hw'1 := hmcW _ x' hy1 hxx'.symm hmc'
    obtain ⟨hwW, hwP⟩ := fromSpec_mem_and_primeIdealOf hW x
    obtain ⟨hw'W, hw'P⟩ := fromSpec_mem_and_primeIdealOf hW x'
    have hy0 : (πW x).asIdeal ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hy1
    have := (πW x).isPrime
    obtain ⟨g, hgy, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy0
    obtain ⟨π, hπ, -, hπy⟩ := exists_prime_dvd_mem hg0 hgy
    have hyπ : (πW x).asIdeal = Ideal.span {π} := eq_span_of_mem hy1 hπ hπy
    have hzπ : x.asIdeal.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) =
        Ideal.span {π} := hyπ
    have hz'π : x'.asIdeal.comap (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) =
        Ideal.span {π} := by rw [← hyπ, hxx']; rfl
    obtain ⟨κ', hr1, hr2⟩ := hG1 _ _ hDi hD0
    have hr0 : algebraMap K X.functionField κ' ≠ 0 := by
      intro h0
      rw [h0] at hr2
      simp at hr2
    rcases exists_mul_eq_or_inv (K := K) hπ κ' with ⟨a₁, s₁, hs₁, h₁⟩ | ⟨a₁, s₁, ha₁, hs₁, h₁⟩
    · have hs₁P' : algebraMap _ Γ(X, W) s₁ ∉ (hW.primeIdealOf ⟨_, hw'W⟩).asIdeal := by
        rw [hw'P]
        intro h
        exact hs₁ (by rw [← hz'π]; exact h)
      have hmem : algebraMap K X.functionField κ' ∈
          Set.range (algebraMap (X.presheaf.stalk (hW.fromSpec x')) X.functionField) := by
        refine (mem_range_stalk_iff hW hw'W _).mpr ⟨algebraMap _ Γ(X, W) a₁,
          algebraMap _ Γ(X, W) s₁, hs₁P', ?_⟩
        have h₂ := congrArg (algebraMap K X.functionField) h₁
        rwa [map_mul, hKLW, hKLW] at h₂
      have := (ord_nonneg_iff hw'1 hr0).mpr hmem
      omega
    · have hs₁P : algebraMap _ Γ(X, W) s₁ ∉ (hW.primeIdealOf ⟨_, hwW⟩).asIdeal := by
        rw [hwP]
        intro h
        exact hs₁ (by rw [← hzπ]; exact h)
      have ha₁P : algebraMap _ Γ(X, W) a₁ ∈ (hW.primeIdealOf ⟨_, hwW⟩).asIdeal := by
        rw [hwP]
        rwa [← hzπ] at ha₁
      have hmem : ∃ t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (hW.fromSpec x)),
          algebraMap (X.presheaf.stalk (hW.fromSpec x)) X.functionField t =
            (algebraMap K X.functionField κ')⁻¹ := by
        refine (mem_maximalIdeal_stalk_iff hW hwW _).mpr ⟨algebraMap _ Γ(X, W) a₁,
          algebraMap _ Γ(X, W) s₁, ha₁P, hs₁P, ?_⟩
        have h₂ := congrArg (algebraMap K X.functionField) h₁
        rwa [map_mul, map_inv₀, hKLW, hKLW] at h₂
      have hpos := (ord_pos_iff hw1 (inv_ne_zero hr0)).mpr hmem
      rw [Stacks.Chow.ord_inv_functionField hr0] at hpos
      omega
  -- the order of `U i` along a prime divisor of `𝔸²` is the push-forward of `Dᵢ`
  have hperY : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) =
        ∑ᶠ z ∈ F y, (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) := by
    intro y hy
    have hS := hfibW y
    have hη : ordAt y (Algebra.norm K (f i / f 0)) =
        ∑ᶠ z ∈ F y, X.ord (f i / f 0) (hW.fromSpec z) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) := by
      rw [hF]; exact ordAt_norm_eq_finsum (k := k) hW hRB_inj hKLW hηne y
    rw [hNη, ordAt_div y hUne hVne] at hη
    have hsplit : ∀ z ∈ F y, X.ord (f i / f 0) (hW.fromSpec z) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) =
        (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) -
        (X.ord (f 0) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) := by
      intro z _
      rw [ord_div (hf i) (hf 0)]
      ring
    have key : ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) -
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (V i)) =
        (∑ᶠ z ∈ F y, (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ)) -
        ∑ᶠ z ∈ F y, (X.ord (f 0) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) :=
      hη.trans ((finsum_mem_congr rfl hsplit).trans (finsum_mem_sub_distrib _ _ hS))
    have hA0 : 0 ≤ ∑ᶠ z ∈ F y, (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) :=
      finsum_nonneg fun z => finsum_nonneg fun _ =>
        mul_nonneg (hD i _) (Nat.cast_nonneg _)
    have hB0 : 0 ≤ ∑ᶠ z ∈ F y, (X.ord (f 0) (hW.fromSpec z) + B (hW.fromSpec z)) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) :=
      finsum_nonneg fun z => finsum_nonneg fun _ =>
        mul_nonneg (hD 0 _) (Nat.cast_nonneg _)
    have hAB : (∑ᶠ z ∈ F y, (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ)) = 0 ∨
        (∑ᶠ z ∈ F y, (X.ord (f 0) (hW.fromSpec z) + B (hW.fromSpec z)) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ)) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hzS, hz⟩ := exists_ne_zero_of_finsum_mem_ne_zero hcon.1
      obtain ⟨z', hz'S, hz'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hcon.2
      have hzy : πW z = y := (hmemF y z).mp hzS
      have hz'y : πW z' = y := (hmemF y z').mp hz'S
      have hmc : AlgebraicCycle.mapCoeff πW coheight coheight z ≠ 0 := fun h =>
        hz (by rw [h, Nat.cast_zero, mul_zero])
      have hmc' : AlgebraicCycle.mapCoeff πW coheight coheight z' ≠ 0 := fun h =>
        hz' (by rw [h, Nat.cast_zero, mul_zero])
      have hDi : 0 < X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z) :=
        lt_of_le_of_ne (hD i _) fun h => hz (by rw [← h, zero_mul])
      have hD0 : 0 < X.ord (f 0) (hW.fromSpec z') + B (hW.fromSpec z') :=
        lt_of_le_of_ne (hD 0 _) fun h => hz' (by rw [← h, zero_mul])
      exact hG1W z z' (hzy.trans hz'y.symm) (by rw [hzy]; exact hy) hmc hmc' hDi hD0
    have hUV : ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) = 0 ∨
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (V i)) = 0 := by
      by_cases hUy : U i ∈ y.asIdeal
      · right
        refine ordAt_algebraMap_eq_zero y hy fun hVy => ?_
        have hy0 : y.asIdeal ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hy
        obtain ⟨g, hgy, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy0
        obtain ⟨π, hπ, -, hπy⟩ := exists_prime_dvd_mem hg0 hgy
        have hyπ : y.asIdeal = Ideal.span {π} := eq_span_of_mem hy hπ hπy
        rw [hyπ, Ideal.mem_span_singleton] at hUy hVy
        exact hπ.not_isUnit (hU.isRelPrime i hUy hVy)
      · left
        exact ordAt_algebraMap_eq_zero y hy hUy
    have hU0 := (ordAt_algebraMap_nonneg_and_pos (K := K) y hy hUne0).1
    have hV0 := (ordAt_algebraMap_nonneg_and_pos (K := K) y hy (hU.ne_zero i)).1
    omega
  rw [← hF]
  exact hperY y hy

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **The horizontal part of the degree of `U i`**, read on the chart `W = pr₁⁻¹ C₀ ∩ pr₂⁻¹ C₀`
over `𝔸²`. The extension `k(X) / K` is finite, and the weighted orders of `U i` at the horizontal
prime divisors of `𝔸²` are those of `Norm (f i)` plus the push-forward of the divisor `B` along
the fibres `c × C`, `C × c` and `Δ`: the push-forward of `Δ` has degree `N`, that of `c × C` has
degree `[κ(c) : k] N` when `c` lies in `C₀` and vanishes otherwise, and that of `C × c`
vanishes. -/
private theorem exists_finsum_horizontal_eq_of_isReducedNormRepresentation
    {k : Type u} [Field k] {C X : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsLocallyNoetherian C] [GeometricallyIntegral (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsCurve k (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial
        ((C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of k)) (C ↘ Spec (.of k)))
    [IsIntegral X] [IsLocallyNoetherian X] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * ((C ↘ Spec (.of k)).residueDegree Q : ℤ) = 1)
    {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (ι₁ ι₂ : C.functionField →+* X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the divisor `N P₁` on `C`, and the generic basis `x` of `H⁰(C, 𝒪(N P₁))` giving `φ_{NP₁}`
    (N : ℕ) {n : ℕ} (E : C → ℤ) (hE : ∀ z, E z = ((N : ℤ) • P₁) z)
    (x : Fin (n + 1) → C.functionField) (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z)
    (hxli : LinearIndependent k x)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = C ↘ Spec (.of k))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- (N): the basis `x` is generic
    (hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    -- the very ample divisor `B` on `X`, and the basis `f` of `H⁰(X, 𝒪(B))` giving `φ_B`
    (s : ℕ)
    (B : X → ℤ) (hB : ∀ w, B w =
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (f : Fin (m + 1) → X.functionField) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hBG1 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w',
      0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    {K : Type u} [Field K] [instRK : Algebra (MvPolynomial (Fin 2) k) K]
    [instFrac : IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [instRL : Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [instTower : IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => f i / f 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    FiniteDimensional K X.functionField ∧
      (∑ᶠ y : PrimeSpectrum (MvPolynomial (Fin 2) k), if IsHor y then
        ((πT k).residueDegree y : ℤ) * ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i))
        else 0) =
      (∑ᶠ y : PrimeSpectrum (MvPolynomial (Fin 2) k), if IsHor y then
        ((πT k).residueDegree y : ℤ) * ordAt y (Algebra.norm K (f i)) else 0) +
      ((s + 1) * ∑ c ∈ P₁.support, P₁ c *
          (if c ∈ φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X 0)) then
            ((C ↘ Spec (.of k)).residueDegree c : ℤ) * N else 0) - N) := by
  classical
  set f₀ := C ↘ Spec (.of k) with hf₀
  have : IsNormal C := isNormal_of_smooth_over_field f₀
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hX.flip inferInstance
  have : Smooth pr₂ := MorphismProperty.of_isPullback (P := @Smooth) hX inferInstance
  have : LocallyOfFiniteType pr₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX.flip inferInstance
  have : IsNormal X := isNormal_of_smooth_over_field (pr₁ ≫ f₀)
  have hx0 : ∀ j, x j ≠ 0 := hxli.ne_zero
  -- the chart `C₀ = φ⁻¹ D₊(T₀)` of `C`, containing the generic point
  obtain ⟨hη₀, hξ₀⟩ := BombieriRoth.exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  set C₀ : C.Opens := φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)) with hC₀def
  have hφNP_ne : (C₀ : Set C).Nonempty := ⟨_, hη₀⟩
  have hC₀ne : Nonempty C₀ := ⟨⟨_, hη₀⟩⟩
  have hC₀ : IsAffineOpen C₀ :=
    (ProjectiveSpace.isAffineOpen_standardOpen n (Spec (.of k)) 0).preimage φNP
  have hchart : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ c : C,
      x a' / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₀ :=
    fun a' ha' c hc => mem_preimage_basicOpen_of_mem_range f₀ E x hx0 hxE φNP hφNPx
      (hNG1 a' ha') hc
  have hint : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ s : Γ(C, C₀), C.germToFunctionField C₀ s ∈
      integralClosure (Algebra.adjoin k {x a' / x 0}) C.functionField :=
    fun a' ha' => germToFunctionField_mem_integralClosure f₀ hkC _ C₀ (hchart a' ha')
  -- the sections `ξ_j = x j / x 0` over `C₀`
  set sec : Fin (n + 1) → Γ(C, C₀) := fun j => φNP.app _
    ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
          (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X _ j)))) with hsecdef
  have hsec : ∀ j, C.germToFunctionField C₀ (sec j) = x j / x 0 := fun j => hξ₀ j
  -- the affine open `W = π_{ab}⁻¹(𝔸²)` of `X` and its ring of sections `Γ(X, W)`
  set W : X.Opens := pr₁ ⁻¹ᵁ C₀ ⊓ pr₂ ⁻¹ᵁ C₀ with hWdef
  have hC₀top : C₀ ≤ f₀ ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  have hW : IsAffineOpen W :=
    isAffineOpen_of_isPullback hX (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top hC₀top hWdef
  have hWne : Nonempty W := by
    obtain ⟨c, hc⟩ := hφNP_ne
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := f₀) c c rfl
    refine ⟨⟨hX.isoPullback.inv z, ?_, ?_⟩⟩
    · change pr₁ (hX.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_fst, hz1]
      exact hc
    · change pr₂ (hX.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_snd, hz2]
      exact hc
  have : Nonempty (pr₁ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.1⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.2⟩⟩
  have : IsDomain Γ(X, W) := IsIntegral.component_integral W
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : IsIntegrallyClosed Γ(X, W) :=
    (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨W, hW⟩ inferInstance
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  have hBL : ∀ b : Γ(X, W), algebraMap Γ(X, W) X.functionField b = X.germToFunctionField W b :=
    fun _ => rfl
  have : Nonempty (⊤ : X.Opens) := ⟨⟨hWne.some.1, trivial⟩⟩
  -- germs of restricted sections
  have hgermLE : ∀ {V : X.Opens} [Nonempty V] (h : W ≤ V) (t : Γ(X, V)),
      X.germToFunctionField W (X.presheaf.map (homOfLE h).op t) = X.germToFunctionField V t :=
    fun h t => X.presheaf.germ_res_apply (homOfLE h) _ _ t
  -- the constants
  set κ : k →+* Γ(X, W) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (pr₁ ≫ f₀).appLE ⊤ W (fun _ _ => trivial)).hom with hκdef
  have hκ : ∀ c, algebraMap Γ(X, W) X.functionField (κ c) = algebraMap k X.functionField c := by
    intro c
    rw [hkX c, hBL]
    exact hgermLE le_top _
  -- the generators `ξ_a`, `ξ'_b` of `Γ(X, W)` over `k`
  have hpr₁ : ∀ s : Γ(C, C₀),
      algebraMap Γ(X, W) X.functionField (pr₁.appLE C₀ W inf_le_left s) =
        ι₁ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₁ C₀ s, hBL]
    exact hgermLE inf_le_left _
  have hpr₂ : ∀ s : Γ(C, C₀),
      algebraMap Γ(X, W) X.functionField (pr₂.appLE C₀ W inf_le_right s) =
        ι₂ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₂ C₀ s, hBL]
    exact hgermLE inf_le_right _
  set ta := pr₁.appLE C₀ W inf_le_left (sec a)
  set tb := pr₂.appLE C₀ W inf_le_right (sec b)
  let : Algebra (MvPolynomial (Fin 2) k) Γ(X, W) := (MvPolynomial.eval₂Hom κ ![ta, tb]).toAlgebra
  have hRBa : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 0) = ta :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBb : algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 1) = tb :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBc : ∀ c, algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.C c) = κ c :=
    fun c => MvPolynomial.eval₂Hom_C _ _ _
  have hRBL : algebraMap (MvPolynomial (Fin 2) k) X.functionField =
      (algebraMap Γ(X, W) X.functionField).comp (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
        algebraMap Γ(X, W) X.functionField
          (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.C c))
      rw [hRBc, hRL₀, hκ]
    · fin_cases j
      · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
          algebraMap Γ(X, W) X.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 0))
        rw [hRBa, hRLa, hpr₁, hsec]
      · change algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
          algebraMap Γ(X, W) X.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) (MvPolynomial.X 1))
        rw [hRBb, hRLb, hpr₂, hsec]
  have : IsScalarTower (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [hRBL]; rfl
  have hRL_inj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k) X.functionField) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 2) k) K X.functionField]
    exact (algebraMap K X.functionField).injective.comp
      (IsFractionRing.injective (MvPolynomial (Fin 2) k) K)
  have hRB_inj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) := by
    intro r r' h
    apply hRL_inj
    rw [hRBL, RingHom.comp_apply, RingHom.comp_apply, h]
  have : FaithfulSMul (MvPolynomial (Fin 2) k) Γ(X, W) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin 2) k) Γ(X, W)).mpr hRB_inj
  -- `ι₁`, `ι₂` are `k`-linear
  have : Nonempty (⊤ : C.Opens) := ⟨⟨pr₁ hWne.some.1, trivial⟩⟩
  have : Nonempty (pr₁ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hWne.some.1, trivial⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hWne.some.1, trivial⟩⟩
  have hι₁k : ∀ c, ι₁ (algebraMap k C.functionField c) = algebraMap k X.functionField c := by
    intro c
    rw [hkC c, hkX c]
    exact (hι₁ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  have hι₂k : ∀ c, ι₂ (algebraMap k C.functionField c) = algebraMap k X.functionField c := by
    intro c
    rw [hkC c, hkX c, hX.w]
    exact (hι₂ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  let ι₁' : C.functionField →ₐ[k] X.functionField := { ι₁ with commutes' := hι₁k }
  let ι₂' : C.functionField →ₐ[k] X.functionField := { ι₂ with commutes' := hι₂k }
  -- `Γ(X, W)` is integral over `(MvPolynomial (Fin 2) k)`
  have hintOf : ∀ (ι' : C.functionField →ₐ[k] X.functionField) (a' : Fin (n + 1)), a' ≠ 0 →
      ∀ j : Fin 2, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X j) =
        ι' (x a' / x 0) → ∀ t : Γ(C, C₀) → Γ(X, W),
      (∀ s, algebraMap Γ(X, W) X.functionField (t s) = ι' (C.germToFunctionField C₀ s)) →
      ∀ s, IsIntegral (MvPolynomial (Fin 2) k) (t s) := by
    intro ι' a' ha' j hj t ht s
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 2) k) Γ(X, W) X.functionField)
      (IsFractionRing.injective Γ(X, W) X.functionField)).mp ?_
    change IsIntegral _ (algebraMap Γ(X, W) X.functionField (t s))
    rw [ht]
    exact isIntegral_map_of_mem_integralClosure ι' _ ⟨_, hj⟩ (fun c => ⟨_, hRL₀ c⟩)
      (hint a' ha' s)
  have : Algebra.IsIntegral (MvPolynomial (Fin 2) k) Γ(X, W) := ⟨fun y => mem_of_isPushout
    (isPushout_appLE_of_isPullback_inter hX (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top
      hC₀top hWdef inf_le_left inf_le_right)
    (integralClosure (MvPolynomial (Fin 2) k) Γ(X, W)).toSubring
    (hintOf ι₁' a ha 0 hRLa _ hpr₁) (hintOf ι₂' b hb 1 hRLb _ hpr₂) y⟩
  -- `Γ(X, W)` is finite over `(MvPolynomial (Fin 2) k)`, so `X.functionField` is finite over `K`
  let : Algebra k Γ(X, W) := κ.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin 2) k) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun c => (hRBc c).symm
  have : Algebra.FiniteType k Γ(X, W) := finiteType_appLE_comp_ΓSpecIso_inv (pr₁ ≫ f₀) hW
  have : Algebra.FiniteType (MvPolynomial (Fin 2) k) Γ(X, W) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 2) k) Γ(X, W)
  have : Module.Finite (MvPolynomial (Fin 2) k) Γ(X, W) := Algebra.IsIntegral.finite
  have : FiniteDimensional K X.functionField :=
    Module.Finite.of_isLocalization (MvPolynomial (Fin 2) k) Γ(X, W) (Rₚ := K)
      (Sₚ := X.functionField) (nonZeroDivisors (MvPolynomial (Fin 2) k))
  -- the curve side: `Γ(C, C₀)` over `k[T]` through `T ↦ ξ_b`
  set κC : k →+* Γ(C, C₀) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    f₀.appLE ⊤ C₀ (fun _ _ => trivial)).hom with hκCdef
  let : Algebra k Γ(C, C₀) := κC.toAlgebra
  have hκC : ∀ c, C.germToFunctionField C₀ (κC c) = algebraMap k C.functionField c := by
    intro c
    rw [hkC c]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  set τC : MvPolynomial (Fin 1) k →+* Γ(C, C₀) := MvPolynomial.eval₂Hom κC ![sec b] with hτCdef
  let : Algebra (MvPolynomial (Fin 1) k) Γ(C, C₀) := τC.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, C₀) :=
    IsScalarTower.of_algebraMap_eq fun c => (MvPolynomial.eval₂Hom_C _ _ _).symm
  have : IsDomain Γ(C, C₀) := IsIntegral.component_integral C₀
  have : Algebra.FiniteType k Γ(C, C₀) := finiteType_appLE_comp_ΓSpecIso_inv f₀ hC₀
  have : Algebra.FiniteType (MvPolynomial (Fin 1) k) Γ(C, C₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 1) k) Γ(C, C₀)
  -- the second coordinate of `W` is pulled back from `C₀`
  have hψW : (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)).comp (ιT k) =
      (pr₂.appLE C₀ W inf_le_right).hom.comp τC := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply]
      rw [show (ιT k) (MvPolynomial.C c) = MvPolynomial.C c from MvPolynomial.rename_C _ _, hRBc,
        hτCdef, MvPolynomial.eval₂Hom_C, hκCdef, hκdef]
      exact congrArg (fun φ => ((Scheme.ΓSpecIso (.of k)).inv ≫ φ).hom c)
        (appLE_comp_eq pr₁ pr₂ f₀ hX.w (U := ⊤) (C₀ := C₀) (W := W) (fun _ _ => trivial)
          inf_le_right _)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [RingHom.comp_apply]
      rw [show (ιT k) (MvPolynomial.X 0) = MvPolynomial.X 1 from MvPolynomial.rename_X _ _, hRBb,
        hτCdef, MvPolynomial.eval₂Hom_X']
      rfl
  have hτC_inj : Function.Injective τC := by
    intro p q hpq
    have h := congrArg (pr₂.appLE C₀ W inf_le_right).hom hpq
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← hψW, RingHom.comp_apply,
      RingHom.comp_apply] at h
    exact MvPolynomial.rename_injective _ (Fin.succ_injective _) (hRB_inj h)
  have hτC_int : τC.IsIntegral := by
    intro t
    let : Algebra (MvPolynomial (Fin 1) k) C.functionField :=
      ((C.germToFunctionField C₀).hom.comp τC).toAlgebra
    have : IsScalarTower (MvPolynomial (Fin 1) k) Γ(C, C₀) C.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 : IsIntegral (MvPolynomial (Fin 1) k) (C.germToFunctionField C₀ t) :=
      isIntegral_map_of_mem_integralClosure (AlgHom.id k C.functionField) (x b / x 0)
        ⟨MvPolynomial.X 0, by
          change C.germToFunctionField C₀ (τC (MvPolynomial.X 0)) = x b / x 0
          rw [hτCdef, MvPolynomial.eval₂Hom_X']
          exact hsec b⟩
        (fun c => ⟨MvPolynomial.C c, by
          change C.germToFunctionField C₀ (τC (MvPolynomial.C c)) = algebraMap k C.functionField c
          rw [hτCdef, MvPolynomial.eval₂Hom_C]
          exact hκC c⟩)
        (hint b hb t)
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 1) k) Γ(C, C₀) C.functionField)
      (C.germToFunctionField_injective C₀)).mp h1
  have : Algebra.IsIntegral (MvPolynomial (Fin 1) k) Γ(C, C₀) := ⟨hτC_int⟩
  have : Module.Finite (MvPolynomial (Fin 1) k) Γ(C, C₀) := Algebra.IsIntegral.finite
  have hτN := residueDegree_genericPoint_chart_curve f₀ ((N : ℤ) • P₁)
    (BombieriSiegel.isClosed_of_mem_support_smul hP₁cl _) N
    (BombieriSiegel.finsum_smul_mul_residueDegree f₀ hP₁ _) E hE (hx0 0) (hx0 b) (hxE 0)
    (hxE b) (hNG1 b hb) hC₀ (hchart b hb) (fun _ => rfl) hτC_inj
    (by
      change C.germToFunctionField C₀ (τC (MvPolynomial.X 0)) = _
      rw [hτCdef, MvPolynomial.eval₂Hom_X']
      exact hsec b)
  -- the fibres `c × C`, `C × c` over the support of `P₁`, and `Δ`
  have hgenC : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηC₀ : genericPoint C ∈ C₀ := hgenC _ hφNP_ne
  obtain ⟨e₁, e₂, he, hpr₁eΔ, hpr₂eΔ, hBeΔ, hBm⟩ :=
    exists_fibrePoints f₀ hX Δ hΔ₁ hΔ₂ P₁ hP₁cl heΔ s B hB
  have heΔeq : eΔ = Δ (genericPoint C) := eq_of_isGenericPoint_range Δ heΔ
  -- the fibres `c × C` and `Δ` are prime divisors
  have hG : ∀ w, 0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w + B w → False := fun w h1 h2 => by
    obtain ⟨r, -, hr1, hr2⟩ := hBG1 i hi w w h1 h2
    omega
  have hcohe₁ : ∀ c ∈ P₁.support, Order.coheight (e₁ c) = 1 := fun c hc =>
    coheight_eq_one_of_ne_zero B f hD i hG (by
      rw [(he c hc).2.2.2.2.2.2]
      exact mul_ne_zero (by positivity) (Finsupp.mem_support_iff.mp hc))
  have hcoheΔ : Order.coheight eΔ = 1 :=
    coheight_eq_one_of_ne_zero B f hD i hG (by rw [hBeΔ]; decide)
  -- the chart `W` over `𝔸²`
  set πW : Spec Γ(X, W) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W))) with hπWdef
  have : IsFinite πW :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨F, hF⟩ : ∃ F : PrimeSpectrum (MvPolynomial (Fin 2) k) → Set (Spec Γ(X, W)),
      ∀ y, F y = πW.base ⁻¹' {y} := ⟨_, fun _ => rfl⟩
  have hmemF : ∀ y z, z ∈ F y ↔ πW z = y := fun y z => by rw [hF]; rfl
  have hfibW : ∀ y, (F y).Finite := fun y => by rw [hF]; exact πW.finite_preimage_singleton y
  have hKLW : ∀ r, algebraMap K X.functionField (algebraMap (MvPolynomial (Fin 2) k) K r) =
      X.germToFunctionField W (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W) r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply, hRBL]; rfl
  have hcohSpec : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      Order.coheight (show Spec (.of (MvPolynomial (Fin 2) k)) from y) = 1 := fun y hy => by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy
  -- the subfield `k(ξ_a, ξ'_b)` is the image of `K`
  have hadj : ∀ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
      ∃ κ' : K, algebraMap K X.functionField κ' = r := by
    let S : IntermediateField k X.functionField :=
      (algebraMap K X.functionField).fieldRange.toIntermediateField fun c =>
        ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.C c), by
          rw [← IsScalarTower.algebraMap_apply, hRL₀]⟩
    have hle : IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)} ≤ S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      · exact ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 0), by
          rw [← IsScalarTower.algebraMap_apply, hRLa]⟩
      · exact ⟨algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 1), by
          rw [← IsScalarTower.algebraMap_apply, hRLb]⟩
    exact fun r hr => hle hr
  -- the order of `U i` along a prime divisor of `𝔸²` is the push-forward of `Dᵢ`
  have hperY : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) =
        ∑ᶠ z ∈ F y, (X.ord (f i) (hW.fromSpec z) + B (hW.fromSpec z)) *
          (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) := fun y hy => by
    rw [hF]
    exact ordAt_num_eq_finsum_chart hW hRB_inj hKLW f hf B hD hU i (fun w w' h1 h2 => by
      obtain ⟨r, hrK, hr1, hr2⟩ := hBG1 i hi w w' h1 h2
      obtain ⟨κ', rfl⟩ := hadj r hrK
      exact ⟨κ', hr1, hr2⟩) y hy
  have hheightW : ∀ z : Spec Γ(X, W), coheight (hW.fromSpec z) = 1 →
      (πW z).asIdeal.height = 1 ∧ coheight z = coheight (πW z) := by
    intro z hz
    have := z.isPrime
    have hz1 : coheight z = 1 := (coheight_eq_of_isOpenImmersion hW.fromSpec).symm.trans hz
    have hzh : z.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hz1
    obtain ⟨π, hπ, hzπ⟩ := exists_prime_comap_eq_span (A := MvPolynomial (Fin 2) k)
      (B := Γ(X, W)) hzh
    have hy : (πW z).asIdeal.height = 1 := by
      have h := height_span_prime hπ
      rw [← hzπ] at h
      exact h
    exact ⟨hy, hz1.trans (hcohSpec _ hy).symm⟩
  -- the weight of a curve over the generic point of the second factor on `W`
  have hwtW : ∀ z : Spec Γ(X, W), pr₂ (hW.fromSpec z) = genericPoint C → ∀ d : ℕ,
      pr₂.residueDegree (hW.fromSpec z) = d → coheight (hW.fromSpec z) = 1 →
      IsHor (πW z) ∧ ((πT k).residueDegree (πW z) : ℤ) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) = d * N := by
    intro z hz d hd hz1
    obtain ⟨hy1, hcoh⟩ := hheightW z hz1
    obtain ⟨h1, h2⟩ := chart_weight (ιT k) hC₀ hW inf_le_right τC hτC_inj
      (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) hψW z hz d hd
    have h3 : (Spec.map (CommRingCat.ofHom τC)).residueDegree
        (genericPoint (Spec Γ(C, C₀))) = N := hτN
    rw [h3] at h1
    refine ⟨by unfold IsHor; exact ⟨hy1, h2⟩, ?_⟩
    rw [AlgebraicCycle.mapCoeff, ite_eq_left hcoh]
    exact_mod_cast h1
  obtain ⟨T, hT⟩ : ∃ T : X → PrimeSpectrum (MvPolynomial (Fin 2) k) → ℤ, ∀ e y, T e y =
      if IsHor y then ((πT k).residueDegree y : ℤ) * ∑ᶠ z ∈ F y,
        (if hW.fromSpec z = e then (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) else 0)
      else 0 := ⟨_, fun _ _ => rfl⟩
  have hjW : Function.Injective (fun z : Spec Γ(X, W) => hW.fromSpec z) :=
    hW.fromSpec.isOpenEmbedding.injective
  have hTval : ∀ z₀ : Spec Γ(X, W), ∑ᶠ y, T (hW.fromSpec z₀) y =
      if IsHor (πW z₀) then ((πT k).residueDegree (πW z₀) : ℤ) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z₀ : ℤ) else 0 := fun z₀ => by
    simp only [hT]
    exact (finsum_fibre_ite_eq hjW F hmemF IsHor (fun y => ((πT k).residueDegree y : ℤ))
      (fun z => (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ)) z₀).2
  have hTzero : ∀ e : X, (∀ z : Spec Γ(X, W), hW.fromSpec z ≠ e) → ∑ᶠ y, T e y = 0 :=
    fun e he => by
      simp only [hT]
      exact (finsum_fibre_ite_eq_zero (j := fun z => hW.fromSpec z) he F IsHor _ _).2
  have hTfin : ∀ e, (Function.support (T e)).Finite := by
    intro e
    by_cases he : ∃ z, hW.fromSpec z = e
    · obtain ⟨z₀, rfl⟩ := he
      refine (Set.finite_singleton (α := PrimeSpectrum (MvPolynomial (Fin 2) k)) (πW z₀)).subset
        fun y hy => ?_
      rw [Function.mem_support, hT, (finsum_fibre_ite_eq hjW F hmemF IsHor
        (fun y => ((πT k).residueDegree y : ℤ))
        (fun z => (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ)) z₀).1 y] at hy
      change y = πW z₀
      by_contra hne
      apply hy
      split_ifs with h1 h2
      · exact absurd h2.symm hne
      · rw [mul_zero]
      · rfl
    · push Not at he
      have h0 := (finsum_fibre_ite_eq_zero (j := fun z => hW.fromSpec z) he F IsHor
        (fun y => ((πT k).residueDegree y : ℤ))
        (fun z => (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ))).1
      refine Set.finite_empty.subset fun y hy => ?_
      rw [Function.mem_support, hT] at hy
      exact absurd (by simp only [h0, mul_zero, ite_self]) hy
  -- the parts of the degree formula over the horizontal prime divisors
  have hfiN : Algebra.norm K (f i) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hf i)
  obtain ⟨hfinN, -⟩ := finsum_add_ordAt_inf_eq_zero (k := k) (K := K) hfiN
  have hBW : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) =
        ordAt y (Algebra.norm K (f i)) +
        ((s + 1) * ∑ c ∈ P₁.support, P₁ c * ∑ᶠ z ∈ F y, (if hW.fromSpec z = e₁ c then
            (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) else 0) +
          (s + 1) * ∑ c ∈ P₁.support, P₁ c * ∑ᶠ z ∈ F y, (if hW.fromSpec z = e₂ c then
            (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) else 0) -
          ∑ᶠ z ∈ F y, (if hW.fromSpec z = eΔ then
            (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) else 0)) := by
    intro y hy
    have hS := hfibW y
    have hN : ordAt y (Algebra.norm K (f i)) = ∑ᶠ z ∈ F y, X.ord (f i) (hW.fromSpec z) *
        (AlgebraicCycle.mapCoeff πW coheight coheight z : ℤ) := by
      rw [hF]; exact ordAt_norm_eq_finsum (k := k) hW hRB_inj hKLW (hf i) y
    rw [hperY y hy, hN]
    simp only [finsum_mem_eq_finite_toFinset_sum _ hS]
    rw [← sum_mul_eq_of_forall_mul_eq _ (fun z => hW.fromSpec z) _ B _ _ _ e₁ e₂ eΔ hBm,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => add_mul _ _ _
  have hterm : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k),
      (if IsHor y then ((πT k).residueDegree y : ℤ) *
        ordAt y (algebraMap (MvPolynomial (Fin 2) k) K (U i)) else 0) =
      (if IsHor y then ((πT k).residueDegree y : ℤ) * ordAt y (Algebra.norm K (f i)) else 0) +
        ((s + 1) * ∑ c ∈ P₁.support, P₁ c * T (e₁ c) y +
          (s + 1) * ∑ c ∈ P₁.support, P₁ c * T (e₂ c) y - T eΔ y) := by
    intro y
    simp only [hT]
    split_ifs with hy
    · rw [hBW y hy.1]
      simp only [mul_left_comm _ ((πT k).residueDegree y : ℤ), ← Finset.mul_sum]
      ring
    · simp
  -- the values at `Δ`
  have heΔW : eΔ ∈ W := ⟨show pr₁ eΔ ∈ C₀ by rw [hpr₁eΔ]; exact hηC₀,
    show pr₂ eΔ ∈ C₀ by rw [hpr₂eΔ]; exact hηC₀⟩
  obtain ⟨zΔ, hzΔ⟩ : ∃ z : Spec Γ(X, W), hW.fromSpec z = eΔ :=
    ⟨hW.primeIdealOf ⟨eΔ, heΔW⟩, hW.fromSpec_primeIdealOf ⟨eΔ, heΔW⟩⟩
  obtain ⟨hHorΔ, hwΔ⟩ := hwtW zΔ (by rw [hzΔ]; exact hpr₂eΔ) 1
    (by rw [hzΔ, heΔeq]; exact (residueDegree_eq_one_of_section Δ pr₂ hΔ₂ _).1)
    (by rw [hzΔ]; exact hcoheΔ)
  have hTΔ : ∑ᶠ y, T eΔ y = N := by
    rw [← hzΔ, hTval zΔ, ite_eq_left hHorΔ, hwΔ, Nat.cast_one, one_mul]
  -- the values at the fibres `c × C`: horizontal of degree `[κ(c) : k] N` when `c ∈ C₀`
  have hT₁ : ∀ c ∈ P₁.support, ∑ᶠ y, T (e₁ c) y =
      if c ∈ C₀ then (f₀.residueDegree c : ℤ) * N else 0 := by
    intro c hc
    obtain ⟨-, hpr₁, hpr₂, hrd, -, -, -⟩ := he c hc
    split_ifs with hcC₀
    · have he₁W : e₁ c ∈ W := ⟨show pr₁ (e₁ c) ∈ C₀ by rw [hpr₁]; exact hcC₀,
        show pr₂ (e₁ c) ∈ C₀ by rw [hpr₂]; exact hηC₀⟩
      obtain ⟨z, hz⟩ : ∃ z : Spec Γ(X, W), hW.fromSpec z = e₁ c :=
        ⟨hW.primeIdealOf ⟨_, he₁W⟩, hW.fromSpec_primeIdealOf ⟨_, he₁W⟩⟩
      obtain ⟨hHor, hw⟩ := hwtW z (by rw [hz]; exact hpr₂) (f₀.residueDegree c)
        (by rw [hz]; exact hrd)
        (by rw [hz]; exact hcohe₁ c hc)
      rw [← hz, hTval z, ite_eq_left hHor, hw]
    · exact hTzero _ fun z hz => by
        obtain ⟨hzW, -⟩ := fromSpec_mem_and_primeIdealOf hW z
        exact hcC₀ (by rw [← hpr₁, ← hz]; exact hzW.1)
  -- the fibres `C × c` are vertical
  have hT₂ : ∀ c ∈ P₁.support, ∑ᶠ y, T (e₂ c) y = 0 := by
    intro c hc
    obtain ⟨hcη, -, -, -, hpr₁, hpr₂, -⟩ := he c hc
    by_cases hcC₀ : c ∈ C₀
    · have he₂W : e₂ c ∈ W := ⟨show pr₁ (e₂ c) ∈ C₀ by rw [hpr₁]; exact hηC₀,
        show pr₂ (e₂ c) ∈ C₀ by rw [hpr₂]; exact hcC₀⟩
      obtain ⟨z, hz⟩ : ∃ z : Spec Γ(X, W), hW.fromSpec z = e₂ c :=
        ⟨hW.primeIdealOf ⟨_, he₂W⟩, hW.fromSpec_primeIdealOf ⟨_, he₂W⟩⟩
      have hnHor : ¬ IsHor (πW z) := fun h => by
        unfold IsHor at h
        exact chart_not_horizontal hC₀ hW inf_le_right τC hτC_int
          (algebraMap (MvPolynomial (Fin 2) k) Γ(X, W)) hψW z
          (by rw [hz, hpr₂]; exact hcη) h.2
      rw [← hz, hTval z, ite_eq_right hnHor]
    · exact hTzero _ fun z hz => by
        obtain ⟨hzW, -⟩ := fromSpec_mem_and_primeIdealOf hW z
        exact hcC₀ (by rw [← hpr₂, ← hz]; exact hzW.2)
  exact ⟨inferInstance, finsum_eq_add_of_forall_eq_add_sum _ _ T ((s : ℤ) + 1) P₁.support P₁ _
    e₁ e₂ eΔ N hfinN hTfin hterm hT₁ hT₂ hTΔ⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **The part at infinity of the degree of `U i`**, read on the chart
`W' = pr₁⁻¹ C₁ ∩ pr₂⁻¹ C₀` at `ξ_a = ∞`, where `C₁ = φ⁻¹ D₊(T_a)`. The order of `Norm (f i)` at
`ξ_a = ∞` and the push-forward of the divisor `B` along the fibres `c × C`, `C × c` and `Δ` add
up to zero, since `D_i` has no component at infinity; the push-forwards of `Δ` and `C × c`
vanish, and that of `c × C` is `[κ(c) : k] N` when `c` is a pole of `ξ_a` and vanishes
otherwise. -/
private theorem exists_ordAt_inf_norm_eq_of_isReducedNormRepresentation
    {k : Type u} [Field k] {C X : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsLocallyNoetherian C] [GeometricallyIntegral (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsCurve k (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial
        ((C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of k)) (C ↘ Spec (.of k)))
    [IsIntegral X] [IsLocallyNoetherian X] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * ((C ↘ Spec (.of k)).residueDegree Q : ℤ) = 1)
    {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (ι₁ ι₂ : C.functionField →+* X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the divisor `N P₁` on `C`, and the generic basis `x` of `H⁰(C, 𝒪(N P₁))` giving `φ_{NP₁}`
    (N : ℕ) {n : ℕ} (E : C → ℤ) (hE : ∀ z, E z = ((N : ℤ) • P₁) z)
    (x : Fin (n + 1) → C.functionField) (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z)
    (hxli : LinearIndependent k x)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = C ↘ Spec (.of k))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- (N): the basis `x` is generic
    (hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    -- the very ample divisor `B` on `X`, and the basis `f` of `H⁰(X, 𝒪(B))` giving `φ_B`
    (s : ℕ)
    (B : X → ℤ) (hB : ∀ w, B w =
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (f : Fin (m + 1) → X.functionField) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hBG1 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w',
      0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w, 0 < X.ord (f i) w + B w →
      0 ≤ X.ord (ι₁ (x a / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b / x 0)) w)
    {K : Type u} [Field K] [instRK : Algebra (MvPolynomial (Fin 2) k) K]
    [instFrac : IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [instRL : Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [instTower : IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    (i : Fin (m + 1)) (hi : i ≠ 0) [FiniteDimensional K X.functionField] :
    @ordAt (MvPolynomial (Fin 2) k) _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf
        (yInf k) (Algebra.norm K (f i)) +
      (s + 1) * ∑ c ∈ P₁.support, P₁ c *
        (if c ∈ φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X 0)) then 0
          else ((C ↘ Spec (.of k)).residueDegree c : ℤ) * N) = 0 := by
  classical
  set f₀ := C ↘ Spec (.of k) with hf₀
  have : IsNormal C := isNormal_of_smooth_over_field f₀
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hX.flip inferInstance
  have : Smooth pr₂ := MorphismProperty.of_isPullback (P := @Smooth) hX inferInstance
  have : LocallyOfFiniteType pr₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX.flip inferInstance
  have : IsNormal X := isNormal_of_smooth_over_field (pr₁ ≫ f₀)
  have hx0 : ∀ j, x j ≠ 0 := hxli.ne_zero
  -- the chart `C₀ = φ⁻¹ D₊(T₀)` of `C`, containing the generic point
  obtain ⟨hη₀, hξ₀⟩ := BombieriRoth.exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  set C₀ : C.Opens := φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X 0)) with hC₀def
  have hφNP_ne : (C₀ : Set C).Nonempty := ⟨_, hη₀⟩
  have hC₀ne : Nonempty C₀ := ⟨⟨_, hη₀⟩⟩
  have hC₀ : IsAffineOpen C₀ :=
    (ProjectiveSpace.isAffineOpen_standardOpen n (Spec (.of k)) 0).preimage φNP
  have hchart : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ c : C,
      x a' / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₀ :=
    fun a' ha' c hc => mem_preimage_basicOpen_of_mem_range f₀ E x hx0 hxE φNP hφNPx
      (hNG1 a' ha') hc
  have hint : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ s : Γ(C, C₀), C.germToFunctionField C₀ s ∈
      integralClosure (Algebra.adjoin k {x a' / x 0}) C.functionField :=
    fun a' ha' => germToFunctionField_mem_integralClosure f₀ hkC _ C₀ (hchart a' ha')
  -- the sections `ξ_j = x j / x 0` over `C₀`
  set sec : Fin (n + 1) → Γ(C, C₀) := fun j => φNP.app _
    ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
          (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X _ j)))) with hsecdef
  have hsec : ∀ j, C.germToFunctionField C₀ (sec j) = x j / x 0 := fun j => hξ₀ j
  have hC₀top : C₀ ≤ f₀ ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  -- the chart `C₁ = φ⁻¹ D₊(T_a)` of `C`, with coordinates `x j / x a`, read on the integral model
  obtain ⟨hC₁ne', hφa⟩ := chart_change x hx0
    (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) hφNP_ne (fun j => hξ₀ j) a
  set C₁ : C.Opens := (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X a) with hC₁def
  have hC₁ne : Nonempty C₁ := ⟨⟨_, hC₁ne'.some_mem⟩⟩
  have hC₁ : IsAffineOpen C₁ :=
    (ProjectiveSpace.isAffineOpen_standardOpen n (Spec (.of k)) a).preimage φNP
  set sec₁ : Fin (n + 1) → Γ(C, C₁) := fun j =>
    (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X a)
        (HomogeneousLocalization.Away.mk _
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ a)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))) with hsec₁def
  have hsec₁ : ∀ j, C.germToFunctionField C₁ (sec₁ j) = x j / x a := fun j => @hφa hC₁ne j
  have hchart₁ : ∀ c : C,
      x 0 / x a ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₁ :=
    fun c hc => mem_preimage_basicOpen_X_of_mem_range f₀ a E x hx0 hxE _ hC₁ne' hφa
      (fun z hz => (hNG1 a ha z hz).symm) hc
  have hint₁ : ∀ t : Γ(C, C₁), C.germToFunctionField C₁ t ∈
      integralClosure (Algebra.adjoin k {C.germToFunctionField C₁ (sec₁ 0)}) C.functionField :=
    fun t => by
      rw [hsec₁]
      exact germToFunctionField_mem_integralClosure f₀ hkC _ C₁ hchart₁ t
  have hint₀ : ∀ t : Γ(C, C₀), C.germToFunctionField C₀ t ∈
      integralClosure (Algebra.adjoin k {C.germToFunctionField C₀ (sec b)}) C.functionField :=
    fun t => by
      rw [hsec]
      exact hint b hb t
  -- the chart `W' = pr₁⁻¹ C₁ ∩ pr₂⁻¹ C₀` at `ξ_a = ∞`
  set W' : X.Opens := pr₁ ⁻¹ᵁ C₁ ⊓ pr₂ ⁻¹ᵁ C₀ with hW'def
  have hC₁top : C₁ ≤ f₀ ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  have hW' : IsAffineOpen W' :=
    isAffineOpen_of_isPullback hX (isAffineOpen_top (Spec (.of k))) hC₁ hC₀ hC₁top hC₀top hW'def
  have hW'ne : Nonempty W' := by
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := f₀)
      hC₁ne'.some hφNP_ne.some (Subsingleton.elim _ _)
    refine ⟨⟨hX.isoPullback.inv z, ?_, ?_⟩⟩
    · change pr₁ (hX.isoPullback.inv z) ∈ C₁
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_fst, hz1]
      exact hC₁ne'.some_mem
    · change pr₂ (hX.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_snd, hz2]
      exact hφNP_ne.some_mem
  have : Nonempty (pr₁ ⁻¹ᵁ C₁) := ⟨⟨hW'ne.some.1, hW'ne.some.2.1⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ C₀) := ⟨⟨hW'ne.some.1, hW'ne.some.2.2⟩⟩
  have : Nonempty (⊤ : X.Opens) := ⟨⟨hW'ne.some.1, trivial⟩⟩
  -- `ι₁`, `ι₂` are `k`-linear
  have : Nonempty (⊤ : C.Opens) := ⟨⟨pr₁ hW'ne.some.1, trivial⟩⟩
  have : Nonempty (pr₁ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hW'ne.some.1, trivial⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hW'ne.some.1, trivial⟩⟩
  have hι₁k : ∀ c, ι₁ (algebraMap k C.functionField c) = algebraMap k X.functionField c := by
    intro c
    rw [hkC c, hkX c]
    exact (hι₁ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  have hι₂k : ∀ c, ι₂ (algebraMap k C.functionField c) = algebraMap k X.functionField c := by
    intro c
    rw [hkC c, hkX c, hX.w]
    exact (hι₂ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  let ι₁' : C.functionField →ₐ[k] X.functionField := { ι₁ with commutes' := hι₁k }
  let ι₂' : C.functionField →ₐ[k] X.functionField := { ι₂ with commutes' := hι₂k }
  -- the curve side: `Γ(C, C₀)` over `k[T]` through `T ↦ ξ_b`
  set κC : k →+* Γ(C, C₀) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    f₀.appLE ⊤ C₀ (fun _ _ => trivial)).hom with hκCdef
  let : Algebra k Γ(C, C₀) := κC.toAlgebra
  have hκC : ∀ c, C.germToFunctionField C₀ (κC c) = algebraMap k C.functionField c := by
    intro c
    rw [hkC c]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  set τC : MvPolynomial (Fin 1) k →+* Γ(C, C₀) := MvPolynomial.eval₂Hom κC ![sec b] with hτCdef
  let : Algebra (MvPolynomial (Fin 1) k) Γ(C, C₀) := τC.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, C₀) :=
    IsScalarTower.of_algebraMap_eq fun c => (MvPolynomial.eval₂Hom_C _ _ _).symm
  have : IsDomain Γ(C, C₀) := IsIntegral.component_integral C₀
  have : Algebra.FiniteType k Γ(C, C₀) := finiteType_appLE_comp_ΓSpecIso_inv f₀ hC₀
  have : Algebra.FiniteType (MvPolynomial (Fin 1) k) Γ(C, C₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 1) k) Γ(C, C₀)
  have hτC_int : τC.IsIntegral := by
    intro t
    let : Algebra (MvPolynomial (Fin 1) k) C.functionField :=
      ((C.germToFunctionField C₀).hom.comp τC).toAlgebra
    have : IsScalarTower (MvPolynomial (Fin 1) k) Γ(C, C₀) C.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 : IsIntegral (MvPolynomial (Fin 1) k) (C.germToFunctionField C₀ t) :=
      isIntegral_map_of_mem_integralClosure (AlgHom.id k C.functionField) (x b / x 0)
        ⟨MvPolynomial.X 0, by
          change C.germToFunctionField C₀ (τC (MvPolynomial.X 0)) = x b / x 0
          rw [hτCdef, MvPolynomial.eval₂Hom_X']
          exact hsec b⟩
        (fun c => ⟨MvPolynomial.C c, by
          change C.germToFunctionField C₀ (τC (MvPolynomial.C c)) = algebraMap k C.functionField c
          rw [hτCdef, MvPolynomial.eval₂Hom_C]
          exact hκC c⟩)
        (hint b hb t)
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 1) k) Γ(C, C₀) C.functionField)
      (C.germToFunctionField_injective C₀)).mp h1
  have : Algebra.IsIntegral (MvPolynomial (Fin 1) k) Γ(C, C₀) := ⟨hτC_int⟩
  have : Module.Finite (MvPolynomial (Fin 1) k) Γ(C, C₀) := Algebra.IsIntegral.finite
  have : IsDomain Γ(X, W') := IsIntegral.component_integral W'
  have : IsNoetherianRing Γ(X, W') := IsLocallyNoetherian.component_noetherian ⟨W', hW'⟩
  have : IsIntegrallyClosed Γ(X, W') :=
    (isNormal_iff_forall_affineOpen_normal X).mp inferInstance ⟨W', hW'⟩ inferInstance
  have hgermLE' : ∀ {V : X.Opens} [Nonempty V] (h : W' ≤ V) (t : Γ(X, V)),
      X.germToFunctionField W' (X.presheaf.map (homOfLE h).op t) = X.germToFunctionField V t :=
    fun h t => X.presheaf.germ_res_apply (homOfLE h) _ _ t
  set κ' : k →+* Γ(X, W') := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (pr₁ ≫ f₀).appLE ⊤ W' (fun _ _ => trivial)).hom with hκ'def
  have hκ' : ∀ c, X.germToFunctionField W' (κ' c) = algebraMap k X.functionField c := by
    intro c
    rw [hkX c]
    exact hgermLE' le_top _
  have hpr₁' : ∀ t : Γ(C, C₁), X.germToFunctionField W' (pr₁.appLE C₁ W' inf_le_left t) =
      ι₁ (C.germToFunctionField C₁ t) := by
    intro t
    rw [hι₁ C₁ t]
    exact hgermLE' inf_le_left _
  have hpr₂' : ∀ t : Γ(C, C₀), X.germToFunctionField W' (pr₂.appLE C₀ W' inf_le_right t) =
      ι₂ (C.germToFunctionField C₀ t) := by
    intro t
    rw [hι₂ C₀ t]
    exact hgermLE' inf_le_right _
  set ψ' : MvPolynomial (Fin 2) k →+* Γ(X, W') := MvPolynomial.eval₂Hom κ'
    ![pr₁.appLE C₁ W' inf_le_left (sec₁ 0), pr₂.appLE C₀ W' inf_le_right (sec b)] with hψ'def
  have hψ'int : ψ'.IsIntegral := chart_isIntegral hX hC₁ hC₀ hW'def inf_le_left inf_le_right
    ι₁' ι₂' hpr₁' hpr₂' (sec₁ 0) (sec b) hint₁ hint₀ κ' hκ'
  let : Algebra k Γ(X, W') := κ'.toAlgebra
  have : Algebra.FiniteType k Γ(X, W') := finiteType_appLE_comp_ΓSpecIso_inv (pr₁ ≫ f₀) hW'
  have hψ'k : ∀ c : k, ψ' (algebraMap k (MvPolynomial (Fin 2) k) c) =
      algebraMap k Γ(X, W') c := fun c => MvPolynomial.eval₂Hom_C _ _ _
  have hψ'fin : ψ'.Finite := by
    let : Algebra (MvPolynomial (Fin 2) k) Γ(X, W') := ψ'.toAlgebra
    have : IsScalarTower k (MvPolynomial (Fin 2) k) Γ(X, W') :=
      IsScalarTower.of_algebraMap_eq fun c => (hψ'k c).symm
    have : Algebra.FiniteType (MvPolynomial (Fin 2) k) Γ(X, W') :=
      Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 2) k) Γ(X, W')
    exact RingHom.IsIntegral.to_finite hψ'int this
  -- the function field of the chart at infinity
  have hKL' : ∀ r, algebraMap K X.functionField (θinf k K r) = X.germToFunctionField W' (ψ' r) := by
    intro r
    have : (algebraMap K X.functionField).comp (θinf k K) =
        (X.germToFunctionField W').hom.comp ψ' := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp only [RingHom.comp_apply]
        rw [hψ'def, MvPolynomial.eval₂Hom_C, hκ', θinf, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hRL₀]
      · fin_cases j
        · change algebraMap K X.functionField (θinf k K (MvPolynomial.X 0)) =
            X.germToFunctionField W' (ψ' (MvPolynomial.X 0))
          rw [θinf_X0, map_inv₀, ← IsScalarTower.algebraMap_apply, hRLa, hψ'def,
            MvPolynomial.eval₂Hom_X']
          change _ = X.germToFunctionField W' (pr₁.appLE C₁ W' inf_le_left (sec₁ 0))
          rw [hpr₁', hsec₁, ← map_inv₀, inv_div]
        · change algebraMap K X.functionField (θinf k K (MvPolynomial.X 1)) =
            X.germToFunctionField W' (ψ' (MvPolynomial.X 1))
          rw [show θinf k K (MvPolynomial.X 1) =
            algebraMap (MvPolynomial (Fin 2) k) K (MvPolynomial.X 1) by simp [θinf],
            ← IsScalarTower.algebraMap_apply, hRLb, hψ'def, MvPolynomial.eval₂Hom_X']
          change _ = X.germToFunctionField W' (pr₂.appLE C₀ W' inf_le_right (sec b))
          rw [hpr₂', hsec]
    exact congr($this r)
  have hψ'inj : Function.Injective ψ' := by
    intro r r' h
    have h1 := congrArg (X.germToFunctionField W') h
    rw [← hKL', ← hKL'] at h1
    exact θinf_injective (k := k) (K := K) ((algebraMap K X.functionField).injective h1)
  have hψ'W : ψ'.comp (ιT k) = (pr₂.appLE C₀ W' inf_le_right).hom.comp τC := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply]
      rw [show (ιT k) (MvPolynomial.C c) = MvPolynomial.C c from MvPolynomial.rename_C _ _,
        hψ'def, MvPolynomial.eval₂Hom_C, hτCdef, MvPolynomial.eval₂Hom_C, hκCdef, hκ'def]
      exact congrArg (fun φ => ((Scheme.ΓSpecIso (.of k)).inv ≫ φ).hom c)
        (appLE_comp_eq pr₁ pr₂ f₀ hX.w (U := ⊤) (C₀ := C₀) (W := W') (fun _ _ => trivial)
          inf_le_right _)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [RingHom.comp_apply]
      rw [show (ιT k) (MvPolynomial.X 0) = MvPolynomial.X 1 from MvPolynomial.rename_X _ _,
        hψ'def, MvPolynomial.eval₂Hom_X', hτCdef, MvPolynomial.eval₂Hom_X']
      rfl
  have hτC_inj : Function.Injective τC := by
    intro p q hpq
    have h := congrArg (pr₂.appLE C₀ W' inf_le_right).hom hpq
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← hψ'W, RingHom.comp_apply,
      RingHom.comp_apply] at h
    exact MvPolynomial.rename_injective _ (Fin.succ_injective _) (hψ'inj h)
  have hτN := residueDegree_genericPoint_chart_curve f₀ ((N : ℤ) • P₁)
    (BombieriSiegel.isClosed_of_mem_support_smul hP₁cl _) N
    (BombieriSiegel.finsum_smul_mul_residueDegree f₀ hP₁ _) E hE (hx0 0) (hx0 b) (hxE 0)
    (hxE b) (hNG1 b hb) hC₀ (hchart b hb) (fun _ => rfl) hτC_inj
    (by
      change C.germToFunctionField C₀ (τC (MvPolynomial.X 0)) = _
      rw [hτCdef, MvPolynomial.eval₂Hom_X']
      exact hsec b)
  -- the fibres `c × C`, `C × c` over the support of `P₁`, and `Δ`
  have hgenC : ∀ U : C.Opens, (U : Set C).Nonempty → genericPoint C ∈ U := fun U hU =>
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηC₀ : genericPoint C ∈ C₀ := hgenC _ hφNP_ne
  obtain ⟨e₁, e₂, he, hpr₁eΔ, hpr₂eΔ, hBeΔ, hBm⟩ :=
    exists_fibrePoints f₀ hX Δ hΔ₁ hΔ₂ P₁ hP₁cl heΔ s B hB
  have heΔeq : eΔ = Δ (genericPoint C) := eq_of_isGenericPoint_range Δ heΔ
  -- the fibres `c × C` and `Δ` are prime divisors
  have hG : ∀ w, 0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w + B w → False := fun w h1 h2 => by
    obtain ⟨r, -, hr1, hr2⟩ := hBG1 i hi w w h1 h2
    omega
  have hcohe₁ : ∀ c ∈ P₁.support, Order.coheight (e₁ c) = 1 := fun c hc =>
    coheight_eq_one_of_ne_zero B f hD i hG (by
      rw [(he c hc).2.2.2.2.2.2]
      exact mul_ne_zero (by positivity) (Finsupp.mem_support_iff.mp hc))
  have hcohSpec : ∀ y : PrimeSpectrum (MvPolynomial (Fin 2) k), y.asIdeal.height = 1 →
      Order.coheight (show Spec (.of (MvPolynomial (Fin 2) k)) from y) = 1 := fun y hy => by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]; exact hy
  -- the chart `W'` over `ℙ¹ × 𝔸¹`, near `ξ_a = ∞`
  set πW' : Spec Γ(X, W') ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
    Spec.map (CommRingCat.ofHom ψ') with hπW'def
  have : IsFinite πW' := (IsFinite.SpecMap_iff _).mpr hψ'fin
  obtain ⟨F', hF'⟩ : ∃ F' : Set (Spec Γ(X, W')), F' = πW'.base ⁻¹' {yInf k} := ⟨_, rfl⟩
  have hmemF' : ∀ z, z ∈ F' ↔ πW' z = yInf k := fun z => by rw [hF']; rfl
  have hfibW' : F'.Finite := by rw [hF']; exact πW'.finite_preimage_singleton _
  have hInf1 : (yInf k).asIdeal.height = 1 := height_span_prime prime_X0
  have hθnorm : @ordAt _ _ _ _ K _ (θinf k K).toAlgebra isFractionRing_θinf (yInf k)
      (Algebra.norm K (f i)) = ∑ᶠ z ∈ F', X.ord (f i) (hW'.fromSpec z) *
        (AlgebraicCycle.mapCoeff πW' coheight coheight z : ℤ) := by
    rw [hF']
    exact ordAt_norm_eq_finsum_of_ringHom hW' ψ' hψ'k hψ'fin hψ'inj (θinf k K) isFractionRing_θinf
      hKL' (hf i) (yInf k)
  -- a prime divisor of `W'` over `ξ_a = ∞` is a pole of `ξ_a`
  have hinfpt : ∀ z : Spec Γ(X, W'), z ∈ F' →
      AlgebraicCycle.mapCoeff πW' coheight coheight z ≠ 0 →
      coheight (hW'.fromSpec z) = 1 ∧ X.ord (ι₁ (x a / x 0)) (hW'.fromSpec z) < 0 := by
    intro z hzF hmc
    have hz := (hmemF' z).mp hzF
    have hz1 : coheight (hW'.fromSpec z) = 1 := by
      rw [AlgebraicCycle.mapCoeff] at hmc
      split_ifs at hmc with hc
      · rw [coheight_eq_of_isOpenImmersion, hc, hz]; exact hcohSpec _ hInf1
      · exact absurd rfl hmc
    refine ⟨hz1, ?_⟩
    obtain ⟨hzW, hzP⟩ := fromSpec_mem_and_primeIdealOf hW' z
    have hX0 : ψ' (MvPolynomial.X 0) ∈ z.asIdeal :=
      show MvPolynomial.X 0 ∈ (πW' z).asIdeal by rw [hz]; exact Ideal.mem_span_singleton_self _
    have hne : ι₁ (x 0 / x a) ≠ 0 :=
      (map_ne_zero_iff _ ι₁.injective).mpr (div_ne_zero (hx0 0) (hx0 a))
    obtain ⟨t, ht, htx⟩ := (mem_primeIdealOf_iff hW' hzW (ψ' (MvPolynomial.X 0))).mp
      (by rw [hzP]; exact hX0)
    have hpos : 0 < X.ord (ι₁ (x 0 / x a)) (hW'.fromSpec z) := by
      refine (ord_pos_iff hz1 hne).mpr ⟨t, ht, ?_⟩
      rw [htx, hψ'def, MvPolynomial.eval₂Hom_X']
      change X.germToFunctionField W' (pr₁.appLE C₁ W' inf_le_left (sec₁ 0)) = _
      rw [hpr₁', hsec₁]
    have hinv : ι₁ (x a / x 0) = (ι₁ (x 0 / x a))⁻¹ := by rw [← map_inv₀, inv_div]
    rw [hinv, Stacks.Chow.ord_inv_functionField hne]
    omega
  -- (G2): `Dᵢ` has no component at infinity
  have hG2' : ∀ z : Spec Γ(X, W'), z ∈ F' →
      AlgebraicCycle.mapCoeff πW' coheight coheight z ≠ 0 →
      X.ord (f i) (hW'.fromSpec z) + B (hW'.fromSpec z) = 0 := by
    intro z hz hmc
    have h := (hinfpt z hz hmc).2
    by_contra hne
    have := (hBG2 i hi _ (lt_of_le_of_ne (hD i _) (Ne.symm hne))).1
    omega
  -- the prime divisors at infinity lie outside `pr₁⁻¹ C₀`
  have hinfW : ∀ z : Spec Γ(X, W'), z ∈ F' →
      AlgebraicCycle.mapCoeff πW' coheight coheight z ≠ 0 → hW'.fromSpec z ∉ pr₁ ⁻¹ᵁ C₀ := by
    intro z hz hmc hzW
    obtain ⟨h1, h2⟩ := hinfpt z hz hmc
    have : Nonempty (pr₁ ⁻¹ᵁ C₀) := ⟨⟨_, hzW⟩⟩
    have hreg : ι₁ (x a / x 0) ∈
        Set.range (algebraMap (X.presheaf.stalk (hW'.fromSpec z)) X.functionField) :=
      ⟨X.presheaf.germ (pr₁ ⁻¹ᵁ C₀) _ hzW (pr₁.app C₀ (sec a)), by
        rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← hι₁ C₀ (sec a), hsec]⟩
    have := (ord_nonneg_iff h1 ((map_ne_zero_iff _ ι₁.injective).mpr
      (div_ne_zero (hx0 a) (hx0 0)))).mpr hreg
    omega
  have hI'zero : ∀ e : X, pr₁ e ∈ C₀ → ∑ᶠ z ∈ F',
      (if hW'.fromSpec z = e then (AlgebraicCycle.mapCoeff πW' coheight coheight z : ℤ)
        else 0) = 0 := by
    intro e he
    refine finsum_mem_eq_zero_of_forall_eq_zero fun z hz => ?_
    split_ifs with hze
    · by_contra hmc
      have hmc' : AlgebraicCycle.mapCoeff πW' coheight coheight z ≠ 0 := fun h =>
        hmc (by rw [h, Nat.cast_zero])
      refine hinfW z hz hmc' ?_
      change pr₁ (hW'.fromSpec z) ∈ C₀
      rw [hze]
      exact he
    · rfl
  have hheightW' : ∀ z : Spec Γ(X, W'), coheight (hW'.fromSpec z) = 1 →
      coheight z = 1 ∧ ∃ π : MvPolynomial (Fin 2) k, Prime π ∧
        (πW' z).asIdeal = Ideal.span {π} := by
    intro z hz
    let : Algebra (MvPolynomial (Fin 2) k) Γ(X, W') := ψ'.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin 2) k) Γ(X, W') := ⟨hψ'int⟩
    have : FaithfulSMul (MvPolynomial (Fin 2) k) Γ(X, W') :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hψ'inj
    have := z.isPrime
    have hz1 : coheight z = 1 := (coheight_eq_of_isOpenImmersion hW'.fromSpec).symm.trans hz
    have hzh : z.asIdeal.height = 1 := by
      rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hz1
    exact ⟨hz1, exists_prime_comap_eq_span (A := MvPolynomial (Fin 2) k) (B := Γ(X, W')) hzh⟩
  obtain ⟨I', hI'⟩ : ∃ I' : X → ℤ, ∀ e, I' e = ∑ᶠ z ∈ F',
      (if hW'.fromSpec z = e then (AlgebraicCycle.mapCoeff πW' coheight coheight z : ℤ)
        else 0) := ⟨_, fun _ => rfl⟩
  have hjW' : Function.Injective (fun z : Spec Γ(X, W') => hW'.fromSpec z) :=
    hW'.fromSpec.isOpenEmbedding.injective
  -- the part at infinity
  have hInfB : (∑ᶠ z ∈ F', X.ord (f i) (hW'.fromSpec z) *
      (AlgebraicCycle.mapCoeff πW' coheight coheight z : ℤ)) +
      ((s + 1) * ∑ c ∈ P₁.support, P₁ c * I' (e₁ c) +
        (s + 1) * ∑ c ∈ P₁.support, P₁ c * I' (e₂ c) - I' eΔ) = 0 := by
    simp only [hI', finsum_mem_eq_finite_toFinset_sum _ hfibW']
    rw [← sum_mul_eq_of_forall_mul_eq _ (fun z => hW'.fromSpec z) _ B _ _ _ e₁ e₂ eΔ hBm,
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Set.Finite.mem_toFinset] at hz
    by_cases hmc : AlgebraicCycle.mapCoeff πW' coheight coheight z = 0
    · simp [hmc]
    · rw [← add_mul, hG2' z hz hmc, zero_mul]
  have hIΔ : I' eΔ = 0 := by rw [hI']; exact hI'zero eΔ (by rw [hpr₁eΔ]; exact hηC₀)
  have hI₂ : ∀ c ∈ P₁.support, I' (e₂ c) = 0 := fun c hc => by
    obtain ⟨-, -, -, -, hpr₁, -, -⟩ := he c hc
    rw [hI']; exact hI'zero _ (by rw [hpr₁]; exact hηC₀)
  -- the fibre `c × C` over a pole `c` of `ξ_a`
  have hI₁ : ∀ c ∈ P₁.support, I' (e₁ c) =
      if c ∈ C₀ then 0 else (f₀.residueDegree c : ℤ) * N := by
    intro c hc
    obtain ⟨-, hpr₁ePC, hpr₂ePC, hrd, -, -, -⟩ := he c hc
    split_ifs with hPC₀
    · rw [hI']; exact hI'zero _ (by rw [hpr₁ePC]; exact hPC₀)
    have hc1 : coheight (pr₁ (e₁ c)) = 1 := by
      rw [hpr₁ePC]; exact Stacks.Zeta.coheight_eq_one_of_isClosed f₀ (hP₁cl c hc)
    have hxa0 : x a / x 0 ≠ 0 := div_ne_zero (hx0 a) (hx0 0)
    have hx0a : x 0 / x a ≠ 0 := div_ne_zero (hx0 0) (hx0 a)
    have hneg : C.ord (x a / x 0) (pr₁ (e₁ c)) < 0 := not_le.mp fun h => hPC₀ (by
      rw [← hpr₁ePC]
      exact hchart a ha _ ((ord_nonneg_iff hc1 hxa0).mp h))
    have hpos : 0 < C.ord (x 0 / x a) (pr₁ (e₁ c)) := by
      rw [show x 0 / x a = (x a / x 0)⁻¹ by rw [inv_div], Stacks.Chow.ord_inv_functionField hxa0]
      omega
    have hePCW' : e₁ c ∈ W' := ⟨hchart₁ _ ((ord_nonneg_iff hc1 hx0a).mp hpos.le),
      show pr₂ (e₁ c) ∈ C₀ by rw [hpr₂ePC]; exact hηC₀⟩
    obtain ⟨z₁, hz₁⟩ : ∃ z : Spec Γ(X, W'), hW'.fromSpec z = e₁ c :=
      ⟨hW'.primeIdealOf ⟨_, hePCW'⟩, hW'.fromSpec_primeIdealOf ⟨_, hePCW'⟩⟩
    obtain ⟨hz₁W', hz₁P⟩ := fromSpec_mem_and_primeIdealOf hW' z₁
    obtain ⟨hz₁c, π, hπ, hzπ⟩ := hheightW' z₁ (by rw [hz₁]; exact hcohe₁ c hc)
    have hc1' : coheight (pr₁ (hW'.fromSpec z₁)) = 1 := by rw [hz₁]; exact hc1
    have hpos' : 0 < C.ord (x 0 / x a) (pr₁ (hW'.fromSpec z₁)) := by rw [hz₁]; exact hpos
    obtain ⟨t₀, ht₀, ht₀x⟩ := (ord_pos_iff hc1' hx0a).mp hpos'
    -- `ξ_a⁻¹` vanishes along `c × C`
    have hX0 : ψ' (MvPolynomial.X 0) ∈ z₁.asIdeal := by
      rw [← hz₁P]
      refine (mem_primeIdealOf_iff hW' hz₁W' _).mpr ⟨pr₁.stalkMap _ t₀, ?_, ?_⟩
      · exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
          ((IsLocalRing.mem_maximalIdeal _).mp ht₀)
            (isUnit_of_map_unit (pr₁.stalkMap _).hom t₀ hu)
      · rw [algebraMap_stalkMap pr₁ ι₁ hι₁ _ t₀, ht₀x, hψ'def, MvPolynomial.eval₂Hom_X']
        change _ = X.germToFunctionField W' (pr₁.appLE C₁ W' inf_le_left (sec₁ 0))
        rw [hpr₁', hsec₁]
    have hπX : Ideal.span {π} = Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)} := by
      have h1 : MvPolynomial.X 0 ∈ Ideal.span {π} := by rw [← hzπ]; exact hX0
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
      have hu : IsUnit c :=
        ((prime_X0 (k := k)).irreducible.isUnit_or_isUnit hc).resolve_left hπ.not_isUnit
      exact Ideal.span_singleton_eq_span_singleton.mpr
        ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
    have hz₁inf : πW' z₁ = yInf k := PrimeSpectrum.ext (hzπ.trans hπX)
    have hz₁F : z₁ ∈ F' := (hmemF' z₁).mpr hz₁inf
    have hcoh : coheight z₁ = coheight (πW' z₁) := by
      rw [hz₁c, hz₁inf]; exact (hcohSpec _ hInf1).symm
    have hw1 := (chart_weight (ιT k) hC₀ hW' inf_le_right τC hτC_inj ψ' hψ'W z₁
      (by rw [hz₁]; exact hpr₂ePC) (f₀.residueDegree c) (by rw [hz₁]; exact hrd)).1
    have h3 : (Spec.map (CommRingCat.ofHom τC)).residueDegree
        (genericPoint (Spec Γ(C, C₀))) = N := hτN
    rw [h3] at hw1
    change (πT k).residueDegree (πW' z₁) * πW'.residueDegree z₁ = f₀.residueDegree c * N at hw1
    rw [hz₁inf, residueDegree_πT_yInf, one_mul] at hw1
    rw [hI', finsum_mem_congr rfl fun z _ => (show (if hW'.fromSpec z = e₁ c then
        (AlgebraicCycle.mapCoeff πW' coheight coheight z : ℤ) else 0) =
        if z = z₁ then (AlgebraicCycle.mapCoeff πW' coheight coheight z₁ : ℤ) else 0 by
          by_cases h : z = z₁
          · rw [h, ite_eq_left hz₁, ite_eq_left rfl]
          · rw [ite_eq_right h, ite_eq_right fun h' => h (hjW' (h'.trans hz₁.symm))]),
      finsum_mem_ite_eq_single, ite_eq_left hz₁F, AlgebraicCycle.mapCoeff, ite_eq_left hcoh]
    exact_mod_cast hw1
  have h₁ : ∑ c ∈ P₁.support, P₁ c * I' (e₁ c) = ∑ c ∈ P₁.support, P₁ c *
      (if c ∈ C₀ then 0 else (f₀.residueDegree c : ℤ) * N) :=
    Finset.sum_congr rfl fun c hc => by rw [hI₁ c hc]
  have h₂ : ∑ c ∈ P₁.support, P₁ c * I' (e₂ c) = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [hI₂ c hc, mul_zero]
  rw [h₁, h₂, hIΔ] at hInfB
  rw [hθnorm]
  linear_combination hInfB

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- The degree of `U i` in the first variable `ξ_a`. -/
private theorem degreeOf_zero_eq_of_isReducedNormRepresentation
    {k : Type u} [Field k] {C X : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsLocallyNoetherian C] [GeometricallyIntegral (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsCurve k (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial
        ((C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of k)) (C ↘ Spec (.of k)))
    [IsIntegral X] [IsLocallyNoetherian X] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * ((C ↘ Spec (.of k)).residueDegree Q : ℤ) = 1)
    {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (ι₁ ι₂ : C.functionField →+* X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the divisor `N P₁` on `C`, and the generic basis `x` of `H⁰(C, 𝒪(N P₁))` giving `φ_{NP₁}`
    (N : ℕ) {n : ℕ} (E : C → ℤ) (hE : ∀ z, E z = ((N : ℤ) • P₁) z)
    (x : Fin (n + 1) → C.functionField) (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z)
    (hxli : LinearIndependent k x)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = C ↘ Spec (.of k))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- (N): the basis `x` is generic
    (hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    -- the very ample divisor `B` on `X`, and the basis `f` of `H⁰(X, 𝒪(B))` giving `φ_B`
    (s : ℕ)
    (B : X → ℤ) (hB : ∀ w, B w =
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (f : Fin (m + 1) → X.functionField) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hBG1 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w',
      0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w, 0 < X.ord (f i) w + B w →
      0 ≤ X.ord (ι₁ (x a / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b / x 0)) w)
    {K : Type u} [Field K] [instRK : Algebra (MvPolynomial (Fin 2) k) K]
    [instFrac : IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [instRL : Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [instTower : IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => f i / f 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    (U i).degreeOf 0 = N * s := by
  classical
  obtain ⟨hFD, hsumT⟩ :=
    exists_finsum_horizontal_eq_of_isReducedNormRepresentation hkC hX hkX Δ hΔ₁ hΔ₂ P₁ hP₁cl hP₁
      heΔ ι₁ ι₂ hι₁ hι₂ N E hE x hxE hxli φNP hφNP hφNPx hNG1 s B hB f hf hD a b ha hb
      hBG1 hRL₀ hRLa hRLb hU i hi
  have hInf :=
    exists_ordAt_inf_norm_eq_of_isReducedNormRepresentation (K := K) hkC hX hkX Δ hΔ₁ hΔ₂ P₁ hP₁cl
      hP₁ heΔ ι₁ ι₂ hι₁ hι₂ N E hE x hxE hxli φNP hφNP hφNPx hNG1 s B hB f hf hD a b ha hb
      hBG1 hBG2 hRL₀ hRLa hRLb i hi
  have hηne : f i / f 0 ≠ 0 := div_ne_zero (hf i) (hf 0)
  have hUne0 : U i ≠ 0 := hU.num_ne_zero hηne
  have hfiN : Algebra.norm K (f i) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hf i)
  obtain ⟨-, hsumN⟩ := finsum_add_ordAt_inf_eq_zero (k := k) (K := K) hfiN
  obtain ⟨-, hdeg⟩ := degreeOf_eq_finsum (k := k) (K := K) hUne0
  -- the fibres `c × C` contribute `[κ(c) : k] N` on the chart or at infinity, and `P₁` has
  -- degree one
  have hP₁' : ∑ c ∈ P₁.support, P₁ c * ((C ↘ Spec (.of k)).residueDegree c : ℤ) = 1 := by
    rw [← hP₁]
    refine (finsum_eq_sum_of_support_subset _ fun c hc => ?_).symm
    exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hsplit : ∀ A : C → Prop, ∀ q : C → ℤ,
      ∑ c ∈ P₁.support, P₁ c * (if A c then q c else 0) +
        ∑ c ∈ P₁.support, P₁ c * (if A c then 0 else q c) = ∑ c ∈ P₁.support, P₁ c * q c :=
    fun A q => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
  have hfib := hsplit (fun c => c ∈ φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n
      (Spec (.of k)) ⁻¹ᵁ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X 0)))
    (fun c => ((C ↘ Spec (.of k)).residueDegree c : ℤ) * N)
  beta_reduce at hfib
  have hN : ∑ c ∈ P₁.support, P₁ c * (((C ↘ Spec (.of k)).residueDegree c : ℤ) * N) = N := by
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hP₁', one_mul]
  have hZ : ((U i).degreeOf 0 : ℤ) = N * s := by
    linear_combination -hdeg + hsumT + hsumN - hInf + (s + 1 : ℤ) * hfib + (s + 1 : ℤ) * hN
  exact_mod_cast hZ

/-! ### Points of residue degree one, fraction fields of the plane, and transcendence -/

section Bridge

open Faltings.BombieriSiegel Faltings.BombieriVojta

namespace BombieriRoth

/-- The residue field of a field at its prime is the field itself. -/
public theorem surjective_algebraMap_residueField {K : Type*} [Field K] (p : Ideal K)
    [p.IsPrime] : Function.Surjective (algebraMap K p.ResidueField) := by
  have : p.IsMaximal := by rw [Ideal.eq_bot_of_prime p]; exact Ideal.bot_isMaximal
  exact Ideal.algebraMap_residueField_surjective p

/-- **A point of residue degree one is a rational point**: it is the image of a section of the
structure morphism. -/
public theorem exists_section_of_residueDegree_eq_one {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (P : C) (hP : f.residueDegree P = 1) :
    ∃ σ : Spec (.of k) ⟶ C, σ ≫ f = 𝟙 _ ∧ Set.range σ.base = {P} := by
  -- `κ(f P) → κ(P)` is onto
  have hφ : Function.Surjective (f.residueFieldMap P).hom := by
    let := (f.residueFieldMap P).hom.toAlgebra
    have h : Module.finrank ((Spec (.of k)).residueField (f P)) (C.residueField P) = 1 := hP
    have h2 := Subalgebra.bot_eq_top_of_finrank_eq_one h
    intro z
    have hz : z ∈ (⊥ : Subalgebra ((Spec (.of k)).residueField (f P)) (C.residueField P)) := by
      rw [h2]; trivial
    obtain ⟨w, hw⟩ := Algebra.mem_bot.mp hz
    exact ⟨w, hw⟩
  -- so is `k → κ(P)`
  have hχ : Function.Surjective (Spec.preimage (C.fromSpecResidueField P ≫ f)).hom := by
    have := (f P).isPrime
    have he : C.fromSpecResidueField P ≫ f = Spec.map (CommRingCat.ofHom
        (algebraMap k (f P).asIdeal.ResidueField) ≫ (Scheme.Spec.residueFieldIso _ (f P)).inv ≫
          f.residueFieldMap P) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Spec.map_comp,
        Spec.map_comp, Category.assoc]
    rw [he, Spec.preimage_map]
    have h1 := surjective_algebraMap_residueField (f P).asIdeal
    exact hφ.comp ((ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso _ (f P)).inv).2.comp h1)
  let := (Spec.preimage (C.fromSpecResidueField P ≫ f)).hom.toAlgebra
  have hrank : Module.rank k (C.residueField P) = 1 := by
    rw [← Subalgebra.bot_eq_top_iff_rank_eq_one, Algebra.eq_top_iff]
    intro z
    obtain ⟨w, hw⟩ := hχ z
    exact Algebra.mem_bot.mpr ⟨w, hw⟩
  obtain ⟨σ, hσ, hσP⟩ := (Faltings.FunctionField.bijOn_rank_residueField_eq_one k f).surjOn hrank
  refine ⟨σ, hσ, ?_⟩
  rw [← hσP]
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact congrArg σ.base (Subsingleton.elim w _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-- **`k⟮t, u⟯` is the fraction field of `k[X₀, X₁]`** when `X₀ ↦ t`, `X₁ ↦ u` is injective. -/
public theorem isFractionRing_adjoin_pair {k L : Type*} [Field k] [Field L] [Algebra k L]
    (t u : L) [Algebra (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k {t, u})]
    (hR : ∀ p : MvPolynomial (Fin 2) k,
      (algebraMap (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k {t, u}) p : L) =
        MvPolynomial.aeval ![t, u] p)
    (hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k {t, u}))) :
    IsFractionRing (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k {t, u}) := by
  have : FaithfulSMul (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k {t, u}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hset : ({t, u} : Set L) = Set.range ![t, u] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
  rw [hset, Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hs
  refine ⟨p, q, Subtype.ext ?_⟩
  rw [hz, IntermediateField.coe_div, hR, hR]
  rfl

end BombieriRoth

section Transcendence

/-- **The affine coordinates of `φ_D` are transcendental.** Let `D` be a divisor of degree
`N ≥ 2g + 1` on closed points of a curve of genus `g ≥ 2`, and `x` a basis of `L(D)`
satisfying (G1). For `a ≠ 0`, `k(C)` is finite over `k⟮x_a / x₀⟯`, of degree `N`, and has
transcendence degree one, so `x_a / x₀` is transcendental over `k`. -/
public theorem BombieriRoth.transcendental_div (k : Type u) [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ AlgebraicGeometry.genus f)
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C)) (N : ℕ)
    (hN : 2 * AlgebraicGeometry.genus f + 1 ≤ N)
    (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N) {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x) {a : Fin (n + 1)} (ha : a ≠ 0) :
    letI := functionFieldAlgebra k f
    Transcendental k (x a / x 0) := by
  let := functionFieldAlgebra k f
  have := BombieriSiegel.finrank_adjoin_div_eq k f hg D hDcl N hN hD x hli hspan hG1 a ha
  have : FiniteDimensional (IntermediateField.adjoin k {x a / x 0}) C.functionField :=
    .of_finrank_pos (by omega)
  exact transcendental_of_finiteDimensional
    (by simp [AlgebraicGeometry.trdeg_functionField_eq_one k f])

end Transcendence

end Bridge

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- The degrees of `U i` in both variables, in the affine-chart setting of
`degreeOf_zero_eq_of_isReducedNormRepresentation`: the second degree follows from the first by
exchanging the two factors of `X` and the two variables of `k[X₀, X₁]`. -/
private theorem degreeOf_eq_of_isReducedNormRepresentation_proj
    {k : Type u} [Field k] {C X : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsLocallyNoetherian C] [GeometricallyIntegral (C ↘ Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [IsCurve k (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial
        ((C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of k)) (C ↘ Spec (.of k)))
    [IsIntegral X] [IsLocallyNoetherian X] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ C ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * ((C ↘ Spec (.of k)).residueDegree Q : ℤ) = 1)
    {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (ι₁ ι₂ : C.functionField →+* X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the divisor `N P₁` on `C`, and the generic basis `x` of `H⁰(C, 𝒪(N P₁))` giving `φ_{NP₁}`
    (N : ℕ) {n : ℕ} (E : C → ℤ) (hE : ∀ z, E z = ((N : ℤ) • P₁) z)
    (x : Fin (n + 1) → C.functionField) (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z)
    (hxli : LinearIndependent k x)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = C ↘ Spec (.of k))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- (N): the basis `x` is generic
    (hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    -- the very ample divisor `B` on `X`, and the basis `f` of `H⁰(X, 𝒪(B))` giving `φ_B`
    (s : ℕ)
    (B : X → ℤ) (hB : ∀ w, B w =
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (f : Fin (m + 1) → X.functionField) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i w, 0 ≤ X.ord (f i) w + B w)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hBG1 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w',
      0 < X.ord (f i) w + B w → 0 < X.ord (f 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ i : Fin (m + 1), i ≠ 0 → ∀ w, 0 < X.ord (f i) w + B w →
      0 ≤ X.ord (ι₁ (x a / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b / x 0)) w)
    {K : Type u} [Field K] [instRK : Algebra (MvPolynomial (Fin 2) k) K]
    [instFrac : IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [instRL : Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [instTower : IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => f i / f 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    (U i).degreeOf 0 = N * s ∧ (U i).degreeOf 1 = N * s := by
  refine ⟨degreeOf_zero_eq_of_isReducedNormRepresentation hkC hX hkX Δ hΔ₁ hΔ₂ P₁ hP₁cl hP₁
    heΔ ι₁ ι₂ hι₁ hι₂ N E hE x hxE hxli φNP hφNP hφNPx hNG1 s B hB f hf hD a b ha hb
    hBG1 hBG2 hRL₀ hRLa hRLb hU i hi, ?_⟩
  -- the second degree: exchange the two factors and the two variables
  let σ : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
    MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)
  have hσσ : ∀ r, σ (σ r) = r := fun r => by
    change MvPolynomial.rename _ (MvPolynomial.rename _ r) = r
    rw [MvPolynomial.rename_rename, show (⇑(Equiv.swap (0 : Fin 2) 1) ∘
      ⇑(Equiv.swap (0 : Fin 2) 1)) = id from funext (Equiv.swap_apply_self 0 1),
      MvPolynomial.rename_id_apply]
  let φK : MvPolynomial (Fin 2) k →+* K := algebraMap (MvPolynomial (Fin 2) k) K
  let φL : MvPolynomial (Fin 2) k →+* X.functionField :=
    algebraMap (MvPolynomial (Fin 2) k) X.functionField
  have hφK : ∀ r, φK r = algebraMap (MvPolynomial (Fin 2) k) K r := fun _ => rfl
  have hφL : ∀ r, φL r = algebraMap (MvPolynomial (Fin 2) k) X.functionField r := fun _ => rfl
  let θK : MvPolynomial (Fin 2) k →+* K := φK.comp σ.toRingEquiv.toRingHom
  let θL : MvPolynomial (Fin 2) k →+* X.functionField := φL.comp σ.toRingEquiv.toRingHom
  have hK : ∀ r, @algebraMap (MvPolynomial (Fin 2) k) K _ _ θK.toAlgebra r = φK (σ r) :=
    fun _ => rfl
  have hL : ∀ r, @algebraMap (MvPolynomial (Fin 2) k) X.functionField _ _ θL.toAlgebra r =
      φL (σ r) := fun _ => rfl
  have fracK : @IsFractionRing (MvPolynomial (Fin 2) k) _ K _ θK.toAlgebra :=
    @IsFractionRing.of_ringEquiv_left _ _ _ _ K _ θK.toAlgebra σ.toRingEquiv _
      (fun _ => rfl) _
  have towerK : @IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField
      (@Algebra.toSMul _ _ _ _ θK.toAlgebra) _ (@Algebra.toSMul _ _ _ _ θL.toAlgebra) := by
    have htow : ∀ r, φL r = algebraMap K X.functionField (φK r) := fun r =>
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) k) K X.functionField r
    let := θK.toAlgebra
    let := θL.toAlgebra
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [hL, hK]
    exact htow (σ r)
  have hU' : @IsReducedNormRepresentation (MvPolynomial (Fin 2) k) K X.functionField _ _ _
      θK.toAlgebra _ m (fun i => f i / f 0) (fun i => σ (U i)) (fun i => σ (V i)) := by
    refine @IsReducedNormRepresentation.mk _ _ _ _ _ _ θK.toAlgebra _ _ _ _ _
      (fun i => ?_) (fun i => ?_) (fun i => ?_) ?_ ?_
    · exact (map_ne_zero_iff _ σ.injective).mpr (hU.ne_zero i)
    · intro d hdU hdV
      have h1 : σ d ∣ U i := by simpa [hσσ] using map_dvd σ hdU
      have h2 : σ d ∣ V i := by simpa [hσσ] using map_dvd σ hdV
      have := hU.isRelPrime i h1 h2
      simpa [hσσ] using this.map σ
    · rw [hK, hK, hσσ, hσσ]
      exact hU.algebraNorm_eq_div i
    · simp [hU.num_zero]
    · simp [hU.den_zero]
  have key := degreeOf_zero_eq_of_isReducedNormRepresentation (pr₁ := pr₂) (pr₂ := pr₁)
    (instRK := θK.toAlgebra) (instFrac := fracK) (instRL := θL.toAlgebra) (instTower := towerK)
    hkC hX.flip (fun c => by rw [hkX c, hX.w]) Δ hΔ₂ hΔ₁ P₁ hP₁cl hP₁ heΔ ι₂ ι₁ hι₂ hι₁ N E hE x
    hxE hxli φNP hφNP hφNPx hNG1 s B (fun w => by rw [hB w]; ring) f hf hD b a hb ha
    (fun i hi w w' h h' => by
      obtain ⟨r, hr, h1, h2⟩ := hBG1 i hi w w' h h'
      exact ⟨r, by rwa [Set.pair_comm], h1, h2⟩)
    (fun i hi w h => (hBG2 i hi w h).symm)
    (fun c => by rw [hL, hφL]; simpa [σ] using hRL₀ c)
    (by rw [hL, hφL]; simpa [σ] using hRLb) (by rw [hL, hφL]; simpa [σ] using hRLa) hU' i hi
  have hdeg := MvPolynomial.degreeOf_rename_of_injective (p := U i)
    (Equiv.swap (0 : Fin 2) 1).injective 1
  rw [Equiv.swap_apply_right] at hdeg
  rwa [← hdeg]

section Main

open BombieriSiegel BombieriVojta

set_option linter.unusedVariables false in
open Classical in
/-- **The degrees of the numerators `Uᵢ`** (Bombieri). In the setting of
`Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`, let `1 ≤ a, b ≤ n`,
let `R = k[X₀, X₁]` map to `k⟮ξ_a, ξ'_b⟯` by `X₀ ↦ ξ_a`, `X₁ ↦ ξ'_b`, and let `(U, V)` be a
family of reduced representations of the norms of `ηᵢ = y i / y 0` from `k(X)` to
`k⟮ξ_a, ξ'_b⟯`. Then for `i ≠ 0` the polynomial `U i` has degree `N * sB` in `X₀` and in
`X₁`. -/
@[faltings "lem_bvr_norm_eta"]
public theorem degreeOf_num_eq_of_isReducedNormRepresentation (k : Type u) [Field k]
    [CharZero k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ AlgebraicGeometry.genus f) (P₁ : C →₀ ℤ)
    (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ)
    (hN : 2 * AlgebraicGeometry.genus f + 1 ≤ N)
    {n : ℕ} (hn : n = N - AlgebraicGeometry.genus f) (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    -- (N): the basis `x` is generic
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (hG3 : SatisfiesG3 k f x)
    -- the product `X = C ×_k C` with its projections and diagonal
    {X : Scheme.{u}} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) [IsIntegral X]
    [IsLocallyNoetherian X] (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k C.functionField] (hkC : ‹Algebra k C.functionField› = functionFieldAlgebra k f)
    [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB) {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (B : X → ℤ) (hB : ∀ w : X, B w =
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hD : ∀ i (w : X), 0 ≤ X.ord (y i) w + B w)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : X.functionField, (∀ w : X, 0 ≤ X.ord h w + B w) →
      h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ w : X, Order.coheight w = 1 → ∃ i, X.ord (y i) w + B w = 0)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k))) [IsClosedImmersion φB]
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of X.functionField)).inv.hom))
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w' : X,
      0 < X.ord (y i) w + B w → 0 < X.ord (y 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i j : Fin (m + 1),
      i.val = 1 → j.val = 2 → ∀ w w' : X, 0 < X.ord (y i) w + B w →
      0 < X.ord (y j) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w : X,
      0 < X.ord (y i) w + B w →
      0 ≤ X.ord (ι₁ (x a' / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b' / x 0)) w)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ q : X,
        (∀ r ∈ 𝔪,
          (∀ w : X, w ⤳ q → Order.coheight w = 1 → 0 ≤ X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) ∧
          ∃ w : X, w ⤳ q ∧ Order.coheight w = 1 ∧ 0 < X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) →
        ∀ w : X, w ⤳ q → Order.coheight w = 1 → X.ord (y i) w + B w = 0)
    (a b : Fin n)
    -- the ring `R = k[ξ_a, ξ'_b]` and a family of reduced representations of the `Norm ηᵢ`
    [Algebra (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})]
    (hR : ∀ p : MvPolynomial (Fin 2) k,
      (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) p :
          X.functionField) =
        MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] p)
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hUV : IsReducedNormRepresentation
      (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (MvPolynomial (Fin 2) k) (fun i => y i / y 0) U V)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    (U i).degreeOf 0 = N * sB ∧ (U i).degreeOf 1 = N * sB := by
  subst hkC
  let : Algebra k C.functionField := functionFieldAlgebra k f
  have hkC' : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := inferInstanceAs (GeometricallyIntegral f)
  have : IsProper f := (instIsProperVarietyOfIsProjectiveVariety k f).toIsProper
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsCurve k (C ↘ Spec (.of k)) := inferInstanceAs (IsCurve k f)
  have : Smooth (C ↘ Spec (.of k)) := inferInstanceAs (Smooth f)
  -- the divisor `N P₁` and condition (G1) in terms of orders of vanishing
  have hNcl := isClosed_of_mem_support_smul hP₁cl (N : ℤ)
  let E : C → ℤ := fun z => ((N : ℤ) • P₁) z
  have hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z := fun j z =>
    ord_add_nonneg_of_span_eq f hNcl hli hspan j z
  have hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0 := by
    intro a ha z hz
    have hcl := Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f
      fun h => FunctionField.coheight_genericPoint_ne_one C (h ▸ hz)
    have h := hG1 a ha z hcl
    have h0 := hxE 0 z
    have ha' := hxE a z
    simp only [E] at h0 ha' ⊢
    omega
  -- `R → k⟮ξ_a, ξ'_b⟯` is injective: `ξ_a` and `ξ'_b` are transcendental
  have hdeg := finsum_smul_mul_residueDegree f hP₁ (N : ℤ)
  have hTa : Transcendental k (x a.succ / x 0) :=
    BombieriRoth.transcendental_div k f hg _ hNcl N hN hdeg x hli hspan hG1 (Fin.succ_ne_zero a)
  have hTb : Transcendental k (x b.succ / x 0) :=
    BombieriRoth.transcendental_div k f hg _ hNcl N hN hdeg x hli hspan hG1 (Fin.succ_ne_zero b)
  have hv : ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] =
      ![ι₁ (x a.succ / x 0), ι₂ (x b.succ / x 0)] := by
    rw [map_div₀, map_div₀]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})) := by
    intro p q hpq
    apply injective_aeval_of_transcendental f hX hkC' ι₁ ι₂ hι₁ hι₂ hTa hTb
    have h := congrArg Subtype.val hpq
    rwa [hR, hR, hv] at h
  -- the fraction field `k⟮ξ_a, ξ'_b⟯` of `R` inside `k(X)`
  let : Algebra (MvPolynomial (Fin 2) k) X.functionField :=
    ((algebraMap
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
        X.functionField).comp
      (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})))
      |>.toAlgebra
  have : IsScalarTower (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) :=
    BombieriRoth.isFractionRing_adjoin_pair _ _ hR hinj
  have hRL : ∀ p, algebraMap (MvPolynomial (Fin 2) k) X.functionField p =
      MvPolynomial.aeval ![ι₁ (x a.succ / x 0), ι₂ (x b.succ / x 0)] p := fun p =>
    (hR p).trans (by rw [hv])
  have hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField
      (MvPolynomial.C c) = algebraMap k X.functionField c := fun c => by
    rw [hRL, MvPolynomial.aeval_C]
  have hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a.succ / x 0) := by
    rw [hRL, MvPolynomial.aeval_X]; rfl
  have hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b.succ / x 0) := by
    rw [hRL, MvPolynomial.aeval_X]; rfl
  exact degreeOf_eq_of_isReducedNormRepresentation_proj hkC' hX hkX Δ hΔ₁ hΔ₂ P₁ hP₁cl hP₁ heΔ
    ι₁.toRingHom ι₂.toRingHom hι₁ hι₂ N E (fun _ => rfl) x hxE hli φNP hφNP hφNPx hNG1 sB B hB y hy
    hD a.succ b.succ (Fin.succ_ne_zero a) (Fin.succ_ne_zero b)
    (hBG1 a.succ b.succ (Fin.succ_ne_zero a) (Fin.succ_ne_zero b))
    (hBG2 a.succ b.succ (Fin.succ_ne_zero a) (Fin.succ_ne_zero b)) hRL₀ hRLa hRLb hUV i hi

end Main

end Faltings
