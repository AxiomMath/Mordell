module

public import Mordell.BombieriVojta.Height.Basic
public import Mordell.BombieriVojta.Taylor.MonomialBound
public import Mordell.BombieriVojta.Taylor.SeparatedVariables
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Weil.Representative
public import Mordell.BombieriVojta.TripleFunction.FirstCoefficient
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.BombieriVojta.Taylor.Expansion
public import Mordell.Height.Machine.IsomorphicPullbacks
public import Mordell.BombieriVojta.Height.LocalMinMax
public import Mordell.Polynomial.BihomogeneousSupport
public import Mordell.AlgebraicGeometry.ProjectiveSpace.ChartRatio

/-!
# Bombieri's Lemma 4: a lower bound for the height `h_V`

Let `(C, P)` be a curve over a number field `K` with a divisor `P` of degree one, of genus `g`.
Let `N ≥ 2g + 1` and let `φ_{NP} : C → ℙⁿ` be the embedding by a basis `x` of `H⁰(C, 𝒪(NP))`;
let `s ≥ 1` and let `φ_B : C × C → ℙᵐ` be the embedding by a basis `y` of
`H⁰(C × C, 𝒪(B))`, `B = s P × C + s C × P - Δ'`; let `ψ = φ_{NP} × φ_{NP}`. Let `d ≥ 1` and let
`δ₁ = (d₁ + s d) / N`, `δ₂ = (d₂ + s d) / N` be positive integers,
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`, and `s` a global section of `𝒪(V)` with a representative
`F = (F_i)`. For a `K`-point `(z, w)` of `C × C`, uniformizers `ς, ς'` at `z, w` and a pair
`(i₁*, i₂*)` admissible for `s` at `(z, w)`,
`h_V(z, w) ≥ -h(F) - n log((δ₁ + n)(δ₂ + n))`
`  - ∑_v max_{i_λ} ∑_λ max_ν log |∂_{i_λ} ξ_{ν j_v}(z)|_v`
`  - ∑_v max_{i'_λ} ∑_λ max_ν log |∂'_{i'_λ} ξ_{ν j'_v}(w)|_v`
`  - (δ₁ + δ₂ + i₁* + i₂*)`,
with `log 0 = -∞`, where `v` runs over the places of `K`, the maxima over all partitions of `i₁*`
and of `i₂*`, and `j_v`, `j'_v` are indices with `|ξ_{ν j_v}(z)|_v ≤ 1` and `|ξ_{ν j'_v}(w)|_v ≤ 1`
for every `ν`. Here `ξ_{νj} = x_ν / x_j` and `∂_i ξ(z)` is the coefficient of `ς ^ i` in the
expansion of `ξ` at `z`.

The proof follows Bombieri. Let `(i°, j°, j'°)` be the triple witnessing admissibility and
`b = ∂_{i₁*} ∂'_{i₂*} G°(p) ≠ 0`. With `D_{ijj'} = ∂_{i₁*} ∂'_{i₂*} F_i(ξ_j, ξ'_{j'})(p)`, the
value formula `Faltings.BombieriVojta.taylorCoeff₂_eq_mul_taylorCoeff₂_eval₂` gives
`b = (y_{i°}/y_i)^d (x_j/x_{j°})^{δ₁} (x'_{j'}/x'_{j'°})^{δ₂} D_{ijj'}`, so by the product
formula the local expression of `h_V` becomes `-∑_v max_i min_{j,j'} log |D_{ijj'}|_v`.
Expanding `F_i` into monomials and applying the Leibniz rule for functions of one variable each,
`D_{ijj'} = ∑_α f_{iα} ∂_{i₁*}(ξ_j^{α₁})(z) ∂'_{i₂*}(ξ'^{α₂}_{j'})(w)`; bounding the at most
`((δ₁ + 1)(δ₂ + 1))ⁿ` terms at each place, and the Taylor coefficients of the monomials at the
indices `j_v, j'_v`, and summing over the places gives the bound.

The local ring of `C ×_K C` at `p` is regular of dimension two with maximal ideal
`(ς ∘ pr₁, ς' ∘ pr₂)`: the regularity is smoothness at a rational point, the maximal ideal is
computed through `AlgebraicGeometry.SpecToEquivOfLocalRing` on the quotient by
`(ς ∘ pr₁, ς' ∘ pr₂)`, and the dimension is detected by the two evaluations
`𝒪_{C ×_K C, p} → 𝒪_{C,z}` and `𝒪_{C ×_K C, p} → 𝒪_{C,w}` that kill one parameter each. The
sums over the places are first computed in `ℝ`, where every local term is shown to be finite and
finitely supported, and then read in `EReal`.

## Main results

* `Faltings.BombieriVojta.vojtaHeight_ge_of_isAdmissiblePair`: Bombieri's Lemma 4.

## Implementation notes

* The curve is `X : Faltings.CurveWithDegreeOneDivisor K`, the source's curve after base change
  to `K`; the point `(z, w)` is a `K`-point `p` of `C ×_K C` (a section of
  `pullback.fst X.f X.f ≫ X.f`), with `z = p ≫ pr₁`, `w = p ≫ pr₂`, and the local parameters of
  `Faltings.BombieriVojta.IsAdmissiblePair` are `ς ∘ pr₁`, `ς' ∘ pr₂`.
* `h_V` is `Faltings.CurveWithDegreeOneDivisor.vojtaHeight`, whose heights `h_{NP}`, `h_B` are
  `Faltings.ProjectiveEmbedding.height` of `φ_{NP}`, `φ_B`. These embeddings are pinned as the
  morphisms `Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of a generating basis of the
  global sections of an invertible sheaf of class `N • [𝒪(P)]`, resp.
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)`.
* The function `ξ_{νj} = x_ν / x_j` near `z` is the pull-back along `φ_{NP}` of the regular
  function `T_ν / T_j` on the chart `D₊(T_j)` of the integral model of `ℙⁿ`
  (`Proj.awayToSection` of the degree-zero fraction), as a germ at `z` (zero off the chart).
  `Faltings.BombieriVojta.taylorCoeff` gives `∂_i ξ_{νj}(z)`. `h(F)` is the absolute height of
  the vector of all coefficients of all `F_i`.
* The normalised `log |a|_v` is `(n_v / [K : ℚ]) log ‖a‖_v` (with `n_v = mult v` at an infinite
  place and `1` at a finite place) for `a ≠ 0`, and `⊥ = -∞` for `a = 0`; the inequality is
  therefore stated in `EReal`. A place is a term of `InfinitePlace K ⊕ FinitePlace K`, and the
  maxima over partitions (`Nat.Partition`) and indices are `Finset.sup`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, Lemma 4, p. 625
-/

open Faltings (chartVal_eq_of_comp chartVal_self iota_mem_iff mem_asHomogeneousIdeal_iff_eval_chartVal)
open Faltings.BombieriVojta (const_comp const_eq ev_const exists_stalk_hom ext_of_germ ne_zero_of_maximalIdeal_eq stalkClosedPointTo_comp_over_germ stalkCongr_const)

open Faltings (chartVal coordPoint exists_mem_basicOpen toDualEquiv_apply_apply top_le_preimage_of_mem)
open Faltings.BombieriVojta (const ev_eq_zero_of_mem stalkClosedPointTo_fromSpecStalk_eq stalkClosedPointTo_germ_of_eq)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing _root_.NumberField Module
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings.BombieriVojta.HeightLowerBound

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

section Geometry

variable {K : Type u} [Field K]

/-- At a `K`-rational point the residue field is separable over `K`. -/
public theorem isSeparable_residueField {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))
    (q : Spec (.of K) ⟶ Y) (hq : q ≫ f = 𝟙 _) :
    letI : Algebra K (Y.residueField (q (closedPoint K))) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ Y.Γevaluation (q (closedPoint K))).hom.toAlgebra
    Algebra.IsSeparableExtension K (Y.residueField (q (closedPoint K))) := by
  let : Algebra K (Y.residueField (q (closedPoint K))) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ Y.Γevaluation (q (closedPoint K))).hom.toAlgebra
  have hy := isRationalPoint_base_of_comp_eq_id f hq (closedPoint K)
  have key : Spec.preimage (Y.fromSpecResidueField (q (closedPoint K)) ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ (Y.fromSpecResidueField (q (closedPoint K)) ≫ f).appTop ≫
        (Scheme.ΓSpecIso _).hom := by
    conv_rhs => rw [← Spec.map_preimage (Y.fromSpecResidueField (q (closedPoint K)) ≫ f)]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpecResidueField_appTop] at key
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      Y.Γevaluation (q (closedPoint K))) := by
    rw [← key]; exact hy
  have hbij : Function.Bijective (algebraMap K (Y.residueField (q (closedPoint K)))) :=
    ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ Y.Γevaluation (q (closedPoint K)))
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp
    (Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij))

/-- The local ring at a `K`-rational point of a smooth `K`-scheme is regular. -/
public theorem isRegularLocalRing_stalk {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [Smooth f]
    (q : Spec (.of K) ⟶ Y) (hq : q ≫ f = 𝟙 _) :
    IsRegularLocalRing (Y.presheaf.stalk (q (closedPoint K))) :=
  (smoothAt_iff_isRegularLocalRing_stalk f _ (isSeparable_residueField f q hq)).mp
    (InfinitesimalLifting.smoothAt_of_smooth f _)

/-- At a `K`-point `q` of a `K`-scheme, a germ minus the constant of its value at `q` lies in the
maximal ideal of the stalk. -/
public theorem sub_const_mem_maximalIdeal {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    (q : Spec (.of K) ⟶ Y) (hq : q ≫ (Y ↘ Spec (.of K)) = 𝟙 _)
    (g : Y.presheaf.stalk (q (closedPoint K))) :
    g - const (K := K) _ ((Scheme.stalkClosedPointTo q).hom g) ∈ maximalIdeal _ := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := (hu.map (Scheme.stalkClosedPointTo q).hom)
  rw [map_sub, ev_const q hq, sub_self] at this
  exact not_isUnit_zero this

/-- Two local homomorphisms out of a stalk inducing the same morphism from `Spec R` agree. -/
public theorem stalk_hom_ext {Y : Scheme.{u}} {x : Y} {R : CommRingCat.{u}} [IsLocalRing R]
    (ψ₁ ψ₂ : Y.presheaf.stalk x ⟶ R) [IsLocalHom ψ₁.hom] [IsLocalHom ψ₂.hom]
    (h : Spec.map ψ₁ ≫ Y.fromSpecStalk x = Spec.map ψ₂ ≫ Y.fromSpecStalk x) : ψ₁ = ψ₂ := by
  have := (SpecToEquivOfLocalRing Y R).symm.injective
    (a₁ := ⟨x, ψ₁, inferInstance⟩) (a₂ := ⟨x, ψ₂, inferInstance⟩) h
  obtain ⟨_, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  simpa using h2

/-- The quotient map of a local ring by an ideal inside the maximal ideal is local. -/
public theorem isLocalHom_quotient_mk {O : Type*} [CommRing O] [IsLocalRing O] {I : Ideal O}
    (hI : I ≤ maximalIdeal O) : IsLocalHom (Ideal.Quotient.mk I) := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨g', hg'⟩ := hf.exists_right_inv
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hg'
  have h2 : IsUnit (f * g) := by
    by_contra hu
    have h3 : f * g - (f * g - 1) ∈ maximalIdeal O :=
      sub_mem ((mem_maximalIdeal _).mpr hu) (hI hg')
    rw [sub_sub_cancel] at h3
    exact (mem_maximalIdeal _).mp h3 isUnit_one
  exact isUnit_of_mul_isUnit_left h2

/-- `f ↦ π (c (ev f))` is local when `ev` is local onto a field and the target is nontrivial. -/
public theorem isLocalHom_comp_comp {O Q : Type*} [CommRing O] [CommRing Q] [Nontrivial Q]
    (π : O →+* Q) (c : K →+* O) (ev : O →+* K) [IsLocalHom ev] :
    IsLocalHom (π.comp (c.comp ev)) := by
  refine ⟨fun f hf => ?_⟩
  by_cases h0 : ev f = 0
  · exfalso
    simp [h0] at hf
  · exact IsLocalHom.map_nonunit (f := ev) f (isUnit_iff_ne_zero.mpr h0)

/-- At a `K`-point `p = (z, w)` of `C ×_K D`, the maximal ideal of the local ring is generated by
the pull-backs of generators of the maximal ideals at `z` and at `w`. -/
public theorem maximalIdeal_stalk_pullback {C D : Scheme.{u}} [C.Over (Spec (.of K))]
    [D.Over (Spec (.of K))] {X : Scheme.{u}} [X.Over (Spec (.of K))] {pr₁ : X ⟶ C} {pr₂ : X ⟶ D}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (D ↘ Spec (.of K)))
    (hXo : pr₁ ≫ (C ↘ Spec (.of K)) = X ↘ Spec (.of K))
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    {ς : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K))}
    {ς' : D.presheaf.stalk ((p ≫ pr₂) (closedPoint K))}
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'}) :
    maximalIdeal (X.presheaf.stalk (p (closedPoint K))) =
      Ideal.span {pr₁.stalkMap (p (closedPoint K)) ς, pr₂.stalkMap (p (closedPoint K)) ς'} := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal (X.presheaf.stalk
        (p (closedPoint K))), I = Ideal.span
      {pr₁.stalkMap (p (closedPoint K)) ς,
        pr₂.stalkMap (p (closedPoint K)) ς'} :=
    ⟨_, rfl⟩
  rw [← hI]
  have hIm : I ≤ maximalIdeal _ := by
    rw [hI, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact map_nonunit (pr₁.stalkMap
        (p (closedPoint K))).hom ς (hς ▸ Ideal.subset_span rfl)
    · exact map_nonunit (pr₂.stalkMap
        (p (closedPoint K))).hom ς' (hς' ▸ Ideal.subset_span rfl)
  refine le_antisymm ?_ hIm
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hIm
  have : Nontrivial (_ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (_ ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let c : K →+* _ := const (p (closedPoint K))
  let ev := (Scheme.stalkClosedPointTo p).hom
  let π : _ ⟶ CommRingCat.of (_ ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let ψ : _ ⟶ CommRingCat.of (_ ⧸ I) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk I).comp (c.comp ev))
  have : IsLocalHom π.hom := isLocalHom_quotient_mk hIm
  have : IsLocalHom ψ.hom := isLocalHom_comp_comp _ _ _
  have hzC : (p ≫ pr₁) ≫ (C ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, hXo]; exact comp_over_eq_id p
  have hzD : (p ≫ pr₂) ≫ (D ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, ← hX.w, hXo]; exact comp_over_eq_id p
  have key : ∀ {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
      (f : X ⟶ Y)
      (hf : f ≫ (Y ↘ Spec (.of K)) = X ↘ Spec (.of K))
      (hY : (p ≫ f) ≫ (Y ↘ Spec (.of K)) = 𝟙 _)
      {t : Y.presheaf.stalk ((p ≫ f) (closedPoint K))}
      (ht : maximalIdeal _ = Ideal.span {t}) (htI : f.stalkMap (p (closedPoint K)) t ∈ I),
      f.stalkMap (p (closedPoint K)) ≫ π = f.stalkMap (p (closedPoint K)) ≫ ψ := by
    intro Y _ f hf hY t ht htI
    ext g
    change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I (c (ev _))
    rw [Ideal.Quotient.eq]
    have hev : ev ((f.stalkMap (p (closedPoint K))).hom g) =
        (Scheme.stalkClosedPointTo (p ≫ f)).hom g := by
      rw [Scheme.stalkClosedPointTo_comp]; rfl
    have hc : c ((Scheme.stalkClosedPointTo (p ≫ f)).hom g) =
        (f.stalkMap (p (closedPoint K))).hom
          (const (K := K) _ ((Scheme.stalkClosedPointTo (p ≫ f)).hom g)) :=
      const_comp f hf _ _
    have hm := sub_const_mem_maximalIdeal (p ≫ f) hY g
    rw [ht, Ideal.mem_span_singleton'] at hm
    obtain ⟨r, hr⟩ := hm
    have hr' : g - const (K := K) (f (p (closedPoint K)))
        ((Scheme.stalkClosedPointTo (p ≫ f)).hom g) = r * t := hr.symm
    change (f.stalkMap (p (closedPoint K))).hom g - c (ev ((f.stalkMap (p (closedPoint K))).hom g))
      ∈ I
    rw [hev, hc, ← map_sub, hr']
    convert I.mul_mem_left ((f.stalkMap (p (closedPoint K))).hom r) htI using 1
    exact map_mul _ r t
  have hfst := key pr₁ hXo hzC hς
    (hI ▸ Ideal.subset_span (Set.mem_insert _ _))
  have hsnd := key pr₂ (hX.w.symm.trans hXo) hzD hς'
    (hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hπψ : π = ψ := by
    refine stalk_hom_ext π ψ (hX.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hfst]
    · rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hsnd]
  intro f hf
  have h1 : π.hom f = ψ.hom f := by rw [hπψ]
  change Ideal.Quotient.mk I f = Ideal.Quotient.mk I (c (ev f)) at h1
  rw [ev_eq_zero_of_mem p hf, map_zero, map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

/-- For a local homomorphism `ev : O →+* K` out of a local ring, `ev` followed by the constants
`K →+* 𝒪_{Y,y}` is local. -/
public theorem isLocalHom_const_comp {Y : Scheme.{u}} [Y.Over (Spec (.of K))] (y : Y)
    {O : Type*} [CommRing O] [IsLocalRing O] (ev : O →+* K) [IsLocalHom ev] :
    IsLocalHom ((const (K := K) y).comp ev) := by
  refine ⟨fun f hf => ?_⟩
  by_cases h0 : ev f = 0
  · exfalso
    simp [h0] at hf
  · exact IsLocalHom.map_nonunit (f := ev) f (isUnit_iff_ne_zero.mpr h0)

/-- Local homomorphisms out of the local rings at `z` and `w` agreeing on constants glue to one
out of the local ring of `C ×_K D` at `(z, w)`. -/
private theorem exists_stalk_hom_of_isPullback {C D : Scheme.{u}} [C.Over (Spec (.of K))]
    [D.Over (Spec (.of K))] {X : Scheme.{u}} {pr₁ : X ⟶ C} {pr₂ : X ⟶ D}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (D ↘ Spec (.of K)))
    (p : Spec (.of K) ⟶ X)
    {R : CommRingCat.{u}} [IsLocalRing R] (ε : R ⟶ CommRingCat.of K) [IsLocalHom ε.hom]
    (ψC : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)) ⟶ R) [IsLocalHom ψC.hom]
    (ψD : D.presheaf.stalk ((p ≫ pr₂) (closedPoint K)) ⟶ R) [IsLocalHom ψD.hom]
    (hεC : ψC ≫ ε = Scheme.stalkClosedPointTo (p ≫ pr₁))
    (hεD : ψD ≫ ε = Scheme.stalkClosedPointTo (p ≫ pr₂))
    (hc : ∀ a, ψC.hom (const (K := K) _ a) = ψD.hom (const (K := K) _ a)) :
    ∃ Ψ : X.presheaf.stalk (p (closedPoint K)) ⟶
        R,
      pr₁.stalkMap
          (p (closedPoint K)) ≫ Ψ = ψC ∧
      pr₂.stalkMap
          (p (closedPoint K)) ≫ Ψ = ψD := by
  set gC := Spec.map ψC ≫ C.fromSpecStalk _
  set gD := Spec.map ψD ≫ D.fromSpecStalk _
  obtain ⟨hgC, hstcC⟩ := stalkClosedPointTo_fromSpecStalk_eq _ ψC
  obtain ⟨hgD, hstcD⟩ := stalkClosedPointTo_fromSpecStalk_eq _ ψD
  have hcond : gC ≫ (C ↘ Spec (.of K)) = gD ≫ (D ↘ Spec (.of K)) := by
    refine ext_of_germ _ _ fun a ↦ ?_
    rw [stalkClosedPointTo_comp_over_germ, stalkClosedPointTo_comp_over_germ, hstcC, hstcD,
      CommRingCat.comp_apply, CommRingCat.comp_apply, stalkCongr_const, stalkCongr_const]
    exact hc a
  set g := hX.lift gC gD hcond
  have hρ : Spec.map ε ≫ g = p := by
    refine hX.hom_ext ?_ ?_
    · rw [Category.assoc, hX.lift_fst, ← Category.assoc, ← Spec.map_comp, hεC,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    · rw [Category.assoc, hX.lift_snd, ← Category.assoc, ← Spec.map_comp, hεD,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hpt : g (closedPoint R) = p (closedPoint K) := by
    rw [← hρ]
    change g _ = g (Spec.map ε (closedPoint K))
    rw [Spec_closedPoint]
  refine ⟨(TopCat.Presheaf.stalkCongr _ (.of_eq hpt.symm)).hom ≫ Scheme.stalkClosedPointTo g,
    ?_, ?_⟩
  · rw [Scheme.Hom.stalkMap_congr_point_assoc _ _ _ hpt.symm, ← Scheme.stalkClosedPointTo_comp,
      stalkClosedPointTo_congr (hX.lift_fst _ _ hcond), hstcC]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.stalkSpecializes_comp_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  · rw [Scheme.Hom.stalkMap_congr_point_assoc _ _ _ hpt.symm, ← Scheme.stalkClosedPointTo_comp,
      stalkClosedPointTo_congr (hX.lift_snd _ _ hcond), hstcD]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.stalkSpecializes_comp_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

/-- The local ring at a `K`-point of `C ×_K D`, `C`, `D` curves, has Krull dimension two. -/
public theorem ringKrullDim_stalk_pullback {C D : Scheme.{u}} [C.Over (Spec (.of K))]
    [D.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))] [IsCurve K (D ↘ Spec (.of K))]
    {X : Scheme.{u}} [X.Over (Spec (.of K))] {pr₁ : X ⟶ C} {pr₂ : X ⟶ D}
    (hX : IsPullback pr₁ pr₂ (C ↘ Spec (.of K)) (D ↘ Spec (.of K)))
    (hXo : pr₁ ≫ (C ↘ Spec (.of K)) = X ↘ Spec (.of K))
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    [IsRegularLocalRing (X.presheaf.stalk
        (p (closedPoint K)))]
    {ς : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K))}
    {ς' : D.presheaf.stalk ((p ≫ pr₂) (closedPoint K))}
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'}) :
    ringKrullDim (X.presheaf.stalk
        (p (closedPoint K))) = 2 := by
  have hm := maximalIdeal_stalk_pullback hX hXo p hς hς'
  have hzC : (p ≫ pr₁) ≫ (C ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, hXo]; exact comp_over_eq_id p
  have hzD : (p ≫ pr₂) ≫ (D ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, ← hX.w, hXo]; exact comp_over_eq_id p
  have hς0 := ne_zero_of_maximalIdeal_eq _ hzC hς
  have hς'0 := ne_zero_of_maximalIdeal_eq _ hzD hς'
  let φ₁ : D.presheaf.stalk ((p ≫ pr₂) (closedPoint K)) ⟶
      C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)) :=
    CommRingCat.ofHom ((const (K := K) _).comp
      (Scheme.stalkClosedPointTo (p ≫ pr₂)).hom)
  let φ₂ : C.presheaf.stalk ((p ≫ pr₁) (closedPoint K)) ⟶
      D.presheaf.stalk ((p ≫ pr₂) (closedPoint K)) :=
    CommRingCat.ofHom ((const (K := K) _).comp
      (Scheme.stalkClosedPointTo (p ≫ pr₁)).hom)
  have : IsLocalHom φ₁.hom := isLocalHom_const_comp _ _
  have : IsLocalHom φ₂.hom := isLocalHom_const_comp _ _
  obtain ⟨Ψ₁, hΨ₁C, hΨ₁D⟩ := exists_stalk_hom_of_isPullback hX p
    (Scheme.stalkClosedPointTo (p ≫ pr₁))
    (𝟙 _) φ₁ (Category.id_comp _) (by ext g; exact ev_const _ hzC _) (fun a => by
      exact congrArg (const _) (ev_const _ hzD a).symm)
  obtain ⟨Ψ₂, hΨ₂C, hΨ₂D⟩ := exists_stalk_hom_of_isPullback hX p
    (Scheme.stalkClosedPointTo (p ≫ pr₂))
    φ₂ (𝟙 _) (by ext g; exact ev_const _ hzD _) (Category.id_comp _) (fun a => by
      exact congrArg (const _) (ev_const _ hzC a))
  have e₁₁ : Ψ₁.hom (pr₁.stalkMap
      (p (closedPoint K)) ς) = ς := congr($hΨ₁C ς)
  have e₁₂ : Ψ₁.hom (pr₂.stalkMap
      (p (closedPoint K)) ς') = 0 := (congr($hΨ₁D ς')).trans (by
    change const _ ((Scheme.stalkClosedPointTo (p ≫ pr₂)).hom ς') = 0
    erw [ev_eq_zero_of_mem _ (hς' ▸ Ideal.subset_span rfl), map_zero])
  have e₂₂ : Ψ₂.hom (pr₂.stalkMap
      (p (closedPoint K)) ς') = ς' := congr($hΨ₂D ς')
  have e₂₁ : Ψ₂.hom (pr₁.stalkMap
      (p (closedPoint K)) ς) = 0 := (congr($hΨ₂C ς)).trans (by
    change const _ ((Scheme.stalkClosedPointTo (p ≫ pr₁)).hom ς) = 0
    erw [ev_eq_zero_of_mem _ (hς ▸ Ideal.subset_span rfl), map_zero])
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk
        (p (closedPoint K)))
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  norm_cast
  apply le_antisymm
  · rw [hm]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le _ _).trans (by simp)
  · by_contra hlt
    push Not at hlt
    set a₁ := pr₁.stalkMap (p (closedPoint K)) ς
    set a₂ := pr₂.stalkMap
      (p (closedPoint K)) ς'
    have ha₁ : a₁ ≠ 0 := fun h => hς0 (by rw [← e₁₁, h, map_zero])
    have : IsNoetherian (X.presheaf.stalk
        (p (closedPoint K))) (X.presheaf.stalk
        (p (closedPoint K))) := IsRegularLocalRing.toIsNoetherian
    obtain ⟨s, hs, hspan⟩ :=
      (IsNoetherian.noetherian (maximalIdeal (X.presheaf.stalk (p (closedPoint K)))))
        |>.exists_span_finset_card_eq_spanFinrank
    obtain ⟨t, hst⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega : s.card ≤ 1)
    have hle : maximalIdeal _ ≤ Ideal.span {t} := by
      rw [← hspan]; exact Submodule.span_mono fun y hy => by simpa using hst hy
    have h1 : a₁ ∈ maximalIdeal _ := hm ▸ Ideal.subset_span (Set.mem_insert _ _)
    have h2 : a₂ ∈ maximalIdeal _ := hm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    obtain ⟨x₁, hx₁⟩ := Ideal.mem_span_singleton'.mp (hle h1)
    obtain ⟨x₂, hx₂⟩ := Ideal.mem_span_singleton'.mp (hle h2)
    have ht : t ∈ maximalIdeal _ := by
      rcases Finset.subset_singleton_iff.mp hst with h | h
      · exfalso
        rw [h, Finset.coe_empty, Submodule.span_empty] at hspan
        exact ha₁ (by simpa [← hspan] using h1)
      · rw [← hspan, h]; exact Submodule.subset_span (by simp)
    rw [hm, Ideal.mem_span_pair] at ht
    obtain ⟨α, β, hαβ⟩ := ht
    have ht0 : t ≠ 0 := by rintro rfl; exact ha₁ (by rw [← hx₁, mul_zero])
    have hone : α * x₁ + β * x₂ = 1 := by
      apply mul_right_cancel₀ ht0
      rw [one_mul, add_mul, mul_assoc, mul_assoc, hx₁, hx₂, hαβ]
    by_cases hu : IsUnit x₁
    · have : a₂ = (x₂ * hu.unit⁻¹) * a₁ := by
        rw [← hx₁, ← hx₂, mul_assoc, ← mul_assoc _ x₁, hu.val_inv_mul, one_mul]
      apply hς'0
      rw [← e₂₂, this, map_mul, e₂₁, mul_zero]
    · have hu₂ : IsUnit x₂ := by
        by_contra hu₂
        have : α * x₁ + β * x₂ ∈ maximalIdeal _ :=
          add_mem (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hu))
            (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hu₂))
        rw [hone] at this
        exact (mem_maximalIdeal _).mp this isUnit_one
      have : a₁ = (x₁ * hu₂.unit⁻¹) * a₂ := by
        rw [← hx₁, ← hx₂, mul_assoc, ← mul_assoc _ x₂, hu₂.val_inv_mul, one_mul]
      apply hς0
      rw [← e₁₁, this, map_mul, e₁₂, mul_zero]

end Geometry

section Taylor

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
  [IsRegularLocalRing (X.presheaf.stalk (p (closedPoint K)))]
  (hdim : ringKrullDim (X.presheaf.stalk (p (closedPoint K))) = 2)
  {ϖ ϖ' : X.presheaf.stalk (p (closedPoint K))}
  (hϖ : maximalIdeal (X.presheaf.stalk (p (closedPoint K))) = Ideal.span {ϖ, ϖ'})

include hdim hϖ

/-- The Taylor coefficients of a linear combination `∑ c(aᵢ) fᵢ` with constant coefficients. -/
public theorem taylorCoeff₂_sum_const_mul {ι : Type*} (s : Finset ι) (a : ι → K)
    (f : ι → X.presheaf.stalk (p (closedPoint K))) (i₁ i₂ : ℕ) :
    taylorCoeff₂ p ϖ ϖ' (∑ i ∈ s, const (p (closedPoint K)) (a i) * f i) i₁ i₂ =
      ∑ i ∈ s, a i * taylorCoeff₂ p ϖ ϖ' (f i) i₁ i₂ := by
  have hev : ∀ k, (Scheme.stalkClosedPointTo p).hom (const (p (closedPoint K)) k) = k :=
    ev_const p (comp_over_eq_id p)
  have key : ∀ g i j, taylorCoeff₂ p ϖ ϖ' g i j =
      MvPowerSeries.coeff (bidegree (i, j))
        (Classical.epsilon fun F ↦ IsExpansion₂ (const (p (closedPoint K))) ϖ ϖ' F g) :=
    fun g i j => rfl
  have hspec : ∀ g, IsExpansion₂ (const (p (closedPoint K))) ϖ ϖ'
      (Classical.epsilon fun F ↦ IsExpansion₂ (const (p (closedPoint K))) ϖ ϖ' F g) g :=
    fun g => Classical.epsilon_spec (exists_isExpansion₂ hϖ _ _ hev g)
  have hsum := (hspec _).unique hdim hϖ
    (isExpansion₂_sum s _ _ fun i _ => (hspec (f i)).const_mul (a i))
  rw [key, hsum, map_sum]
  simp only [MvPowerSeries.coeff_C_mul, key]

end Taylor

section Decomposition

variable {K : Type u} [Field K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]

/-- **The Taylor coefficient `D_{ijj'}` of `F_i(ξ_j, ξ'_{j'})`.** For a polynomial `P` in the two
sets of variables `x_ν, x'_ν`, whose coefficients act through constants, the Taylor coefficient of
`P(ξ ∘ pr₁, ξ' ∘ pr₂)` at `(z, w)` is `∑_α P_α ∂_{i₁}(ξ^{α₁})(z) ∂'_{i₂}(ξ'^{α₂})(w)`. -/
private theorem taylorCoeff₂_eval₂_sumElim
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))]
    [IsRegularLocalRing ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk
        (p (closedPoint K)))]
    {ς : C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K))}
    {ς' : C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))}
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'})
    {R : Type*} [CommRing R] {n : ℕ} (P : MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) R)
    (c : R →+* (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk
        (p (closedPoint K))) (a : R → K) (hc : ∀ t, c t = const _ (a t))
    (ξ : Fin (n + 1) → C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K)))
    (ξ' : Fin (n + 1) → C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K)))
    (i₁ i₂ : ℕ) :
    taylorCoeff₂ p
        ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
        ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
        (P.eval₂ c (Sum.elim
          (fun ν => (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
            (p (closedPoint K)) (ξ ν))
          (fun ν => (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
            (p (closedPoint K)) (ξ' ν)))) i₁ i₂ =
      ∑ e ∈ P.support, a (P.coeff e) *
        (taylorCoeff (p ≫ pullback.fst _ _) ς (∏ ν, ξ ν ^ e (Sum.inl ν)) i₁ *
          taylorCoeff (p ≫ pullback.snd _ _) ς' (∏ ν, ξ' ν ^ e (Sum.inr ν)) i₂) := by
  have hpb := IsPullback.of_hasPullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
  have hm := maximalIdeal_stalk_pullback hpb pullback.condition p hς hς'
  have hdim := ringKrullDim_stalk_pullback hpb pullback.condition p hς hς'
  have hP : P.eval₂ c (Sum.elim
          (fun ν => (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
            (p (closedPoint K)) (ξ ν))
          (fun ν => (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
            (p (closedPoint K)) (ξ' ν))) =
      ∑ e ∈ P.support, const (p (closedPoint K)) (a (P.coeff e)) *
        ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K))
            (∏ ν, ξ ν ^ e (Sum.inl ν)) *
          (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K))
            (∏ ν, ξ' ν ^ e (Sum.inr ν))) := by
    rw [MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hc, Fintype.prod_sum_type]
    exact congrArg₂ _ rfl (congrArg₂ _
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun ν _ => map_pow _ _ _)).symm
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun ν _ => map_pow _ _ _)).symm)
  rw [hP, taylorCoeff₂_sum_const_mul p hdim hm]
  exact Finset.sum_congr rfl fun e _ =>
    congrArg _ (taylorCoeff₂_stalkMap_fst_mul_stalkMap_snd p ς _ ς' _ hς hς' i₁ i₂)

end Decomposition

section Analysis

open Real

variable {K : Type u} [Field K] [NumberField K]

/-- The weight `n_v / [K : ℚ]` of a place `v` of `K`. -/
@[expose] public noncomputable def wt (v : InfinitePlace K ⊕ FinitePlace K) : ℝ :=
  Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K)
    (fun _ : FinitePlace K => 1 / finrank ℚ K) v

/-- The absolute value `‖·‖_v` at a place `v` of `K`. -/
@[expose] public noncomputable def absV (v : InfinitePlace K ⊕ FinitePlace K) : AbsoluteValue K ℝ :=
  Sum.elim (fun w : InfinitePlace K => w.1) (fun w : FinitePlace K => w.1) v

/-- Bombieri's normalised `log |x|_v`, with `log 0 = ⊥`. -/
@[expose] public noncomputable def logAbsV (v : InfinitePlace K ⊕ FinitePlace K) (x : K) : EReal :=
  haveI := Classical.propDecidable (x = 0)
  if x = 0 then ⊥ else
    ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w x))
      (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w x)) v : ℝ) : EReal)

/-- The weight `n_v / [K : ℚ]` of a place is positive. -/
public lemma wt_pos (v : InfinitePlace K ⊕ FinitePlace K) : 0 < wt v := by
  rcases v with w | w
  · exact div_pos (by exact_mod_cast w.mult_pos) (by exact_mod_cast finrank_pos)
  · exact div_pos one_pos (by exact_mod_cast finrank_pos)

/-- `log |0|_v = ⊥`. -/
public lemma logAbsV_zero (v : InfinitePlace K ⊕ FinitePlace K) : logAbsV v (0 : K) = ⊥ := by
  simp [logAbsV]

/-- For `x ≠ 0`, `log |x|_v` is the real number `wt v * log ‖x‖_v`. -/
public lemma logAbsV_of_ne_zero (v : InfinitePlace K ⊕ FinitePlace K) {x : K} (hx : x ≠ 0) :
    logAbsV v x = ((wt v * log (absV v x) : ℝ) : EReal) := by
  rcases v with w | w <;> simp [logAbsV, hx, wt, absV] <;> rfl

/-- `log |x|_v` is never `⊤`. -/
public lemma logAbsV_ne_top (v : InfinitePlace K ⊕ FinitePlace K) (x : K) : logAbsV v x ≠ ⊤ := by
  by_cases hx : x = 0
  · simp [hx, logAbsV_zero]
  · rw [logAbsV_of_ne_zero v hx]; exact EReal.coe_ne_top _

/-- `log |x y|_v = log |x|_v + log |y|_v`. -/
public lemma logAbsV_mul (v : InfinitePlace K ⊕ FinitePlace K) (x y : K) :
    logAbsV v (x * y) = logAbsV v x + logAbsV v y := by
  by_cases hx : x = 0
  · simp [hx, logAbsV_zero]
  by_cases hy : y = 0
  · simp [hy, logAbsV_zero]
  rw [logAbsV_of_ne_zero v (mul_ne_zero hx hy), logAbsV_of_ne_zero v hx, logAbsV_of_ne_zero v hy,
    map_mul, log_mul ((absV v).pos hx).ne' ((absV v).pos hy).ne', mul_add, EReal.coe_add]

/-- If `y ≠ 0` and `‖x‖_v ≤ ‖y‖_v`, then `log |x|_v ≤ log |y|_v`. -/
public lemma logAbsV_le_of_le (v : InfinitePlace K ⊕ FinitePlace K) {x y : K} (hy : y ≠ 0)
    (h : absV v x ≤ absV v y) : logAbsV v x ≤ logAbsV v y := by
  by_cases hx : x = 0
  · simp [hx, logAbsV_zero]
  rw [logAbsV_of_ne_zero v hx, logAbsV_of_ne_zero v hy, EReal.coe_le_coe_iff]
  exact mul_le_mul_of_nonneg_left (log_le_log ((absV v).pos hx) h) (wt_pos v).le

/-- The archimedean correction `ε_v log M`: `log M` weighted at an infinite place, `0` at a
finite one. -/
@[expose] public noncomputable def archLog (v : InfinitePlace K ⊕ FinitePlace K) (M : ℝ) : ℝ :=
  Sum.elim (fun _ => wt v * log M) (fun _ => 0) v

/-- Some term `t_e` of a nonempty finite sum bounds it: `‖∑ tᵢ‖_v ≤ #s ‖t_e‖_v` at an infinite
place and `‖∑ tᵢ‖_v ≤ ‖t_e‖_v` at a finite place. -/
public lemma exists_absV_sum_le {ι : Type*} (v : InfinitePlace K ⊕ FinitePlace K)
    {s : Finset ι} (hs : s.Nonempty) (t : ι → K) :
    ∃ e ∈ s, absV v (∑ i ∈ s, t i) ≤
      Sum.elim (fun _ => (s.card : ℝ)) (fun _ => 1) v * absV v (t e) := by
  rcases v with w | w
  · obtain ⟨e, he, hmax⟩ := s.exists_max_image (fun i => absV (.inl w) (t i)) hs
    refine ⟨e, he, ((absV (.inl w)).sum_le s t).trans ?_⟩
    simpa using Finset.sum_le_card_nsmul s _ _ hmax
  · have hna : IsNonarchimedean (absV (K := K) (.inr w)) := fun a b => FinitePlace.add_le w a b
    obtain ⟨e, he, h⟩ := hna.finset_image_add_of_nonempty (g := t) hs
    exact ⟨e, he, by simpa using h⟩

/-- `log |∑_{i ∈ s} tᵢ|_v ≤ ε_v log M + max_i log |tᵢ|_v` when `s` has at most `M` elements. -/
public lemma logAbsV_sum_le {ι : Type*} (v : InfinitePlace K ⊕ FinitePlace K) (s : Finset ι)
    (t : ι → K) {M : ℕ} (hM : s.card ≤ M) :
    logAbsV v (∑ i ∈ s, t i) ≤ (archLog v M : EReal) + s.sup fun i => logAbsV v (t i) := by
  by_cases h0 : ∑ i ∈ s, t i = 0
  · rw [h0, logAbsV_zero]; exact bot_le
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact h0 (by simp [h])
  obtain ⟨e, he, hle⟩ := exists_absV_sum_le v hs t
  have hpos := (absV v).pos h0
  have hte : t e ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hle
    linarith
  refine le_trans ?_ (add_le_add le_rfl (Finset.le_sup (f := fun i => logAbsV v (t i)) he))
  rw [logAbsV_of_ne_zero v h0, logAbsV_of_ne_zero v hte, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hcard : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have hMr : (s.card : ℝ) ≤ M := by exact_mod_cast hM
  have hte' := (absV v).pos hte
  rcases v with w | w
  · simp only [Sum.elim_inl] at hle
    simp only [archLog, Sum.elim_inl]
    rw [← mul_add, ← log_mul (by linarith : (M : ℝ) ≠ 0) hte'.ne']
    refine mul_le_mul_of_nonneg_left (log_le_log hpos (hle.trans ?_)) (wt_pos _).le
    exact mul_le_mul_of_nonneg_right hMr hte'.le
  · simp only [Sum.elim_inr, one_mul] at hle
    simp only [archLog, Sum.elim_inr, zero_add]
    exact mul_le_mul_of_nonneg_left (log_le_log hpos hle) (wt_pos _).le

private lemma absV_inl (w : InfinitePlace K) (x : K) : absV (.inl w) x = w x := rfl

private lemma absV_inr (w : FinitePlace K) (x : K) : absV (.inr w) x = w x := rfl

/-- The maximum of `log |x_c|_v` over the entries of a nonzero vector is
`log max_c |x_c|_v`. -/
public lemma sup_logAbsV_eq {ι : Type*} [Fintype ι] (v : InfinitePlace K ⊕ FinitePlace K)
    {x : ι → K} (hx : x ≠ 0) :
    (Finset.univ.sup fun c => logAbsV v (x c)) =
      ((wt v * log (⨆ c, absV v (x c)) : ℝ) : EReal) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c, x c ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨c₀⟩
  obtain ⟨c₁, hc₁⟩ := exists_eq_ciSup_of_finite (f := fun c => absV v (x c))
  have hpos : 0 < absV v (x c₁) := by
    rw [hc₁]
    exact ((absV v).pos hc₀).trans_le (Finite.le_ciSup_of_le c₀ le_rfl)
  have hc₁0 : x c₁ ≠ 0 := fun h => by simp [h] at hpos
  rw [← hc₁, ← logAbsV_of_ne_zero v hc₁0]
  refine le_antisymm (Finset.sup_le fun c _ => logAbsV_le_of_le v hc₁0 ?_)
    (Finset.le_sup (f := fun c => logAbsV v (x c)) (Finset.mem_univ c₁))
  rw [hc₁]
  exact Finite.le_ciSup_of_le c le_rfl

/-- The product formula, in logarithmic form. -/
public lemma sum_log_eq_zero {a : K} (ha : a ≠ 0) :
    (∑ w : InfinitePlace K, w.mult * log (w a)) + ∑ᶠ w : FinitePlace K, log (w a) = 0 := by
  have hi (w : InfinitePlace K) : 0 < w a := w.pos_iff.mpr ha
  have hf (w : FinitePlace K) : 0 < w a := w.pos_iff.mpr ha
  have h := NumberField.prod_abs_eq_one ha
  have := congrArg Real.log h
  rw [Real.log_one, log_mul (Finset.prod_pos fun w _ => pow_pos (hi w) _).ne'
      (finprod_induction (0 < ·) one_pos (fun _ _ => mul_pos) hf).ne',
    log_prod fun w _ => (pow_pos (hi w) _).ne', log_finprod hf] at this
  simpa [log_pow] using this

/-- A finitely supported sum over the places of `K` splits into the infinite and the finite
places. -/
public lemma finsum_places {M : Type*} [AddCommMonoid M]
    (f : InfinitePlace K ⊕ FinitePlace K → M)
    (hf : (Function.support fun w : FinitePlace K => f (.inr w)).Finite) :
    ∑ᶠ v, f v = (∑ w : InfinitePlace K, f (.inl w)) + ∑ᶠ w : FinitePlace K, f (.inr w) := by
  classical
  let t := hf.toFinset
  have hsub : Function.support f ⊆
      ((Finset.univ : Finset (InfinitePlace K)).disjSum t : Finset _) := by
    rintro (w | w) hw
    · simp
    · simpa [t] using hw
  rw [finsum_eq_sum_of_support_subset f hsub, Finset.sum_disjSum,
    finsum_eq_sum_of_support_subset (s := t) _ (by simp [t])]

/-- The sum of the weights of the infinite places is `1`. -/
public lemma sum_wt_inl : ∑ w : InfinitePlace K, wt (K := K) (.inl w) = 1 := by
  simp only [wt, Sum.elim_inl]
  rw [← Finset.sum_div]
  have : (∑ w : InfinitePlace K, (w.mult : ℝ)) = finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  rw [this, div_self (by exact_mod_cast finrank_pos.ne')]

private lemma archLog_inr (w : FinitePlace K) (M : ℝ) : archLog (.inr w) M = 0 := rfl

/-- `∑_v ε_v log M = log M`. -/
public lemma sum_archLog (M : ℝ) :
    ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v M = log M := by
  rw [finsum_places _ (by simp [archLog_inr])]
  simp only [archLog_inr, finsum_zero, add_zero]
  simp only [archLog, Sum.elim_inl]
  rw [← Finset.sum_mul, sum_wt_inl, one_mul]

/-- `log ‖a‖_w` vanishes at all but finitely many finite places `w`. -/
public lemma finite_support_log (a : K) :
    (Function.support fun w : FinitePlace K => log (w a)).Finite := by
  by_cases ha : a = 0
  · simp [ha]
  refine (FinitePlace.hasFiniteMulSupport (K := K) ha).subset fun w hw => ?_
  intro h
  exact hw (by simp [h])

/-- The finitely supported sum `∑_v` of reals, read in `EReal`. -/
public lemma finsum_coe_ereal {α : Type*} (p : α → ℝ) (hp : (Function.support p).Finite) :
    ∑ᶠ a, (p a : EReal) = ((∑ᶠ a, p a : ℝ) : EReal) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := hp.toFinset) p (by simp),
    finsum_eq_sum_of_support_subset (s := hp.toFinset) _ (fun a ha => by simpa using ha)]
  exact (map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm

/-- Summing local lower bounds `w_v T_v ≥ w_v log |q|_v - R_v` over the places: by the product
formula, `∑_v n_v T_v / [K : ℚ] ≥ -∑_v R_v`. -/
public lemma neg_finsum_le {T R : InfinitePlace K ⊕ FinitePlace K → ℝ} {q : K} (hq : q ≠ 0)
    (hT : ∀ v, wt v * log (absV v q) - R v ≤ wt v * T v)
    (hTf : (Function.support fun w : FinitePlace K => T (.inr w)).Finite)
    (hRf : (Function.support fun w : FinitePlace K => R (.inr w)).Finite) :
    -(∑ᶠ v, R v) ≤ ((∑ w : InfinitePlace K, w.mult * T (.inl w)) +
      ∑ᶠ w : FinitePlace K, T (.inr w)) / finrank ℚ K := by
  have hN : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  rw [finsum_places R hRf, le_div_iff₀ hN]
  have hinf : ∀ w : InfinitePlace K, w.mult * log (w q) - finrank ℚ K * R (.inl w) ≤
      w.mult * T (.inl w) := by
    intro w
    have h := hT (.inl w)
    simp only [wt, Sum.elim_inl, absV_inl] at h
    have := mul_le_mul_of_nonneg_left h hN.le
    have e : (finrank ℚ K : ℝ) * ((w.mult : ℝ) / finrank ℚ K) = w.mult := by field_simp
    rw [mul_sub, ← mul_assoc, e, ← mul_assoc, e] at this
    linarith
  have hfin : ∀ w : FinitePlace K, log (w q) - finrank ℚ K * R (.inr w) ≤ T (.inr w) := by
    intro w
    have h := hT (.inr w)
    simp only [wt, Sum.elim_inr, absV_inr] at h
    have := mul_le_mul_of_nonneg_left h hN.le
    have e : (finrank ℚ K : ℝ) * (1 / finrank ℚ K) = 1 := by field_simp
    rw [mul_sub, ← mul_assoc, e, ← mul_assoc, e, one_mul, one_mul] at this
    linarith
  have h1 := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hinf w
  have h2 : ∑ᶠ w : FinitePlace K, (log (w q) - finrank ℚ K * R (.inr w)) ≤
      ∑ᶠ w : FinitePlace K, T (.inr w) :=
    finsum_le_finsum' (((finite_support_log q).union hRf).subset fun w hw => by
        by_contra h
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
        exact hw (by simp [h.1, h.2])) hTf hfin
  rw [finsum_sub_distrib (finite_support_log q)
      (hRf.subset (Function.support_mul_subset_right _ _)), ← mul_finsum' _ _ hRf] at h2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  have hp := sum_log_eq_zero (K := K) hq
  linarith

/-- A function on the places of `K` with finite support among the finite places has finite
support. -/
public lemma finite_support_of_inr {M : Type*} [Zero M]
    {f : InfinitePlace K ⊕ FinitePlace K → M}
    (hf : (Function.support fun w : FinitePlace K => f (.inr w)).Finite) :
    (Function.support f).Finite := by
  refine ((Set.finite_univ (α := InfinitePlace K)).image Sum.inl |>.union
    (hf.image Sum.inr)).subset ?_
  rintro (w | w) hw
  · exact Or.inl ⟨w, trivial, rfl⟩
  · exact Or.inr ⟨w, hw, rfl⟩

/-- **Steps 1 and 2 of Bombieri's Lemma 4.** If `b ≠ 0` and, for every non-vanishing triple
`(i, j, j')`, `b = (y_{i°} / y_i)^d (x_j / x_{j°})^{δ₁} (x'_{j'} / x'_{j'°})^{δ₂} D_{ijj'}`, then
the local expression of `h_V` is at least `-∑_v R_v` as soon as
`w_v log |D_{i j_v j'_v}|_v ≤ R_v` for all `v` and all `i` with `y_i ≠ 0`. -/
public theorem neg_finsum_le_localExpression {ι κ : Type*} [Fintype ι] [Fintype κ]
    {x x' : ι → K} {y : κ → K} (hy : y ≠ 0) (δ₁ δ₂ d : ℕ) {b : K} (hb : b ≠ 0)
    {i₀ : κ} {j₀ j₀' : ι} (hy₀ : y i₀ ≠ 0) (hx₀ : x j₀ ≠ 0) (hx₀' : x' j₀' ≠ 0)
    (D : κ → ι → ι → K)
    (hval : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 →
      b = (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j₀') ^ δ₂ * D i j j')
    (j₁ j₂ : InfinitePlace K ⊕ FinitePlace K → ι) (hj₁ : ∀ v, x (j₁ v) ≠ 0)
    (hj₂ : ∀ v, x' (j₂ v) ≠ 0) (R : InfinitePlace K ⊕ FinitePlace K → ℝ)
    (hR : ∀ v i, y i ≠ 0 → wt v * log (absV v (D i (j₁ v) (j₂ v))) ≤ R v)
    (hRf : (Function.support fun w : FinitePlace K => R (.inr w)).Finite) :
    -(∑ᶠ v, R v) ≤ ((∑ w : InfinitePlace K, w.mult *
          ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
            log (w (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ (d : ℤ)))) +
        ∑ᶠ w : FinitePlace K, ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
            log (w (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ (d : ℤ)))) / finrank ℚ K := by
  have : Nonempty {i // y i ≠ 0} := let ⟨i, hi⟩ := Function.ne_iff.mp hy; ⟨⟨i, hi⟩⟩
  have : Nonempty {j // x j ≠ 0} := ⟨⟨j₀, hx₀⟩⟩
  have : Nonempty {j // x' j ≠ 0} := ⟨⟨j₀', hx₀'⟩⟩
  set q : K := x j₀ ^ δ₁ * x' j₀' ^ δ₂ / y i₀ ^ d * b with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact mul_ne_zero (by simp [hx₀, hx₀', hy₀]) hb
  have hD0 : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 → D i j j' ≠ 0 := by
    intro i j j' hi hj hj' h
    exact hb (by rw [hval i j j' hi hj hj', h, mul_zero])
  have hquot : ∀ i j j', y i ≠ 0 → x j ≠ 0 → x' j' ≠ 0 →
      x j ^ δ₁ * x' j' ^ δ₂ / y i ^ (d : ℤ) = q / D i j j' := by
    intro i j j' hi hj hj'
    have hD := hD0 i j j' hi hj hj'
    rw [zpow_natCast, eq_div_iff hD, hq, hval i j j' hi hj hj']
    simp only [div_pow]
    field_simp
  let T : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v =>
    ⨅ i : {i // y i ≠ 0}, ⨆ jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0},
      log (absV v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ (d : ℤ)))
  have hterm : ∀ v (i : {i // y i ≠ 0}) (jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0}),
      log (absV v (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ (d : ℤ))) =
        log (absV v q) - log (absV v (D i jj.1 jj.2)) := by
    intro v i jj
    rw [hquot i jj.1 jj.2 i.2 jj.1.2 jj.2.2, map_div₀,
      log_div ((absV v).pos hq0).ne' ((absV v).pos (hD0 _ _ _ i.2 jj.1.2 jj.2.2)).ne']
  refine neg_finsum_le (T := T) hq0 (fun v => ?_) ?_ hRf
  · have hw := wt_pos v
    suffices h : (wt v * log (absV v q) - R v) / wt v ≤ T v by
      have := mul_le_mul_of_nonneg_left h hw.le
      rwa [mul_div_cancel₀ _ hw.ne'] at this
    refine le_ciInf fun i => ?_
    refine le_trans ?_ (Finite.le_ciSup_of_le (⟨j₁ v, hj₁ v⟩, ⟨j₂ v, hj₂ v⟩) le_rfl)
    rw [hterm, div_le_iff₀' hw, mul_sub]
    linarith [hR v i i.2]
  · classical
    let S : Finset (κ × ι × ι) := Finset.univ.filter fun t => D t.1 t.2.1 t.2.2 ≠ 0
    refine ((FinitePlace.hasFiniteMulSupport (K := K) hq0).union
      (Set.finite_iUnion fun t : S => FinitePlace.hasFiniteMulSupport (K := K)
        (Finset.mem_filter.mp t.2).2)).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_iUnion, Function.mem_mulSupport, not_or, not_exists,
      not_not] at h
    apply hw
    have h0 : ∀ (i : {i // y i ≠ 0}) (jj : {j // x j ≠ 0} × {j' // x' j' ≠ 0}),
        log (absV (.inr w) (x jj.1 ^ δ₁ * x' jj.2 ^ δ₂ / y i ^ (d : ℤ))) = 0 := by
      intro i jj
      rw [hterm, absV_inr, absV_inr, h.1,
        h.2 ⟨(i.1, jj.1.1, jj.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hD0 _ _ _ i.2 jj.1.2 jj.2.2⟩⟩]
      simp
    simp only [T, h0, ciSup_const, ciInf_const]

/-- Bombieri's maximum over the partitions `π` of `i` of `∑_{l ∈ π} g l`. -/
@[expose] public noncomputable def partitionSup (i : ℕ) (g : ℕ → EReal) : EReal :=
  (Finset.univ : Finset (Nat.Partition i)).sup fun q => (q.parts.map g).sum

/-- A finite sum of values of `g`, none of which is `⊤`, is not `⊤`. -/
public lemma multiset_sum_ne_top (s : Multiset ℕ) (g : ℕ → EReal) (hg : ∀ l, g l ≠ ⊤) :
    (s.map g).sum ≠ ⊤ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    exact (EReal.add_lt_top (hg a) ih).ne

/-- `partitionSup i g ≠ ⊤` when `g` never takes the value `⊤`. -/
public lemma partitionSup_ne_top (i : ℕ) (g : ℕ → EReal) (hg : ∀ l, g l ≠ ⊤) :
    partitionSup i g ≠ ⊤ :=
  ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun q _ =>
    (multiset_sum_ne_top q.parts g hg).lt_top).ne

/-- A finite supremum of values, none of which is `⊤`, is not `⊤`. -/
public lemma finset_sup_ne_top {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i, g i ≠ ⊤) :
    s.sup g ≠ ⊤ :=
  ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ => (hg i).lt_top).ne

/-- Values in `{⊥, 0}` are closed under sums and maxima. -/
@[expose] public def BotOrZero (x : EReal) : Prop := x = ⊥ ∨ x = 0

/-- `BotOrZero` is closed under addition. -/
public lemma botOrZero_add {x y : EReal} (hx : BotOrZero x) (hy : BotOrZero y) :
    BotOrZero (x + y) := by
  rcases hx with rfl | rfl
  · left; exact EReal.bot_add _
  · rcases hy with rfl | rfl
    · left; simp
    · right; simp

/-- `BotOrZero` is closed under finite suprema. -/
public lemma botOrZero_finset_sup {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hg : ∀ i ∈ s, BotOrZero (g i)) : BotOrZero (s.sup g) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; rfl
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [BotOrZero, h1, h2]

/-- `partitionSup i g` is `⊥` or `0` when `g l` is for every `l ≤ i`. -/
public lemma botOrZero_partitionSup (i : ℕ) (g : ℕ → EReal)
    (hg : ∀ l ≤ i, BotOrZero (g l)) : BotOrZero (partitionSup i g) := by
  refine botOrZero_finset_sup _ _ fun q _ => ?_
  have key : ∀ s : Multiset ℕ, (∀ l ∈ s, l ≤ i) → BotOrZero (s.map g).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; right; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.sum_cons]
      exact botOrZero_add (hg a (hs a (Multiset.mem_cons_self a s)))
        (ih fun l hl => hs l (Multiset.mem_cons_of_mem hl))
  refine key q.parts fun l hl => ?_
  rw [← q.parts_sum]
  exact Multiset.le_sum_of_mem hl

/-- At a finite place where every nonzero element of a finite set has absolute value `1`,
the normalised logarithms of the elements of that set lie in `{⊥, 0}`. -/
public lemma botOrZero_logAbsV {w : FinitePlace K} {x : K}
    (hx : x ≠ 0 → w x = 1) : BotOrZero (logAbsV (.inr w) x) := by
  by_cases h : x = 0
  · left; rw [h, logAbsV_zero]
  · right
    rw [logAbsV_of_ne_zero _ h, absV_inr, hx h]
    simp

/-- `ε_v log |2 ^ k|_v` as an `archLog`. -/
public lemma sumElim_logAbsV_two_pow (v : InfinitePlace K ⊕ FinitePlace K) (k : ℕ) :
    Sum.elim (fun _ => logAbsV v ((2 : K) ^ k)) (fun _ => (0 : EReal)) v =
      ((archLog v ((2 : ℝ) ^ k) : ℝ) : EReal) := by
  rcases v with w | w
  · simp only [Sum.elim_inl, archLog]
    rw [logAbsV_of_ne_zero _ (pow_ne_zero _ two_ne_zero), absV_inl, map_pow]
    have h2 : w (2 : K) = 2 := by exact_mod_cast InfinitePlace.map_natCast w 2
    rw [h2]
  · simp [archLog]

/-- `∑_v ε_v log |2 ^ k|_v ≤ k`. -/
public lemma sum_archLog_two_pow_le (k : ℕ) :
    ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v ((2 : ℝ) ^ k) ≤ k := by
  rw [sum_archLog, Real.log_pow]
  have := Real.log_two_lt_d9
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith

/-- `∑_v w_v log max_c |x_c|_v` is the absolute logarithmic height of a nonzero vector. -/
public lemma finsum_wt_log_iSup {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, wt v * log (⨆ c, absV v (x c)) =
      Height.logHeight x / finrank ℚ K := by
  rw [finsum_places _ ((hasFiniteSupport_log_iSup hx).subset
      (Function.support_mul_subset_right _ _)), logHeight_eq_sum_log_iSup hx]
  simp only [wt, Sum.elim_inl, Sum.elim_inr, absV_inl, absV_inr]
  rw [← mul_finsum' _ _ (hasFiniteSupport_log_iSup hx), add_div, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · ring

/-- `log |∑_e f_e A_e B_e|_v ≤ ε_v log M + max log |f|_v + max log |A|_v + max log |B|_v`. -/
public lemma logAbsV_sum_mul_le (v : InfinitePlace K ⊕ FinitePlace K) {σ : Type*}
    (s : Finset σ) (f A B : σ → K) {M : ℕ} (hs : s.card ≤ M) {G α β : EReal}
    (hf : ∀ e ∈ s, logAbsV v (f e) ≤ G) (hA : ∀ e ∈ s, logAbsV v (A e) ≤ α)
    (hB : ∀ e ∈ s, logAbsV v (B e) ≤ β) :
    logAbsV v (∑ e ∈ s, f e * (A e * B e)) ≤ (archLog v M : EReal) + (G + (α + β)) :=
  (logAbsV_sum_le v s _ hs).trans (add_le_add le_rfl (Finset.sup_le fun e he => by
    rw [logAbsV_mul, logAbsV_mul]
    exact add_le_add (hf e he) (add_le_add (hA e he) (hB e he))))

/-- Reading the bound of `logAbsV_sum_mul_le` in `ℝ` at a nonzero value: the partition terms are
then finite. -/
public lemma real_of_logAbsV_le (v : InfinitePlace K ⊕ FinitePlace K) {x : K} (hx : x ≠ 0)
    {a g e₁ e₂ : ℝ} {P P' : EReal} (hP : P ≠ ⊤) (hP' : P' ≠ ⊤)
    (h : logAbsV v x ≤ (a : EReal) + ((g : EReal) + ((P + e₁) + (P' + e₂)))) :
    P ≠ ⊥ ∧ P' ≠ ⊥ ∧ wt v * log (absV v x) ≤ a + g + (P.toReal + e₁) + (P'.toReal + e₂) := by
  rw [logAbsV_of_ne_zero v hx] at h
  induction P using EReal.rec with
  | bot =>
    simp only [EReal.bot_add, EReal.add_bot] at h
    exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
  | top => exact absurd rfl hP
  | coe P =>
    induction P' using EReal.rec with
    | bot =>
      simp only [EReal.bot_add, EReal.add_bot] at h
      exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
    | top => exact absurd rfl hP'
    | coe P' =>
      refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _, ?_⟩
      simp only [EReal.toReal_coe]
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
        ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      linarith

/-- The partition terms vanish at all but finitely many places. -/
public lemma finite_support_partitionSup {ι κ : Type*} [Fintype ι] [Fintype κ] (i : ℕ)
    (c : ℕ → ι → κ → K) (j : InfinitePlace K ⊕ FinitePlace K → κ)
    (hne : ∀ v, partitionSup i (fun l => Finset.univ.sup fun ν => logAbsV v (c l ν (j v))) ≠ ⊥) :
    (Function.support fun w : FinitePlace K =>
      (partitionSup i (fun l => Finset.univ.sup fun ν =>
        logAbsV (.inr w) (c l ν (j (.inr w))))).toReal).Finite := by
  classical
  let T : Finset (ℕ × ι × κ) := (Finset.range (i + 1) ×ˢ Finset.univ ×ˢ Finset.univ).filter
    fun t => c t.1 t.2.1 t.2.2 ≠ 0
  refine (Set.finite_iUnion fun t : T => FinitePlace.hasFiniteMulSupport (K := K)
    (Finset.mem_filter.mp t.2).2).subset fun w hw => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  apply hw
  have hbz : BotOrZero (partitionSup i (fun l => Finset.univ.sup fun ν =>
      logAbsV (.inr w) (c l ν (j (.inr w))))) :=
    botOrZero_partitionSup _ _ fun l hl => botOrZero_finset_sup _ _ fun ν _ =>
      botOrZero_logAbsV fun hc => h ⟨(l, ν, j (.inr w)), Finset.mem_filter.mpr
        ⟨by simp [Nat.lt_succ_iff.mpr hl], hc⟩⟩
  rcases hbz with h0 | h0
  · exact absurd h0 (hne _)
  · simp [h0]

end Analysis

section Bridge

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open Stacks.ProjectiveSpaceChartRatio

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {K : Type u} [Field K]

/-- The integral-model chart `D₊(T_i)` pulled back along `t` is the pull-back of the chart of the
polynomial model. -/
private lemma chartOf_eq_preimage {Y : Scheme.{u}} {r : ℕ}
    (t : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (i : Fin (r + 1)) :
    chartOf t i = (t ≫ (polynomialComparison K r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K r) (MvPolynomial.X i) := by
  unfold chartOf
  conv_rhs => rw [← coordinateProjMap_preimage_basicOpen (k := K) (n := r) i,
    ← Scheme.Hom.comp_preimage, Category.assoc,
    polynomialComparison_iso_hom_comp_coordinateProjMap K r]

/-- `appLE` along equal morphisms. -/
private lemma appLE_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- Evaluating the germ of a section at a `K`-point. -/
private lemma stalkClosedPointTo_germ_eq {Y : Scheme.{u}} (q : Spec (.of K) ⟶ Y) (W : Y.Opens)
    (hq : q (closedPoint K) ∈ W) (hp : ⊤ ≤ q ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Scheme.stalkClosedPointTo q).hom (Y.presheaf.germ W _ hq x) =
      (Scheme.ΓSpecIso (.of K)).hom (q.appLE W ⊤ hp x) := by
  have h := congr($(Scheme.germ_stalkClosedPointTo q W hq) x)
  refine h.trans ?_
  simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.comp_apply]
  rfl

/-- **Chart values are the pulled-back ratios.** On the chart `D₊(Tᵢ)` containing the `K`-point
`q ≫ t`, its chart values in the polynomial model are the values of the ratios `T_j / T_i` of
the integral model. -/
private lemma chartVal_eq_ratioOf {Y : Scheme.{u}} {r : ℕ}
    (t : Y ⟶ projectiveSpaceOver r (Spec (.of K))) (q : Spec (.of K) ⟶ Y) (i : Fin (r + 1))
    (hi : ⊤ ≤ ((q ≫ t) ≫ (polynomialComparison K r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K r) (MvPolynomial.X i)) (j : Fin (r + 1)) :
    chartVal ((q ≫ t) ≫ (polynomialComparison K r).iso.hom) i hi j =
      (Scheme.stalkClosedPointTo q).hom (ratioOf t (q (closedPoint K)) j i) := by
  have hW : chartOf t i ≤ (t ≫ (polynomialComparison K r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K r) (MvPolynomial.X i) := (chartOf_eq_preimage t i).le
  have hp : ⊤ ≤ q ⁻¹ᵁ chartOf t i := by
    rw [chartOf_eq_preimage]; exact hi
  have hq0 : q (closedPoint K) ∈ chartOf t i :=
    hp (show closedPoint K ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
  rw [chartVal_eq_of_comp q (t ≫ (polynomialComparison K r).iso.hom) _ (Category.assoc _ _ _).symm
    i hi hW hp j]
  simp only [ratioOf, dif_pos hq0]
  refine Eq.trans ?_ (stalkClosedPointTo_germ_eq q _ hq0 hp _).symm
  congr 2
  have e : Proj.basicOpen (polyGrading K r) (MvPolynomial.X i) ≤
      coordinateProjMap K r (integralGradedHom K r) (mapDomain_integralGradedHom_eq_top K r) ⁻¹ᵁ
        Proj.basicOpen (polyGrading (ULift.{u} ℤ) r) (MvPolynomial.X i) :=
    (coordinateProjMap_preimage_basicOpen (k := K) (n := r) i).ge
  have key := appLE_awayToSection_coordinateProjMap (k := K) (n := r) i e
    (coordFracAt (ULift.{u} ℤ) r i j)
  rw [chartBaseChange_coordFracAt] at key
  rw [← key, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_congr (by rw [Category.assoc, polynomialComparison_iso_hom_comp_coordinateProjMap K r]),
    Scheme.Hom.app_eq_appLE]
  rfl

/-- **Coordinates of a `K`-point under a projective embedding.** A `K`-point `q` of `Y` has a
coordinate vector `a` for `φ` (in the sense of `IsCoordinatesOf`, read on the charts of the
integral model) whose logarithmic height computes the height `h_φ(q)`. -/
private lemma exists_isCoordinatesOf_height [NumberField K] {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of K)} [IsProjectiveVariety K f] [Smooth f] {r : ℕ}
    (φ : ProjectiveEmbedding f r) (q : Spec (.of K) ⟶ Y) (hq : q ≫ f = 𝟙 _) :
    ∃ a : Fin (r + 1) → K, IsCoordinatesOf φ.hom q a ∧
      φ.height ⟨q, hq⟩ = Height.logHeight a / finrank ℚ K := by
  have hw : ((q ≫ φ.hom) ≫ (polynomialComparison K r).iso.hom) ≫ projToSpecCoeff K r = 𝟙 _ := by
    rw [Category.assoc, Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff, Category.assoc]; erw [φ.hom_over]; rw [hq]
  obtain ⟨i, hi⟩ := exists_mem_basicOpen φ.hom (q.base default)
  have hi' : ⊤ ≤ ((q ≫ φ.hom) ≫ (polynomialComparison K r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading K r) (MvPolynomial.X i) := top_le_preimage_of_mem _ hi
  set a := chartVal ((q ≫ φ.hom) ≫ (polynomialComparison K r).iso.hom) i hi' with ha_def
  have ha0 : a ≠ 0 := chartVal_ne_zero _ i hi'
  refine ⟨a, ⟨ha0, fun j hj => ?_⟩, ?_⟩
  · have hjk : ⊤ ≤ ((q ≫ φ.hom) ≫ (polynomialComparison K r).iso.hom) ⁻¹ᵁ
        Proj.basicOpen (polyGrading K r) (MvPolynomial.X j) := by
      intro x _
      change _ ∈ Proj.basicOpen (polyGrading K r) (MvPolynomial.X j)
      rw [Proj.mem_basicOpen]
      intro hmem
      rw [mem_asHomogeneousIdeal_iff_eval_chartVal _ hw i hi'
        (MvPolynomial.isHomogeneous_X K j) x, MvPolynomial.eval_X] at hmem
      exact hj hmem
    have hmem : q (closedPoint K) ∈ chartOf φ.hom j := by
      rw [chartOf_eq_preimage]
      exact hjk (show closedPoint K ∈ (⊤ : (Spec (.of K)).Opens) from trivial)
    refine ⟨hmem, fun ν => ?_⟩
    rw [← chartVal_eq_ratioOf φ.hom q j hjk ν]
    have h1 := coordPoint_kPoint φ.hom φ.hom_over ⟨q, hq⟩ i hi'
    have h2 := coordPoint_kPoint φ.hom φ.hom_over ⟨q, hq⟩ j hjk
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp (h2.symm.trans h1)
    have hcj := congrFun hc j
    simp only [Pi.smul_apply, Units.smul_def, chartVal_self, smul_eq_mul] at hcj
    have hcν := congrFun hc ν
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hcν
    have hcj' : (c : K) * a j = 1 := hcj
    have hcν' : (c : K) * a ν =
        chartVal ((q ≫ φ.hom) ≫ (polynomialComparison K r).iso.hom) j hjk ν := hcν
    rw [← hcν', eq_div_iff hj]
    linear_combination (a ν) * hcj'
  · change weilHeight (coordPoint (kPoint φ.hom φ.hom_over ⟨q, hq⟩)) = _
    rw [coordPoint_kPoint φ.hom φ.hom_over ⟨q, hq⟩ i hi']
    rw [weilHeight_eq_sumLocalHeight (F := K) (y := a) (by simpa using ha0) (by simp [a]),
      sumLocalHeight_eq_logHeight ha0]

end Bridge

/-- Bombieri's Lemma 4 for given coordinate vectors of the points. -/
private theorem bound_of_coordinates {K : Type u} [Field K] [NumberField K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))]
    [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [IrreducibleSpace (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) : Scheme.{u})]
    {n m : ℕ} (φNP : C ⟶ projectiveSpaceOver n (Spec (.of K))) [φNP.IsOver (Spec (.of K))]
    [IsClosedImmersion φNP]
    (φB : pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ⟶ projectiveSpaceOver m (Spec (.of K)))
    [φB.IsOver (Spec (.of K))] [IsClosedImmersion φB]
    (s₀ : ℤ) (hs : 1 ≤ s₀) (N : ℕ) (hN : 0 < N) (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd : 1 ≤ d)
    (hδ₁ : d₁ + s₀ * d = N * δ₁) (hδ₂ : d₂ + s₀ * d = N * δ₂) (hδ₁pos : 0 < δ₁)
    (hδ₂pos : 0 < δ₂)
    (s : Γ(vojtaLineBundle (pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp)) φB
      δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of K), ⊤))
    (hF : IsVojtaRepresentative (pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp)) φB
      δ₁ δ₂ d s F)
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))]
    (ς : C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K)))
    (ς' : C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K)))
    (hς : maximalIdeal (C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K))) =
      Ideal.span {ς})
    (hς' : maximalIdeal (C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))) =
      Ideal.span {ς'})
    (i₁ i₂ : ℕ)
    (hadm : IsAdmissiblePair (pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp)) φB
      δ₁ δ₂ d s p
      ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
      ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
      i₁ i₂)
    (xNP : (Spec (.of K) ⟶ C) → Fin (n + 1) → K)
    (yB : (Spec (.of K) ⟶ C) × (Spec (.of K) ⟶ C) → Fin (m + 1) → K)
    (j₁ j₂ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1)) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    -- the chart `D₊(T_j)` of the integral model of `ℙʳ`, pulled back along `f`
    let chart : ∀ {Y : Scheme.{u}} {r : ℕ}, (Y ⟶ projectiveSpaceOver r (Spec (.of K))) →
        Fin (r + 1) → Y.Opens := fun {_ r} f j =>
      (f ≫ projectiveSpaceOver.toIntegralAtUniverse r _) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
    -- the germ at `y` of the pull-back along `f` of `T_ν / T_j` (zero off the chart)
    let ratio : ∀ {Y : Scheme.{u}} {r : ℕ}, (Y ⟶ projectiveSpaceOver r (Spec (.of K))) →
        ∀ y : Y, Fin (r + 1) → Fin (r + 1) → Y.presheaf.stalk y := fun {Y r} f y ν j =>
      haveI := Classical.propDecidable (y ∈ chart f j)
      if h : y ∈ chart f j then
        Y.presheaf.germ (chart f j) y h
          ((f ≫ projectiveSpaceOver.toIntegralAtUniverse r _).app _
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk _
                (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))
      else 0
    -- the nonzero vector `a` is a coordinate vector of the `K`-point `q ≫ f` of `ℙʳ`
    let IsCoordinates : ∀ {Y : Scheme.{u}} {r : ℕ}, (Y ⟶ projectiveSpaceOver r (Spec (.of K))) →
        (Spec (.of K) ⟶ Y) → (Fin (r + 1) → K) → Prop := fun {_ _} f q a =>
      a ≠ 0 ∧ ∀ j, a j ≠ 0 → q (closedPoint K) ∈ chart f j ∧
        ∀ ν, (Scheme.stalkClosedPointTo q).hom (ratio f (q (closedPoint K)) ν j) = a ν / a j
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
          logAbs v (taylorCoeff q ϖ (ratio φNP (q (closedPoint K)) ν (j v)) l)).sum
    let z := p ≫ pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
    let w := p ≫ pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
    -- `h(F)`: the absolute height of the vector of all coefficients of all `F_i`
    let hF : ℝ := Height.logHeight (fun c : Σ i, (F i).support =>
        (Scheme.ΓSpecIso (.of K)).hom ((F c.1).coeff c.2)) / finrank ℚ K
    IsCoordinates φNP z (xNP z) → IsCoordinates φNP w (xNP w) → IsCoordinates φB p (yB (z, w)) →
    (∀ v, z (closedPoint K) ∈ chart φNP (j₁ v)) → (∀ v, w (closedPoint K) ∈ chart φNP (j₂ v)) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo z).hom
      (ratio φNP (z (closedPoint K)) ν (j₁ v))) ≤ 0) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo w).hom
      (ratio φNP (w (closedPoint K)) ν (j₂ v))) ≤ 0) →
    (((-hF - n * Real.log ((δ₁ + n) * (δ₂ + n)) : ℝ) : EReal)
        - ∑ᶠ v, partitionTerm z ς i₁ j₁ v - ∑ᶠ v, partitionTerm w ς' i₂ j₂ v
        - ((δ₁ + δ₂ + i₁ + i₂ : ℕ) : EReal) ≤
      ((oldVojtaHeight s₀ N (fun q => Height.logHeight (xNP q) / finrank ℚ K)
        (fun q => Height.logHeight (yB q) / finrank ℚ K) d₁ d₂ d (z, w) : ℝ) : EReal)) := by
  intro chart ratio IsCoordinates logAbs partitionTerm z w hFt hcz hcw hcp hj₁ hj₂ hjv hjv'
  classical
  have hcz' : IsCoordinatesOf φNP z (xNP z) := hcz
  have hcw' : IsCoordinatesOf φNP w (xNP w) := hcw
  have hcp' : IsCoordinatesOf φB p (yB (z, w)) := hcp
  have hj₁' : ∀ v, z (closedPoint K) ∈ chartOf φNP (j₁ v) := hj₁
  have hj₂' : ∀ v, w (closedPoint K) ∈ chartOf φNP (j₂ v) := hj₂
  haveI : Smooth (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ↘ Spec (.of K)) := by
    change Smooth (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ≫ (C ↘ Spec (.of K)))
    infer_instance
  haveI := isRegularLocalRing_stalk
    (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ↘ Spec (.of K)) p (comp_over_eq_id p)
  have hpb := IsPullback.of_hasPullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
  have hm := maximalIdeal_stalk_pullback hpb pullback.condition p hς hς'
  have hdim := ringKrullDim_stalk_pullback hpb pullback.condition p hς hς'
  obtain ⟨i₀, j₀, j₀', hx₀, g₀, hg₀, hb, hvanish⟩ := hadm
  have hψ₁ : pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp) ≫
      pullback.fst (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
      pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ≫ φNP := pullback.lift_fst _ _ _
  have hψ₂ : pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp) ≫
      pullback.snd (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
      pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ≫ φNP := pullback.lift_snd _ _ _
  have hz₀ : z (closedPoint K) ∈ chartOf φNP j₀ := by
    have := hx₀.2.1; rw [hψ₁] at this; exact this
  have hw₀ : w (closedPoint K) ∈ chartOf φNP j₀' := by
    have := hx₀.2.2; rw [hψ₂] at this; exact this
  have hp₀ : p (closedPoint K) ∈ chartOf φB i₀ := hx₀.1
  set x := xNP z with hx_def
  set x' := xNP w with hx'_def
  set y := yB (z, w) with hy_def
  have hy₀ : y i₀ ≠ 0 := hcp'.ne_zero hp₀
  have hx₀' : x j₀ ≠ 0 := hcz'.ne_zero hz₀
  have hx₀'' : x' j₀' ≠ 0 := hcw'.ne_zero hw₀
  let a : Γ(Spec (.of K), ⊤) → K := fun t => (Scheme.ΓSpecIso (.of K)).hom t
  let cX : Γ(Spec (.of K), ⊤) →+*
      (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk (p (closedPoint K)) :=
    (const (p (closedPoint K))).comp (Scheme.ΓSpecIso (.of K)).hom.hom
  let A : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ) → K := fun j e =>
    taylorCoeff z ς (∏ ν, ratioOf φNP (z (closedPoint K)) ν j ^ e (Sum.inl ν)) i₁
  let B : Fin (n + 1) → (Fin (n + 1) ⊕ Fin (n + 1) →₀ ℕ) → K := fun j e =>
    taylorCoeff w ς' (∏ ν, ratioOf φNP (w (closedPoint K)) ν j ^ e (Sum.inr ν)) i₂
  let D : Fin (m + 1) → Fin (n + 1) → Fin (n + 1) → K := fun i j j' =>
    ∑ e ∈ (F i).support, a ((F i).coeff e) * (A j e * B j' e)
  have hVF : ∀ i j j', p (closedPoint K) ∈ chartOf φB i → z (closedPoint K) ∈ chartOf φNP j →
      w (closedPoint K) ∈ chartOf φNP j' →
      taylorCoeff₂ p
          ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
          ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
          g₀ i₁ i₂ =
        (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j₀') ^ δ₂ *
          taylorCoeff₂ p
            ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
            ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
            ((F i).eval₂ cX (Sum.elim
              (fun ν => (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
                (p (closedPoint K)) (ratioOf φNP (z (closedPoint K)) ν j))
              (fun ν => (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap
                (p (closedPoint K)) (ratioOf φNP (w (closedPoint K)) ν j')))) i₁ i₂ := by
    intro i j j' hpi hzj hwj'
    have hstruct : pullback.map _ _ _ _ φNP φNP (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) ≫
        (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
        pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ↘ Spec (.of K) := by
      rw [← Category.assoc, hψ₁, Category.assoc, comp_over φNP (Spec (.of K)),
        pullback.condition]
      rfl
    refine (taylorCoeff₂_eq_mul_taylorCoeff₂_eval₂ _ φB δ₁ δ₂ d s F hF p hdim hm
      i₀ i j₀ j₀'
      j j' hx₀ ⟨hpi, by rw [hψ₁]; exact hzj, by rw [hψ₂]; exact hwj'⟩ g₀ hg₀ i₁ i₂ hvanish
      x x' y ⟨hcz'.1, fun k hk ν => (hcz'.eq_mul_comp (pullback.fst _ _) φNP _ hψ₁ p hk ν).trans
        (congrArg _ (congrArg _ (germ_app_eq_ratioOf _ _ _ _ hk).symm))⟩
      ⟨hcw'.1, fun k hk ν => (hcw'.eq_mul_comp (pullback.snd _ _) φNP _ hψ₂ p hk ν).trans
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
      taylorCoeff₂ p
          ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς)
          ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap (p (closedPoint K)) ς')
          g₀ i₁ i₂ =
        (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j₀') ^ δ₂ * D i j j' := by
    intro i j j' hi hj hj'
    rw [hVF i j j' (hcp'.2 i hi).1 (hcz'.2 j hj).1 (hcw'.2 j' hj').1]
    exact congrArg _ (taylorCoeff₂_eval₂_sumElim p hς hς' (F i) cX a (fun t => rfl) _ _ i₁ i₂)
  haveI : z.IsOver (Spec (.of K)) := ⟨by
    change (p ≫ pullback.fst _ _) ≫ _ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact comp_over p (Spec (.of K))⟩
  haveI : w.IsOver (Spec (.of K)) := ⟨by
    change (p ≫ pullback.snd _ _) ≫ _ = _
    rw [Category.assoc]
    exact comp_over p (Spec (.of K))⟩
  let coef : (Σ i, (F i).support) → K := fun c =>
    (Scheme.ΓSpecIso (.of K)).hom ((F c.1).coeff c.2)
  let G : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v => wt v * Real.log (⨆ c, absV v (coef c))
  let M : ℕ := ((δ₁ + 1) * (δ₂ + 1)) ^ n
  let Pv : InfinitePlace K ⊕ FinitePlace K → EReal := fun v => partitionTerm z ς i₁ j₁ v
  let Pv' : InfinitePlace K ⊕ FinitePlace K → EReal := fun v => partitionTerm w ς' i₂ j₂ v
  let R : InfinitePlace K ⊕ FinitePlace K → ℝ := fun v =>
    archLog v M + G v + ((Pv v).toReal + archLog v ((2 : ℝ) ^ (δ₁ + i₁))) +
      ((Pv' v).toReal + archLog v ((2 : ℝ) ^ (δ₂ + i₂)))
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
      Pv v ≠ ⊥ ∧ Pv' v ≠ ⊥ ∧ wt v * Real.log (absV v (D i (j₁ v) (j₂ v))) ≤ R v := by
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
  have hPf : (Function.support fun w : FinitePlace K => (Pv (.inr w)).toReal).Finite :=
    finite_support_partitionSup i₁
      (fun l ν k => taylorCoeff z ς (ratioOf φNP (z (closedPoint K)) ν k) l) j₁ hPne
  have hPf' : (Function.support fun w' : FinitePlace K => (Pv' (.inr w')).toReal).Finite :=
    finite_support_partitionSup i₂
      (fun l ν k => taylorCoeff w ς' (ratioOf φNP (w (closedPoint K)) ν k) l) j₂ hPne'
  have hGf : (Function.support fun w' : FinitePlace K => G (.inr w')).Finite :=
    (hasFiniteSupport_log_iSup hcoef₀).subset (Function.support_mul_subset_right _ _)
  have hAf : ∀ M' : ℝ, (Function.support fun w' : FinitePlace K =>
      archLog (.inr w') M').Finite := fun M' => by simp [archLog_inr]
  have hRf : (Function.support fun w' : FinitePlace K => R (.inr w')).Finite := by
    refine ((hGf.union hPf).union hPf').subset fun w' hw' => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    apply hw'
    simp only [R, archLog_inr, h.1.1, h.1.2, h.2]
    ring
  have hmain := neg_finsum_le_localExpression hcp'.1 δ₁ δ₂ d hb hy₀ hx₀' hx₀'' D hval j₁ j₂
    hx₁ hx₂ R (fun v i hi => (key v i hi).2.2) hRf
  have hloc := vojtaHeight_eq_sum_iInf_iSup_log K xNP yB s₀ hs N hN d₁ d₂ d
    (by exact_mod_cast hd) δ₁ δ₂ hδ₁ hδ₂ hδ₁pos hδ₂pos z w hcz'.1 hcw'.1 hcp'.1
  rw [← hloc] at hmain
  have fin_add : ∀ {u u' : InfinitePlace K ⊕ FinitePlace K → ℝ}, (Function.support u).Finite →
      (Function.support u').Finite → (Function.support fun v => u v + u' v).Finite :=
    fun hu hu' => (hu.union hu').subset (Function.support_add _ _)
  have h1 := finite_support_of_inr (f := fun v => archLog v (M : ℝ)) (hAf (M : ℝ))
  have h2 := finite_support_of_inr (f := G) hGf
  have h3 := finite_support_of_inr (f := fun v => (Pv v).toReal) hPf
  have h4 := finite_support_of_inr (f := fun v => archLog v ((2 : ℝ) ^ (δ₁ + i₁)))
    (hAf ((2 : ℝ) ^ (δ₁ + i₁)))
  have h5 := finite_support_of_inr (f := fun v => (Pv' v).toReal) hPf'
  have h6 := finite_support_of_inr (f := fun v => archLog v ((2 : ℝ) ^ (δ₂ + i₂)))
    (hAf ((2 : ℝ) ^ (δ₂ + i₂)))
  have hR : ∑ᶠ v, R v = ((∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v (M : ℝ)) +
        ∑ᶠ v, G v) +
      ((∑ᶠ v, (Pv v).toReal) +
        ∑ᶠ v : InfinitePlace K ⊕ FinitePlace K, archLog v ((2 : ℝ) ^ (δ₁ + i₁))) +
      ((∑ᶠ v, (Pv' v).toReal) +
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
  have hP1 : ∑ᶠ v, partitionTerm z ς i₁ j₁ v = ((∑ᶠ v, (Pv v).toReal : ℝ) : EReal) := by
    rw [← finsum_coe_ereal _ h3]
    exact finsum_congr fun v => (EReal.coe_toReal (hPtop v) (hPne v)).symm
  have hP2 : ∑ᶠ v, partitionTerm w ς' i₂ j₂ v = ((∑ᶠ v, (Pv' v).toReal : ℝ) : EReal) := by
    rw [← finsum_coe_ereal _ h5]
    exact finsum_congr fun v => (EReal.coe_toReal (hPtop' v) (hPne' v)).symm
  rw [hP1, hP2, ← EReal.coe_natCast, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  push_cast at h2s h2s' ⊢
  linarith only [hmain, hR, hGs, hMs, h2s, h2s', hlogM]

/-- Two `Over` structures with the same structure morphism are equal. -/
private lemma over_ext {Y S : Scheme.{u}} {i₁ i₂ : Y.Over S}
    (h : (@OverClass.hom _ _ Y S i₁) = (@OverClass.hom _ _ Y S i₂)) : i₁ = i₂ := by
  cases i₁; cases i₂; cases h; rfl

/-- Admissibility only sees the structure morphism through the `Over` instance. -/
private lemma isAdmissiblePair_of_over_eq {S Y : Scheme.{u}} {n m : ℕ}
    {ψ : Y ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)}
    {φ : Y ⟶ projectiveSpaceOver m S} {δ₁ δ₂ d : ℤ} [IrreducibleSpace Y]
    {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)} {K : Type u} [Field K] {i₁ i₂ : Y.Over (Spec (.of K))}
    (h : i₁ = i₂) {p : Spec (.of K) ⟶ Y} {ς ς' : Y.presheaf.stalk (p (closedPoint K))}
    {a b : ℕ} (ha : @IsAdmissiblePair S Y n m ψ φ δ₁ δ₂ d _ s K _ i₁ p ς ς' a b) :
    @IsAdmissiblePair S Y n m ψ φ δ₁ δ₂ d _ s K _ i₂ p ς ς' a b := by
  subst h; exact ha

end Faltings.BombieriVojta.HeightLowerBound

namespace Faltings.BombieriVojta

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

open HeightLowerBound in
/-- **Bombieri's Lemma 4.** Let `X = (C, P)` be a curve over a number field `K` with a divisor of
degree one, `φNP`, `φB` the embeddings of `C` and `C ×_K C` by bases of the global sections of
invertible sheaves of classes `N • [𝒪(P)]` (`2g + 1 ≤ N`) and `vojtaClass X s s (-1)`, and
`ψ = φNP × φNP`. Let `s` be a global section of `vojtaLineBundle ψ φB δ₁ δ₂ d` with
representative `F` (`IsVojtaRepresentative`), `p = (z, w)` a `K`-point of `C ×_K C`, `ς`, `ς'`
uniformizers at `z`, `w`, and `(i₁, i₂)` admissible (`IsAdmissiblePair`) for `s` at `p` with
respect to `ς ∘ pr₁`, `ς' ∘ pr₂`. Then `vojtaHeight X φNP φB s N d₁ d₂ d z w` is at least
`-h(F) - n log((δ₁ + n)(δ₂ + n))` minus, for each of `(z, ς, i₁, j_v)` and `(w, ς', i₂, j'_v)`,
the sum over the places `v` of `max_{i_λ} ∑_λ max_ν log |taylorCoeff ς ξ_{ν j_v} i_λ|_v` over the
partitions `(i_λ)`, minus `δ₁ + δ₂ + i₁ + i₂`; here `ξ_{νj} = x_ν / x_j` and
`|ξ_{ν j_v}(z)|_v ≤ 1` for every `ν`. -/
@[faltings "thm_bv_lower_bound_height_vojta"]
public theorem vojtaHeight_ge_of_isAdmissiblePair {K : Type u} [Field K] [NumberField K]
    (X : CurveWithDegreeOneDivisor K) {n m : ℕ}
    (φNP : ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback K X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve K X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (s₀ : ℤ) (hs : 1 ≤ s₀)
    (M : (pullback X.f X.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      X.vojtaClass s₀ s₀ (-1))
    (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd : 1 ≤ d)
    (hδ₁ : d₁ + s₀ * d = N * δ₁) (hδ₂ : d₂ + s₀ * d = N * δ₂) (hδ₁pos : 0 < δ₁)
    (hδ₂pos : 0 < δ₂) :
    letI : X.C.Over (Spec (.of K)) := ⟨X.f⟩
    letI : (pullback X.f X.f).Over (Spec (.of K)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
    haveI := (IsSmoothProjectiveCurve.surface_pullback K X.f X.f).1
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    -- `ψ = φ_{NP} × φ_{NP}`
    let ψ := pullback.map X.f X.f _ _ φNP.hom φNP.hom (𝟙 _) (by simp [φNP.hom_over])
      (by simp [φNP.hom_over])
    -- the chart `D₊(T_j)` of the integral model of `ℙⁿ`, pulled back to `C`
    let chart : Fin (n + 1) → X.C.Opens := fun j =>
      (φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X j)
    -- the germ at `c` of `ξ_{νj} = x_ν / x_j`, the pull-back of `T_ν / T_j` (zero off the chart)
    let ξ : ∀ c : X.C, Fin (n + 1) → Fin (n + 1) → X.C.presheaf.stalk c := fun c ν j =>
      haveI := Classical.propDecidable (c ∈ chart j)
      if h : c ∈ chart j then
        X.C.presheaf.germ (chart j) c h
          ((φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk _
                (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν))))
      else 0
    -- Bombieri's normalised `log |a|_v`, with `log 0 = ⊥`
    let logAbs : InfinitePlace K ⊕ FinitePlace K → K → EReal := fun v a =>
      haveI := Classical.propDecidable (a = 0)
      if a = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w a))
          (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w a)) v : ℝ) : EReal)
    -- the `v`-term `max_{i_λ} ∑_λ max_ν log |∂_{i_λ} ξ_{ν j_v}(q)|_v` at the `K`-point `q` of `C`
    let partitionTerm : ∀ q : Spec (.of K) ⟶ X.C, X.C.presheaf.stalk (q (closedPoint K)) → ℕ →
        (InfinitePlace K ⊕ FinitePlace K → Fin (n + 1)) →
        InfinitePlace K ⊕ FinitePlace K → EReal := fun q ϖ i j v =>
      (Finset.univ : Finset (Nat.Partition i)).sup fun π =>
        (π.parts.map fun l => Finset.univ.sup fun ν : Fin (n + 1) =>
          logAbs v (taylorCoeff q ϖ (ξ (q (closedPoint K)) ν (j v)) l)).sum
    ∀ (x : Module.Basis (Fin (n + 1)) K Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
      φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f →
    ∀ (y : Module.Basis (Fin (m + 1)) K Γ(M, ⊤))
      (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y),
      φB.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
        (pullback.fst X.f X.f ≫ X.f) →
    ∀ (s : Γ(vojtaLineBundle ψ φB.hom δ₁ δ₂ d, ⊤))
      (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of K), ⊤)),
      IsVojtaRepresentative ψ φB.hom δ₁ δ₂ d s F →
    ∀ (p : Spec (.of K) ⟶ pullback X.f X.f) (hp : p ≫ pullback.fst X.f X.f ≫ X.f = 𝟙 _)
      (ς : X.C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K)))
      (ς' : X.C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))),
      maximalIdeal (X.C.presheaf.stalk ((p ≫ pullback.fst _ _) (closedPoint K))) =
        Ideal.span {ς} →
      maximalIdeal (X.C.presheaf.stalk ((p ≫ pullback.snd _ _) (closedPoint K))) =
        Ideal.span {ς'} →
    ∀ i₁ i₂ : ℕ, IsAdmissiblePair ψ φB.hom δ₁ δ₂ d s p
      ((pullback.fst X.f X.f).stalkMap (p (closedPoint K)) ς)
      ((pullback.snd X.f X.f).stalkMap (p (closedPoint K)) ς') i₁ i₂ →
    ∀ j₁ j₂ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1),
    let z := p ≫ pullback.fst X.f X.f
    let w := p ≫ pullback.snd X.f X.f
    (∀ v, z (closedPoint K) ∈ chart (j₁ v)) → (∀ v, w (closedPoint K) ∈ chart (j₂ v)) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo z).hom (ξ (z (closedPoint K)) ν (j₁ v))) ≤ 0) →
    (∀ v ν, logAbs v ((Scheme.stalkClosedPointTo w).hom (ξ (w (closedPoint K)) ν (j₂ v))) ≤ 0) →
    -- `h(F)`: the absolute height of the vector of all coefficients of all `F_i`
    let heightF : ℝ := Height.logHeight (fun c : Σ i, (F i).support =>
        (Scheme.ΓSpecIso (.of K)).hom ((F c.1).coeff c.2)) / finrank ℚ K
    (((-heightF - n * Real.log ((δ₁ + n) * (δ₂ + n)) : ℝ) : EReal)
        - ∑ᶠ v, partitionTerm z ς i₁ j₁ v - ∑ᶠ v, partitionTerm w ς' i₂ j₂ v
        - ((δ₁ + δ₂ + i₁ + i₂ : ℕ) : EReal) ≤
      ((X.vojtaHeight φNP φB s₀ N d₁ d₂ d ⟨z, by simpa [z] using hp⟩
        ⟨w, by simpa [w, pullback.condition] using hp⟩ : ℝ) : EReal)) := by
  intro ψ chart ξ logAbs partitionTerm x hx hxφ y hy hyφ s F hF p hp ς ς' hς hς' i₁ i₂ hadm
    j₁ j₂ z w hj₁ hj₂ hjv hjv' heightF
  classical
  letI : X.C.Over (Spec (.of K)) := ⟨X.f⟩
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve K X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  haveI hproj := (IsSmoothProjectiveCurve.surface_pullback K X.f X.f).1
  haveI : Smooth (pullback.fst X.f X.f ≫ X.f) := by
    haveI := (IsSmoothProjectiveCurve.surface_pullback K X.f X.f).2.2
    exact SmoothOfRelativeDimension.smooth 2 _
  haveI : IrreducibleSpace (pullback X.f X.f : Scheme.{u}) := by
    haveI := hproj.toIsIntegral; infer_instance
  haveI : IsCurve K (X.C ↘ Spec (.of K)) := ‹IsCurve K X.f›
  haveI : Smooth (X.C ↘ Spec (.of K)) := ‹Smooth X.f›
  haveI : IrreducibleSpace (pullback (X.C ↘ Spec (.of K)) (X.C ↘ Spec (.of K)) : Scheme.{u}) :=
    ‹IrreducibleSpace (pullback X.f X.f : Scheme.{u})›
  haveI : φNP.hom.IsOver (Spec (.of K)) := ⟨φNP.hom_over⟩
  haveI : IsClosedImmersion φNP.hom := φNP.isClosedImmersion
  haveI : IsClosedImmersion φB.hom := φB.isClosedImmersion
  have hzf : z ≫ X.f = 𝟙 _ := by simpa [z] using hp
  have hwf : w ≫ X.f = 𝟙 _ := by simpa [w, pullback.condition] using hp
  have hlift : pullback.lift z w (hzf.trans hwf.symm) = p :=
    pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hpf : pullback.lift z w (hzf.trans hwf.symm) ≫ pullback.fst X.f X.f ≫ X.f = 𝟙 _ := by
    rwa [hlift]
  obtain ⟨xz, hxz, hhz⟩ := exists_isCoordinatesOf_height φNP z hzf
  obtain ⟨xw, hxw, hhw⟩ := exists_isCoordinatesOf_height φNP w hwf
  obtain ⟨yp, hyp, hhp⟩ := exists_isCoordinatesOf_height φB _ hpf
  rw [hlift] at hyp
  let xNP : (Spec (.of K) ⟶ X.C) → Fin (n + 1) → K := fun q => if q = z then xz else xw
  let yB : (Spec (.of K) ⟶ X.C) × (Spec (.of K) ⟶ X.C) → Fin (m + 1) → K := fun _ => yp
  have hcz : IsCoordinatesOf φNP.hom z (xNP z) := by simpa [xNP] using hxz
  have hcw : IsCoordinatesOf φNP.hom w (xNP w) := by
    by_cases h : w = z
    · simp only [xNP, if_pos h]; rw [h]; exact hxz
    · simp only [xNP, if_neg h]; exact hxw
  have hhw' : φNP.height ⟨w, hwf⟩ = Height.logHeight (xNP w) / finrank ℚ K := by
    by_cases h : w = z
    · simp only [xNP, if_pos h]
      rw [← hhz]; congr 1; exact Subtype.ext h
    · simp only [xNP, if_neg h]; exact hhw
  have hhz' : φNP.height ⟨z, hzf⟩ = Height.logHeight (xNP z) / finrank ℚ K := by
    simpa [xNP] using hhz
  have hcan : (pullback (X.C ↘ Spec (.of K)) (X.C ↘ Spec (.of K))) ↘ Spec (.of K) =
      pullback.fst X.f X.f ≫ X.f := by
    first | rfl | exact pullback.condition | exact pullback.condition.symm
  haveI : Scheme.Hom.IsOver (X := pullback (X.C ↘ Spec (.of K)) (X.C ↘ Spec (.of K)))
      φB.hom (Spec (.of K)) := ⟨by rw [hcan]; exact φB.hom_over⟩
  haveI : Scheme.Hom.IsOver (Y := pullback (X.C ↘ Spec (.of K)) (X.C ↘ Spec (.of K)))
      p (Spec (.of K)) := ⟨by
    rw [hcan]
    refine hp.trans ?_
    change _ = Spec.map (CommRingCat.ofHom (algebraMap K K))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩
  haveI : IsClosedImmersion (X := pullback (X.C ↘ Spec (.of K)) (X.C ↘ Spec (.of K))) φB.hom :=
    φB.isClosedImmersion
  have hadm' := isAdmissiblePair_of_over_eq (over_ext hcan.symm) hadm
  have key := bound_of_coordinates (C := X.C) φNP.hom φB.hom s₀ hs N (by omega) d₁ d₂ δ₁ δ₂ d
    hd hδ₁ hδ₂ hδ₁pos hδ₂pos s F hF p ς ς' hς hς' i₁ i₂ hadm' xNP yB j₁ j₂ hcz hcw hyp hj₁ hj₂
    hjv hjv'
  have heq : X.vojtaHeight φNP φB s₀ N d₁ d₂ d ⟨z, hzf⟩ ⟨w, hwf⟩ =
      oldVojtaHeight s₀ N (fun q => Height.logHeight (xNP q) / finrank ℚ K)
        (fun q => Height.logHeight (yB q) / finrank ℚ K) d₁ d₂ d (z, w) := by
    simp only [CurveWithDegreeOneDivisor.vojtaHeight, oldVojtaHeight]
    rw [hhz', hhw', hhp]
  rw [heq]
  exact key

end Faltings.BombieriVojta
