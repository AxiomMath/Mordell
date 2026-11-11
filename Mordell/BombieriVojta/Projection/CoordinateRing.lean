module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic
public import Mordell.BombieriVojta.Projection.GenericBasis
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# The coordinate ring of `U` is free over `k[ξ_a]`

Let `C` be the curve of Bombieri's Sections 8 and 9: a smooth projective geometrically irreducible
curve of genus `g ≥ 2` over a number field `k`, with a rational point `P`, `N ≥ 2g + 1`, and
`x₀, …, xₙ` a `k`-basis of `H⁰(C, 𝒪(NP))` whose morphism `φ_{NP} : C → ℙⁿ` is an embedding. Let
`U = {x₀ ≠ 0}` (`Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)`) and, for `a ∈ {1, …, n}`, let
`ξ_a = x_a / x₀`, a regular function on `U`. If `x₀` and `x_a` have no common zero on `C`
(condition (G1)), then the projection
`π_a = (x₀ : x_a) : C → ℙ¹` is finite, `U = π_a⁻¹(𝔸¹)`, and `k[U] = Γ(C, U)` is a free
`k[ξ_a]`-module of rank `N = [k(C) : k(ξ_a)]`.

## Main results

* `Faltings.BombieriSiegel.free_and_finrank_affineOpen`: under (G1), `Γ(C, U)` is a free module of
  rank `N` over the polynomial ring `k[X]` acting through `X ↦ ξ_a`.

## Implementation notes

The regular function `ξ_a = x_a / x₀` on `U` is characterised by `x_a|_U = ξ_a • x₀|_U` in
`Γ(L, U)`; since `x₀` generates `L` on `U`, this determines it, and the statement is made for every
`ξ` satisfying this relation. The ring `k[ξ_a]` is the polynomial ring `k[X]`, acting on `Γ(C, U)`
through `Polynomial.aeval ξ_a`; freeness of positive rank forces `ξ_a` to be transcendental, so
this is the same as freeness over the subalgebra `k[ξ_a] ⊆ Γ(C, U)`. Condition (G1) is stated for
the sections `x_ν` of `L ≅ 𝒪(NP)`: for each `b ∈ {1, …, n}`, the nonvanishing loci of `x₀` and
`x_b` cover `C`. The index `a ∈ {1, …, n}` is `a.succ` for `a : Fin n`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 629
-/

namespace Faltings.BombieriSiegel

open CategoryTheory AlgebraicGeometry Polynomial

universe u

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

/-! ### Two facts of commutative algebra -/

/-- A finite module over `k[X]`, acting on a domain `B` through `X ↦ ξ` with `ξ` transcendental,
is free, of rank `dim_k B / ξB`. -/
private theorem free_and_finrank_eq {k B : Type*} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] (ξ : B) (hξ : Transcendental k ξ)
    (hfin : letI := (aeval (R := k) ξ).toRingHom.toAlgebra; Module.Finite k[X] B) :
    letI := (aeval (R := k) ξ).toRingHom.toAlgebra
    Module.Free k[X] B ∧ Module.finrank k[X] B = Module.finrank k (B ⧸ Ideal.span {ξ}) := by
  let := (aeval (R := k) ξ).toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap k[X] B) := (transcendental_iff_injective).mp hξ
  have : Module.IsTorsionFree k[X] B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, ?_⟩
  have hsm : ∀ (p : k[X]) (m : B), p • m = aeval ξ p * m := fun _ _ => rfl
  have hCsm : ∀ (c : k) (m : B), (C c : k[X]) • m = c • m := fun c m => by
    rw [hsm, aeval_C, Algebra.smul_def]
  set r := Module.finrank k[X] B
  let b := Module.finBasis k[X] B
  let Φ : B →ₗ[k] (Fin r → k) :=
    { toFun := fun m i => (b.repr m i).eval 0
      map_add' := fun m m' => by ext i; simp
      map_smul' := fun c m => by
        ext i
        rw [← hCsm, map_smul]
        simp }
  have hsurj : Function.Surjective Φ := by
    intro v
    refine ⟨∑ i, (C (v i) : k[X]) • b i, ?_⟩
    ext i
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, b.repr_self,
      Finsupp.smul_single, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_one]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (fun h => absurd (Finset.mem_univ i) h)]
    simp
  have hker : LinearMap.ker Φ = (Ideal.span {ξ}).restrictScalars k := by
    ext m
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hm
      have hdvd : ∀ i, (Polynomial.X : k[X]) ∣ b.repr m i := fun i => by
        rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact congrFun hm i
      choose q hq using hdvd
      refine ⟨∑ i, q i • b i, ?_⟩
      conv_rhs => rw [← b.sum_repr m]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsm, hsm, hq i, map_mul, aeval_X]
      ring
    · rintro ⟨m', rfl⟩
      ext i
      have : m' * ξ = (Polynomial.X : k[X]) • m' := by rw [hsm, aeval_X, mul_comm]
      simp [Φ, this]
  have e := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {ξ})).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj))
  rw [e.finrank_eq, Module.finrank_fin_fun]

/-- An element of a domain that is algebraic over a field is zero or a unit. -/
private theorem eq_zero_or_isUnit_of_isAlgebraic {k B : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] {ξ : B} (h : IsAlgebraic k ξ) : ξ = 0 ∨ IsUnit ξ := by
  by_cases h0 : ξ = 0
  · exact Or.inl h0
  right
  set p := minpoly k ξ
  have hc : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero h.isIntegral h0
  have hp : aeval ξ p = 0 := minpoly.aeval k ξ
  rw [← X_mul_divX_add p, map_add, map_mul, aeval_X, aeval_C] at hp
  refine isUnit_iff_exists_inv.mpr ⟨algebraMap k B (-(p.coeff 0)⁻¹) * aeval ξ p.divX, ?_⟩
  rw [mul_left_comm, eq_neg_of_add_eq_zero_left hp, mul_neg, ← map_mul, neg_mul,
    inv_mul_cancel₀ hc, map_neg, map_one, neg_neg]

/-! ### The projection `π_a` is finite over the chart `𝔸¹` -/

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceChartRatio
  Stacks.AlgebraicGeometry.ProjPolyChart in
/-- Let `s₀, s₁` be generating sections of an invertible module `L` on a proper curve `C` over
`k`, with `C_{s₀} ≠ C` nonempty, and `ξ = s₁ / s₀` on `C_{s₀}`. Then `C_{s₀}` is affine and
`Γ(C, C_{s₀})` is finite over `k[X]` acting through `X ↦ ξ`: it is the preimage of the chart
`𝔸¹ = D₊(T₀)` under the finite morphism `(s₀ : s₁) : C → ℙ¹_k`. -/
private theorem isAffineOpen_and_finite_aeval {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L] (s : Fin 2 → Γ(L, ⊤))
    (hs : GeneratesStalks s)
    (hU : nvCover s 0 ≠ ⊤) (hU' : (nvCover s 0 : Set C).Nonempty)
    (ξ : Γ(C, nvCover s 0))
    (hξ : L.presheaf.map (homOfLE (le_top : nvCover s 0 ≤ ⊤)).op (s 1) =
      ξ • L.presheaf.map (homOfLE (le_top : nvCover s 0 ≤ ⊤)).op (s 0)) :
    letI : Algebra k Γ(C, nvCover s 0) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        C.presheaf.map (homOfLE (le_top : nvCover s 0 ≤ ⊤)).op).hom.toAlgebra
    IsAffineOpen (nvCover s 0) ∧ (aeval (R := k) ξ).toRingHom.Finite := by
  let : Algebra k Γ(C, nvCover s 0) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        C.presheaf.map (homOfLE (le_top : nvCover s 0 ≤ ⊤)).op).hom.toAlgebra
  set ψ := toPolynomialModel s hs f with hψ
  set D0 := Proj.basicOpen (polyGrading k 1) (MvPolynomial.X (0 : Fin 2)) with hD0def
  have hpre : ψ ⁻¹ᵁ D0 = nvCover s 0 := by
    have h := preimage_basicOpen_eq_nvCover_canonical s hs 0
    rw [← toPolynomialModel_comp_coordinateProjMap s hs f] at h
    rwa [hD0def, ← coordinateProjMap_preimage_basicOpen k 1 0, ← Scheme.Hom.comp_preimage]
  have hprop : IsProper ψ := by
    have h1 : IsProper (toProjectiveSpaceOver s hs f) := by
      have : IsProper (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
        isProper_projectiveSpaceOver 1 _
      have : IsProper (toProjectiveSpaceOver s hs f ≫
          (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) := by
        rw [show toProjectiveSpaceOver s hs f ≫
          (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f from
          toProjectiveSpaceOver_fst s hs f]
        infer_instance
      exact IsProper.of_comp _ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    rw [hψ]
    unfold toPolynomialModel
    infer_instance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := {}
  have : TopologicalSpace.NoetherianSpace C := IsNoetherian.noetherianSpace
  have hdim : topologicalKrullDim C ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hne : ¬ (Set.range ψ).Subsingleton := by
    intro hsub
    obtain ⟨y, hy⟩ := hU'
    apply hU
    refine eq_top_iff.2 fun z _ => ?_
    have hy' : y ∈ ψ ⁻¹ᵁ D0 := hpre ▸ hy
    rw [← hpre]
    change ψ z ∈ D0
    rw [hsub ⟨z, rfl⟩ ⟨y, rfl⟩]
    exact hy'
  have hfin : IsFinite ψ := ψ.isFinite_of_not_subsingleton_range hdim hne
  have hD0 : IsAffineOpen D0 := Proj.isAffineOpen_basicOpen _ _ (X_mem_one k 1 0) one_pos
  have haff : IsAffineOpen (nvCover s 0) := hpre ▸ hD0.preimage ψ
  refine ⟨haff, ?_⟩
  have hle := nvCover_le_preimage_basicOpen_toPolynomialModel s hs f 0
  have happ : (ψ.app D0).hom.Finite := ψ.finite_app D0 hD0
  have happLE : (ψ.appLE D0 (nvCover s 0) hle).hom.Finite := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ ?_) happ
    have : IsIso (C.presheaf.map (homOfLE hle).op) := by
      rw [Subsingleton.elim (homOfLE hle) (eqToHom hpre.symm), eqToHom_op, eqToHom_map]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hchart : (chartPullback s hs f 0).Finite := by
    have : IsIso (AlgebraicGeometry.Proj.awayToSection (polyGrading k 1) (MvPolynomial.X 0)) := by
      rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom _ _ (X_mem_one k 1 0) one_pos]
      infer_instance
    refine RingHom.Finite.comp (RingHom.Finite.comp happLE
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2))
      (RingHom.Finite.of_surjective _ (chartHom_surjective k 1 0))
  let e : MvPolynomial {j : Fin 2 // j ≠ 0} k →+* k[X] :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)
  have hratio : ratio s 0 1 = ξ := (eq_div (s 0) le_rfl hξ.symm).symm
  have heq : chartPullback s hs f 0 = (aeval ξ).toRingHom.comp e := by
    rw [chartPullback_eq]
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, e, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_C]
      rfl
    · obtain ⟨j, hj⟩ := j
      obtain rfl : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, e, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
      exact hratio
  rw [heq] at hchart
  exact RingHom.Finite.of_comp_finite hchart

/-! ### The degree of `L` -/

/-- The point `σ` of a rational section, as a divisor, has `k` as its ring of functions. -/
private theorem isIso_ker_subscheme {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSeparated f] (σ : Spec (.of k) ⟶ C) (hσ : σ ≫ f = 𝟙 _) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (σ.ker.subschemeι ≫ f).appTop) := by
  have : IsClosedImmersion (σ ≫ f) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ f
  have h : σ.toImage ≫ (σ.imageι ≫ f) = 𝟙 _ := by rw [← Category.assoc, σ.toImage_imageι, hσ]
  have : IsIso (σ.imageι ≫ f) := by
    rw [(IsIso.eq_inv_of_hom_inv_id h)]
    infer_instance
  have : IsIso (σ.ker.subschemeι ≫ f) := this
  have : IsIso (σ.ker.subschemeι ≫ f).appTop :=
    Scheme.Hom.instIsIsoCommRingCatApp (σ.ker.subschemeι ≫ f) ⊤
  infer_instance

/-- If `[L] = N • [σ]` in the Picard group, then `deg L = N`, since the point `σ` has degree
one. -/
private theorem invertibleCurveDegree_eq_of_picardClass {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (σ : Spec (.of k) ⟶ C) (hσ : σ ≫ f = 𝟙 _)
    [Stacks.Divisors.IsEffectiveCartierDivisor σ.ker]
    (N : ℕ) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    (hL : Stacks.SheafOfModules.picardClass C.presheaf (Stacks.RingedSpace.structureIsSheaf _) L
      ‹_› = (N : ℤ) • Stacks.Divisors.picardClass σ.ker) :
    invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L =
      N := by
  have h1 := congrArg (invertibleCurveDegreeHom k f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le) hL
  rw [invertibleCurveDegreeHom_picardClass, map_zsmul,
    invertibleCurveDegreeHom_picardClass k f _ (Stacks.Divisors.invertibleSheaf' _)
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)] at h1
  have := isIso_ker_subscheme f σ hσ
  have h2 := invertibleCurveDegree_divisorSheaf_eq_one k f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le σ.ker
  rw [h1, smul_eq_mul]
  erw [h2]
  exact mul_one _

/-- The value of the section family of a global section `t` over `⊤` is `t`. -/
private theorem sectionsEquiv_symm_eval_top {C : Scheme.{u}} (L : C.Modules) (t : Γ(L, ⊤)) :
    ((Stacks.NonvanishingSpelling.sectionsEquiv C L).symm t).eval (Opposite.op ⊤) = t := by
  rw [Stacks.NonvanishingSpelling.sectionsEquiv_symm_eval]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The degree of `L` is the length of the zero scheme of any nonzero section.** -/
private theorem invertibleCurveDegree_eq_finrank_zeroScheme {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (t : Γ(L, ⊤)) (ht : t ≠ 0) :
    letI : Algebra k Γ((zeroScheme C L t).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((zeroScheme C L t).subschemeι ≫ f).appTop).hom.toAlgebra
    invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L =
      (Module.finrank k
        Γ((zeroScheme C L t).subscheme, ⊤) : ℤ) := by
  have hsec := sectionsEquiv_symm_eval_top L t
  exact invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one k f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L
    ((Stacks.NonvanishingSpelling.sectionsEquiv C L).symm t) (by rw [hsec]; exact ht) _
    (by rw [hsec])

/-! ### Functions on a closed subscheme inside an affine open -/

/-- If the support of a closed subscheme `D` lies in an affine open `U`, then the ring of
functions on `D` is `Γ(X, U) ⧸ I_D(U)`, compatibly with the structure over `k`. -/
private theorem finrank_subscheme_eq_finrank_quotient {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.IdealSheafData) (U : X.affineOpens)
    (hU : (D.support : Set X) ⊆ U.1) :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom.toAlgebra
    Module.finrank k Γ(D.subscheme, ⊤) = Module.finrank k (Γ(X, U.1) ⧸ D.ideal U) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom.toAlgebra
  have hpre : D.subschemeι ⁻¹ᵁ U.1 = ⊤ := by
    refine eq_top_iff.2 fun z _ => hU ?_
    rw [← D.range_subschemeι]
    exact ⟨z, rfl⟩
  have e : (⊤ : D.subscheme.Opens) ≤ D.subschemeι ⁻¹ᵁ U.1 := hpre.ge
  let φ := D.subschemeι.appLE U.1 ⊤ e
  have hiso : IsIso (D.subscheme.presheaf.map (homOfLE e).op) := by
    rw [Subsingleton.elim (homOfLE e) (eqToHom hpre.symm), eqToHom_op, eqToHom_map]
    infer_instance
  have hφ : φ = D.subschemeι.app U.1 ≫ D.subscheme.presheaf.map (homOfLE e).op := rfl
  have hsurj : Function.Surjective φ.hom := by
    rw [hφ, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp (D.subschemeι_app_surjective U)
  have hker : RingHom.ker φ.hom = D.ideal U := by
    rw [hφ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso _).1, D.ker_subschemeι_app U]
  let φa : Γ(X, U.1) →ₐ[k] Γ(D.subscheme, ⊤) :=
    { φ.hom with
      commutes' := fun r => by
        change φ.hom ((X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
            (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))) =
          ((D.subschemeι ≫ f).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
          Scheme.Hom.map_appLE, Stacks.ProjectiveSpaceChartRatio.appLE_top_top] }
  have e₁ := (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := φa) hsurj)
  exact e₁.toLinearEquiv.finrank_eq.symm

/-- On the nonvanishing open `U = C_{s₀}`, which `s₀` trivializes, the ideal of the zero scheme
of `s₁` is generated by the ratio `ξ = s₁ / s₀`. -/
private theorem zeroScheme_ideal_eq_span {C : Scheme.{u}} (L : C.Modules)
    [Stacks.Ample.IsInvertibleModule C L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (s₀ s₁ : Γ(L, ⊤)) (hU : IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen C L s₀))
    (ξ : Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀))
    (hξ : L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₁ =
      ξ • L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₀) :
    (zeroScheme C L s₁).ideal ⟨_, hU⟩ = Ideal.span {ξ} := by
  rw [zeroScheme_ideal]
  let g : Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) →ₗ[Γ(C, _)]
      Γ(L, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) :=
    LinearMap.toSpanSingleton _ _ (L.presheaf.map
      (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₀)
  have hg : Function.Bijective g := Stacks.NonvanishingSpelling.bijective_smul C L s₀ le_rfl
  let e := LinearEquiv.ofBijective g hg
  have he : e ξ = L.presheaf.map
      (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₁ :=
    hξ.symm
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro a ⟨φ, rfl⟩
    refine Ideal.mem_span_singleton'.mpr ⟨φ (L.presheaf.map
      (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₀), ?_⟩
    rw [hξ, map_smul, smul_eq_mul, mul_comm]
  · refine Ideal.span_le.mpr ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    refine Ideal.subset_span ⟨e.symm.toLinearMap, ?_⟩
    rw [ha, LinearEquiv.coe_toLinearMap, ← he, LinearEquiv.symm_apply_apply]

/-- On an integral scheme the zero scheme of a nonzero section `t` of an invertible module is
supported on the complement of the nonvanishing open `C_t`. -/
private theorem support_zeroScheme_eq_compl {C : Scheme.{u}} [IsIntegral C] (L : C.Modules)
    [Stacks.Ample.IsInvertibleModule C L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (t : Γ(L, ⊤)) (ht : t ≠ 0) :
    ((zeroScheme C L t).support : Set C) =
      (Stacks.NonvanishingOpen.nonvanishingOpen C L t : Set C)ᶜ := by
  have hsec := sectionsEquiv_symm_eval_top L t
  have h := nonvanishingLocus_eq_compl_supportSet_zeroScheme L
    ((Stacks.NonvanishingSpelling.sectionsEquiv C L).symm t) (by rw [hsec]; exact ht)
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq, hsec] at h
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, h, compl_compl]
  rfl

/-- A nonzero section of an invertible module on an integral scheme whose zero scheme has
nonzero length over `k` vanishes somewhere. -/
private theorem nonvanishingOpen_ne_top {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ Spec (.of k)) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (t : Γ(L, ⊤)) (ht : t ≠ 0)
    (hlen : letI : Algebra k Γ((zeroScheme C L t).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ ((zeroScheme C L t).subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ((zeroScheme C L t).subscheme, ⊤) ≠ 0) :
    Stacks.NonvanishingOpen.nonvanishingOpen C L t ≠ ⊤ := by
  intro htop
  have hsupp := support_zeroScheme_eq_compl L t ht
  rw [htop] at hsupp
  have : IsEmpty (zeroScheme C L t).subscheme := ⟨fun z => by
    have hz : (zeroScheme C L t).subschemeι z ∈ ((zeroScheme C L t).support : Set C) := by
      rw [← (zeroScheme C L t).range_subschemeι]
      exact ⟨z, rfl⟩
    rw [hsupp] at hz
    exact hz trivial⟩
  let : Algebra k Γ((zeroScheme C L t).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((zeroScheme C L t).subschemeι ≫ f).appTop).hom.toAlgebra
  exact hlen Module.finrank_zero_of_subsingleton

/-- On an integral scheme, let `s₀, s₁` be sections of `L` with `C_{s₀}` and `C_{s₁}` nonempty,
and `ξ = s₁ / s₀` on `C_{s₀}`. If `Γ(C, C_{s₀}) / ξ` is nonzero, then `ξ` is transcendental
over `k`: it is not `0`, as `s₁` does not vanish on `C_{s₀} ∩ C_{s₁}`, and not a unit. -/
private theorem transcendental_ratio {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ Spec (.of k)) (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    (s₀ s₁ : Γ(L, ⊤))
    (hU : (Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ : Set C).Nonempty)
    (hV : (Stacks.NonvanishingOpen.nonvanishingOpen C L s₁ : Set C).Nonempty)
    (ξ : Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀))
    (hξ : L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₁ =
      ξ • L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op s₀) :
    letI : Algebra k Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        C.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op
          ).hom.toAlgebra
    Module.finrank k
        (Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) ⧸ Ideal.span {ξ}) ≠ 0 →
      Transcendental k ξ := by
  let : Algebra k Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      C.presheaf.map
        (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)).op).hom.toAlgebra
  intro hq halg
  have : Nonempty (Stacks.NonvanishingOpen.nonvanishingOpen C L s₀) := hU.to_subtype
  rcases eq_zero_or_isUnit_of_isAlgebraic halg with h0 | hu
  · obtain ⟨y, hyU, hyV⟩ := nonempty_preirreducible_inter
      (Stacks.NonvanishingOpen.nonvanishingOpen C L s₀).isOpen
      (Stacks.NonvanishingOpen.nonvanishingOpen C L s₁).isOpen hU hV
    refine (Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff C L s₁ y).mp hyV ?_
    rw [TopCat.Presheaf.Γgerm, ← TopCat.Presheaf.germ_res_apply L.presheaf
      (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L s₀ ≤ ⊤)) y hyU,
      hξ, h0, zero_smul, map_zero]
    exact Submodule.zero_mem _
  · rw [Ideal.span_singleton_eq_top.mpr hu] at hq
    exact hq Module.finrank_zero_of_subsingleton

/-- **The coordinate ring of `U = {x₀ ≠ 0}` is free of rank `N` over `k[ξ_a]`.** Let `C` be a curve
over the number field `k` as in Bombieri's Section 8, `L ≅ 𝒪(NP)`, and `x₀, …, xₙ` a `k`-basis of
`Γ(C, L)` embedding `C` in `ℙⁿ`, such that `x₀` and `x_b` have no common zero for each `b ≥ 1`.
For `a ∈ {1, …, n}`, if `ξ ∈ Γ(C, U)` is the function `x_a / x₀` (that is, `x_a|_U = ξ • x₀|_U`),
then `Γ(C, U)` is a free `k[X]`-module of rank `N`, where `X` acts as `ξ`. -/
@[faltings "lem_bvs_coordinate_ring_free"]
public theorem free_and_finrank_affineOpen (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f] [Smooth f]
    [IsProper f] [IsProjectiveVariety k f] (hg : 2 ≤ genus f)
    (σ : Spec (.of k) ⟶ C) (hσ : σ ≫ f = 𝟙 _)
    [Stacks.Divisors.IsEffectiveCartierDivisor σ.ker]
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    (L : C.Modules) [Stacks.Ample.IsInvertibleModule C L]
    (hL : Stacks.SheafOfModules.picardClass C.presheaf (Stacks.RingedSpace.structureIsSheaf _) L
      ‹_› = (N : ℤ) • Stacks.Divisors.picardClass σ.ker)
    {n : ℕ} (x : Fin (n + 1) → Γ(L, ⊤))
    (hxb : letI : Module k Γ(L, ⊤) := (Module.compHom _
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
      LinearIndependent k x ∧ Submodule.span k (Set.range x) = ⊤)
    (hx : Stacks.ProjectiveFromSections.GeneratesStalks x)
    [IsClosedImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse x hx)]
    (hG1 : ∀ b : Fin n, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ⊔
      Stacks.NonvanishingOpen.nonvanishingOpen C L (x b.succ) = ⊤)
    (a : Fin n) (ξ : Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)))
    (hξ : L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ≤ ⊤)).op
        (x a.succ) =
      ξ • L.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ≤ ⊤)).op
        (x 0)) :
    letI : Algebra k Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        C.presheaf.map
          (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ≤ ⊤)).op
          ).hom.toAlgebra
    letI : Algebra k[X] Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) :=
      (Polynomial.aeval ξ).toRingHom.toAlgebra
    Module.Free k[X] Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) ∧
      Module.finrank k[X] Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) = N := by
  let : Algebra k Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      C.presheaf.map
        (homOfLE (le_top : Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ≤ ⊤)).op
        ).hom.toAlgebra
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj
    C.ringCatSheaf.property L := ‹_›
  have hdeg := invertibleCurveDegree_eq_of_picardClass f σ hσ N L hL
  have hlen : ∀ t : Γ(L, ⊤), t ≠ 0 →
      letI : Algebra k Γ((zeroScheme C L t).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ ((zeroScheme C L t).subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ((zeroScheme C L t).subscheme, ⊤) = N := fun t ht => by
    exact_mod_cast ((invertibleCurveDegree_eq_finrank_zeroScheme f L t ht).symm.trans hdeg)
  have hx0 : ∀ i, x i ≠ 0 := by
    let : Module k Γ(L, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
    exact hxb.1.ne_zero
  have hnt : ∀ i, Stacks.NonvanishingOpen.nonvanishingOpen C L (x i) ≠ ⊤ := fun i =>
    nonvanishingOpen_ne_top f L (x i) (hx0 i) (by rw [hlen _ (hx0 i)]; omega)
  have hcov : ∀ z : C, z ∈ Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) ∨
      z ∈ Stacks.NonvanishingOpen.nonvanishingOpen C L (x a.succ) := fun z =>
    TopologicalSpace.Opens.mem_sup.mp (by rw [hG1 a]; trivial)
  have hUne : (Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0) : Set C).Nonempty := by
    by_contra hne
    exact hnt a.succ (eq_top_iff.2 fun z _ => (hcov z).resolve_left fun h => hne ⟨z, h⟩)
  have hVne : (Stacks.NonvanishingOpen.nonvanishingOpen C L (x a.succ) : Set C).Nonempty := by
    by_contra hne
    exact hnt 0 (eq_top_iff.2 fun z _ => (hcov z).resolve_right fun h => hne ⟨z, h⟩)
  have hs : Stacks.ProjectiveFromSections.GeneratesStalks ![x 0, x a.succ] :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun y =>
      (hcov y).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
  obtain ⟨haff, hfin⟩ := isAffineOpen_and_finite_aeval f _ hs (hnt 0) hUne ξ hξ
  have hq : Module.finrank k
      (Γ(C, Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) ⧸ Ideal.span {ξ}) = N := by
    rw [← zeroScheme_ideal_eq_span L (x 0) (x a.succ) haff ξ hξ, ← hlen _ (hx0 _)]
    refine (finrank_subscheme_eq_finrank_quotient f _ ⟨_, haff⟩ ?_).symm
    rw [support_zeroScheme_eq_compl L _ (hx0 _)]
    exact fun z hz => (hcov z).resolve_right hz
  have : Nonempty (Stacks.NonvanishingOpen.nonvanishingOpen C L (x 0)) := hUne.to_subtype
  obtain ⟨hfree, hrank⟩ := free_and_finrank_eq ξ
    (transcendental_ratio f L _ _ hUne hVne ξ hξ (by omega)) hfin
  exact ⟨hfree, hrank.trans hq⟩

end Faltings.BombieriSiegel
