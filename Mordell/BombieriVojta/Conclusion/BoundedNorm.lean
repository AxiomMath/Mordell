module
public import Mordell.BombieriVojta.Height.NPNeronNorm
public import Mordell.Height.Weil.Northcott
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import Mordell.BombieriVojta.Height.SegreVeroneseClass

/-!
# Points of bounded Néron norm

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `(J, ι)` a Jacobian of `C`, `j = j_P : C → J` the Abel–Jacobi map, `θ` the class of the
theta divisor and `⟨x, y⟩ = ĥ_θ(x + y) - ĥ_θ(x) - ĥ_θ(y)` the Néron form on `J(k̄)`; for
`z ∈ C(k̄)` write `|z| = √⟨j z, j z⟩`. Then for every finite extension `K` of `k` inside `k̄`
and every real `B ≥ 0`, the set of `z ∈ C(K)` with `|z| < B` is finite.

The proof is Northcott's: by the comparison of `h_{NP}` with the Néron norm, a point with
`|z| < B` has height `h_{NP}(z) ≤ (N / 2g) B² + c_{NP} (1 + B)`, the embedding `φ_{NP}` maps
`C(K)` injectively into `ℙⁿ(K)`, and `ℙⁿ(K)` has only finitely many points of bounded height.

## Main results

* `Faltings.finite_setOf_neronNorm_abelJacobi_lt`: the points of `C(K)` of bounded Néron norm
  form a finite set.

## Implementation notes

The Néron form is `Faltings.neronPairing` on the `k̄`-points of `J`, for the Abel–Jacobi map `j`
(`Faltings.IsAbelJacobiMap`) and the reduced effective Cartier divisor `D` whose support is
`Faltings.thetaDivisor`, as in `Faltings.exists_abs_weilHeight_sub_neronPairing_le`. A point of
`C(k̄)` is a morphism `Spec k̄ ⟶ C` over `Spec k`, and `j z` is the composite `z ≫ j`. The field
`K` is an intermediate field of `k̄ / k`, finite over `k`, and `C(K) ⊆ C(k̄)` is the set of
`z` whose underlying morphism factors through `Spec k̄ ⟶ Spec K`, as in
`Faltings.IsEvenClass.finite_setOf_neronTateHeight_le`; since `Spec k̄ ⟶ Spec K` is an
epimorphism, this identifies `C(K)` with a subset of `C(k̄)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, pp. 638–639
-/

open Faltings.CurveWithDegreeOneDivisor (exists_eq_projectiveSpacePoint_of_eq_one)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

section Charts

variable {n : ℕ}

/-- A tuple with some coordinate equal to `1` generates the unit ideal. -/
private theorem span_range_eq_top_of_eq_one {R : Type*} [CommSemiring R] {ι : Type*}
    {c : ι → R} {j : ι} (hj : c j = 1) : Ideal.span (Set.range c) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) (hj ▸ isUnit_one)

/-- Two coordinate vectors over a field defining the same point of `ℙ(Rⁿ⁺¹)` define the same
point of `ℙⁿ_ℤ`. -/
private theorem projectiveSpacePoint_eq_of_mk_eq {R : Type u} [Field R]
    {c c' : Fin (n + 1) → R} (h0 : c ≠ 0) (h0' : c' ≠ 0)
    (hc : Ideal.span (Set.range c) = ⊤) (hc' : Ideal.span (Set.range c') = ⊤)
    (h : Projectivization.mk R c h0 = Projectivization.mk R c' h0') :
    projectiveSpacePoint (R := .of R) c hc = projectiveSpacePoint (R := .of R) c' hc' := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff R c c' h0 h0').1 h
  have hfun : c = fun i => ((a : R) : CommRingCat.of R) * c' i := by
    rw [← ha]; funext i; rfl
  subst hfun
  exact projectiveSpacePoint_unit_mul (R := .of R) a c' hc' hc

end Charts

/-- The field of definition of a point of `ℙ(Ωⁿ⁺¹)` with homogeneous coordinates in a finite
extension `E` of `ℚ` inside `Ω` has degree at most `[E : ℚ]`. -/
private theorem degreeOfPoint_mk_le {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] {ι : Type*} (c : ι → Ω) (hc : c ≠ 0)
    (hcE : ∀ i, c i ∈ E) :
    degreeOfPoint ℚ (Projectivization.mk Ω c hc) ≤ Module.finrank ℚ E := by
  refine IntermediateField.finrank_le_of_le_right ?_
  rw [pointField, IntermediateField.adjoin_le_iff]
  rintro r ⟨i, j, -, rfl⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep Ω c hc
  rw [← ha, Pi.smul_apply, Pi.smul_apply, Units.smul_def, Units.smul_def, smul_eq_mul,
    smul_eq_mul, mul_div_mul_left _ _ a.ne_zero]
  exact div_mem (hcE i) (hcE j)

/-- A bound `a x² + c (1 + x)` is uniform in `0 ≤ x ≤ B`. -/
private theorem mul_sq_add_mul_one_add_le {a c x B : ℝ} (hx : 0 ≤ x) (hxB : x ≤ B) :
    a * x ^ 2 + c * (1 + x) ≤ |a| * B ^ 2 + |c| * (1 + B) := by
  nlinarith [le_abs_self a, le_abs_self c, abs_nonneg a, abs_nonneg c,
    pow_le_pow_left₀ hx hxB 2, sq_nonneg x]

/-- **Points of bounded norm.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field
`k` with a divisor of degree one, `A = (J, ι)` a Jacobian, `j = j_P` the Abel–Jacobi map, `D` the
reduced divisor with support the theta divisor, `Ω` an algebraic closure of `k` and
`|z| = √(neronPairing (j z) (j z))` for `z ∈ C(Ω)`. For every intermediate field `K` of `Ω / k`
finite over `k` and every real `B ≥ 0`, the set of `z ∈ C(K)` with `|z| < B` is finite. -/
@[faltings "lem_bvr_bounded_part"]
public theorem finite_setOf_neronNorm_abelJacobi_lt {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] (B : ℝ) (_hB : 0 ≤ B) :
    {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk X.f |
      (∃ q : Spec (.of K) ⟶ X.C, z.left = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ q) ∧
        √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Ω
          (.ofMul (z ≫ j)) (.ofMul (z ≫ j))) < B}.Finite := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  haveI : FiniteDimensional ℚ K := Module.Finite.trans k K
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  -- `𝒪(NP)` for `N = 2g + 1`
  set N : ℕ := 2 * genus X.f + 1 with hN
  obtain ⟨L, hLs, hLc⟩ : ∃ (L : X.C.Modules) (hLs : Stacks.SheafOfModules.IsInvertible
      X.C.presheaf (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L),
      Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L hLs =
      (N : ℤ) • X.classP :=
    Stacks.SheafOfModules.exists_picardClass_eq _ _ _
  haveI hLinv : Stacks.Ample.IsInvertibleModule X.C L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).mp hLs
  -- a `k`-basis of `Γ(C, L)`, which has dimension `N + 1 - g ≥ 1`
  have hdim1 : topologicalKrullDim X.C = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)
  have hdeg := X.invertibleCurveDegree_eq_of_picardClass hdim1.le N L hLc
  have hb := X.finrank_globalSections_eq_of_invertibleCurveDegree hdim1.le N L (by omega) hdeg
  have hpos : 0 < Module.finrank k Γ(L, ⊤) := by omega
  haveI : Module.Finite k Γ(L, ⊤) := Module.finite_of_finrank_pos hpos
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k Γ(L, ⊤) = n + 1 :=
    ⟨Module.finrank k Γ(L, ⊤) - 1, by omega⟩
  let x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤) := Module.finBasisOfFinrankEq k _ hn
  obtain ⟨-, hx, hci, α, hα, -⟩ := X.isClosedImmersion_toProjectiveSpaceOver N le_rfl L hLc x
  -- the height comparison, for `φ_{NP}`, whose `φ_{NP}^* 𝒪(1) ≅ L` has the class `N • P` of `L`
  obtain ⟨cNP, hcNP⟩ :=
    exists_abs_weilHeight_sub_neronPairing_le X A hg j hj D hrad hsupp N le_rfl
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f)
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _)
      (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ L _ _).mpr
        ⟨(Scheme.Modules.pullbackComp
            (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f)
            (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).app
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≪≫
            @asIso _ _ _ _ α hα⟩).trans hLc) Ω
  clear α hα
  set φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f
  set ι := projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of k))
  set M : ℝ := |(N : ℝ) / (2 * genus X.f)| * B ^ 2 + |cNP| * (1 + B)
  -- `φ_{NP}` is a monomorphism, so a point is determined by its image in `ℙⁿ_ℤ`
  have hinj : ∀ z w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk X.f,
      z.left ≫ φ ≫ ι = w.left ≫ φ ≫ ι → z = w := by
    intro z w h
    ext1
    refine (cancel_mono φ).1 (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, φ, Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst]
      exact (Over.w z).trans (Over.w w).symm
    · simpa only [Category.assoc] using h
  -- the image of a point of bounded norm defined over `K`
  have key : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk X.f,
      (∃ q : Spec (.of K) ⟶ X.C, z.left = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ q) →
      √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Ω
          (.ofMul (z ≫ j)) (.ofMul (z ≫ j))) < B →
      ∃ y : ℙ Ω (Fin (n + 1) → Ω),
        (weilHeight y ≤ M ∧ degreeOfPoint ℚ y ≤ Module.finrank ℚ K) ∧
        ∃ (c : Fin (n + 1) → Ω) (hc0 : c ≠ 0) (hcs : Ideal.span (Set.range c) = ⊤),
          Projectivization.mk Ω c hc0 = y ∧
            z.left ≫ φ ≫ ι = projectiveSpacePoint (R := .of Ω) c hcs := by
    rintro z ⟨q, hq⟩ hlt
    obtain ⟨j₀, c, hc, hcj, ht⟩ := exists_eq_projectiveSpacePoint_of_eq_one (q ≫ φ ≫ ι)
    set cΩ : Fin (n + 1) → Ω := fun i => algebraMap K Ω (c i)
    have hcΩ1 : cΩ j₀ = 1 := by simp [cΩ, hcj]
    have hcΩ0 : cΩ ≠ 0 := fun h => one_ne_zero (hcΩ1.symm.trans (congrFun h j₀))
    have hcΩs : Ideal.span (Set.range cΩ) = ⊤ := span_range_eq_top_of_eq_one hcΩ1
    have hz : z.left ≫ φ ≫ ι = projectiveSpacePoint (R := .of Ω) cΩ hcΩs := by
      rw [hq, Category.assoc, ht]
      exact specMap_comp_projectiveSpacePoint (CommRingCat.ofHom (algebraMap K Ω)) c hc hcΩs
    refine ⟨Projectivization.mk Ω cΩ hcΩ0, ⟨?_, ?_⟩, cΩ, hcΩ0, hcΩs, rfl, hz⟩
    · have h1 := (abs_le.1 (hcNP z cΩ hcΩ0 hz)).2
      beta_reduce at h1
      have h2 := mul_sq_add_mul_one_add_le (a := (N : ℝ) / (2 * genus X.f)) (c := cNP)
        (Real.sqrt_nonneg _) hlt.le
      linarith
    · haveI : FiniteDimensional ℚ (K.restrictScalars ℚ) :=
        inferInstanceAs (FiniteDimensional ℚ K)
      exact degreeOfPoint_mk_le (K.restrictScalars ℚ) cΩ hcΩ0 fun i => (c i).2
  choose! F hF using key
  have hfin := finite_setOf_weilHeight_le_of_degreeOfPoint_le (K := Ω) (ι := Fin (n + 1))
    (by positivity : 0 ≤ M) (D := Module.finrank ℚ K) Module.finrank_pos
  refine Set.Finite.of_finite_image (f := F) (hfin.subset ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact (hF z hz.1 hz.2).1
  · intro z hz w hw h
    obtain ⟨c, hc0, hcs, hcz, hz⟩ := (hF z hz.1 hz.2).2
    obtain ⟨c', hc0', hcs', hcw, hw⟩ := (hF w hw.1 hw.2).2
    exact hinj z w (hz.trans <| (projectiveSpacePoint_eq_of_mk_eq hc0 hc0' hcs hcs'
      (hcz.trans <| h.trans hcw.symm)).trans hw.symm)

end Faltings
