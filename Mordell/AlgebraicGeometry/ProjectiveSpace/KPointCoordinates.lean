module

public import Mathlib
public import Mordell.Height.Machine.EmbeddingGroup
public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.ProductEmbedding
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.ProductPullback
public import Mordell.Height.Weil.Segre
public import Mordell.Height.Weil.ZeroCoordinates
public import Mordell.Height.Weil.LinearMapLower
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint

/-!
# Homogeneous coordinates of `k`-points of projective space

Chart values `(T_j/T_i)(w)` of a `k`-point `w` of `ℙⁿ_k = Proj k[T₀, …, T_n]`, the dictionary
`kPointProjectivization : ℙⁿ_k(k) → ℙ(k^{n+1})` and its computation through integral chart values,
coordinates of Segre products of `k`-points, and `weilHeight_mk_mul_comp_equiv`. This is the
coordinate API used by the Weil height machine and by Bombieri's lemmas.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

universe u v

namespace Faltings

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section ChartValues

variable {k : Type u} [Field k] {N : ℕ}

/-- The value at a `k`-point `w` of `Proj k[T₀, …, T_N]` lying in `D₊(Tᵢ)` of the affine
coordinate `T_j / T_i`. -/
@[expose] public noncomputable def chartVal (w : Spec (.of k) ⟶ Proj (polyGrading k N))
    (i : Fin (N + 1)) (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i))
    (j : Fin (N + 1)) : k :=
  (Scheme.ΓSpecIso (.of k)).hom (w.appLE _ ⊤ hi
    ((Proj.awayToSection (polyGrading k N) (MvPolynomial.X i)).hom
      (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j)))

/-- On a point `Spec θ ≫ awayι` of the chart, the chart value is `θ` of the fraction. -/
private theorem chartVal_specMap_comp_awayι
    (i : Fin (N + 1)) (θ : CommRingCat.of (Away (polyGrading k N) (MvPolynomial.X i)) ⟶
      CommRingCat.of k)
    (hi : ⊤ ≤ (Spec.map θ ≫ Proj.awayι (polyGrading k N) (MvPolynomial.X i)
      (X_mem_one k N i) Nat.one_pos) ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i))
    (j : Fin (N + 1)) :
    chartVal (Spec.map θ ≫ Proj.awayι (polyGrading k N) (MvPolynomial.X i)
      (X_mem_one k N i) Nat.one_pos) i hi j =
      θ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j) := by
  have h1 : (⊤ : (Spec (CommRingCat.of (Away (polyGrading k N) (MvPolynomial.X i)))).Opens) ≤
      Proj.awayι (polyGrading k N) (MvPolynomial.X i) (X_mem_one k N i) Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (polyGrading k N) (MvPolynomial.X i) := by
    rw [← Proj.opensRange_awayι _ _ (X_mem_one k N i) Nat.one_pos]
    intro x _
    exact ⟨x, rfl⟩
  unfold chartVal
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map θ) _ _ ⊤ ⊤ h1 le_top]
  rw [CommRingCat.comp_apply,
    Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection]
  erw [Stacks.ProjectiveSpaceChartRatio.appLE_top_top]
  have := congrArg (fun g => (Scheme.ΓSpecIso (.of k)).hom (g.hom
    (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j))) (Scheme.ΓSpecIso_inv_naturality θ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [← this]
  simp

/-- A `k`-point of `Proj k[T₀, …, T_N]` inside `D₊(Tᵢ)` factors through the chart
`Spec k[T]_{(Tᵢ)}`. -/
private theorem exists_specMap_comp_awayι (w : Spec (.of k) ⟶ Proj (polyGrading k N))
    (i : Fin (N + 1))
    (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i)) :
    ∃ θ : CommRingCat.of (Away (polyGrading k N) (MvPolynomial.X i)) ⟶ CommRingCat.of k,
      Spec.map θ ≫ Proj.awayι (polyGrading k N) (MvPolynomial.X i)
        (X_mem_one k N i) Nat.one_pos = w := by
  have H : Set.range w.base ⊆ Set.range (Proj.awayι (polyGrading k N) (MvPolynomial.X i)
      (X_mem_one k N i) Nat.one_pos).base := by
    rintro _ ⟨a, rfl⟩
    have h1 : w.base a ∈ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i) :=
      hi (show a ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial)
    rw [← Proj.opensRange_awayι _ _ (X_mem_one k N i) Nat.one_pos] at h1
    rwa [← Scheme.Hom.coe_opensRange]
  exact ⟨Spec.preimage (IsOpenImmersion.lift _ w H), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

/-- A `k`-point of the chart lying over `Spec k` is `k`-linear on the chart ring. -/
private theorem apply_coeffToAway (i : Fin (N + 1))
    (θ : CommRingCat.of (Away (polyGrading k N) (MvPolynomial.X i)) ⟶ CommRingCat.of k)
    (hw : (Spec.map θ ≫ Proj.awayι (polyGrading k N) (MvPolynomial.X i)
        (X_mem_one k N i) Nat.one_pos) ≫ projToSpecCoeff k N = 𝟙 _) (r : k) :
    θ.hom (coeffToAway k N i r) = r := by
  rw [Category.assoc, awayι_comp_projToSpecCoeff, ← Spec.map_comp, ← Spec.map_id] at hw
  exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of k => g.hom r) (Spec.map_injective hw)

/-- The fraction `Tᵢ / Tᵢ` is `1`. -/
private theorem coordFracAt_self (i : Fin (N + 1)) :
    Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i i = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, Stacks.ProjectiveSpaceChartRatio.coordFracAt,
    Away.val_mk, HomogeneousLocalization.val_one]
  simp

/-- A `k`-linear ring map out of the chart `k[T]_{(Tᵢ)}` sends `R / Tᵢ^d` to the value of `R`
at the images of the affine coordinates. -/
private theorem apply_mk_eq_eval (i : Fin (N + 1))
    (θ : CommRingCat.of (Away (polyGrading k N) (MvPolynomial.X i)) ⟶ CommRingCat.of k)
    (hθ : ∀ r : k, θ.hom (coeffToAway k N i r) = r) (d : ℕ)
    (R : MvPolynomial (Fin (N + 1)) k) (hR : R ∈ polyGrading k N (d • 1)) :
    θ.hom (Away.mk (polyGrading k N) (X_mem_one k N i) d R hR) =
      MvPolynomial.eval (fun j => θ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j))
        R := by
  obtain ⟨q, hq⟩ := chartHom_surjective k N i (Away.mk (polyGrading k N) (X_mem_one k N i) d R hR)
  have hq' : q = setOneHom k N i R := by
    have := congrArg (chartRetract k N i) hq
    rw [chartRetract_mk] at this
    rw [← this, ← RingHom.comp_apply, chartRetract_comp_chartHom, RingHom.id_apply]
  rw [← hq, hq']
  have hcomp : θ.hom.comp (chartHom k N i) =
      MvPolynomial.eval (fun j => θ.hom (chartCoord k N i j)) := by
    rw [chartHom, MvPolynomial.comp_eval₂Hom]
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [hθ]
    · simp
  rw [← RingHom.comp_apply, hcomp, ← RingHom.comp_apply]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp
  · by_cases hj : j = i
    · subst hj
      simp [setOneHom_X_self, coordFracAt_self]
    · have := setOneHom_X_ne k N i ⟨j, hj⟩
      simp only [RingHom.comp_apply] at this ⊢
      rw [this]
      simp [chartCoord, Stacks.ProjectiveSpaceChartRatio.coordFracAt]

/-- **A homogeneous polynomial vanishes at a `k`-point exactly when it vanishes at its chart
coordinates.** For a `k`-point `w` of `Proj k[T₀, …, T_N]` inside `D₊(Tᵢ)`, a homogeneous `R`
lies in the homogeneous prime of `w` if and only if `R` vanishes at the vector of affine
coordinates `(T_j / T_i)(w)`. -/
public theorem mem_asHomogeneousIdeal_iff_eval_chartVal
    (w : Spec (.of k) ⟶ Proj (polyGrading k N)) (hw : w ≫ projToSpecCoeff k N = 𝟙 _)
    (i : Fin (N + 1)) (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i))
    {d : ℕ} {R : MvPolynomial (Fin (N + 1)) k} (hR : R.IsHomogeneous d) (a : Spec (.of k)) :
    R ∈ (w.base a).asHomogeneousIdeal ↔ MvPolynomial.eval (chartVal w i hi) R = 0 := by
  obtain ⟨θ, rfl⟩ := exists_specMap_comp_awayι w i hi
  have hθ := apply_coeffToAway i θ hw
  have hchart : chartVal _ i hi =
      fun j => θ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt k N i j) :=
    funext (chartVal_specMap_comp_awayι i θ hi)
  have hRd : R ∈ polyGrading k N d := (MvPolynomial.mem_homogeneousSubmodule _ _).2 hR
  have hR' : R ∈ polyGrading k N (d • 1) := by simpa using hRd
  rw [hchart, ← apply_mk_eq_eval i θ hθ d R hR']
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨c, rfl⟩ : ∃ c, R = MvPolynomial.C c :=
      ⟨_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hR.totalDegree_le)⟩
    have hmk : Away.mk (polyGrading k N) (X_mem_one k N i) 0 (MvPolynomial.C c) hR' =
        coeffToAway k N i c := (coeffToAway_eq_mk k N i c).symm
    rw [hmk, hθ]
    constructor
    · intro hc
      by_contra hc0
      exact (ProjectiveSpectrum.isPrime _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hc ((Ne.isUnit hc0).map MvPolynomial.C))
    · rintro rfl
      simp
  · have hpre := Proj.awayι_preimage_basicOpen (polyGrading k N) (X_mem_one k N i)
      Nat.one_pos hRd hd
    have helem : Away.isLocalizationElem (X_mem_one k N i) hRd =
        Away.mk (polyGrading k N) (X_mem_one k N i) d R hR' := by
      rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk, pow_one]
    rw [← not_iff_not, ← Proj.mem_basicOpen]
    change (Spec.map θ).base a ∈ Proj.awayι (polyGrading k N) (MvPolynomial.X i)
      (X_mem_one k N i) Nat.one_pos ⁻¹ᵁ Proj.basicOpen (polyGrading k N) R ↔ _
    rw [hpre]
    change Away.isLocalizationElem (X_mem_one k N i) hRd ∉ Ideal.comap θ.hom a.asIdeal ↔ _
    rw [helem, Ideal.mem_comap, (Ideal.eq_bot_or_top a.asIdeal).resolve_right a.isPrime.ne_top,
      Ideal.mem_bot]

/-- The chart value of `T_i / T_i` is `1`. -/
public theorem chartVal_self (w : Spec (.of k) ⟶ Proj (polyGrading k N)) (i : Fin (N + 1))
    (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i)) :
    chartVal w i hi i = 1 := by
  simp [chartVal, coordFracAt_self]

/-- The vector of chart values is nonzero. -/
public theorem chartVal_ne_zero (w : Spec (.of k) ⟶ Proj (polyGrading k N)) (i : Fin (N + 1))
    (hi : ⊤ ≤ w ⁻¹ᵁ Proj.basicOpen (polyGrading k N) (MvPolynomial.X i)) :
    chartVal w i hi ≠ 0 := fun h => by
  simpa [chartVal_self] using congrFun h i

end ChartValues

section Dictionary

variable {k : Type u} [Field k] {n : ℕ}

/-- Under the coordinate isomorphism `𝐏(kⁿ⁺¹) ≅ Proj k[T]` of the standard basis, the degree-one
form `v` vanishes at the point over `w` exactly when the linear form `∑ v_j T_j` vanishes at
`w`. -/
public theorem iota_mem_iff (w : AlgebraicGeometry.Proj (polyGrading k n)) (v : Fin (n + 1) → k) :
    SymmetricAlgebra.ι k _ v ∈ ((projectiveSpaceOfModuleIsoProjMvPolynomial
      (Pi.basisFun k (Fin (n + 1)))).inv.base w).asHomogeneousIdeal ↔
      (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) ∈ w.asHomogeneousIdeal := by
  set e := projectiveSpaceOfModuleIsoProjMvPolynomial (Pi.basisFun k (Fin (n + 1)))
  have hw : e.hom.base (e.inv.base w) = w := by
    change (e.inv ≫ e.hom).base w = w
    rw [e.inv_hom_id]
    rfl
  have key : ∀ R, R ∈ w.asHomogeneousIdeal ↔
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin (n + 1)))).symm R ∈
        (e.inv.base w).asHomogeneousIdeal := by
    intro R
    conv_lhs => rw [← hw]
    rfl
  have hv : SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin (n + 1)))
      (SymmetricAlgebra.ι k _ v) = ∑ j, MvPolynomial.C (v j) * MvPolynomial.X j := by
    conv_lhs => rw [← (Pi.basisFun k (Fin (n + 1))).sum_repr v]
    simp only [map_sum, map_smul, MvPolynomial.smul_eq_C_mul, Pi.basisFun_repr]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [key, ← hv, AlgEquiv.symm_apply_apply]

/-- The standard dual-basis functional of a vector `a` evaluates to `∑ a_j v_j`. -/
public theorem toDualEquiv_apply_apply (a v : Fin (n + 1) → k) :
    (Pi.basisFun k (Fin (n + 1))).toDualEquiv a v = ∑ j, v j * a j := by
  conv_lhs => rw [← (Pi.basisFun k (Fin (n + 1))).sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Module.Basis.toDualEquiv_apply, Module.Basis.toDual_apply_left]
  simp

/-- **The homogeneous coordinates of a `k`-point of `ℙⁿ_k` are its chart values.** The point of
`ℙ k (Fin (n + 1) → k)` attached to `q = y ≫ (𝐏(kⁿ⁺¹) ≅ ℙⁿ_k)⁻¹` by the one-dimensional-quotient
dictionary is the class of the affine coordinates `(T_j / T_i)(y)` of any chart `D₊(Tᵢ)`
containing `y`. -/
public theorem dictionary_eq_mk_chartVal (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (q : {q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (n + 1) → k) //
      q ≫ projectiveSpaceOfModuleToSpec k _ = 𝟙 _})
    (hq : q.1 = y ≫ (basisProjectiveSpaceOfModuleIso (Pi.basisFun k (Fin (n + 1)))).inv.left)
    (hw : (y ≫ (polynomialComparison k n).iso.hom) ≫ projToSpecCoeff k n = 𝟙 _)
    (i : Fin (n + 1)) (hi : ⊤ ≤ (y ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k n) (MvPolynomial.X i)) :
    (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
        (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ q)).map
          (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.toLinearMap
          (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm.injective =
      Projectivization.mk k (chartVal _ i hi) (chartVal_ne_zero _ i hi) := by
  set a := chartVal _ i hi
  set φa := (Pi.basisFun k (Fin (n + 1))).toDualEquiv a with hφa_def
  have hφa : φa ≠ 0 := fun h => chartVal_ne_zero _ i hi
    ((Pi.basisFun k (Fin (n + 1))).toDualEquiv.map_eq_zero_iff.mp h)
  have hK : (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ q).val =
      LinearMap.ker φa := by
    ext v
    rw [ProjectiveSpaceOfModule.mem_kValuedPointEquivOneDimQuotient, hq]
    change SymmetricAlgebra.ι k _ v ∈ ((projectiveSpaceOfModuleIsoProjMvPolynomial
      (Pi.basisFun k (Fin (n + 1)))).inv.base
        ((y ≫ (polynomialComparison k n).iso.hom).base default)).asHomogeneousIdeal ↔ _
    have hlin : (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j :
        MvPolynomial (Fin (n + 1)) k).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
        (MvPolynomial.isHomogeneous_C_mul_X _ _)
    rw [iota_mem_iff, mem_asHomogeneousIdeal_iff_eval_chartVal _ hw i hi hlin, LinearMap.mem_ker,
      hφa_def, toDualEquiv_apply_apply]
    simp [a]
  have h1 : ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
      (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ q) =
        Projectivization.mk k φa hφa := by
    rw [ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual, Equiv.symm_apply_eq]
    exact Subtype.ext (hK.trans
      (ProjectiveSpaceOfModule.kerOfProjectivizationDual_mk k _ φa hφa).symm)
  rw [h1, Projectivization.map_mk]
  congr 1
  exact (Pi.basisFun k (Fin (n + 1))).toDualEquiv.symm_apply_apply a

end Dictionary

section Points

variable {k : Type u} [Field k] {n : ℕ}

/-- **The point of `ℙ(kⁿ⁺¹)` of a `k`-point of `ℙⁿ_k`.** A `k`-point `y` of `ℙⁿ_k` is a
one-dimensional quotient of `kⁿ⁺¹`, that is a line of the dual, which the standard basis identifies
with a point of `ℙ k (Fin (n + 1) → k)`. This is the dictionary through which
`Faltings.ProjectiveEmbedding.height` reads the image of a `k`-point. -/
noncomputable def kPointProjectivization (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hy : y ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) :
    ℙ k (Fin (n + 1) → k) :=
  let b := Pi.basisFun k (Fin (n + 1))
  let q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (n + 1) → k) :=
    y ≫ (projectiveSpaceOfModuleIso b).inv
  have hq : q ≫ projectiveSpaceOfModuleToSpec k (Fin (n + 1) → k) = 𝟙 _ := by
    simp only [q, Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
    exact hy
  (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
      (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ ⟨q, hq⟩)).map
    b.toDualEquiv.symm.toLinearMap b.toDualEquiv.symm.injective

/-- The height relative to a projective embedding `φ` at `p` is the Weil height of the point
`Faltings.kPointProjectivization` of `φ(p)`. -/
theorem ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f]
    (φ : Faltings.ProjectiveEmbedding f n) (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) :
    φ.height p = Faltings.weilHeight (kPointProjectivization (p.1 ≫ φ.hom)
      (by rw [Category.assoc, φ.hom_over, p.2])) := rfl

/-- The value at a `k`-point `z` of the integral model `ℙⁿ_ℤ` lying in `D₊(Tᵢ)` of the affine
coordinate `T_j / T_i`. -/
noncomputable def intVal (z : Spec (.of k) ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1))
    (hi : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (j : Fin (n + 1)) : k :=
  (Scheme.ΓSpecIso (.of k)).hom (z.appLE _ ⊤ hi
    ((Proj.awayToSection (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)).hom
      (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j)))

/-- `intVal` only depends on the point and the chart, not on the proof that the point lies in
the chart. -/
theorem intVal_congr {z z' : Spec (.of k) ⟶ projectiveSpaceAtUniverse.{u} n} (hzz : z = z')
    {i i' : Fin (n + 1)} (hii : i = i')
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i')) :
    intVal z i h = intVal z' i' h' := by
  subst hzz hii; rfl

/-- The preimage of `D₊(Tᵢ)` of the polynomial model of `ℙⁿ_k` is that of `D₊(Tᵢ)` of `ℙⁿ_ℤ`. -/
private theorem preimage_basicOpen_polynomialComparison
    (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k))) (i : Fin (n + 1)) :
    (y ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ
        Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) =
      (y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
  rw [← Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_coordinateProjMap,
    ← Category.assoc]
  exact (congrArg ((y ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ ·)
    (Stacks.ProjectiveSpaceChartRatio.coordinateProjMap_preimage_basicOpen k n i)).symm

/-- The chart values of `y` in the polynomial model are its integral chart values. -/
private theorem chartVal_eq_intVal (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (i : Fin (n + 1))
    (hi : ⊤ ≤ (y ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
    (h' : ⊤ ≤ (y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) (j : Fin (n + 1)) :
    chartVal _ i hi j = intVal _ i h' j := by
  set w := y ≫ (polynomialComparison k n).iso.hom
  set cpm := coordinateProjMap k n (integralGradedHom k n) (mapDomain_integralGradedHom_eq_top k n)
  have he : Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) ≤
      cpm ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) :=
    (Stacks.ProjectiveSpaceChartRatio.coordinateProjMap_preimage_basicOpen k n i).ge
  have hwc : w ≫ cpm = y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) := by
    simp only [w, cpm, Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_coordinateProjMap]
  have key : ∀ h'', chartVal w i hi j = (Scheme.ΓSpecIso (.of k)).hom ((w ≫ cpm).appLE _ ⊤ h''
      ((Proj.awayToSection (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)).hom
        (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j))) := by
    intro h''
    unfold chartVal
    rw [← Stacks.ProjectiveSpaceChartRatio.chartBaseChange_coordFracAt,
      ← Stacks.ProjectiveSpaceChartRatio.appLE_awayToSection_coordinateProjMap k n i he,
      ← Scheme.Hom.appLE_comp_appLE w cpm _ _ ⊤ he hi]
    rfl
  rw [key (fun x hx => he (hi hx))]
  unfold intVal
  congr 1
  exact CategoryTheory.ConcreteCategory.congr_hom
    (Stacks.TwistPullbackPinned.appLE_congr_hom hwc _ _ _ _) _

/-- **The homogeneous coordinates of a `k`-point of `ℙⁿ_k` are its integral chart values.** If
the image `z` of `y` in the integral model `ℙⁿ_ℤ` lies in the chart `D₊(Tᵢ)`, then
`Faltings.kPointProjectivization y` is the class of the vector `((T_j / T_i)(z))_j`. -/
theorem kPointProjectivization_eq_mk_intVal
    (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hy : y ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) (i : Fin (n + 1))
    (h' : ⊤ ≤ (y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) :
    ∃ hne : intVal _ i h' ≠ 0,
      kPointProjectivization y hy = Projectivization.mk k (intVal _ i h') hne := by
  have hi : ⊤ ≤ (y ≫ (polynomialComparison k n).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k n) (MvPolynomial.X i) := by
    rwa [preimage_basicOpen_polynomialComparison]
  have heq : chartVal _ i hi = intVal _ i h' := funext (chartVal_eq_intVal y i hi h')
  refine ⟨heq ▸ chartVal_ne_zero _ i hi, ?_⟩
  have hw : (y ≫ (polynomialComparison k n).iso.hom) ≫ projToSpecCoeff k n = 𝟙 _ := by
    have h := (polynomialComparison k n).toBase
    simp only [Category.assoc, projToSpecCoeff] at h ⊢
    rw [h]
    exact hy
  exact (dictionary_eq_mk_chartVal y _ rfl hw i hi).trans (mk_congr heq _ _)

/-- Every `k`-point of `ℙⁿ_ℤ` lies in some standard chart `D₊(Tᵢ)`. -/
private theorem exists_chart_intVal (z : Spec (.of k) ⟶ projectiveSpaceAtUniverse.{u} n) :
    ∃ i, ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
  have hadj : Algebra.adjoin ↥(polyGrading (ULift.{u} ℤ) n 0)
      (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) =
        ⊤ := by
    refine eq_top_iff.2 fun P _ => ?_
    clear ‹P ∈ ⊤›
    induction P using MvPolynomial.induction_on with
    | C r =>
      exact Subalgebra.algebraMap_mem _
        (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
          (MvPolynomial.isHomogeneous_C _ r)⟩ : polyGrading (ULift.{u} ℤ) n 0)
    | add P Q hP hQ => exact Subalgebra.add_mem _ hP hQ
    | mul_X P i hP => exact Subalgebra.mul_mem _ hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  have htop := Proj.iSup_basicOpen_eq_top' (polyGrading (ULift.{u} ℤ) n)
    (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
    (fun i => ⟨1, X_mem_one (ULift.{u} ℤ) n i⟩) hadj
  have hmem : z (IsLocalRing.closedPoint k) ∈
      ⨆ i, Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
    rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  rwa [Subsingleton.elim a (IsLocalRing.closedPoint k)]

/-- Every point of `X` maps into some standard chart under a morphism to `ℙʳ_k`. -/
public theorem exists_mem_basicOpen {X : Scheme.{u}} {r : ℕ}
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (x : X) :
    ∃ j : Fin (r + 1), (t ≫ (polynomialComparison k r).iso.hom).base x ∈
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X j) := by
  have h := (iSup_basicOpen_X_eq_top k r).ge
    (Set.mem_univ ((t ≫ (polynomialComparison k r).iso.hom).base x))
  exact TopologicalSpace.Opens.mem_iSup.mp h

end Points

section ProjectiveSpacePoints

open Stacks.SectionsToProjectiveSpace

variable {k : Type u} [Field k] {n : ℕ}

/-- The `k`-point of `ℙⁿ_ℤ` with coordinates `t`, `t i = 1`, lies in the chart `D₊(Tᵢ)`. -/
public theorem top_le_preimage_projectiveSpacePoint (t : Fin (n + 1) → k)
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1)) (hti : t i = 1) :
    ⊤ ≤ projectiveSpacePoint (R := .of k) t ht ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
  have := Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n)
    (sectionsHom fun j => (Scheme.ΓSpecIso (.of k)).inv (t j))
    (map_irrelevant_eq_top _ (span_range_ΓSpecIso_inv (R := .of k) t ht)) Nat.one_pos
    (X_mem_coordGrading_one i)
  intro a _
  have hmem : a ∈ (Spec (.of k)).basicOpen
      ((sectionsHom fun j => (Scheme.ΓSpecIso (.of k)).inv (t j)) (MvPolynomial.X i)) := by
    rw [sectionsHom_X, hti, map_one, Scheme.basicOpen_one]; trivial
  rwa [← this] at hmem

/-- The point of `ℙᵐ_ℤ` with coordinates `c` is unchanged by scaling `c` by a unit. -/
public theorem projectiveSpacePoint_unit_mul {R : CommRingCat.{u}} {m : ℕ} (u : Rˣ)
    (c : Fin (m + 1) → R) (hc : Ideal.span (Set.range c) = ⊤)
    (huc : Ideal.span (Set.range fun i => (u : R) * c i) = ⊤) :
    projectiveSpacePoint (fun i => (u : R) * c i) huc = projectiveSpacePoint c hc := by
  have hfun : (fun i => (Scheme.ΓSpecIso R).inv.hom ((u : R) * c i)) = fun i =>
      ((Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom u : Γ(Spec R, ⊤)ˣ) : Γ(Spec R, ⊤)) *
        (Scheme.ΓSpecIso R).inv.hom (c i) := by
    funext i; rw [map_mul]; rfl
  unfold projectiveSpacePoint
  rw [toProjectiveSpaceAtUniverse_congr hfun _
    (by rw [← hfun]; exact span_range_ΓSpecIso_inv _ huc)]
  exact Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance _ _ _ _

/-- The integral chart values of the `k`-point of `ℙⁿ_ℤ` with coordinates `t`, `t i = 1`, in the
chart `D₊(Tᵢ)` are the `t j`. -/
theorem intVal_projectiveSpacePoint (t : Fin (n + 1) → k)
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1)) (hti : t i = 1)
    (h : ⊤ ≤ projectiveSpacePoint (R := .of k) t ht ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) :
    intVal (projectiveSpacePoint (R := .of k) t ht) i h = t := by
  funext j
  have := Stacks.TwistPullbackPinned.appLE_top_coordFrac
    (fun j => (Scheme.ΓSpecIso (.of k)).inv (t j)) (span_range_ΓSpecIso_inv (R := .of k) t ht) i j
    (by simp [hti]) h
  unfold intVal
  rw [show Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j =
    Stacks.TwistPullbackPinned.coordFrac.{u} i j from rfl]
  erw [this]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of k)).inv_hom_id (t j)

/-- **A `k`-point of `ℙⁿ_k` over the point `[c]` of the integral model reads as `[c]`.** If the
image of `y` in `ℙⁿ_ℤ` is `projectiveSpacePoint c`, then `Faltings.kPointProjectivization y` is
the class of `c`. -/
theorem kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint
    (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hy : y ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
    (c : Fin (n + 1) → k) (hcs : Ideal.span (Set.range c) = ⊤) (hc : c ≠ 0)
    (h : y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) c hcs) :
    kPointProjectivization y hy = Projectivization.mk k c hc := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  set t : Fin (n + 1) → k := fun j => (c i)⁻¹ * c j
  have hti : t i = 1 := inv_mul_cancel₀ hi
  have hts : Ideal.span (Set.range t) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by rw [hti]; exact isUnit_one)
  have hpt : projectiveSpacePoint (R := .of k) c hcs = projectiveSpacePoint (R := .of k) t hts :=
    (projectiveSpacePoint_unit_mul (R := .of k) (Units.mk0 _ (inv_ne_zero hi)) c hcs hts).symm
  have h0 := top_le_preimage_projectiveSpacePoint t hts i hti
  have h' : ⊤ ≤ (y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
    rwa [h, hpt]
  obtain ⟨hne, heq⟩ := kPointProjectivization_eq_mk_intVal y hy i h'
  have hval : intVal _ i h' = t :=
    (intVal_congr (h.trans hpt) rfl h' h0).trans (intVal_projectiveSpacePoint t hts i hti h0)
  rw [heq, mk_congr hval hne (hval ▸ hne)]
  exact (Projectivization.mk_eq_mk_iff' k _ _ _ hc).2 ⟨(c i)⁻¹, funext fun j => by simp [t]⟩

end ProjectiveSpacePoints

section SectionsMorphism

open Stacks.ProjectiveSpaceSections

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : X.Modules)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
  {n : ℕ} (s : Fin (n + 1) → L.sections) (hs : (⨆ i, nonvanishingChart L (s i)) = ⊤)

/-- **The pullback of `T_j / T_i` along the morphism defined by sections, at a point of the chart
`X_{sᵢ}`, is the value of the ratio `s_j / s_i`.** -/
private theorem appLE_morphismAtUniverse_coordFracAt (z : Spec (.of k) ⟶ X) (i j : Fin (n + 1))
    (hz : ⊤ ≤ z ⁻¹ᵁ nonvanishingChart L (s i))
    (h : ⊤ ≤ (z ≫ morphismAtUniverse L s hs) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) :
    (z ≫ morphismAtUniverse L s hs).appLE _ ⊤ h
        ((Proj.awayToSection (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)).hom
          (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j)) =
      z.appLE _ ⊤ hz (Stacks.SheafOfModules.divBySection (X := X.toRingedSpace) L (s i) le_rfl
        ((s j).eval (Opposite.op _))) := by
  set W := nonvanishingChart L (s i)
  have H : Set.range z.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hz trivial
  obtain ⟨z', rfl⟩ : ∃ z', z' ≫ W.ι = z := ⟨_, IsOpenImmersion.lift_fac _ _ H⟩
  have e' : (⊤ : W.toScheme.Opens) ≤ chartMorphism L s i ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
    rw [chartMorphism_preimage_basicOpen, chartRatio_self, Scheme.basicOpen_one]
  have hcomp : (z' ≫ W.ι) ≫ morphismAtUniverse L s hs = z' ≫ chartMorphism L s i := by
    rw [Category.assoc, nonvanishingChart_ι_morphismAtUniverse]
  have hι : W.ι.appLE W ⊤ (le_of_eq W.ι_preimage_self.symm) = W.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  have hspan : Ideal.span (Set.range (chartRatio L s i)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨i, chartRatio_self L s i⟩
  have h0 : (⊤ : (Spec (.of k)).Opens) ≤ (z' ≫ chartMorphism L s i) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := fun x _ => e' trivial
  refine (CategoryTheory.ConcreteCategory.congr_hom
    (Stacks.TwistPullbackPinned.appLE_congr_hom hcomp _ _ _ h0) _).trans ?_
  refine (CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE z' (chartMorphism L s i) _ ⊤ ⊤ e' le_top) _).symm.trans ?_
  refine (congrArg (z'.appLE ⊤ ⊤ le_top).hom
    (Stacks.TwistPullbackPinned.appLE_top_coordFrac (chartRatio L s i) hspan i j
      (chartRatio_self L s i) e')).trans ?_
  refine Eq.trans ?_ (CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE z' W.ι W ⊤ ⊤ (le_of_eq W.ι_preimage_self.symm) le_top) _)
  rw [CategoryTheory.ConcreteCategory.comp_apply, hι]
  rfl

end SectionsMorphism

section SegreValues

open Stacks.SheafOfModules Segre

variable {k : Type u} [Field k]

/-- **The ratio `X_a / X_i` of coordinate sections of `𝒪(1)` on `ℙⁿ_ℤ`, at a `k`-point of
`D₊(Xᵢ)`, is the value of the affine coordinate `X_a / X_i`.** -/
private theorem appLE_divBySection_coordinateSection {n : ℕ}
    (y : Spec (.of k) ⟶ projectiveSpaceAtUniverse.{u} n) (i a : Fin (n + 1))
    (hz : ⊤ ≤ y ⁻¹ᵁ nonvanishingOpen (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
    (h : ⊤ ≤ y ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) :
    y.appLE _ ⊤ hz (divBySection (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i) le_rfl
        ((coordinateSection.{u} n a).eval (Opposite.op _))) =
      y.appLE _ ⊤ h ((Proj.awayToSection (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)).hom
        (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i a)) := by
  have hDN := Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection
    (coordinateGrading.{u} n) (MvPolynomial.X i) (Stacks.ProjectiveChart.X_mem_degree_one _ i)
  have hinv : IsInvertible (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule (coordinateGrading.{u} n) 1) :=
    isInvertible_projectiveSpaceAtUniverseTwistingSheaf_one.{u} n
  refine (CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE y h (homOfLE hDN).op) _).symm.trans ?_
  have hfrac : HomogeneousLocalization.Away.isLocalizationElem
      (Stacks.ProjectiveChart.X_mem_degree_one (ULift.{u} ℤ) (n := n) i)
      (Stacks.ProjectiveChart.X_mem_degree_one _ a) =
        Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i a := by
    rw [HomogeneousLocalization.ext_iff_val, Away.val_mk,
      Stacks.ProjectiveSpaceChartRatio.coordFracAt, Away.val_mk]
    simp
  refine (CategoryTheory.ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
  refine (map_divBySection (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace) _ _ hDN
    le_rfl _).trans ?_
  refine (congrArg (divBySection (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace) _ _ _)
    (secRestr_sections_eval (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace) _ _
      hDN)).trans ?_
  exact (Stacks.ProjTwistSection.divBySection_homogeneousSection (coordinateGrading.{u} n)
    (MvPolynomial.X i) (MvPolynomial.X a) (Stacks.ProjectiveChart.X_mem_degree_one _ i)
    (Stacks.ProjectiveChart.X_mem_degree_one _ a)).trans (congrArg _ hfrac)

end SegreValues

section SegreRatio

open Stacks.SheafOfModules Segre Opposite Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.ProjTwistSection Stacks.ProjectiveSpaceSections

variable (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1))

/-- The Segre chart ratio `Z_{ab} / Z_{ij}` is the product of the pullbacks of `X_a / Xᵢ` and
`Y_b / Yⱼ`. -/
private theorem divBySection_segreSection_eq_mul (a : Fin (n + 1)) (b : Fin (m + 1))
    (hle : nonvanishingOpen (X := (Segre.segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
        (segreSection.{u} n m i j)
      ≤ segreFst.{u} n m ⁻¹ᵁ nonvanishingOpen
          (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i))
    (hleG : nonvanishingOpen (X := (Segre.segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
        (segreSection.{u} n m i j)
      ≤ segreSnd.{u} n m ⁻¹ᵁ nonvanishingOpen
          (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
          (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j)) :
    divBySection (X := (Segre.segreProduct.{u} n m).toRingedSpace) (segreModule.{u} n m)
        (segreSection.{u} n m i j) le_rfl
        ((segreSection.{u} n m a b).eval (op (nonvanishingOpen (segreModule.{u} n m)
          (segreSection.{u} n m i j))))
      = ((segreFst.{u} n m).appLE _ _ hle).hom
          (divBySection (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i) le_rfl
            ((coordinateSection.{u} n a).eval (op (nonvanishingOpen
              (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1)
              (coordinateSection.{u} n i)))))
        * ((segreSnd.{u} n m).appLE _ _ hleG).hom
          (divBySection (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
            (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j) le_rfl
            ((coordinateSection.{u} m b).eval (op (nonvanishingOpen
              (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1)
              (coordinateSection.{u} m j))))) := by
  have hVF := hle.trans (le_of_eq (preimage_nonvanishingOpen (segreFst.{u} n m)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i)))
  have hVG := hleG.trans (le_of_eq (preimage_nonvanishingOpen (segreSnd.{u} n m)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j)))
  refine Eq.trans (divBySection_tensorSections
    ((Scheme.Modules.pullback (segreFst.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1))
    ((Scheme.Modules.pullback (segreSnd.{u} n m)).obj
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1))
    (modulePullbackSection (segreFst.{u} n m).toLRSHom _ (coordinateSection.{u} n i))
    (modulePullbackSection (segreFst.{u} n m).toLRSHom _ (coordinateSection.{u} n a))
    (modulePullbackSection (segreSnd.{u} n m).toLRSHom _ (coordinateSection.{u} m j))
    (modulePullbackSection (segreSnd.{u} n m).toLRSHom _ (coordinateSection.{u} m b))
    hVF hVG) ?_
  exact congrArg₂ (· * ·)
    (divBySection_modulePullbackSection_of_le (segreFst.{u} n m)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i)
      (coordinateSection.{u} n a) le_rfl hle)
    (divBySection_modulePullbackSection_of_le (segreSnd.{u} n m)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j)
      (coordinateSection.{u} m b) le_rfl hleG)

end SegreRatio

section SegrePoints

open Stacks.SheafOfModules Segre Opposite Stacks.ProjectiveSpaceSections

variable {k : Type u} [Field k] {r m : ℕ}

/-- **The affine coordinates of the Segre image of a `k`-point are products.** On the chart
`D₊(Z_{ij})`, the value of `Z_{ab} / Z_{ij}` at the image under the Segre morphism of a `k`-point
`z` of `ℙʳ_ℤ ×_ℤ ℙᵐ_ℤ` is the product of the values of `X_a / X_i` and `Y_b / Y_j`. -/
private theorem intVal_segreMorphism (z : Spec (.of k) ⟶ Segre.segreProduct.{u} r m)
    (K L : Fin (r * m + r + m + 1))
    (hK : ⊤ ≤ (z ≫ Segre.segreMorphism.{u} r m) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) (r * m + r + m)) (MvPolynomial.X K))
    (h1 : ⊤ ≤ (z ≫ segreFst.{u} r m) ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) r)
      (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv r m K).1))
    (h2 : ⊤ ≤ (z ≫ segreSnd.{u} r m) ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) m)
      (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv r m K).2)) :
    intVal (z ≫ Segre.segreMorphism.{u} r m) K hK L =
      intVal (z ≫ segreFst.{u} r m) _ h1 (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).1 *
        intVal (z ≫ segreSnd.{u} r m) _ h2 (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).2 := by
  set i := (Stacks.ProductFamilyTwist.segreIndexEquiv r m K).1
  set j := (Stacks.ProductFamilyTwist.segreIndexEquiv r m K).2
  set a := (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).1
  set b := (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).2
  have hW := morphismAtUniverse_preimage_basicOpen (segreModule.{u} r m) (segreSections.{u} r m)
    (iSup_nonvanishingChart_segreSections_eq_top.{u} r m) K
  have hzW : ⊤ ≤ z ⁻¹ᵁ nonvanishingChart (segreModule.{u} r m) (segreSections.{u} r m K) :=
    fun x hx => hW.le (hK hx)
  have hle : nonvanishingOpen (X := (Segre.segreProduct.{u} r m).toRingedSpace)
        (segreModule.{u} r m) (segreSection.{u} r m i j)
      ≤ segreFst.{u} r m ⁻¹ᵁ nonvanishingOpen
          (X := (projectiveSpaceAtUniverse.{u} r).toRingedSpace)
          (projectiveSpaceAtUniverseTwistingSheaf.{u} r 1) (coordinateSection.{u} r i) :=
    (nonvanishingOpen_segreSection.{u} r m i j).le.trans inf_le_left
  have hleG : nonvanishingOpen (X := (Segre.segreProduct.{u} r m).toRingedSpace)
        (segreModule.{u} r m) (segreSection.{u} r m i j)
      ≤ segreSnd.{u} r m ⁻¹ᵁ nonvanishingOpen
          (X := (projectiveSpaceAtUniverse.{u} m).toRingedSpace)
          (projectiveSpaceAtUniverseTwistingSheaf.{u} m 1) (coordinateSection.{u} m j) :=
    (nonvanishingOpen_segreSection.{u} r m i j).le.trans inf_le_right
  have e1 := appLE_morphismAtUniverse_coordFracAt (segreModule.{u} r m) (segreSections.{u} r m)
    (iSup_nonvanishingChart_segreSections_eq_top.{u} r m) z K L hzW hK
  have e2 := divBySection_segreSection_eq_mul r m i j a b hle hleG
  have e3 := appLE_divBySection_coordinateSection (z ≫ segreFst.{u} r m) i a
    (fun x hx => hle (hzW hx)) h1
  have e4 := appLE_divBySection_coordinateSection (z ≫ segreSnd.{u} r m) j b
    (fun x hx => hleG (hzW hx)) h2
  unfold intVal
  rw [← map_mul]
  refine congrArg _ ((e1.trans (congrArg _ e2)).trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ _ ?_ ?_
  · exact (CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_comp_appLE z (segreFst.{u} r m) _ _ ⊤ hle hzW) _).trans e3
  · exact (CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_comp_appLE z (segreSnd.{u} r m) _ _ ⊤ hleG hzW) _).trans e4

/-- The point of `ℙ k (Fin (n + 1) → k)` does not depend on the proof that the point is a
section. -/
theorem kPointProjectivization_congr {n : ℕ}
    {y y' : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k))}
    (hyy : y = y') (hy : y ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
    (hy' : y' ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) :
    kPointProjectivization y hy = kPointProjectivization y' hy' := by
  subst hyy; rfl

/-- **The homogeneous coordinates of the Segre product at a `k`-point are the products of those
of the factors**, reindexed by `Stacks.ProductFamilyTwist.segreIndexEquiv`. -/
theorem exists_kPointProjectivization_segreProduct {X : Scheme.{u}}
    (f₁ : X ⟶ projectiveSpaceOver r (Spec (.of k))) (f₂ : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (h : f₁ ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) =
      f₂ ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) (p : Spec (.of k) ⟶ X)
    (hy : (p ≫ Faltings.segreProduct f₁ f₂ h) ≫
      projectiveSpaceOver (r * m + r + m) (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
    (hy₁ : (p ≫ f₁) ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
    (hy₂ : (p ≫ f₂) ≫ projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) :
    ∃ (P : Fin (r + 1) → k) (Q : Fin (m + 1) → k) (hP : P ≠ 0) (hQ : Q ≠ 0)
      (hPQ : (fun L => P (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).1 *
        Q (Stacks.ProductFamilyTwist.segreIndexEquiv r m L).2) ≠ 0),
      kPointProjectivization _ hy₁ = Projectivization.mk k P hP ∧
      kPointProjectivization _ hy₂ = Projectivization.mk k Q hQ ∧
      kPointProjectivization _ hy = Projectivization.mk k _ hPQ := by
  set z : Spec (.of k) ⟶ Segre.segreProduct.{u} r m := p ≫ pullback.lift f₁ f₂ h ≫
    pullback.lift (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)))
      (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
      (terminal.hom_ext _ _)
  have hz : (p ≫ Faltings.segreProduct f₁ f₂ h) ≫
      projectiveSpaceOver.toIntegralAtUniverse (r * m + r + m) (Spec (.of k)) =
        z ≫ Segre.segreMorphism.{u} r m := by
    simp only [z, Faltings.segreProduct, Faltings.segreMorphism, Category.assoc,
      projectiveSpaceOver.liftAtUniverse_toIntegralAtUniverse]
    rfl
  have hz₁ : z ≫ segreFst.{u} r m =
      (p ≫ f₁) ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) := by
    erw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.assoc]
  have hz₂ : z ≫ segreSnd.{u} r m =
      (p ≫ f₂) ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) := by
    erw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.assoc]
  obtain ⟨i, h1⟩ := exists_chart_intVal
    ((p ≫ f₁) ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)))
  obtain ⟨j, h2⟩ := exists_chart_intVal
    ((p ≫ f₂) ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
  obtain ⟨hP, hP1⟩ := kPointProjectivization_eq_mk_intVal (p ≫ f₁) hy₁ i h1
  obtain ⟨hQ, hQ1⟩ := kPointProjectivization_eq_mk_intVal (p ≫ f₂) hy₂ j h2
  set e := Stacks.ProductFamilyTwist.segreIndexEquiv r m
  set K := e.symm (i, j)
  have hK : e K = (i, j) := e.apply_symm_apply _
  have h1' : ⊤ ≤ (z ≫ segreFst.{u} r m) ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) r)
      (MvPolynomial.X (e K).1) := by
    rwa [hz₁, hK]
  have h2' : ⊤ ≤ (z ≫ segreSnd.{u} r m) ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) m)
      (MvPolynomial.X (e K).2) := by
    rwa [hz₂, hK]
  have hKz : ⊤ ≤ (z ≫ Segre.segreMorphism.{u} r m) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) (r * m + r + m)) (MvPolynomial.X K) :=
    fun x hx => (segreMorphism_preimage_standardOpen_eq_inf_basicOpen.{u} r m K).ge
      ⟨h1' hx, h2' hx⟩
  have hKy : ⊤ ≤ ((p ≫ Faltings.segreProduct f₁ f₂ h) ≫
      projectiveSpaceOver.toIntegralAtUniverse (r * m + r + m) (Spec (.of k))) ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) (r * m + r + m)) (MvPolynomial.X K) := by
    rwa [hz]
  obtain ⟨hR, hR1⟩ :=
    kPointProjectivization_eq_mk_intVal (p ≫ Faltings.segreProduct f₁ f₂ h) hy K hKy
  have hval : intVal _ K hKy = fun L => intVal _ i h1 (e L).1 * intVal _ j h2 (e L).2 := by
    funext L
    exact (congrFun (intVal_congr hz rfl hKy hKz) L).trans
      ((intVal_segreMorphism z K L hKz h1' h2').trans (congrArg₂ (· * ·)
        (congrFun (intVal_congr hz₁ (congrArg Prod.fst hK) h1' h1) _)
        (congrFun (intVal_congr hz₂ (congrArg Prod.snd hK) h2' h2) _)))
  exact ⟨_, _, hP, hQ, hval ▸ hR, hP1, hQ1, hR1.trans (mk_congr hval hR _)⟩

end SegrePoints

section Heights

variable {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

/-- Permuting the homogeneous coordinates does not change the Weil height. -/
public theorem weilHeight_mk_comp_equiv {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ]
    [LinearOrder κ] (e : κ ≃ ι) (v : ι → K) (hv : v ≠ 0) (hve : v ∘ e ≠ 0) :
    Faltings.weilHeight (Projectivization.mk K (v ∘ e) hve) =
      Faltings.weilHeight (Projectivization.mk K v hv) := by
  have hext : Function.extend e (v ∘ e) 0 = v := by
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp [e.injective.extend_apply]
  rw [← Faltings.weilHeight_mk_extend_zero e.injective (v ∘ e) hve]
  congr 1
  exact mk_congr (K := K) hext _ _

/-- **The height of the point with coordinates `P_a Q_b`, in any order, is `h(P) + h(Q)`.** -/
theorem weilHeight_mk_mul_comp_equiv {ι κ μ : Type*} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [LinearOrder κ] [Fintype μ] [LinearOrder μ] (e : μ ≃ ι × κ) (P : ι → K)
    (Q : κ → K) (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : (fun l => P (e l).1 * Q (e l).2) ≠ 0) :
    Faltings.weilHeight (Projectivization.mk K _ hPQ) =
      Faltings.weilHeight (Projectivization.mk K P hP) +
        Faltings.weilHeight (Projectivization.mk K Q hQ) := by
  let : LinearOrder (ι × κ) := LinearOrder.lift' e.symm e.symm.injective
  have hw : (fun ab : ι × κ => P ab.1 * Q ab.2) ≠ 0 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hP
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hQ
    exact Function.ne_iff.mpr ⟨(a, b), mul_ne_zero ha hb⟩
  rw [← Faltings.weilHeight_segreMap]
  have hseg : Faltings.segreMap (Projectivization.mk K P hP) (Projectivization.mk K Q hQ) =
      Projectivization.mk K _ hw := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K P hP
    obtain ⟨d, hd⟩ := Projectivization.exists_smul_eq_mk_rep K Q hQ
    rw [Faltings.segreMap, Projectivization.mk_eq_mk_iff']
    refine ⟨(c * d : K), funext fun ab => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← hc, ← hd, Units.smul_def]
    ring
  rw [hseg]
  exact weilHeight_mk_comp_equiv e _ hw hPQ

end Heights

end Faltings
