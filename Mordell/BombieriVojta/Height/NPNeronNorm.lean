module
public import Mordell.CurveProduct.Embedding.NP
public import Mordell.NeronTate.MumfordFormula.NP
public import Mordell.NeronTate.MumfordFormula.Theta
public import Mordell.Jacobian.Theta.Symmetry
public import Mordell.NeronTate.PhiMap
public import Mordell.NeronTate.Pairing.CauchySchwarz
public import Mordell.NeronTate.Pairing.Bilinear

/-!
# The height `h_{NP}` in terms of the Néron norm

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `(J, ι)` a Jacobian of `C`, `j = j_P : C → J` the Abel–Jacobi map, `θ` the class of the
theta divisor and `⟨x, y⟩ = ĥ_θ(x + y) - ĥ_θ(x) - ĥ_θ(y)` the Néron form on `J(k̄)`; for
`z ∈ C(k̄)` write `|z| = √⟨j z, j z⟩`. Let `N ≥ 2g + 1` and let `φ_{NP} : C → ℙⁿ` be a
projective embedding over `k` with `φ_{NP}^* 𝒪(1)` of class `NP`, with height
`h_{NP}(z) = h(φ_{NP}(z))`. Then there is a constant `c_{NP}` with
`|h_{NP}(z) - (N / 2g) |z|²| ≤ c_{NP} (1 + |z|)` for every `z ∈ C(k̄)`.

The error is `O(|z|)` and not `O(1)`: `h_{NP} = (N / g) ĥ_{θ⁻} + O(1)` by Mumford's formula,
and `ĥ_{θ⁻} = |z|² / 2 - ĥ_{θ - θ⁻} / 2`, where the odd part `ĥ_{θ - θ⁻}` is linear, hence
`O(|z|)`.

## Main results

* `Faltings.exists_abs_weilHeight_sub_neronPairing_le`: the estimate.

## Implementation notes

The Néron form is `Faltings.neronPairing`, on the Jacobian `A : Faltings.Jacobian k X.f`, for
the Abel–Jacobi map `j` (`Faltings.IsAbelJacobiMap`) and the reduced effective Cartier divisor
`D` whose support is `Faltings.thetaDivisor`. A point of `C(k̄)` is a morphism `Spec k̄ ⟶ C`
over `Spec k`, and `j z` is the composite `z ≫ j`.

The embedding `φ_{NP}` is any closed immersion `C ⟶ ℙⁿ_k` over `k` whose pull-back of the
twisting sheaf `𝒪(1)` of `ℙⁿ_ℤ` has class `N • ∑ nₓ [𝒪_C(x)]`; the embedding of a `k`-basis of
`H⁰(C, 𝒪(NP))` (`Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver`) is
one. Only this class enters the proof, through the height machine. The point `φ_{NP}(z)` is
read on the integral model `ℙⁿ_ℤ` as the `k̄`-point `projectiveSpacePoint c` with homogeneous
coordinates `c ∈ k̄ⁿ⁺¹ \ {0}`, and `h_{NP}(z)` is the absolute logarithmic Weil height
`Faltings.weilHeight` of `[c] ∈ ℙ k̄ (k̄ⁿ⁺¹)`; every `k̄`-point of `ℙⁿ_ℤ` has such coordinates,
determined up to a scalar. The norm `|z|` is `Real.sqrt`, and `|z|²` is read literally as
`√⟨z, z⟩ ^ 2`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5, proof of Lemma 2,
  and the Errata-Corrige (1991), correction to page 638
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

section Heights

variable {k : Type u} [Field k] {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)}
  [IsProjectiveVariety k f] [Smooth f]

/-- The class of a projective embedding `φ` with `φ^* 𝒪(1) ≅ g^* L` is the pull-back class of
`[L]` along `g`. -/
private lemma embeddingClass_eq_pullbackPicardClass {n : ℕ} (φ : ProjectiveEmbedding f n)
    {Z : Scheme.{u}} (g : Y ⟶ Z) (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatIsSheaf L)
    (hφ : Nonempty ((Scheme.Modules.pullback
      (φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅
          (Scheme.Modules.pullback g).obj L)) :
    embeddingClass f (FreeAbelianGroup.of ⟨n, φ⟩) =
      Stacks.SheafOfModules.pullbackPicardClass g L hL := by
  rw [embeddingClass_apply_of]
  refine (Y.picardClass_eq_iff _ _ _ _).mpr ⟨?_⟩
  exact (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    φ.hom.toLRSHom.toShHom).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction φ.hom)).app _).symm ≪≫
    (Scheme.Modules.pullbackComp φ.hom _).app _ ≪≫ hφ.some ≪≫
    (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    g.toLRSHom.toShHom).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction g)).app _)

end Heights

/-- The first component of `lift f g` in the cartesian monoidal structure of `Over S`. -/
private lemma lift_left_fst {S : Scheme.{u}} {W X Y : Over S} (f : W ⟶ X) (g : W ⟶ Y) :
    (CartesianMonoidalCategory.lift f g).left ≫ pullback.fst X.hom Y.hom = f.left :=
  congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst f g)

/-- The second component of `lift f g` in the cartesian monoidal structure of `Over S`. -/
private lemma lift_left_snd {S : Scheme.{u}} {W X Y : Over S} (f : W ⟶ X) (g : W ⟶ Y) :
    (CartesianMonoidalCategory.lift f g).left ≫ pullback.snd X.hom Y.hom = g.left :=
  congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd f g)

/-- A choice satisfying a hypothesis-guarded specification: from `∀ κ, (∀ h : P, κ = F h) → Q κ`
in a nonempty type, some `κ` satisfies `Q`. -/
private lemma exists_of_forall_eq_imp {α : Sort*} [Nonempty α] {P : Prop} {F : P → α}
    {Q : α → Prop} (H : ∀ κ, (∀ h : P, κ = F h) → Q κ) : ∃ κ, Q κ := by
  by_cases hP : P
  · exact ⟨F hP, H _ fun _ => rfl⟩
  · exact ⟨Classical.arbitrary α, H _ fun h => absurd h hP⟩

/-- The closing estimate: if `|h - (N / g) F| ≤ B` with `F = ½ p - ½ q` and `|q| ≤ √p κ`, then
`|h - (N / 2g) (√p)²| ≤ max B ((N / 2g) κ) (1 + √p)`. -/
private lemma abs_sub_div_mul_sqrt_sq_le {h F p q N g B κ : ℝ} (hg : 0 < g) (hN : 0 ≤ N)
    (hp : 0 ≤ p) (hB : |h - N / g * F| ≤ B) (hF : F = 1 / 2 * p - 1 / 2 * q)
    (hq : |q| ≤ √p * κ) :
    |h - N / (2 * g) * √p ^ 2| ≤ max B (N / (2 * g) * κ) * (1 + √p) := by
  have hN' : 0 ≤ N / (2 * g) := by positivity
  have hq' : |N / (2 * g) * q| ≤ N / (2 * g) * κ * √p := by
    rw [abs_mul, abs_of_nonneg hN', mul_assoc, mul_comm κ]
    exact mul_le_mul_of_nonneg_left hq hN'
  have heq : h - N / (2 * g) * √p ^ 2 = (h - N / g * F) - N / (2 * g) * q := by
    rw [Real.sq_sqrt hp, hF]; field_simp; ring
  rw [heq]
  calc _ ≤ |h - N / g * F| + |N / (2 * g) * q| := abs_sub _ _
    _ ≤ B + N / (2 * g) * κ * √p := add_le_add hB hq'
    _ ≤ _ := by
      nlinarith [Real.sqrt_nonneg p, le_max_left B (N / (2 * g) * κ),
        le_max_right B (N / (2 * g) * κ)]

variable {k : Type u} [Field k]

/-- The odd part `ĥ_{θ - θ⁻}` of the theta height is `⟨·, y₀⟩` for some `y₀ ∈ J(K)`. -/
private lemma exists_eq_neronPairing_of_isNeronTateHeight_sub [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let classK : A.J.left.picardGroup → ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      fun c ↦ (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) c
    let pt : Additive (Over.mk φK ⟶ A.J) → {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} :=
      fun z ↦ ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
    let θ := Stacks.Divisors.picardClass D
    let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
    ∃ y₀ : Additive (Over.mk φK ⟶ A.J),
      ∀ f'' : {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} → ℝ,
        IsNeronTateHeight JK (classK (θ - θm)) f'' → ∀ x,
          f'' (pt x) = neronPairing X A hg j hj D hrad hsupp K x y₀ := by
  haveI := A.isAbelianVariety
  letI : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  intro φK JK classK pt θ θm
  haveI : Nonempty (Over.mk φK ⟶ A.J) := ⟨1⟩
  obtain ⟨κ, -, hκ⟩ := exists_of_forall_eq_imp
    (schemePullbackClass_thetaNeg_eq_translate X A hg j hj D hrad hsupp K)
  refine ⟨.ofMul κ⁻¹, fun f'' hf'' x => ?_⟩
  let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left := classK θ
  let y : Over.mk (𝟙 (Spec (.of K))) ⟶ JK := GroupScheme.toBaseChange φK A.J κ⁻¹
  have hphi := neronTateBilinear_isNeronTateHeight_phi JK θK y
  have htrans : (𝟙 JK * (Over.homMk JK.hom ≫ y : JK ⟶ JK)).left ≫ pullback.fst A.J.hom φK =
      (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.J (Over.mk φK))
        (CartesianMonoidalCategory.snd A.J (Over.mk φK) ≫ κ⁻¹) ≫ μ[A.J]).left := by
    have key : ∀ g : JK ⟶ JK, g.left ≫ pullback.fst A.J.hom φK =
        (((Over.mapPullbackAdj φK).homEquiv JK A.J).symm g).left := by
      intro g
      simp [Over.mapPullbackAdj]
    have hmul : ∀ a b : JK ⟶ JK, ((Over.mapPullbackAdj φK).homEquiv JK A.J).symm (a * b) =
        ((Over.mapPullbackAdj φK).homEquiv JK A.J).symm a *
          ((Over.mapPullbackAdj φK).homEquiv JK A.J).symm b := by
      intro a b
      apply ((Over.mapPullbackAdj φK).homEquiv JK A.J).injective
      rw [mapPullbackAdj_homEquiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    rw [key, hmul, Hom.mul_def, Over.comp_left, Over.comp_left]
    congr 1
    apply pullback.hom_ext
    · rw [lift_left_fst, lift_left_fst, ← key, Over.id_left, Category.id_comp]
      rfl
    · rw [lift_left_snd, lift_left_snd, ← key, Over.comp_left, Over.comp_left]
      simp only [y, Over.homMk_left, Category.assoc]
      erw [pullback.lift_fst]
      rfl
  have hcls : (Stacks.Picard.schemePullbackClassHom
      (𝟙 JK * (Over.homMk JK.hom ≫ y : JK ⟶ JK)).left).toIntLinearMap.baseChange ℚ θK - θK =
        classK (θ - θm) := by
    simp only [θK, classK, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
    rw [← TensorProduct.tmul_sub]
    congr 1
    change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ θ) -
        Stacks.Picard.schemePullbackClass _ θ = Stacks.Picard.schemePullbackClass _ (θ - θm)
    rw [Stacks.Picard.schemePullbackClass_comp, htrans]
    refine Eq.trans ?_
      (map_sub (Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)) θ θm).symm
    exact hκ.symm
  rw [hf''.unique (hcls ▸ hphi)]
  change neronTateBilinear JK θK ((GroupScheme.toBaseChangeHom φK A.J).toAdditive x)
    ((GroupScheme.toBaseChangeHom φK A.J).toAdditive (.ofMul κ⁻¹)) = _
  unfold neronTateBilinear neronPairing
  simp only [QuadraticMap.polar]
  rw [← map_add]
  rfl

/-- The base change `φ_{NP, K} : C_K ⟶ ℙⁿ_K` of `φ_{NP}` has a height `h` associated to the class
of `NP` on `C_K`, and `h` is the Weil height of the homogeneous coordinates of `φ_{NP}(z)`. -/
private lemma exists_isHeightOfClass_eq_weilHeight [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (N : ℕ)
    {n : ℕ} (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
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
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    [IsProjectiveVariety K (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    ∃ h : {s : Spec (.of K) ⟶ pullback X.f φK // s ≫ pullback.snd X.f φK = 𝟙 _} → ℝ,
      IsHeightOfClass (pullback.snd X.f φK)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f φK)
            ((N : ℤ) • X.classP) ⊗ₜ (1 : ℚ)) h ∧
      ∀ s (c : Fin (n + 1) → K) (hc0 : c ≠ 0) (hcs : Ideal.span (Set.range c) = ⊤),
        s.1 ≫ pullback.fst X.f φK ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
          projectiveSpacePoint (R := CommRingCat.of K) c hcs →
        h s = weilHeight (Projectivization.mk K c hc0) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  intro φK
  have e₂ : φNP ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = X.f := hφNP
  let ψ : pullback X.f φK ⟶ projectiveSpaceOver n (Spec (.of K)) :=
    pullback.lift (pullback.snd X.f φK)
      (pullback.fst X.f φK ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _)
      (terminal.hom_ext _ _)
  have hψ₂ : ψ ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
      pullback.fst X.f φK ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _ :=
    pullback.lift_snd _ _ _
  have hψci : IsClosedImmersion ψ := by
    let ψk : projectiveSpaceOver n (Spec (.of K)) ⟶ projectiveSpaceOver n (Spec (.of k)) :=
      pullback.map _ _ _ _ φK (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (by simp)
    have hP : IsPullback (pullback.fst (terminal.from (Spec (.of K)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n))) ψk φK
        (pullback.fst (terminal.from (Spec (.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
      refine (IsPullback.of_right (h₁₂ := pullback.snd _ _) (v₁₃ := terminal.from _)
        (h₂₂ := terminal.from _) ?_ (by simp [ψk]) (IsPullback.of_hasPullback _ _).flip).flip
      have e₁ : ψk ≫ pullback.snd (terminal.from (Spec (.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = pullback.snd _ _ := by simp [ψk]
      rw [e₁, show φK ≫ terminal.from (Spec (.of k)) = terminal.from _ from
        terminal.hom_ext _ _]
      exact (IsPullback.of_hasPullback _ _).flip
    have hsq : IsPullback ψ (pullback.fst X.f φK) ψk φNP := by
      refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := φK)
        (h₂₂ := pullback.fst _ _) ?_ ?_ hP
      · have e₁ : ψ ≫ pullback.fst (terminal.from (Spec (.of K)))
            (terminal.from (projectiveSpaceAtUniverse.{u} n)) = pullback.snd X.f φK :=
          pullback.lift_fst _ _ _
        rw [e₁, e₂]
        exact (IsPullback.of_hasPullback X.f φK).flip
      · apply pullback.hom_ext
        · simp only [ψ, ψk, Category.assoc, pullback.lift_fst]
          erw [pullback.lift_fst_assoc]
          rw [e₂]
          exact (pullback.condition (f := X.f) (g := φK)).symm
        · simp only [ψ, ψk, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip
      ‹IsClosedImmersion φNP›
  let E : ProjectiveEmbedding (pullback.snd X.f φK) n :=
    ⟨ψ, hψci, pullback.lift_fst _ _ _⟩
  refine ⟨E.height, ?_, fun s c hc0 hcs hs => ?_⟩
  · let L : X.C.Modules :=
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      (Scheme.Modules.pullback φNP).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1))
    have hLi : Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatIsSheaf L :=
      (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
        _).mpr ‹_›
    have hcl : embeddingClass (pullback.snd X.f φK) (FreeAbelianGroup.of ⟨n, E⟩) =
        Stacks.Picard.schemePullbackClassHom (pullback.fst X.f φK) ((N : ℤ) • X.classP) := by
      rw [embeddingClass_eq_pullbackPicardClass E (pullback.fst X.f φK) L hLi
        ⟨eqToIso (by rw [hψ₂]) ≪≫
          (Scheme.Modules.pullbackComp (pullback.fst X.f φK)
            (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).symm.app _ ≪≫
          (Scheme.Modules.pullback (pullback.fst X.f φK)).mapIso
            ((Scheme.Modules.pullbackComp φNP (projectiveSpaceOver.toIntegralAtUniverse n _)).app
              (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)).symm⟩]
      refine (Stacks.SheafOfModules.pullbackPicardHom_picardClass
        (pullback.fst X.f φK) L hLi).symm.trans ?_
      rw [← schemePullbackClassHom_eq_pullbackPicardHom]
      congr 1
    rw [← hcl]
    exact isHeightOfClass_height E
  · rw [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization]
    congr 1
    refine kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint _ _ c hcs hc0 ?_
    change s.1 ≫ ψ ≫ projectiveSpaceOver.toIntegralAtUniverse n _ = _
    rw [hψ₂, hs]

/-- **`h_{NP}` in terms of the Néron norm.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a
number field `k` with a divisor of degree one, `A = (J, ι)` a Jacobian, `j = j_P` the
Abel–Jacobi map, `D` the reduced divisor with support the theta divisor, `N ≥ 2g + 1`, and
`φ : C ⟶ ℙⁿ_k` a closed immersion over `k` with `φ^* 𝒪(1)` of class `N • P`. There is a
constant `c` such that, with `K = k̄` and `|z| = √(neronPairing (j z) (j z))`, every `z ∈ C(K)`
and every coordinate vector `c' ≠ 0` of `φ(z)` satisfy
`|weilHeight [c'] - (N / 2g) |z|²| ≤ c (1 + |z|)`. -/
@[faltings "lem_bv_height_np_neron_tate"]
theorem exists_abs_weilHeight_sub_neronPairing_le {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n : ℕ} (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
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
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let norm : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) → ℝ :=
      fun z => √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp K
        (.ofMul (z ≫ j)) (.ofMul (z ≫ j)))
    ∃ cNP : ℝ, ∀ (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)
      (c : Fin (n + 1) → K) (hc0 : c ≠ 0),
      z.left ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _ =
          projectiveSpacePoint (R := CommRingCat.of K) c (by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hc0
            exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ne.isUnit hi)) →
        |weilHeight (Projectivization.mk K c hc0) -
            N / (2 * genus X.f) * norm z ^ 2| ≤ cNP * (1 + norm z) := by
  intro norm
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  have hg1 : 1 ≤ genus X.f := Nat.le_of_succ_le hg
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsVariety K (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
  haveI : IsProjectiveVariety K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(IsProjectiveVariety.isProjective (f := X.f)).baseChange _⟩
  haveI := A.isAbelianVariety
  obtain ⟨h, hh, hW⟩ := exists_isHeightOfClass_eq_weilHeight X N φNP hφNP hφNPL K
  let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
  let θ := Stacks.Divisors.picardClass D
  let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
  obtain ⟨f', hf'⟩ := exists_isNeronTateHeight_of_isAlgebraic JK
    ((1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) θm)
  obtain ⟨f'', hf''⟩ := exists_isNeronTateHeight_of_isAlgebraic JK
    ((1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) (θ - θm))
  obtain ⟨B, hB⟩ := IsHeightOfClass.exists_abs_sub_neronTateHeight_le X A hg1 j hj D hrad hsupp
    K N (by omega) h f' hh hf'
  have hθ := neronTateHeight_pullbackInv_eq_half_neronPairing_sub X A hg1 j hj D hrad hsupp K
    f' f'' hf' hf''
  obtain ⟨y₀, hy₀⟩ := exists_eq_neronPairing_of_isNeronTateHeight_sub X A hg1 j hj D hrad hsupp K
  refine ⟨max B (N / (2 * genus X.f) * √(neronPairing X A hg1 j hj D hrad hsupp K y₀ y₀)),
    fun z c hc0 hz => ?_⟩
  let s : {s : Spec (.of K) ⟶ pullback X.f φK // s ≫ pullback.snd X.f φK = 𝟙 _} :=
    ⟨pullback.lift z.left (𝟙 _) (by simpa using Over.w z), pullback.lift_snd _ _ _⟩
  have hs : h s = weilHeight (Projectivization.mk K c hc0) :=
    hW s c hc0 _ (by
      change pullback.lift z.left (𝟙 _) _ ≫ pullback.fst X.f φK ≫ φNP ≫ _ = _
      erw [pullback.lift_fst_assoc]
      exact hz)
  have hpt : (⟨pullback.lift (s.1 ≫ pullback.fst X.f φK ≫ j.left) (𝟙 _)
      (by simp only [Category.assoc, Over.w j, Over.mk_hom, Category.id_comp]
          rw [pullback.condition, reassoc_of% s.2]), pullback.lift_snd _ _ _⟩ :
        {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _}) =
      ⟨pullback.lift (Additive.ofMul (z ≫ j)).toMul.left (𝟙 _) (by simpa using Over.w z),
        pullback.lift_snd _ _ _⟩ :=
    Subtype.ext (by
      apply pullback.hom_ext
      · simp only [pullback.lift_fst]
        erw [pullback.lift_fst_assoc]
        rfl
      · simp only [pullback.lift_snd])
  have hBz := hB s
  dsimp only at hBz
  rw [hpt] at hBz
  rw [← hs]
  refine abs_sub_div_mul_sqrt_sq_le (by exact_mod_cast (by omega : 0 < genus X.f)) N.cast_nonneg
    (neronPairing_self_nonneg X A hg1 j hj D hrad hsupp K _) hBz (hθ (.ofMul (z ≫ j))) ?_
  rw [hy₀ f'' hf'']
  exact abs_neronPairing_le_sqrt_mul_sqrt X A hg1 j hj D hrad hsupp K _ y₀

end Faltings
