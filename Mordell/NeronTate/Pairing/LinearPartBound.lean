module

public import Mordell.NeronTate.PhiMap
public import Mordell.NeronTate.Pairing.Bilinear
public import Mordell.Jacobian.Theta.Symmetry
public import Mordell.Jacobian.Autoduality.Ample
public import Mordell.NeronTate.Pairing.SelfHeight
public import Mordell.NeronTate.Nonneg
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbedding
public import Mordell.NeronTate.Pairing.CauchySchwarz

/-!
# The linear part of the height of θ is bounded by the Néron norm

Let `k` be a number field, `(C, P)` a curve over `k` with a divisor of degree one, of genus
`g ≥ 1`, `(J, ι)` a Jacobian, `θ` the class of the theta divisor and `θ⁻ = [-1]^* θ`. Over an
algebraic closure `K` of `k`, Riemann's symmetry of the theta divisor
(`Faltings.schemePullbackClass_thetaNeg_eq_translate`) writes
`θ - θ⁻ = φ_θ(y₀) = τ_{y₀}^* θ - θ` for the point `y₀ = -κ ∈ J(K)`. The Néron–Tate height of
`φ_θ(y₀)` is `x ↦ B_θ(x, y₀)` (`Faltings.neronTateBilinear_isNeronTateHeight_phi`), and
`B_θ(x, y₀) = ⟨x, y₀⟩` is the Néron pairing. The bound `|ĥ_{θ-θ⁻}(x)| ≤ |y₀| |x|` is then the
Cauchy–Schwarz inequality for the Néron form (`Faltings.abs_neronPairing_le_sqrt_mul_sqrt`).

## Main results

* `Faltings.exists_neronPairing_eq_of_isNeronTateHeight_sub_neg`: `ĥ_{θ-θ⁻}(x) = ⟨x, y₀⟩` and
  `|ĥ_{θ-θ⁻}(x)| ≤ √⟨y₀, y₀⟩ √⟨x, x⟩` for all `x ∈ J(K)`.

## Implementation notes

As in `Faltings.neronPairing`, heights live on the base change `J_K` of `J` to `K`, the class of
`θ` there is `θ_K = 1 ⊗ (pull-back of θ along J_K ⟶ J)` in `ℚ ⊗ Pic(J_K)`, and
`θ_K⁻` is its pull-back along the inversion `ι[J_K]` of `J_K`. A point `x : Spec K ⟶ J` over
`k` is read on `J_K` as the section `(x, 1)`. The Néron–Tate height `ĥ_{θ-θ⁻}` is any function
`f` with `Faltings.IsNeronTateHeight J_K (θ_K - θ_K⁻) f`; the conclusion is stated for all of
them with one `y₀`, which is the source's statement since the Néron–Tate height is unique.

Translation `τ_y` on the base change `J_K`, followed by the projection `J_K ⟶ J`, is the
translate `(x, t) ↦ x · y(t)` of `J ⊗ Spec K` in which Riemann's symmetry is stated; this is read
off through the bijection `J_K(T) ≃ J(T)` of points.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

section Translation

open CartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translation by `y` on the base change `A_K`, followed by the projection `A_K ⟶ A`, is the
translate `(x, t) ↦ x · y(t)` of `A ⊗ Spec K`. -/
public lemma translate_left_comp_fst
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A
    (𝟙 JK * (Over.homMk JK.hom ≫ GroupScheme.toBaseChange φK A y : JK ⟶ JK)).left ≫
        pullback.fst A.hom φK =
      (lift (fst A (Over.mk φK)) (snd A (Over.mk φK) ≫ y) ≫ μ[A]).left := by
  intro φK JK
  let e : MonoidalCategoryStruct.tensorObj A (Over.mk φK) ⟶ (Over.map φK).obj JK :=
    Over.homMk (𝟙 _) (by simp [JK, pullback.condition])
  have h₁ : e ≫ GroupScheme.pointsMulEquiv φK A JK (𝟙 JK) = fst A (Over.mk φK) := by
    ext; simp [e]
  have h₂ : e ≫ GroupScheme.pointsMulEquiv φK A JK
      (Over.homMk JK.hom ≫ GroupScheme.toBaseChange φK A y) =
      snd A (Over.mk φK) ≫ y := by
    ext; simp [e, GroupScheme.toBaseChange]; rfl
  have H : e ≫ GroupScheme.pointsMulEquiv φK A JK
      (𝟙 JK * (Over.homMk JK.hom ≫ GroupScheme.toBaseChange φK A y)) =
        fst A (Over.mk φK) * (snd A (Over.mk φK) ≫ y) := by
    refine (congrArg (e ≫ ·) ((GroupScheme.pointsMulEquiv φK A JK).map_mul _ _)).trans ?_
    rw [MonObj.comp_mul, h₁, h₂]
  have := congrArg Over.Hom.left H
  rw [Over.comp_left, GroupScheme.pointsMulEquiv_apply_left, Hom.mul_def] at this
  exact (Category.id_comp _).symm.trans this

end Translation

/-- If `Q b` holds for every `b` that equals `F h` whenever `h : p`, then `Q b` holds for some
`b`. -/
public lemma exists_of_forall_forall_eq {β : Sort*} {p : Prop} {F : p → β} {Q : β → Prop}
    (b₀ : β) (H : ∀ b, (∀ h, b = F h) → Q b) : ∃ b, Q b := by
  classical
  exact ⟨_, H (if h : p then F h else b₀) fun h => by simp [h]⟩

/-- **Riemann's symmetry**, in the form used here: over `K`, `θ - θ⁻ = τ_{y₀}^* θ - θ` for a
point `y₀ ∈ J(K)`. -/
public lemma exists_sub_pullbackInv_eq_translate {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)
        (Stacks.Divisors.picardClass D)
    ∃ y₀ : Over.mk φK ⟶ A.J,
      θK - (Stacks.Picard.schemePullbackClassHom ι[JK].left).toIntLinearMap.baseChange ℚ θK =
        (Stacks.Picard.schemePullbackClassHom
          (𝟙 JK * (Over.homMk JK.hom ≫ GroupScheme.toBaseChange φK A.J y₀ : JK ⟶ JK)).left
            ).toIntLinearMap.baseChange ℚ θK - θK := by
  have := A.isAbelianVariety
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  intro φK JK θK
  obtain ⟨κ, -, hR⟩ := exists_of_forall_forall_eq 1
    (schemePullbackClass_thetaNeg_eq_translate X A hg j hj D hrad hsupp K)
  refine ⟨κ⁻¹, ?_⟩
  have hc {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x) :
      Stacks.Picard.schemePullbackClassHom f (Stacks.Picard.schemePullbackClassHom g x) =
        Stacks.Picard.schemePullbackClassHom (f ≫ g) x :=
    Stacks.Picard.schemePullbackClass_comp f g x
  have hι : ι[JK].left ≫ pullback.fst A.J.hom φK = pullback.fst A.J.hom φK ≫ ι[A.J].left := by
    change ((Over.pullback φK).map ι[A.J]).left ≫ _ = _
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hτ := translate_left_comp_fst A.J κ⁻¹
  have hfst : (SemiCartesianMonoidalCategory.fst A.J (Over.mk φK)).left =
      pullback.fst A.J.hom φK := by simp
  rw [AbelianVariety.phiMap, hfst] at hR
  simp only [θK, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, hc, hι]
  rw [← TensorProduct.tmul_sub, ← TensorProduct.tmul_sub, ← hc, hτ]
  exact congrArg _ hR

/-- The bilinear form `B_θ` of `ĥ_θ` on `J_K(K)`, read on `J(K)` through `x ↦ (x, 1)`, is the
Néron pairing. -/
public lemma neronTateBilinear_toBaseChange {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)
        (Stacks.Divisors.picardClass D)
    ∀ x y : Over.mk φK ⟶ A.J,
      neronTateBilinear JK θK (.ofMul (GroupScheme.toBaseChange φK A.J x))
          (.ofMul (GroupScheme.toBaseChange φK A.J y)) =
        neronPairing X A hg j hj D hrad hsupp K (.ofMul x) (.ofMul y) := by
  have := A.isAbelianVariety
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  intro φK JK θK x y
  rw [neronTateBilinear_apply]
  simp only [neronPairing, QuadraticMap.polar, Function.comp_apply, ← ofMul_mul, toMul_ofMul]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg _ (Subtype.ext ?_)) rfl) rfl
  exact congrArg Over.Hom.left (GroupScheme.toBaseChange_mul φK A.J x y).symm

/-- Over an algebraic closure `K` of the number field `k`, the Néron–Tate height `f` of
`θ - θ⁻` on the Jacobian is a linear form of the Néron pairing: there is `y₀ ∈ J(K)` with
`f(x) = ⟨x, y₀⟩` (`Faltings.neronPairing`), hence `|f(x)| ≤ √⟨y₀, y₀⟩ · √⟨x, x⟩`, for all
`x ∈ J(K)`. -/
@[faltings "lem_nt_odd_part_linear_bound"]
theorem exists_neronPairing_eq_of_isNeronTateHeight_sub_neg {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI := A.isAbelianVariety
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let θK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK)
        (Stacks.Divisors.picardClass D)
    let θKneg : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      (Stacks.Picard.schemePullbackClassHom ι[JK].left).toIntLinearMap.baseChange ℚ θK
    let pt : Additive (Over.mk φK ⟶ A.J) →
        {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} :=
      fun z ↦ ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
    ∃ y₀ : Additive (Over.mk φK ⟶ A.J),
      ∀ f : {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} → ℝ,
        IsNeronTateHeight JK (θK - θKneg) f → ∀ x,
          f (pt x) = neronPairing X A hg j hj D hrad hsupp K x y₀ ∧
          |f (pt x)| ≤ √(neronPairing X A hg j hj D hrad hsupp K y₀ y₀) *
            √(neronPairing X A hg j hj D hrad hsupp K x x) := by
  have := A.isAbelianVariety
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  intro φK JK θK θKneg pt
  obtain ⟨y₀, hy₀⟩ := exists_sub_pullbackInv_eq_translate X A hg j hj D hrad hsupp K
  refine ⟨.ofMul y₀, fun f hf x ↦ ?_⟩
  have hphi := neronTateBilinear_isNeronTateHeight_phi JK θK (GroupScheme.toBaseChange φK A.J y₀)
  rw [← hy₀] at hphi
  have hval : f (pt x) = neronPairing X A hg j hj D hrad hsupp K x (.ofMul y₀) := by
    rw [hf.unique hphi]
    exact neronTateBilinear_toBaseChange X A hg j hj D hrad hsupp K x.toMul y₀
  refine ⟨hval, ?_⟩
  rw [hval]
  exact (abs_neronPairing_le_sqrt_mul_sqrt X A hg j hj D hrad hsupp K x _).trans_eq (mul_comm _ _)

end Faltings
