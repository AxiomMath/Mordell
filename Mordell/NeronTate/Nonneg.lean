module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.PicardPullback
public import Mordell.AbelianVariety.EvenOddClass
public import Mordell.NeronTate.Basic
public import Mordell.AlgebraicGeometry.Ample
public import Mordell.Height.Class.Functoriality
public import Mordell.Height.Class.AmpleBoundedBelow
public import Mordell.NeronTate.Existence
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower

/-!
# The Néron–Tate height of an ample even class is non-negative

Let `A` be an abelian variety over a number field `k`, `K` an algebraic closure of `k`, and
`c ∈ Pic(A) ⊗ ℚ` an ample (`Faltings.IsAmpleClass`), even (`Faltings.IsEvenClass`) class. Then
`ĥ_c(x) ≥ 0` for every `x ∈ A(K)`, where `ĥ_c` is the Néron–Tate height
(`Faltings.IsNeronTateHeight`) of the pull-back `c_K` of `c` to the base change `A_K`.

Write `ĥ_c(x) = ½ b(x, x) + ℓ(x)` with `ĥ_c - h` bounded for a height `h` of `c_K`. A positive
multiple of `c_K` is the class of the base change of a projective embedding of `A`, whose height
is non-negative, so `h` and hence `ĥ_c` are bounded below. Since `[-1]^* c = c`, functoriality of
heights along `[-1]` makes `h` even up to a bounded function, so `ℓ` is bounded, hence zero. Then
`ĥ_c(n • x) = n ^ 2 * ĥ_c(x) ≥ -M` for every `n`, so `ĥ_c(x) ≥ 0`.

## Main results

* `Faltings.IsEvenClass.nonneg_of_isNeronTateHeight`: if `c` is ample and even and `f` is a
  Néron–Tate height of `c_K` on `A_K`, then `0 ≤ f x` for every `x ∈ A_K(K)`.

## Implementation notes

The points `A(K)` are the `K`-points of the base change `A_K = A ×_k K`, the abelian variety
over `K` on which `Faltings.IsNeronTateHeight` is evaluated, exactly as for
`Faltings.neronPairing`. The class `c_K ∈ ℚ ⊗ Pic(A_K)` is the `ℚ`-linear base change of the
pull-back along the projection `A_K ⟶ A`. Ampleness is that of `c` on `A` over `k`, through
`TensorProduct.comm` from `ℚ ⊗[ℤ] Pic(A)` to the `Pic(A) ⊗[ℤ] ℚ` of `Faltings.IsAmpleClass`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [Wu] Theorem 2.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Faltings

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

variable {A X : Scheme.{u}} {fA : A ⟶ Spec (.of k)} [IsProjectiveVariety k fA]
  {fX : X ⟶ Spec (.of K)} [IsProjectiveVariety K fX] {p : X ⟶ A}

omit [Algebra k K] [IsProjectiveVariety K fX] in
/-- The pull-back of `𝒪(1)` along the base change of `φ` is the pull-back along `p` of
`φ^* 𝒪(1)`, at the level of Picard classes. -/
lemma picardClass_pullback_baseChangeHom {n : ℕ}
    (φ : A ⟶ projectiveSpaceOver n (Spec (.of k))) :
    X.picardClass ((Scheme.Modules.pullback (baseChangeHom (fX := fX) (p := p) φ)).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of K))))
        inferInstance =
      Stacks.Picard.schemePullbackClassHom p (A.picardClass ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))))
        inferInstance) := by
  rw [schemePullbackClassHom_picardClass]
  refine (X.picardClass_eq_iff _ _ _ _).2 ⟨?_⟩
  refine (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    eqToIso (by rw [baseChangeHom_snd]) ≪≫ ((Scheme.Modules.pullbackComp _ _).symm.app _) ≪≫
    (Scheme.Modules.pullback p).mapIso ((Scheme.Modules.pullbackComp _ _).symm.app _)

end BaseChange

section AmpleClass

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A X : Scheme.{u}} {fA : A ⟶ Spec (.of k)} [IsProjectiveVariety k fA]
  {fX : X ⟶ Spec (.of K)} [IsProjectiveVariety K fX] [Smooth fX] {p : X ⟶ A}

/-- An ample class `c` on `A` has a multiple `N • p^* c` which is the class of the base change
of a projective embedding of `A`. -/
lemma exists_embeddingClass_baseChange
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A} (hamp : IsAmpleClass fA (TensorProduct.comm ℤ ℚ _ c)) :
    ∃ (N n : ℕ) (φ : ProjectiveEmbedding fA n), 0 < N ∧
      embeddingClass fX (FreeAbelianGroup.of ⟨n, ProjectiveEmbedding.baseChange hX φ⟩) ⊗ₜ[ℤ]
          (1 : ℚ) =
        N • TensorProduct.comm ℤ ℚ _
          ((Stacks.Picard.schemePullbackClassHom p).toIntLinearMap.baseChange ℚ c) := by
  obtain ⟨e, L, hL, he, ⟨e', he', n, φ, ⟨ι⟩⟩, hec⟩ := hamp
  have hpow : A.picardClass (Stacks.Ample.tensorPowModule A L e') inferInstance =
      e' • A.picardClass L hL :=
    ((A.picardClass_eq_iff _ _ _ _).2
      ⟨(Stacks.PowerFamilyBridge.tensorPowerModuleIso A L e').symm⟩).trans
      (Stacks.SheafOfModules.picardClass_schemeTensorPower A L hL e')
  have hclA : A.picardClass ((Scheme.Modules.pullback φ.hom).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))))
      inferInstance = e' • A.picardClass L hL := by
    rw [← hpow]
    exact (A.picardClass_eq_iff _ _ _ _).2 ⟨ι.symm⟩
  have hcl : embeddingClass fX (FreeAbelianGroup.of ⟨n, ProjectiveEmbedding.baseChange hX φ⟩) =
      Stacks.Picard.schemePullbackClassHom p (e' • A.picardClass L hL) := by
    rw [embeddingClass_apply_of, ← hclA]
    exact picardClass_pullback_baseChangeHom φ.hom
  have hm : (((e * e').toNat : ℕ) : ℤ) = e * e' := Int.toNat_of_nonneg (by positivity)
  refine ⟨(e * e').toNat, n, φ, Int.lt_toNat.2 (by positivity), ?_⟩
  rw [hcl, map_zsmul, ← natCast_zsmul, hm, comm_baseChange,
    ← LinearMap.map_smul_of_tower, mul_comm, mul_smul, hec]
  simp [TensorProduct.smul_tmul']

end AmpleClass

/-- If `ψ ≫ p = p ≫ ι` and `ι^* c = c`, then `ψ^*` fixes the pull-back `p^* c`, written as
`Faltings.IsHeightOfClass` reads classes. -/
private lemma rTensor_pullbackPicardHom_comm_baseChange_of_comp_eq {X Y : Scheme.{u}}
    {ψ : X ⟶ X} {p : X ⟶ Y} {ι : Y ⟶ Y} (hι : ψ ≫ p = p ≫ ι)
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme Y}
    (hc : (Stacks.Picard.schemePullbackClassHom ι).toIntLinearMap.baseChange ℚ c = c) :
    LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom ψ).toIntLinearMap
        (TensorProduct.comm ℤ ℚ _
          ((Stacks.Picard.schemePullbackClassHom p).toIntLinearMap.baseChange ℚ c)) =
      TensorProduct.comm ℤ ℚ _
        ((Stacks.Picard.schemePullbackClassHom p).toIntLinearMap.baseChange ℚ c) := by
  rw [← comm_baseChange]
  congr 1
  have e' : (Stacks.SheafOfModules.pullbackPicardHom ψ).toIntLinearMap ∘ₗ
      (Stacks.Picard.schemePullbackClassHom p).toIntLinearMap =
      (Stacks.Picard.schemePullbackClassHom p).toIntLinearMap ∘ₗ
        (Stacks.Picard.schemePullbackClassHom ι).toIntLinearMap := by
    refine LinearMap.ext fun z => ?_
    change Stacks.SheafOfModules.pullbackPicardHom ψ (Stacks.Picard.schemePullbackClassHom p z) =
      Stacks.Picard.schemePullbackClassHom p (Stacks.Picard.schemePullbackClassHom ι z)
    simp only [schemePullbackClassHom_eq_pullbackPicardHom]
    rw [← Stacks.SheafOfModules.pullbackPicardHom_comp_apply,
      ← Stacks.SheafOfModules.pullbackPicardHom_comp_apply, hι]
  rw [← LinearMap.comp_apply (LinearMap.baseChange ℚ _), ← LinearMap.baseChange_comp, e',
    LinearMap.baseChange_comp, LinearMap.comp_apply, hc]

/-- A real number `a` with `n * |a| ≤ D` for every natural `n` is zero. -/
private lemma eq_zero_of_forall_nat_mul_abs_le {a D : ℝ} (h : ∀ n : ℕ, n * |a| ≤ D) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ := exists_nat_gt (D / |a|)
  rw [div_lt_iff₀ (abs_pos.2 ha)] at hn
  linarith [h n]

/-- A real number `a` with `-M ≤ n ^ 2 * a` for every natural `n` is non-negative. -/
private lemma nonneg_of_forall_nat_sq_mul_ge {a M : ℝ} (h : ∀ n : ℕ, -M ≤ (n : ℝ) ^ 2 * a) :
    0 ≤ a := by
  by_contra! ha
  obtain ⟨n, hn⟩ := exists_nat_gt (M / -a)
  rw [div_lt_iff₀ (by linarith)] at hn
  rcases n.eq_zero_or_pos with rfl | hpos
  · have := h 0
    simp at hn this
    linarith
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  nlinarith [h n, mul_nonneg (sub_nonneg.2 h1) (mul_nonneg n.cast_nonneg (neg_nonneg.2 ha.le))]

/-- **The scaling argument.** Let `F = ½ b(x, x) + ℓ(x)` on an abelian group, with `b` biadditive
and `ℓ` additive. If `F` is bounded below and `F(-x) - F(x)` is bounded, then `F ≥ 0`: the
second bound forces `ℓ = 0`, so `F(n • x) = n ^ 2 * F(x)`, and the first bound gives `F(x) ≥ 0`. -/
private lemma nonneg_of_bddBelow_of_abs_neg_sub_le {G : Type*} [AddCommGroup G]
    (b : G →+ G →+ ℝ) (ℓ : G →+ ℝ) {F : G → ℝ} (hF : ∀ g, F g = b g g / 2 + ℓ g) {M D : ℝ}
    (hlow : ∀ g, -M ≤ F g) (hneg : ∀ g, |F (-g) - F g| ≤ D) (g : G) : 0 ≤ F g := by
  have hℓ : ℓ g = 0 := eq_zero_of_forall_nat_mul_abs_le (D := D / 2) fun n => by
    have e := hneg (n • g)
    rw [show F (-(n • g)) - F (n • g) = -2 * (n * ℓ g) by
      simp only [hF, map_neg, map_nsmul, AddMonoidHom.neg_apply, AddMonoidHom.nsmul_apply,
        nsmul_eq_mul]
      ring, abs_mul, abs_mul, abs_neg, abs_two, Nat.abs_cast] at e
    linarith
  refine nonneg_of_forall_nat_sq_mul_ge (M := M) fun n => ?_
  have := hlow (n • g)
  simp only [hF, hℓ, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, mul_zero,
    add_zero] at this ⊢
  linarith

open scoped MonObj in
/-- On an abelian variety `A` over a number field `k`, the Néron–Tate height of an ample even
class `c ∈ Pic(A) ⊗ ℚ` is non-negative: if `f` is a Néron–Tate height of the pull-back of `c` to
`A_K`, `K` an algebraic closure of `k`, then `0 ≤ f x` for every `x ∈ A(K)`. -/
@[faltings "prop_nt_ample_even_nonneg_torsion"]
theorem IsEvenClass.nonneg_of_isNeronTateHeight {k : Type u} [Field k] [NumberField k]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsAbelianVariety k A]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    (hamp :
      letI : IsProjectiveVariety k A.hom :=
        ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
          (isProjective_of_isAbelianVariety k A)⟩
      IsAmpleClass A.hom (TensorProduct.comm ℤ ℚ _ c))
    (hc : IsEvenClass k A c) (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let AK : Over (Spec (.of K)) := (Over.pullback φK).obj A
    ∀ f : {p : Spec (.of K) ⟶ AK.left // p ≫ AK.hom = 𝟙 _} → ℝ,
      IsNeronTateHeight AK
        ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φK)).toIntLinearMap.baseChange
          ℚ c) f →
      ∀ x, 0 ≤ f x := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  intro φK AK f hf x
  letI : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  letI : IsProjectiveVariety K AK.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := AK.hom)
      (isProjective_of_isAbelianVariety K AK)⟩
  letI : Smooth AK.hom := smooth_of_isAbelianVariety K AK
  letI : IsCommMonObj AK := isCommMonObj_of_isProper_of_geometricallyIntegral AK
  obtain ⟨⟨h, hh, C, hC⟩, b, -, ℓ, hfb⟩ := hf
  have hX : IsPullback (pullback.fst A.hom φK) AK.hom A.hom φK := IsPullback.of_hasPullback _ _
  -- `h` is bounded below: a multiple of `c_K` is the class of a projective embedding
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ y, -M₀ ≤ h y := by
    obtain ⟨N, n, φ, hN, hcl⟩ := exists_embeddingClass_baseChange hX hamp
    obtain ⟨C', hC'⟩ := hh.exists_abs_sub_le
      (h₂ := fun y => (N : ℝ)⁻¹ * (ProjectiveEmbedding.baseChange hX φ).height y)
      ⟨N, _, hN, hcl, 0, fun y => by simp [EmbeddingGroup.height]⟩
    refine ⟨C', fun y => ?_⟩
    have h0 : 0 ≤ (N : ℝ)⁻¹ * (ProjectiveEmbedding.baseChange hX φ).height y :=
      mul_nonneg (by positivity) (by rw [ProjectiveEmbedding.height_def]; exact weilHeight_nonneg _)
    linarith [(abs_le.1 (hC' y)).1]
  -- `h` is even up to a bounded function: `[-1]^* c_K = c_K`
  have hι : (GrpObj.inv (X := AK)).left ≫ pullback.fst A.hom φK =
      pullback.fst A.hom φK ≫ (GrpObj.inv (X := A)).left := by
    change ((Over.pullback φK).map (GrpObj.inv (X := A))).left ≫ _ = _
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have h' := IsHeightOfClass.comp (GrpObj.inv (X := AK)).left (Over.w _) hh
  rw [rTensor_pullbackPicardHom_comm_baseChange_of_comp_eq hι hc] at h'
  obtain ⟨D, hD⟩ := h'.exists_abs_sub_le hh
  -- the scaling argument on the group `A_K(K)`
  let sec (g : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ AK)) :
      {p : Spec (.of K) ⟶ AK.left // p ≫ AK.hom = 𝟙 _} := ⟨g.toMul.left, Over.w g.toMul⟩
  refine nonneg_of_bddBelow_of_abs_neg_sub_le b ℓ (F := f ∘ sec) (fun g => hfb (sec g))
    (M := M₀ + C) (D := C + D + C) (fun g => ?_) (fun g => ?_) (.ofMul (Over.homMk x.1 x.2))
  · change -(M₀ + C) ≤ f (sec g)
    linarith [hM₀ (sec g), (abs_le.1 (hC (sec g))).1]
  · have e1 := abs_le.1 (hC (sec (-g)))
    have e2 := abs_le.1 (hC (sec g))
    have e3 : |h (sec (-g)) - h (sec g)| ≤ D := hD (sec g)
    rw [abs_le] at e3
    change |f (sec (-g)) - f (sec g)| ≤ C + D + C
    exact abs_le.2 ⟨by linarith, by linarith⟩

end Faltings
