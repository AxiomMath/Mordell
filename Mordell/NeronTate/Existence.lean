module

public import Mordell.NeronTate.Basic
public import Mordell.Height.Class.Existence
public import Mordell.Height.Class.Linearity
public import Mordell.Height.Class.Functoriality
public import Mordell.Height.Class.Uniqueness
public import Mordell.AbelianVariety.ParallelogramRelation
public import Mordell.Algebra.Quadratic.Parallelogram
public import Mordell.Algebra.Quadratic.PolarDiagonal
public import Mordell.NeronTate.TateLimit

/-!
# Existence of the Néron–Tate height

Let `A` be an abelian variety over a number field `k`, `K` an algebraic closure of `k`, and
`c ∈ Pic(A) ⊗ ℚ`. Then `c` has a Néron–Tate height: there is a function
`f = ½ b(x, x) + ℓ(x)` on `A(K)`, with `b` symmetric biadditive and `ℓ` additive, such that
`f - h` is bounded for a height `h` associated to `c`.

Let `h` be a height associated to `c`. The parallelogram relation
`s₁₂^* c + s₁₋₂^* c = 2 s₁^* c + s₂^* (c + [-1]^* c)` on `A × A`, carried to heights by the
functoriality of heights along `s₁₂, s₁₋₂, s₁, s₂, [-1] ∘ s₂ : A × A → A` and the uniqueness of
heights up to bounded functions, gives
`h(x + y) + h(x - y) = 2 h(x) + h(y) + h(-y) + O(1)`. The even and odd parts
`h₊(x) = h(x) + h(-x)` and `h₋(x) = h(x) - h(-x)` then satisfy
`h₊(x + y) + h₊(x - y) = 2 h₊(x) + 2 h₊(y) + O(1)` and
`h₋(x + y) + h₋(x - y) = 2 h₋(x) + O(1)`; Tate's limits along `[2]` with ratios `4` and `2`
turn them into an exact quadratic function `Q₊` and an exact additive function `L₋`, and
`½ Q₊ + ½ L₋` is the Néron–Tate height.

## Main results

* `Faltings.exists_isNeronTateHeight`: every class of `Pic(A) ⊗ ℚ` has a Néron–Tate height.
* `Faltings.schemePullbackClassHom_eq_pullbackPicardHom`: the pull-back of Picard classes along
  a morphism of schemes is the pull-back homomorphism of the underlying ringed spaces.
* `Faltings.comm_baseChange`: swapping the factors of `ℚ ⊗ M` turns the base change of a
  `ℤ`-linear map into its `rTensor`.

## Implementation notes

The argument is made for an abelian variety over any field algebraic over `ℚ`, and then applied
to the base change `A_K = (Over.pullback (Spec K ⟶ Spec k)).obj A`, an abelian variety over `K`
whose `K`-points are the sections of `A_K ⟶ Spec K` on which `Faltings.IsNeronTateHeight` is
stated. The class of `c` on `A_K` is its image under the base change to `ℚ` of the pull-back
`Stacks.Picard.schemePullbackClassHom` along the projection `A_K ⟶ A`, as for the class of `θ`
in `Faltings.neronPairing`.

The even and odd parts are taken on the level of heights rather than of classes: the
parallelogram relation is applied to `c` itself, so that the pull-back `[-1]^*` enters only
through `s₂^*`, and the doubling bounds needed for Tate's limits are the approximate
parallelogram laws at `x = y`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 2.
* [Lang, *Fundamentals of Diophantine geometry*], Chapter 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj Filter Topology
open scoped TensorProduct

universe u

namespace Faltings

section Analytic

variable {G : Type*} [AddCommGroup G]

/-- The iterates of doubling are multiplication by powers of two. -/
private lemma iterate_two_nsmul (n : ℕ) (x : G) : (fun y : G => 2 • y)^[n] x = 2 ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← mul_nsmul, pow_succ, mul_comm]

/-- **Tate's limit makes an approximate parallelogram law exact.** If
`|H(x + y) + H(x - y) - 2 H(x) - β H(y)| ≤ M` with `β ≥ 0`, then the Tate limit of `H` along
doubling, with ratio `2 + β`, is a function `Q` with `Q 0 = 0`, `Q - H` bounded, and
`Q(x + y) + Q(x - y) = 2 Q(x) + β Q(y)`. -/
private lemma exists_add_add_sub_eq_of_abs_le (β : ℝ) (hβ : 0 ≤ β) (H : G → ℝ) (M : ℝ)
    (hM : ∀ x y, |H (x + y) + H (x - y) - 2 * H x - β * H y| ≤ M) :
    ∃ Q : G → ℝ, Q 0 = 0 ∧ (∃ C, ∀ x, |Q x - H x| ≤ C) ∧
      ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + β * Q y := by
  have hα : (1 : ℝ) < 2 + β := by linarith
  have hM' : ∀ x, |H (2 • x) - (2 + β) * H x| ≤ M + |H 0| := fun x => by
    have h := hM x x
    rw [sub_self, ← two_nsmul] at h
    calc _ = |(H (2 • x) + H 0 - 2 * H x - β * H x) - H 0| := by congr 1; ring
      _ ≤ M + |H 0| := (abs_sub _ _).trans (by linarith)
  choose Q hQ hQH using abs_tateLimit_sub_le (fun y : G => 2 • y) hα H hM'
  have hT : ∀ x, Tendsto (fun n : ℕ => ((2 + β) ^ n)⁻¹ * H (2 ^ n • x)) atTop (𝓝 (Q x)) := by
    intro x
    obtain ⟨hd, hx⟩ := hQ x
    rw [← hx]
    exact (tendsto_nhds_limUnder hd).congr fun n => by rw [iterate_two_nsmul]
  have hinv : Tendsto (fun n : ℕ => ((2 + β) ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hα)
  refine ⟨Q, tendsto_nhds_unique (hT 0) (by simpa using hinv.mul_const (H 0)),
    ⟨_, hQH⟩, fun x y => ?_⟩
  have hlim := (((hT (x + y)).add (hT (x - y))).sub ((hT x).const_mul 2)).sub
    ((hT y).const_mul β)
  rw [← sub_eq_zero, ← sub_sub]
  refine tendsto_nhds_unique hlim ?_
  refine squeeze_zero_norm (a := fun n : ℕ => ((2 + β) ^ n)⁻¹ * M) (fun n => ?_)
    (by simpa using hinv.mul_const M)
  have hpos : 0 < ((2 + β) ^ n)⁻¹ := by positivity
  rw [smul_add, smul_sub, Real.norm_eq_abs]
  calc _ = |((2 + β) ^ n)⁻¹ * (H (2 ^ n • x + 2 ^ n • y) + H (2 ^ n • x - 2 ^ n • y) -
        2 * H (2 ^ n • x) - β * H (2 ^ n • y))| := by congr 1; ring
    _ ≤ ((2 + β) ^ n)⁻¹ * M := by
      rw [abs_mul, abs_of_pos hpos]; exact mul_le_mul_of_nonneg_left (hM _ _) hpos.le

/-- The even (`s = 1`) and odd (`s = -1`) parts `x ↦ H x + s H(-x)` of a function with
`H(x + y) + H(x - y) = 2 H(x) + H(y) + H(-y) + O(1)` satisfy the approximate parallelogram law
with `β = 1 + s`. -/
private lemma abs_add_mul_neg_parallelogram_le (H : G → ℝ) (M : ℝ)
    (hM : ∀ x y, |H (x + y) + H (x - y) - 2 * H x - H y - H (-y)| ≤ M)
    {s : ℝ} (hs : |s| = 1) (x y : G) :
    |(H (x + y) + s * H (-(x + y))) + (H (x - y) + s * H (-(x - y))) -
      2 * (H x + s * H (-x)) - (1 + s) * (H y + s * H (-y))| ≤ 2 * M := by
  have h₂ := hM (-x) (-y)
  rw [neg_neg, ← neg_add, sub_neg_eq_add, show -x + y = -(x - y) by abel] at h₂
  have hs2 : s * s = 1 := (abs_mul_abs_self s).symm.trans (by rw [hs]; norm_num)
  calc _ = |(H (x + y) + H (x - y) - 2 * H x - H y - H (-y)) +
        s * (H (-(x + y)) + H (-(x - y)) - 2 * H (-x) - H (-y) - H y)| := by
          congr 1; linear_combination (-H (-y)) * hs2
    _ ≤ M + M := (abs_add_le _ _).trans (add_le_add (hM x y) (by rw [abs_mul, hs]; linarith))
    _ = 2 * M := by ring

/-- **Quadratic plus linear approximation.** A function `H` on an abelian group with
`H(x + y) + H(x - y) = 2 H(x) + H(y) + H(-y) + O(1)` differs by a bounded function from
`½ b(x, x) + ℓ(x)`, for a symmetric biadditive `b` and an additive `ℓ`. -/
private lemma exists_bilinear_linear_of_abs_le (H : G → ℝ) (M : ℝ)
    (hM : ∀ x y, |H (x + y) + H (x - y) - 2 * H x - H y - H (-y)| ≤ M) :
    ∃ b : G →+ G →+ ℝ, (∀ x y, b x y = b y x) ∧ ∃ ℓ : G →+ ℝ, ∃ C : ℝ,
      ∀ x, |b x x / 2 + ℓ x - H x| ≤ C := by
  obtain ⟨Q, -, ⟨C₁, hC₁⟩, hQ⟩ := exists_add_add_sub_eq_of_abs_le (1 + 1) (by norm_num)
    (fun x => H x + 1 * H (-x)) (2 * M) (abs_add_mul_neg_parallelogram_le H M hM (by simp))
  obtain ⟨L, hL0, ⟨C₂, hC₂⟩, hL⟩ := exists_add_add_sub_eq_of_abs_le (1 + -1) (by norm_num)
    (fun x => H x + -1 * H (-x)) (2 * M) (abs_add_mul_neg_parallelogram_le H M hM (by simp))
  have hQ' : ∀ x y, Q (x + y) + Q (x - y) = 2 • Q x + 2 • Q y := fun x y => by
    rw [hQ, two_nsmul, two_nsmul]; ring
  have hL' : ∀ x y, L (x + y) + L (x - y) = 2 • L x := fun x y => by
    rw [hL, two_nsmul]; ring
  obtain ⟨hsymm, hadd₁, hadd₂⟩ := polar_comm_and_add_of_add_add_sub_eq_two_nsmul hQ'
  let b : G →+ G →+ ℝ :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => QuadraticMap.polar Q x y / 2)
      fun y y' => by rw [hadd₂]; ring)
      fun x x' => by
        ext y; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]; rw [hadd₁]; ring
  let ℓ : G →+ ℝ := AddMonoidHom.mk' (fun x => L x / 2) fun x y => by
    rw [map_add_of_add_add_sub_eq_two_nsmul hL0 hL' x y]; ring
  refine ⟨b, fun x y => by simp only [b, AddMonoidHom.mk'_apply]; rw [hsymm], ℓ,
    (C₁ + C₂) / 2, fun x => ?_⟩
  have h₁ := hC₁ x
  have h₂ := hC₂ x
  simp only [b, ℓ, AddMonoidHom.mk'_apply, polar_self_of_add_add_sub_eq hQ' x, two_nsmul]
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith

end Analytic

section Geometric

/-- Pull-back of Picard classes along a morphism of schemes, read off the underlying ringed
spaces, is the pull-back homomorphism `Stacks.SheafOfModules.pullbackPicardHom`. -/
lemma schemePullbackClassHom_eq_pullbackPicardHom {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    Stacks.Picard.schemePullbackClassHom φ = Stacks.SheafOfModules.pullbackPicardHom φ := by
  ext x
  conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x]
  conv_rhs => rw [← Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x]
  exact (Stacks.Picard.pullbackClass_classOf _ _ _).trans
    (Stacks.SheafOfModules.pullbackPicardHom_picardClass _ _ _).symm

/-- Swapping the factors of `ℚ ⊗ M` turns the base change of `φ` into `φ ⊗ ℚ`. -/
lemma comm_baseChange {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (φ : M →ₗ[ℤ] N) (c : ℚ ⊗[ℤ] M) :
    TensorProduct.comm ℤ ℚ N (φ.baseChange ℚ c) =
      φ.rTensor ℚ (TensorProduct.comm ℤ ℚ M c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `comm_baseChange` for the pull-back of Picard classes, with the Picard group of the source
of the pull-back written `Stacks.Picard.ofScheme`, as in the statement of
`Faltings.exists_isNeronTateHeight`. -/
private lemma comm_baseChange_pullbackPicardHom {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (c : ℚ ⊗[ℤ] Y.picardGroup) :
    TensorProduct.comm ℤ ℚ (Stacks.Picard.ofScheme X)
        ((Stacks.SheafOfModules.pullbackPicardHom φ).toIntLinearMap.baseChange ℚ c) =
      (Stacks.SheafOfModules.pullbackPicardHom φ).toIntLinearMap.rTensor ℚ
        (TensorProduct.comm ℤ ℚ Y.picardGroup c) :=
  comm_baseChange _ c

variable {K : Type u} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

/-- The sum of heights of two classes is a height of their sum. -/
private lemma isHeightOfClass_add {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
    [IsProjectiveVariety K f] [Smooth f] {c c' : X.picardGroup ⊗[ℤ] ℚ}
    {h h' : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} → ℝ}
    (hc : IsHeightOfClass f c h) (hc' : IsHeightOfClass f c' h') :
    IsHeightOfClass f (c + c') (fun x ↦ h x + h' x) := by
  simpa using hc.linearCombination hc' 1 1

omit [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] in
/-- The product of a geometrically integral projective variety with itself is a projective
variety. -/
private lemma isProjectiveVariety_tensorObj (A : Over (Spec (.of K)))
    [IsProjectiveVariety K A.hom] [GeometricallyIntegral A.hom] :
    IsProjectiveVariety K (A ⊗ A).hom := by
  change IsProjectiveVariety K (pullback.fst A.hom A.hom ≫ A.hom)
  have : GeometricallyIntegral (pullback.fst A.hom A.hom ≫ A.hom) :=
    Cube.geometricallyIntegral_fst_comp _ _
  have : IsIntegral (pullback A.hom A.hom) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst A.hom A.hom ≫ A.hom)
  have hproj : IsProjectiveMorphism (pullback.fst A.hom A.hom ≫ A.hom) := by
    rw [pullback.condition]
    exact (IsProjectiveVariety.isProjective (f := A.hom)).baseChange A.hom |>.comp
      (IsProjectiveVariety.isProjective (f := A.hom))
  exact (isProjectiveVariety_iff K _).mpr ⟨IsVariety.mk, hproj⟩

/-- **Existence of the Néron–Tate height** over a field algebraic over `ℚ`. -/
public theorem exists_isNeronTateHeight_of_isAlgebraic (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety K A] (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) :
    ∃ f, IsNeronTateHeight A c f := by
  let : IsProjectiveVariety K A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety K A)⟩
  let : Smooth A.hom := smooth_of_isAbelianVariety K A
  have : IsProjectiveVariety K (A ⊗ A).hom := isProjectiveVariety_tensorObj A
  have : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  obtain ⟨h, hh⟩ := exists_isHeightOfClass A.hom (TensorProduct.comm ℤ ℚ _ c)
  have ks := IsHeightOfClass.comp (fst A A * snd A A).left (Over.w _) hh
  have kd := IsHeightOfClass.comp (fst A A / snd A A).left (Over.w _) hh
  have k₁ := IsHeightOfClass.comp (fst A A).left (Over.w _) hh
  have k₂ := IsHeightOfClass.comp (snd A A).left (Over.w _) hh
  have k₂' := IsHeightOfClass.comp (snd A A ≫ ι[A]).left (Over.w _) hh
  have hL := isHeightOfClass_add ks kd
  have hR := isHeightOfClass_add (isHeightOfClass_add k₁ k₁) (isHeightOfClass_add k₂ k₂')
  have hrel := congrArg (TensorProduct.comm ℤ ℚ _) (pullback_add_add_pullback_sub_eq K A c)
  simp only [map_add, comm_baseChange_pullbackPicardHom,
    schemePullbackClassHom_eq_pullbackPicardHom, two_nsmul] at hrel
  rw [hrel] at hL
  have hcomp : LinearMap.rTensor ℚ
      (Stacks.SheafOfModules.pullbackPicardHom (snd A A ≫ ι[A]).left).toIntLinearMap
        (TensorProduct.comm ℤ ℚ _ c) =
      LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom (snd A A).left).toIntLinearMap
        (LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom ι[A].left).toIntLinearMap
          (TensorProduct.comm ℤ ℚ _ c)) := by
    rw [Over.comp_left, Stacks.SheafOfModules.pullbackPicardHom_comp]
    exact LinearMap.rTensor_comp_apply (M := ℚ)
      (Stacks.SheafOfModules.pullbackPicardHom (snd A A).left).toIntLinearMap
      (Stacks.SheafOfModules.pullbackPicardHom ι[A].left).toIntLinearMap _
  rw [hcomp] at hR
  obtain ⟨C, hC⟩ := hL.exists_abs_sub_le hR
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let H : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A) → ℝ := fun g =>
    h ⟨g.toMul.left, Over.w g.toMul⟩
  have hH : ∀ x y, |H (x + y) + H (x - y) - 2 * H x - H y - H (-y)| ≤ C := by
    intro x y
    have hq := hC ⟨(lift x.toMul y.toMul).left, Over.w (lift x.toMul y.toMul)⟩
    have e₁ : x + y = .ofMul (lift x.toMul y.toMul ≫ (fst A A * snd A A)) := by
      rw [comp_mul, lift_fst, lift_snd]; rfl
    have e₂ : x - y = .ofMul (lift x.toMul y.toMul ≫ (fst A A / snd A A)) := by
      rw [div_eq_mul_inv, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, ← div_eq_mul_inv]; rfl
    have e₃ : x = .ofMul (lift x.toMul y.toMul ≫ fst A A) := by rw [lift_fst]; rfl
    have e₄ : y = .ofMul (lift x.toMul y.toMul ≫ snd A A) := by rw [lift_snd]; rfl
    have e₅ : -y = .ofMul (lift x.toMul y.toMul ≫ snd A A ≫ ι[A]) := by
      rw [← Category.assoc, lift_snd]; rfl
    have hq' : |(H (.ofMul (lift x.toMul y.toMul ≫ (fst A A * snd A A))) +
          H (.ofMul (lift x.toMul y.toMul ≫ (fst A A / snd A A)))) -
          (H (.ofMul (lift x.toMul y.toMul ≫ fst A A)) +
            H (.ofMul (lift x.toMul y.toMul ≫ fst A A)) +
            (H (.ofMul (lift x.toMul y.toMul ≫ snd A A)) +
              H (.ofMul (lift x.toMul y.toMul ≫ snd A A ≫ ι[A]))))| ≤ C := hq
    rw [← e₁, ← e₂, ← e₅, ← e₃, ← e₄] at hq'
    convert hq' using 2
    ring
  obtain ⟨b, hb, ℓ, C', hC'⟩ := exists_bilinear_linear_of_abs_le H C hH
  exact ⟨fun p => b (.ofMul (Over.homMk p.1 p.2)) (.ofMul (Over.homMk p.1 p.2)) / 2 +
      ℓ (.ofMul (Over.homMk p.1 p.2)),
    ⟨h, hh, C', fun p => hC' _⟩, b, hb, ℓ, fun _ => rfl⟩

end Geometric

/-- **Existence of the Néron–Tate height.** Let `A` be an abelian variety over a number field
`k` and `K` an algebraic closure of `k`. Every `c ∈ Pic(A) ⊗ ℚ` has a Néron–Tate height on
`A(K)`, i.e. its pull-back to the base change `A_K` has a Néron–Tate height. -/
@[faltings "thm_nt_neron_tate_height"]
theorem exists_isNeronTateHeight {k : Type u} [Field k] [NumberField k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    ∃ f, IsNeronTateHeight ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)
      ((Stacks.Picard.schemePullbackClassHom
        (pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))).toIntLinearMap
          |>.baseChange ℚ c) f :=
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  exists_isNeronTateHeight_of_isAlgebraic _ _

end Faltings
