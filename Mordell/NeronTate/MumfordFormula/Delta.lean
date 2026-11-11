module

public import Mathlib
public import Mordell.Attr
public import Mordell.CurveProduct.VojtaClass
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.CurveProduct.Diagonal
public import Mordell.Jacobian.BombieriLemma1.Delta
public import Mordell.Height.Class.Functoriality
public import Mordell.Height.Class.Uniqueness
public import Mordell.NeronTate.Existence
public import Mordell.NeronTate.Pairing.DeltaHeight
public import Mordell.CurveProduct.Surface

/-!
# Mumford's formula: `h_{Δ'}` in terms of the Néron form

Let `k` be a number field, `(C, P)` a curve over `k` with a divisor of degree one, of genus
`g ≥ 1`, `(J, ι)` a Jacobian of `C`, `j = j_P` and `⟨ , ⟩` the Néron form on `J(k̄)`. On
`C × C` let `Δ' = Δ - P × C - C × P`. For every height `h_{Δ'}` associated to `cl(Δ')`, the
function `(z, w) ↦ h_{Δ'}(z, w) + ⟨j z, j w⟩` is bounded on `(C × C)(k̄)`.

The proof: by Bombieri's Lemma 1 (`Faltings.schemePullbackClass_abelJacobi_deltaClass`),
`(j × j)^* δ = cl(Δ')`, and the identity survives base change to `k̄` along the square of
`(j × j)_K : (C × C)_K ⟶ (J × J)_K`. Functoriality of heights (`Faltings.IsHeightOfClass.comp`)
makes `h_δ ∘ (j × j)_K` a height of `cl(Δ')`, which uniqueness
(`Faltings.IsHeightOfClass.exists_abs_sub_le`) compares with `h_{Δ'}`; `h_δ - ĥ_δ` is bounded by
definition of the Néron–Tate height, and `ĥ_δ(x, y) = -⟨x, y⟩`
(`Faltings.isNeronTateHeight_deltaClass_apply_eq_neg_neronPairing`).

## Main results

* `Faltings.IsHeightOfClass.exists_abs_add_neronPairing_le`: Mumford's formula
  `h_{Δ'}(z, w) = -⟨z, w⟩ + O(1)`.

## Implementation notes

As in `Faltings.neronPairing`, heights live on the base change
`(C ×_k C)_K = (C ×_k C) ×_k Spec K` to an algebraic closure `K` of `k`, and the class of
`Δ'` there is the pull-back of `Faltings.CurveWithDegreeOneDivisor.vojtaClass X 0 0 1` along
the projection, tensored with `1 ∈ ℚ`. A point of `(C × C)(K)` is a section `s` of
`(C ×_k C)_K ⟶ Spec K`; its coordinates `z, w : Spec K ⟶ C` are `s` followed by the two
projections, and `j z`, `j w` are points of `J` over `Spec k`, the arguments of the Néron
form. Heights of classes are defined on smooth projective varieties; smoothness of the base
change is an instance, and its projectivity is proved in the statement: `C ×_k C` is a
projective variety (`Faltings.IsSmoothProjectiveCurve.surface_pullback`), projective morphisms
are stable under base change, and the base change of the geometrically integral `C ×_k C` to `K`
is integral.

The Néron form is that of the class `θ = cl(Θ)` of the theta divisor, given, as in
`Faltings.neronPairing`, by a reduced effective Cartier divisor `D` on `J` with support
`Faltings.thetaDivisor`. Such a `D` exists and is unique: `Θ` is the support of a prime divisor
(`Faltings.exists_primeDivisor_support_eq_thetaDivisor`), whose ideal sheaf is reduced and is
Cartier since `J` is smooth, hence locally factorial; a reduced closed subscheme is determined by
its support.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, proof of Lemma 2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Faltings

/-- Pulling a Picard class back around the two sides of a commutative square gives the same
class. -/
public lemma pullbackPicardHom_schemePullbackClassHom_of_comm {W X Y Z : Scheme.{u}}
    {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (w : a ≫ b = c ≫ d) (x : Z.picardGroup) :
    Stacks.SheafOfModules.pullbackPicardHom a (Stacks.Picard.schemePullbackClassHom b x) =
      Stacks.Picard.schemePullbackClassHom c (Stacks.Picard.schemePullbackClassHom d x) := by
  rw [← schemePullbackClassHom_eq_pullbackPicardHom]
  change Stacks.Picard.schemePullbackClass a (Stacks.Picard.schemePullbackClass b x) =
    Stacks.Picard.schemePullbackClass c (Stacks.Picard.schemePullbackClass d x)
  rw [Stacks.Picard.schemePullbackClass_comp, w, ← Stacks.Picard.schemePullbackClass_comp]

variable {k : Type u} [Field k]

/-- **Mumford's formula for `Δ'`.** Let `X = (C, P)` be a curve with a divisor of degree one
over a number field `k`, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian, `j = j_P`, `D` the reduced
effective Cartier divisor with support the theta divisor (it exists and is unique: `Θ` is the
support of a prime divisor by `Faltings.exists_primeDivisor_support_eq_thetaDivisor`, which is
Cartier on the smooth variety `J`), and `K` an algebraic closure of `k`. The base change
`(C ×_k C)_K` is a smooth projective variety over `K`. If `h` is a height on `(C ×_k C)_K`
associated to the class of `Δ' = Δ - P × C - C × P`
(`Faltings.CurveWithDegreeOneDivisor.vojtaClass X 0 0 1`), then `(z, w) ↦ h (z, w) + ⟨j z, j w⟩`
is bounded, `⟨ , ⟩` being `Faltings.neronPairing`. -/
@[faltings "thm_nt_mumford_delta_prime_height"]
theorem IsHeightOfClass.exists_abs_add_neronPairing_le [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    {h : {s : Spec (.of K) ⟶ pullback (pullback.fst X.f X.f ≫ X.f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) //
        s ≫ pullback.snd _ _ = 𝟙 _} → ℝ} :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : GeometricallyIntegral (pullback.fst X.f X.f ≫ X.f) :=
      Cube.geometricallyIntegral_fst_comp X.f X.f
    haveI : IsVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
    haveI : IsProjectiveVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      ⟨(IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1.isProjective.baseChange _⟩
    IsHeightOfClass (pullback.snd (pullback.fst X.f X.f ≫ X.f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Stacks.Picard.schemePullbackClassHom
        (pullback.fst (pullback.fst X.f X.f ≫ X.f)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (CurveWithDegreeOneDivisor.vojtaClass X 0 0 1) ⊗ₜ (1 : ℚ)) h →
    ∃ B : ℝ, ∀ s, |h s + neronPairing X A hg j hj D hrad hsupp K
      (Additive.ofMul (Over.homMk (V := Over.mk X.f)
        (s.1 ≫ pullback.fst _ _ ≫ pullback.fst X.f X.f)
        (by
          simp only [Over.mk_hom, Category.assoc]
          rw [pullback.condition (f := pullback.fst X.f X.f ≫ X.f), reassoc_of% s.2]) ≫ j))
      (Additive.ofMul (Over.homMk (V := Over.mk X.f)
        (s.1 ≫ pullback.fst _ _ ≫ pullback.snd X.f X.f)
        (by
          simp only [Over.mk_hom, Category.assoc]
          rw [← pullback.condition (f := X.f) (g := X.f),
            pullback.condition (f := pullback.fst X.f X.f ≫ X.f),
            reassoc_of% s.2]) ≫ j))| ≤ B := by
  open MonoidalCategory CartesianMonoidalCategory in (
    intro hh
    have := A.isAbelianVariety
    have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    let : Algebra ℚ K := DivisionRing.toRatAlgebra
    have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    have : GeometricallyIntegral (pullback.fst X.f X.f ≫ X.f) :=
      Cube.geometricallyIntegral_fst_comp X.f X.f
    have : IsVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
    have : IsProjectiveVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      ⟨(IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1.isProjective.baseChange _⟩
    have := isAbelianVariety_tensorObj A.J
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JJK : Over (Spec (.of K)) := (Over.pullback φK).obj (A.J ⊗ A.J)
    let δK : ℚ ⊗[ℤ] Stacks.Picard.ofScheme JJK.left :=
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst (A.J ⊗ A.J).hom φK)
        (deltaClass X A hg j hj D hrad hsupp)
    have : IsProjectiveVariety K JJK.hom :=
      ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := JJK.hom)
        (isProjective_of_isAbelianVariety K JJK)⟩
    have : Smooth JJK.hom := smooth_of_isAbelianVariety K JJK
    obtain ⟨f, hf⟩ := exists_isNeronTateHeight_of_isAlgebraic JJK δK
    have hnt := isNeronTateHeight_deltaClass_apply_eq_neg_neronPairing X A hg j hj D hrad hsupp K
      f hf
    obtain ⟨⟨hδ, hδh, C₁, hC₁⟩, -⟩ := hf
    -- the base change `(j × j)_K : (C × C)_K ⟶ (J × J)_K`, which carries `δ_K` to `cl(Δ')_K`
    obtain ⟨jjK, hfst, hsnd⟩ : ∃ m : pullback (pullback.fst X.f X.f ≫ X.f) φK ⟶ JJK.left,
        m ≫ pullback.fst (A.J ⊗ A.J).hom φK = pullback.fst _ φK ≫ (j ⊗ₘ j).left ∧
          m ≫ pullback.snd (A.J ⊗ A.J).hom φK = pullback.snd _ φK :=
      ⟨pullback.lift _ _ (by rw [Category.assoc, Over.w (j ⊗ₘ j)]; exact pullback.condition),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hjjK : jjK ≫ JJK.hom = pullback.snd _ φK := hsnd
    have hc := IsHeightOfClass.comp jjK hjjK hδh
    rw [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap,
      pullbackPicardHom_schemePullbackClassHom_of_comm hfst,
      schemePullbackClass_abelJacobi_deltaClass] at hc
    obtain ⟨C₂, hC₂⟩ := hh.exists_abs_sub_le hc
    refine ⟨C₂ + C₁, fun s ↦ ?_⟩
    have e₁ : (j ⊗ₘ j).left ≫ pullback.fst A.J.hom A.J.hom = pullback.fst X.f X.f ≫ j.left :=
      congrArg Over.Hom.left (tensorHom_fst j j)
    have e₂ : (j ⊗ₘ j).left ≫ pullback.snd A.J.hom A.J.hom = pullback.snd X.f X.f ≫ j.left :=
      congrArg Over.Hom.left (tensorHom_snd j j)
    -- the point `(j z, j w)` of `(J × J)_K` is the image of `s` under `(j × j)_K`
    have key : ∀ x' y' : Over.mk φK ⟶ A.J,
        x'.left = s.1 ≫ pullback.fst _ φK ≫ pullback.fst X.f X.f ≫ j.left →
        y'.left = s.1 ≫ pullback.fst _ φK ≫ pullback.snd X.f X.f ≫ j.left →
        ∀ hw hq, |h s + -f ⟨pullback.lift (lift x' y').left (𝟙 _) hw, hq⟩| ≤ C₂ + C₁ := by
      intro x' y' hx hy hw hq
      have hq' : (s.1 ≫ jjK) ≫ JJK.hom = 𝟙 _ := by rw [Category.assoc, hjjK, s.2]
      have e : pullback.lift (lift x' y').left (𝟙 _) hw = s.1 ≫ jjK := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, hfst]
          apply pullback.hom_ext
          · simp only [Category.assoc]
            rw [e₁, ← hx]
            exact congrArg Over.Hom.left (lift_fst x' y')
          · simp only [Category.assoc]
            rw [e₂, ← hy]
            exact congrArg Over.Hom.left (lift_snd x' y')
        · rw [pullback.lift_snd, Category.assoc, hsnd, s.2]; rfl
      have e' : (⟨pullback.lift (lift x' y').left (𝟙 _) hw, hq⟩ :
          {p : Spec (.of K) ⟶ JJK.left // p ≫ JJK.hom = 𝟙 _}) = ⟨s.1 ≫ jjK, hq'⟩ := Subtype.ext e
      rw [e']
      have h₁ := abs_le.mp (hC₂ s)
      have h₂ := abs_le.mp (hC₁ ⟨s.1 ≫ jjK, hq'⟩)
      rw [abs_le]
      constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
    rw [← neg_neg (neronPairing X A hg j hj D hrad hsupp K _ _), ← hnt]
    exact key _ _ rfl rfl _ _)

end Faltings
