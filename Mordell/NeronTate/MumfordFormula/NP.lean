module
public import Mordell.Height.Class.Functoriality
public import Mordell.Height.Class.Linearity
public import Mordell.Height.Class.Uniqueness
public import Mordell.Jacobian.BombieriLemma1.ThetaNeg
public import Mordell.NeronTate.Basic
public import Mordell.NeronTate.MumfordFormula.Delta

/-!
# Mumford's formula: `h_{NP}` in terms of `ĥ_{θ⁻}`

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one, of
genus `g ≥ 1`, `(J, ι)` a Jacobian of `C`, `j = j_P` the Abel–Jacobi map, `θ = cl(Θ) ∈ Pic(J)`
the class of the theta divisor and `θ⁻ = [-1]^* θ`. For every integer `N ≥ 1` and every height
`h_{NP}` associated to the divisor `NP` on `C`, the function
`h_{NP} - (N / g) ĥ_{θ⁻} ∘ j` is bounded on `C(k̄)`.

The proof: by Bombieri's Lemma 1 (`Faltings.schemePullbackClass_abelJacobi_thetaNeg`),
`j^* θ⁻ = g cl(P)`, and the identity survives base change to `k̄` along the square of
`j_K : C_K ⟶ J_K`. Functoriality of heights (`Faltings.IsHeightOfClass.comp`) makes
`h_{θ⁻} ∘ j_K` a height of `g cl(P)`, so `(N / g) h_{θ⁻} ∘ j_K` is a height of `N cl(P)`, and
uniqueness (`Faltings.IsHeightOfClass.exists_abs_sub_le`) compares it with `h_{NP}`; finally
`ĥ_{θ⁻} - h_{θ⁻}` is bounded by definition of the Néron–Tate height.

## Main results

* `Faltings.IsHeightOfClass.exists_abs_sub_neronTateHeight_le`: Mumford's formula
  `h_{NP} = (N / g) ĥ_{θ⁻} ∘ j + O(1)`.

## Implementation notes

As in `Faltings.neronPairing`, everything is read over an algebraic closure `K` of `k`. Heights
on `C` are heights on the base change `C_K = C ×_k Spec K`, a smooth projective variety over
`K`, and the class of `NP` there is the pull-back of `N • [𝒪_C(P)]`
(`Faltings.CurveWithDegreeOneDivisor.classP`) along the projection `C_K ⟶ C`, tensored with
`1 ∈ ℚ`. A point of `C(K)` is a section `s` of `C_K ⟶ Spec K`, and `j` sends it to the point
`s ≫ pr₁ ≫ j` of `J` over `Spec k`, read on `J_K` as in `Faltings.neronPairing`. The
Néron–Tate height `ĥ_{θ⁻}` is any function satisfying `Faltings.IsNeronTateHeight` for the
class of `θ⁻ = [-1]^* θ` on `J_K`; it is unique. Projectivity of `C_K` over `K`, needed to
speak of heights on it, is taken as an instance argument; it holds for every curve.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, proof of Lemma 2.
* [M] D. Mumford, *A remark on Mordell's conjecture*.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

/-- In `M ⊗ ℚ`, scaling `(g • c) ⊗ 1` by `N / g` gives `(N • c) ⊗ 1`. -/
private lemma lTensor_div_zsmul_tmul_one {M : Type*} [AddCommGroup M] (c : M) {g : ℕ}
    (hg : g ≠ 0) (N : ℕ) :
    LinearMap.lTensor M (LinearMap.mulLeft ℤ ((N : ℚ) / g)) (((g : ℤ) • c) ⊗ₜ[ℤ] (1 : ℚ)) =
      ((N : ℤ) • c) ⊗ₜ 1 := by
  rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, TensorProduct.smul_tmul,
    TensorProduct.smul_tmul]
  congr 1
  simp only [zsmul_eq_mul, Int.cast_natCast]
  field_simp

variable {k : Type u} [Field k]

/-- **Mumford's formula for `h_{NP}`.** Let `X = (C, P)` be a curve with a divisor of degree one
over a number field `k`, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian, `j = j_P`, `D` the reduced
effective Cartier divisor with support the theta divisor, `θ = cl(D)`, `θ⁻ = [-1]^* θ`, and `K`
an algebraic closure of `k`. If `N ≥ 1`, `h` is a height on `C_K` associated to the class of
`NP`, and `f` is a Néron–Tate height (`Faltings.IsNeronTateHeight`) of the class of `θ⁻` on
`J_K`, then `Q ↦ h Q - (N / g) f (j Q)` is bounded on `C(K)`. -/
@[faltings "thm_nt_mumford_diagonal_height"]
theorem IsHeightOfClass.exists_abs_sub_neronTateHeight_le [NumberField k]
    (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    [IsProjectiveVariety K (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (N : ℕ) (hN : 1 ≤ N) :
    haveI := A.isAbelianVariety
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A.J
    let θ := Stacks.Divisors.picardClass D
    let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
    /- The point `j(Q) ∈ J(K)` of a section `s` of `C_K ⟶ Spec K`, read on `J_K`. -/
    let jpt : {s : Spec (.of K) ⟶ pullback X.f φK // s ≫ pullback.snd X.f φK = 𝟙 _} →
        {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} := fun s ↦
      ⟨pullback.lift (s.1 ≫ pullback.fst X.f φK ≫ j.left) (𝟙 _)
        (by simp only [Category.assoc, Over.w j, Over.mk_hom, Category.id_comp]
            rw [pullback.condition, reassoc_of% s.2]), pullback.lift_snd _ _ _⟩
    ∀ (h : {s : Spec (.of K) ⟶ pullback X.f φK // s ≫ pullback.snd X.f φK = 𝟙 _} → ℝ)
      (f : {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} → ℝ),
      IsHeightOfClass (pullback.snd X.f φK)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f φK)
            ((N : ℤ) • X.classP) ⊗ₜ (1 : ℚ)) h →
      IsNeronTateHeight JK ((1 : ℚ) ⊗ₜ
          Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) θm) f →
      ∃ B : ℝ, ∀ s, |h s - (N : ℝ) / (genus X.f : ℝ) * f (jpt s)| ≤ B := by
  intro φK JK θ θm jpt h f hh hf
  have := A.isAbelianVariety
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsProjectiveVariety K JK.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := JK.hom)
      (isProjective_of_isAbelianVariety K JK)⟩
  have : Smooth JK.hom := smooth_of_isAbelianVariety K JK
  obtain ⟨⟨_, hθh, C₁, hC₁⟩, -⟩ := hf
  -- the base change `j_K : C_K ⟶ J_K` of `j`, which carries `θ⁻_K` to `g cl(P)_K`
  let jK : pullback X.f φK ⟶ JK.left :=
    pullback.map X.f φK A.J.hom φK j.left (𝟙 _) (𝟙 _) (by simp [Over.w j]) (by simp)
  have hjK : jK ≫ JK.hom = pullback.snd X.f φK := by simp [jK, JK]
  have hpull : Stacks.SheafOfModules.pullbackPicardHom jK
      (Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) θm) =
        (genus X.f : ℤ) • Stacks.Picard.schemePullbackClassHom (pullback.fst X.f φK) X.classP := by
    have L1 : Stacks.Picard.schemePullbackClassHom j.left θm = (genus X.f : ℤ) • X.classP :=
      schemePullbackClass_abelJacobi_thetaNeg X A
        (fun T ↦ A.map_add (.op T)) hg j hj D hrad hsupp
    rw [pullbackPicardHom_schemePullbackClassHom_of_comm (pullback.lift_fst _ _ _), L1, map_zsmul]
  have h₂ := isHeightOfClass_ratMul (IsHeightOfClass.comp jK hjK hθh) ((N : ℚ) / genus X.f)
  rw [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap, hpull,
    lTensor_div_zsmul_tmul_one _ (by omega), ← map_zsmul] at h₂
  obtain ⟨C₂, hC₂⟩ := hh.exists_abs_sub_le h₂
  refine ⟨C₂ + (N : ℝ) / genus X.f * C₁, fun s ↦ ?_⟩
  have e : jpt s = ⟨s.1 ≫ jK, by rw [Category.assoc, hjK, s.2]⟩ := Subtype.ext <|
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans (by simp [jK]))
      ((pullback.lift_snd _ _ _).trans (by simp [jK, s.2]))
  rw [e]
  exact abs_sub_mul_le_add_mul (by positivity) (by simpa using hC₂ s) (hC₁ _)

end Faltings
