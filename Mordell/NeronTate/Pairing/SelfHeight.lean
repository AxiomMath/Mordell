module

public import Mordell.NeronTate.Pairing.Basic
public import Mordell.NeronTate.Additivity
public import Mordell.NeronTate.Functoriality
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import Mordell.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# The Néron norm is the height of `θ + θ⁻`

Let `k` be a number field, `(C, P)` a curve over `k` with a rational divisor of degree one, of
genus `g ≥ 1`, `(J, ι)` a Jacobian of `C`, `θ ∈ Pic(J)` the class of the theta divisor and
`θ⁻ = [-1]^* θ`. For `x ∈ J(k̄)` the Néron norm `|x|² = ⟨x, x⟩` satisfies
`|x|² = ĥ_θ(x) + ĥ_{θ⁻}(x) = ĥ_{θ + θ⁻}(x)`.

Writing `ĥ_θ x = ½ B_θ(x, x) + L_θ(x)`, one has `ĥ_{θ⁻}(x) = ĥ_θ(-x) = ½ B_θ(x, x) - L_θ(x)`,
so `ĥ_θ + ĥ_{θ⁻} = B_θ(x, x) = ⟨x, x⟩`; and `ĥ_θ + ĥ_{θ⁻} = ĥ_{θ + θ⁻}` by additivity of the
Néron–Tate height in the class.

## Main definitions

* `Faltings.GroupScheme.toBaseChange`: a point `x : S' ⟶ A` over `S` as the section `(x, 1)` of
  the base change `A ×_S S' ⟶ S'`.
* `Faltings.GroupScheme.fromBaseChange`: its inverse, a section followed by the projection to
  `A`, as a homomorphism of groups of points.

## Main results

* `Faltings.neronPairing_self_eq_add_and_add_eq`: if `f`, `f'`, `f''` are the Néron–Tate
  heights of `θ`, `θ⁻`, `θ + θ⁻` on `J_K`, then `neronPairing … x x = f x + f' x` and
  `f x + f' x = f'' x`.

## Implementation notes

As in `Faltings.neronPairing`, heights live on the abelian variety
`J_K = (Over.pullback (Spec K ⟶ Spec k)).obj J` over `K`: a class `c ∈ Pic(J)` enters
`ℚ ⊗ Pic(J_K)` as `1 ⊗ c_K`, `c_K` the pull-back of `c` along the projection `J_K ⟶ J`, and a
point `x : Spec K ⟶ J` over `k` is the section `(x, 1)` of `J_K ⟶ Spec K`. The Néron–Tate
height `ĥ_c` is unique when it exists, so the three heights are taken as functions `f`, `f'`,
`f''` satisfying `Faltings.IsNeronTateHeight` of the respective classes; this is the predicate
by which `Faltings.neronPairing` chooses `ĥ_θ`. The class `θ⁻` is
`Stacks.Picard.schemePullbackClassHom ι[A.J].left θ`, the pull-back along the inversion.

The proof needs `x ↦ (x, 1)` to be a homomorphism from `J(K)` to the group of sections of `J_K`:
it is `Faltings.GroupScheme.toBaseChange`, the inverse of the homomorphism
`Faltings.GroupScheme.fromBaseChange` built from `AlgebraicGeometry.GroupScheme.pointsMulEquiv`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

section Inverse

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]

/-- The point given by the section `p ≫ [-1]` is the opposite of the point given by `p`. -/
private lemma ofMul_homMk_comp_inv (p : {p : S ⟶ A.left // p ≫ A.hom = 𝟙 _}) :
    Additive.ofMul (Over.homMk (p.1 ≫ ι[A].left)
      (by rw [Category.assoc, Over.w ι[A], p.2]; rfl) : Over.mk (𝟙 S) ⟶ A) =
      -Additive.ofMul (Over.homMk p.1 p.2 : Over.mk (𝟙 S) ⟶ A) := by
  apply Additive.toMul.injective
  change _ = (Over.homMk p.1 p.2 : Over.mk (𝟙 S) ⟶ A)⁻¹
  rw [CategoryTheory.Hom.inv_def]
  ext
  rfl

end Inverse

section NeronTate

variable {K : Type u} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
  {A : Over (Spec (.of K))} [GrpObj A] [IsAbelianVariety K A]

/-- **The polar of a Néron–Tate height on the diagonal.** If `f = ½ b(x, x) + ℓ(x)` and
`r = p + p`, then `f r - 2 f p = b(p, p) = f p + f (-p)`. -/
private lemma IsNeronTateHeight.polar_self {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    {f : {p : Spec (.of K) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ}
    (hf : IsNeronTateHeight A c f) (p r : {p : Spec (.of K) ⟶ A.left // p ≫ A.hom = 𝟙 _})
    (hr : (Additive.ofMul (Over.homMk r.1 r.2) : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A)) =
      .ofMul (Over.homMk p.1 p.2) + .ofMul (Over.homMk p.1 p.2)) :
    f r - f p - f p = f p + f ⟨p.1 ≫ ι[A].left, by rw [Category.assoc, Over.w ι[A], p.2]⟩ := by
  obtain ⟨-, b, -, ℓ, hfx⟩ := hf
  rw [hfx r, hr, hfx p, hfx ⟨_, _⟩, ofMul_homMk_comp_inv]
  simp only [map_add, map_neg, AddMonoidHom.add_apply, AddMonoidHom.neg_apply, neg_neg]
  ring

end NeronTate

variable {k : Type u} [Field k]

/-- **The Néron norm is the height of `θ + θ⁻`.** In the situation of `Faltings.neronPairing`,
let `θ = Stacks.Divisors.picardClass D` and `θ⁻ = [-1]^* θ`. If `f`, `f'`, `f''` are the
Néron–Tate heights on `J_K` of the classes of `θ`, `θ⁻`, `θ + θ⁻`, then for `x ∈ J(K)`,
`⟨x, x⟩ = f x + f' x = f'' x`. -/
@[faltings "lem_nt_neron_norm_ample_height"]
theorem neronPairing_self_eq_add_and_add_eq [NumberField k] (X : CurveWithDegreeOneDivisor k)
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
    let cls : A.J.left.picardGroup → ℚ ⊗[ℤ] Stacks.Picard.ofScheme JK.left :=
      fun c ↦ (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.J.hom φK) c
    let pt : Additive (Over.mk φK ⟶ A.J) → {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} :=
      fun z ↦ ⟨pullback.lift z.toMul.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
    let θ := Stacks.Divisors.picardClass D
    let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
    ∀ f f' f'' : {p : Spec (.of K) ⟶ JK.left // p ≫ JK.hom = 𝟙 _} → ℝ,
      IsNeronTateHeight JK (cls θ) f → IsNeronTateHeight JK (cls θm) f' →
      IsNeronTateHeight JK (cls (θ + θm)) f'' → ∀ x,
        neronPairing X A hg j hj D hrad hsupp K x x = f (pt x) + f' (pt x) ∧
          f (pt x) + f' (pt x) = f'' (pt x) := by
  have := A.isAbelianVariety
  let : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  intro φK JK cls pt θ θm f f' f'' hf hf' hf'' x
  let : IsCommMonObj JK := isCommMonObj_of_isProper_of_geometricallyIntegral JK
  -- the class of `θ⁻` on `J_K` is the pull-back of the class of `θ` along `[-1]`
  have hι : ι[JK].left ≫ pullback.fst A.J.hom φK = pullback.fst A.J.hom φK ≫ ι[A.J].left := by
    change ((Over.pullback φK).map ι[A.J]).left ≫ _ = _
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hcls : (Stacks.Picard.schemePullbackClassHom ι[JK].left).toIntLinearMap.baseChange ℚ
      (cls θ) = cls θm := by
    simp only [cls, θm, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
      schemePullbackClassHom_eq_pullbackPicardHom]
    rw [← Stacks.SheafOfModules.pullbackPicardHom_comp_apply, hι,
      Stacks.SheafOfModules.pullbackPicardHom_comp_apply]
  have hf'eq := hf'.unique (hcls ▸ hf.comp ι[JK])
  have hadd : (1 : ℚ) • cls θ + (1 : ℚ) • cls θm = cls (θ + θm) := by
    simp only [one_smul, cls, map_add, TensorProduct.tmul_add]
  have hf''eq := hf''.unique (hadd ▸ hf.smul_add_smul hf' 1 1)
  refine ⟨?_, by simp [hf''eq]⟩
  change QuadraticMap.polar
    ((Classical.epsilon fun f ↦ IsNeronTateHeight JK (cls θ) f) ∘ pt) x x = _
  rw [(Classical.epsilon_spec ⟨f, hf⟩).unique hf, hf'eq]
  exact hf.polar_self (pt x) (pt (x + x))
    (congrArg Additive.ofMul (GroupScheme.toBaseChange_mul φK A.J x.toMul x.toMul))

end Faltings
