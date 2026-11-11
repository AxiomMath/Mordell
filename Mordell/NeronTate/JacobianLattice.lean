module

public import Mathlib
public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
import Mordell.MordellWeil.Main
import Mordell.NeronTate.Pairing.SelfHeight
import Mordell.NeronTate.Pairing.Bilinear
import Mordell.NeronTate.Nonneg
import Mordell.NeronTate.Northcott
import Mordell.Algebra.Quadratic.LatticeCriterion
import Mordell.Jacobian.Autoduality.Ample
import Mordell.Jacobian.Theta.PrimeDivisor
import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbedding
import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# The Néron–Tate lattice of a Jacobian

Let `k` be a number field, `(C, P)` a curve of genus `g ≥ 1` over `k` with a rational divisor of
degree one, `(J, ι)` a Jacobian of `C` and `⟨ , ⟩` the Néron form on `J(k̄)`. For every number
field `K` with `k ⊆ K ⊆ k̄` the group `J(K)` is commutative, and the Néron form restricted to
`J(K)` extends to a positive definite inner product on the real vector space `J(K) ⊗_ℤ ℝ`.

The proof: `J(K)` is finitely generated (Mordell–Weil over `K`). The height `ĥ_θ` is a quadratic
form plus a linear form, so `⟨ , ⟩` is symmetric and biadditive, and `⟨x, x⟩ = ĥ_θ(x) + ĥ_θ(-x)`
is the Néron–Tate height of the class `θ + θ⁻`, which is ample and even. By Northcott's theorem
the sets `{x ∈ J(K) | ⟨x, x⟩ ≤ C}` are finite, and the lattice criterion gives positive
definiteness.

## Main results

* `Faltings.exists_posDef_extension_neronPairing`: the Néron form `Faltings.neronPairing` on
  `J(K)` extends to a positive definite symmetric `ℝ`-bilinear form on the real base change of
  `J(K)`.

## Implementation notes

The Néron form `Faltings.neronPairing` is defined on `J(k̄)`, `k̄` an algebraic closure of `k`.
The field `K` is an intermediate extension `k ⊆ K ⊆ k̄` (`IsScalarTower k K k̄`), and a point
`x : Spec K ⟶ J` over `Spec k` is read in `J(k̄)` by precomposing with `Spec k̄ ⟶ Spec K`; this
map `res : J(K) → J(k̄)` is the inclusion of `J(K)` in `J(k̄)`. The `K`-points of `J` form a
commutative group under the group law of `J` (`CategoryTheory.Hom.commGroup`, commutative by
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`), written additively
through `Additive`. The real vector space `J(K) ⊗_ℤ ℝ` is any `V` with `j : J(K) →ₗ[ℤ] V`
satisfying `IsBaseChange ℝ j`, and the extension `Bf` is pinned by `Bf (j x) (j y) = ⟨x, y⟩`.

Autoduality gives ampleness of `θ + θ⁻` as an ample invertible sheaf in the sense of Stacks,
Tag 01PS; on the proper variety `J` over `k`, a power of such a sheaf is the pull-back of `𝒪(1)`
along a closed immersion into projective space, which is ampleness of the class in the sense of
`Faltings.IsAmpleClass`. The prime divisor `Θ` of autoduality is identified with the reduced
ideal sheaf `D` of the Néron form through their common support.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped MonObj

universe u

namespace Faltings

/-- An ample invertible sheaf `M` on a projective variety `X` over `k` has a class
`1 ⊗ [M]` that is ample in the sense of `Faltings.IsAmpleClass`: a power of `M` is the
pull-back of `𝒪(1)` along a closed immersion into projective space over `k`. -/
private lemma isAmpleClass_of_isAmple {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (M : X.Modules)
    [hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (hM : Scheme.Modules.IsAmple X M) (c : Stacks.Picard.ofScheme X)
    (hc : Stacks.SheafOfModules.picardClass X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) M
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hinv) = c) :
    IsAmpleClass f (TensorProduct.comm ℤ ℚ _ ((1 : ℚ) ⊗ₜ c)) := by
  have : Stacks.Ample.IsInvertibleModule X M := hinv
  obtain ⟨d, hd, N, ψ, hψ, hover, ⟨e⟩⟩ :=
    Stacks.AmpleFormalSystemEmbedding.exists_isClosedImmersion_projectiveSpaceOver_of_isAmple f M
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X M).2 hM)
  refine ⟨1, M, inferInstance, le_rfl, ⟨d, by exact_mod_cast hd, N, ⟨ψ, hψ, hover⟩, ⟨e⟩⟩, ?_⟩
  rw [one_smul, TensorProduct.comm_tmul, ← hc]
  rfl

/-- A reduced ideal sheaf with the support of a prime divisor is the ideal sheaf of that prime
divisor. -/
private lemma PrimeDivisor.idealSheaf_eq_of_support_eq {X : Scheme.{u}}
    (Z : Stacks.Divisors.PrimeDivisor X) {D : X.IdealSheafData} (hrad : D.radical = D)
    (hsupp : D.support = Z.support) : Z.idealSheaf = D := by
  have : IsIntegral Z.idealSheaf.subscheme := Z.integral
  have hZrad : Z.idealSheaf.radical = Z.idealSheaf := by
    ext1
    funext U
    rw [Scheme.IdealSheafData.radical_ideal, ← Z.idealSheaf.ker_subschemeι, Scheme.Hom.ker_apply]
    exact Ideal.radical_eq_iff.mpr
      ((RingHom.ker_isRadical_iff_reduced_of_surjective
        (Z.idealSheaf.subschemeι_app_surjective U)).mpr inferInstance)
  rw [← hZrad, ← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext1
  exact hsupp.symm

/-- **The Néron–Tate lattice of a Jacobian.** Let `k` be a number field, `X = (C, P)` a curve of
genus `g ≥ 1` over `k` with a divisor of degree one, `A = (J, ι)` a Jacobian of `C`, and
`⟨ , ⟩ = Faltings.neronPairing` the Néron form on `J(k̄)`. For every number field `K` between `k`
and `k̄`, the restriction of `⟨ , ⟩` to `J(K)` extends to a positive definite symmetric bilinear
form on the real vector space `J(K) ⊗_ℤ ℝ`, exhibited as `V` by `j : J(K) → V`. -/
@[faltings "thm_mw_neron_tate_lattice"]
theorem exists_posDef_extension_neronPairing {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 1 ≤ genus X.f)
    (jac : Over.mk X.f ⟶ A.J) (hjac : IsAbelJacobiMap X A jac) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg jac hjac)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (K : Type u) [Field K] [NumberField K] [Algebra k K] [Algebra K kbar]
    [IsScalarTower k K kbar] :
    haveI := A.isAbelianVariety
    letI := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
    letI : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :=
      Hom.commGroup
    let res : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) →
        Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A.J) :=
      fun x ↦ .ofMul (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) (by
          simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]) ≫ x.toMul)
    ∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
      (j : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) →ₗ[ℤ] V)
      (_hj : IsBaseChange ℝ j),
      ∃ Bf : LinearMap.BilinForm ℝ V,
        (∀ x y, Bf (j x) (j y) = neronPairing X A hg jac hjac D hrad hsupp kbar (res x) (res y)) ∧
        Bf.IsSymm ∧ Bf.toQuadraticMap.PosDef := by
  have := A.isAbelianVariety
  have := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  intro res V _ _ j hj
  -- `D` is the ideal sheaf of the prime divisor `Θ`, and `θ + θ⁻` is ample and even
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg jac hjac
  obtain rfl := PrimeDivisor.idealSheaf_eq_of_support_eq Z hrad (hsupp.trans hZ.symm)
  obtain ⟨heven, M, _, hMamp, hMcl⟩ :=
    isEvenClass_thetaClass_add_inv_and_exists_isAmple X A hg jac hjac Z hZ
  have : IsProjectiveVariety k A.J.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.J.hom)
      (isProjective_of_isAbelianVariety k A.J)⟩
  have hamp := isAmpleClass_of_isAmple A.J.hom M hMamp _ hMcl
  -- `⟨x, x⟩ = ĥ_{θ + θ⁻}(x)` on `J(k̄)`
  have : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  have : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
  let θ := Stacks.Divisors.picardClass Z.idealSheaf
  let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
  obtain ⟨f, hf⟩ := exists_isNeronTateHeight A.J kbar ((1 : ℚ) ⊗ₜ θ)
  obtain ⟨f', hf'⟩ := exists_isNeronTateHeight A.J kbar ((1 : ℚ) ⊗ₜ θm)
  obtain ⟨F, hF⟩ := exists_isNeronTateHeight A.J kbar ((1 : ℚ) ⊗ₜ (θ + θm))
  have hF' := hF
  rw [LinearMap.baseChange_tmul] at hf hf' hF'
  have hnorm := fun x ↦ (neronPairing_self_eq_add_and_add_eq X A hg jac hjac Z.idealSheaf hrad
    hsupp kbar f f' F hf hf' hF' x).elim Eq.trans
  -- restricted to `J(K)`, the Néron form is a symmetric biadditive form `b`
  obtain ⟨Bk, hBks, hBk⟩ := exists_addMonoidHom_eq_neronPairing X A hg jac hjac Z.idealSheaf
    hrad hsupp kbar
  let s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) (by
      simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])
  let resHom : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) →+
      Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A.J) :=
    MonoidHom.toAdditive ((yonedaMonObj A.J).map s.op).hom
  let b := (Bk.comp resHom).compl₂ resHom
  have hb : ∀ x y, b x y = neronPairing X A hg jac hjac Z.idealSheaf hrad hsupp kbar
      (res x) (res y) := fun x y => (hBk _ _).symm
  have hbb : ∀ x, b x x = F _ := fun x ↦ (hb x x).trans (hnorm (res x))
  -- Mordell–Weil, nonnegativity and Northcott feed the lattice criterion
  have : Module.Finite ℤ (Additive (Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k K))) ⟶ A.J)) := Module.Finite.iff_addGroup_fg.2
    (AddGroup.fg_iff_mul_fg.2 (group_fg_points_of_numberField K A.J))
  obtain ⟨Bf, hBf, hsymm, hpos⟩ := exists_bilinForm_posDef_of_finite_setOf_le b
    (fun x y => hBks _ _)
    (fun x ↦ hbb x ▸ IsEvenClass.nonneg_of_isNeronTateHeight hamp heven kbar F hF _)
    (fun C ↦ by
      simp_rw [hbb]
      exact IsEvenClass.finite_setOf_neronTateHeight_le_of_numberField hamp heven kbar K C F hF)
      j hj
  exact ⟨Bf, fun x y => (hBf x y).trans (hb x y), hsymm, hpos⟩

end Faltings

end
