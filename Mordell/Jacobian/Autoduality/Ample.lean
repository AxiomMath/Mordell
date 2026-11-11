module

public import Mordell.Attr
public import Mordell.AbelianVariety.EvenOddClass
public import Mordell.Jacobian.Autoduality.Injective
public import Mordell.AbelianVariety.Ample.FiniteStabiliser
public import Mordell.AbelianVariety.Ample.Automorphism
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AbelMap
public import StacksFrontier.AlgebraicGeometry.TensorPowerProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic

/-!
# Autoduality: ampleness of `θ + θ⁻`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C`, `j = j_P` the Abel–Jacobi map and `Θ = W^{g-1} ⊆ J` the theta
divisor. `Θ` is a prime divisor on the smooth variety `J`, hence an effective Cartier divisor, and
`θ = [𝒪_J(Θ)] ∈ Pic(J)` is its class; `θ⁻ = [-1]^* θ` is its pull-back along the inversion of
`J`. Then `θ + θ⁻` is an ample even class: its image in `Pic(J) ⊗ ℚ` is fixed by `[-1]^*`, and it
is the class of an ample invertible sheaf.

The proof follows [MilAV, III, 6.6]. Let `K` be an algebraic closure of `k`. A `K`-point `x` of
`J` with `τ_x^* Θ_K = Θ_K` has `φ_θ(x) = τ_x^* θ - θ = 0`, so `x = 0` by the injectivity of
`φ_θ` (`Faltings.injective_phiMap_picardClass_thetaDivisor`). The stabiliser of `Θ_K` is
therefore finite, and `θ` is ample (`Faltings.isAmple_of_finite_setOf_comap_translation_eq`).
Then `θ⁻ = [-1]^* θ` is ample (`Faltings.isAmple_of_picardClass_eq_schemePullbackClass`), and so
is the tensor product of the two (Stacks, Tag 0890), whose class is `θ + θ⁻`. It is even since
`[-1] ∘ [-1] = id`.

## Main results

* `Faltings.isEvenClass_thetaClass_add_inv_and_exists_isAmple`: `θ + θ⁻` is even and ample.

## Implementation notes

The theorem is stated over the base field `k` of the Jacobian, for arbitrary `k`; the case of an
algebraically closed `k` is the statement over `k̄`. The prime divisor with support `Θ` is an
argument `Z`, pinned by `Z.support = Faltings.thetaDivisor X A hg j hj` (a prime divisor is
determined by its support); it exists by `Faltings.exists_primeDivisor_support_eq_thetaDivisor`.
That `Z` is an effective Cartier divisor (automatic on the smooth variety `J`) is an instance
argument, which is what makes the invertible sheaf `𝒪_J(Z)` =
`Stacks.Divisors.invertibleSheaf Z.idealSheaf` and its class `θ` formable.

Ampleness is stated in `Pic(J)` itself, by an ample invertible representative of `θ + θ⁻`; this
implies ampleness of `1 ⊗ (θ + θ⁻)` in `Pic(J) ⊗ ℚ` (take `e = 1`).

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 5.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Theorem 6.6, Lemma 6.9, Summary 6.11.
* [MumAV] D. Mumford, *Abelian Varieties*, Sec. 6, Application 1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory AlgebraicGeometry
  TensorProduct
open scoped MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- An ideal sheaf whose closed subscheme is reduced is its own radical. -/
private lemma radical_eq_self_of_isReduced {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [IsReduced D.subscheme] : D.radical = D := by
  ext1
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, ← D.ker_subschemeι, Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr
    ((RingHom.ker_isRadical_iff_reduced_of_surjective
      (D.subschemeι_app_surjective U)).mpr inferInstance)

/-- **Autoduality; ampleness of `θ + θ⁻`** ([MilAV, III, 6.6], [B, Sec. 5]). Let `X = (C, P)` be
a curve over `k` with a divisor of degree one, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian of `C`,
`j = j_P` the Abel–Jacobi map, and `Z` the prime divisor of `J` with support the theta divisor
`Faltings.thetaDivisor X A hg j hj`, an effective Cartier divisor. Write `θ ∈ Pic(J)` for the
class of `𝒪_J(Z)` and `θ⁻ = [-1]^* θ`. Then `θ + θ⁻` is even, i.e. `1 ⊗ (θ + θ⁻)` satisfies
`Faltings.IsEvenClass`, and it is ample: it is the class of an ample invertible sheaf on `J`. -/
@[faltings "thm_nt_autoduality"]
theorem isEvenClass_thetaClass_add_inv_and_exists_isAmple (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (Z : Stacks.Divisors.PrimeDivisor A.J.left)
    (hZ : Z.support = thetaDivisor X A hg j hj)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf] :
    haveI := A.isAbelianVariety
    let θ : Stacks.Picard.ofScheme A.J.left :=
      Stacks.SheafOfModules.picardClass A.J.left.presheaf
        (Stacks.RingedSpace.structureIsSheaf A.J.left.toRingedSpace)
        (Stacks.Divisors.invertibleSheaf Z.idealSheaf)
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance)
    IsEvenClass k A.J
        (1 ⊗ₜ (θ + Stacks.Picard.schemePullbackClass (GrpObj.inv (X := A.J)).left θ)) ∧
      ∃ (M : A.J.left.Modules)
        (_ : AlgebraicGeometry.SheafOfModules.IsInvertible A.J.left.toRingedSpace.presheaf
          (structureSheafRing A.J.left.toRingedSpace).property M),
        Scheme.Modules.IsAmple A.J.left M ∧
        Stacks.SheafOfModules.picardClass A.J.left.presheaf
            (Stacks.RingedSpace.structureIsSheaf A.J.left.toRingedSpace) M
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M ‹_›) =
          θ + Stacks.Picard.schemePullbackClass (GrpObj.inv (X := A.J)).left θ := by
  have := A.isAbelianVariety
  intro θ
  classical
  set D := Z.idealSheaf
  have : IsIntegral D.subscheme := Z.integral
  have hrad : D.radical = D := radical_eq_self_of_isReduced D
  have hθ : θ = Stacks.Divisors.picardClass D := rfl
  /- The inversion `[-1]` of `J`, an automorphism of the underlying scheme. -/
  let σ : A.J.left ≅ A.J.left :=
    { hom := (GrpObj.inv (X := A.J)).left
      inv := (GrpObj.inv (X := A.J)).left
      hom_inv_id := by rw [← Over.comp_left, GrpObj.inv_comp_inv]; rfl
      inv_hom_id := by rw [← Over.comp_left, GrpObj.inv_comp_inv]; rfl }
  /- Evenness: `[-1]^*(θ + θ⁻) = θ⁻ + θ`. -/
  have hinvinv : Stacks.Picard.schemePullbackClass σ.hom
      (Stacks.Picard.schemePullbackClass σ.hom θ) = θ := by
    rw [Stacks.Picard.schemePullbackClass_comp]
    exact (congrArg (fun f => Stacks.Picard.schemePullbackClass f θ) σ.hom_inv_id).trans
      (Stacks.Picard.schemePullbackClass_id _ θ)
  refine ⟨?_, ?_⟩
  · change (Stacks.Picard.schemePullbackClassHom σ.hom).toIntLinearMap.baseChange ℚ _ = _
    rw [LinearMap.baseChange_tmul]
    congr 1
    change Stacks.Picard.schemePullbackClass σ.hom _ = _
    rw [Stacks.Picard.schemePullbackClass_add, hinvinv, add_comm]
  /- `θ` is ample: its stabiliser over `K = k̄` lies in `ker φ_θ = 0`. -/
  let K := AlgebraicClosure k
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hinj := injective_phiMap_picardClass_thetaDivisor X A hg j hj D hrad hZ K
  have : Flat (fst A.J T).left := by
    change Flat (Limits.pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (fst A.J T).left) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ D inferInstance
  have hfstθ : Stacks.Picard.schemePullbackClass (fst A.J T).left (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass (D.comap (fst A.J T).left) :=
    Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ D _ rfl
  have key : ∀ x : T ⟶ A.J, (D.comap (fst A.J _).left).comap
      (lift (lift (fst _ _) (snd _ _ ≫ x) ≫ μ) (snd _ _)).left = D.comap (fst A.J _).left →
      AbelianVariety.phiMap A.J (Stacks.Divisors.picardClass D) x = 0 := by
    intro x hx
    have hτ : (lift (fst A.J T) (snd A.J T ≫ x) ≫ μ).left =
        (lift (lift (fst A.J T) (snd A.J T ≫ x) ≫ μ) (snd A.J T)).left ≫ (fst A.J T).left := by
      rw [← Over.comp_left, lift_fst]
    have h2 : Stacks.Picard.schemePullbackClass
        (lift (lift (fst A.J T) (snd A.J T ≫ x) ≫ μ) (snd A.J T)).left
        (Stacks.Divisors.picardClass (D.comap (fst A.J T).left)) =
        Stacks.Divisors.picardClass (D.comap (fst A.J T).left) :=
      Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ _ hx.symm
    unfold AbelianVariety.phiMap
    rw [hτ, ← Stacks.Picard.schemePullbackClass_comp, hfstθ, h2, sub_self]
  have hfin : {x : T ⟶ A.J | (D.comap (fst A.J _).left).comap
      (lift (lift (fst _ _) (snd _ _ ≫ x) ≫ μ) (snd _ _)).left = D.comap (fst A.J _).left}.Finite :=
    Set.Subsingleton.finite fun x hx y hy => hinj ((key x hx).trans (key y hy).symm)
  let L : A.J.left.Modules := Stacks.Divisors.invertibleSheaf D
  have hL : Scheme.Modules.IsAmple A.J.left L :=
    isAmple_of_finite_setOf_comap_translation_eq A.J K D hfin L (Iso.refl _)
  /- `θ⁻ = [-1]^* θ` is ample. -/
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap σ.hom) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ D inferInstance
  have hD' : Stacks.Picard.schemePullbackClass σ.hom (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass (D.comap σ.hom) :=
    Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ D _ rfl
  let L' : A.J.left.Modules := Stacks.Divisors.invertibleSheaf (D.comap σ.hom)
  have hL' : Scheme.Modules.IsAmple A.J.left L' :=
    isAmple_of_picardClass_eq_schemePullbackClass k A.J σ L L' hL hD'.symm
  /- `θ + θ⁻` is the class of the ample `L ⊗ L'`. -/
  let M : A.J.left.Modules := Scheme.Modules.tensorProductModule A.J.left L L'
  refine ⟨M, inferInstance, ?_, ?_⟩
  · exact Scheme.Modules.isAmple_tensor_of_power_sections_cover A.J.left L L' hL fun x =>
      let ⟨n, hn, s, hs, _⟩ := hL'.2 x; ⟨n, hn, s, hs⟩
  · rw [hθ, hD']
    exact (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L L' _ _ _).symm

end Faltings
