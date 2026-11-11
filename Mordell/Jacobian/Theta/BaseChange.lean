module
public import Mordell.Jacobian.Theta.Basic
public import Mordell.Jacobian.AbelJacobiBaseChange
public import Mordell.Jacobian.BaseChange
public import Mordell.Jacobian.Points

/-!
# Changing the base divisor of the theta divisor

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C` with `ι` additive, and let `j_P : C ⟶ J` be the Abel–Jacobi
map. Let `K ⊇ k` be a field, `P₀` a divisor of degree one on `C_K = C ×_k Spec K`, and
`e = ι(Spec K)(cl(P_K - P₀)) ∈ J(K)`. Over `K` the theta divisors of the two base divisors
differ by a translation:
`Θ_P = Θ_{P₀} - (g - 1) e` inside `J_K = J ×_k Spec K`.

## Main results

* `Faltings.thetaDivisor_baseChange_eq_image_translate`: the preimage of
  `Faltings.thetaDivisor X A hg j hj` in `J_K` is the image of the theta divisor of `(C_K, P₀)`,
  for the Jacobian `(J_K, ι_K)`, under translation by `-(g - 1) e`.

## Implementation notes

The base change `J_K` is `(Over.pullback (Spec K ⟶ Spec k)).obj J`, with the group law and the
abelian-variety structure it carries in the library, and the base-changed curve is
`pullback.snd f (Spec K ⟶ Spec k)`. That this is again a smooth projective curve over `K` is
part of `Faltings.Jacobian.exists_baseChange`, and its genus is that of `C`
(`Faltings.genus_baseChange`). The morphism of functors `ι_K : P⁰_{C_K} ⟶ J_K(-)` restricting
`ι` is characterised elementwise, as in `Faltings.Jacobian.exists_baseChange`; any such `ι_K` is
additive and bijective where `C_K` has points (`Faltings.Jacobian.map_add_of_baseChange`,
`Faltings.Jacobian.isIso_app_of_baseChange`), so `(J_K, ι_K)` is a Jacobian of `C_K`. The theta
divisor of `(C_K, P₀)` is `Faltings.thetaDivisor` for this Jacobian and the Abel–Jacobi map
`j_{P₀} : C_K ⟶ J_K`.

"`Θ_P` over `K`" is the preimage of `Θ_P` under the projection `J_K ⟶ J`, which is the
underlying set of the base change of the subscheme `Θ_P`. The point `e` is the
`k`-morphism `Spec K ⟶ J` given by `ι` on the `k`-scheme `Spec K`, and it is read as a `K`-point
`Spec K ⟶ J_K` through the universal property of the fibre product. The translation by
`-(g - 1) e` is the `K`-endomorphism `x ↦ x · (e^{g-1})⁻¹` of `J_K`, written in the group
`Hom_K(J_K, J_K)`.

The morphism `ι` of a `Faltings.Jacobian` is a morphism of set-valued functors; its additivity
`hι` is a hypothesis, without which the statement fails: replacing `ι` by `ι · a` for a
`k`-point `a ≠ 1` of `J` gives again a Jacobian, which translates both theta divisors by
`(g - 1) a` and `e` by `a`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Sections 2 and 6.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Picard
  Stacks.RigidifiedPicard
open scoped MonObj

universe u

namespace Faltings

section BaseChange

open MonoidalCategory CartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

private lemma sumMap_comp_eq (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (Y : Over (Spec (.of k))) (j : Y ⟶ A) (j₀ : (Over.pullback π).obj Y ⟶ (Over.pullback π).obj A)
    (e : Over.mk π ⟶ A)
    (hrel : P Y (𝟙 _) ≫ j = P A j₀ *
      ((Over.homMk ((Over.pullback π).obj Y).hom : (Over.map π).obj ((Over.pullback π).obj Y) ⟶
        Over.mk π) ≫ e)⁻¹)
    (n : ℕ) :
    let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback π).obj A :=
      Over.homMk (pullback.lift e.left (𝟙 _) (by simp [Over.w e])) (pullback.lift_snd _ _ _)
    let τ : (Over.pullback π).obj A ⟶ (Over.pullback π).obj A :=
      𝟙 _ * (Over.homMk ((Over.pullback π).obj A).hom (Category.comp_id _) ≫ eK ^ n)⁻¹
    sumMap n j₀ ≫ τ =
      inv (piComparison (Over.pullback π) (fun _ : Fin n => Y)) ≫
        (Over.pullback π).map (sumMap n j) := by
  intro eK τ
  set CN₀ := ∏ᶜ fun _ : Fin n => (Over.pullback π).obj Y
  let c : (Over.map π).obj CN₀ ⟶ A := (Over.homMk CN₀.hom : (Over.map π).obj CN₀ ⟶ Over.mk π) ≫ e
  apply ((Over.mapPullbackAdj π).homEquiv CN₀ A).symm.injective
  change P A _ = P A _
  rw [P_comp_right]
  let u₀ : CN₀ ⟶ Over.mk (𝟙 (Spec (.of K))) := Over.homMk CN₀.hom (Category.comp_id _)
  have h1 : sumMap n j₀ ≫ τ = sumMap n j₀ * (u₀ ≫ eK ^ n)⁻¹ := by
    simp only [τ, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc]
    congr 3
    ext
    simpa [u₀] using Over.w (sumMap n j₀)
  have h2 : P A (u₀ ≫ eK) = c := by
    ext
    rw [P_left]
    simp [c, eK, u₀]
  have h3 : ∀ i, P (∏ᶜ fun _ : Fin n => Y)
      (inv (piComparison (Over.pullback π) fun _ : Fin n => Y)) ≫
        Pi.π (fun _ : Fin n => Y) i ≫ j = P A (Pi.π _ i ≫ j₀) * c⁻¹ := by
    intro i
    have hπ : inv (piComparison (Over.pullback π) fun _ : Fin n => Y) ≫
        (Over.pullback π).map (Pi.π (fun _ : Fin n => Y) i) = Pi.π _ i := by
      rw [IsIso.inv_comp_eq, piComparison_comp_π]
    have hP := P_comp_left Y (Pi.π (fun _ : Fin n => (Over.pullback π).obj Y) i) (𝟙 _)
    rw [Category.comp_id] at hP
    rw [← Category.assoc, ← P_comp_right, hπ, hP, Category.assoc, hrel, MonObj.comp_mul,
      GrpObj.comp_inv, ← P_comp_left, ← Category.assoc]
    congr 3
    ext
    simpa using Over.w (Pi.π (fun _ : Fin n => (Over.pullback π).obj Y) i)
  rw [h1, ← pEquiv_apply, map_mul, map_inv, MonObj.comp_pow, map_pow, pEquiv_apply A (u₀ ≫ eK), h2,
    sumMap, map_list_prod, List.map_ofFn, comp_list_prod, List.map_ofFn]
  simp only [Function.comp_def, pEquiv_apply, List.prod_ofFn]
  rw [Finset.prod_congr rfl (fun i _ => h3 i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, inv_pow]

private lemma range_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) :
    Set.range (f ≫ g) = Set.range g := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, f.surjective.range_comp]

/-- The base change of `S : Y ⟶ A` has image the preimage of the image of `S`. -/
private lemma range_pullback_map_left {A Y : Over (Spec (.of k))} (S : Y ⟶ A) :
    Set.range ((Over.pullback π).map S).left = pullback.fst A.hom π ⁻¹' Set.range S.left := by
  have hp : ((Over.pullback π).map S).left ≫ pullback.fst A.hom π =
      pullback.fst Y.hom π ≫ S.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hbig : IsPullback (((Over.pullback π).map S).left ≫ pullback.snd A.hom π)
      (pullback.fst Y.hom π) π (S.left ≫ A.hom) := by
    have h1 : ((Over.pullback π).map S).left ≫ pullback.snd A.hom π = pullback.snd Y.hom π := by
      simp only [Over.pullback_map_left]
      exact pullback.lift_snd _ _ _
    rw [h1, Over.w S]
    exact (IsPullback.of_hasPullback Y.hom π).flip
  have h := IsPullback.of_right hbig hp (IsPullback.of_hasPullback A.hom π).flip
  rw [← h.isoPullback_hom_fst, range_comp_of_isIso, Scheme.Pullback.range_fst]

private lemma preimage_range_sumMap_eq (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (Y : Over (Spec (.of k))) (j : Y ⟶ A) (j₀ : (Over.pullback π).obj Y ⟶ (Over.pullback π).obj A)
    (e : Over.mk π ⟶ A)
    (hrel : P Y (𝟙 _) ≫ j = P A j₀ *
      ((Over.homMk ((Over.pullback π).obj Y).hom : (Over.map π).obj ((Over.pullback π).obj Y) ⟶
        Over.mk π) ≫ e)⁻¹)
    (n : ℕ) :
    let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback π).obj A :=
      Over.homMk (pullback.lift e.left (𝟙 _) (by simp [Over.w e])) (pullback.lift_snd _ _ _)
    let τ : (Over.pullback π).obj A ⟶ (Over.pullback π).obj A :=
      𝟙 _ * (Over.homMk ((Over.pullback π).obj A).hom (Category.comp_id _) ≫ eK ^ n)⁻¹
    pullback.fst A.hom π ⁻¹' Set.range (sumMap n j).left =
      τ.left '' Set.range (sumMap n j₀).left := by
  intro eK τ
  have h := sumMap_comp_eq A Y j j₀ e hrel n
  rw [← Set.range_comp, ← range_pullback_map_left]
  change _ = Set.range (sumMap n j₀ ≫ τ).left
  rw [h, Over.comp_left, range_comp_of_isIso]

end BaseChange

section Picard

/-- The class of the zero section is preserved by pull-back along an isomorphism of pointed
families. -/
public lemma schemePullbackClass_picardClass_zeroDivisor {S : Scheme.{u}}
    (E E' : ModuliEllipticCurves.PointedFamily S) [IsSeparated E.map]
    [SmoothOfRelativeDimension 1 E.map] [IsSeparated E'.map] [SmoothOfRelativeDimension 1 E'.map]
    (φ : E'.total ⟶ E.total) [IsIso φ] (hφ : E'.zero ≫ φ = E.zero) :
    haveI := E.isEffectiveCartierDivisor_zeroDivisor
    haveI := E'.isEffectiveCartierDivisor_zeroDivisor
    schemePullbackClass φ (Stacks.Divisors.picardClass E.zeroDivisor) =
      Stacks.Divisors.picardClass E'.zeroDivisor := by
  have hE := E.isEffectiveCartierDivisor_zeroDivisor
  have := E'.isEffectiveCartierDivisor_zeroDivisor
  have : Stacks.Divisors.IsPullbackDefined φ E.zeroDivisor :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hE
  have : IsClosedImmersion E.zero := E.isClosedImmersion_zero
  have hsq : IsPullback E'.zero (𝟙 _) φ E.zero :=
    IsPullback.of_vert_isIso ⟨by rw [hφ, Category.id_comp]⟩
  rw [Stacks.Divisors.schemePullbackClass_picardClass]
  congr 1
  rw [ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_ker,
    ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_ker,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hsq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

end Picard

variable {k : Type u} [Field k]

/-- **Changing the base divisor of `Θ`.** Let `X = (C, P)` be a curve over `k` with a divisor
of degree one, of genus `g ≥ 1`, `A = (J, ι)` a Jacobian of `C` with `ι` additive, and
`j = j_P` its Abel–Jacobi map. Let `K ⊇ k` be a field, `P₀` a divisor of degree one on
`C_K = C ×_k Spec K`, `(J_K, ι_K)` the base-changed Jacobian of `C_K`, `j₀ = j_{P₀}` the
Abel–Jacobi map of `(C_K, P₀)` and `e = ι(Spec K)(cl(P_K - P₀)) ∈ J(K)`. Then
`Θ_P = Θ_{P₀} - (g - 1) e` over `K`: the preimage of `Faltings.thetaDivisor X A hg j hj` in
`J_K` is the image of the theta divisor of `(C_K, P₀)` under translation by `-(g - 1) e`. -/
@[faltings "lem_nt_theta_change_base"]
public theorem thetaDivisor_baseChange_eq_image_translate (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f) {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (K : Type u) [Field K] [Algebra k K]
    (P₀ : {x : ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) //
      IsClosed ({x} : Set ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))} →₀ ℤ)
    (hP₀ : (P₀.sum fun x n =>
      n * ((pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree
        x.1 : ℤ)) = 1) :
    /- `C_K` is a smooth projective curve over `K`. -/
    haveI : IsSmoothProjectiveCurve K
        (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      (Jacobian.exists_baseChange k K X.f A).fst
    /- `ι_K : P⁰_{C_K} ⟶ J_K(-)`, the restriction of `ι`. -/
    ∀ (ι' : relativePicZeroFunctor K
          (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⋙
          forget AddCommGrpCat ⟶
        yoneda.obj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J))
    (hι'c : ∀ (T : Over (Spec (.of K)))
        (x : (relativePicZeroFunctor k X.f).obj
          (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)))
        (y : (relativePicZeroFunctor K
          (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj (op T)),
        (∃ a b, x = QuotientAddGroup.mk a ∧ y = QuotientAddGroup.mk b ∧
          (b : smallOfScheme
              (bc (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T)) =
            smallSchemePullbackClassHom
            (pullback.lift
              (pullback.fst
                (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T.hom ≫
                pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              (pullback.snd _ T.hom) (by
                simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
                  pullback.condition_assoc]) :
              bc (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T ⟶
                bc X.f ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T))
            (a : smallOfScheme
              (bc X.f ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)))) →
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left),
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    let π := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let T : Over (Spec (.of k)) := Over.mk π
    /- The curve `(C_K, P₀)` over `K`. -/
    let X₀ : CurveWithDegreeOneDivisor K := ⟨pullback X.f π, pullback.snd X.f π, P₀, hP₀⟩
    /- The base change `J_K` of `J`, and the Jacobian `(J_K, ι_K)` of `C_K`. -/
    let JK : Over (Spec (.of K)) := (Over.pullback π).obj A.J
    haveI := A.isAbelianVariety
    let A₀ : Jacobian K X₀.f :=
      ⟨JK, inferInstance, ι', Jacobian.map_add_of_baseChange X.f A ι' hι'c,
        Jacobian.isIso_app_of_baseChange X.f A ι' hι'c⟩
    haveI : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback X.f T.hom) inferInstance
    haveI : Smooth (bcProj X.f T) := SmoothOfRelativeDimension.smooth 1 _
    haveI : IsCurve K (bcProj X.f T) :=
      Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one (bcProj X.f T)
    /- The class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`. -/
    let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    /- The class `[𝒪(P₀)] = ∑ nₓ [𝒪(x)]` in `Pic(C_K)`. -/
    let classP₀ : Stacks.Picard.ofScheme (bc X.f T) := P₀.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (C := bc X.f T) (bcProj X.f T) x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (C := bc X.f T) x)
    /- `cl(P_K - P₀)` in `Pic(C_K)`, in the small model of the Picard group. -/
    let zₑ : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀)
    /- `C_K` has genus `g ≥ 1`. -/
    have hg₀ : 1 ≤ genus X₀.f :=
      hg.trans_eq (genus_baseChange k K (pullback.fst X.f π) X₀.f X.f
        (IsPullback.of_hasPullback X.f π)).symm
    ∀ {j₀ : Over.mk X₀.f ⟶ A₀.J} (hj₀ : IsAbelJacobiMap X₀ A₀ j₀)
      (e : T ⟶ A.J),
    (∀ hdeg : degree X.f hdim T zₑ = 0,
      e = A.ι.app (op T)
        (show (relativePicZeroFunctor k X.f).obj (op T) from
          QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker))) →
    /- `e` as a `K`-point of `J_K`, and the translation `τ_{-(g-1)e}` of `J_K`. -/
    let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK :=
      Over.homMk (pullback.lift e.left (𝟙 _) (by simpa [T] using Over.w e))
        (pullback.lift_snd _ _ _)
    let τ : JK ⟶ JK := 𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ eK ^ (genus X.f - 1))⁻¹
    pullback.fst A.J.hom π ⁻¹' thetaDivisor X A hg j hj =
      τ.left '' thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := by
  have : IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (Jacobian.exists_baseChange k K X.f A).fst
  intro ι' hι'c hdim π T X₀ JK A₀ classP classP₀ zₑ hg₀ j₀ hj₀ e he eK τ
  have := A.isAbelianVariety
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have hgen : genus X₀.f = genus X.f :=
    genus_baseChange k K (pullback.fst X.f π) X₀.f X.f (IsPullback.of_hasPullback X.f π)
  have hrel : P (Over.mk X.f) (𝟙 _) ≫ j =
      P (T := (Over.pullback π).obj (Over.mk X.f)) A.J j₀ *
      ((Over.homMk ((Over.pullback π).obj (Over.mk X.f)).hom :
        (Over.map π).obj ((Over.pullback π).obj (Over.mk X.f)) ⟶ Over.mk π) ≫ e)⁻¹ := by
    have hAJ := IsAbelJacobiMap.comp_fst_eq_mul_inv X A hι hj K P₀ hP₀
      (P (T := (Over.pullback π).obj (Over.mk X.f)) A.J j₀) e ?_ he
    · have h1 : P (Over.mk X.f) (𝟙 ((Over.pullback π).obj (Over.mk X.f))) =
          Over.homMk (pullback.fst X.f π) pullback.condition := by
        ext
        rw [P_left]
        simp
        rfl
      rwa [h1]
    · intro L _ _ _ _ Q T' hL g Qk E z hdeg
      let TL : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      let ι₀ : T' ≅ (Over.map π).obj TL :=
        Over.isoMk (Iso.refl _) (by rwa [Iso.refl_hom, Category.id_comp])
      let w : (relativePicZeroFunctor k X.f).obj (op T') :=
        QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T').ker)
      have hnat : A.ι.app (op ((Over.map π).obj TL))
          ((relativePicZeroFunctor k X.f).map ι₀.inv.op w) = ι₀.inv ≫ A.ι.app (op T') w :=
        ConcreteCategory.congr_hom (A.ι.naturality ι₀.inv.op) w
      let bcIso : bc X₀.f TL ⟶ bc X.f T' :=
        pullback.lift (pullback.fst X₀.f TL.hom ≫ pullback.fst X.f π) (pullback.snd X₀.f TL.hom)
          (by
            rw [Category.assoc, pullback.condition]
            exact (pullback.condition_assoc (f := X₀.f) (g := TL.hom) π).trans
              (congrArg _ hL))
      have hbig : IsPullback (pullback.fst X₀.f TL.hom ≫ pullback.fst X.f π)
          (pullback.snd X₀.f TL.hom) X.f T'.hom := by
        rw [← hL]
        exact (IsPullback.of_hasPullback X₀.f TL.hom).paste_horiz (IsPullback.of_hasPullback X.f π)
      have : IsIso bcIso := by
        rw [show bcIso = hbig.isoPullback.hom by
          apply pullback.hom_ext
          · rw [hbig.isoPullback_hom_fst]
            exact pullback.lift_fst _ _ _
          · rw [hbig.isoPullback_hom_snd]
            exact pullback.lift_snd _ _ _]
        infer_instance
      have hbcIsopb : IsPullback bcIso (bcProj X₀.f TL) (bcProj X.f T') (𝟙 _) :=
        @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _) ⟨by
          rw [Category.comp_id]
          exact pullback.lift_snd _ _ _⟩
      have hbc : bcIso ≫ bcMap X.f g = pullback.fst X₀.f TL.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, bcMap_fst]
          exact pullback.lift_fst _ _ _
        · rw [Category.assoc, bcMap_snd, ← Category.assoc]
          erw [pullback.lift_snd]
          exact pullback.condition.symm
      have hlift : (pullback.lift (pullback.fst X₀.f TL.hom ≫ pullback.fst X.f π)
          (pullback.snd X₀.f TL.hom) (by
            rw [Over.map_obj_hom, Category.assoc, pullback.condition]
            exact pullback.condition_assoc π) :
            bc X₀.f TL ⟶ bc X.f ((Over.map π).obj TL)) ≫
          bcMap X.f ι₀.inv = bcIso := by
        apply pullback.hom_ext
        · rw [Category.assoc, bcMap_fst]
          exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, bcMap_snd]
          exact ((pullback.lift_snd_assoc _ _ _ _).trans (Category.comp_id _)).trans
            (pullback.lift_snd _ _ _).symm
      let E' : ModuliEllipticCurves.PointedFamily TL.left :=
        ⟨bc X₀.f TL, bcProj X₀.f TL, pullback.lift Q.left (𝟙 TL.left) (Over.w Q),
          pullback.lift_snd _ _ _⟩
      have hsec : E'.zero ≫ bcIso = E.zero := by
        apply pullback.hom_ext
        · rw [Category.assoc]
          erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
          rfl
        · rw [Category.assoc]
          erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
          rfl
      have : SmoothOfRelativeDimension 1 (bcProj X.f T') :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback X.f T'.hom) inferInstance
      have : IsSeparated E.map := inferInstanceAs (IsSeparated (bcProj X.f T'))
      have : SmoothOfRelativeDimension 1 E.map := ‹SmoothOfRelativeDimension 1 (bcProj X.f T')›
      have : SmoothOfRelativeDimension 1 (bcProj X₀.f TL) :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback X₀.f TL.hom) inferInstance
      have : IsSeparated E'.map := inferInstanceAs (IsSeparated (bcProj X₀.f TL))
      have : SmoothOfRelativeDimension 1 E'.map :=
        ‹SmoothOfRelativeDimension 1 (bcProj X₀.f TL)›
      have := E'.isEffectiveCartierDivisor_zeroDivisor
      have hcl := schemePullbackClass_picardClass_zeroDivisor E E' bcIso hsec
      have : Smooth X₀.f := SmoothOfRelativeDimension.smooth 1 X₀.f
      have : IsCurve K X₀.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X₀.f
      have hdim₀ : ∀ s, topologicalKrullDim ↥(X₀.f.fiber s) ≤ 1 := fun s =>
        (topologicalKrullDim_fiber_spec X₀.f s).trans_le
          (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X₀.f)
      let classP₀' : ofScheme X₀.C := X₀.P.sum fun x n =>
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
      let z₀ : smallOfScheme (bc X₀.f TL) := (smallEquiv (bc X₀.f TL)).symm
        (Stacks.Divisors.picardClass E'.zeroDivisor -
          schemePullbackClass (pullback.fst X₀.f TL.hom) classP₀')
      have hz : z₀ = smallSchemePullbackClassHom bcIso z := by
        apply (smallEquiv.{u} _).injective
        rw [smallEquiv_smallSchemePullbackClassHom]
        simp only [z₀, z, AddEquiv.apply_symm_apply]
        rw [show ∀ a b, schemePullbackClass bcIso (a - b) =
            schemePullbackClass bcIso a - schemePullbackClass bcIso b from
          fun a b => map_sub (schemePullbackClassHom bcIso) a b,
          hcl, schemePullbackClass_comp, hbc]
        rfl
      have hdeg₀ : degree X₀.f hdim₀ TL z₀ = 0 := by
        rw [hz, degree_smallSchemePullbackClassHom_of_isPullback X.f X₀.f hdim hdim₀ bcIso
          (𝟙 _) hbcIsopb, hdeg]
        rfl
      have h0 := hj₀ L Q hdeg₀
      let a : (degree X.f hdim ((Over.map π).obj TL)).ker :=
        ⟨smallSchemePullbackClassHom (bcMap X.f ι₀.inv) z, by
          rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_bcMap, hdeg]
          rfl⟩
      have hc := hι'c TL ((relativePicZeroFunctor k X.f).map ι₀.inv.op w)
        (QuotientAddGroup.mk (⟨z₀, hdeg₀⟩ : (degree X₀.f hdim₀ TL).ker))
        ⟨a, ⟨z₀, hdeg₀⟩, rfl, rfl, by
          change z₀ = _
          rw [hz, smallSchemePullbackClassHom_comp, hlift]⟩
      apply Over.OverMorphism.ext
      rw [← Iso.hom_inv_id_assoc ι₀ (A.ι.app (op T') w), ← hnat]
      exact (congrArg (Qk.left ≫ ·) (P_left A.J j₀)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (·.left ≫ pullback.fst A.J.hom π) h0).trans
          (hc.trans (Category.id_comp _).symm)))
  change pullback.fst A.J.hom π ⁻¹' Set.range (sumMap (genus X.f - 1) j).left =
    τ.left '' Set.range (sumMap (genus X₀.f - 1) j₀).left
  rw [hgen]
  exact preimage_range_sumMap_eq A.J (Over.mk X.f) j j₀ e hrel (genus X.f - 1)

end Faltings
