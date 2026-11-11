module
public import Mordell.Jacobian.BaseChange
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import Mordell.Jacobian.Theta.BaseChange
public import Mordell.AbelianVariety.PicZero
public import Mordell.Jacobian.Theta.PullbackTranslate
public import Mordell.Jacobian.Theta.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import Mordell.Jacobian.AbelJacobiBaseChange
public import Mordell.AlgebraicGeometry.ReducedImage

/-!
# Autoduality: `j^* φ_θ = -id`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C` with `ι` additive, `j = j_P : C ⟶ J` the Abel–Jacobi map and
`θ = cl(Θ) ∈ Pic(J)` the class of the theta divisor `Θ = W^{g-1}`. For an algebraically closed
field `K ⊇ k` and `b ∈ J(K)`, the class `φ_θ(b) = τ_b^* θ - θ ∈ Pic(J_K)` pulls back along
`j_K : C_K ⟶ J_K` to a class of degree zero, and under `ι(Spec K) : P⁰_C(Spec K) → J(K)` this
class goes to `-b`. In other words the dual of `j` is `-φ_θ^{-1}`: this is Milne's
`f^∨ = -φ_{L(Θ)}^{-1}`.

The proof follows [MilAV, III, Lemma 6.9]. Choose a `K`-point `P₀` of `C_K` and put
`e = ι(cl(P_K - P₀))`. Then `j_P = τ_{-e} ∘ j_{P₀}` on `C_K`
(`Faltings.IsAbelJacobiMap.comp_fst_eq_mul_inv`) and `Θ_P = τ_{-(g-1)e} Θ_{P₀}` over `K`
(`Faltings.thetaDivisor_baseChange_eq_image_translate`). The class of the reduced divisor
`Θ_{P₀}` is therefore the pull-back of `θ` along the translation, `Θ` being geometrically reduced
as the scheme-theoretic image of the smooth `C^{g-1}`. For a `K`-point `a`, Jacobi inversion
(Riemann–Roch in degree `g`) writes `ι⁻¹(a) + g[P₀]` as an effective divisor `D_a`, and
`(a - j_{P₀})^*[Θ_{P₀}] = [D_a]` (`Faltings.schemePullbackClass_thetaDivisor_translate_eq`).
Since `[-1]^*` acts as `-1` on `Pic⁰(J_K)` (`Faltings.schemePullbackClassHom_inv_of_mem_picZero`),
`j^* φ_θ(b) = -(-j)^* φ_θ(b) = [D_{e^g}] - [D_{e b e^{g-1}}]`, which `ι` sends to `b⁻¹`.

## Main results

* `Faltings.Jacobian.ι_app_pullback_phiMap_theta_eq_inv`: `j^* φ_θ(b)` has degree zero on `C_K`
  and `ι(Spec K)` sends its class to `-b`.

## Implementation notes

The theta divisor `Faltings.thetaDivisor` is a subset of `J`; its class `θ` is the Picard class
`Stacks.Divisors.picardClass D` of the reduced effective Cartier divisor `D` with support `Θ`
(it exists, `Θ` being a prime divisor on the smooth variety `J`, and it is unique, a reduced
closed subscheme being determined by its support). The statement therefore takes such a `D`.

The morphism `ι` of a `Faltings.Jacobian` is a morphism of set-valued functors; its additivity
`hι` is a hypothesis, without which the statement fails: replacing `ι` by `ι · a` for a
`k`-point `a ≠ 1` of `J` gives again a Jacobian, with Abel–Jacobi map `j · a`, and moves the
right-hand side by `a_K` while leaving the left-hand side unchanged.

The group law of `J(K) = Hom_k(Spec K, J)` is written multiplicatively, so `-b` is `b⁻¹`.
The base change `j_K` is `j ×_k Spec K : C ×_k Spec K ⟶ J ×_k Spec K`, and the class of
`P⁰_C(Spec K)` is the class of the pulled-back Picard class read in the small model
`Stacks.Picard.smallOfScheme`, as in `Faltings.IsAbelJacobiMap`. That this class has degree zero
on the fibre is part of the conclusion. Since `Pic(Spec K) = 0`, `P⁰_C(Spec K)` is the group of
degree-zero classes on `C_K`.

The `K`-points of `J_K = J ×_k Spec K` are compared with the `k`-morphisms `Spec K ⟶ J`
through the adjunction `Over.map ⊣ Over.pullback`, which is multiplicative. The base-changed
`ι_K` is the one of `Faltings.Jacobian.exists_baseChange`; its additivity follows from that of
`ι`, which is the hypothesis `hι`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Lemma 6.9, Remark 6.10(c), Summary 6.11.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.RigidifiedPicard
open scoped MonObj

universe u

namespace Faltings

/-! ### Comparing `ι` and its base change -/

section Link

open Stacks.Picard

variable {k : Type u} [Field k]

/-- The canonical comparison `C_K ×_K Spec L ⟶ C ×_k Spec L`, an isomorphism. -/
@[expose] public noncomputable abbrev bcIso (X : CurveWithDegreeOneDivisor k) (K L : Type u)
    [Field K] [Algebra k K] [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    bc (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ⟶
      bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst X.f _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc]
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

/-- **`ι_K` restricts `ι`**, on classes: if a degree-zero class `z₀` on `C_K ×_K Spec L` is the
pull-back of a degree-zero class `z` on `C ×_k Spec L`, then `ι_K(z₀)` and `ι(z)` are the same
`L`-point of `J`. -/
public lemma ι'_app_left_fst (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (K : Type u) [Field K] [Algebra k K]
    [IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (ι' : relativePicZeroFunctor K
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
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1)
    (hdim₀ : ∀ s, topologicalKrullDim
      ↥((pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fiber s) ≤ 1)
    (z : smallOfScheme (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))))
    (hdeg : degree X.f hdim _ z = 0)
    (z₀ : smallOfScheme (bc (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))))
    (hdeg₀ : degree _ hdim₀ _ z₀ = 0)
    (hz : z₀ = smallSchemePullbackClassHom (bcIso X K L) z) :
    (ι'.app (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
        (show (relativePicZeroFunctor K _).obj _ from
          QuotientAddGroup.mk (⟨z₀, hdeg₀⟩ : (degree _ hdim₀ _).ker))).left ≫
        pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      (A.ι.app (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
        (show (relativePicZeroFunctor k X.f).obj _ from
          QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim _).ker))).left := by
  have hL : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let T' : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let TL : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let ι₀ : T' ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj TL :=
    Over.isoMk (Iso.refl _) (by
      rw [Iso.refl_hom, Category.id_comp]
      exact hL)
  let w : (relativePicZeroFunctor k X.f).obj (op T') :=
    QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T').ker)
  have hnat : A.ι.app (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj TL))
      ((relativePicZeroFunctor k X.f).map ι₀.inv.op w) = ι₀.inv ≫ A.ι.app (op T') w :=
    ConcreteCategory.congr_hom (A.ι.naturality ι₀.inv.op) w
  have hlift : (pullback.lift (pullback.fst _ TL.hom ≫ pullback.fst X.f _)
      (pullback.snd _ TL.hom) (by
        rw [Over.map_obj_hom, Category.assoc, pullback.condition]
        exact pullback.condition_assoc _) :
        bc (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) TL ⟶
          bc X.f ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj TL)) ≫
      bcMap X.f ι₀.inv = bcIso X K L := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst]
      exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, bcMap_snd]
      exact ((pullback.lift_snd_assoc _ _ _ _).trans (Category.comp_id _)).trans
        (pullback.lift_snd _ _ _).symm
  let a : (degree X.f hdim
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj TL)).ker :=
    ⟨smallSchemePullbackClassHom (bcMap X.f ι₀.inv) z, by
      rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_bcMap, hdeg]
      rfl⟩
  have hc := hι'c TL ((relativePicZeroFunctor k X.f).map ι₀.inv.op w)
    (QuotientAddGroup.mk (⟨z₀, hdeg₀⟩ : (degree _ hdim₀ TL).ker))
    ⟨a, ⟨z₀, hdeg₀⟩, rfl, rfl, by
      change z₀ = _
      rw [hz, smallSchemePullbackClassHom_comp, hlift]⟩
  refine hc.trans ?_
  rw [hnat]
  exact Category.id_comp _

/-- **The base-changed `ι_K` is additive** when `ι` is: `ι_K` is `ι` read through the
isomorphisms `C_K ×_K T ≅ C ×_k T` and `Hom_K(T, J_K) ≅ Hom_k(T, J)`, the latter multiplicative. -/
public lemma ι'_add (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (K : Type u) [Field K] [Algebra k K]
    [IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (ι' : relativePicZeroFunctor K
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
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left) :
    haveI := A.isAbelianVariety
    ∀ (T : Over (Spec (.of K))) (x y : (relativePicZeroFunctor K
        (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj (op T)),
      (show T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J from
          ι'.app (op T) (x + y)) =
        (show T ⟶ _ from ι'.app (op T) x) * (show T ⟶ _ from ι'.app (op T) y) := by
  intro T x y
  let π := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  have hdim₀ : ∀ s, topologicalKrullDim ↥((pullback.snd X.f π).fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec (pullback.snd X.f π) s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension (pullback.snd X.f π))
  let lft : bc (pullback.snd X.f π) T ⟶ bc X.f ((Over.map π).obj T) :=
    pullback.lift (pullback.fst (pullback.snd X.f π) T.hom ≫ pullback.fst X.f π)
      (pullback.snd _ T.hom) (by
        simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
          pullback.condition_assoc])
  have hbig : IsPullback (pullback.fst (pullback.snd X.f π) T.hom ≫ pullback.fst X.f π)
      (pullback.snd (pullback.snd X.f π) T.hom) X.f ((Over.map π).obj T).hom :=
    (IsPullback.of_hasPullback (pullback.snd X.f π) T.hom).paste_horiz
      (IsPullback.of_hasPullback X.f π)
  have hlft : lft = hbig.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [hbig.isoPullback_hom_fst]
      exact pullback.lift_fst _ _ _
    · rw [hbig.isoPullback_hom_snd]
      exact pullback.lift_snd _ _ _
  have : IsIso lft := by rw [hlft]; infer_instance
  have hpb : IsPullback (inv lft) (bcProj X.f ((Over.map π).obj T))
      (bcProj (pullback.snd X.f π) T) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, IsIso.inv_comp_eq]
      exact (pullback.lift_snd _ _ _).symm⟩
  /- Every class upstairs comes from a class downstairs. -/
  have hcomp : ∀ b : (degree (pullback.snd X.f π) hdim₀ T).ker,
      ∃ a : (degree X.f hdim ((Over.map π).obj T)).ker,
        (b : smallOfScheme _) = smallSchemePullbackClassHom lft (a : smallOfScheme _) := by
    intro b
    refine ⟨⟨smallSchemePullbackClassHom (inv lft) b, ?_⟩, ?_⟩
    · rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_of_isPullback _ _ hdim₀ hdim
        _ _ hpb, AddMonoidHom.mem_ker.1 b.2]
      rfl
    · change _ = smallSchemePullbackClassHom lft (smallSchemePullbackClassHom (inv lft) b)
      rw [smallSchemePullbackClassHom_comp, IsIso.hom_inv_id, smallSchemePullbackClassHom_id]
  have hP : ∀ (a : (degree X.f hdim ((Over.map π).obj T)).ker)
      (b : (degree (pullback.snd X.f π) hdim₀ T).ker),
      (b : smallOfScheme _) = smallSchemePullbackClassHom lft (a : smallOfScheme _) →
      P A.J (show T ⟶ _ from ι'.app (op T) (QuotientAddGroup.mk b)) =
        A.ι.app (op _) (QuotientAddGroup.mk a) := fun a b hab => by
    ext
    rw [P_left]
    exact hι'c T _ _ ⟨a, b, rfl, rfl, hab⟩
  induction x using QuotientAddGroup.induction_on with | H b₁ => ?_
  induction y using QuotientAddGroup.induction_on with | H b₂ => ?_
  obtain ⟨a₁, h₁⟩ := hcomp b₁
  obtain ⟨a₂, h₂⟩ := hcomp b₂
  apply (pEquiv A.J T).injective
  dsimp only
  rw [map_mul, pEquiv_apply, pEquiv_apply, pEquiv_apply]
  erw [← QuotientAddGroup.mk_add]
  rw [hP (a₁ + a₂) (b₁ + b₂) (by
      change ((b₁ : smallOfScheme (bc (pullback.snd X.f π) T)) + b₂) =
        smallSchemePullbackClassHom lft
          ((a₁ : smallOfScheme (bc X.f ((Over.map π).obj T))) + a₂)
      rw [map_add, ← h₁, ← h₂]),
    hP a₁ b₁ h₁, hP a₂ b₂ h₂, QuotientAddGroup.mk_add]
  exact hι _ _ _

/-- The Abel–Jacobi map of `(C_K, P₀)` for the Jacobian `(J_K, ι_K)`, read as a `k`-morphism
`C_K ⟶ J`, is `τ_e ∘ j_P` on `C_K` (`Faltings.IsAbelJacobiMap.comp_fst_eq_mul_inv`). -/
public lemma P_comp_eq_mul_inv (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (K : Type u) [Field K] [Algebra k K]
    [IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (P₀ : {x : ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) //
      IsClosed ({x} : Set ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))} →₀ ℤ)
    (hP₀ : (P₀.sum fun x n =>
      n * ((pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree
        x.1 : ℤ)) = 1)
    (ι' : relativePicZeroFunctor K
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
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left)
    (hι' : ∀ T : Over (Spec (.of K)),
      Nonempty (T ⟶ Over.mk (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) →
        IsIso (ι'.app (op T))) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    let π := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let T : Over (Spec (.of k)) := Over.mk π
    let X₀ : CurveWithDegreeOneDivisor K := ⟨pullback X.f π, pullback.snd X.f π, P₀, hP₀⟩
    let JK : Over (Spec (.of K)) := (Over.pullback π).obj A.J
    haveI := A.isAbelianVariety
    let A₀ : Jacobian K X₀.f :=
      ⟨JK, inferInstance, ι', Jacobian.map_add_of_baseChange X.f A ι' hι'c, hι'⟩
    haveI : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback X.f T.hom) inferInstance
    haveI : Smooth (bcProj X.f T) := SmoothOfRelativeDimension.smooth 1 _
    haveI : IsCurve K (bcProj X.f T) :=
      Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one (bcProj X.f T)
    let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    let classP₀ : Stacks.Picard.ofScheme (bc X.f T) := P₀.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (C := bc X.f T) (bcProj X.f T) x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (C := bc X.f T) x)
    let zₑ : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀)
    ∀ {j₀ : Over.mk X₀.f ⟶ A₀.J} (_hj₀ : IsAbelJacobiMap X₀ A₀ j₀) (e : T ⟶ A.J),
    (∀ hdeg : degree X.f hdim T zₑ = 0,
      e = A.ι.app (op T)
        (show (relativePicZeroFunctor k X.f).obj (op T) from
          QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker))) →
    P (Over.mk X.f) (𝟙 _) ≫ j =
      P (T := (Over.pullback π).obj (Over.mk X.f)) A.J j₀ *
      ((Over.homMk ((Over.pullback π).obj (Over.mk X.f)).hom :
        (Over.map π).obj ((Over.pullback π).obj (Over.mk X.f)) ⟶ Over.mk π) ≫ e)⁻¹ := by
  intro hdim π T X₀ JK A₀ classP classP₀ zₑ j₀ hj₀ e he
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
    have hbig : IsPullback (pullback.fst X₀.f TL.hom ≫ pullback.fst X.f π)
        (pullback.snd X₀.f TL.hom) X.f T'.hom := by
      rw [← hL]
      exact (IsPullback.of_hasPullback X₀.f TL.hom).paste_horiz (IsPullback.of_hasPullback X.f π)
    have : IsIso (bcIso X K L) := by
      rw [show bcIso X K L = hbig.isoPullback.hom by
        apply pullback.hom_ext
        · rw [hbig.isoPullback_hom_fst]
          exact pullback.lift_fst _ _ _
        · rw [hbig.isoPullback_hom_snd]
          exact pullback.lift_snd _ _ _]
      infer_instance
    have hbcIsopb : IsPullback (bcIso X K L) (bcProj X₀.f TL) (bcProj X.f T') (𝟙 _) :=
      @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _) ⟨by
        rw [Category.comp_id]
        exact pullback.lift_snd _ _ _⟩
    have hbc : bcIso X K L ≫ bcMap X.f g = pullback.fst X₀.f TL.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, bcMap_snd, ← Category.assoc]
        erw [pullback.lift_snd]
        exact pullback.condition.symm
    let E' : ModuliEllipticCurves.PointedFamily TL.left :=
      ⟨bc X₀.f TL, bcProj X₀.f TL, pullback.lift Q.left (𝟙 TL.left) (Over.w Q),
        pullback.lift_snd _ _ _⟩
    have hsec : E'.zero ≫ bcIso X K L = E.zero := by
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
    have hcl := schemePullbackClass_picardClass_zeroDivisor E E' (bcIso X K L) hsec
    have : Smooth X₀.f := SmoothOfRelativeDimension.smooth 1 X₀.f
    have : IsCurve K X₀.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X₀.f
    have hdim₀ : ∀ s, topologicalKrullDim ↥(X₀.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X₀.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X₀.f)
    let classP₀' : Stacks.Picard.ofScheme X₀.C := X₀.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    let z₀ : Stacks.Picard.smallOfScheme (bc X₀.f TL) := (smallEquiv (bc X₀.f TL)).symm
      (Stacks.Divisors.picardClass E'.zeroDivisor -
        Stacks.Picard.schemePullbackClass (pullback.fst X₀.f TL.hom) classP₀')
    have hz : z₀ = Stacks.Picard.smallSchemePullbackClassHom (bcIso X K L) z := by
      apply (smallEquiv.{u} _).injective
      rw [smallEquiv_smallSchemePullbackClassHom]
      simp only [z₀, z, T', AddEquiv.apply_symm_apply]
      rw [show ∀ a b, Stacks.Picard.schemePullbackClass (bcIso X K L) (a - b) =
          Stacks.Picard.schemePullbackClass (bcIso X K L) a -
            Stacks.Picard.schemePullbackClass (bcIso X K L) b from
        fun a b => map_sub (Stacks.Picard.schemePullbackClassHom (bcIso X K L)) a b,
        hcl, Stacks.Picard.schemePullbackClass_comp, hbc]
      rfl
    have hdeg₀ : degree X₀.f hdim₀ TL z₀ = 0 := by
      rw [hz, degree_smallSchemePullbackClassHom_of_isPullback X.f X₀.f hdim hdim₀ (bcIso X K L)
        (𝟙 _) hbcIsopb, hdeg]
      rfl
    have h0 := hj₀ L Q hdeg₀
    apply Over.OverMorphism.ext
    exact (congrArg (Qk.left ≫ ·) (P_left A.J j₀)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (·.left ≫ pullback.fst A.J.hom π) h0).trans
        (ι'_app_left_fst X A K ι' hι'c L hdim hdim₀ z hdeg z₀ hdeg₀ hz)))

end Link

/-! ### Flat base change of a reduced scheme-theoretic image -/

/-- **`Θ` is geometrically reduced**: if `D` is a reduced closed subscheme of `J` supported on
`Θ`, its inverse image along any base change `φ : J ×_k Spec K ⟶ J` is reduced. `D` is the
scheme-theoretic image of the summation morphism `σ : C^{g-1} ⟶ J`, the source `C^{g-1}` stays
reduced (indeed smooth) over `K`, and `φ` is flat. -/
public lemma isReduced_comap_of_support_eq_thetaDivisor {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 1 ≤ genus X.f)
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [IsReduced D.subscheme] (hD : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] {Y : Scheme.{u}} (φ : Y ⟶ A.J.left)
    (ψ : Y ⟶ Spec (.of K))
    (hφ : IsPullback φ ψ A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsReduced (D.comap φ).subscheme := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat φ := MorphismProperty.of_isPullback hφ.flip inferInstance
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  let W := ∏ᶜ fun _ : Fin (genus X.f - 1) => Over.mk X.f
  let σ : W.left ⟶ A.J.left := (List.ofFn fun i : Fin (genus X.f - 1) =>
    Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i ≫ j).prod.left
  have : Smooth (Over.mk X.f).hom := ‹Smooth X.f›
  have : IsReduced W.left := isReduced_of_smooth W.hom
  have : IsProper A.J.hom := A.isAbelianVariety.toIsProper
  have : QuasiCompact σ := by
    have : IsProper (Over.mk X.f).hom := (inferInstance : IsProper X.f)
    have : IsProper W.hom := Stacks.RigidifiedPicard.isProper_fibrePower_hom _ _
    have : IsProper (σ ≫ A.J.hom) := by rw [Over.w]; infer_instance
    have : IsProper σ := .of_comp _ A.J.hom
    infer_instance
  /- `D` is the scheme-theoretic image of the summation morphism. -/
  have hDσ : D = σ.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D _ ?_
    ext1
    rw [TopologicalSpace.Closeds.coe_closure, ← show (D.support : Set A.J.left) = Set.range σ
      from hD, D.support.isClosed.closure_eq]
  /- The base change of `W` to `K` is reduced. -/
  have : IsReduced (pullback σ φ) := by
    have hbig := (IsPullback.of_hasPullback σ φ).paste_vert hφ
    rw [Over.w] at hbig
    have : IsReduced (pullback W.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      isReduced_of_smooth (pullback.snd W.hom _)
    exact isReduced_of_isOpenImmersion hbig.isoPullback.hom
  exact hDσ ▸ isReduced_comap_ker_of_flat σ φ

/-! ### Effective divisors of large degree -/

/-- **Riemann–Roch, existence half**: on a curve over an algebraically closed field, a Picard
class of degree at least the genus is the class of an effective divisor. -/
public lemma exists_nonneg_divisorClass_eq {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of K)) [IsProper g] [Smooth g] [IsCurve K g]
    [IsLocallyNoetherian C] (c : Stacks.Picard.ofScheme C)
    (hc : (genus g : ℤ) ≤
      Stacks.Picard.picardDegree g (Stacks.Zeta.topologicalKrullDim_le_one g) c) :
    ∃ D : Stacks.Zeta.ClosedPoint C →₀ ℤ, 0 ≤ D ∧ Stacks.Zeta.divisorClass g D = c := by
  letI := Stacks.Zeta.ffAlg g
  obtain ⟨E, hE⟩ := Stacks.Zeta.exists_divisorClass_eq g c
  have hRR := Stacks.Zeta.h0_sub_h1 g c
  have h0 : 0 < Stacks.Zeta.h0 g c := by omega
  rw [← hE, ← Stacks.Zeta.finrank_rrSpace g E] at h0
  have := Module.nontrivial_of_finrank_pos h0
  obtain ⟨⟨f, hfmem⟩, hf0⟩ := exists_ne (0 : Stacks.Zeta.rrSpace g E)
  have hf : f ≠ 0 := fun h => hf0 (Subtype.ext h)
  rcases (Stacks.Zeta.mem_rrSpace g).1 hfmem with h | h
  · exact absurd h hf
  refine ⟨E + Stacks.Zeta.divOf g hf, fun x => ?_, ?_⟩
  · simp only [Finsupp.coe_add, Pi.add_apply, Stacks.Zeta.divOf_apply, Finsupp.coe_zero,
      Pi.zero_apply]
    have := h x
    omega
  · rw [map_add, Stacks.Zeta.divisorClass_divOf, add_zero, hE]

/-- **Jacobi inversion**: on a curve over an algebraically closed field, if `c` has degree zero
and `p` has degree one, then `c + g p` is the class of an effective divisor of degree `g`. -/
private lemma exists_nonneg_divisor_eq_add_genus_smul {K : Type u} [Field K] [IsAlgClosed K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) [IsProper f] [Smooth f] [IsCurve K f]
    [IsLocallyNoetherian C] (hdimC : topologicalKrullDim C ≤ 1) {c p : Stacks.Picard.ofScheme C}
    (hc : invertibleCurveDegreeHom K f hdimC c = 0)
    (hp : invertibleCurveDegreeHom K f hdimC p = 1) :
    ∃ D : {x : C // IsClosed ({x} : Set C)} →₀ ℤ, 0 ≤ D ∧
      (D.sum fun x n =>
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) = c + (genus f : ℤ) • p ∧
      (D.sum fun x n => n * (f.residueDegree x.1 : ℤ)) = genus f := by
  have hcg : invertibleCurveDegreeHom K f hdimC (c + (genus f : ℤ) • p) = genus f := by
    rw [map_add, map_zsmul, hc, hp, zero_add, smul_eq_mul, mul_one]
  obtain ⟨D, hD0, hD⟩ := exists_nonneg_divisorClass_eq f (c + (genus f : ℤ) • p) hcg.ge
  have hDcl : (D.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) = c + (genus f : ℤ) • p :=
    (Stacks.Zeta.divisorClass_apply _ D).symm.trans hD
  exact ⟨D, hD0, hDcl, (degree_divisorClass f hdimC D).symm.trans (by rw [hDcl, hcg])⟩

/-- `e^g (e b e^{g-1})⁻¹ = b⁻¹` in a commutative group, for `g ≥ 1`. -/
private lemma pow_mul_inv_mul_pow_pred {G : Type*} [CommGroup G] (e b : G) {g : ℕ} (hg : 1 ≤ g) :
    e ^ g * (e * b * e ^ (g - 1))⁻¹ = b⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_inv_eq_iff_eq_mul, mul_comm e b, mul_assoc,
    inv_mul_cancel_left, mul_comm]

/-- A commutative-group identity used for the translate `τ_b ∘ (-j_P)`. -/
private lemma inv_mul_inv_mul_eq {G : Type*} [CommGroup G] (J x y : G) (n : ℕ) :
    (J * x⁻¹)⁻¹ * y = x * y * x ^ n * J⁻¹ * (x ^ n)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

/-- A commutative-group identity used for `-j_P`. -/
private lemma inv_mul_inv_eq {G : Type*} [CommGroup G] (J x : G) {g : ℕ} (hg : 1 ≤ g) :
    (J * x⁻¹)⁻¹ = x ^ g * J⁻¹ * (x ^ (g - 1))⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, Nat.add_sub_cancel]
  rw [succ_nsmul]
  abel

section

variable {k : Type u} [Field k]

/-- **Autoduality: `j^* φ_θ = -id`** ([MilAV, III, Lemma 6.9 and Summary 6.11]). Let
`X = (C, P)` be a curve over `k` with a divisor of degree one, of genus `g ≥ 1`, `A = (J, ι)` a
Jacobian of `C` with `ι` additive, `j = j_P` the Abel–Jacobi map, and `D` the reduced effective
Cartier divisor on `J` whose support is the theta divisor `Faltings.thetaDivisor X A hg j hj`, so
that `θ = Stacks.Divisors.picardClass D`. For an algebraically closed field `K ⊇ k` and `b ∈ J(K)`,
the pull-back of `φ_θ(b) = Faltings.AbelianVariety.phiMap A.J θ b` along
`j ×_k Spec K : C_K ⟶ J_K` has degree zero, and `ι(Spec K)` sends its class in `P⁰_C(Spec K)`
to `-b`. -/
@[faltings "lem_nt_abel_jacobi_pullback_phi"]
public theorem Jacobian.ι_app_pullback_phiMap_theta_eq_inv (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [IsReduced D.subscheme]
    (hD : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :
    let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    /- The base change `j_K = j ×_k Spec K : C_K ⟶ J_K`. -/
    let jK : bc X.f T ⟶ (A.J ⊗ T).left :=
      pullback.map X.f T.hom A.J.hom T.hom j.left (𝟙 _) (𝟙 _)
        (by simp) (by simp)
    /- `j_K^* φ_θ(b)` in `Pic(C_K)`, in the small model of the Picard group. -/
    let z : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Picard.schemePullbackClass jK
        (AbelianVariety.phiMap A.J (Stacks.Divisors.picardClass D) b))
    ∃ hdeg : degree X.f hdim T z = 0,
      A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
          QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T).ker)) = b⁻¹ := by
  intro T hdim jK z
  have := A.isAbelianVariety
  have hCK : IsSmoothProjectiveCurve K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    isSmoothProjectiveCurve_pullback_snd X.f _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : {x : ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) //
      IsClosed ({x} : Set ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))},
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree x₀.1 =
        1 := by
    have : CompactSpace ↥(pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
      (quasiCompact_iff_compactSpace
        (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).1 inferInstance
    exact exists_closedPoint_residueDegree_eq_one _
  let P₀ := Finsupp.single x₀ (1 : ℤ)
  have hP₀ : (P₀.sum fun x n =>
      n * ((pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree
        x.1 : ℤ)) = 1 := by
    simp [P₀, hx₀]
  obtain ⟨_, _, ι', _, hι', _, hι'c⟩ := Jacobian.exists_baseChange k K X.f A
  let X₀ : CurveWithDegreeOneDivisor K :=
    ⟨pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))), P₀, hP₀⟩
  let A₀ : Jacobian K X₀.f :=
    ⟨(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J, inferInstance,
      ι', Jacobian.map_add_of_baseChange X.f A ι' hι'c, hι'⟩
  have hgen : genus X₀.f = genus X.f :=
    genus_baseChange k K (pullback.fst X.f _) X₀.f X.f (IsPullback.of_hasPullback X.f _)
  have hg₀ : 1 ≤ genus X₀.f := hgen ▸ hg
  obtain ⟨j₀, hj₀, -⟩ := existsUnique_isAbelJacobiMap X₀ A₀
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have : Smooth (bcProj X.f T) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve K (bcProj X.f T) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one (bcProj X.f T)
  let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
  let classP₀ : Stacks.Picard.ofScheme (bc X.f T) := P₀.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (C := bc X.f T) (bcProj X.f T) x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal (C := bc X.f T) x)
  let zₑ : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
    (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀)
  let e : T ⟶ A.J := if h : degree X.f hdim T zₑ = 0 then
      A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨zₑ, h⟩ : (degree X.f hdim T).ker)) else 1
  have he : ∀ hdeg : degree X.f hdim T zₑ = 0, e = A.ι.app (op T)
      (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker)) :=
    fun hdeg => dite_eq_left hdeg
  have hΘ' :=
    thetaDivisor_baseChange_eq_image_translate X A hι hg hj K P₀ hP₀ ι' hι'c hj₀ e he
  have hrel := P_comp_eq_mul_inv X A hι hj K P₀ hP₀ ι' hι'c hι' hj₀ e he
  /- The base change `J_K`, the `K`-points `e_K`, `b_K` and the translation `τ = τ_{-(g-1)e}`. -/
  let JK : Over (Spec (.of K)) :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J
  have : IsAbelianVariety K JK := A₀.isAbelianVariety
  have : IsCommMonObj JK := isCommMonObj_of_isProper_of_geometricallyIntegral JK
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK :=
    Over.homMk (pullback.lift e.left (𝟙 _) (by simp [T]))
      (pullback.lift_snd _ _ _)
  let bK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK :=
    Over.homMk (pullback.lift b.left (𝟙 _) (by simp))
      (pullback.lift_snd _ _ _)
  let τ : JK ⟶ JK := 𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ eK ^ (genus X.f - 1))⁻¹
  have hΘ'' : pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹'
      thetaDivisor X A hg j hj = τ.left '' thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := hΘ'
  have : IsIso τ := by
    refine ⟨⟨𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ eK ^ (genus X.f - 1)), ?_, ?_⟩⟩
    · rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        Over.mkIdTerminal.hom_ext (τ ≫ Over.homMk JK.hom (Category.comp_id _))
          (Over.homMk JK.hom (Category.comp_id _)), mul_assoc, inv_mul_cancel, mul_one]
    · rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc,
        Over.mkIdTerminal.hom_ext (_ ≫ Over.homMk JK.hom (Category.comp_id _))
          (Over.homMk JK.hom (Category.comp_id _)), mul_assoc, mul_inv_cancel, mul_one]
  have : IsIso τ.left := (Over.forget _).map_isIso τ
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  /- The prime divisor `Θ_{P₀}` of `J_K` and the pull-back of `θ` to it. -/
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X₀ A₀ hg₀ j₀ hj₀
  have hZD : Z.idealSheaf =
      D.comap (τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    let φ := τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    have := isReduced_comap_of_support_eq_thetaDivisor X A hg hj D hD K φ JK.hom
      (IsPullback.of_iso (IsPullback.of_hasPullback A.J.hom _) (asIso τ.left).symm (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (by simp [φ]) (by
          simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp]
          exact Over.w τ) (by simp) (by simp))
    have := Z.integral
    refine eq_comap_of_preimage_support_eq Z.idealSheaf D φ ?_
    rw [hD]
    refine (preimage_comp_eq_of_preimage_eq_image τ.left.isOpenEmbedding.injective hΘ'').trans ?_
    exact hZ.symm
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf := by
    rw [hZD]
    exact Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have hZcl : Stacks.Divisors.picardClass Z.idealSheaf =
      Stacks.Picard.schemePullbackClass
        (τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Stacks.Divisors.picardClass D) := by
    have : Stacks.Divisors.IsPullbackDefined
        (τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) D :=
      Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
    rw [Stacks.Divisors.schemePullbackClass_picardClass]
    exact Stacks.Divisors.picardClass_congr hZD
  /- `K`-points of `J_K` as `k`-points of `J`. -/
  let tT : T ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk (𝟙 (Spec (.of K)))) := Over.homMk (𝟙 _) (by simp [T])
  let Φ : (Over.mk (𝟙 (Spec (.of K))) ⟶ JK) →* (T ⟶ A.J) :=
    { toFun := fun aK => tT ≫ P A.J aK
      map_one' := by
        rw [← pEquiv_apply, map_one, MonObj.comp_one]
      map_mul' := fun a b => by
        rw [← pEquiv_apply, map_mul, MonObj.comp_mul]
        rfl }
  have hΦ : ∀ aK, (Φ aK).left = aK.left ≫ pullback.fst A.J.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := fun aK => by
    change (tT ≫ P A.J aK).left = _
    rw [Over.comp_left, P_left]
    exact Category.id_comp _
  let u : Over.mk X₀.f ⟶ Over.mk (𝟙 (Spec (.of K))) := Over.homMk X₀.f (Category.comp_id _)
  /- The key computation, for one point. -/
  have key : ∀ aK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK, ∃ w : (degree X.f hdim T).ker,
      A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk w) = Φ aK ∧
      Stacks.Picard.schemePullbackClass (((u ≫ aK) * j₀⁻¹).left ≫ τ.left ≫
          pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Divisors.picardClass D) =
        smallEquiv (bc X.f T) (w : Stacks.Picard.smallOfScheme (bc X.f T)) +
          (genus X.f : ℤ) • classP₀ := by
    intro aK
    have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
      topologicalKrullDim_le_one_of_smoothOfRelativeDimension (bcProj X.f T)
    have : IsLocallyNoetherian (bc X.f T) := LocallyOfFiniteType.isLocallyNoetherian X₀.f
    have : Smooth X₀.f := ‹Smooth (bcProj X.f T)›
    have : IsCurve K X₀.f := ‹IsCurve K (bcProj X.f T)›
    have : IsProper X₀.f := inferInstanceAs (IsProper (bcProj X.f T))
    /- `C` has a `K`-point, so `ι(Spec K)` is bijective. -/
    have hpt : (pointOfClosedPoint (pullback.snd X.f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))) x₀.1 x₀.2 ≫ pullback.fst X.f _) ≫ X.f =
          Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
        Category.id_comp]
    have hC : Nonempty (T ⟶ Over.mk X.f) := ⟨Over.homMk _ hpt⟩
    have := A.isIso_app T hC
    obtain ⟨y, hy⟩ := ((isIso_iff_bijective (A.ι.app (op T))).1 inferInstance).2 (Φ aK)
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
    refine ⟨w, hy, ?_⟩
    /- Jacobi inversion: `cl(w) + g [P₀]` is the class of an effective divisor `D'`. -/
    let c : Stacks.Picard.ofScheme (bc X.f T) :=
      smallEquiv (bc X.f T) (w : Stacks.Picard.smallOfScheme (bc X.f T))
    have hc0 : invertibleCurveDegreeHom K (bcProj X.f T) hdimT c = 0 := by
      have h0 : degree X.f hdim T (w : Stacks.Picard.smallOfScheme (bc X.f T)) = 0 := w.2
      have h := (degree_apply X.f hdim T _ (IsLocalRing.closedPoint K)).symm.trans
        (congrFun h0 _)
      exact (relativeInvertibleDegreeHomAt_spec (k := K) (bcProj X.f T) hdimT _
        (IsLocalRing.closedPoint K) _).symm.trans h
    obtain ⟨D', hD'0, hD'cl, hDdeg⟩ :=
      exists_nonneg_divisor_eq_add_genus_smul (bcProj X.f T) hdimT hc0
      ((degree_divisorClass (bcProj X.f T) hdimT P₀).trans hP₀)
    rw [show genus (bcProj X.f T) = genus X.f from hgen] at hD'cl
    let T₀ : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K)))
    let t₀ : T₀ ⟶ Over.mk (𝟙 (Spec (.of K))) := Over.homMk T₀.hom (Category.comp_id _)
    have hι₀ := ι'_add X A hι K ι' hι'c
    have ht := schemePullbackClass_thetaDivisor_translate_eq X₀ x₀ rfl A₀ hι₀ hg₀ j₀ hj₀ Z hZ D'
      hD'0 hDdeg (t₀ ≫ aK)
    have hT₀ : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    have hfst : pullback.fst X₀.f T₀.hom = bcIso X K K := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).symm
      · refine (pullback.condition.trans ?_).trans (pullback.lift_snd _ _ _).symm
        exact (congrArg (pullback.snd X₀.f T₀.hom ≫ ·) hT₀).trans (Category.comp_id _)
    have hP₀cl : classP₀ = @Stacks.Divisors.picardClass (bc X.f T) (Stacks.Zeta.pointIdeal x₀)
        (Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x₀) := by
      simp only [classP₀, P₀, Finsupp.sum_single_index, zero_smul, one_smul]
      try rfl
    have hcD : (D'.sum fun x n => n • @Stacks.Divisors.picardClass (bc X.f T)
        (Stacks.Zeta.pointIdeal x) (Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x)) -
        (genus X₀.f : ℤ) • @Stacks.Divisors.picardClass (bc X.f T) (Stacks.Zeta.pointIdeal x₀)
          (Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X₀.f x₀) = c := by
      rw [hD'cl, hgen, ← hP₀cl]
      exact add_sub_cancel_right _ _
    have hψ : (Over.homMk (U := Over.mk X₀.f) (V := T₀) X₀.f
        (by simp [T₀, Algebra.algebraMap_self]) ≫ t₀ ≫ aK) * j₀⁻¹ = (u ≫ aK) * j₀⁻¹ := by
      rw [← Category.assoc, Over.mkIdTerminal.hom_ext (_ ≫ t₀) u]
    have ht' := ht (fun hdeg₀ => by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · rw [ι'_app_left_fst X A K ι' hι'c K hdim _ (w : Stacks.Picard.smallOfScheme (bc X.f T))
          w.2 _ hdeg₀ (by
            apply (smallEquiv.{u} _).injective
            rw [smallEquiv_smallSchemePullbackClassHom, AddEquiv.apply_symm_apply, ← hfst]
            exact congrArg _ hcD)]
        rw [Over.comp_left, Category.assoc, ← hΦ, ← hy]
        change Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ _ = _
        rw [hT₀, Category.id_comp]
      · exact (Over.w (t₀ ≫ aK)).trans (Over.w (ι'.app (op T₀) _)).symm)
    dsimp only at ht'
    rw [hψ] at ht'
    rw [← Stacks.Picard.schemePullbackClass_comp, ← hZcl]
    exact ht'.trans hD'cl
  obtain ⟨w₁, hw₁, hcl₁⟩ := key (eK * bK * eK ^ (genus X.f - 1))
  obtain ⟨w₂, hw₂, hcl₂⟩ := key (eK ^ genus X.f)
  /- The two group-law identities. -/
  let uJ : JK ⟶ Over.mk (𝟙 (Spec (.of K))) := Over.homMk JK.hom (Category.comp_id _)
  let jK' : Over.mk X₀.f ⟶ JK := Over.homMk jK (by
    change jK ≫ pullback.snd _ _ = pullback.snd _ _
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _))
  have hjK' : jK' = j₀ * (u ≫ eK)⁻¹ := by
    apply (pEquiv A.J (Over.mk X₀.f)).injective
    rw [map_mul, map_inv, pEquiv_apply, pEquiv_apply, pEquiv_apply]
    have h1 : P A.J jK' = P (Over.mk X.f) (𝟙 ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X.f))) ≫ j := by
      ext
      rw [P_left, Over.comp_left, P_left]
      exact pullback.lift_fst _ _ _
    have h2 : P A.J (u ≫ eK) = (Over.homMk ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X.f)).hom :
          (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
              (Over.mk X.f)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫ e := by
      ext
      rw [P_left, Over.comp_left, Over.comp_left, Category.assoc]
      exact congrArg (u.left ≫ ·) (pullback.lift_fst _ _ _)
    rw [h1, h2]
    exact hrel
  have hψτ : ∀ ψ : Over.mk X₀.f ⟶ JK, ψ ≫ τ = ψ * (u ≫ eK ^ (genus X.f - 1))⁻¹ := by
    intro ψ
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc,
      Over.mkIdTerminal.hom_ext (ψ ≫ Over.homMk JK.hom (Category.comp_id _)) u]
  have hinv : jK ≫ (ι[JK]).left = (jK'⁻¹).left := by rw [Hom.inv_def]; rfl
  have hgrp₁ : jK ≫ (ι[JK]).left ≫
      (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.J T)
        (CartesianMonoidalCategory.snd A.J T ≫ b) ≫ μ[A.J]).left =
      ((u ≫ (eK * bK * eK ^ (genus X.f - 1))) * j₀⁻¹).left ≫ τ.left ≫
        pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have htb : (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A.J T)
        (CartesianMonoidalCategory.snd A.J T ≫ b) ≫ μ[A.J]).left =
        (𝟙 JK * (uJ ≫ bK)).left ≫
          pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
      rw [← P_left, ← pEquiv_apply, map_mul, pEquiv_apply, pEquiv_apply, Hom.mul_def,
        Over.comp_left, Over.comp_left]
      congr 1
      apply pullback.hom_ext
      · simp only [Over.lift_left, P_left]
        erw [pullback.lift_fst, pullback.lift_fst]
        exact (Category.id_comp _).symm
      · simp only [Over.lift_left, P_left]
        erw [pullback.lift_snd, pullback.lift_snd]
        change _ = pullback.snd _ _ ≫ pullback.lift b.left (𝟙 _) _ ≫ pullback.fst _ _
        rw [pullback.lift_fst]
        rfl
    have key1 : jK'⁻¹ ≫ (𝟙 JK * (uJ ≫ bK)) =
        ((u ≫ (eK * bK * eK ^ (genus X.f - 1))) * j₀⁻¹) ≫ τ := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        Over.mkIdTerminal.hom_ext (jK'⁻¹ ≫ uJ) u, hψτ, hjK', MonObj.comp_mul, MonObj.comp_mul,
        MonObj.comp_pow]
      exact inv_mul_inv_mul_eq _ _ _ _
    rw [htb, ← Category.assoc, hinv, ← Over.comp_left_assoc, key1, Over.comp_left,
      Category.assoc]
  have hgrp₂ : jK ≫ (ι[JK]).left ≫ (CartesianMonoidalCategory.fst A.J T).left =
      ((u ≫ eK ^ genus X.f) * j₀⁻¹).left ≫ τ.left ≫
        pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have key2 : jK'⁻¹ = ((u ≫ eK ^ genus X.f) * j₀⁻¹) ≫ τ := by
      rw [hψτ, hjK', MonObj.comp_pow, MonObj.comp_pow]
      exact inv_mul_inv_eq _ _ hg
    rw [← Category.assoc, hinv, key2, Over.comp_left, Category.assoc]
    rfl
  /- `j_K^* φ_θ(b) = [D₂] - [D₁]`, by the oddness of `Pic⁰`. -/
  have hodd := schemePullbackClassHom_inv_of_mem_picZero K JK
    (AbelianVariety.phiMap_mem_picZero A.J (Stacks.Divisors.picardClass D) b)
  have hz : z = (w₂ : Stacks.Picard.smallOfScheme (bc X.f T)) - w₁ := by
    apply (smallEquiv (bc X.f T)).injective
    rw [map_sub]
    simp only [z, AddEquiv.apply_symm_apply]
    rw [← neg_neg (AbelianVariety.phiMap A.J (Stacks.Divisors.picardClass D) b), ← hodd]
    change Stacks.Picard.schemePullbackClassHom jK (-(Stacks.Picard.schemePullbackClassHom
      (ι[JK]).left (Stacks.Picard.schemePullbackClass _ (Stacks.Divisors.picardClass D) -
        Stacks.Picard.schemePullbackClass _ (Stacks.Divisors.picardClass D)))) = _
    rw [map_neg, map_sub, map_sub]
    change -((Stacks.Picard.schemePullbackClass jK (Stacks.Picard.schemePullbackClass (ι[JK]).left
        (Stacks.Picard.schemePullbackClass _ (Stacks.Divisors.picardClass D)))) -
      Stacks.Picard.schemePullbackClass jK (Stacks.Picard.schemePullbackClass (ι[JK]).left
        (Stacks.Picard.schemePullbackClass _ (Stacks.Divisors.picardClass D)))) = _
    rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
      Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
      Category.assoc, Category.assoc, hgrp₁, hgrp₂, hcl₁, hcl₂]
    abel
  have hdeg : degree X.f hdim T z = 0 := by
    rw [hz, map_sub, AddMonoidHom.mem_ker.1 w₁.2, AddMonoidHom.mem_ker.1 w₂.2, sub_zero]
  refine ⟨hdeg, ?_⟩
  have hw : (⟨z, hdeg⟩ : (degree X.f hdim T).ker) = w₂ - w₁ := Subtype.ext hz
  have hb : Φ bK = b := by
    ext
    rw [hΦ]
    exact pullback.lift_fst _ _ _
  rw [hw, QuotientAddGroup.mk_sub]
  refine (A.ι_app_sub T _ _).trans ?_
  rw [hw₁, hw₂, ← map_inv, ← map_mul, ← hb, ← map_inv]
  exact congrArg Φ (pow_mul_inv_mul_pow_pred eK bK hg)

end

end Faltings
