module
public import Mordell.Curve.PointClass
public import Mordell.Jacobian.PicZeroRigidified
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints

/-!
# The Abel–Jacobi map

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, with structure
morphism `f : C ⟶ Spec k`, and let `(J, ι)` be a Jacobian of `C`, so that
`ι : P⁰_C ⟶ J(-)` is a morphism from the relative Picard functor of degree zero to the functor
of points of `J`. The *Abel–Jacobi map* attached to `P` is the `k`-morphism `j = j_P : C ⟶ J`
such that, for every field `K ⊇ k` and every `Q ∈ C(K)`,
`j_P(Q) = ι(Spec K)(cl(Q - P_K)) ∈ J(K)`, where `cl(Q - P_K) ∈ P⁰_C(Spec K)` is the class of
the degree-zero divisor `Q - P_K` on `C_K = C ×_k Spec K`.

## Main definitions

* `Faltings.IsAbelJacobiMap X A j`: the `k`-morphism `j : C ⟶ J` is the Abel–Jacobi map of the
  curve with degree-one divisor `X = (C, P)` and the Jacobian `A = (J, ι)`.

## Implementation notes

The definition is the characterising property of `j_P`, a predicate on `k`-morphisms
`C ⟶ J`; that exactly one `k`-morphism satisfies it is a separate result.

A field `K ⊇ k` is a `k`-algebra `K` which is a field, and `Spec K` is the `k`-scheme
`Spec K ⟶ Spec k`. A point `Q ∈ C(K)` is a `k`-morphism `Spec K ⟶ C`, and `j_P(Q)` is the
composite `Q ≫ j`. The point `Q` determines the section `(Q, id) : Spec K ⟶ C_K` of the
projection `C_K ⟶ Spec K`; its image is the divisor `Q` on `C_K`, the kernel of the section,
an effective Cartier divisor since `C_K ⟶ Spec K` is separated and smooth of relative
dimension one. The divisor `P = ∑ nₓ x` has the class `∑ nₓ [𝒪_C(x)]` in `Pic(C)`, each closed
point of the smooth curve `C` being an effective Cartier divisor, and `P_K` is its pull-back to
`C_K`, so that `[𝒪(P_K)]` is the pull-back of `[𝒪_C(P)]` along the projection `C_K ⟶ C`.
Hence `cl(Q - P_K) = [𝒪(Q)] - pr₁^*[𝒪_C(P)]` in `Pic(C_K)`.

An element of `P⁰_C(Spec K)` is the class of a Picard class of `C_K` of degree zero on every
fibre of `C_K ⟶ Spec K` (`Stacks.RigidifiedPicard.degree`). That `Q - P_K` has degree zero
is a property of the divisor, not part of its definition; the condition is therefore stated
for every proof of it, which is to say whenever it holds, and it always does.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 2.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.RigidifiedPicard

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **The Abel–Jacobi map.** For a curve `X = (C, P)` over `k` with a divisor `P` of degree
one and a Jacobian `A = (J, ι)` of `C`, a `k`-morphism `j : C ⟶ J` is *the Abel–Jacobi map
`j_P`* when, for every field `K ⊇ k` and every `Q ∈ C(K)`,
`j_P(Q) = ι(Spec K)(cl(Q - P_K))`. Here `cl(Q - P_K) ∈ P⁰_C(Spec K)` is the class of
`[𝒪(Q)] - pr₁^*[𝒪_C(P)] ∈ Pic(C_K)`, where `𝒪(Q)` is the divisor of the section
`(Q, id) : Spec K ⟶ C_K` and `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` for `P = ∑ nₓ x`. -/
@[expose, faltings "def_nt_abel_jacobi"]
public def IsAbelJacobiMap (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (j : Over.mk X.f ⟶ A.J) : Prop :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
  /- The class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`. -/
  let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
    haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
  ∀ (K : Type u) [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f),
    let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    haveI : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback X.f T.hom) inferInstance
    /- The point `Q` as a section `(Q, id)` of `C_K ⟶ Spec K`. -/
    let E : ModuliEllipticCurves.PointedFamily T.left :=
      ⟨bc X.f T, bcProj X.f T, pullback.lift Q.left (𝟙 T.left) (Over.w Q),
        pullback.lift_snd _ _ _⟩
    haveI : IsSeparated E.map := inferInstanceAs (IsSeparated (bcProj X.f T))
    haveI : SmoothOfRelativeDimension 1 E.map := ‹SmoothOfRelativeDimension 1 (bcProj X.f T)›
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor E.zeroDivisor :=
      E.isEffectiveCartierDivisor_zeroDivisor
    /- `[𝒪(Q)] - [𝒪(P_K)]` in `Pic(C_K)`, in the small model of the Picard group. -/
    let z : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Divisors.picardClass E.zeroDivisor -
        Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP)
    ∀ hdeg : degree X.f hdim T z = 0,
      Q ≫ j = A.ι.app (op T)
        (show (relativePicZeroFunctor k X.f).obj (op T) from
          QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T).ker))

end Faltings


/-!
# Existence and uniqueness of the Abel–Jacobi map

Let `(C, P)` be a curve over a field `k` with a rational divisor `P` of degree one, and let
`(J, ι)` be a Jacobian of `C`. There is exactly one `k`-morphism `j : C ⟶ J` such that
`j(Q) = ι(Spec K)(cl(Q - P_K))` for every field `K ⊇ k` and every `Q ∈ C(K)`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.abelJacobiClass`: for a point `Q ∈ C(T)`, the class
  `cl(Q - P_T) = [𝒪(Q)] - pr₁^*[𝒪_C(P)] ∈ Pic(C_T)`, with `[𝒪_C(P)]` the class
  `Faltings.CurveWithDegreeOneDivisor.classP`.
* `Faltings.CurveWithDegreeOneDivisor.pointClass`: over a field `K ⊇ k`, the class
  `cl(Q - P_K) ∈ P⁰_C(Spec K)` of a point `Q ∈ C(K)`.
* `Faltings.CurveWithDegreeOneDivisor.univClass`: the universal class
  `𝓛_P = cl(Δ - pr₁^*P) ∈ P⁰_C(C)`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.degree_abelJacobiClass_field`: over a field `K ⊇ k`,
  `cl(Q - P_K)` has degree zero.
* `Faltings.CurveWithDegreeOneDivisor.abelJacobiClass_pullback`: `cl(Q - P_T)` is natural
  in `T`.
* `Faltings.CurveWithDegreeOneDivisor.degree_abelJacobiClass_id`: `𝓛_P` has degree zero.
* `Faltings.IsAbelJacobiMap.comp_eq`: an Abel–Jacobi map sends `Q ∈ C(K)` to
  `ι(Spec K)(cl(Q - P_K))`.
* `Faltings.existsUnique_isAbelJacobiMap`: there is exactly one `k`-morphism `C ⟶ J`
  satisfying `Faltings.IsAbelJacobiMap`.
* `Faltings.IsAbelJacobiMap.eq_ι_app_univClass`: the Abel–Jacobi map is `ι(C)(𝓛_P)`.

## Implementation notes

For a `k`-scheme `T` and a point `Q ∈ C(T)`, the section `(Q, id)` of `C_T ⟶ T` cuts out an
effective Cartier divisor on `C_T`, and `𝓛_Q = [𝒪(Q)] - pr₁^*[𝒪_C(P)] ∈ Pic(C_T)`. For `T = C`
and `Q = id` this is `𝓛_P = 𝒪_{C×C}(Δ) ⊗ p^*𝒪_C(-P)`. The class is natural in `T`, since the
section `(g ≫ Q, id)` is the base change of `(Q, id)`, and over a field it has degree
`1 - 1 = 0`; so `𝓛_P` lies in `P⁰_C(C)`. Existence takes `j = ι(C)(𝓛_P)`, using that `ι` is a
morphism of functors. Uniqueness: two Abel–Jacobi maps agree on every point `Spec κ(x) ⟶ C`,
and `C` is reduced and `J` separated over `k`, so they are equal.

The diagonal of `C × C` appears as the zero divisor of the family `C × C ⟶ C` pointed by
`(id, id)`, so the effective Cartier property and the base-change compatibility both come from
the pointed-family API.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 2.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.RigidifiedPicard

namespace Faltings

variable {k : Type u} [Field k]

namespace CurveWithDegreeOneDivisor

/-- The base change `C_T ⟶ T` of the curve is smooth of relative dimension one. -/
public lemma smoothOfRelativeDimension_bcProj (X : CurveWithDegreeOneDivisor k)
    (T : Over (Spec (.of k))) : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback X.f T.hom) inferInstance

/-- The family `C_T ⟶ T` pointed by the section `(Q, id)` of a point `Q ∈ C(T)`. -/
@[expose] public noncomputable abbrev pointFamily (X : CurveWithDegreeOneDivisor k)
    {T : Over (Spec (.of k))} (Q : T ⟶ Over.mk X.f) : ModuliEllipticCurves.PointedFamily T.left :=
  ⟨bc X.f T, bcProj X.f T, pullback.lift Q.left (𝟙 T.left) (Over.w Q),
    pullback.lift_snd _ _ _⟩

/-- The image of the section `(Q, id)` of `C_T ⟶ T` is an effective Cartier divisor. -/
public lemma isEffectiveCartierDivisor_pointFamily (X : CurveWithDegreeOneDivisor k)
    {T : Over (Spec (.of k))} (Q : T ⟶ Over.mk X.f) :
    Stacks.Divisors.IsEffectiveCartierDivisor (X.pointFamily Q).zeroDivisor :=
  haveI : IsSeparated (X.pointFamily Q).map := inferInstanceAs (IsSeparated (bcProj X.f T))
  haveI : SmoothOfRelativeDimension 1 (X.pointFamily Q).map := X.smoothOfRelativeDimension_bcProj T
  (X.pointFamily Q).isEffectiveCartierDivisor_zeroDivisor

/-- The class `cl(Q - P_T) = [𝒪(Q)] - pr₁^*[𝒪_C(P)]` in `Pic(C_T)` of a point `Q ∈ C(T)`. -/
@[expose] public noncomputable def abelJacobiClass (X : CurveWithDegreeOneDivisor k) {T : Over (Spec (.of k))}
    (Q : T ⟶ Over.mk X.f) : Stacks.Picard.ofScheme (bc X.f T) :=
  haveI := X.isEffectiveCartierDivisor_pointFamily Q
  Stacks.Divisors.picardClass (X.pointFamily Q).zeroDivisor -
    Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) X.classP

/-- `deg pr₁^*𝒪_C(P) = 1` on `C_K = C ×_k Spec K`. -/
public lemma invertibleCurveDegreeHom_schemePullbackClass_classP (X : CurveWithDegreeOneDivisor k)
    (K : Type u) [Field K] [Algebra k K]
    (hdimT : topologicalKrullDim (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      ≤ 1) :
    haveI : IsProper (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
      inferInstanceAs (IsProper (pullback.snd X.f _))
    invertibleCurveDegreeHom K
      (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) hdimT
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) X.classP) = 1 :=
  (invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
    (IsPullback.of_hasPullback X.f _) (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    hdimT X.classP).trans (X.invertibleCurveDegreeHom_classP _)

/-- Over a field `K ⊇ k`, the class `cl(Q - P_K)` of a point `Q ∈ C(K)` has degree
`1 - 1 = 0`. -/
public lemma degree_abelJacobiClass_field (X : CurveWithDegreeOneDivisor k)
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1) (K : Type u) [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    degree X.f hdim _ ((smallEquiv.{u} _).symm (X.abelJacobiClass Q)) = 0 := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let π : bc X.f T ⟶ Spec (.of K) := bcProj X.f T
  haveI : SmoothOfRelativeDimension 1 π := X.smoothOfRelativeDimension_bcProj T
  haveI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  haveI : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  haveI : GeometricallyIrreducible π :=
    MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
      (IsPullback.of_hasPullback X.f T.hom) inferInstance
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections K π
  funext t
  rw [degree_apply, AddEquiv.apply_symm_apply]
  refine (relativeInvertibleDegreeHomAt_spec π hdimT _ t _).trans ?_
  have hP : invertibleCurveDegreeHom K π hdimT
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) X.classP) = 1 :=
    X.invertibleCurveDegreeHom_schemePullbackClass_classP K hdimT
  haveI := X.isEffectiveCartierDivisor_pointFamily Q
  have hQ : invertibleCurveDegreeHom K π hdimT
      (Stacks.Divisors.picardClass (X.pointFamily Q).zeroDivisor) = 1 := by
    haveI : IsSeparated (X.pointFamily Q).map := inferInstanceAs (IsSeparated (bcProj X.f T))
    have hs : (X.pointFamily Q).zero ≫ π = 𝟙 _ := (X.pointFamily Q).zero_map
    have hv := ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_vanishingIdeal (k := K)
      (X.pointFamily Q) (IsLocalRing.closedPoint K)
    haveI := GenusOne.isEffectiveCartierDivisor π h0 (X.pointFamily Q).zero hs
    rw [Stacks.Divisors.picardClass_congr hv]
    exact invertibleCurveDegreeHom_divisorPicardClass_point K π hdimT h0
      (X.pointFamily Q).zero hs
  simp only [abelJacobiClass]
  rw [map_sub, hP, hQ]
  rfl

end CurveWithDegreeOneDivisor

open CurveWithDegreeOneDivisor

/-- An Abel–Jacobi map `j` sends a point `Q ∈ C(K)` to `ι(Spec K)(cl(Q - P_K))`. -/
public lemma IsAbelJacobiMap.comp_eq {X : CurveWithDegreeOneDivisor k} {A : Jacobian k X.f}
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1) (K : Type u) [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    Q ≫ j = A.ι.app (op _)
      (QuotientAddGroup.mk ⟨_, X.degree_abelJacobiClass_field hdim K Q⟩) :=
  hj K Q _

/-- The class `cl(Q - P_K) ∈ P⁰_C(Spec K)` of a point `Q ∈ C(K)` with values in a field
`K ⊇ k`. -/
@[expose] public noncomputable def CurveWithDegreeOneDivisor.pointClass
    (X : CurveWithDegreeOneDivisor k) {K : Type u} [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    (relativePicZeroFunctor k X.f).obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
  QuotientAddGroup.mk ⟨_, AddMonoidHom.mem_ker.2 (X.degree_abelJacobiClass_field
    (relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f) K Q)⟩

/-- An Abel–Jacobi map `j` sends a point `Q ∈ C(K)` to `ι(Spec K)(cl(Q - P_K))`. -/
public lemma IsAbelJacobiMap.comp_eq_ι_pointClass {X : CurveWithDegreeOneDivisor k}
    {A : Jacobian k X.f} {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j) {K : Type u}
    [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    Q ≫ j = A.ι.app (op _) (X.pointClass Q) :=
  hj K Q _

namespace CurveWithDegreeOneDivisor

/-- The section `(g ≫ Q, id)` of `C_T` is the base change of the section `(Q, id)` of `C_U`. -/
private lemma isPullback_pointFamily_zero (X : CurveWithDegreeOneDivisor k)
    {T U : Over (Spec (.of k))} (g : T ⟶ U) (Q : U ⟶ Over.mk X.f) :
    IsPullback (X.pointFamily (g ≫ Q)).zero g.left (bcMap X.f g) (X.pointFamily Q).zero := by
  refine IsPullback.of_right (h₁₂ := bcProj X.f T) (h₂₂ := bcProj X.f U) ?_ ?_
    (bcMap_isPullback_proj X.f g).flip
  · rw [(X.pointFamily (g ≫ Q)).zero_map, (X.pointFamily Q).zero_map]
    exact IsPullback.id_horiz g.left
  · apply pullback.hom_ext
    · simp only [pointFamily, bcMap, Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
      rfl
    · simp only [pointFamily, bcMap, Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
      simp

private lemma comap_pointFamily_zeroDivisor (X : CurveWithDegreeOneDivisor k)
    {T U : Over (Spec (.of k))} (g : T ⟶ U) (Q : U ⟶ Over.mk X.f) :
    (X.pointFamily Q).zeroDivisor.comap (bcMap X.f g) = (X.pointFamily (g ≫ Q)).zeroDivisor := by
  haveI : IsSeparated (X.pointFamily Q).map := inferInstanceAs (IsSeparated (bcProj X.f U))
  haveI : IsClosedImmersion (X.pointFamily Q).zero := (X.pointFamily Q).isClosedImmersion_zero
  rw [ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_ker,
    ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_ker,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_pointFamily_zero X g Q).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Naturality of `cl(Q - P_T)`: its pull-back along `C_T ⟶ C_U` over `g : T ⟶ U` is
`cl(g^*Q - P_T)`. -/
public lemma abelJacobiClass_pullback (X : CurveWithDegreeOneDivisor k)
    {T U : Over (Spec (.of k))} (g : T ⟶ U) (Q : U ⟶ Over.mk X.f) :
    Stacks.Picard.schemePullbackClass (bcMap X.f g) (X.abelJacobiClass Q) =
      X.abelJacobiClass (g ≫ Q) := by
  haveI := X.isEffectiveCartierDivisor_pointFamily Q
  haveI := X.isEffectiveCartierDivisor_pointFamily (g ≫ Q)
  have hcomap := comap_pointFamily_zeroDivisor X g Q
  have hD : Stacks.Divisors.IsPullbackDefined (bcMap X.f g) (X.pointFamily Q).zeroDivisor := by
    change Stacks.Divisors.IsEffectiveCartierDivisor _
    rw [hcomap]
    infer_instance
  simp only [abelJacobiClass]
  rw [schemePullbackClass_sub',
    Stacks.Zeta.schemePullbackClass_picardClass_comap _ _ hD,
    Stacks.Divisors.picardClass_congr hcomap,
    Stacks.Picard.schemePullbackClass_comp, bcMap_fst]

/-- The universal class `𝓛_P = cl(Δ - pr₁^*P)` on `C × C` pulls back along `Q ∈ C(T)` to
`cl(Q - P_T)`. -/
public lemma smallSchemePullbackClassHom_abelJacobiClass (X : CurveWithDegreeOneDivisor k)
    {T : Over (Spec (.of k))} (Q : T ⟶ Over.mk X.f) :
    Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f Q)
        ((smallEquiv.{u} _).symm (X.abelJacobiClass (𝟙 (Over.mk X.f)))) =
      (smallEquiv.{u} _).symm (X.abelJacobiClass Q) := by
  apply (smallEquiv.{u} _).injective
  rw [smallEquiv_smallSchemePullbackClassHom, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, abelJacobiClass_pullback, Category.comp_id]

/-- The point `Spec κ(x) ⟶ C` of a point `x` of `C`, as a point with values in a field. -/
private noncomputable def residuePoint (X : CurveWithDegreeOneDivisor k) (x : X.C) :
    letI := overResidueFieldAlgebra (Over.mk X.f) x
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k ((Over.mk X.f).left.residueField x)))) ⟶
      Over.mk X.f :=
  letI := overResidueFieldAlgebra (Over.mk X.f) x
  Over.homMk ((Over.mk X.f).left.fromSpecResidueField x)
    (spec_map_algebraMap_overResidueFieldAlgebra (Over.mk X.f) x).symm

private lemma residuePoint_left_apply (X : CurveWithDegreeOneDivisor k) (x : X.C)
    (p : Spec ((Over.mk X.f).left.residueField x)) : (residuePoint X x).left p = x :=
  Scheme.fromSpecResidueField_apply x p

/-- The universal class `𝓛_P = cl(Δ - pr₁^*P)` on `C × C` has degree zero: its fibre over a
point `x` of `C` is `cl(x - P_{κ(x)})`. -/
public lemma degree_abelJacobiClass_id (X : CurveWithDegreeOneDivisor k)
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1) :
    degree X.f hdim (Over.mk X.f)
      ((smallEquiv.{u} _).symm (X.abelJacobiClass (𝟙 (Over.mk X.f)))) = 0 := by
  funext x
  letI := overResidueFieldAlgebra (Over.mk X.f) x
  have h := degree_smallSchemePullbackClassHom_bcMap X.f hdim (residuePoint X x)
    ((smallEquiv.{u} _).symm (X.abelJacobiClass (𝟙 _)))
  rw [smallSchemePullbackClassHom_abelJacobiClass, degree_abelJacobiClass_field] at h
  rw [← residuePoint_left_apply X x (IsLocalRing.closedPoint _)]
  exact (congrFun h _).symm

/-- The universal class `𝓛_P = cl(Δ - pr₁^*P) ∈ P⁰_C(C)`. -/
@[expose] public noncomputable def univClass (X : CurveWithDegreeOneDivisor k) :
    (relativePicZeroFunctor k X.f).obj (op (Over.mk X.f)) :=
  QuotientAddGroup.mk ⟨_, X.degree_abelJacobiClass_id fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)⟩

/-- `ι(C)(𝓛_P)` sends a point `Q ∈ C(K)` to `ι(K)(𝓛_Q)`: naturality of `ι`, since `𝓛_P` pulls
back to `𝓛_Q` along `Q`. -/
public lemma comp_ι_app_univClass (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1) (K : Type u) [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    Q ≫ A.ι.app (op (Over.mk X.f)) X.univClass =
      A.ι.app (op _) (QuotientAddGroup.mk ⟨_, X.degree_abelJacobiClass_field hdim K Q⟩) := by
  have h := ConcreteCategory.congr_hom (A.ι.naturality Q.op) X.univClass
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h.symm.trans (congrArg (A.ι.app (op _)) (congrArg (QuotientAddGroup.mk' _)
    (Subtype.ext (X.smallSchemePullbackClassHom_abelJacobiClass Q))))

end CurveWithDegreeOneDivisor

/-- **Existence and uniqueness of the Abel–Jacobi map.** For a curve `X = (C, P)` over `k`
with a divisor of degree one and a Jacobian `A = (J, ι)` of `C`, there is exactly one
`k`-morphism `j : C ⟶ J` with `Faltings.IsAbelJacobiMap X A j`. -/
@[faltings "lem_nt_abel_jacobi_exists"]
public theorem existsUnique_isAbelJacobiMap (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) :
    ∃! j : Over.mk X.f ⟶ A.J, IsAbelJacobiMap X A j := by
  have hdim := relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f
  refine ⟨A.ι.app (op (Over.mk X.f)) X.univClass, ?_, fun j hj => ?_⟩
  · intro K _ _ Q T E z hdeg
    exact X.comp_ι_app_univClass A hdim K Q
  haveI : IsSeparated A.J.hom := by
    haveI := A.isAbelianVariety
    infer_instance
  refine Over.OverMorphism.ext (ext_of_fromSpecResidueField_eq j.left _ A.J.hom Set.univ
    dense_univ (fun x _ => ?_) (by rw [Over.w j, Over.w]))
  letI := overResidueFieldAlgebra (Over.mk X.f) x
  exact congrArg Over.Hom.left
    ((hj.comp_eq hdim _ (residuePoint X x)).trans
    (X.comp_ι_app_univClass A hdim _ (residuePoint X x)).symm)

/-- An Abel–Jacobi map is `ι(C)` of the universal class: `j = ι(C)(cl(Δ - pr₁^*P))`. -/
public lemma IsAbelJacobiMap.eq_ι_app_univClass {X : CurveWithDegreeOneDivisor k} {A : Jacobian k X.f}
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j) :
    j = A.ι.app (op (Over.mk X.f)) X.univClass :=
  (existsUnique_isAbelJacobiMap X A).unique hj fun K _ _ Q => by
    intros
    exact X.comp_ι_app_univClass A
      (relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f) K Q

end Faltings
