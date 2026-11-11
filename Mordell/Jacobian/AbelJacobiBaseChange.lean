module
public import Mordell.Jacobian.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints

/-!
# Changing the base divisor of the Abel–Jacobi map

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, `(J, ι)` a Jacobian
of `C` and `j_P : C ⟶ J` the Abel–Jacobi map. Let `K ⊇ k` be a field and `P₀` a divisor of
degree one on `C_K = C ×_k Spec K`, and let `j_{P₀} : C_K ⟶ J_K` be the Abel–Jacobi map of
`(C_K, P₀)`, so that `j_{P₀}(Q) = ι(cl(Q - P₀))` for every field `L ⊇ K` and `Q ∈ C_K(L)`.
Put `e = ι(Spec K)(cl(P_K - P₀)) ∈ J(K)`. Then `j_P = τ_{-e} ∘ j_{P₀}` over `K`, that is,
`j_P(Q) = j_{P₀}(Q) - e` on `C_K`.

## Main results

* `Faltings.IsAbelJacobiMap.comp_fst_eq_mul_inv`: the base change of `j_P` to `C_K` is
  `j_{P₀} - e`.

## Implementation notes

A `K`-morphism `C_K ⟶ J_K = J ×_k Spec K` is the same as a `k`-morphism `C_K ⟶ J`, and this
is how `j_{P₀}` is given: a morphism `C_K ⟶ J` in `Over (Spec k)`, where `C_K` is the
fibre product `pullback X.f (Spec K ⟶ Spec k)` regarded as a `k`-scheme. The base change of
`j_P` is then `pr₁ ≫ j_P` with `pr₁ : C_K ⟶ C` the projection, and `τ_{-e} ∘ j_{P₀}` is the
difference `j_{P₀} - pr₂ ≫ e` in the group of `k`-morphisms `C_K ⟶ J`, with
`pr₂ : C_K ⟶ Spec K`; the group law of `J` is written multiplicatively, as for group objects.

The morphism `ι` is assumed to respect the group laws: `ι(T)` is a homomorphism from
`P⁰_C(T)` to the group `J(T)` of `T`-points, for every `k`-scheme `T`, as in [MilAV] III §1,
where `ι` is a morphism of group-valued functors.

The morphism `j_{P₀}` is characterised as in `Faltings.IsAbelJacobiMap`, with `ι_K` the
restriction of `ι` to `K`-schemes: for every field `L ⊇ K` and every `Q ∈ C_K(L)`, the point
`j_{P₀}(Q) ∈ J(L)` is `ι(Spec L)` of the class `[𝒪(Q)] - [𝒪(P₀,L)]` on
`C_L = C ×_k Spec L`, where `𝒪(Q)` is the divisor of the section of `C_L ⟶ Spec L` given by
`Q` and `[𝒪(P₀,L)]` the pull-back of `[𝒪(P₀)] = ∑ nₓ [𝒪(x)]` along `C_L ⟶ C_K`. The divisor
`P_K` enters only through its class, the pull-back of `[𝒪_C(P)]` along `C_K ⟶ C`. As in
`Faltings.IsAbelJacobiMap`, the conditions are stated for every proof that the classes have
degree zero.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 2.
* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.RigidifiedPicard
open scoped CategoryTheory.MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **Changing the base divisor of the Abel–Jacobi map.** Let `X = (C, P)` be a curve over `k`
with a divisor of degree one, `A = (J, ι)` a Jacobian of `C` with `ι` additive and `j = j_P` its
Abel–Jacobi map.
Let `K ⊇ k` be a field, `P₀` a divisor of degree one on `C_K = C ×_k Spec K`, and
`j₀ : C_K ⟶ J` the Abel–Jacobi map of `(C_K, P₀)`: for every field `L ⊇ K` and `Q ∈ C_K(L)`,
`j₀(Q) = ι(Spec L)([𝒪(Q)] - [𝒪(P₀,L)])`. If `e = ι(Spec K)(cl(P_K - P₀)) ∈ J(K)`, then
`j_P = τ_{-e} ∘ j₀` over `K`: `pr₁ ≫ j = j₀ * (pr₂ ≫ e)⁻¹`. -/
@[faltings "lem_nt_abel_jacobi_basic"]
public theorem IsAbelJacobiMap.comp_fst_eq_mul_inv (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f)
    (hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y))
    {j : Over.mk X.f ⟶ A.J} (hj : IsAbelJacobiMap X A j)
    (K : Type u) [Field K] [Algebra k K]
    (P₀ : {x : bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) //
      IsClosed ({x} : Set _)} →₀ ℤ)
    (hP₀ : (P₀.sum fun x n =>
      n * ((bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))).residueDegree
        x.1 : ℤ)) = 1) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    /- `C_K` as a `k`-scheme, with its projections to `C` and to `Spec K`. -/
    let CK : Over (Spec (.of k)) := Over.mk (bcProj X.f T ≫ T.hom)
    let pr₁ : CK ⟶ Over.mk X.f := Over.homMk (pullback.fst X.f T.hom) pullback.condition
    let pr₂ : CK ⟶ T := Over.homMk (bcProj X.f T) rfl
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
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (bcProj X.f T) x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    /- `cl(P_K - P₀)` in `Pic(C_K)`, in the small model of the Picard group. -/
    let zₑ : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv (bc X.f T)).symm
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀)
    ∀ (j₀ : CK ⟶ A.J) (e : T ⟶ A.J),
    (∀ (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ Over.mk (bcProj X.f T)),
      let T' : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      have hL : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ T.hom = T'.hom := by
        simp only [T, T', Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]
      /- `Spec L ⟶ Spec K` as a morphism of `k`-schemes. -/
      let g : T' ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K L))) hL
      /- `Q` as a `k`-point of `C_K`, and its image in `C(L)`. -/
      let Qk : T' ⟶ CK := Over.homMk Q.left (by
        have hQ := Over.w Q
        simp only [Over.mk_hom] at hQ
        simp only [CK, Over.mk_hom, ← Category.assoc, hQ]
        exact hL)
      haveI : SmoothOfRelativeDimension 1 (bcProj X.f T') :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback X.f T'.hom) inferInstance
      /- The point `Qk ≫ pr₁ ∈ C(L)` as a section of `C_L ⟶ Spec L`. -/
      let E : ModuliEllipticCurves.PointedFamily T'.left :=
        ⟨bc X.f T', bcProj X.f T', pullback.lift (Qk ≫ pr₁).left (𝟙 T'.left) (Over.w (Qk ≫ pr₁)),
          pullback.lift_snd _ _ _⟩
      haveI : IsSeparated E.map := inferInstanceAs (IsSeparated (bcProj X.f T'))
      haveI : SmoothOfRelativeDimension 1 E.map :=
        ‹SmoothOfRelativeDimension 1 (bcProj X.f T')›
      haveI : Stacks.Divisors.IsEffectiveCartierDivisor E.zeroDivisor :=
        E.isEffectiveCartierDivisor_zeroDivisor
      /- `[𝒪(Q)] - [𝒪(P₀,L)]` in `Pic(C_L)`. -/
      let z : Stacks.Picard.smallOfScheme (bc X.f T') := (smallEquiv (bc X.f T')).symm
        (Stacks.Divisors.picardClass E.zeroDivisor -
          Stacks.Picard.schemePullbackClass (bcMap X.f g) classP₀)
      ∀ hdeg : degree X.f hdim T' z = 0,
        Qk ≫ j₀ = A.ι.app (op T')
          (show (relativePicZeroFunctor k X.f).obj (op T') from
            QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T').ker))) →
    (∀ hdeg : degree X.f hdim T zₑ = 0,
      e = A.ι.app (op T)
        (show (relativePicZeroFunctor k X.f).obj (op T) from
          QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker))) →
    pr₁ ≫ j = j₀ * (pr₂ ≫ e)⁻¹ := by
  intro hdim T CK pr₁ pr₂ classP classP₀ zₑ j₀ e hj₀ he
  let π : bc X.f T ⟶ Spec (.of K) := bcProj X.f T
  have : SmoothOfRelativeDimension 1 π := X.smoothOfRelativeDimension_bcProj T
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have : IsCurve K π := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one π
  have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension π
  have hdegₑ : degree X.f hdim T zₑ = 0 := by
    funext t
    rw [degree_apply, AddEquiv.apply_symm_apply]
    refine (relativeInvertibleDegreeHomAt_spec π hdimT _ t _).trans ?_
    have hP : invertibleCurveDegreeHom K π hdimT
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP) = 1 :=
      (invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
        (IsPullback.of_hasPullback X.f T.hom)
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f) hdimT classP).trans
          (X.invertibleCurveDegreeHom_classP _)
    rw [map_sub, hP, degree_divisorClass π hdimT, hP₀]
    rfl
  have : IsReduced CK.left := isReduced_of_smooth π
  have : IsSeparated A.J.hom := by
    have := A.isAbelianVariety
    infer_instance
  refine Over.OverMorphism.ext (ext_of_fromSpecResidueField_eq _ _ A.J.hom Set.univ
    dense_univ (fun x _ => ?_) ?_)
  swap
  · rw [Over.w, Over.w]
  let L := CK.left.residueField x
  let : Algebra K L :=
    (Spec.preimage (CK.left.fromSpecResidueField x ≫ π)).hom.toAlgebra
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hQ : CK.left.fromSpecResidueField x ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    change _ = Spec.map (CommRingCat.ofHom
      (Spec.preimage (CK.left.fromSpecResidueField x ≫ π)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ Over.mk π :=
    Over.homMk (CK.left.fromSpecResidueField x) hQ
  let T' : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  have hL : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ T.hom = T'.hom := by
    simp only [T, T', Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let g : T' ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K L))) hL
  let Qk : T' ⟶ CK := Over.homMk (CK.left.fromSpecResidueField x) (by
    simp only [CK, T', Over.mk_hom, ← Category.assoc]
    erw [hQ]
    exact hL)
  let R : T' ⟶ Over.mk X.f := Qk ≫ pr₁
  have := X.isEffectiveCartierDivisor_pointFamily R
  let z₀ : Stacks.Picard.smallOfScheme (bc X.f T') := (smallEquiv.{u} _).symm
    (Stacks.Divisors.picardClass (X.pointFamily R).zeroDivisor -
      Stacks.Picard.schemePullbackClass (bcMap X.f g) classP₀)
  have h0 : ∀ hdeg : degree X.f hdim T' z₀ = 0, Qk ≫ j₀ = A.ι.app (op T')
      (QuotientAddGroup.mk (⟨z₀, hdeg⟩ : (degree X.f hdim T').ker)) := hj₀ L Q
  let zj : Stacks.Picard.smallOfScheme (bc X.f T') :=
    (smallEquiv.{u} _).symm (X.abelJacobiClass R)
  have hdegj : degree X.f hdim T' zj = 0 := X.degree_abelJacobiClass_field hdim L R
  have h1 : R ≫ j = A.ι.app (op T')
      (QuotientAddGroup.mk (⟨zj, hdegj⟩ : (degree X.f hdim T').ker)) := hj L R hdegj
  let zₑ' := Stacks.Picard.smallSchemePullbackClassHom (bcMap X.f g) zₑ
  have hdegₑ' : degree X.f hdim T' zₑ' = 0 := by
    rw [degree_smallSchemePullbackClassHom_bcMap, hdegₑ]
    rfl
  have hadd : zj + zₑ' = z₀ := by
    apply (smallEquiv.{u} _).injective
    rw [map_add, smallEquiv_smallSchemePullbackClassHom]
    simp only [zj, z₀, zₑ, AddEquiv.apply_symm_apply, CurveWithDegreeOneDivisor.abelJacobiClass,
      schemePullbackClass_sub',
      Stacks.Picard.schemePullbackClass_comp, bcMap_fst]
    exact sub_add_sub_cancel _ _ _
  have hdeg₀ : degree X.f hdim T' z₀ = 0 := by
    rw [← hadd, map_add, hdegj, hdegₑ', add_zero]
  have he' : g ≫ e = A.ι.app (op T')
      (QuotientAddGroup.mk (⟨zₑ', hdegₑ'⟩ : (degree X.f hdim T').ker)) := by
    rw [he hdegₑ]
    exact (ConcreteCategory.congr_hom (A.ι.naturality g.op)
      (QuotientAddGroup.mk (⟨zₑ, hdegₑ⟩ : (degree X.f hdim T).ker))).symm
  have hQk : Qk ≫ pr₂ = g := by
    ext
    exact hQ
  have hmain : Qk ≫ (pr₁ ≫ j) = Qk ≫ (j₀ * (pr₂ ≫ e)⁻¹) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc Qk pr₂ e, hQk, he', h0 hdeg₀,
      ← Category.assoc]
    change R ≫ j = _
    rw [h1, eq_mul_inv_iff_mul_eq]
    refine (hι T' _ _).symm.trans (congrArg _ ?_)
    exact (QuotientAddGroup.mk_add _ _ _).symm.trans
      (congrArg QuotientAddGroup.mk (Subtype.ext hadd))
  exact congrArg Over.Hom.left hmain

end Faltings
