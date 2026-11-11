module
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Jacobian.PicZeroRigidified
public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions

/-!
# The dimension of a Jacobian

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor of degree one, and let
`(J, ι)` be a Jacobian of `C`. Then `dim J = g`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.nonempty_algebraicClosure_point`: `C` has a `k̄`-point.
* `Faltings.Jacobian.topologicalKrullDim_eq_genus`: `dim J = g`.

## Implementation notes

Over `K = k̄` the curve has a rational point `σ`. Through `ι` and the adjunction between
`K`-schemes and `k`-schemes, the base change `J_K` represents `P⁰_C` restricted to `K`-schemes,
which is the `Pic⁰` of `C_K` rigidified along `σ`
(`Faltings.relativePicZeroFunctor.rigidifiedIso`). The degree-zero component of the Picard scheme
of `C_K` represents the same functor and is smooth of relative dimension `g`, so the two are
isomorphic, and `dim J = dim J_K = g`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace Faltings

/-- **A curve has a point over the algebraic closure** of its base field. -/
public lemma CurveWithDegreeOneDivisor.nonempty_algebraicClosure_point {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) :
    Nonempty (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶
      Over.mk X.f) := by
  have : CompactSpace X.C := (quasiCompact_iff_compactSpace X.f).1 inferInstance
  have : Nonempty X.C := inferInstance
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X.C) isClosed_univ
    ⟨this.some, trivial⟩
  obtain ⟨b, hb, -⟩ := exists_algebraicClosure_point_of_isClosed X.f x hx
  exact ⟨Over.homMk b hb⟩

section Psi

variable {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
  (K : Type u) [Field K] [Algebra k K]

/-- `Spec K ⟶ Spec k`. -/
private noncomputable abbrev specMapK : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The base change `J_K`. -/
private noncomputable abbrev JK (J : Over (Spec (.of k))) : Over (Spec (.of K)) :=
  (Over.pullback (specMapK (k := k) K)).obj J

/-- A `K`-scheme as a `k`-scheme. -/
private noncomputable abbrev toK (U : Over (Spec (.of K))) : Over (Spec (.of k)) :=
  (Over.map (specMapK (k := k) K)).obj U

/-- The pull-back on `P⁰_C` along a morphism of `K`-schemes. -/
private noncomputable abbrev picMap {U' U : Over (Spec (.of K))} (g : U' ⟶ U) :
    (relativePicZeroFunctor k X.f).obj (op (toK K U)) →+
      (relativePicZeroFunctor k X.f).obj (op (toK K U')) :=
  ((relativePicZeroFunctor k X.f).map ((Over.map (specMapK (k := k) K)).map g).op).hom

variable (c₀ : toK (k := k) K (𝟙_ (Over (Spec (.of K)))) ⟶ Over.mk X.f)

/-- `ι` read on `K`-schemes, with values in `J_K`. -/
private noncomputable def psi (U : Over (Spec (.of K))) :
    (relativePicZeroFunctor k X.f).obj (op (toK K U)) ≃ (U ⟶ JK K A.J) :=
  haveI := A.isIso_app (toK K U) ⟨(Over.map (specMapK (k := k) K)).map (toUnit U) ≫ c₀⟩
  (asIso (A.ι.app (op (toK K U)))).toEquiv.trans
    ((Over.mapPullbackAdj (specMapK (k := k) K)).homEquiv U A.J)

private lemma psi_apply (U : Over (Spec (.of K))) (a) :
    psi X A K c₀ U a = (Over.mapPullbackAdj (specMapK (k := k) K)).homEquiv U A.J
      (A.ι.app (op (toK K U)) a) := rfl

private lemma psi_naturality {U' U : Over (Spec (.of K))} (g : U' ⟶ U) (a) :
    psi X A K c₀ U' (picMap X K g a) = g ≫ psi X A K c₀ U a := by
  rw [psi_apply, psi_apply, ← Adjunction.homEquiv_naturality_left]
  congr 1
  exact NatTrans.naturality_apply A.ι ((Over.map (specMapK (k := k) K)).map g).op a

end Psi

section Dimension

variable {k : Type u} [Field k]

open Stacks.RigidifiedPicard relativePicZeroFunctor in
/-- **`dim J = g`.** Over `K = k̄` the curve has a rational point `σ`, the base change `J_K`
represents the rigidified `Pic⁰_{C_K/K,σ}` (through `ι`), and so does the degree-zero component
of the Picard scheme of `C_K`, which is smooth of relative dimension `g` over `K`; the two are
isomorphic, and the dimension of `J` is that of `J_K`. -/
public theorem Jacobian.topologicalKrullDim_eq_genus (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) : topologicalKrullDim A.J.left = (genus X.f : WithBot ℕ∞) := by
  have := A.isAbelianVariety
  have hAV : IsAbelianVariety k A.J := inferInstance
  have hV := hAV.toIsProperVariety.toIsVariety
  have : LocallyOfFiniteType A.J.hom := hV.toLocallyOfFiniteType
  let K := AlgebraicClosure k
  obtain ⟨c₁⟩ := X.nonempty_algebraicClosure_point
  let e : toK (k := k) K (𝟙_ (Over (Spec (.of K)))) ⟶ Over.mk (specMap k K) :=
    Over.homMk (𝟙 _) (by simp [toK])
  let c₀ : toK (k := k) K (𝟙_ (Over (Spec (.of K)))) ⟶ Over.mk X.f := e ≫ c₁
  let fK := curveOver k X.f K
  have := smoothOfRelativeDimension_curveOver k X.f K
  have := isProper_curveOver k X.f K
  have := geometricallyIrreducible_curveOver k X.f K
  have := smooth_curveOver k X.f K
  have := isCurve_curveOver k X.f K
  have hdimX := topologicalKrullDim_curveOver k X.f K
  have hproj := isProjectiveMorphism_curveOver k X.f K
  have hdimE := topologicalKrullDim_fiber_curveOver_le_one k X.f K
  let σ := pointSection X.f (Over.mk (specMap k K)) c₁
  have hσ : σ ≫ fK = 𝟙 _ := pointSection_bcProj X.f _ c₁
  -- `J_K` represents the rigidified `Pic⁰`
  let iso1 : (Over.map (specMap k K)).op ⋙ relativePicZeroFunctor k X.f ⋙
      forget AddCommGrpCat ≅ yoneda.obj (JK K A.J) :=
    NatIso.ofComponents (fun U => (psi X A K c₀ U.unop).toIso) (fun {U U'} g => by
      ext a
      exact psi_naturality X A K c₀ g.unop a)
  let R1 : (rigidified k X.f K c₁ ⋙ forget GrpCat).RepresentableBy (JK K A.J) :=
    Functor.representableByEquiv.symm ((rigidifiedIso k X.f K c₁ ≪≫ iso1).symm)
  -- the Picard scheme of `C_K`
  let HH : ∀ d : ℕ, Σ H : Over (Spec (.of K)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk fK) H d := fun d =>
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk fK) hproj d).some
  obtain ⟨P, ⟨eP⟩, hP⟩ := exists_smooth_grp_iso_functor fK hdimX σ hσ (fun d => (HH d).1)
    (fun d => (HH d).2)
    (fun T c => Stacks.WeilCohomology.cohomologyLocusDivisorExistence K fK T c)
    (fun T Z Z' => Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness K fK T Z Z')
    (fun L _ _ c => exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one K L fK c)
  let R2 := degreeLocusZeroRepresentableBy fK hdimE σ hσ P eP
  let i := R1.uniqueUpToIso R2
  have : IsIso i.hom.left := (Over.forget _).map_isIso i.hom
  have h1 : topologicalKrullDim (JK K A.J).left =
      topologicalKrullDim (degreeLocusOver fK hdimE σ hσ P eP 0).left :=
    IsHomeomorph.topologicalKrullDim_eq _ i.hom.left.homeomorph.isHomeomorph
  have := hP
  have h2 := topologicalKrullDim_degreeLocus_eq (g := genus fK) fK hdimX hdimE σ hσ
    P eP 0
  have h3 : genus fK = genus X.f := genus_bc_spec X.f (specMap k K)
  have h4 : topologicalKrullDim (JK K A.J).left = topologicalKrullDim A.J.left :=
    topologicalKrullDim_baseChange k K (pullback.fst A.J.hom (specMap k K))
      (pullback.snd A.J.hom (specMap k K)) A.J.hom (IsPullback.of_hasPullback _ _)
  rw [← h4, h1, ← h3]
  exact h2

end Dimension

end Faltings
