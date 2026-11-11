module

public import Mathlib
public import Mordell.Attr
public import Mordell.Jacobian.AbelJacobi
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Jacobian.DeltaClass
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Diagonal
public import Mordell.AbelianVariety.PicZero
public import Mordell.Jacobian.AbelJacobiBaseChange
public import Mordell.Jacobian.Autoduality.PhiTheta
public import Mordell.Jacobian.Theta.MumfordClass
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import Mordell.Jacobian.Theta.BaseChange
public import Mordell.Jacobian.BaseChange
public import Mordell.Jacobian.Theta.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity

/-!
# Bombieri's Lemma 1: the pull-back of `δ` to `C × C`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C`, `j = j_P : C ⟶ J` the Abel–Jacobi map and
`δ = s₁^* θ + s₂^* θ - s₁₂^* θ ∈ Pic(J × J)` the class built from the theta class
`θ = cl(Θ)`, the class of a reduced effective Cartier divisor `D` with support `Θ`. On `C × C`
let `Δ` be the diagonal and `Δ' = Δ - P × C - C × P`. Then `(j × j)^* δ = cl(Δ')` in
`Pic(C × C)`.

## Main results

* `Faltings.schemePullbackClass_abelJacobi_deltaClass`: `(j × j)^* δ = cl(Δ')`.

## Implementation notes

The product `J × J` is the monoidal product `J ⊗ J` in schemes over `Spec k`, as in
`Faltings.deltaClass`, and `j × j` is the tensor product `j ⊗ₘ j` of morphisms over `Spec k`;
its underlying morphism of schemes has source `C ×_k C = pullback X.f X.f`. The class
`cl(Δ') = [𝒪(Δ)] - pr₁^*[𝒪_C(P)] - pr₂^*[𝒪_C(P)]` is
`Faltings.CurveWithDegreeOneDivisor.vojtaClass X 0 0 1`, in which the diagonal is an
effective Cartier divisor by `Faltings.isEffectiveCartierDivisor_ker_diagonal`. Pull-backs of
classes are `Stacks.Picard.schemePullbackClassHom`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5, Lemma 1.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.RigidifiedPicard Faltings
open scoped MonObj

universe u

namespace Faltings

/-! ### The square `C_K ×_K C_K ⟶ C ×_k C` -/

section Square

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The canonical morphism `C_K ×_K C_K ⟶ C ×_k C`. -/
private noncomputable abbrev bcCC {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) :
    pullback (pullback.snd f π) (pullback.snd f π) ⟶ pullback f f :=
  pullback.map _ _ f f (pullback.fst f π) (pullback.fst f π) π pullback.condition.symm
    pullback.condition.symm

/-- `C_K ×_K C_K ⟶ C_K` is the base change of `C ×_k C ⟶ C` along `C_K ⟶ C`. -/
private lemma isPullback_bcCC_fst {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) :
    IsPullback (bcCC (K := K) f) (pullback.fst _ _) (pullback.fst f f) (pullback.fst f π) := by
  have hout : IsPullback (bcCC (K := K) f ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f π) (pullback.snd f π)) f (pullback.fst f π ≫ f) := by
    have h := (IsPullback.of_hasPullback (pullback.snd f π) (pullback.snd f π)).flip.paste_horiz
      (IsPullback.of_hasPullback f π)
    rw [← pullback.condition] at h
    convert h using 1
    exact pullback.lift_snd _ _ _
  exact IsPullback.of_right hout (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip

/-- `C_K ×_K C_K` is the base change of `C ×_k C` along `Spec K ⟶ Spec k`. -/
private lemma isPullback_bcCC {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) :
    IsPullback (bcCC (K := K) f) (pullback.fst _ _ ≫ pullback.snd f π)
      (pullback.fst f f ≫ f) π :=
  (isPullback_bcCC_fst f).paste_vert (IsPullback.of_hasPullback f π)

/-- The diagonal of `C_K` is the base change of the diagonal of `C`. -/
private lemma isPullback_diagonal_bcCC {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) :
    IsPullback (pullback.diagonal (pullback.snd f π)) (pullback.fst f π) (bcCC (K := K) f)
      (pullback.diagonal f) := by
  have hout : IsPullback (pullback.diagonal (pullback.snd f π) ≫ pullback.fst _ _)
      (pullback.fst f π) (pullback.fst f π) (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst, pullback.diagonal_fst]
    exact IsPullback.id_horiz _
  exact IsPullback.of_right hout (by
    apply pullback.hom_ext <;> simp [bcCC]) (isPullback_bcCC_fst f).flip

/-- Pull-back of classes along a composite, in the additive form. -/
private lemma pb_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClassHom f (Stacks.Picard.schemePullbackClassHom g x) =
      Stacks.Picard.schemePullbackClassHom (f ≫ g) x :=
  Stacks.Picard.schemePullbackClass_comp f g x

/-- Pull-back of `a^* t + b^* t - c^* t` along a composite, in the form used for `δ`. -/
private lemma pb_pb_add_sub {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a b c : Z ⟶ W)
    (t : Stacks.Picard.ofScheme W) :
    Stacks.Picard.schemePullbackClassHom f (Stacks.Picard.schemePullbackClassHom g
        (Stacks.Picard.schemePullbackClassHom a t + Stacks.Picard.schemePullbackClassHom b t -
          Stacks.Picard.schemePullbackClassHom c t)) =
      Stacks.Picard.schemePullbackClassHom ((f ≫ g) ≫ a) t +
        Stacks.Picard.schemePullbackClassHom ((f ≫ g) ≫ b) t -
        Stacks.Picard.schemePullbackClassHom ((f ≫ g) ≫ c) t := by
  rw [pb_comp, map_sub, map_add, pb_comp, pb_comp, pb_comp]

/-- Pull-back of `a - b - c`. -/
private lemma pb_sub_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (a b c : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClassHom f (a - b - c) =
      Stacks.Picard.schemePullbackClassHom f a - Stacks.Picard.schemePullbackClassHom f b -
        Stacks.Picard.schemePullbackClassHom f c := by
  rw [map_sub, map_sub]

/-- Pull-back along an isomorphism is injective on classes. -/
private lemma injective_pb_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom e.hom) := by
  intro x y hxy
  have h := congrArg (Stacks.Picard.schemePullbackClassHom e.inv) hxy
  rw [pb_comp, pb_comp, e.inv_hom_id] at h
  exact (Stacks.Picard.schemePullbackClass_id _ x).symm.trans
    (h.trans (Stacks.Picard.schemePullbackClass_id _ y))

/-- **Classes on `C ×_k C` are detected over `K`** ([Stacks, Tag 0CC5]): `C ×_k C` is integral
and proper over `k`, so its ring of global sections is finite over `k`. -/
private lemma injective_bcCC (X : CurveWithDegreeOneDivisor k) :
    Function.Injective (Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)) := by
  have hpb := isPullback_bcCC (K := K) X.f
  let fCC := pullback.fst X.f X.f ≫ X.f
  have : IsIntegral X.C := GeometricallyIntegral.isIntegral_of_subsingleton X.f
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : CompactSpace ↥(pullback X.f X.f) :=
    (quasiCompact_iff_compactSpace fCC).1 inferInstance
  have : QuasiSeparatedSpace ↥(pullback X.f X.f) :=
    (quasiSeparated_iff_quasiSeparatedSpace fCC).1 inferInstance
  have hfd : letI := Stacks.AlgebraicGeometry.PicardBaseChange.globalSectionsAlgebra fCC
      FiniteDimensional k Γ(pullback X.f X.f, ⊤) := by
    letI := Stacks.AlgebraicGeometry.PicardBaseChange.globalSectionsAlgebra fCC
    change Module.Finite k Γ(pullback X.f X.f, ⊤)
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k fCC).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩))
  have hinj :=
    Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional
      (pullback X.f X.f) (algebraMap k K) fCC hfd
  have hiso := injective_pb_iso hpb.isoPullback
  have hW : bcCC (K := K) X.f = hpb.isoPullback.hom ≫ pullback.fst fCC
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := hpb.isoPullback_hom_fst.symm
  intro x y hxy
  rw [hW, ← pb_comp, ← pb_comp] at hxy
  exact hinj (hiso hxy)

/-- **The Mumford class of a translate**, read on `k`-morphisms: if `θ₀` is the pull-back of
`θ` along `τ` followed by `A_K ⟶ A`, and `τ` acts on `T`-points as multiplication by `c⁻¹`, then
`(j₀ × j₀)^*(s₁₂^* θ₀ - s₁^* θ₀ - s₂^* θ₀)` is
`F(r₁ r₂ c⁻¹) - F(r₁ c⁻¹) - F(r₂ c⁻¹)`, where `F(x) = x^* θ` and `rᵢ = j₀ ∘ prᵢ`. -/
private lemma pb_tensorHom_mumford_translate (A : Over (Spec (.of k))) [GrpObj A]
    {Y : Over (Spec (.of K))} (j₀ : Y ⟶ (Over.pullback π).obj A)
    (τ : (Over.pullback π).obj A ⟶ (Over.pullback π).obj A)
    (c : Y ⊗ Y ⟶ (Over.pullback π).obj A) (hτ : ∀ ψ : Y ⊗ Y ⟶ _, ψ ≫ τ = ψ * c⁻¹)
    (θ : Stacks.Picard.ofScheme A.left) :
    Stacks.Picard.schemePullbackClassHom (j₀ ⊗ₘ j₀).left
        (Stacks.Picard.schemePullbackClassHom μ[(Over.pullback π).obj A].left
            (Stacks.Picard.schemePullbackClass (τ.left ≫ pullback.fst A.hom π) θ) -
          Stacks.Picard.schemePullbackClassHom
            (CartesianMonoidalCategory.fst ((Over.pullback π).obj A) _).left
            (Stacks.Picard.schemePullbackClass (τ.left ≫ pullback.fst A.hom π) θ) -
          Stacks.Picard.schemePullbackClassHom
            (CartesianMonoidalCategory.snd ((Over.pullback π).obj A) _).left
            (Stacks.Picard.schemePullbackClass (τ.left ≫ pullback.fst A.hom π) θ)) =
      Stacks.Picard.schemePullbackClass (P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) *
          P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) * (P A c)⁻¹).left θ -
        Stacks.Picard.schemePullbackClass
          (P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) * (P A c)⁻¹).left θ -
        Stacks.Picard.schemePullbackClass
          (P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) * (P A c)⁻¹).left θ := by
  have key : ∀ (x : Y ⊗ Y ⟶ (Over.pullback π).obj A ⊗ (Over.pullback π).obj A)
      (y : (Over.pullback π).obj A ⊗ (Over.pullback π).obj A ⟶ (Over.pullback π).obj A),
      Stacks.Picard.schemePullbackClassHom x.left (Stacks.Picard.schemePullbackClassHom y.left
          (Stacks.Picard.schemePullbackClass (τ.left ≫ pullback.fst A.hom π) θ)) =
        Stacks.Picard.schemePullbackClass (P A (x ≫ y ≫ τ)).left θ := by
    intro x y
    rw [P_left, Over.comp_left, Over.comp_left]
    refine (pb_comp _ _ _).trans ((pb_comp _ _ _).trans ?_)
    simp only [Category.assoc]
    rfl
  have h₁ : P A ((j₀ ⊗ₘ j₀) ≫ μ[(Over.pullback π).obj A] ≫ τ) =
      P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) * P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) *
        (P A c)⁻¹ := by
    rw [← CartesianMonoidalCategory.lift_fst_comp_snd_comp, ← Category.assoc, ← Hom.mul_def, hτ,
      ← pEquiv_apply, map_mul, map_mul, map_inv]
    rfl
  have h₂ : P A ((j₀ ⊗ₘ j₀) ≫ CartesianMonoidalCategory.fst _ _ ≫ τ) =
      P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) * (P A c)⁻¹ := by
    rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_fst, hτ, ← pEquiv_apply, map_mul,
      map_inv]
    rfl
  have h₃ : P A ((j₀ ⊗ₘ j₀) ≫ CartesianMonoidalCategory.snd _ _ ≫ τ) =
      P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) * (P A c)⁻¹ := by
    rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_snd, hτ, ← pEquiv_apply, map_mul,
      map_inv]
    rfl
  rw [pb_sub_sub, key, key, key, h₁, h₂, h₃]

/-- The pull-back of `φ_c(a)` along a `T`-point `u` of `A_K`, restricted along `v`, is
`(P(v u) · a)^* c - P(v u)^* c`. -/
private lemma pb_phiMap (A : Over (Spec (.of k))) [GrpObj A] {T T' : Over (Spec (.of K))}
    (u : T ⟶ (Over.pullback π).obj A) (v : T' ⟶ T) (c : Stacks.Picard.ofScheme A.left)
    (a : Over.mk π ⟶ A) :
    Stacks.Picard.schemePullbackClass v.left
        (Stacks.Picard.schemePullbackClass u.left (AbelianVariety.phiMap A c a)) =
      Stacks.Picard.schemePullbackClass
          (P A (v ≫ u) * ((Over.homMk T'.hom : (Over.map π).obj T' ⟶ Over.mk π) ≫ a)).left c -
        Stacks.Picard.schemePullbackClass (P A (v ≫ u)).left c := by
  rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left, AbelianVariety.phiMap]
  refine (map_sub (Stacks.Picard.schemePullbackClassHom (v ≫ u).left) _ _).trans ?_
  erw [pb_comp, pb_comp]
  rw [← lift_P_left A (v ≫ u), ← Over.comp_left, ← Over.comp_left, Hom.mul_def,
    CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd_assoc]
  rfl

end Square

/-! ### Base change of the classes on `C × C` -/

section ClassesBaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

private lemma flat_specMap_algebraMap : Flat π := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
  infer_instance

/-- The diagonal of `C` pulls back to the diagonal of `C_K`. -/
private lemma comap_ker_diagonal_bcCC {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSeparated f] :
    (pullback.diagonal f).ker.comap (bcCC (K := K) f) =
      (pullback.diagonal (pullback.snd f π)).ker := by
  have hsq := isPullback_diagonal_bcCC (K := K) f
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hsq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- **`[𝒪(Δ)]` pulls back to `[𝒪(Δ_K)]`** along `C_K ×_K C_K ⟶ C ×_k C`. -/
private lemma pb_bcCC_picardClass_diagonal (X : CurveWithDegreeOneDivisor k)
    [IsSmoothProjectiveCurve K (pullback.snd X.f π)] :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
      (isEffectiveCartierDivisor_ker_diagonal k X.f).1
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor
        (pullback.diagonal (pullback.snd X.f π)).ker :=
      (isEffectiveCartierDivisor_ker_diagonal K (pullback.snd X.f π)).1
    Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)
        (Stacks.Divisors.picardClass (pullback.diagonal X.f).ker) =
      Stacks.Divisors.picardClass (pullback.diagonal (pullback.snd X.f π)).ker := by
  have hΔ : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (pullback.diagonal (pullback.snd X.f π)).ker :=
    (isEffectiveCartierDivisor_ker_diagonal K (pullback.snd X.f π)).1
  have : Flat π := flat_specMap_algebraMap
  have : Flat (bcCC (K := K) X.f) :=
    MorphismProperty.of_isPullback (isPullback_bcCC (K := K) X.f).flip inferInstance
  have : Stacks.Divisors.IsPullbackDefined (bcCC (K := K) X.f) (pullback.diagonal X.f).ker :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hΔ
  refine (Stacks.Divisors.schemePullbackClass_picardClass _ _).trans ?_
  exact Stacks.Divisors.picardClass_congr (comap_ker_diagonal_bcCC X.f)

/-- **`cl(Δ')` over `K`**: the pull-back of `cl(Δ - P × C - C × P)` to `C_K ×_K C_K` is
`cl(Δ_K - P₀ × C_K - C_K × P₀) + pr₁^*[P₀] + pr₂^*[P₀] - pr₁^*[P_K] - pr₂^*[P_K]` for any
divisor `P₀` of degree one on `C_K`. -/
private lemma pb_bcCC_vojtaClass (X : CurveWithDegreeOneDivisor k)
    (P₀ : {x : ↥(pullback X.f π) // IsClosed ({x} : Set ↥(pullback X.f π))} →₀ ℤ)
    (hP₀ : (P₀.sum fun x n => n * ((pullback.snd X.f π).residueDegree x.1 : ℤ)) = 1)
    [IsSmoothProjectiveCurve K (pullback.snd X.f π)] :
    let X₀ : CurveWithDegreeOneDivisor K := ⟨pullback X.f π, pullback.snd X.f π, P₀, hP₀⟩
    Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f) (X.vojtaClass 0 0 1) =
      X₀.vojtaClass 0 0 1 +
        Stacks.Picard.schemePullbackClassHom (pullback.fst X₀.f X₀.f) X₀.classP +
        Stacks.Picard.schemePullbackClassHom (pullback.snd X₀.f X₀.f) X₀.classP -
        Stacks.Picard.schemePullbackClassHom (pullback.fst X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f π) X.classP) -
        Stacks.Picard.schemePullbackClassHom (pullback.snd X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f π) X.classP) := by
  intro X₀
  have h₁ := pb_bcCC_picardClass_diagonal (K := K) X
  have h₂ : Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)
      (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) X.classP) =
        Stacks.Picard.schemePullbackClassHom (pullback.fst X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f π) X.classP) := by
    refine (pb_comp _ _ _).trans ((congrArg (fun f => Stacks.Picard.schemePullbackClassHom f
      X.classP) ?_).trans (pb_comp _ _ _).symm)
    simp [bcCC]
    rfl
  have h₃ : Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)
      (Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f) X.classP) =
        Stacks.Picard.schemePullbackClassHom (pullback.snd X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f π) X.classP) := by
    refine (pb_comp _ _ _).trans ((congrArg (fun f => Stacks.Picard.schemePullbackClassHom f
      X.classP) ?_).trans (pb_comp _ _ _).symm)
    simp [bcCC]
    rfl
  have e₀ := X₀.vojtaClass_zero_zero_one
  refine ((congrArg (Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f))
    X.vojtaClass_zero_zero_one).trans (pb_sub_sub _ _ _ _)).trans ?_
  rw [e₀]
  linear_combination (norm := module) h₁ - h₂ - h₃

/-- **`(j × j)^* δ` on `C_K ×_K C_K`**: if `q₁, q₂` are the `k`-morphisms `j ∘ prᵢ` from
`C_K ×_K C_K`, the pull-back of `δ` is `q₁^* θ + q₂^* θ - (q₁ q₂)^* θ`. -/
private lemma pb_bcCC_deltaClass (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D) (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (q₁ q₂ : (Over.map π).obj (Over.mk (pullback.snd X.f π) ⊗ Over.mk (pullback.snd X.f π)) ⟶ A.J)
    (hq₁ : q₁.left = pullback.fst (pullback.snd X.f π) (pullback.snd X.f π) ≫
      pullback.fst X.f π ≫ j.left)
    (hq₂ : q₂.left = pullback.snd (pullback.snd X.f π) (pullback.snd X.f π) ≫
      pullback.fst X.f π ≫ j.left) :
    let θ := Stacks.Divisors.picardClass D
    Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)
        (Stacks.Picard.schemePullbackClassHom (j ⊗ₘ j).left
          (deltaClass X A hg j hj D hrad hsupp)) =
      Stacks.Picard.schemePullbackClass q₁.left θ + Stacks.Picard.schemePullbackClass q₂.left θ -
        Stacks.Picard.schemePullbackClass (q₁ * q₂).left θ := by
  intro θ
  have := A.isAbelianVariety
  have hm : (CartesianMonoidalCategory.lift q₁ q₂).left = bcCC (K := K) X.f ≫ (j ⊗ₘ j).left := by
    apply pullback.hom_ext
    · change ((CartesianMonoidalCategory.lift q₁ q₂) ≫ CartesianMonoidalCategory.fst _ _).left =
        bcCC (K := K) X.f ≫ (j ⊗ₘ j).left ≫ pullback.fst _ _
      rw [CartesianMonoidalCategory.lift_fst, hq₁]
      change _ = bcCC (K := K) X.f ≫ ((j ⊗ₘ j) ≫ CartesianMonoidalCategory.fst _ _).left
      rw [CartesianMonoidalCategory.tensorHom_fst, Over.comp_left]
      change _ = bcCC (K := K) X.f ≫ pullback.fst X.f X.f ≫ j.left
      simp [bcCC]
    · change ((CartesianMonoidalCategory.lift q₁ q₂) ≫ CartesianMonoidalCategory.snd _ _).left =
        bcCC (K := K) X.f ≫ (j ⊗ₘ j).left ≫ pullback.snd _ _
      rw [CartesianMonoidalCategory.lift_snd, hq₂]
      change _ = bcCC (K := K) X.f ≫ ((j ⊗ₘ j) ≫ CartesianMonoidalCategory.snd _ _).left
      rw [CartesianMonoidalCategory.tensorHom_snd, Over.comp_left]
      change _ = bcCC (K := K) X.f ≫ pullback.snd X.f X.f ≫ j.left
      simp [bcCC]
  have e₁ : (bcCC (K := K) X.f ≫ (j ⊗ₘ j).left) ≫
      (CartesianMonoidalCategory.fst A.J A.J).left = q₁.left :=
    (congrArg (· ≫ (CartesianMonoidalCategory.fst A.J A.J).left) hm.symm).trans
      (by rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst])
  have e₂ : (bcCC (K := K) X.f ≫ (j ⊗ₘ j).left) ≫
      (CartesianMonoidalCategory.snd A.J A.J).left = q₂.left :=
    (congrArg (· ≫ (CartesianMonoidalCategory.snd A.J A.J).left) hm.symm).trans
      (by rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd])
  have e₃ : (bcCC (K := K) X.f ≫ (j ⊗ₘ j).left) ≫ μ[A.J].left = (q₁ * q₂).left :=
    (congrArg (· ≫ μ[A.J].left) hm.symm).trans
      (by rw [← Over.comp_left, ← Hom.mul_def])
  unfold deltaClass
  dsimp only
  refine (pb_pb_add_sub _ _ _ _ _ _).trans ?_
  exact congrArg₂ (· - ·) (congrArg₂ (· + ·)
    (congrArg (fun f => Stacks.Picard.schemePullbackClassHom f θ) e₁)
    (congrArg (fun f => Stacks.Picard.schemePullbackClassHom f θ) e₂))
    (congrArg (fun f => Stacks.Picard.schemePullbackClassHom f θ) e₃)

end ClassesBaseChange

/-- **Translation by constants in the theorem of the cube.** Let `F` satisfy the identity of the
cube on a commutative group, `qᵢ = rᵢ a` with `F(a²) = 0`, and `F(b) = 0`. Then
`F(q₁) + F(q₂) - F(q₁ q₂)` is `-(F(r₁ r₂ b) - F(r₁ b) - F(r₂ b))` corrected by the two
differences `F(qᵢ a) - F(qᵢ)`: each side differs from `F(r₁ r₂ t) - F(r₁ t) - F(r₂ t)`,
`t = a², b`, by the same amount. -/
private lemma add_sub_cube_eq {M G : Type*} [CommGroup M] [AddCommGroup G] (F : M → G)
    (hcube : ∀ f g h, F (f * g * h) + F f + F g + F h = F (f * g) + F (f * h) + F (g * h))
    {q₁ q₂ r₁ r₂ a b : M} (hq₁ : q₁ = r₁ * a) (hq₂ : q₂ = r₂ * a) (ha : F (a * a) = 0)
    (hb : F b = 0) :
    F q₁ + F q₂ - F (q₁ * q₂) =
      -(F (r₁ * r₂ * b) - F (r₁ * b) - F (r₂ * b)) - (F (q₁ * a) - F q₁) -
        (F (q₂ * a) - F q₂) := by
  subst hq₁ hq₂
  rw [mul_mul_mul_comm, mul_assoc r₁ a a, mul_assoc r₂ a a]
  linear_combination (norm := module) hcube r₁ r₂ b - hcube r₁ r₂ (a * a) - hb + ha

/-- Pull-back of a difference of classes. -/
private lemma pb_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (x y : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass f (x - y) =
      Stacks.Picard.schemePullbackClass f x - Stacks.Picard.schemePullbackClass f y :=
  map_sub (Stacks.Picard.schemePullbackClassHom f) x y

/-- The final computation: the two instances of the theorem of the cube, the Mumford identity
over `K` and autoduality, assembled in `Pic(C_K ×_K C_K)`. -/
private lemma eq_of_cube {M G : Type*} [CommGroup M] [AddCommGroup G] (F : M → G)
    (hcube : ∀ f g h, F (f * g * h) + F f + F g + F h = F (f * g) + F (f * h) + F (g * h))
    {q₁ q₂ r₁ r₂ a b : M} (hq₁ : q₁ = r₁ * a) (hq₂ : q₂ = r₂ * a) (ha : F (a * a) = 0)
    (hb : F b = 0) {L R V s₁ s₂ t₁ t₂ : G} (hL : L = F q₁ + F q₂ - F (q₁ * q₂))
    (hR : R = V + t₁ + t₂ - s₁ - s₂)
    (hM : F (r₁ * r₂ * b) - F (r₁ * b) - F (r₂ * b) = -V)
    (h₁ : F (q₁ * a) - F q₁ = s₁ - t₁) (h₂ : F (q₂ * a) - F q₂ = s₂ - t₂) : L = R := by
  rw [hL, hR, add_sub_cube_eq F hcube hq₁ hq₂ ha hb, hM, h₁, h₂]
  abel

section Helpers

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- Two degree-zero classes on `C_K` with the same image under `ι(Spec K)` are equal, when `C`
has a `K`-point. -/
private lemma smallEquiv_eq_of_ι_app_eq (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1)
    (hC : Nonempty (Over.mk π ⟶ Over.mk X.f))
    {z z' : Stacks.Picard.smallOfScheme (bc X.f (Over.mk π))}
    (hz : degree X.f hdim (Over.mk π) z = 0) (hz' : degree X.f hdim (Over.mk π) z' = 0)
    (h : A.ι.app (op (Over.mk π)) (show (relativePicZeroFunctor k X.f).obj (op (Over.mk π)) from
        QuotientAddGroup.mk (⟨z, hz⟩ : (degree X.f hdim (Over.mk π)).ker)) =
      A.ι.app (op (Over.mk π)) (show (relativePicZeroFunctor k X.f).obj (op (Over.mk π)) from
        QuotientAddGroup.mk (⟨z', hz'⟩ : (degree X.f hdim (Over.mk π)).ker))) :
    smallEquiv (bc X.f (Over.mk π)) z = smallEquiv (bc X.f (Over.mk π)) z' := by
  have := A.isIso_app (Over.mk π) hC
  have h1 := ((isIso_iff_bijective (A.ι.app (op (Over.mk π)))).1 inferInstance).1 h
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h1
  have hw' := congrArg (smallEquiv (bc X.f (Over.mk π))) hw
  rw [smallEquiv_smallSchemePullbackClassHom] at hw'
  have : Subsingleton (Stacks.Picard.ofScheme (Over.mk π).left) :=
    AlgebraicGeometry.subsingleton_picardGroup_spec_field K
  rw [Subsingleton.elim (smallEquiv (Over.mk π).left w) 0] at hw'
  have key := hw'.symm.trans (map_zero (Stacks.Picard.schemePullbackClassHom _))
  simp only [AddSubgroup.coe_subtype, map_add, map_neg] at key
  exact neg_add_eq_zero.1 key

/-- **The Mumford identity for a translate by a constant.** If `θ₀` is the pull-back of `θ`
along `τ = τ_{c⁻¹}` followed by `A_K ⟶ A`, for a constant `c`, then the Mumford class of `θ₀`
pulled back along `j₀ × j₀` is `F(r₁ r₂ b) - F(r₁ b) - F(r₂ b)` for the constant `b = c⁻¹`,
where `F(x) = x^* θ` and `rᵢ = j₀ ∘ prᵢ`; and `F(b) = 0`. -/
private lemma exists_const_mumford (A : Over (Spec (.of k))) [GrpObj A] {Y : Over (Spec (.of K))}
    (j₀ : Y ⟶ (Over.pullback π).obj A)
    (e' : Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback π).obj A)
    (θ : Stacks.Picard.ofScheme A.left) {θ₀ : Stacks.Picard.ofScheme ((Over.pullback π).obj A).left}
    {V : Stacks.Picard.ofScheme (Y ⊗ Y).left}
    (hθ₀ : θ₀ = Stacks.Picard.schemePullbackClass
      ((𝟙 ((Over.pullback π).obj A) * (Over.homMk ((Over.pullback π).obj A).hom
        (Category.comp_id _) ≫ e')⁻¹).left ≫ pullback.fst A.hom π) θ)
    (hM : Stacks.Picard.schemePullbackClassHom (j₀ ⊗ₘ j₀).left
        (Stacks.Picard.schemePullbackClassHom μ[(Over.pullback π).obj A].left θ₀ -
          Stacks.Picard.schemePullbackClassHom
            (CartesianMonoidalCategory.fst ((Over.pullback π).obj A) _).left θ₀ -
          Stacks.Picard.schemePullbackClassHom
            (CartesianMonoidalCategory.snd ((Over.pullback π).obj A) _).left θ₀) = -V) :
    ∃ b : (Over.map π).obj (Y ⊗ Y) ⟶ A, Stacks.Picard.schemePullbackClass b.left θ = 0 ∧
      Stacks.Picard.schemePullbackClass (P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) *
          P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) * b).left θ -
        Stacks.Picard.schemePullbackClass
          (P A (CartesianMonoidalCategory.fst Y Y ≫ j₀) * b).left θ -
        Stacks.Picard.schemePullbackClass
          (P A (CartesianMonoidalCategory.snd Y Y ≫ j₀) * b).left θ = -V := by
  let JK := (Over.pullback π).obj A
  let uS : Y ⊗ Y ⟶ Over.mk (𝟙 (Spec (.of K))) := Over.homMk (Y ⊗ Y).hom (Category.comp_id _)
  let cK : Y ⊗ Y ⟶ JK := uS ≫ e'
  have hψτ : ∀ ψ : Y ⊗ Y ⟶ JK,
      ψ ≫ (𝟙 JK * (Over.homMk JK.hom (Category.comp_id _) ≫ e')⁻¹) = ψ * cK⁻¹ := by
    intro ψ
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc,
      Over.mkIdTerminal.hom_ext (ψ ≫ Over.homMk JK.hom (Category.comp_id _)) uS]
  have hT := pb_tensorHom_mumford_translate A j₀ _ cK hψτ θ
  rw [← hθ₀] at hT
  refine ⟨(P A cK)⁻¹, ?_, hT.symm.trans hM⟩
  rw [← pEquiv_apply, ← map_inv, pEquiv_apply, ← GrpObj.comp_inv]
  change Stacks.Picard.schemePullbackClass (P A (uS ≫ e'⁻¹)).left θ = 0
  rw [P_left, Over.comp_left, Category.assoc]
  exact AbelianVariety.schemePullbackClass_comp_spec_field (Y ⊗ Y).hom _ θ

end Helpers

variable {k : Type u} [Field k]

/-- **Bombieri's Lemma 1, second identity.** For a curve `X = (C, P)` with a divisor of degree
one, of genus `g ≥ 1`, a Jacobian `A = (J, ι)`, the Abel–Jacobi map `j = j_P` and
`θ = [𝒪(D)]` for a reduced effective Cartier divisor `D` with support `Θ`, the pull-back of
`δ = Faltings.deltaClass X A hg j hj D hrad hsupp ∈ Pic(J × J)` along `j × j` is the class
`cl(Δ') = Faltings.CurveWithDegreeOneDivisor.vojtaClass X 0 0 1` of `Δ' = Δ - P × C - C × P` in
`Pic(C ×_k C)`. -/
@[faltings "lem_nt_bombieri_lemma1_delta"]
theorem schemePullbackClass_abelJacobi_deltaClass (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj) :
    Stacks.Picard.schemePullbackClassHom (j ⊗ₘ j).left (deltaClass X A hg j hj D hrad hsupp) =
      CurveWithDegreeOneDivisor.vojtaClass X 0 0 1 := by
  have hι : ∀ (T : Over (Spec (.of k))) (x y : (relativePicZeroFunctor k X.f).obj (op T)),
      (show T ⟶ A.J from A.ι.app (op T) (x + y)) =
        (show T ⟶ A.J from A.ι.app (op T) x) * (show T ⟶ A.J from A.ι.app (op T) y) :=
    fun T x y => A.map_add (op T) x y
  /- `D` is the vanishing ideal of `Θ`, being radical with support `Θ`. -/
  have hDv : D = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ := by
    rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    change (D.support : Set A.J.left) = closure (thetaDivisor X A hg j hj)
    rw [← hsupp, D.support.isClosed.closure_eq]
  subst hDv
  let K := AlgebraicClosure k
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec X.f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
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
  /- `cl(P_K - P₀)` has degree `1 - 1 = 0`. -/
  have hdegₑ : degree X.f hdim T zₑ = 0 := by
    have : IsProper (bcProj X.f T) := inferInstanceAs (IsProper X₀.f)
    have : GeometricallyIrreducible (bcProj X.f T) :=
      MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
        (IsPullback.of_hasPullback X.f T.hom) inferInstance
    have hdimT : topologicalKrullDim (bc X.f T) ≤ 1 :=
      topologicalKrullDim_le_one_of_smoothOfRelativeDimension (bcProj X.f T)
    have hP : invertibleCurveDegreeHom K (bcProj X.f T) hdimT
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP) = 1 :=
      (invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k K
        (IsPullback.of_hasPullback X.f T.hom)
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f) hdimT X.classP).trans
          (X.invertibleCurveDegreeHom_classP _)
    have hP₀' : invertibleCurveDegreeHom K (bcProj X.f T) hdimT classP₀ = 1 :=
      X₀.invertibleCurveDegreeHom_classP hdimT
    funext t
    rw [degree_apply, AddEquiv.apply_symm_apply]
    refine (relativeInvertibleDegreeHomAt_spec (bcProj X.f T) hdimT _ t _).trans ?_
    rw [map_sub, hP, hP₀']
    rfl
  let e : T ⟶ A.J := A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
    QuotientAddGroup.mk (⟨zₑ, hdegₑ⟩ : (degree X.f hdim T).ker))
  have he : ∀ hdeg : degree X.f hdim T zₑ = 0, e = A.ι.app (op T)
      (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨zₑ, hdeg⟩ : (degree X.f hdim T).ker)) := fun _ => rfl
  have hΘ' := thetaDivisor_baseChange_eq_image_translate X A hι hg hj K P₀ hP₀ ι' hι'c hj₀ e he
  have hrel := P_comp_eq_mul_inv X A hι hj K P₀ hP₀ ι' hι'c hι' hj₀ e he
  /- The base change `J_K`, the `K`-point `e_K` and the translation `τ = τ_{-(g-1)e}`. -/
  let JK : Over (Spec (.of K)) :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J
  have : IsAbelianVariety K JK := A₀.isAbelianVariety
  have : IsCommMonObj JK := isCommMonObj_of_isProper_of_geometricallyIntegral JK
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  let eK : Over.mk (𝟙 (Spec (.of K))) ⟶ JK :=
    Over.homMk (pullback.lift e.left (𝟙 _) (by simp [T]))
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
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := flat_specMap_algebraMap
  /- `θ` is the class of the reduced divisor `D` on `Θ`, and `θ₀ = cl(Θ_{P₀})` is `τ^* θ_K`. -/
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg j hj
  obtain ⟨Z₀, hZ₀⟩ := exists_primeDivisor_support_eq_thetaDivisor X₀ A₀ hg₀ j₀ hj₀
  have hΘcl : closure (thetaDivisor X A hg j hj) = thetaDivisor X A hg j hj := by
    rw [← hZ]; exact Z.idealSheaf.support.isClosed.closure_eq
  have hΘ₀cl : closure (thetaDivisor X₀ A₀ hg₀ j₀ hj₀) = thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := by
    rw [← hZ₀]; exact Z₀.idealSheaf.support.isClosed.closure_eq
  let D := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (thetaDivisor X A hg j hj), isClosed_closure⟩ : TopologicalSpace.Closeds A.J.left)
  let D₀ := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (thetaDivisor X₀ A₀ hg₀ j₀ hj₀), isClosed_closure⟩ :
      TopologicalSpace.Closeds A₀.J.left)
  have : IsReduced D.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IsReduced D₀.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hD : (D.support : Set A.J.left) = thetaDivisor X A hg j hj := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hΘcl
  have hD₀ : (D₀.support : Set A₀.J.left) = thetaDivisor X₀ A₀ hg₀ j₀ hj₀ := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hΘ₀cl
  let φ := τ.left ≫ pullback.fst A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hD₀D : D₀ = D.comap φ := by
    have := isReduced_comap_of_support_eq_thetaDivisor X A hg hj D hD K φ JK.hom
      (IsPullback.of_iso (IsPullback.of_hasPullback A.J.hom _) (asIso τ.left).symm (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (by simp [φ]) (by
          simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp]
          exact Over.w τ) (by simp) (by simp))
    refine eq_comap_of_preimage_support_eq D₀ D φ ?_
    rw [hD, hD₀]
    exact preimage_comp_eq_of_preimage_eq_image τ.left.isOpenEmbedding.injective hΘ''
  have : Stacks.Divisors.IsPullbackDefined φ D :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have hD₀C : Stacks.Divisors.IsEffectiveCartierDivisor D₀ := by
    rw [hD₀D]
    exact ‹Stacks.Divisors.IsPullbackDefined φ D›
  have hθ₀ : Stacks.Divisors.picardClass D₀ =
      Stacks.Picard.schemePullbackClass φ (Stacks.Divisors.picardClass D) := by
    rw [Stacks.Divisors.schemePullbackClass_picardClass]
    exact Stacks.Divisors.picardClass_congr hD₀D
  have hι₀ : ∀ (T : Over (Spec (.of K))) (x y : (relativePicZeroFunctor K X₀.f).obj (op T)),
      (show T ⟶ A₀.J from A₀.ι.app (op T) (x + y)) =
        (show T ⟶ A₀.J from A₀.ι.app (op T) x) * (show T ⟶ A₀.J from A₀.ι.app (op T) y) :=
    fun T x y => A₀.map_add (op T) x y
  have hD₀rad : D₀.radical = D₀ := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
  have hM := schemePullbackClassHom_tensorHom_mumfordClass_eq_neg_vojtaClass X₀ x₀ rfl A₀ hι₀
    hg₀ j₀ hj₀ D₀ hD₀rad hD₀
  have hφ := Jacobian.ι_app_pullback_phiMap_theta_eq_inv X A hι hg j hj D hD K e⁻¹
  /- `j_K^* φ_θ(e⁻¹) = cl(P_K - P₀)`: both are sent to `e` by the bijection `ι(Spec K)`. -/
  let jKm : bc X.f T ⟶ (A.J ⊗ T).left :=
    pullback.map X.f T.hom A.J.hom T.hom j.left (𝟙 _) (𝟙 _)
      (by simp) (by simp)
  have hz : Stacks.Picard.schemePullbackClass jKm
      (AbelianVariety.phiMap A.J (Stacks.Divisors.picardClass D) e⁻¹) =
        Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀ := by
    obtain ⟨hdeg, hιz⟩ := hφ
    have hpt : (pointOfClosedPoint (pullback.snd X.f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))) x₀.1 x₀.2 ≫ pullback.fst X.f _) ≫ X.f =
          Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
        Category.id_comp]
    have h := smallEquiv_eq_of_ι_app_eq X A hdim ⟨Over.homMk _ hpt⟩ hdeg hdegₑ
      (hιz.trans (inv_inv e))
    rw [AddEquiv.apply_symm_apply] at h
    erw [(smallEquiv (bc X.f T)).apply_symm_apply] at h
    exact h
  /- The computation on `C_K ×_K C_K`, viewed as a `k`-scheme `S`, in terms of
  `F(x) = x^* θ` for `k`-morphisms `x : S ⟶ J`. -/
  let θ := Stacks.Divisors.picardClass D
  let S' : Over (Spec (.of K)) := Over.mk X₀.f ⊗ Over.mk X₀.f
  let S : Over (Spec (.of k)) := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj S'
  let Fθ : (S ⟶ A.J) → Stacks.Picard.ofScheme S.left := fun x =>
    Stacks.Picard.schemePullbackClass x.left θ
  let σ : S ⟶ T := Over.homMk S'.hom rfl
  have hF0 : ∀ t : T ⟶ A.J, Fθ (σ ≫ t) = 0 := fun t =>
    AbelianVariety.schemePullbackClass_comp_spec_field S'.hom t.left θ
  let ρ : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X.f)) ⟶ A.J :=
    P (Over.mk X.f) (𝟙 ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk X.f))) ≫ j
  let ι₁ : S ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X.f)) :=
    (Over.map _).map (CartesianMonoidalCategory.fst (Over.mk X₀.f) (Over.mk X₀.f))
  let ι₂ : S ⟶ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj (Over.mk X.f)) :=
    (Over.map _).map (CartesianMonoidalCategory.snd (Over.mk X₀.f) (Over.mk X₀.f))
  let q₁ := ι₁ ≫ ρ
  let q₂ := ι₂ ≫ ρ
  let r₁ : S ⟶ A.J := P A.J (CartesianMonoidalCategory.fst (Over.mk X₀.f) (Over.mk X₀.f) ≫ j₀)
  let r₂ : S ⟶ A.J := P A.J (CartesianMonoidalCategory.snd (Over.mk X₀.f) (Over.mk X₀.f) ≫ j₀)
  let a : S ⟶ A.J := (σ ≫ e)⁻¹
  have hL : Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f)
      (Stacks.Picard.schemePullbackClassHom (j ⊗ₘ j).left (deltaClass X A hg j hj _ hrad hsupp)) =
        Fθ q₁ + Fθ q₂ - Fθ (q₁ * q₂) := by
    refine pb_bcCC_deltaClass (K := K) X A hg j hj _ hrad hsupp q₁ q₂ ?_ ?_
    · change (CartesianMonoidalCategory.fst (Over.mk X₀.f) (Over.mk X₀.f)).left ≫
        (P (Over.mk X.f) (𝟙 _)).left ≫ j.left = _
      rw [P_left]
      rfl
    · change (CartesianMonoidalCategory.snd (Over.mk X₀.f) (Over.mk X₀.f)).left ≫
        (P (Over.mk X.f) (𝟙 _)).left ≫ j.left = _
      rw [P_left]
      rfl
  have hR : Stacks.Picard.schemePullbackClassHom (bcCC (K := K) X.f) (X.vojtaClass 0 0 1) =
      X₀.vojtaClass 0 0 1 +
        Stacks.Picard.schemePullbackClass (pullback.fst X₀.f X₀.f) classP₀ +
        Stacks.Picard.schemePullbackClass (pullback.snd X₀.f X₀.f) classP₀ -
        Stacks.Picard.schemePullbackClass (pullback.fst X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP) -
        Stacks.Picard.schemePullbackClass (pullback.snd X₀.f X₀.f)
          (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP) :=
    pb_bcCC_vojtaClass (K := K) X P₀ hP₀
  /- `j = j₀ · e⁻¹` on `C_K`. -/
  have hq₁ : q₁ = r₁ * a := by
    change ι₁ ≫ ρ = _
    rw [show ρ = _ from hrel, MonObj.comp_mul, GrpObj.comp_inv, ← P_comp_left, ← Category.assoc]
    congr 3
  have hq₂ : q₂ = r₂ * a := by
    change ι₂ ≫ ρ = _
    rw [show ρ = _ from hrel, MonObj.comp_mul, GrpObj.comp_inv, ← P_comp_left, ← Category.assoc]
    congr 3
    ext
    exact (pullback.condition (f := X₀.f) (g := X₀.f)).symm
  obtain ⟨b, hb0, hMk⟩ : ∃ b : S ⟶ A.J, Fθ b = 0 ∧
      Fθ (r₁ * r₂ * b) - Fθ (r₁ * b) - Fθ (r₂ * b) = -X₀.vojtaClass 0 0 1 :=
    exists_const_mumford A.J j₀ (eK ^ (genus X.f - 1)) θ hθ₀ hM
  let jK' : Over.mk X₀.f ⟶ JK := Over.homMk jKm (by
    change jKm ≫ pullback.snd _ _ = pullback.snd _ _
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _))
  have hPj : P A.J jK' = ρ := by
    ext
    rw [P_left, Over.comp_left, P_left]
    exact pullback.lift_fst _ _ _
  have hσa : (Over.homMk S'.hom : S ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
      e⁻¹ = a := by
    rw [GrpObj.comp_inv]
  have hφᵢ : ∀ v : S' ⟶ Over.mk X₀.f,
      Fθ ((Over.map _).map v ≫ ρ * a) - Fθ ((Over.map _).map v ≫ ρ) =
        Stacks.Picard.schemePullbackClass v.left
          (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀) := by
    intro v
    have h := pb_phiMap A.J jK' v θ e⁻¹
    rw [P_comp_left, hPj, hσa] at h
    exact h.symm.trans (congrArg (Stacks.Picard.schemePullbackClass v.left) hz)
  have hφ₁ : Fθ (q₁ * a) - Fθ q₁ = Stacks.Picard.schemePullbackClass (pullback.fst X₀.f X₀.f)
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀) :=
    hφᵢ (CartesianMonoidalCategory.fst _ _)
  have hφ₂ : Fθ (q₂ * a) - Fθ q₂ = Stacks.Picard.schemePullbackClass (pullback.snd X₀.f X₀.f)
      (Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP - classP₀) :=
    hφᵢ (CartesianMonoidalCategory.snd _ _)
  have haa : Fθ (a * a) = 0 := by
    rw [show a * a = σ ≫ (e⁻¹ * e⁻¹) by rw [MonObj.comp_mul, GrpObj.comp_inv]]
    exact hF0 _
  apply injective_bcCC (K := K) X
  exact eq_of_cube Fθ (AbelianVariety.schemePullbackClass_cube A.J θ) hq₁ hq₂ haa hb0 hL hR hMk
    (hφ₁.trans (pb_sub _ _ _)) (hφ₂.trans (pb_sub _ _ _))

end Faltings
