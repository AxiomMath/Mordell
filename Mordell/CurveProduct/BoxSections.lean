module
public import Mordell.AlgebraicGeometry.PicardPullback
public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqs
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import Mordell.Jacobian.AbelJacobi
public import Mordell.CurveProduct.VeryAmple

/-!
# Sections of a box product on a product of curves

Let `k` be a field and `C`, `D` smooth projective curves over `k` of genera `g_C`, `g_D`.
For invertible modules `𝒜` on `C` and `ℬ` on `D` of degrees `a > 2 g_C - 2` and
`b > 2 g_D - 2`, the space of global sections of the external tensor product
`pr₁^*𝒜 ⊗ pr₂^*ℬ` on `C ×_k D` has dimension `(a + 1 - g_C)(b + 1 - g_D)`.
Indeed `H¹(C, 𝒜) = H¹(D, ℬ) = 0` in these degrees, so Riemann–Roch gives
`dim_k H⁰(C, 𝒜) = a + 1 - g_C` and `dim_k H⁰(D, ℬ) = b + 1 - g_D`, and the Künneth formula
`AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap` in degree `0` identifies
`H⁰(C ×_k D, pr₁^*𝒜 ⊗ pr₂^*ℬ)` with `H⁰(C, 𝒜) ⊗_k H⁰(D, ℬ)`.

## Main results

* `Faltings.finrank_cohomologyOverField_externalTensorProduct_zero`: the dimension formula.

## Implementation notes

The source states the formula for `X = C × C`; it is stated here for a product `C ×_k D` of
two curves, which is the case `D = C`, `g = f` when the two curves agree. Cohomology is
`AlgebraicGeometry.cohomologyOverField` with its `k`-vector space structure, on
`pullback f g` with structure morphism `pullback.fst f g ≫ f`, and the box product is
`AlgebraicGeometry.externalTensorProduct f g 𝒜 ℬ`, exactly the target of the Künneth map.
Degrees are `AlgebraicGeometry.invertibleCurveDegree` and genera `AlgebraicGeometry.genus`;
the formula is an identity in `ℤ`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 0BEF], [Stacks Project, Tag 0AYR]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- On a smooth projective curve, an invertible module of degree `> 2g - 2` has
`dim_k H⁰ = deg + 1 - g`: Riemann–Roch, with `H¹ = 0` in degree `≥ 2g - 1`. -/
private theorem finrank_cohomologyOverField_zero_eq (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (A : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    (hA : 2 * (genus f : ℤ) - 2 <
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A) :
    (Module.finrank k (cohomologyOverField k f A 0) : ℤ) =
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A
        + 1 - genus f := by
  have : IsCurve k f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one f
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  have := ModuleCat.subsingleton_of_isZero <|
    isZero_cohomologyOverField_one_of_geometricallyIntegral k f A ‹_› (by omega)
  simpa [Module.finrank_zero_of_subsingleton] using
    finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A

/-- The Künneth formula in degree `0`: for quasi-compact, quasi-separated `X`, `Y` over `k` and
quasi-coherent `F`, `G`, `dim_k H⁰(X ×_k Y, pr₁^*F ⊗ pr₂^*G) = dim_k H⁰(X, F) · dim_k H⁰(Y, G)`. -/
private theorem finrank_cohomologyOverField_externalTensorProduct_zero_eq_mul {k : Type u}
    [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent] :
    Module.finrank k
        (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) 0) =
      Module.finrank k (cohomologyOverField k f F 0) *
        Module.finrank k (cohomologyOverField k g G 0) := by
  have := KunnethQcqs.isIso_kunnethMap f g F G 0
  -- the only pair of natural numbers with sum `0` is `(0, 0)`
  letI : Unique {pq : ℕ × ℕ // pq.1 + pq.2 = 0} :=
    { default := ⟨(0, 0), rfl⟩
      uniq := fun ⟨⟨a, b⟩, h⟩ => by ext <;> dsimp at h ⊢ <;> omega }
  rw [← (asIso (KunnethQcqs.kunnethMap f g F G 0)).toLinearEquiv.finrank_eq,
    ((DirectSum.linearEquivFunOnFintype k _ _).trans (LinearEquiv.piUnique k _)).finrank_eq,
    Module.finrank_tensorProduct]
  rfl

/-- For smooth projective curves `f : C ⟶ Spec k`, `g : D ⟶ Spec k` and invertible modules
`A` on `C`, `B` on `D` with `deg A > 2 genus f - 2` and `deg B > 2 genus g - 2`,
`dim_k H⁰(C ×_k D, pr₁^* A ⊗ pr₂^* B) = (deg A + 1 - genus f) (deg B + 1 - genus g)`. -/
@[faltings "lem_nt_h0_box_formula"]
public theorem finrank_cohomologyOverField_externalTensorProduct_zero (k : Type u) [Field k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) (g : D ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve k g] (A : C.Modules) (B : D.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible D.presheaf D.ringCatSheaf.2 B]
    (hA : 2 * (genus f : ℤ) - 2 <
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A)
    (hB : 2 * (genus g : ℤ) - 2 <
      invertibleCurveDegree k g (topologicalKrullDim_le_one_of_smoothOfRelativeDimension g) B) :
    (Module.finrank k
        (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g A B) 0) : ℤ) =
      (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A
          + 1 - genus f) *
        (invertibleCurveDegree k g (topologicalKrullDim_le_one_of_smoothOfRelativeDimension g) B
          + 1 - genus g) := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have : CompactSpace D := (quasiCompact_iff_compactSpace g).mp inferInstance
  have : QuasiSeparatedSpace D := (quasiSeparated_iff_quasiSeparatedSpace g).mp inferInstance
  have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property A := ‹_›
  have : SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property B := ‹_›
  have : A.IsQuasicoherent := isQuasicoherent_of_isInvertible A
  have : B.IsQuasicoherent := isQuasicoherent_of_isInvertible B
  rw [finrank_cohomologyOverField_externalTensorProduct_zero_eq_mul, Nat.cast_mul,
    finrank_cohomologyOverField_zero_eq k f A hA, finrank_cohomologyOverField_zero_eq k g B hB]

end Faltings


/-!
# Sections of `δ₁ (N P) × C + δ₂ C × (N P)`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g`, and
let `X = C ×_k C`. For integers `N, δ₁, δ₂ ≥ 1` with `N δ₁ > 2g - 2` and `N δ₂ > 2g - 2`, the
divisor `δ₁ (N P) × C + δ₂ C × (N P)` is the external tensor product
`pr₁^* 𝒪_C(N δ₁ P) ⊗ pr₂^* 𝒪_C(N δ₂ P)`, of degrees `N δᵢ > 2g - 2` on the factors, so the
Künneth formula and Riemann–Roch on `C` give
`h⁰(X, 𝒪_X(δ₁ (N P) × C + δ₂ C × (N P))) = (N δ₁ + 1 - g)(N δ₂ + 1 - g)
  = N² δ₁ δ₂ - N (g - 1)(δ₁ + δ₂) + (g - 1)²`.

## Main results

* `CurveWithDegreeOneDivisor.finrank_cohomologyOverField_zero_of_picardClass_eq_vojtaClass`:
  the dimension formula, for every invertible module on `C ×_k C` in the class of the divisor.

## Implementation notes

The divisor enters through its class in `Pic(C ×_k C)`: `δ₁ (N P) × C + δ₂ C × (N P)` has
class `Faltings.CurveWithDegreeOneDivisor.vojtaClass X (N * δ₁) (N * δ₂) 0`, the coefficient of
`Δ'` being zero. Since `h⁰` depends only on the isomorphism class, the statement is made for
every invertible `𝒪_X`-module `L` whose class `Stacks.SheafOfModules.picardClass` is that
class, rather than for one chosen representative. Cohomology is
`AlgebraicGeometry.cohomologyOverField` over the structure morphism
`pullback.fst X.f X.f ≫ X.f` of `C ×_k C`, and the formula is an identity in `ℤ`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 8
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings.CurveWithDegreeOneDivisor

/-- `dim_k Hⁿ` is an isomorphism invariant of the module. -/
private lemma finrank_cohomologyOverField_congr (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) {F G : Y.Modules} (e : F ≅ G) (n : ℕ) :
    Module.finrank k (cohomologyOverField k f F n) =
      Module.finrank k (cohomologyOverField k f G n) :=
  ((ModuleCat.restrictScalars _).mapIso
    (((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)).rightDerived n).mapIso
      e)).toLinearEquiv.finrank_eq

/-- A box product `pr₁^* A ⊗ pr₂^* B` of invertible modules is invertible. -/
private lemma isInvertible_externalTensorProduct {S C D : Scheme.{u}} (f : C ⟶ S) (g : D ⟶ S)
    (A : C.Modules) (B : D.Modules)
    (hA : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) A)
    (hB : Stacks.SheafOfModules.IsInvertible D.presheaf
      (Stacks.RingedSpace.structureIsSheaf D.toRingedSpace) B) :
    Stacks.SheafOfModules.IsInvertible (pullback f g).presheaf
      (pullback f g).ringCatIsSheaf (externalTensorProduct f g A B) :=
  have : Stacks.Ample.IsInvertibleModule C A :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ A).mp hA
  have : Stacks.Ample.IsInvertibleModule D B :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ B).mp hB
  @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ (pullback f g).presheaf
    (Stacks.RingedSpace.structureIsSheaf (pullback f g).toRingedSpace) _ _ _ _
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.fst f g) A))
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd f g) B))

/-- An invertible module on `C` of class `n [𝒪_C(P)]` has degree `n`. -/
private lemma invertibleCurveDegree_of_picardClass_eq_zsmul_classP {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (hdim : topologicalKrullDim X.C ≤ 1) (n : ℤ)
    (A : X.C.Modules) (hA : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) A)
    (h : Stacks.SheafOfModules.picardClass X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) A hA = n • X.classP) :
    invertibleCurveDegree k X.f hdim A = n := by
  rw [← invertibleCurveDegreeHom_picardClass k X.f hdim A hA, h, map_zsmul,
    X.invertibleCurveDegreeHom_classP, smul_eq_mul, mul_one]

/-- **The class of a box product.** For invertible `A`, `B` on `C` of classes `a [𝒪_C(P)]` and
`b [𝒪_C(P)]`, the box product `pr₁^* A ⊗ pr₂^* B` has class `vojtaClass a b 0`. -/
private lemma picardClass_externalTensorProduct {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (a b : ℤ) (A B : X.C.Modules)
    (hA : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) A)
    (hB : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) B)
    (hAP : Stacks.SheafOfModules.picardClass X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) A hA = a • X.classP)
    (hBP : Stacks.SheafOfModules.picardClass X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) B hB = b • X.classP)
    (hE : Stacks.SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf (externalTensorProduct X.f X.f A B)) :
    Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf (externalTensorProduct X.f X.f A B) hE =
        X.vojtaClass a b 0 := by
  have : Stacks.Ample.IsInvertibleModule X.C A :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ A).mp hA
  have : Stacks.Ample.IsInvertibleModule X.C B :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ B).mp hB
  have hA' := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr (Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.fst X.f X.f) A)
  have hB' := (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    _ _ _).mpr (Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd X.f X.f) B)
  refine (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hA' hB' hE).symm.trans ?_
  refine (congrArg₂ (· + ·)
    ((schemePullbackClassHom_picardClass (pullback.fst X.f X.f) A hA).symm.trans
      (congrArg (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f)) hAP))
    ((schemePullbackClassHom_picardClass (pullback.snd X.f X.f) B hB).symm.trans
      (congrArg (Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f)) hBP))).trans ?_
  rw [map_zsmul, map_zsmul, vojtaClass, zero_smul, add_zero]
  rfl

variable {k : Type u} [Field k]

/-- Let `X = (C, P)` be a curve with a divisor of degree one, of genus `g = genus X.f`, and
`N, δ₁, δ₂ ≥ 1` with `N δ₁ > 2g - 2` and `N δ₂ > 2g - 2`. For every invertible module `L` on
`C ×_k C` in the class `vojtaClass X (N * δ₁) (N * δ₂) 0` of `δ₁ (N P) × C + δ₂ C × (N P)`,
`dim_k H⁰(C ×_k C, L) = N² δ₁ δ₂ - N (g - 1)(δ₁ + δ₂) + (g - 1)²`. -/
@[faltings "lem_nt_h0_box_product"]
public theorem finrank_cohomologyOverField_zero_of_picardClass_eq_vojtaClass
    (X : CurveWithDegreeOneDivisor k) (N δ₁ δ₂ : ℤ) (hN : 1 ≤ N) (hδ₁ : 1 ≤ δ₁) (hδ₂ : 1 ≤ δ₂)
    (h₁ : 2 * (genus X.f : ℤ) - 2 < N * δ₁) (h₂ : 2 * (genus X.f : ℤ) - 2 < N * δ₂)
    (L : (pullback X.f X.f).Modules)
    (hLinv : Stacks.SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf L)
    (hL : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf L hLinv = X.vojtaClass (N * δ₁) (N * δ₂) 0) :
    (Module.finrank k (cohomologyOverField k (pullback.fst X.f X.f ≫ X.f) L 0) : ℤ) =
      N ^ 2 * δ₁ * δ₂ - N * ((genus X.f : ℤ) - 1) * (δ₁ + δ₂) + ((genus X.f : ℤ) - 1) ^ 2 := by
  have hdim := topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  -- `𝒪_C(N δ₁ P)` and `𝒪_C(N δ₂ P)`
  obtain ⟨A, hAs, hA⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.C.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) ((N * δ₁) • X.classP)
  obtain ⟨B, hBs, hB⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.C.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) ((N * δ₂) • X.classP)
  have hE := isInvertible_externalTensorProduct X.f X.f A B hAs hBs
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ L _ hLinv hE).1
    (hL.trans (picardClass_externalTensorProduct X _ _ A B hAs hBs hA hB hE).symm)
  have : Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatSheaf.2 A := hAs
  have : Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatSheaf.2 B := hBs
  have hdegA := invertibleCurveDegree_of_picardClass_eq_zsmul_classP X hdim _ A hAs hA
  have hdegB := invertibleCurveDegree_of_picardClass_eq_zsmul_classP X hdim _ B hBs hB
  rw [finrank_cohomologyOverField_congr k _ e,
    finrank_cohomologyOverField_externalTensorProduct_zero k X.f X.f A B
      (by rwa [hdegA]) (by rwa [hdegB]), hdegA, hdegB]
  ring

end Faltings.CurveWithDegreeOneDivisor
