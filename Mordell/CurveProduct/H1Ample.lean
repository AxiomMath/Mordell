module

public import Mordell.CurveProduct.VeryAmple
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower

/-!
# The class `H₁` on `C × C` is ample

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, and let
`pr₁, pr₂ : C ×_k C ⟶ C` be the projections. The class
`H₁ = pr₁^*[𝒪_C(P)] + pr₂^*[𝒪_C(P)]` in `Pic(C ×_k C)`, the class of
`pr₁^* 𝒪_C(P) ⊗ pr₂^* 𝒪_C(P)`, is ample: it is represented by an ample invertible sheaf.
For `N ≥ 2g + 1` its `N`-th multiple `H_N` is very ample, and an invertible sheaf with a very
ample power is ample.

## Main results

* `Faltings.picardClass_tensorPowModule`: on any scheme `Y`, the class of the tensor power
  `L^{⊗ d}` of an invertible sheaf is `d • [L]` in `Pic(Y)`.
* `Faltings.CurveWithDegreeOneDivisor.exists_isAmple_picardClass_eq_vojtaClass_one_one_zero`:
  some ample invertible sheaf on `C ×_k C` has class `vojtaClass 1 1 0 = H₁`.

## Implementation notes

`H₁` is `Faltings.CurveWithDegreeOneDivisor.vojtaClass X 1 1 0`, the class
`pr₁^*[𝒪_C(P)] + pr₂^*[𝒪_C(P)]` in the additive group `Stacks.Picard.ofScheme`. Ampleness is a
property of invertible sheaves (`AlgebraicGeometry.Scheme.Modules.IsAmple`) invariant under
isomorphism, so a class is ample when it is the class
`Stacks.SheafOfModules.picardClass` of an ample invertible sheaf.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks, Tag 01VT]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-- The class in `Pic(Y)` of the tensor power `L^{⊗ d}` is `d • [L]`. -/
theorem picardClass_tensorPowModule (Y : Scheme.{u}) (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] (d : ℤ) :
    Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) (Stacks.Ample.tensorPowModule Y L d)
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr inferInstance) =
      d • Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr inferInstance) := by
  refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_schemeTensorPower Y L _ d)
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    ⟨(Stacks.PowerFamilyBridge.tensorPowerModuleIso Y L d).symm⟩

namespace CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- `H_N = N • H₁`: the class `vojtaClass X N N 0` is `N` times `vojtaClass X 1 1 0`. -/
private theorem vojtaClass_self_self_zero (X : CurveWithDegreeOneDivisor k) (N : ℤ) :
    X.vojtaClass N N 0 = N • X.vojtaClass 1 1 0 := by
  have key : ∀ a b c : Stacks.Picard.ofScheme (pullback X.f X.f),
      N • a + N • b + (0 : ℤ) • c = N • ((1 : ℤ) • a + (1 : ℤ) • b + (0 : ℤ) • c) := by
    intro a b c
    rw [zero_zsmul, add_zero, add_zero, one_zsmul, one_zsmul, zsmul_add]
  exact key _ _ _

/-- On `C ×_k C`, for a curve `C` with a divisor `P` of degree one, the class
`H₁ = pr₁^*[𝒪_C(P)] + pr₂^*[𝒪_C(P)]` (`vojtaClass X 1 1 0`) is ample: it is the class of an
ample invertible sheaf. -/
@[faltings "lem_nt_h1_ample"]
theorem exists_isAmple_picardClass_eq_vojtaClass_one_one_zero
    (X : CurveWithDegreeOneDivisor k) :
    ∃ (L : (pullback X.f X.f).Modules)
      (_ : SheafOfModules.IsInvertible (pullback X.f X.f).toRingedSpace.presheaf
        (structureSheafRing (pullback X.f X.f).toRingedSpace).property L),
      Scheme.Modules.IsAmple (pullback X.f X.f) L ∧
      Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L ‹_›) =
        X.vojtaClass 1 1 0 := by
  -- an invertible `L` of class `H₁`: the chosen representative of the class
  let R := Stacks.Picard.picardRepresentative (pullback X.f X.f).toRingedSpace
    (X.vojtaClass 1 1 0)
  let L : (pullback X.f X.f).Modules := R.obj
  haveI hL : Stacks.Ample.IsInvertibleModule (pullback X.f X.f) L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
      R.property
  have hcls : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) L
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr inferInstance) = X.vojtaClass 1 1 0 :=
    Stacks.Picard.classOf_picardRepresentative _ _
  refine ⟨L, hL, ?_, hcls⟩
  -- `L^{⊗ d}` has class `H_d`, very ample for `d ≥ 2g + 1`, so `L` is ample (Tag 01VT)
  apply Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple
  rw [Stacks.AmpleRelativeFiniteType.isAmple_iff_eventually_isRelativelyVeryAmple
    (pullback.fst X.f X.f ≫ X.f)]
  refine ⟨(2 * (genus X.f : ℤ) + 1).toNat, by omega, fun d hd => ?_⟩
  refine isRelativelyVeryAmple_of_picardClass_eq_vojtaClass X d (by omega) _ ?_
  rw [picardClass_tensorPowModule, hcls, vojtaClass_self_self_zero X d]

end CurveWithDegreeOneDivisor

end Faltings
