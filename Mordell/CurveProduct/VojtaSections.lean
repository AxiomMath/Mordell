module

public import Mathlib
public import Mordell.Attr
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Surface
public import Mordell.CurveProduct.BoxEulerCharacteristic
public import Mordell.AlgebraicGeometry.Surface.NegativeIntersectionSections
public import Mordell.CurveProduct.VeryAmple
public import Mordell.CurveProduct.H1Ample
public import Mordell.CurveProduct.IntersectionHN
public import Mordell.CurveProduct.VojtaIntersection
public import Mordell.AlgebraicGeometry.Surface.RiemannRochInequality
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqs

/-!
# Sections of the Vojta divisor

Let `(C, P)` be a curve of genus `g` over a field `k` with a divisor `P` of degree one, let
`X = C ×_k C`, and for integers `d₁, d₂, d` let `V = d₁ (P × C) + d₂ (C × P) + d Δ'`, where
`Δ' = Δ - P × C - C × P` and `Δ` is the diagonal. If `d₁ + d₂ > 4g - 4`, then

`h⁰(X, 𝒪_X(V)) ≥ d₁ d₂ - g d² - (g - 1)(d₁ + d₂) + (g - 1)²`.

The proof is the Riemann–Roch inequality on the surface `X`: `h⁰(K_X - V) = 0` because `V`
meets the ample class `H_N` more than `K_X` does, and `V² = 2 (d₁ d₂ - g d²)`,
`K_X · V = (2g - 2)(d₁ + d₂)`, `χ(𝒪_X) = (1 - g)²`.

## Main results

* `CurveWithDegreeOneDivisor.le_finrank_cohomologyOverField_zero_of_picardClass_eq_vojtaClass`:
  the lower bound above, for every invertible `𝒪_X`-module of class
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass X d₁ d₂ d`.

## Implementation notes

The divisor `V` enters through its class `vojtaClass X d₁ d₂ d` in `Pic(X)`. Since `h⁰` is
an invariant of the isomorphism class, `h⁰(𝒪_X(V))` is stated for an arbitrary invertible
`𝒪_X`-module `L` whose class `Stacks.SheafOfModules.picardClass` is `vojtaClass X d₁ d₂ d`;
`h⁰(X, L)` is `Module.finrank k` of `AlgebraicGeometry.cohomologyOverField` in degree `0` for
the structure morphism `pr₁ ≫ f` of `X` over `k`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 4 and Section 8
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {k : Type u} [Field k]

/-- The twist `K ⊗ L^{⊗ -1}` of an invertible module by the inverse of another is invertible,
of class `[K] - [L]`. -/
private lemma picardClass_twistedSheaf_neg_one {Y : Scheme.{u}} (K L : Y.Modules)
    [hK : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 K]
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    ∃ h : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (twistedSheaf K (fun _ : Fin 1 => L) (fun _ => -1)),
      Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf
          (twistedSheaf K (fun _ : Fin 1 => L) (fun _ => -1)) h =
        Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf K hK -
          Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf L hL := by
  have hP := Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower Y.presheaf
    Y.ringCatIsSheaf L (-1)
  have hT := Stacks.SheafOfModules.isInvertible_tensorSheaf Y.presheaf Y.ringCatIsSheaf K
    (Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf Y.ringCatIsSheaf L (-1))
  refine ⟨hT, ?_⟩
  rw [sub_eq_add_neg]
  refine (Stacks.SheafOfModules.picardClass_tensorSheaf Y.presheaf Y.ringCatIsSheaf K _ hK hP
    hT).symm.trans ?_
  congr 1
  exact Stacks.SheafOfModules.picardClass_tensorPower_neg_one Y.presheaf Y.ringCatIsSheaf L

/-- On a scheme over `k`, `H⁰` of a module without nonzero global sections vanishes. -/
private lemma finrank_cohomologyOverField_zero_eq_zero (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) (h : Subsingleton (M.val.obj (op ⊤))) :
    Module.finrank k (cohomologyOverField k f M 0) = 0 := by
  let ev := SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))
  have : PreservesFiniteLimits ev :=
    _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits Y.ringCatSheaf _
  have : Subsingleton (cohomologyOverField k f M 0) :=
    ((ev.rightDerivedZeroIsoSelf.app M).toLinearEquiv.toEquiv).subsingleton_congr.2 h
  exact Module.finrank_zero_of_subsingleton

/-- The intersection form on `Pic(Y)` at the classes of two invertible modules is their
intersection number. -/
private lemma picardIntersection_pair (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsProper f] (hd : topologicalKrullDim Y ≤ (2 : ℕ)) (L M : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    picardIntersection k f (𝟙 Y) 2 hd
        ![Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf L hL,
          Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf M hM] =
      @intersectionNumber k _ Y Y f _ (𝟙 Y) _ 2 hd ![L, M] (Fin.forall_fin_two.2 ⟨hL, hM⟩) := by
  haveI : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L, M] q) :=
    Fin.forall_fin_two.2 ⟨hL, hM⟩
  convert picardIntersection_picardClass k f (𝟙 Y) 2 hd ![L, M] using 2
  ext q
  fin_cases q <;> rfl

/-- The intersection number of two invertible modules is symmetric. -/
private lemma intersectionNumber_pair_comm (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsProper f] (hd : topologicalKrullDim Y ≤ (2 : ℕ)) (L M : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] :
    @intersectionNumber k _ Y Y f _ (𝟙 Y) _ 2 hd ![L, M] (Fin.forall_fin_two.2 ⟨hL, hM⟩) =
      @intersectionNumber k _ Y Y f _ (𝟙 Y) _ 2 hd ![M, L] (Fin.forall_fin_two.2 ⟨hM, hL⟩) := by
  haveI : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![M, L] q) :=
    Fin.forall_fin_two.2 ⟨hM, hL⟩
  haveI : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L, M] q) :=
    Fin.forall_fin_two.2 ⟨hL, hM⟩
  refine (intersectionNumber_congr_family k f (𝟙 Y) 2 hd ?_).trans
    (intersectionNumber_comp_perm k f (𝟙 Y) 2 hd ![M, L] (Equiv.swap 0 1))
  ext q
  fin_cases q <;> rfl

/-- A bilinear form is additive in its second argument: `I(c, a - b) = I(c, a) - I(c, b)`. -/
private lemma multilinearMap_fin_two_sub {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : MultilinearMap R (fun _ : Fin 2 => M) N)
    (c a b : M) : I ![c, a - b] = I ![c, a] - I ![c, b] := by
  have h := (I.curryLeft c).cons_add Fin.elim0 (a - b) b
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- `h⁰(X, K_X - V) = 0` when `d₁ + d₂ > 4g - 4`: the ample class `H₁` meets `K_X - V` in
`4(g - 1) - (d₁ + d₂) < 0`. -/
private lemma finrank_cohomologyOverField_canonical_sub_vojta_eq_zero {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ) (hd : 4 * (genus X.f : ℤ) - 4 < d₁ + d₂)
    (L : (pullback X.f X.f).Modules)
    [hLinv : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2 L]
    (hL : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf L hLinv = X.vojtaClass d₁ d₂ d) :
    haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
      (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
      (pullback.fst X.f X.f ≫ X.f) 2
    haveI : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
        (pullback X.f X.f).ringCatSheaf.2
        (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2) :=
      (Scheme.Modules.isInvertible_exteriorPower_self _ 2).toAlgebraicGeometry
    Module.finrank k (cohomologyOverField k (pullback.fst X.f X.f ≫ X.f)
      (twistedSheaf
        (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2)
        (fun _ : Fin 1 => L) (fun _ => -1)) 0) = 0 := by
  obtain ⟨_, _, _⟩ := IsSmoothProjectiveCurve.surface_pullback k X.f X.f
  haveI : Nonempty ↥(pullback X.f X.f : Scheme.{u}) :=
    ⟨(pullback.diagonal X.f).base (Classical.arbitrary X.C)⟩
  have hX :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (pullback.fst X.f X.f ≫ X.f)
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
    (pullback.fst X.f X.f ≫ X.f) 2
  haveI hK : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2) :=
    (Scheme.Modules.isInvertible_exteriorPower_self _ 2).toAlgebraicGeometry
  haveI : IsIntegral (pullback X.f X.f : Scheme.{u}) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst X.f X.f ≫ X.f)
  obtain ⟨hHV, hHK⟩ := picardIntersection_vojtaClass_hN_and_canonical X 1 d₁ d₂ d
  rw [← hL] at hHV
  obtain ⟨H, hHinv, hHample, hHcl⟩ := exists_isAmple_picardClass_eq_vojtaClass_one_one_zero X
  obtain ⟨hMinv, hMcl⟩ := picardClass_twistedSheaf_neg_one
    (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2) L
  have hHM : @intersectionNumber k _ _ _ (pullback.fst X.f X.f ≫ X.f) _ (𝟙 _) _ 2 hX.le
      ![H, twistedSheaf
        (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2)
        (fun _ : Fin 1 => L) (fun _ => -1)] (Fin.forall_fin_two.2 ⟨hHinv, hMinv⟩) < 0 := by
    rw [← @picardIntersection_pair k _ _ _ _ hX.le _ _ hHinv hMinv, hMcl, hHcl,
      multilinearMap_fin_two_sub]
    linarith
  exact finrank_cohomologyOverField_zero_eq_zero k _ _ <|
    @subsingleton_sections_of_intersectionNumber_neg k _ _ _
      (pullback.fst X.f X.f ≫ X.f) _ hX H _ hHinv hMinv hHample hHM

/-- For a curve `(C, P)` of genus `g` with a divisor of degree one, `X = C ×_k C`, and integers
with `d₁ + d₂ > 4g - 4`, every invertible `𝒪_X`-module `L` of class
`vojtaClass X d₁ d₂ d = [𝒪_X(d₁ (P × C) + d₂ (C × P) + d Δ')]` satisfies
`dim_k H⁰(X, L) ≥ d₁ d₂ - g d² - (g - 1)(d₁ + d₂) + (g - 1)²`. -/
@[faltings "lem_nt_h0_vojta_divisor"]
theorem le_finrank_cohomologyOverField_zero_of_picardClass_eq_vojtaClass
    (X : CurveWithDegreeOneDivisor k) (d₁ d₂ d : ℤ)
    (hd : 4 * (genus X.f : ℤ) - 4 < d₁ + d₂)
    (L : (pullback X.f X.f).Modules)
    [hLinv : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2 L]
    (hL : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatIsSheaf L hLinv = X.vojtaClass d₁ d₂ d) :
    d₁ * d₂ - genus X.f * d ^ 2 - (genus X.f - 1) * (d₁ + d₂) + (genus X.f - 1) ^ 2 ≤
      (Module.finrank k
        (cohomologyOverField k (pullback.fst X.f X.f ≫ X.f) L 0) : ℤ) := by
  obtain ⟨_, _, _⟩ := IsSmoothProjectiveCurve.surface_pullback k X.f X.f
  haveI : Nonempty ↥(pullback X.f X.f : Scheme.{u}) :=
    ⟨(pullback.diagonal X.f).base (Classical.arbitrary X.C)⟩
  have hX :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (pullback.fst X.f X.f ≫ X.f)
  have RR := riemannRoch_inequality_surface k (pullback.fst X.f X.f ≫ X.f) hX L
  obtain ⟨hVV, hKV⟩ := picardIntersection_vojtaClass_self_and_canonical X d₁ d₂ d
  rw [← hL] at hVV hKV
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
    (pullback.fst X.f X.f ≫ X.f) 2
  haveI : SheafOfModules.IsInvertible (pullback X.f X.f).presheaf
      (pullback X.f X.f).ringCatSheaf.2
      (Scheme.Modules.exteriorPower (pullback.fst X.f X.f ≫ X.f).relativeDifferentials 2) :=
    (Scheme.Modules.isInvertible_exteriorPower_self _ 2).toAlgebraicGeometry
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (pullback.fst X.f X.f ≫ X.f)
  -- `V² = 2 (d₁ d₂ - g d²)`, `V · K_X = (2g - 2)(d₁ + d₂)`, `h⁰(K_X - V) = 0`, `χ(𝒪_X) = (1 - g)²`
  rw [(picardIntersection_pair k _ hX.le L L).symm.trans hVV,
    (intersectionNumber_pair_comm k _ hX.le L _).trans
      ((picardIntersection_pair k _ hX.le _ L).symm.trans hKV),
    finrank_cohomologyOverField_canonical_sub_vojta_eq_zero X d₁ d₂ d hd L hL,
    eulerCharacteristic_unit_pullback k X.f] at RR
  have key : ((d₁ * d₂ - genus X.f * d ^ 2 - (genus X.f - 1) * (d₁ + d₂) + (genus X.f - 1) ^ 2 :
      ℤ) : ℚ) ≤ ((Module.finrank k
        (cohomologyOverField k (pullback.fst X.f X.f ≫ X.f) L 0) : ℤ) : ℚ) := by
    push_cast at RR ⊢
    linarith
  exact_mod_cast key

end Faltings.CurveWithDegreeOneDivisor
