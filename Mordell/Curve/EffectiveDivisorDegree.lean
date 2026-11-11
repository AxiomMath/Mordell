module
public import Mordell.Curve.PointClass
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingDiagonal
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingCartier
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankDisjointCover
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveResolution
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# Degrees of effective divisors on a curve

Let `(C, P)` be a curve over a field `k` with a divisor of degree one. An effective Cartier divisor
`E` on `C` is finite locally free of some rank `r` over `k`, and `deg 𝒪_C(E) = r`; a divisor of
rank zero is empty, with trivial class. If the support of `E` contains `n` rational points, then
`deg 𝒪_C(E) ≥ n`. An invertible module with `h⁰ = 1` and `h¹ = 0` has a nonzero global section.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.invertibleCurveDegreeHom_picardClass_of_rank`: the degree
  of an effective Cartier divisor is its rank over `k`.
* `Faltings.picardClass_eq_zero_of_rank_zero`: an effective Cartier divisor of rank zero over a
  field has trivial class.
* `Faltings.CurveWithDegreeOneDivisor.card_le_invertibleCurveDegreeHom_picardClass`: an effective
  Cartier divisor whose support contains `n` rational points has degree at least `n`.
* `Faltings.CurveWithDegreeOneDivisor.exists_section_ne_zero`: an invertible module with
  one-dimensional `H⁰` and no `H¹` on its fibre over `k` has a nonzero global section.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **A module with one-dimensional `H⁰` and no `H¹` on its fibre over `k` has a nonzero
section.** -/
public lemma CurveWithDegreeOneDivisor.exists_section_ne_zero
    (X : CurveWithDegreeOneDivisor k) (U : Stacks.TwoAffineCech.Cover.{u} → X.C.Opens)
    (hU : (⊤ : X.C.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
    (N : X.C.Modules) [Stacks.Ample.IsInvertibleModule X.C N]
    (h1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f N t 1) = 0)
    (h0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology X.f N t 0) = 1) :
    ∃ s : Γ(N, ⊤), s ≠ 0 := by
  classical
  have : N.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N
  by_contra hall
  push Not at hall
  have hk : IsPullback (𝟙 X.C) X.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]
    have hid : IsIso (𝟙 (Spec (CommRingCat.of k))) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
    have hidX : IsIso (𝟙 X.C) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hidX hid
      ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
  have hd : Function.Surjective (Stacks.TwoAffineCech.cechD X.f U N) :=
    Stacks.TwoAffineCech.surjective_cechD_of_isPullback X.f U hU hUaff (𝟙 X.C) X.f hk N h1
  have hker : ∀ c : LinearMap.ker (Stacks.TwoAffineCech.cechD X.f U N), c = 0 := by
    intro c
    obtain ⟨t, rfl⟩ := Stacks.TwoAffineCech.exists_sectionCocycle_eq X.f U N hU c
    rw [hall t]
    exact Subtype.ext (Subtype.ext (Stacks.TwoAffineCech.sectionCochain_zero U N))
  have : Subsingleton (LinearMap.ker (Stacks.TwoAffineCech.cechD X.f U N)) :=
    ⟨fun a b => (hker a).trans (hker b).symm⟩
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := Stacks.TwoAffineCech.finrank_cohomologyOverField_zero_eq X.f U N hU hUaff p
  rw [Stacks.TwoAffineCech.finrank_fibre_eq_fibreCohomology] at h
  have e1 := h0 (Stacks.TwoAffineCech.specPoint p)
  have e2 := (Stacks.TwoTermComplex.baseChangeKerEquiv _ hd p.asIdeal.ResidueField).finrank_eq
  have e3 : Module.finrank p.asIdeal.ResidueField (TensorProduct k p.asIdeal.ResidueField
      (LinearMap.ker (Stacks.TwoAffineCech.cechD X.f U N))) = 0 :=
    Module.finrank_zero_of_subsingleton
  exact one_ne_zero (e1.symm.trans (h.trans (e2.symm.trans e3)))

/-- An effective Cartier divisor of rank zero over a field is empty, so its class is zero. -/
public lemma picardClass_eq_zero_of_rank_zero {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k))
    (I : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ fY) 0) :
    Stacks.Divisors.picardClass I = 0 := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ fY).appTop).hom.toAlgebra
  obtain ⟨-, hfin, h0⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ 0).1 h
  have hsub : Subsingleton Γ(I.subscheme, ⊤) := Module.finrank_zero_iff.1 h0
  have hemp : IsEmpty I.subscheme := ⟨fun x => by
    have := (I.subscheme.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
    exact not_subsingleton _ hsub⟩
  have hsupp : I.support = ⊥ := by
    ext x
    simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hx
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨y, -⟩ := hx
    exact hemp.false y
  rw [Scheme.IdealSheafData.support_eq_bot_iff] at hsupp
  rw [Stacks.Divisors.picardClass_congr hsupp]
  exact Stacks.Divisors.picardClass_top

/-- The degree of an effective Cartier divisor on `C` is its rank over `k`. -/
public lemma CurveWithDegreeOneDivisor.invertibleCurveDegreeHom_picardClass_of_rank
    (X : CurveWithDegreeOneDivisor k) (I : X.C.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] {r : ℕ}
    (hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ X.f) r) :
    invertibleCurveDegreeHom k X.f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
      (Stacks.Divisors.picardClass I) = r := by
  obtain ⟨d, hd, hdeg⟩ := exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree
    k X.f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f) I
  rw [invertibleCurveDegreeHom_picardClass k X.f _ (Stacks.Divisors.invertibleSheaf' I)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard I)]
  refine hdeg.symm.trans ?_
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ X.f).appTop).hom.toAlgebra
  have e1 := ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ d).1 hd).2.2
  have e2 := ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ r).1 hr).2.2
  exact_mod_cast e1.symm.trans e2

omit [Field k] in
/-- An effective Cartier divisor on an integral scheme does not contain the generic point. -/
public lemma support_ne_univ_of_isEffectiveCartierDivisor {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (I : Y.IdealSheafData)
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] :
    (I.support : Set Y) ≠ Set.univ := fun h => by
  have hmem := Set.mem_univ (genericPoint Y)
  rw [← h] at hmem
  exact genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hI hmem

/-- **Degree at least the number of rational points of the support**: an effective Cartier
divisor on `C` whose support contains `n` closed points of degree one has degree at least `n`. -/
public lemma CurveWithDegreeOneDivisor.card_le_invertibleCurveDegreeHom_picardClass
    (X : CurveWithDegreeOneDivisor k)
    (S : Finset {x : X.C // IsClosed ({x} : Set X.C)})
    (hS1 : ∀ x ∈ S, X.f.residueDegree x.1 = 1) :
    ∀ (E : X.C.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E],
      (∀ x ∈ S, x.1 ∈ E.support) →
      (S.card : ℤ) ≤ invertibleCurveDegreeHom k X.f
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
        (Stacks.Divisors.picardClass E) := by
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : IsNoetherian X.C := isNoetherian_of_locallyOfFiniteType (Y := Spec (.of k)) X.f
  have : IsIntegral X.C := inferInstance
  have hreg : IsRegular X.C := isRegular_of_smooth_over_regular X.f
  have hdimC : topologicalKrullDim X.C ≤ 1 :=
    topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f
  induction S using Finset.induction_on with
  | empty =>
    intro E _ _
    obtain ⟨d, hd, -⟩ :=
      exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree k X.f hdimC E
    rw [X.invertibleCurveDegreeHom_picardClass_of_rank E hd]
    simp
  | insert x S hx ih =>
    intro E hE hSE
    have hP := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
    have hEP : E ≤ Stacks.Zeta.pointIdeal x := by
      rw [Stacks.Zeta.pointIdeal, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact hSE x (Finset.mem_insert_self _ _)
    obtain ⟨dE, hdE, -⟩ :=
      exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree k X.f hdimC E
    obtain ⟨dP, hdP, -⟩ :=
      exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree k X.f hdimC
        (Stacks.Zeta.pointIdeal x)
    have := hdE
    have := hdP
    obtain ⟨R, hR, -⟩ := exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le X.f
      (Stacks.Zeta.pointIdeal x) E dP dE hEP
    have hRc : Stacks.Divisors.IsEffectiveCartierDivisor R :=
      isEffectiveCartierDivisor_of_isRegular_of_support_ne_univ hdimC hreg R (fun h =>
        support_ne_univ_of_isEffectiveCartierDivisor E (Set.eq_univ_of_univ_subset (by
          rw [← h, hR, Scheme.IdealSheafData.support_mul]
          exact le_sup_right)))
    have hR' : ∀ y ∈ S, y.1 ∈ R.support := fun y hy => by
      have h := hSE y (Finset.mem_insert_of_mem hy)
      rw [hR, Scheme.IdealSheafData.support_mul] at h
      rcases h with h | h
      · exfalso
        have hyx : y.1 = x.1 := by
          simpa [Stacks.Zeta.pointIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] using h
        exact hx (Subtype.ext hyx ▸ hy)
      · exact h
    have h1 := ih (fun y hy => hS1 y (Finset.mem_insert_of_mem hy)) R hR'
    have hxdeg : invertibleCurveDegreeHom k X.f hdimC
        (Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) = 1 := by
      rw [X.invertibleCurveDegreeHom_picardClass_pointIdeal hdimC x,
        hS1 x (Finset.mem_insert_self _ _)]
      rfl
    rw [Stacks.Divisors.picardClass_congr hR, Stacks.Divisors.picardClass_mul, map_add, hxdeg,
      Finset.card_insert_of_notMem hx]
    push_cast
    linarith

end Faltings
