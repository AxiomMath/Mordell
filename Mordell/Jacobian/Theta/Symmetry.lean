module
public import Mordell.Jacobian.Theta.PrimeDivisor
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import StacksFrontier.AlgebraicGeometry.Curves.DualizingInvertibleDimensionDuality
public import StacksFrontier.AlgebraicGeometry.Curves.DifferentialsDegreeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.LinearSystem
public import Mordell.Jacobian.Autoduality.PhiTheta

/-!
# Riemann's symmetry of the theta divisor

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`, let
`(J, ι)` be a Jacobian of `C`, `j = j_P : C ⟶ J` the Abel–Jacobi map, `Θ ⊆ J` the theta divisor
and `θ = cl(Θ) ∈ Pic(J)`, `θ⁻ = [-1]^* θ`. Over an algebraically closed field `K ⊇ k` let `K_C`
be a canonical divisor of `C_K` and `κ = cl(K_C - 2(g - 1)P) ∈ J(K)`. Then `θ⁻ = τ_κ^* θ` on
`J_K`, and hence `θ - θ⁻ = φ_θ(-κ)`.

On `K`-points `Θ = {cl(D - (g - 1)P) : D ≥ 0, deg D = g - 1}`. For such a `D`, Riemann–Roch
and Serre duality on `C_K` give `h⁰(K_C - D) = h⁰(D) ≥ 1`, so `K_C - D` is linearly equivalent
to an effective divisor `D'` of degree `g - 1` and `κ - cl(D - (g - 1)P) = cl(D' - (g - 1)P)`
lies on `Θ`. Thus `x ↦ κ - x` maps `Θ` into itself, hence onto itself, being an involution, and
`[-1]^{-1} Θ = τ_κ^{-1} Θ` on the closed points of `J_K`, hence as closed subsets. Since `Θ` is
geometrically reduced, the inverse images of the reduced divisor `Θ` along the two base changes
`J_K ⟶ J` are the same reduced divisor, and their classes agree. The second identity follows
from the theorem of the square.

## Main results

* `Faltings.schemePullbackClass_thetaNeg_eq_translate`: `θ⁻ = τ_κ^* θ` in `Pic(J_K)`, and
  `θ - θ⁻ = φ_θ(-κ)`.

## Implementation notes

The class `θ` is `Stacks.Divisors.picardClass D` of an effective Cartier divisor `D` on `J`
which is radical (`D.radical = D`) with support `Faltings.thetaDivisor`. The base change is
`J_K = J ⊗ Spec K` in `k`-schemes, as in `Faltings.AbelianVariety.phiMap`; `θ` and `θ⁻` on
`J_K` are their pull-backs along the projection, `[-1]` is `GrpObj.inv` and `τ_κ` is
`x ↦ x + κ`. The point `κ` is a `k`-morphism `Spec K ⟶ J`, characterized by
`κ = ι(Spec K)(cl(K_C - 2(g - 1)P_K))`, where `K_C` enters through its class
`[Ω_{C_K/K}] ∈ Pic(C_K)` and `P_K` through `pr₁^*[𝒪_C(P)]`, as in `Faltings.IsAbelJacobiMap`.

Serre duality is used in the form `dim H¹(C, ℒ) = dim H⁰(C, ℒ^{⊗ -1} ⊗ ω_C)` for the dualizing
sheaf `ω_C`, and `ω_C ≅ Ω_{C/k}` for a smooth curve. Effective divisors on `C_K` are
`ℤ`-combinations of closed points, each of which is a `K`-point since `K` is algebraically
closed.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Sections 5–6.
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4), [Tag 0BS6], [Tag 0C1A].
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped MonObj

universe u

namespace Faltings

section Curve

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

open Stacks.SheafOfModules.Invertible (mulNegOneIso tensorPowerModule tensorPower_isInvertible)

omit [IsAlgClosed Ω] in
/-- `h⁰` of the class of an effective divisor is positive. -/
private lemma one_le_h0_divisorClass {E : Stacks.Zeta.ClosedPoint C →₀ ℤ} (hE : 0 ≤ E) :
    1 ≤ Stacks.Zeta.h0 g (Stacks.Zeta.divisorClass g E) := by
  let := Stacks.Zeta.ffAlg g
  set c := Stacks.Zeta.divisorClass g E
  set L : C.Modules := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
  have hL : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral C L
  have hcls : Stacks.Zeta.divisorClass g (Stacks.Zeta.sectionDivisor g L s hs) = c :=
    (Stacks.Zeta.divisorClass_sectionDivisor g L s hs hL).trans
      (Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c)
  obtain ⟨f, hf, hfD⟩ := Stacks.Zeta.exists_divOf_eq_of_divisorClass_eq_zero g
    (D := E - Stacks.Zeta.sectionDivisor g L s hs) (by rw [map_sub, hcls, sub_self])
  have hmem : f ∈ Stacks.Zeta.rrSpace g (Stacks.Zeta.sectionDivisor g L s hs) := by
    refine (Stacks.Zeta.mem_rrSpace g).2 (Or.inr fun x => ?_)
    have h1 := congrArg (fun D => D x) hfD
    simp only [Stacks.Zeta.divOf_apply, Finsupp.coe_sub, Pi.sub_apply] at h1
    have h2 := hE x
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
    omega
  rw [← Stacks.Zeta.range_coordLinear] at hmem
  obtain ⟨t, ht⟩ := hmem
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hf (by rw [← ht, map_zero])
  have : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible C L
  have := finiteDimensional_cohomologyOverField_of_isProper Ω g L 0
  let e := (cohomologyOverFieldZeroIsoSections Ω g L).toLinearEquiv
  have := e.finiteDimensional
  have : Nontrivial ((ModuleCat.restrictScalars (Stacks.Zeta.globalAlgebraMap g)).obj
      ((_root_.SheafOfModules.evaluation C.ringCatSheaf (op (⊤ : C.Opens))).obj L)) :=
    ⟨⟨t, 0, ht0⟩⟩
  change 0 < Module.finrank Ω (cohomologyOverField Ω g L 0)
  rw [e.finrank_eq]
  exact Module.finrank_pos

omit [IsAlgClosed Ω] in
/-- A class with `h⁰ ≥ 1` is the class of an effective divisor. -/
private lemma exists_nonneg_divisorClass_eq_of_one_le_h0 (c : Stacks.Picard.ofScheme C)
    (hc : 1 ≤ Stacks.Zeta.h0 g c) :
    ∃ E : Stacks.Zeta.ClosedPoint C →₀ ℤ, 0 ≤ E ∧ Stacks.Zeta.divisorClass g E = c := by
  obtain ⟨D, hD⟩ := Stacks.Zeta.exists_divisorClass_eq g c
  let := Stacks.Zeta.ffAlg g
  rw [← hD, ← Stacks.Zeta.finrank_rrSpace] at hc
  have := Module.nontrivial_of_finrank_pos (R := Ω) hc
  obtain ⟨⟨f, hfmem⟩, hf⟩ := exists_ne (0 : Stacks.Zeta.rrSpace g D)
  have hf0 : f ≠ 0 := fun h => hf (Subtype.ext h)
  refine ⟨D + Stacks.Zeta.divOf g hf0, fun x => ?_, ?_⟩
  · rcases (Stacks.Zeta.mem_rrSpace g).1 hfmem with h | h
    · exact absurd h hf0
    · have := h x
      simp only [Finsupp.coe_add, Pi.add_apply, Stacks.Zeta.divOf_apply, Finsupp.coe_zero,
        Pi.zero_apply]
      omega
  · rw [map_add, Stacks.Zeta.divisorClass_divOf, add_zero, hD]

/-- The class `[ω_C]` of the dualizing sheaf of the curve. -/
private noncomputable def dualizingClass
    (hω : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)
      (Stacks.Duality.dualizingSheafOverField g)) : Stacks.Picard.ofScheme C :=
  Stacks.SheafOfModules.picardClass C.presheaf (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)
    (Stacks.Duality.dualizingSheafOverField g) hω

omit [Smooth g] [IsLocallyNoetherian C] in
/-- **Riemann–Roch with Serre duality** in degree `g - 1`: if `deg c = g - 1` then
`h⁰(ω - c) = h⁰(c)`, `ω` the class of the dualizing sheaf. -/
private lemma h0_dualizingClass_sub_eq
    (hω : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)
      (Stacks.Duality.dualizingSheafOverField g))
    (c : Stacks.Picard.ofScheme C)
    (hc : Stacks.Picard.picardDegree g (Stacks.Zeta.topologicalKrullDim_le_one g) c + 1 =
      genus g) :
    Stacks.Zeta.h0 g (dualizingClass g hω - c) = Stacks.Zeta.h0 g c := by
  have hRR := Stacks.Zeta.h0_sub_h1 g c
  set L := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj with hLdef
  have hL : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) L :=
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L :=
    hL.toAlgebraicGeometry
  have hdual := finrank_cohomologyOverField_one_eq_zero_tensorPowerModuleNegOneTensorDualizing
    Ω g (Stacks.Zeta.topologicalKrullDim_le_one g) L
  set N := tensorPowerModule L (-1)
  have hN : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) N :=
    tensorPower_isInvertible C.presheaf C.ringCatSheaf.property L (-1)
  set M := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨C.presheaf,
      CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp _ C.presheaf
        (CategoryTheory.forget₂ CommRingCat RingCat) C.ringCatSheaf.property⟩).obj N).obj
      (Stacks.Duality.dualizingSheafOverField g))
  have hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) M :=
    @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ C.presheaf C.ringCatSheaf.property _ _
      _ _ hN hω
  have hNM := Stacks.SheafOfModules.picardClass_tensorSheaf C.presheaf
    (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)
    N (Stacks.Duality.dualizingSheafOverField g) hN hω hM
  have hLN : Stacks.SheafOfModules.picardClass C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) L hL +
      Stacks.SheafOfModules.picardClass C.presheaf
        (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) N hN = 0 := by
    rw [Stacks.SheafOfModules.picardClass_tensorSheaf C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) L N hL hN
      (@Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ C.presheaf C.ringCatSheaf.property _
        _ _ _ hL hN)]
    rw [← Stacks.SheafOfModules.picardClass_zero C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨mulNegOneIso C.presheaf C.ringCatSheaf.property L⟩
  have hcL : Stacks.SheafOfModules.picardClass C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) L hL = c :=
    Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c
  have hclassM : Stacks.SheafOfModules.picardClass C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace) M hM = dualizingClass g hω - c := by
    rw [dualizingClass, ← hNM, ← hcL, eq_sub_iff_add_eq, add_comm, ← add_assoc, hLN, zero_add]
  set c' := dualizingClass g hω - c
  have hiso : Nonempty ((Stacks.Picard.picardRepresentative C.toRingedSpace c').obj ≅ M) :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
      ((Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c').trans hclassM.symm)
  have h0eq : Stacks.Zeta.h0 g c' = Module.finrank Ω (cohomologyOverField Ω g M 0) :=
    finrank_cohomologyOverField_eq_of_iso Ω g hiso.some 0
  rw [h0eq, ← hdual]
  omega

/-- **The complementary divisor.** If `E ≥ 0` has degree `g - 1`, there is `E' ≥ 0` of
degree `g - 1` with `[E] + [E'] = [ω]`: by Riemann–Roch and Serre duality
`h⁰(ω - [E]) = h⁰([E]) ≥ 1`. -/
private lemma exists_nonneg_add_eq_dualizingClass [IsIso ((Scheme.ΓSpecIso (.of Ω)).inv ≫ g.appTop)]
    (hω : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C.toRingedSpace)
      (Stacks.Duality.dualizingSheafOverField g))
    {E : Stacks.Zeta.ClosedPoint C →₀ ℤ} (hE : 0 ≤ E)
    (hdeg : (E.sum fun _ n => n) + 1 = genus g) :
    ∃ E' : Stacks.Zeta.ClosedPoint C →₀ ℤ, 0 ≤ E' ∧ (E'.sum fun _ n => n) + 1 = genus g ∧
      Stacks.Zeta.divisorClass g E + Stacks.Zeta.divisorClass g E' = dualizingClass g hω := by
  have hdegE := Stacks.Zeta.picardDegree_divisorClass g E
  have h0 := h0_dualizingClass_sub_eq g hω (Stacks.Zeta.divisorClass g E) (by rw [hdegE, hdeg])
  have h1 := one_le_h0_divisorClass g hE
  obtain ⟨E', hE', hcl⟩ := exists_nonneg_divisorClass_eq_of_one_le_h0 g _ (h0 ▸ h1)
  refine ⟨E', hE', ?_, by rw [hcl, add_sub_cancel]⟩
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField g) := hω
  have hω2 := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible Ω g
    (Stacks.Zeta.topologicalKrullDim_le_one g)
  have hωd : Stacks.Picard.picardDegree g (Stacks.Zeta.topologicalKrullDim_le_one g)
      (dualizingClass g hω) = 2 * (genus g : ℤ) - 2 :=
    (Stacks.Picard.picardDegreeFun_picardClass g _ _ hω).trans hω2
  have hdegE' := Stacks.Zeta.picardDegree_divisorClass g E'
  rw [hcl, map_sub, hωd, hdegE] at hdegE'
  omega

end Curve

/-- A nonnegative `ℤ`-valued finitely supported function of total mass `m` is a sum of `m`
point masses. -/
private lemma exists_eq_sum_single_of_nonneg {α : Type*} :
    ∀ (m : ℕ) {E : α →₀ ℤ}, 0 ≤ E → (E.sum fun _ n => n) = m →
      ∃ x : Fin m → α, E = ∑ i, Finsupp.single (x i) 1 := by
  classical
  intro m
  induction m with
  | zero =>
    intro E hE hsum
    refine ⟨Fin.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    ext a
    by_contra h
    have ha : a ∈ E.support := Finsupp.mem_support_iff.2 h
    rw [Finsupp.sum, Nat.cast_zero] at hsum
    exact h ((Finset.sum_eq_zero_iff_of_nonneg fun x _ => hE x).1 hsum a ha)
  | succ m ih =>
    intro E hE hsum
    have hne : E ≠ 0 := by
      rintro rfl
      simp only [Finsupp.sum_zero_index] at hsum
      omega
    obtain ⟨a, ha⟩ : ∃ a, E a ≠ 0 := by
      by_contra h
      exact hne (Finsupp.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
    have hpos : 1 ≤ E a := by
      have := hE a
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    set E' := E - Finsupp.single a 1 with hE'def
    have hEE : E = E' + Finsupp.single a 1 := by rw [hE'def, sub_add_cancel]
    have hE' : 0 ≤ E' := fun x => by
      by_cases hx : x = a
      · subst hx
        simp only [hE'def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
          Finsupp.coe_zero, Pi.zero_apply]
        omega
      · simp only [hE'def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_of_ne hx,
          sub_zero]
        exact hE x
    have hsum' : (E'.sum fun _ n => n) = m := by
      rw [hEE, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl] at hsum
      push_cast at hsum
      omega
    obtain ⟨x, hx⟩ := ih hE' hsum'
    refine ⟨Fin.cons a x, ?_⟩
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [← hx, hEE, add_comm]

section PointClasses

open Stacks.RigidifiedPicard

variable {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)

/-- The section `(Q, id) : Spec K ⟶ C_K` of a point `Q ∈ C(K)`. -/
private noncomputable abbrev sec {K : Type u} [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    Spec (.of K) ⟶ bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  (X.pointFamily Q).zero

/-- The closed point of `C_K` of a point `Q ∈ C(K)`: the image of the section `(Q, id)`. -/
private noncomputable def closedPt {K : Type u} [Field K] [Algebra k K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    Stacks.Zeta.ClosedPoint (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
  haveI : IsSeparated (X.pointFamily Q).map := inferInstanceAs (IsSeparated (bcProj X.f _))
  haveI : IsClosedImmersion (sec X Q) := (X.pointFamily Q).isClosedImmersion_zero
  ⟨sec X Q (IsLocalRing.closedPoint K), by
    have h := (sec X Q).isClosedEmbedding.isClosedMap _
      (isClosed_singleton (x := (IsLocalRing.closedPoint K : Spec (.of K))))
    convert h using 1
    exact Set.image_singleton.symm⟩

/-- The class of the zero divisor of `(Q, id)` is the class of the closed point of `Q`. -/
private lemma picardClass_zeroDivisor_eq_pointClass {K : Type u} [Field K] [Algebra k K]
    [IsAlgClosed K]
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) :
    haveI := X.isEffectiveCartierDivisor_pointFamily Q
    haveI : SmoothOfRelativeDimension 1
        (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
      X.smoothOfRelativeDimension_bcProj _
    haveI : Smooth (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
      SmoothOfRelativeDimension.smooth 1 _
    haveI : IsCurve K (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
      Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
    Stacks.Divisors.picardClass (X.pointFamily Q).zeroDivisor =
      Stacks.Zeta.pointClass (bcProj X.f _) (closedPt X Q) := by
  have := X.isEffectiveCartierDivisor_pointFamily Q
  have : SmoothOfRelativeDimension 1
      (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    X.smoothOfRelativeDimension_bcProj _
  have : Smooth (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve K (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
  have : IsSeparated (X.pointFamily Q).map := inferInstanceAs (IsSeparated (bcProj X.f _))
  have hv := ModuliEllipticCurves.PointedFamily.zeroDivisor_eq_vanishingIdeal (k := K)
    (X.pointFamily Q) (IsLocalRing.closedPoint K)
  have : Stacks.Divisors.IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      ⟨{(X.pointFamily Q).zero (IsLocalRing.closedPoint K)}, (closedPt X Q).2⟩) :=
    Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (bcProj X.f _) (closedPt X Q)
  exact Stacks.Divisors.picardClass_congr hv

/-- Every closed point of `C_K` is the closed point of a point `Q ∈ C(K)`. -/
private lemma exists_closedPt_eq {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    (x : Stacks.Zeta.ClosedPoint
      (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f,
      closedPt X Q = x := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let p : Spec (.of K) ⟶ bc X.f T := pointOfClosedPoint (bcProj X.f T) x.1 x.2
  have hp : p ≫ pullback.snd X.f T.hom = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hw : (p ≫ pullback.fst X.f T.hom) ≫ X.f = T.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, Category.id_comp]
  let Q : T ⟶ Over.mk X.f := Over.homMk (p ≫ pullback.fst X.f T.hom) hw
  refine ⟨Q, ?_⟩
  have hz : sec X Q = p :=
    pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans hp.symm)
  apply Subtype.ext
  change sec X Q (IsLocalRing.closedPoint K) = x.1
  rw [hz]
  exact pointOfClosedPoint_apply _ _ _ _

/-- The class `[𝒪(Q)]` of the section `(Q, id)` in `Pic(C_T)`. -/
private noncomputable def zClass {T : Over (Spec (.of k))} (Q : T ⟶ Over.mk X.f) :
    Stacks.Picard.ofScheme (bc X.f T) :=
  haveI := X.isEffectiveCartierDivisor_pointFamily Q
  Stacks.Divisors.picardClass (X.pointFamily Q).zeroDivisor

/-- The canonical class `[K_C] = [Ω_{C_K/K}]` of `C_K` in `Pic(C_K)`. -/
private noncomputable def canClass (K : Type u) [Field K] [Algebra k K] :
    Stacks.Picard.ofScheme (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
  haveI : SmoothOfRelativeDimension 1
      (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    X.smoothOfRelativeDimension_bcProj _
  haveI : Smooth (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    SmoothOfRelativeDimension.smooth 1 _
  haveI : IsCurve K (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
  Stacks.SheafOfModules.picardClass _ (Stacks.RingedSpace.structureIsSheaf _)
    (Scheme.Hom.relativeDifferentials
      (bcProj X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))))
    (isInvertible_relativeDifferentials_of_isCurve _)

/-- **Riemann's complement on `C_K`.** For `g - 1` points `Qᵢ ∈ C(K)`, `K` algebraically
closed, there are `g - 1` points `Q'ᵢ ∈ C(K)` with `∑ [Qᵢ] + ∑ [Q'ᵢ] = [K_C]`. -/
private lemma exists_points_add_eq_canClass {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    (hg : 1 ≤ genus X.f)
    (Q : Fin (genus X.f - 1) →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)) :
    ∃ Q' : Fin (genus X.f - 1) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f),
      (∑ i, zClass X (Q i)) + (∑ i, zClass X (Q' i)) = canClass X K := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let π : bc X.f T ⟶ Spec (.of K) := bcProj X.f T
  have : SmoothOfRelativeDimension 1 π := X.smoothOfRelativeDimension_bcProj T
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  have : IsCurve K π := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one π
  have : IsProper π := inferInstanceAs (IsProper (bcProj X.f T))
  have : IsLocallyNoetherian (bc X.f T) := LocallyOfFiniteType.isLocallyNoetherian π
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have := isIso_globalSections_bc_spec X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hgen : genus π = genus X.f :=
    genus_bc_spec X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : SheafOfModules.IsInvertible (bc X.f T).presheaf (bc X.f T).ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField π) :=
    isInvertible_dualizingSheafOverField_of_isCurve π
  have hω : Stacks.SheafOfModules.IsInvertible (bc X.f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc X.f T).toRingedSpace)
      (Stacks.Duality.dualizingSheafOverField π) := ‹_›
  classical
  let E : Stacks.Zeta.ClosedPoint (bc X.f T) →₀ ℤ := ∑ i, Finsupp.single (closedPt X (Q i)) 1
  have hE : 0 ≤ E := by
    intro x
    simp only [E, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact Finset.sum_nonneg fun i _ => by
      rw [Finsupp.single_apply]
      split_ifs <;> omega
  have hsum : ∀ (n : ℕ) (x : Fin n → Stacks.Zeta.ClosedPoint (bc X.f T)),
      ((∑ i, Finsupp.single (x i) (1 : ℤ)).sum fun _ n => n) = n := by
    intro n x
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp [Finsupp.sum_single_index]
  have hEdeg : (E.sum fun _ n => n) + 1 = genus π := by
    rw [hsum, hgen]
    omega
  obtain ⟨E', hE', hE'deg, hcl⟩ := exists_nonneg_add_eq_dualizingClass π hω hE hEdeg
  obtain ⟨x', hx'⟩ := exists_eq_sum_single_of_nonneg (genus X.f - 1) hE' (by
    rw [hgen] at hE'deg
    omega)
  choose Q' hQ' using fun i => exists_closedPt_eq X (x' i)
  refine ⟨Q', ?_⟩
  have hdiv : ∀ (x : Fin (genus X.f - 1) → Stacks.Zeta.ClosedPoint (bc X.f T)),
      Stacks.Zeta.divisorClass π (∑ i, Finsupp.single (x i) 1) =
        ∑ i, Stacks.Zeta.pointClass π (x i) := by
    intro x
    rw [map_sum]
    simp only [Stacks.Zeta.divisorClass_single]
    exact Finset.sum_congr rfl fun i _ => one_zsmul _
  have hz : ∀ R : T ⟶ Over.mk X.f, zClass X R = Stacks.Zeta.pointClass π (closedPt X R) :=
    fun R => picardClass_zeroDivisor_eq_pointClass X R
  simp only [hz]
  have h1 := hdiv (fun i => closedPt X (Q i))
  have h2 := hdiv x'
  rw [← hx'] at h2
  have hQ'' : x' = fun i => closedPt X (Q' i) := funext fun i => (hQ' i).symm
  rw [hQ''] at h2
  rw [← h1, ← h2]
  refine hcl.trans ?_
  /- `[ω] = [Ω]`. -/
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials π)

end PointClasses

section Jacobian

open Stacks.RigidifiedPicard CartesianMonoidalCategory

variable {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
  {j : Over.mk X.f ⟶ A.J}

/-- The point `j(Q₁) + ⋯ + j(Qₙ)` is `ι(∑ cl(Qᵢ - P_K))`. -/
private lemma list_prod_eq_ι_sum (hj : IsAbelJacobiMap X A j) {K : Type u} [Field K]
    [Algebra k K] {n : ℕ}
    (Q : Fin n → (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)) :
    (List.ofFn fun i => Q i ≫ j).prod =
      (show _ ⟶ A.J from A.ι.app (op _) (∑ i, X.pointClass (Q i))) := by
  rw [Jacobian.ι_app_sum]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hj.comp_eq_ι_pointClass (Q i)))

/-- The class `cl(K_C - 2(g - 1)P_K)` in `Pic(C_K)`, in the small model. -/
private noncomputable def kappaClass (K : Type u) [Field K] [Algebra k K] :
    Stacks.Picard.smallOfScheme
      (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :=
  (smallEquiv.{u} _).symm (canClass X K - (2 * ((genus X.f : ℤ) - 1)) •
    (Stacks.Picard.schemePullbackClass
      (pullback.fst X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom)
      X.classP : Stacks.Picard.ofScheme
        (bc X.f (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))))

/-- **The key step of Riemann's symmetry.** If `u = j(Q₁) + ⋯ + j(Q_{g-1})` then
`κ - u = j(Q'₁) + ⋯ + j(Q'_{g-1})` for some points `Q'ᵢ`. -/
private lemma exists_mul_inv_eq_list_prod (hg : 1 ≤ genus X.f) (hj : IsAbelJacobiMap X A j)
    {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    (κ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)
    (hκ : ∀ hdeg : degree X.f (relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f) _
        (kappaClass X K) = 0,
      κ = A.ι.app (op _) (QuotientAddGroup.mk ⟨kappaClass X K, hdeg⟩))
    (Q : Fin (genus X.f - 1) →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)) :
    ∃ Q' : Fin (genus X.f - 1) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f),
      κ * ((List.ofFn fun i => Q i ≫ j).prod)⁻¹ = (List.ofFn fun i => Q' i ≫ j).prod := by
  obtain ⟨Q', hQ'⟩ := exists_points_add_eq_canClass X hg Q
  refine ⟨Q', ?_⟩
  have hdim := relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let w : (T ⟶ Over.mk X.f) → (degree X.f hdim T).ker := fun R =>
    ⟨(smallEquiv.{u} _).symm (X.abelJacobiClass R),
      AddMonoidHom.mem_ker.2 (X.degree_abelJacobiClass_field hdim K R)⟩
  have hw : ∀ R, X.pointClass R = QuotientAddGroup.mk (w R) := fun R => rfl
  set P : Stacks.Picard.ofScheme (bc X.f T) :=
    Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) X.classP with hP
  have hab : ∀ R : T ⟶ Over.mk X.f, X.abelJacobiClass R = zClass X R - P := fun R => rfl
  have key : canClass X K - (2 * ((genus X.f : ℤ) - 1)) • P =
      ∑ i, X.abelJacobiClass (Q' i) + ∑ i, X.abelJacobiClass (Q i) := by
    simp only [hab]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← hQ', ← natCast_zsmul]
    have h2 : (2 * ((genus X.f : ℤ) - 1)) =
        ((genus X.f - 1 : ℕ) : ℤ) + ((genus X.f - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hg]
      ring
    rw [h2, add_zsmul, sub_add_sub_comm, add_comm (∑ x, zClass X (Q' x))]
  have hz : kappaClass X K = ∑ i, (w (Q' i) : Stacks.Picard.smallOfScheme (bc X.f T)) +
      ∑ i, (w (Q i) : Stacks.Picard.smallOfScheme (bc X.f T)) := by
    change (smallEquiv.{u} (bc X.f T)).symm (canClass X K - (2 * ((genus X.f : ℤ) - 1)) • P) = _
    rw [key, map_add, map_sum, map_sum]
  have hdeg : degree X.f hdim T (kappaClass X K) = 0 := by
    rw [hz, map_add, map_sum, map_sum]
    simp only [AddMonoidHom.mem_ker.1 (w _).2, Finset.sum_const_zero, add_zero]
  have hmem : kappaClass X K ∈ (degree X.f hdim T).ker := hdeg
  have hsub : (⟨kappaClass X K, hmem⟩ : (degree X.f hdim T).ker) =
      (∑ i, w (Q' i)) + ∑ i, w (Q i) := by
    apply Subtype.ext
    change kappaClass X K =
      (degree X.f hdim T).ker.subtype ((∑ i, w (Q' i)) + ∑ i, w (Q i))
    rw [map_add, map_sum, map_sum]
    exact hz
  have hmk : (QuotientAddGroup.mk ⟨kappaClass X K, hmem⟩ :
      (relativePicZeroFunctor k X.f).obj (op T)) =
      (∑ i, X.pointClass (Q' i)) + ∑ i, X.pointClass (Q i) := by
    rw [hsub]
    have h := map_add (QuotientAddGroup.mk' ((Stacks.Picard.smallSchemePullbackClassHom
      (bcProj X.f T)).range.addSubgroupOf (degree X.f hdim T).ker))
      (∑ i, w (Q' i)) (∑ i, w (Q i))
    rw [map_sum, map_sum] at h
    exact h
  have h1 : κ = (show T ⟶ A.J from A.ι.app (op T)
      ((∑ i, X.pointClass (Q' i)) + ∑ i, X.pointClass (Q i))) :=
    (hκ hdeg).trans (congrArg (fun x => (show T ⟶ A.J from A.ι.app (op T) x)) hmk)
  rw [h1, list_prod_eq_ι_sum X A hj, list_prod_eq_ι_sum X A hj]
  exact mul_inv_eq_of_eq_mul (A.map_add (op T) _ _)

/-- The closed point of `Spec K`. -/
private noncomputable abbrev ptK (K : Type u) [Field K] : Spec (.of K) :=
  IsLocalRing.closedPoint K

private lemma pi_lift_comp_sumMap {T : Over (Spec (.of k))}
    (Q : Fin (genus X.f - 1) → (T ⟶ Over.mk X.f)) :
    Pi.lift Q ≫ sumMap (genus X.f - 1) j = (List.ofFn fun i => Q i ≫ j).prod := by
  rw [comp_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.lift_π_assoc]

/-- `j(Q₁) + ⋯ + j(Q_{g-1})` lies on `Θ`. -/
private lemma mem_thetaDivisor_list_prod (hg : 1 ≤ genus X.f) (hj : IsAbelJacobiMap X A j)
    {K : Type u} [Field K] [Algebra k K]
    (Q : Fin (genus X.f - 1) →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)) :
    (show Spec (.of K) ⟶ A.J.left from ((List.ofFn fun i => Q i ≫ j).prod).left) (ptK K) ∈
      thetaDivisor X A hg j hj := by
  refine ⟨(show Spec (.of K) ⟶ _ from (Pi.lift Q).left) (ptK K), ?_⟩
  rw [← pi_lift_comp_sumMap X A Q, Over.comp_left]
  rfl

/-- **A point of `Θ` with values in an algebraically closed field is a sum of `g - 1` points of
`j(C)`.** -/
private lemma exists_list_prod_eq_of_mem (hg : 1 ≤ genus X.f) (hj : IsAbelJacobiMap X A j)
    {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)
    (hu : (show Spec (.of K) ⟶ A.J.left from u.left) (ptK K) ∈ thetaDivisor X A hg j hj) :
    ∃ Q : Fin (genus X.f - 1) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f),
      u = (List.ofFn fun i => Q i ≫ j).prod := by
  let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let W := ∏ᶜ fun _ : Fin (genus X.f - 1) => Over.mk X.f
  let σ : W ⟶ A.J := sumMap (genus X.f - 1) j
  obtain ⟨y, hy⟩ := hu
  have : IsProper A.J.hom := A.isAbelianVariety.toIsProper
  have : IsProper (Over.mk X.f).hom := (inferInstance : IsProper X.f)
  have : IsProper W.hom := Stacks.RigidifiedPicard.isProper_fibrePower_hom _ _
  have : IsProper (σ.left ≫ A.J.hom) := by rw [Over.w]; infer_instance
  have : IsProper σ.left := .of_comp _ A.J.hom
  let uK : Spec (.of K) ⟶ A.J.left := u.left
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := uK) (g := σ.left)
    (ptK K) y hy.symm
  let PB : Scheme.{u} := pullback uK σ.left
  let pr : PB ⟶ Spec (.of K) := pullback.fst uK σ.left
  have : IsProper pr := inferInstanceAs (IsProper (pullback.fst uK σ.left))
  have : CompactSpace PB := (quasiCompact_iff_compactSpace pr).1 inferInstance
  have : Nonempty PB := ⟨z⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := PB) isClosed_univ
    Set.univ_nonempty
  let p := pointOfClosedPoint pr x hx
  have hp : p ≫ pr = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hpσ : (p ≫ pullback.snd uK σ.left) ≫ σ.left = uK := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    change (p ≫ pr) ≫ uK = uK
    rw [hp, Category.id_comp]
  let q : T ⟶ W := Over.homMk (p ≫ pullback.snd uK σ.left) (by
    change (p ≫ pullback.snd uK σ.left) ≫ W.hom = T.hom
    rw [← Over.w σ, ← Category.assoc, hpσ]
    exact Over.w u)
  refine ⟨fun i => q ≫ Pi.π _ i, ?_⟩
  have hq : q ≫ σ = u := by
    ext1
    rw [Over.comp_left]
    exact hpσ
  rw [← hq, ← pi_lift_comp_sumMap X A]
  congr 1
  exact Pi.hom_ext _ _ fun i => by rw [Pi.lift_comp_π]

/-- **Riemann's symmetry on points.** If `u ∈ Θ(K)` then `κ - u ∈ Θ(K)`. -/
private lemma mem_thetaDivisor_mul_inv (hg : 1 ≤ genus X.f) (hj : IsAbelJacobiMap X A j)
    {K : Type u} [Field K] [Algebra k K] [IsAlgClosed K]
    (κ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)
    (hκ : ∀ hdeg : degree X.f (relativePicZeroFunctor.topologicalKrullDim_fiber_le_one X.f) _
        (kappaClass X K) = 0,
      κ = A.ι.app (op _) (QuotientAddGroup.mk ⟨kappaClass X K, hdeg⟩))
    (u : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)
    (hu : (show Spec (.of K) ⟶ A.J.left from u.left) (ptK K) ∈ thetaDivisor X A hg j hj) :
    (show Spec (.of K) ⟶ A.J.left from (κ * u⁻¹).left) (ptK K) ∈ thetaDivisor X A hg j hj := by
  obtain ⟨Q, rfl⟩ := exists_list_prod_eq_of_mem X A hg hj u hu
  obtain ⟨Q', hQ'⟩ := exists_mul_inv_eq_list_prod X A hg hj κ hκ Q
  rw [hQ']
  exact mem_thetaDivisor_list_prod X A hg hj Q'

/-- Two inverse images of `θ` along base changes `Y ⟶ J` agree when the inverse images of `Θ`
do. -/
private lemma schemePullbackClass_eq_of_preimage_eq (hg : 1 ≤ genus X.f)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [IsReduced D.subscheme]
    (hD : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] {Y : Scheme.{u}} (φ₁ φ₂ : Y ⟶ A.J.left)
    (ψ₁ ψ₂ : Y ⟶ Spec (.of K))
    (h₁ : IsPullback φ₁ ψ₁ A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (h₂ : IsPullback φ₂ ψ₂ A.J.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (h : φ₁ ⁻¹' thetaDivisor X A hg j hj = φ₂ ⁻¹' thetaDivisor X A hg j hj) :
    Stacks.Picard.schemePullbackClass φ₁ (Stacks.Divisors.picardClass D) =
      Stacks.Picard.schemePullbackClass φ₂ (Stacks.Divisors.picardClass D) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat φ₁ := MorphismProperty.of_isPullback h₁.flip inferInstance
  have : Flat φ₂ := MorphismProperty.of_isPullback h₂.flip inferInstance
  have : Stacks.Divisors.IsPullbackDefined φ₁ D :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have : Stacks.Divisors.IsPullbackDefined φ₂ D :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have := isReduced_comap_of_support_eq_thetaDivisor X A hg hj D hD K φ₁ ψ₁ h₁
  have := isReduced_comap_of_support_eq_thetaDivisor X A hg hj D hD K φ₂ ψ₂ h₂
  have heq : D.comap φ₁ = D.comap φ₂ := by
    refine eq_comap_of_preimage_support_eq (D.comap φ₁) D φ₂ ?_
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hD, h,
      ← hD]
  rw [Stacks.Divisors.schemePullbackClass_picardClass,
    Stacks.Divisors.schemePullbackClass_picardClass]
  exact Stacks.Divisors.picardClass_congr heq

end Jacobian

section Main

open Stacks.RigidifiedPicard CartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- For a group object `G` and an object `Y` of a cartesian monoidal category, the map
`(g, y) ↦ (g⁻¹, y)` of `G ⊗ Y` is an isomorphism. -/
private lemma isIso_lift_inv_fst {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
    (G Y : 𝒞) [GrpObj G] : IsIso (lift (fst G Y)⁻¹ (snd G Y)) := by
  refine ⟨⟨lift (fst G Y)⁻¹ (snd G Y), ?_, ?_⟩⟩ <;>
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, Category.id_comp, GrpObj.comp_inv, lift_fst, inv_inv]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

/-- For a group object `G`, an object `Y` and `κ : Y ⟶ G` in a cartesian monoidal category, the
translation `(g, y) ↦ (g * κ(y), y)` of `G ⊗ Y` is an isomorphism. -/
private lemma isIso_lift_fst_mul {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
    {G Y : 𝒞} [GrpObj G] (κ : Y ⟶ G) : IsIso (lift (fst G Y * (snd G Y ≫ κ)) (snd G Y)) := by
  refine ⟨⟨lift (fst G Y * (snd G Y ≫ κ⁻¹)) (snd G Y), ?_, ?_⟩⟩
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, Category.id_comp, MonObj.comp_mul, lift_fst,
        ← Category.assoc, lift_snd, mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
        MonObj.comp_one, mul_one]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, Category.id_comp, MonObj.comp_mul, lift_fst,
        ← Category.assoc, lift_snd, mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
        MonObj.comp_one, mul_one]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

/-- If `lift ψ (snd X Y)` is an isomorphism, then `ψ : X ⊗ Y ⟶ X` and the second projection
exhibit `X ⊗ Y` as the pullback of `X ⟶ S` along `Y ⟶ S`. -/
private lemma isPullback_left_of_isIso_lift {S : Scheme.{u}} {X Y : Over S} (ψ : X ⊗ Y ⟶ X)
    [IsIso (lift ψ (snd X Y))] : IsPullback ψ.left (snd X Y).left X.hom Y.hom := by
  have hpb₀ : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have : IsIso (lift ψ (snd X Y)).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (lift ψ (snd X Y))))
  refine IsPullback.of_iso hpb₀ (asIso (lift ψ (snd X Y)).left).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
      ← Over.comp_left, lift_fst]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
      ← Over.comp_left, lift_snd]

/-- **Riemann's symmetry of the theta divisor** ([MilAV, III, Sections 5–6]). Let
`X = (C, P)` be a curve over `k` with a divisor of degree one, of genus `g ≥ 1`, `A = (J, ι)` a
Jacobian of `C`, `j = j_P` the Abel–Jacobi map and `θ = Stacks.Divisors.picardClass D` the class of
the reduced effective Cartier divisor `D` with support the theta divisor
`Faltings.thetaDivisor X A hg j hj`. Let `K ⊇ k` be algebraically closed, `K_C` a canonical
divisor of `C_K`, with class `[Ω_{C_K/K}]`, and `κ = ι(Spec K)(cl(K_C - 2(g - 1)P_K)) ∈ J(K)`.
Then on `J_K` the pull-back of `θ⁻ = [-1]^* θ` is `τ_κ^* θ`, and
`θ - θ⁻ = φ_θ(-κ) = Faltings.AbelianVariety.phiMap A.J θ κ⁻¹`. -/
@[faltings "lem_nt_theta_symmetry"]
public theorem schemePullbackClass_thetaNeg_eq_translate (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (κ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :
    let T : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    have hdim : ∀ s, topologicalKrullDim ↥(X.f.fiber s) ≤ 1 := fun s =>
      (topologicalKrullDim_fiber_spec X.f s).trans_le
        (topologicalKrullDim_le_one_of_smoothOfRelativeDimension X.f)
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI : SmoothOfRelativeDimension 1 (bcProj X.f T) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback X.f T.hom) inferInstance
    haveI : Smooth (bcProj X.f T) := SmoothOfRelativeDimension.smooth 1 _
    haveI : IsCurve K (bcProj X.f T) := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
    /- The class `[𝒪_C(P)] = ∑ nₓ [𝒪_C(x)]` in `Pic(C)`. -/
    let classP : Stacks.Picard.ofScheme X.C := X.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)
    /- The canonical class `[K_C] = [Ω_{C_K/K}]` in `Pic(C_K)`. -/
    let canonical : Stacks.Picard.ofScheme (bc X.f T) :=
      Stacks.SheafOfModules.picardClass _ (Stacks.RingedSpace.structureIsSheaf _)
        (Scheme.Hom.relativeDifferentials (bcProj X.f T))
        (isInvertible_relativeDifferentials_of_isCurve _)
    /- `K_C - 2(g - 1) P_K` in `Pic(C_K)`, in the small model of the Picard group. -/
    let z : Stacks.Picard.smallOfScheme (bc X.f T) := (smallEquiv.{u} (bc X.f T)).symm
      (canonical - (2 * ((genus X.f : ℤ) - 1)) •
        Stacks.Picard.schemePullbackClass (pullback.fst X.f T.hom) classP)
    /- `κ = cl(K_C - 2(g - 1)P) ∈ J(K)`. -/
    (∀ hdeg : degree X.f hdim T z = 0,
      κ = A.ι.app (op T) (show (relativePicZeroFunctor k X.f).obj (op T) from
        QuotientAddGroup.mk (⟨z, hdeg⟩ : (degree X.f hdim T).ker))) →
    /- `θ = cl(Θ)` and `θ⁻ = [-1]^* θ` in `Pic(J)`. -/
    let θ := Stacks.Divisors.picardClass D
    let θneg := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
    Stacks.Picard.schemePullbackClass (fst A.J T).left θneg =
        Stacks.Picard.schemePullbackClass (lift (fst A.J T) (snd A.J T ≫ κ) ≫ μ[A.J]).left θ ∧
      Stacks.Picard.schemePullbackClass (fst A.J T).left θ -
          Stacks.Picard.schemePullbackClass (fst A.J T).left θneg =
        AbelianVariety.phiMap A.J θ κ⁻¹ := by
  intro T hdim classP canonical z hκ θ θneg
  have := A.isAbelianVariety
  have : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  have hκ' : ∀ hdeg : degree X.f hdim T (kappaClass X K) = 0,
      κ = A.ι.app (op T) (QuotientAddGroup.mk ⟨kappaClass X K, hdeg⟩) := hκ
  have hDv : D = Scheme.IdealSheafData.vanishingIdeal D.support := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, hrad]
  have : IsReduced D.subscheme := by
    rw [hDv]
    infer_instance
  have hkey := mem_thetaDivisor_mul_inv X A hg hj κ hκ'
  let JK : Over (Spec (.of k)) := A.J ⊗ T
  let ψ₁ : JK ⟶ A.J := (fst A.J T)⁻¹
  let ψ₂ : JK ⟶ A.J := fst A.J T * (snd A.J T ≫ κ)
  have hψ₁ : ψ₁ = fst A.J T ≫ ι[A.J] := rfl
  have hψ₂ : ψ₂ = lift (fst A.J T) (snd A.J T ≫ κ) ≫ μ[A.J] := rfl
  /- `Θ` is closed. -/
  have hΘc : IsClosed (thetaDivisor X A hg j hj) := hsupp ▸ D.support.isClosed
  /- The two inverse images of `Θ` agree on closed points, by Riemann's symmetry. -/
  have : IsProper A.J.hom := A.isAbelianVariety.toIsProper
  let pr : JK.left ⟶ Spec (.of K) := (snd A.J T).left
  have : LocallyOfFiniteType pr :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd A.J.hom T.hom))
  have hpt : ∀ x : JK.left, IsClosed ({x} : Set JK.left) →
      (x ∈ ψ₁.left ⁻¹' thetaDivisor X A hg j hj ↔ x ∈ ψ₂.left ⁻¹' thetaDivisor X A hg j hj) := by
    intro x hx
    let p := pointOfClosedPoint pr x hx
    have hp : p ≫ pr = 𝟙 _ := pointOfClosedPoint_comp _ _ _
    let pt : T ⟶ JK := Over.homMk p (by
      change p ≫ JK.hom = T.hom
      rw [← Over.w (snd A.J T), ← Category.assoc]
      change (p ≫ pr) ≫ T.hom = T.hom
      rw [hp, Category.id_comp])
    have hsnd : pt ≫ snd A.J T = 𝟙 T := Over.OverMorphism.ext hp
    have hev : ∀ ψ : JK ⟶ A.J, ψ.left x =
        (show Spec (.of K) ⟶ A.J.left from (pt ≫ ψ).left) (ptK K) := by
      intro ψ
      rw [Over.comp_left]
      change _ = ψ.left (p (ptK K))
      rw [pointOfClosedPoint_apply]
    have h1 : pt ≫ ψ₁ = (pt ≫ fst A.J T)⁻¹ := GrpObj.comp_inv _ _
    have h2 : pt ≫ ψ₂ = (pt ≫ fst A.J T) * κ := by
      rw [MonObj.comp_mul, ← Category.assoc, hsnd, Category.id_comp]
    simp only [Set.mem_preimage]
    rw [hev ψ₁, hev ψ₂, h1, h2]
    constructor
    · intro h
      have := hkey _ h
      rwa [inv_inv, mul_comm] at this
    · intro h
      have := hkey _ h
      rwa [mul_inv_rev, mul_inv_cancel_left] at this
  have hset : ψ₁.left ⁻¹' thetaDivisor X A hg j hj = ψ₂.left ⁻¹' thetaDivisor X A hg j hj := by
    have : JacobsonSpace JK.left := LocallyOfFiniteType.jacobsonSpace pr
    have hc₁ : IsClosed (ψ₁.left ⁻¹' thetaDivisor X A hg j hj) := hΘc.preimage ψ₁.left.continuous
    have hc₂ : IsClosed (ψ₂.left ⁻¹' thetaDivisor X A hg j hj) := hΘc.preimage ψ₂.left.continuous
    have e₁ := JacobsonSpace.closure_inter_closedPoints_eq_closure hc₁.isLocallyClosed
    have e₂ := JacobsonSpace.closure_inter_closedPoints_eq_closure hc₂.isLocallyClosed
    rw [hc₁.closure_eq] at e₁
    rw [hc₂.closure_eq] at e₂
    rw [← e₁, ← e₂]
    congr 1
    ext x
    exact and_congr_left (hpt x)
  have : IsIso (lift ψ₁ (snd A.J T)) := isIso_lift_inv_fst A.J T
  have : IsIso (lift ψ₂ (snd A.J T)) := isIso_lift_fst_mul κ
  have hcl := schemePullbackClass_eq_of_preimage_eq X A hg hj D hsupp K ψ₁.left ψ₂.left
    (snd A.J T).left (snd A.J T).left (isPullback_left_of_isIso_lift ψ₁)
    (isPullback_left_of_isIso_lift ψ₂) hset
  have hθneg : Stacks.Picard.schemePullbackClass (fst A.J T).left θneg =
      Stacks.Picard.schemePullbackClass ψ₁.left θ := by
    change Stacks.Picard.schemePullbackClass (fst A.J T).left
      (Stacks.Picard.schemePullbackClass ι[A.J].left θ) = _
    rw [Stacks.Picard.schemePullbackClass_comp, hψ₁, Over.comp_left]
  have hfirst := hθneg.trans hcl
  refine ⟨hfirst, ?_⟩
  /- `φ_θ(-κ) = -φ_θ(κ) = θ - τ_κ^* θ`. -/
  have hφ1 : AbelianVariety.phiMap A.J θ (1 : T ⟶ A.J) = 0 := by
    simp only [AbelianVariety.phiMap]
    rw [MonObj.comp_one, show lift (fst A.J T) 1 ≫ μ[A.J] = fst A.J T * 1 from rfl, mul_one,
      sub_self]
  have hφinv : AbelianVariety.phiMap A.J θ κ⁻¹ = -AbelianVariety.phiMap A.J θ κ := by
    have h := AbelianVariety.phiMap_mul A.J θ κ κ⁻¹
    rw [mul_inv_cancel, hφ1] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  rw [hφinv, hfirst, hψ₂]
  simp only [AbelianVariety.phiMap]
  rw [neg_sub]

end Main

end Faltings
