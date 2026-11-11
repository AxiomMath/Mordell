module
public import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.SmallSection.U0
public import Mordell.BombieriVojta.Representative.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.LinearSystem
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatAtPullbackMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
public import StacksFrontier.AlgebraicGeometry.GradedSectionsModule.IntGraded
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
import Mordell.BombieriVojta.Representative.Chart

/-!
# The dimension of `U₀`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, with a divisor `P` of degree one, `N ≥ 2g + 1`, `n = N - g`, and let
`φ_{NP} : C → ℙⁿ` be the closed immersion given by a `k`-basis `x = (x₀, …, xₙ)` of
`H⁰(C, 𝒪(NP))`, and `ψ = φ_{NP} × φ_{NP}`. Suppose that every global section of
`ψ^*𝒪(δ₁, δ₂)` on `C × C` is the restriction of a bihomogeneous form of bidegree `(δ₁, δ₂)` over
`k` (this holds for `δ₁, δ₂ ≥ δ₀`), and that `N δ₁, N δ₂ > 2g - 2`. Then the space
`U₀ ⊆ k(C × C)^{m+1}` of tuples `(F_i(ξ, ξ'))_{i=0}^m` has dimension
`(m + 1)(N²δ₁δ₂ - N(g - 1)(δ₁ + δ₂) + (g - 1)²) ≤ (m + 1) N² δ₁ δ₂`.

Indeed `F ↦ F(ξ, ξ')` identifies the restrictions of forms with `H⁰(C × C, ψ^*𝒪(δ₁, δ₂))`, and
`ψ^*𝒪(δ₁, δ₂) = 𝒪(δ₁(NP) × C + δ₂ C × (NP))` has `(Nδ₁ + 1 - g)(Nδ₂ + 1 - g)` sections.

## Main results

* `Faltings.BombieriVojta.finrank_affineEvaluationTuples`: the dimension of `U₀`, and its upper
  bound.

## Implementation notes

* `C × C` is `pullback f f` over `Spec k` and `ψ = pullback.map _ _ _ _ φ_{NP} φ_{NP} (𝟙 _) _ _`;
  `pr₁^*, pr₂^* : k(C) →ₐ[k] k(C × C)` are `AlgebraicGeometry.functionFieldMapAlgHom` of the two
  projections.
* The basis `x` is a family `ℓ : Fin (n + 1) → k(C)`, linearly independent over `k` and spanning
  the Riemann–Roch space `L(NP) = {g | g = 0 ∨ ord_Q g + N P(Q) ≥ 0 for all closed Q}`, and
  `φ_{NP}` is the morphism it defines: the pull-back of `T_ν / T_j` has germ `ℓ_ν / ℓ_j` at the
  generic point of `C`.
* The integer `δ₀` enters only through its defining property at `(δ₁, δ₂)`: the restriction map
  `Faltings.vojtaFormRestriction` from forms of bidegree `(δ₁, δ₂)` over `k` to the global
  sections of `ψ^*𝒪(δ₁, δ₂)` is surjective.
* Since `Faltings.BombieriVojta.affineEvaluation` is invariant under rescaling `x`, the index `j`
  of the chart is arbitrary; the source's case is `j = 0`.
* The dimension is an integer identity, `N²δ₁δ₂ - N(g - 1)(δ₁ + δ₂) + (g - 1)²` being computed
  in `ℤ`.

* The dimension is squeezed between two bounds. *Upper bound*: `F(ξ, ξ')` is a sum of products
  `pr₁^* a · pr₂^* b` with `a ∈ ℓ_j^{-δ₁} L(δ₁ N P)` and `b ∈ ℓ_j^{-δ₂} L(δ₂ N P)`, since a
  product of `δ` sections of `𝒪(NP)` is a section of `𝒪(δ N P)`, and by Riemann–Roch
  `dim L(δ N P) = N δ + 1 - g`. *Lower bound*: on the chart `x_j x'_j ≠ 0` of `C × C` every
  global section of `ψ^*𝒪(δ₁, δ₂)` is a function times `x_j^{δ₁} x'_j^{δ₂}`, the function being
  `F(ξ, ξ')` for a form `F` restricting to it. The sections `pr₁^* σ ⊗ pr₂^* τ`, for `σ`, `τ`
  running through bases of `H⁰(C, φ^*𝒪(δ₁))` and `H⁰(C, φ^*𝒪(δ₂))`, give linearly independent
  values, because `k(C) ⊗_k k(C) → k(C × C)` is injective; and `h⁰(C, φ^*𝒪(δ)) = N δ + 1 - g`,
  the linear system `|NP|` being base point free. The source instead computes
  `h⁰(C × C, ψ^*𝒪(δ₁, δ₂))` by the Künneth formula.
* The injectivity of `k(C) ⊗_k k(C) → k(C × C)` is deduced from the integrality of `C × C`:
  for an affine open `U = Spec A` of `C`, `U ×_k U = Spec (A ⊗_k A)` is a nonempty open of
  `C × C`, so `A ⊗_k A` is a domain, hence so is its localization `k(C) ⊗_k k(C)`, and the local
  ring of `C × C` at its generic point is a localization of `k(C) ⊗_k k(C)` at a prime.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 630–631
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open Stacks.ProjectiveFromSections (resT resO resM)
open Opposite MonoidalCategory
open scoped TensorProduct

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriVojta

universe u

/-! ### Coordinates against a regular meromorphic section -/

section GenericCoord

/-- The coordinate `ρ(t)` of a global section `t` against a regular meromorphic section is
nonzero as soon as `t` does not vanish at some point. -/
private theorem genericCoord_ne_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    {t : Γ(L, ⊤)} {x : X} (ht : x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L t) :
    Stacks.Zeta.genericCoord X L s hs t ≠ 0 := by
  intro h0
  have h00 := Stacks.Zeta.genericCoord_add X L s hs 0 0
  rw [add_zero, left_eq_add] at h00
  have ht0 : t = 0 := Stacks.Zeta.genericCoord_injective X L s hs (h0.trans h00.symm)
  obtain ⟨w, hw⟩ := Stacks.SectionProduct.exists_notMem_maximalSmul L x
  obtain ⟨r, hr⟩ := (Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates L t x).1 ht w
  apply hw
  rw [hr, ht0, map_zero, smul_zero]
  exact zero_mem _

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- At a point of codimension one where the global section `t` of the invertible module `L` does
not vanish, the coordinate `ρ(t)` of `t` against a regular meromorphic section `s` has order
`-ord_Z(s)`. -/
private theorem ord_genericCoord_add_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (Z : PrimeDivisor X) [IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)]
    (t : Γ(L, ⊤)) (ht : Z.genericPoint ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L t) :
    X.ord (Stacks.Zeta.genericCoord X L s hs t) Z.genericPoint +
      orderOfVanishingMeromorphic X L s hs Z = 0 := by
  have hx1 := PrimeDivisor.coheight_genericPoint Z
  have hgen := (Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates L t
    Z.genericPoint).1 ht
  have ha0 := genericCoord_ne_zero L s hs ht
  have hge := (Stacks.Zeta.genericCoord_mem X L s hs t Z).resolve_left ha0
  refine le_antisymm ?_ hge
  by_contra hlt
  push Not at hlt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk Z.genericPoint)
  have hπ0 : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  have hπ1 := Stacks.BombieriStepanov.ord_algebraMap_irreducible hx1 hϖ
  set πK := algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField ϖ with hπK
  set a := Stacks.Zeta.genericCoord X L s hs t with ha
  set b := a * πK⁻¹ with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hπ0)
  have hab : a = b * πK := by rw [hb, inv_mul_cancel_right₀ hπ0]
  have hordb : X.ord a Z.genericPoint = X.ord b Z.genericPoint + 1 := by
    rw [hab, Scheme.ord_mul hb0 hπ0, hπ1]
  obtain ⟨m, hm⟩ := (Stacks.Zeta.mem_range_stalkSpecializes_iff X L s hs Z hb0).2 (by omega)
  obtain ⟨r, hr⟩ := hgen m
  have hsp : L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
      (Set.mem_univ Z.genericPoint)) ((L.presheaf.Γgerm Z.genericPoint).hom t) =
      a • Stacks.Zeta.genericValue X L s := by
    rw [ha, ← Stacks.Zeta.genericCoord_spec X L s hs t]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [hr, Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ r _, hsp, smul_smul] at hm
  have hrb : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField r * a = b :=
    smul_left_injective X.functionField (Stacks.Zeta.genericValue_ne_zero X L s hs) hm
  have h1 : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField (r * ϖ) = 1 := by
    rw [map_mul, ← hπK]
    rw [hab] at hrb
    exact mul_right_cancel₀ hb0 (by linear_combination hrb)
  have h2 : r * ϖ = 1 :=
    (IsFractionRing.injective (X.presheaf.stalk Z.genericPoint) X.functionField)
      (h1.trans (map_one _).symm)
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one r (by rw [mul_comm]; exact h2))

/-- If `t = a t₀` on an open `U` containing the generic point, then `ρ(t) = a ρ(t₀)`. -/
private theorem genericCoord_eq_of_resT {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    {U : X.Opens} (hU : genericPoint X ∈ U) {t t₀ : Γ(L, ⊤)} {a : Γ(X, U)}
    (h : Stacks.ProjectiveFromSections.resT U t = a • Stacks.ProjectiveFromSections.resT U t₀) :
    Stacks.Zeta.genericCoord X L s hs t =
      X.presheaf.germ U (genericPoint X) hU a * Stacks.Zeta.genericCoord X L s hs t₀ := by
  have hg : ∀ x : Γ(L, ⊤), L.presheaf.germ ⊤ (genericPoint X) trivial x =
      L.presheaf.germ U (genericPoint X) hU (Stacks.ProjectiveFromSections.resT U x) := fun x =>
    (TopCat.Presheaf.germ_res_apply _ _ _ _ x).symm
  have e1 : Stacks.Zeta.genericCoord X L s hs t = (Stacks.Zeta.genericBasisEquiv X L s hs).symm
      (L.presheaf.germ ⊤ (genericPoint X) trivial t) := rfl
  have e2 : Stacks.Zeta.genericCoord X L s hs t₀ = (Stacks.Zeta.genericBasisEquiv X L s hs).symm
      (L.presheaf.germ ⊤ (genericPoint X) trivial t₀) := rfl
  rw [e1, e2, hg t, h, Stacks.ModuleStalk.germ_smul L _ U hU a, map_smul, ← hg]
  rfl

end GenericCoord

/-! ### Riemann–Roch spaces of multiples of `P` -/

section RiemannRoch

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
  [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]

/-- The divisor `D` read on the closed points. -/
private noncomputable def closedDivisor (D : C →₀ ℤ) : Stacks.Zeta.ClosedPoint C →₀ ℤ :=
  Finsupp.comapDomain Subtype.val D Subtype.val_injective.injOn

omit [IsLocallyNoetherian C] in
private theorem closedDivisor_apply (D : C →₀ ℤ) (x : Stacks.Zeta.ClosedPoint C) :
    closedDivisor D x = D x.1 := rfl

omit [GeometricallyIntegral f] [IsLocallyNoetherian C] in
/-- The degree of the class of a closed point is its residue degree. -/
private theorem picardDegree_pointClass_eq (x : Stacks.Zeta.ClosedPoint C) :
    Stacks.Picard.picardDegree f (Stacks.Zeta.topologicalKrullDim_le_one f)
      (Stacks.Zeta.pointClass f x) = f.residueDegree x.1 := by
  have := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal f x
  have hdeg := Stacks.Picard.picardDegree_divisorPicardClass f
    (Stacks.Zeta.topologicalKrullDim_le_one f) (Stacks.Zeta.pointIdeal x)
  have hI : IsIntegral (Stacks.Zeta.pointIdeal x).subscheme :=
    isIntegral_subscheme_vanishingIdeal x.2
  have hS : Subsingleton (Stacks.Zeta.pointIdeal x).subscheme :=
    subsingleton_subscheme_vanishingIdeal x.2
  obtain ⟨η⟩ : Nonempty (Stacks.Zeta.pointIdeal x).subscheme :=
    nonempty_subscheme_vanishingIdeal x.2
  have hres := Stacks.Chow.residueDegree_eq_finrank_globalSections k
    ((Stacks.Zeta.pointIdeal x).subschemeι ≫ f) η
  rw [residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isPreimmersion (Stacks.Zeta.pointIdeal x).subschemeι,
    mul_one] at hres
  have hpt : (Stacks.Zeta.pointIdeal x).subschemeι η = x.1 :=
    (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal
      (⟨{x.1}, x.2⟩ : TopologicalSpace.Closeds C)).subset ⟨η, rfl⟩
  rw [hpt] at hres
  change Stacks.Picard.picardDegree f _ (Stacks.Divisors.picardClass _) = _
  rw [hdeg, ← hres]

omit [GeometricallyIntegral f] [IsLocallyNoetherian C] in
/-- The degree of the class of a divisor on the closed points. -/
private theorem picardDegree_divisorClass_eq (D : Stacks.Zeta.ClosedPoint C →₀ ℤ) :
    Stacks.Picard.picardDegree f (Stacks.Zeta.topologicalKrullDim_le_one f)
      (Stacks.Zeta.divisorClass f D) = D.sum fun x n => n * (f.residueDegree x.1 : ℤ) := by
  rw [Stacks.Zeta.divisorClass_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_zsmul, picardDegree_pointClass_eq, smul_eq_mul]

/-- **Riemann–Roch in large degree.** -/
private theorem finrank_rrSpace_eq (D : Stacks.Zeta.ClosedPoint C →₀ ℤ)
    (hD : 2 * (genus f : ℤ) - 1 ≤ D.sum fun x n => n * (f.residueDegree x.1 : ℤ)) :
    letI := functionFieldAlgebra k f
    (Module.finrank k (Stacks.Zeta.rrSpace f D) : ℤ) =
      (D.sum fun x n => n * (f.residueDegree x.1 : ℤ)) + 1 - genus f := by
  let := functionFieldAlgebra k f
  have hdim := Stacks.Zeta.topologicalKrullDim_le_one f
  rw [Stacks.Zeta.finrank_rrSpace f D, ← picardDegree_divisorClass_eq f D]
  rw [← picardDegree_divisorClass_eq f D] at hD
  set c := Stacks.Zeta.divisorClass f D
  have hL := (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  set L := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L := hL
  have hL' : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L := hL
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  have hvan := isZero_cohomologyOverField_one_of_geometricallyIntegral k f L hL' hD
  have h1 : Module.finrank k (cohomologyOverField k f L 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero hvan
    exact Module.finrank_zero_of_subsingleton
  rw [h1, Nat.cast_zero, sub_zero] at hRR
  exact hRR

omit [GeometricallyIntegral f] in
/-- Membership in `L(D)` for a divisor `D` on `C`, in the form of the statement. -/
private theorem mem_rrSpace_closedDivisor {D : C →₀ ℤ} {g : C.functionField} :
    letI := functionFieldAlgebra k f
    g ∈ Stacks.Zeta.rrSpace f (closedDivisor D) ↔
      g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q := by
  let := functionFieldAlgebra k f
  rw [Stacks.Zeta.mem_rrSpace]
  simp only [Subtype.forall, closedDivisor_apply]

omit [IsCurve k f] [IsLocallyNoetherian C] [GeometricallyIntegral f] [IsProjectiveVariety k f]
  [Smooth f] in
/-- The degree of `e • P` is `e` when `P` has degree one. -/
private theorem sum_closedDivisor_smul (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (e : ℤ) :
    ((closedDivisor (e • P)).sum fun x m => m * (f.residueDegree x.1 : ℤ)) = e := by
  classical
  have hsupp : ∀ Q ∈ (e • P).support, IsClosed ({Q} : Set C) := fun Q hQ =>
    hPclosed Q (Finsupp.support_smul hQ)
  have h1 : ((closedDivisor (e • P)).sum fun x m => m * (f.residueDegree x.1 : ℤ)) =
      ∑ Q ∈ (e • P).support, (e • P) Q * (f.residueDegree Q : ℤ) := by
    rw [Finsupp.sum, closedDivisor, Finsupp.comapDomain_support]
    refine Finset.sum_preimage Subtype.val _ _
      (fun Q => (e • P) Q * (f.residueDegree Q : ℤ)) fun Q hQ hQr => ?_
    exact absurd ⟨⟨Q, hsupp Q hQ⟩, rfl⟩ hQr
  have h2 : ∑ᶠ Q : C, (e • P) Q * (f.residueDegree Q : ℤ) =
      ∑ Q ∈ (e • P).support, (e • P) Q * (f.residueDegree Q : ℤ) := by
    refine finsum_eq_sum_of_support_subset _ fun Q hQ => ?_
    simp only [Function.mem_support, ne_eq] at hQ
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hQ (by rw [h0, zero_mul])
  have h3 : ∑ᶠ Q : C, (e • P) Q * (f.residueDegree Q : ℤ) =
      e * ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) := by
    rw [mul_finsum]
    · refine finsum_congr fun Q => ?_
      rw [Finsupp.smul_apply, smul_eq_mul, mul_assoc]
  rw [h1, ← h2, h3, hP, mul_one]

/-- **Riemann–Roch for `L(e P)`**: if `deg P = 1` and `e ≥ 2g - 1`, then
`dim L(e P) = e + 1 - g`. -/
private theorem finrank_rrSpace_smul (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (e : ℤ)
    (he : 2 * (genus f : ℤ) - 1 ≤ e) :
    letI := functionFieldAlgebra k f
    (Module.finrank k (Stacks.Zeta.rrSpace f (closedDivisor (e • P))) : ℤ) =
      e + 1 - genus f := by
  have h := finrank_rrSpace_eq f (closedDivisor (e • P))
    (by rw [sum_closedDivisor_smul f P hPclosed hP]; exact he)
  rwa [sum_closedDivisor_smul f P hPclosed hP] at h

/-- The sections of `𝒪(D)` vanishing at the closed point `Q`. -/
private noncomputable def vanishingSpace (D : Stacks.Zeta.ClosedPoint C →₀ ℤ)
    (Q : Stacks.Zeta.ClosedPoint C) :
    letI := functionFieldAlgebra k f
    Submodule k C.functionField :=
  Stacks.Zeta.rrSpace f (D - Finsupp.single Q 1)

omit [GeometricallyIntegral f] in
/-- A section of `𝒪(D)` with a zero at `Q` lies in `vanishingSpace f D Q`. -/
private theorem mem_vanishingSpace_of (D : Stacks.Zeta.ClosedPoint C →₀ ℤ)
    {Q : Stacks.Zeta.ClosedPoint C} {g : C.functionField}
    (hg : letI := functionFieldAlgebra k f; g ∈ Stacks.Zeta.rrSpace f D)
    (hQ : 0 < C.ord g Q.1 + D Q) :
    letI := functionFieldAlgebra k f
    g ∈ vanishingSpace f D Q := by
  let := functionFieldAlgebra k f
  rcases (Stacks.Zeta.mem_rrSpace f).1 hg with h0 | hall
  · exact (Stacks.Zeta.mem_rrSpace f).2 (Or.inl h0)
  refine (Stacks.Zeta.mem_rrSpace f).2 (Or.inr fun x => ?_)
  by_cases hx : x = Q
  · subst hx
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_of_ne hx, sub_zero]
    exact hall x

omit [GeometricallyIntegral f] in
/-- If `D` has the class of the invertible module `L` and `s` is a regular meromorphic section of
`L`, then `D = div s + div h` for some `h ≠ 0`, and `h⁻¹ ρ(u) ∈ L(D)` for every global section
`u` of `L`. -/
private theorem exists_eq_sectionDivisor_add_divOf (D : Stacks.Zeta.ClosedPoint C →₀ ℤ)
    (L : C.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
    (hL : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L)
    (hc : Stacks.SheafOfModules.picardClass C.sheaf.obj C.ringCatSheaf.property L hL =
      Stacks.Zeta.divisorClass f D)
    (s : MeromorphicSection C.sheaf L) (hs : IsRegularMeromorphicSection C.sheaf L s) :
    letI := functionFieldAlgebra k f
    ∃ (h : C.functionField) (hh : h ≠ 0),
      D = Stacks.Zeta.sectionDivisor f L s hs + Stacks.Zeta.divOf f hh ∧
      ∀ u : Γ(L, ⊤), h⁻¹ * Stacks.Zeta.genericCoord C L s hs u ∈ Stacks.Zeta.rrSpace f D := by
  let := functionFieldAlgebra k f
  obtain ⟨h, hh, hhD⟩ := Stacks.Zeta.exists_divOf_eq_of_divisorClass_eq_zero f
    (D := D - Stacks.Zeta.sectionDivisor f L s hs)
    (by rw [map_sub, Stacks.Zeta.divisorClass_sectionDivisor f L s hs hL, hc, sub_self])
  have hD : D = Stacks.Zeta.sectionDivisor f L s hs + Stacks.Zeta.divOf f hh := by
    rw [hhD]; abel
  refine ⟨h, hh, hD, fun u => ?_⟩
  rw [hD, Stacks.Zeta.mem_rrSpace_add_divOf_iff f hh, mul_inv_cancel_left₀ hh,
    ← Stacks.Zeta.range_coordLinear f L s hs]
  exact ⟨u, rfl⟩

/-- **Global generation.** If `deg D ≥ 2g`, then for every closed point `Q` some section of
`𝒪(D)` does not vanish at `Q`. -/
private theorem exists_mem_rrSpace_notMem_vanishingSpace (D : Stacks.Zeta.ClosedPoint C →₀ ℤ)
    (hD : 2 * (genus f : ℤ) ≤ D.sum fun x n => n * (f.residueDegree x.1 : ℤ))
    (Q : Stacks.Zeta.ClosedPoint C) :
    letI := functionFieldAlgebra k f
    ¬ Stacks.Zeta.rrSpace f D ≤ vanishingSpace f D Q := by
  let := functionFieldAlgebra k f
  rw [← picardDegree_divisorClass_eq f D] at hD
  set c := Stacks.Zeta.divisorClass f D
  have hL := (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  set L : C.Modules := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
  have : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L := hL
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  have : Stacks.Ample.IsInvertibleModule C L := hL
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  -- `L` is generated by its global sections, so some section does not vanish at `Q`
  let S : CohenMacaulayCurveSituation :=
    { k := k, X := C, f := f
      dimension_one := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f) }
  have hgg := S.isGeneratedByGlobalSections_of_two_mul_genus_le L hD
  have hgen := generatesStalks_id_of_isGeneratedByGlobalSections L hgg
  obtain ⟨t, ht⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks id hgen Q.1
  -- a regular meromorphic section `s` of `L`, and `D = div s + div h`
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral C L
  obtain ⟨h, hh, hD', hmem⟩ := exists_eq_sectionDivisor_add_divOf f D L hL
    (Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c) s hs
  -- the coordinate of `t` has the exact order `-ord(s)` at `Q`
  set Z := Stacks.Zeta.primeDivisorOfClosedPoint f Q
  have hZ : Z.genericPoint = Q.1 := PrimeDivisor.genericPoint_ofCoheightOne _ _
  have : IsDiscreteValuationRing (C.presheaf.stalk Z.genericPoint) :=
    Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one f _
      (PrimeDivisor.coheight_genericPoint Z)
  have hord := ord_genericCoord_add_eq_zero L s hs Z t (by rw [hZ]; exact ht)
  rw [hZ] at hord
  set a := Stacks.Zeta.genericCoord C L s hs t
  have ha0 : a ≠ 0 := genericCoord_ne_zero L s hs ht
  -- the section `v = a / h` of `𝒪(D)` does not vanish at `Q`
  intro hle
  have hvmem : h⁻¹ * a ∈ Stacks.Zeta.rrSpace f D := hmem t
  have hv0 : h⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hh) ha0
  have hvan := ((Stacks.Zeta.mem_rrSpace f).1 (hle hvmem)).resolve_left hv0 Q
  have hmul : C.ord a Q.1 = C.ord h Q.1 + C.ord (h⁻¹ * a) Q.1 := by
    have := Stacks.Zeta.dvr_closedPoint f Q
    rw [← Scheme.ord_mul hh hv0, mul_inv_cancel_left₀ hh]
  have hDQ : D Q = Stacks.Zeta.sectionDivisor f L s hs Q + C.ord h Q.1 := by
    rw [hD', Finsupp.add_apply, Stacks.Zeta.divOf_apply]
  rw [Stacks.Zeta.sectionDivisor_apply] at hDQ
  change D Q = orderOfVanishingMeromorphic C L s hs Z + C.ord h Q.1 at hDQ
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at hvan
  linarith

end RiemannRoch

/-! ### Products of sections of `𝒪(D)` -/

section Products

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]

/-- `g ∈ L(D)`: `g = 0` or `ord_Q g + D(Q) ≥ 0` at every closed point `Q`. -/
private def InL (D : C →₀ ℤ) (g : C.functionField) : Prop :=
  g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q

private theorem ord_one (Q : C) : C.ord (1 : C.functionField) Q = 0 := by
  have h := Scheme.ord_mul (x := Q) (one_ne_zero (α := C.functionField))
    (one_ne_zero (α := C.functionField))
  rw [mul_one] at h
  omega

private theorem inL_one : InL (0 : C →₀ ℤ) (1 : C.functionField) :=
  Or.inr fun Q _ => by simp

private theorem InL.mul {D D' : C →₀ ℤ} {g g' : C.functionField} (hg : InL D g)
    (hg' : InL D' g') : InL (D + D') (g * g') := by
  rcases hg with rfl | hg
  · exact Or.inl (zero_mul _)
  rcases hg' with rfl | hg'
  · exact Or.inl (mul_zero _)
  by_cases h0 : g = 0
  · exact Or.inl (by rw [h0, zero_mul])
  by_cases h0' : g' = 0
  · exact Or.inl (by rw [h0', mul_zero])
  refine Or.inr fun Q hQ => ?_
  rw [Scheme.ord_mul h0 h0', Finsupp.add_apply]
  have := hg Q hQ
  have := hg' Q hQ
  omega

private theorem InL.pow {D : C →₀ ℤ} {g : C.functionField} (hg : InL D g) (e : ℕ) :
    InL ((e : ℤ) • D) (g ^ e) := by
  induction e with
  | zero => simpa using (inL_one : InL (0 : C →₀ ℤ) 1)
  | succ e ih =>
    have := ih.mul hg
    rwa [pow_succ, Nat.cast_succ, add_smul, one_smul]

/-- A product `∏_{ν ∈ s} x_ν ^ a_ν` of sections of `𝒪(D)` is a section of
`𝒪((∑_{ν ∈ s} a_ν) D)`. -/
private theorem inL_prod_finset {ι : Type*} {D : C →₀ ℤ} {x : ι → C.functionField}
    (hx : ∀ ν, InL D (x ν)) (a : ι → ℕ) (s : Finset ι) :
    InL (((∑ ν ∈ s, a ν : ℕ) : ℤ) • D) (∏ ν ∈ s, x ν ^ a ν) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inL_one : InL (0 : C →₀ ℤ) 1)
  | insert ν s hν ih =>
    rw [Finset.prod_insert hν, Finset.sum_insert hν, Nat.cast_add, add_smul]
    exact ((hx ν).pow _).mul ih

/-- A product of `|a|` sections of `𝒪(D)` is a section of `𝒪(|a| D)`. -/
private theorem inL_prod {ι : Type*} {D : C →₀ ℤ} {x : ι → C.functionField}
    (hx : ∀ ν, InL D (x ν)) (a : ι →₀ ℕ) :
    InL ((a.degree : ℤ) • D) (a.prod fun ν e => x ν ^ e) :=
  inL_prod_finset hx a a.support

/-- If the span of `ℓ` is `L(D)`, membership in the span is `InL D`. -/
private theorem mem_span_iff_inL {k ι : Type*} [Field k] [Algebra k C.functionField]
    {ℓ : ι → C.functionField} {D : C →₀ ℤ}
    (hspan : ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) :
      Set C.functionField) = {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    {g : C.functionField} : g ∈ Submodule.span k (Set.range ℓ) ↔ InL D g :=
  Set.ext_iff.mp hspan g

private theorem ord_pow_eq {g : C.functionField} (hg : g ≠ 0) (Q : C) (e : ℕ) :
    C.ord (g ^ e) Q = e * C.ord g Q := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero e hg) hg, ih]
    push_cast
    ring

private theorem ord_inv_eq {g : C.functionField} (hg : g ≠ 0) (Q : C) :
    C.ord g⁻¹ Q = - C.ord g Q := by
  have h := Scheme.ord_mul (x := Q) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, ord_one] at h
  omega

private theorem ord_div_eq {g g' : C.functionField} (hg : g ≠ 0) (hg' : g' ≠ 0) (Q : C) :
    C.ord (g / g') Q = C.ord g Q - C.ord g' Q := by
  rw [div_eq_mul_inv, Scheme.ord_mul hg (inv_ne_zero hg'), ord_inv_eq hg']
  ring

end Products

/-! ### The evaluation of forms is a sum of products -/

section Upper

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  (pr₁ pr₂ : K →ₐ[k] L)

/-- The multiplication map `W₁ ⊗ W₂ → L`, `a ⊗ b ↦ pr₁ a · pr₂ b`. -/
private noncomputable def boxMul (W₁ W₂ : Submodule k K) : W₁ ⊗[k] W₂ →ₗ[k] L :=
  TensorProduct.lift ((LinearMap.mul k L).compl₁₂ (pr₁.toLinearMap ∘ₗ W₁.subtype)
    (pr₂.toLinearMap ∘ₗ W₂.subtype))

/-- `F(ξ, ξ')` as a sum over the monomials of `F`. -/
private theorem affineEvaluation_eq_sum {ι : Type*} [Fintype ι] (x : ι → K) (j : ι)
    (δ : ℕ × ℕ) (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ) :
    affineEvaluation pr₁ pr₂ x j δ F = ∑ α ∈ F.1.support, F.1.coeff α •
      (pr₁ ((α.comapDomain Sum.inl Sum.inl_injective.injOn).prod
          (fun ν e => x ν ^ e) / x j ^ δ.1) *
        pr₂ ((α.comapDomain Sum.inr Sum.inr_injective.injOn).prod
          (fun ν e => x ν ^ e) / x j ^ δ.2)) := by
  classical
  obtain ⟨F, hF⟩ := F
  change MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) F /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2) = _
  conv_lhs => rw [F.as_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial, Algebra.smul_def, map_div₀, map_div₀, map_pow, map_pow,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_prod]
  simp only [Sum.elim_inl, Sum.elim_inr, Finsupp.comapDomain_apply, map_pow]
  ring

/-- The values `F(ξ, ξ')` of forms of bidegree `(δ₁, δ₂)` are sums of products
`pr₁ a · pr₂ b` with `a ∈ W₁`, `b ∈ W₂`, as soon as `W_i` contains the monomials of degree `δ_i`
in `ξ = x / x_j`. -/
private theorem range_affineEvaluation_le {ι : Type*} [Fintype ι] (x : ι → K) (j : ι)
    (δ : ℕ × ℕ) (W₁ W₂ : Submodule k K)
    (h₁ : ∀ a : ι →₀ ℕ, a.degree = δ.1 → (a.prod fun ν e => x ν ^ e) / x j ^ δ.1 ∈ W₁)
    (h₂ : ∀ a : ι →₀ ℕ, a.degree = δ.2 → (a.prod fun ν e => x ν ^ e) / x j ^ δ.2 ∈ W₂) :
    LinearMap.range (affineEvaluation pr₁ pr₂ x j δ) ≤ LinearMap.range (boxMul pr₁ pr₂ W₁ W₂) := by
  rintro _ ⟨F, rfl⟩
  rw [affineEvaluation_eq_sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  have hw := degree_comapDomain_of_weight (F.2 (MvPolynomial.mem_support_iff.mp hα))
  exact ⟨⟨_, h₁ _ hw.1⟩ ⊗ₜ ⟨_, h₂ _ hw.2⟩, rfl⟩

/-- `F(ξ, ξ')` does not change when `x` is replaced by `x / x_j`. -/
public theorem affineEvaluation_div {ι : Type*} [Fintype ι] (x : ι → K) (j : ι) (hj : x j ≠ 0)
    (δ : ℕ × ℕ) :
    affineEvaluation pr₁ pr₂ (fun ν => x ν / x j) j δ = affineEvaluation pr₁ pr₂ x j δ := by
  classical
  refine LinearMap.ext fun F => ?_
  rw [affineEvaluation_eq_sum, affineEvaluation_eq_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hw := degree_comapDomain_of_weight (δ₁ := δ.1) (δ₂ := δ.2)
    (F.2 (MvPolynomial.mem_support_iff.mp hα))
  have key : ∀ (β : ι →₀ ℕ) (d : ℕ), β.degree = d →
      (β.prod fun ν e => (x ν / x j) ^ e) / (x j / x j) ^ d =
        (β.prod fun ν e => x ν ^ e) / x j ^ d := by
    intro β d hβ
    rw [div_self hj, one_pow, div_one]
    simp_rw [div_pow]
    rw [Finsupp.prod, Finsupp.prod, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← hβ]
    rfl
  rw [key _ _ hw.1, key _ _ hw.2]

end Upper

/-! ### The upper bound -/

section UpperCurve

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
  [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]

/-- The space `W_δ = x_j^{-δ} L(δ N P)`. -/
private noncomputable def shiftedRRSpace (P : C →₀ ℤ) (N : ℕ) {ι : Type*} (x : ι → C.functionField)
    (j : ι) (δ : ℕ) :
    letI := functionFieldAlgebra k f
    Submodule k C.functionField :=
  letI := functionFieldAlgebra k f
  (Stacks.Zeta.rrSpace f (closedDivisor (((N * δ : ℕ) : ℤ) • P))).map
    (LinearMap.mulLeft k (x j ^ δ)⁻¹)

omit [GeometricallyIntegral f] in
/-- The monomials of degree `δ` in `ξ = x / x_j` lie in `x_j^{-δ} L(δ N P)`. -/
private theorem prod_div_mem_shiftedRRSpace (P : C →₀ ℤ) (N : ℕ) {ι : Type*}
    (x : ι → C.functionField) (hx : ∀ ν, InL ((N : ℤ) • P) (x ν)) (j : ι) (δ : ℕ)
    (a : ι →₀ ℕ) (ha : a.degree = δ) :
    letI := functionFieldAlgebra k f
    (a.prod fun ν e => x ν ^ e) / x j ^ δ ∈ shiftedRRSpace k f P N x j δ := by
  let := functionFieldAlgebra k f
  refine ⟨a.prod fun ν e => x ν ^ e, ?_, by simp [div_eq_inv_mul]⟩
  have h := inL_prod hx a
  rw [ha, smul_smul] at h
  refine (mem_rrSpace_closedDivisor f).2 ?_
  have e : (((N * δ : ℕ) : ℤ)) = (δ : ℤ) * N := by push_cast; ring
  rw [e]
  exact h

/-- `dim W_δ = N δ + 1 - g`. -/
private theorem finrank_shiftedRRSpace (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) {ι : Type*}
    (x : ι → C.functionField) (j : ι) (hj : x j ≠ 0) (δ : ℕ)
    (hδ : 2 * (genus f : ℤ) - 1 ≤ N * δ) :
    letI := functionFieldAlgebra k f
    (finrank k (shiftedRRSpace k f P N x j δ) : ℤ) = N * δ + 1 - genus f := by
  let := functionFieldAlgebra k f
  have hinj : Function.Injective (LinearMap.mulLeft k (x j ^ δ)⁻¹) := fun a b h =>
    mul_left_cancel₀ (inv_ne_zero (pow_ne_zero δ hj)) h
  have e := (Submodule.equivMapOfInjective _ hinj
    (Stacks.Zeta.rrSpace f (closedDivisor (((N * δ : ℕ) : ℤ) • P)))).finrank_eq
  have h := finrank_rrSpace_smul f P hPclosed hP ((N * δ : ℕ) : ℤ) (by push_cast; exact hδ)
  calc (finrank k (shiftedRRSpace k f P N x j δ) : ℤ)
      = finrank k (Stacks.Zeta.rrSpace f (closedDivisor (((N * δ : ℕ) : ℤ) • P))) := by
        exact_mod_cast e.symm
    _ = _ := by rw [h]; push_cast; ring

/-- `W_δ` is finite-dimensional. -/
private theorem finiteDimensional_shiftedRRSpace (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) {ι : Type*}
    (x : ι → C.functionField) (j : ι) (hj : x j ≠ 0) (δ : ℕ)
    (hδ : 2 * (genus f : ℤ) - 1 ≤ N * δ) :
    letI := functionFieldAlgebra k f
    FiniteDimensional k (shiftedRRSpace k f P N x j δ) := by
  let := functionFieldAlgebra k f
  have e := finrank_shiftedRRSpace k f P hPclosed hP N x j hj δ hδ
  have : (0 : ℤ) ≤ N * δ := by positivity
  exact FiniteDimensional.of_finrank_pos (by omega)

omit [GeometricallyIntegral f] in
/-- The values `F(ξ, ξ')` lie in the image of `W_{δ₁} ⊗ W_{δ₂}`. -/
private theorem range_affineEvaluation_le_boxMul (P : C →₀ ℤ) (N : ℕ) {n : ℕ}
    (ℓ : Fin (n + 1) → C.functionField) (hℓ : ∀ ν, InL ((N : ℤ) • P) (ℓ ν))
    (j : Fin (n + 1)) {L : Type*} [Field L] [Algebra k L]
    (pr₁ pr₂ : letI := functionFieldAlgebra k f; C.functionField →ₐ[k] L) (δ₁ δ₂ : ℕ) :
    letI := functionFieldAlgebra k f
    LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂)) ≤ LinearMap.range
      (boxMul pr₁ pr₂ (shiftedRRSpace k f P N ℓ j δ₁) (shiftedRRSpace k f P N ℓ j δ₂)) :=
  letI := functionFieldAlgebra k f
  range_affineEvaluation_le pr₁ pr₂ ℓ j (δ₁, δ₂) _ _
    (prod_div_mem_shiftedRRSpace k f P N ℓ hℓ j δ₁) (prod_div_mem_shiftedRRSpace k f P N ℓ hℓ j δ₂)

/-- **The upper bound** `dim {F(ξ, ξ')} ≤ (N δ₁ + 1 - g)(N δ₂ + 1 - g)`. -/
private theorem finrank_range_affineEvaluation_le (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) {n : ℕ}
    (ℓ : Fin (n + 1) → C.functionField) (hℓ : ∀ ν, InL ((N : ℤ) • P) (ℓ ν))
    (j : Fin (n + 1)) (hj : ℓ j ≠ 0) {L : Type*} [Field L] [Algebra k L]
    (pr₁ pr₂ : letI := functionFieldAlgebra k f; C.functionField →ₐ[k] L) (δ₁ δ₂ : ℕ)
    (hδ₁ : 2 * (genus f : ℤ) - 1 ≤ N * δ₁) (hδ₂ : 2 * (genus f : ℤ) - 1 ≤ N * δ₂) :
    letI := functionFieldAlgebra k f
    (finrank k (LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂))) : ℤ) ≤
      (N * δ₁ + 1 - genus f) * (N * δ₂ + 1 - genus f) := by
  let := functionFieldAlgebra k f
  have := finiteDimensional_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₁ hδ₁
  have := finiteDimensional_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₂ hδ₂
  have : Module.Free k (shiftedRRSpace k f P N ℓ j δ₁) := Module.Free.of_divisionRing k _
  have : Module.Free k (shiftedRRSpace k f P N ℓ j δ₂) := Module.Free.of_divisionRing k _
  have h := (Submodule.finrank_mono (range_affineEvaluation_le_boxMul k f P N ℓ hℓ j pr₁ pr₂
    δ₁ δ₂)).trans (LinearMap.finrank_range_le _)
  rw [Module.finrank_tensorProduct (R := k) (S := k)] at h
  rw [← finrank_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₁ hδ₁,
    ← finrank_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₂ hδ₂]
  exact_mod_cast h

/-- The values `F(ξ, ξ')` span a finite-dimensional space. -/
private theorem finiteDimensional_range_affineEvaluation (P : C →₀ ℤ)
    (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) {n : ℕ}
    (ℓ : Fin (n + 1) → C.functionField) (hℓ : ∀ ν, InL ((N : ℤ) • P) (ℓ ν))
    (j : Fin (n + 1)) (hj : ℓ j ≠ 0) {L : Type*} [Field L] [Algebra k L]
    (pr₁ pr₂ : letI := functionFieldAlgebra k f; C.functionField →ₐ[k] L) (δ₁ δ₂ : ℕ)
    (hδ₁ : 2 * (genus f : ℤ) - 1 ≤ N * δ₁) (hδ₂ : 2 * (genus f : ℤ) - 1 ≤ N * δ₂) :
    letI := functionFieldAlgebra k f
    FiniteDimensional k (LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂))) := by
  let := functionFieldAlgebra k f
  have := finiteDimensional_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₁ hδ₁
  have := finiteDimensional_shiftedRRSpace k f P hPclosed hP N ℓ j hj δ₂ hδ₂
  exact Submodule.finiteDimensional_of_le (range_affineEvaluation_le_boxMul k f P N ℓ hℓ j pr₁ pr₂
    δ₁ δ₂)

end UpperCurve

/-- `Submodule.pi Set.univ (fun _ => W)` is linearly equivalent to `σ → W`. -/
private def piUnivEquiv {k M : Type*} [Semiring k] [AddCommMonoid M] [Module k M]
    (σ : Type*) (W : Submodule k M) :
    (Submodule.pi Set.univ fun _ : σ => W) ≃ₗ[k] (σ → W) where
  toFun y i := ⟨y.1 i, y.2 i trivial⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dimension of `Submodule.pi Set.univ (fun _ : σ => W)` is `|σ| · dim W`. -/
private lemma finrank_pi_univ_const {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (σ : Type*) [Fintype σ] (W : Submodule k M) [FiniteDimensional k W] :
    Module.finrank k (Submodule.pi Set.univ fun _ : σ => W) = Fintype.card σ * finrank k W := by
  rw [(piUnivEquiv σ W).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

/-! ### Coordinates of sections against a nonvanishing section -/

section Coord

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable (k : Type u) [Field k] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (.of k))]
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (s : Γ(M, ⊤)) {U : Y.Opens}
  (hU : U ≤ Stacks.ProjectiveFromSections.nvOpen M s) [Nonempty U]

/-- The coordinate `t ↦ (t / s)(η) ∈ K(Y)` of a global section `t` of the invertible `M` against
a section `s` that vanishes nowhere on the nonempty open `U`. -/
private noncomputable def coord :
    letI := stalkAlgebraOver k (Y ↘ Spec (.of k)) (genericPoint Y)
    Γ(M, ⊤) →ₗ[k] Y.functionField :=
  letI := stalkAlgebraOver k (Y ↘ Spec (.of k)) (genericPoint Y)
  { toFun := fun t => Y.germToFunctionField U (Stacks.ProjectiveFromSections.div s hU (resT U t))
    map_add' := fun t t' => by
      have h : Stacks.ProjectiveFromSections.div s hU (resT U (t + t')) =
          Stacks.ProjectiveFromSections.div s hU (resT U t) +
            Stacks.ProjectiveFromSections.div s hU (resT U t') :=
        (Stacks.ProjectiveFromSections.eq_div s hU (by
          rw [add_smul, Stacks.ProjectiveFromSections.div_smul,
            Stacks.ProjectiveFromSections.div_smul]
          exact (map_add _ t t').symm)).symm
      rw [h, map_add]
    map_smul' := fun c t => by
      have h : Stacks.ProjectiveFromSections.div s hU (resT U (c • t)) =
          resO (le_top : U ≤ ⊤)
              (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k Y c) *
            Stacks.ProjectiveFromSections.div s hU (resT U t) :=
        (Stacks.ProjectiveFromSections.eq_div s hU (by
          rw [mul_smul, Stacks.ProjectiveFromSections.div_smul]
          exact (Stacks.ProjectiveFromSections.resM_smul (le_top : U ≤ ⊤) _ t).symm)).symm
      rw [h, map_mul, RingHom.id_apply, Algebra.smul_def]
      congr 1
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _ }

/-- The coordinate of `t = a s` on `U` is the germ of `a`. -/
private theorem coord_eq {t : Γ(M, ⊤)} {a : Γ(Y, U)} (h : resT U t = a • resT U s) :
    letI := stalkAlgebraOver k (Y ↘ Spec (.of k)) (genericPoint Y)
    coord k M s hU t = Y.germToFunctionField U a := by
  change Y.germToFunctionField U (Stacks.ProjectiveFromSections.div s hU (resT U t)) = _
  rw [← Stacks.ProjectiveFromSections.eq_div _ _ h.symm]

private theorem coord_injective :
    letI := stalkAlgebraOver k (Y ↘ Spec (.of k)) (genericPoint Y)
    Function.Injective (coord k M s hU) := by
  let := stalkAlgebraOver k (Y ↘ Spec (.of k)) (genericPoint Y)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h0 : Stacks.ProjectiveFromSections.div s hU (resT U t) = 0 :=
    Scheme.germToFunctionField_injective Y U (ht.trans (map_zero _).symm)
  have h1 := Stacks.ProjectiveFromSections.div_smul s hU (resT U t)
  rw [h0, zero_smul] at h1
  exact eq_zero_of_res_eq_zero M (Set.nonempty_coe_sort.mp ‹Nonempty U›) t h1.symm

/-- Coordinates along a morphism `E : M' ⟶ M`: `(E t / s) = (t / s') · (E s' / s)`. -/
private theorem coord_map {M' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y M'] (E : M' ⟶ M)
    (s' : Γ(M', ⊤)) (hU' : U ≤ Stacks.ProjectiveFromSections.nvOpen M' s') (t : Γ(M', ⊤)) :
    coord k M s hU (E.app ⊤ t) = coord k M' s' hU' t * coord k M s hU (E.app ⊤ s') := by
  set a := Stacks.ProjectiveFromSections.div s' hU' (resT U t)
  set b := Stacks.ProjectiveFromSections.div s hU (resT U (E.app ⊤ s'))
  have hnat : ∀ x : Γ(M', ⊤), resT U (E.app ⊤ x) = E.app U (resT U x) := fun x =>
    (PresheafOfModules.naturality_apply E.val (homOfLE (le_top : U ≤ ⊤)).op x).symm
  have ha : resT U t = a • resT U s' := (Stacks.ProjectiveFromSections.div_smul s' hU' _).symm
  have hb : resT U (E.app ⊤ s') = b • resT U s :=
    (Stacks.ProjectiveFromSections.div_smul s hU _).symm
  have h : resT U (E.app ⊤ t) = (a * b) • resT U s := by
    rw [hnat, ha, Scheme.Modules.Hom.app_smul, ← hnat, hb, mul_smul]
  rw [coord_eq k M s hU h, map_mul]
  rfl

/-- `H⁰(X, M)` and `Γ(M, ⊤)` have the same dimension over `k`. -/
private lemma finrank_cohomologyOverField_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    Module.finrank k (cohomologyOverField k f M 0) = Module.finrank k Γ(M, ⊤) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let e : (restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).obj M) ≃ₗ[k] Γ(M, ⊤) :=
    { toFun := fun a => a
      invFun := fun a => a
      map_add' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_smul' := fun c a =>
        congrArg (fun r => (((Scheme.ΓSpecIso (.of k)).inv ≫ r).hom c) •
          (show Γ(M, ⊤) from a)) (appLE_top_top_eq_appTop f _) }
  exact ((cohomologyOverFieldZeroLinearIso k f M).toLinearEquiv.trans e).finrank_eq

end Coord

/-! ### Sections on `C` and on `C × C` -/

section Sections

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  MvPolynomial.gradedAlgebra

attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj
  Stacks.InvertiblePullback.isInvertibleModule_pullback in
/-- The coordinate of the box product `p₁^* σ ⊗ p₂^* τ` against `p₁^* s₁ ⊗ p₂^* s₂` is
`p₁^*(σ / s₁) · p₂^*(τ / s₂)`. -/
private theorem coord_prodSection (k : Type u) [Field k] {X C : Scheme.{u}} [IsIntegral X]
    [IsIntegral C] [X.Over (Spec (.of k))] [C.Over (Spec (.of k))] (p₁ p₂ : X ⟶ C)
    [IsDominant p₁] [IsDominant p₂] (M₁ M₂ : C.Modules) [Stacks.Ample.IsInvertibleModule C M₁]
    [Stacks.Ample.IsInvertibleModule C M₂] (s₁ : Γ(M₁, ⊤)) (s₂ : Γ(M₂, ⊤)) {U₁ U₂ : C.Opens}
    (hU₁ : U₁ ≤ Stacks.ProjectiveFromSections.nvOpen M₁ s₁)
    (hU₂ : U₂ ≤ Stacks.ProjectiveFromSections.nvOpen M₂ s₂) [Nonempty U₁] [Nonempty U₂]
    {W : X.Opens} [Nonempty W] (hW₁ : W ≤ p₁ ⁻¹ᵁ U₁) (hW₂ : W ≤ p₂ ⁻¹ᵁ U₂)
    (hW : W ≤ Stacks.ProjectiveFromSections.nvOpen _ (Stacks.ProductFamilyTwist.prodSection
      (pullbackGlobalSections p₁ M₁ s₁) (pullbackGlobalSections p₂ M₂ s₂)))
    (σ : Γ(M₁, ⊤)) (τ : Γ(M₂, ⊤)) :
    coord k _ _ hW (Stacks.ProductFamilyTwist.prodSection (pullbackGlobalSections p₁ M₁ σ)
        (pullbackGlobalSections p₂ M₂ τ)) =
      functionFieldMap p₁ (coord k M₁ s₁ hU₁ σ) * functionFieldMap p₂ (coord k M₂ s₂ hU₂ τ) := by
  set a := Stacks.ProjectiveFromSections.div s₁ hU₁ (resT U₁ σ)
  set b := Stacks.ProjectiveFromSections.div s₂ hU₂ (resT U₂ τ)
  have ha : resT U₁ σ = a • resT U₁ s₁ := (Stacks.ProjectiveFromSections.div_smul s₁ hU₁ _).symm
  have hb : resT U₂ τ = b • resT U₂ s₂ := (Stacks.ProjectiveFromSections.div_smul s₂ hU₂ _).symm
  have h := resT_prodSection_eq_smul (T := W)
    (resT_eq_smul_of_le hW₁ (resT_pullbackGlobalSections_eq_smul p₁ ha))
    (resT_eq_smul_of_le hW₂ (resT_pullbackGlobalSections_eq_smul p₂ hb))
  rw [coord_eq k _ _ hW h, map_mul]
  have e₁ := Scheme.Hom.functionFieldMap_germToFunctionField p₁ hW₁ a
  have e₂ := Scheme.Hom.functionFieldMap_germToFunctionField p₂ hW₂ b
  exact congrArg₂ (· * ·) e₁.symm e₂.symm

end Sections

/-! ### `k(C)` and `k(C)` are linearly disjoint in `k(C × C)` -/

section Disjoint

/-- The ring of an affine open `U` of `C`, as a `k`-algebra through `f`. -/
private noncomputable abbrev affineAlgebra (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k))
    (U : C.Opens) : Algebra k Γ(C, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- If `C ×_k C` is integral, then `Γ(U) ⊗_k Γ(U)` is a domain for every nonempty affine open `U`
of `C`: it is the ring of the nonempty open `U ×_k U` of `C ×_k C`. -/
private theorem isDomain_tensorProduct_of_isAffineOpen (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)] {U : C.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := affineAlgebra k f U
    IsDomain (Γ(C, U) ⊗[k] Γ(C, U)) := by
  let := affineAlgebra k f U
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, U))) = hU.fromSpec ≫ f := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, ← Spec.map_comp]
    rfl
  let g : Spec (.of Γ(C, U)) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, U)))
  let ι : (pullback g g : Scheme.{u}) ⟶ pullback f f :=
    pullback.map g g f f hU.fromSpec hU.fromSpec (𝟙 _)
      (by rw [Category.comp_id]; exact hφ) (by rw [Category.comp_id]; exact hφ)
  have : Nontrivial (Γ(C, U) ⊗[k] Γ(C, U)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (RingHom.injective _) (RingHom.injective _)
  have : Nonempty (pullback g g : Scheme.{u}) :=
    ⟨(pullbackSpecIso k Γ(C, U) Γ(C, U)).inv.base (Nonempty.some inferInstance)⟩
  have := isIntegral_of_isOpenImmersion ι
  have : IsIntegral (Spec (.of (Γ(C, U) ⊗[k] Γ(C, U)))) :=
    IsIntegral.of_isIso (pullbackSpecIso k Γ(C, U) Γ(C, U)).hom
  exact (affine_isIntegral_iff (.of (Γ(C, U) ⊗[k] Γ(C, U)))).mp inferInstance

/-- If `A ⊗_k A` is a domain, so is `K ⊗_k K` for the fraction field `K` of `A`. -/
private theorem isDomain_tensorProduct_of_isFractionRing {k A K : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] (hA : IsDomain (A ⊗[k] A)) : IsDomain (K ⊗[k] K) := by
  classical
  let ι : A ⊗[k] A →ₐ[k] K ⊗[k] K :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A K) (IsScalarTower.toAlgHom k A K)
  have hι : Function.Injective ι :=
    TensorProduct.map_injective_of_flat_flat (IsScalarTower.toAlgHom k A K).toLinearMap
      (IsScalarTower.toAlgHom k A K).toLinearMap (IsFractionRing.injective A K)
      (IsFractionRing.injective A K)
  have hne : ∀ s : nonZeroDivisors A, algebraMap A K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hden : ∀ z : K ⊗[k] K, ∃ (s t : nonZeroDivisors A) (w : A ⊗[k] A),
      z * (algebraMap A K s ⊗ₜ algebraMap A K t) = ι w := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, 1, 0, by simp⟩
    | tmul a b =>
      obtain ⟨x, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) a
      obtain ⟨y, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      refine ⟨⟨s, hs⟩, ⟨t, ht⟩, x ⊗ₜ y, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, div_mul_cancel₀ _ (hne ⟨s, hs⟩),
        div_mul_cancel₀ _ (hne ⟨t, ht⟩)]
      rfl
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨s₁, t₁, w₁, hw₁⟩ := h₁
      obtain ⟨s₂, t₂, w₂, hw₂⟩ := h₂
      refine ⟨s₁ * s₂, t₁ * t₂, w₁ * ((s₂ : A) ⊗ₜ (t₂ : A)) + w₂ * ((s₁ : A) ⊗ₜ (t₁ : A)), ?_⟩
      have e : ∀ (s t : nonZeroDivisors A), ι ((s : A) ⊗ₜ (t : A)) =
          algebraMap A K s ⊗ₜ algebraMap A K t := fun _ _ => rfl
      rw [map_add, map_mul, map_mul, e, e, ← hw₁, ← hw₂, Submonoid.coe_mul, Submonoid.coe_mul,
        map_mul, map_mul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
  have hunit : ∀ s t : nonZeroDivisors A, IsUnit (algebraMap A K s ⊗ₜ[k] algebraMap A K t) :=
    fun s t => IsUnit.of_mul_eq_one ((algebraMap A K s)⁻¹ ⊗ₜ (algebraMap A K t)⁻¹) (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hne s), mul_inv_cancel₀ (hne t),
        Algebra.TensorProduct.one_def])
  have : Nontrivial (K ⊗[k] K) := hι.nontrivial
  have : NoZeroDivisors (K ⊗[k] K) := ⟨fun {z z'} h => by
    obtain ⟨s, t, w, hw⟩ := hden z
    obtain ⟨s', t', w', hw'⟩ := hden z'
    have h0 : ι (w * w') = 0 := by
      rw [map_mul, ← hw, ← hw', mul_mul_mul_comm, h, zero_mul]
    rcases mul_eq_zero.mp (hι (h0.trans (map_zero ι).symm)) with h1 | h1
    · left
      rw [h1, map_zero] at hw
      exact (hunit s t).mul_left_eq_zero.mp hw
    · right
      rw [h1, map_zero] at hw'
      exact (hunit s' t').mul_left_eq_zero.mp hw'⟩
  exact NoZeroDivisors.to_isDomain _

/-- Two additive maps out of a tensor product that agree on pure tensors are equal. -/
private theorem tensorProduct_coe_ext {R A B S F G : Type*} [CommSemiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [AddCommMonoid S] [FunLike F (A ⊗[R] B) S]
    [FunLike G (A ⊗[R] B) S] [AddMonoidHomClass F (A ⊗[R] B) S] [AddMonoidHomClass G (A ⊗[R] B) S]
    (f : F) (g : G) (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : ⇑f = ⇑g := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If `k(C) ⊗_k k(C)` is a domain, then `a ⊗ b ↦ pr₁^* a · pr₂^* b` is injective: the local
ring of `C ×_k C` at its generic point is a localization of `k(C) ⊗_k k(C)` at a prime. -/
private theorem injective_lift_functionFieldMapAlgHom (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)]
    [IsDominant (pullback.fst f f)] [IsDominant (pullback.snd f f)]
    (hdom : letI := stalkAlgebraOver k f (genericPoint C)
      IsDomain (C.functionField ⊗[k] C.functionField)) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    Function.Injective (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)) := by
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  have hx : pullback.fst f f (genericPoint (pullback f f : Scheme.{u})) = genericPoint C :=
    map_genericPoint_of_isDominant _
  have hy : pullback.snd f f (genericPoint (pullback f f : Scheme.{u})) = genericPoint C :=
    map_genericPoint_of_isDominant _
  obtain ⟨ψ₀, h₁, h₂, hloc₀⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct k f f
      (genericPoint (pullback f f : Scheme.{u}))
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensor_stalk_transport₂ k f f _ _ _ _ hx hy ψ₀ hloc₀
  have hψψ : ψ = (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)).toRingHom := by
    refine DFunLike.ext' (tensorProduct_coe_ext _ _ fun a b => ?_)
    rw [hψ, h₁, h₂]
    rfl
  have hinj : Function.Injective ψ := by
    let := ψ.toAlgebra
    have := hloc
    exact IsLocalization.injective (M := (Ideal.comap ψ
      (IsLocalRing.maximalIdeal (pullback f f : Scheme.{u}).functionField)).primeCompl)
      (pullback f f : Scheme.{u}).functionField (Ideal.primeCompl_le_nonZeroDivisors _)
  rw [hψψ] at hinj
  exact hinj

end Disjoint

/-! ### The lower bound -/

section LowerBound

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj
  Stacks.InvertiblePullback.isInvertibleModule_pullback
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- At a closed point, a nonzero `k`-combination of the `ℓ_μ` has order at least any common
lower bound of the orders of the `ℓ_μ`. -/
private theorem le_ord_of_mem_span (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [IsLocallyNoetherian C] {ι : Type*} [Fintype ι] (ℓ : ι → C.functionField)
    (hℓ0 : ∀ μ, ℓ μ ≠ 0) (Q : Stacks.Zeta.ClosedPoint C) {m : ℤ}
    (hm : ∀ μ, m ≤ C.ord (ℓ μ) Q.1) {g : C.functionField}
    (hg : letI := functionFieldAlgebra k f; g ∈ Submodule.span k (Set.range ℓ)) (hg0 : g ≠ 0) :
    m ≤ C.ord g Q.1 := by
  let := functionFieldAlgebra k f
  have := Stacks.Zeta.dvr_closedPoint f Q
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hg
  refine (Finset.sum_induction _ (fun x => x = 0 ∨ m ≤ C.ord x Q.1) ?_ (Or.inl rfl)
    fun i _ => ?_).resolve_left hg0
  · rintro x y (rfl | hx) (rfl | hy)
    · exact Or.inl (add_zero 0)
    · rw [zero_add]; exact Or.inr hy
    · rw [add_zero]; exact Or.inr hx
    · by_cases hxy : x + y = 0
      · exact Or.inl hxy
      · exact Or.inr ((le_min hx hy).trans (Scheme.ord_add hxy))
  · by_cases hai : a i = 0
    · exact Or.inl (by rw [hai, zero_smul])
    have ha0 : algebraMap k C.functionField (a i) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k C.functionField).injective).mpr hai
    have hc0 : C.ord (algebraMap k C.functionField (a i)) Q.1 = 0 :=
      Stacks.Zeta.ord_algebraMap_const f hai Q
    rw [Algebra.smul_def, Scheme.ord_mul ha0 (hℓ0 i), hc0, zero_add]
    exact Or.inr (hm i)

/-- **`|NP|` is base point free.** If `ℓ` spans `L(NP)` with `N ≥ 2g`, and `ℓ_ν` has the least
order among the `ℓ_μ` at the closed point `Q`, then `ord_Q ℓ_ν = -N P(Q)`. -/
private theorem ord_eq_neg_of_forall_ord_le (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f ≤ N)
    {ι : Type*} [Fintype ι] (ℓ : ι → C.functionField) (hℓ0 : ∀ μ, ℓ μ ≠ 0)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P) Q})
    (Q : Stacks.Zeta.ClosedPoint C) (ν : ι) (hmin : ∀ μ, C.ord (ℓ ν) Q.1 ≤ C.ord (ℓ μ) Q.1) :
    C.ord (ℓ ν) Q.1 = -(N * P Q.1) := by
  let := functionFieldAlgebra k f
  have hlow := ((mem_span_iff_inL hspan).1 (Submodule.subset_span ⟨ν, rfl⟩)).resolve_left
    (hℓ0 ν) Q.1 Q.2
  rw [Finsupp.smul_apply, smul_eq_mul] at hlow
  -- a section `g` of `𝒪(NP)` not vanishing at `Q`
  obtain ⟨g, hgL, hgv⟩ := SetLike.not_le_iff_exists.mp
    (exists_mem_rrSpace_notMem_vanishingSpace f (closedDivisor ((N : ℤ) • P))
      (by rw [sum_closedDivisor_smul f P hPclosed hP]; omega) Q)
  have hg0 : g ≠ 0 := by rintro rfl; exact hgv (zero_mem _)
  have hup : C.ord g Q.1 + N * P Q.1 ≤ 0 := by
    by_contra hcon
    refine hgv (mem_vanishingSpace_of f _ hgL ?_)
    rw [closedDivisor_apply, Finsupp.smul_apply, smul_eq_mul]
    omega
  have hcomb := le_ord_of_mem_span k f ℓ hℓ0 Q hmin
    ((mem_span_iff_inL hspan).2 ((mem_rrSpace_closedDivisor f).1 hgL)) hg0
  omega

/-- **`h⁰(C, φ^*𝒪(d)) = N d + 1 - g`** for `N d > 2g - 2`. -/
private theorem finrank_twistPb (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n : ℕ} (_hn : n = N - genus f)
    (ℓ : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P) Q})
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (_hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          C.presheaf.germ _ (genericPoint C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    (d : ℕ) (hd : 2 * (genus f : ℤ) - 2 < N * d) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    (finrank k Γ(twistPb φNP d, ⊤) : ℤ) = N * d + 1 - genus f := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let := functionFieldAlgebra k f
  set M := twistPb φNP d with hM
  have hMinv : Stacks.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 M :=
    (inferInstance : Stacks.Ample.IsInvertibleModule C M)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M :=
    hMinv.toAlgebraicGeometry
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral C M
  have hg2 : (2 : ℤ) ≤ genus f := by exact_mod_cast hg
  have hd0 : (0 : ℤ) < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; push_cast at hd; omega
    · exact_mod_cast h
  -- the coordinates `cᵥ` of the sections `φ^* T_ν^d`
  set cf : Fin (n + 1) → C.functionField := fun ν =>
    Stacks.Zeta.genericCoord C M s hs (vojtaCoordinatePow φNP d ν) with hcf
  obtain ⟨hη, -⟩ := hφℓ 0 0
  have hηU : genericPoint C ∈ chartOne φNP 0 := hη
  have hℓ0 : ∀ ν, ℓ ν ≠ 0 := hli.ne_zero
  have hc : ∀ ν, cf ν = (ℓ ν / ℓ 0) ^ d * cf 0 := fun ν => by
    rw [hcf]
    dsimp only
    rw [genericCoord_eq_of_resT M s hs hηU (resT_vojtaCoordinatePow_eq_app_pow_smul φNP d 0 ν)]
    congr 1
    obtain ⟨_, h⟩ := hφℓ ν 0
    rw [← h]
    exact map_pow ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app
      (projChart.{u} n 0) ≫ φNP.app _ ≫
        C.presheaf.germ (chartOne φNP 0) (genericPoint C) hηU).hom _ d
  have hcf0 : cf 0 ≠ 0 := genericCoord_ne_zero M s hs (chartOne_le_nvOpen φNP 0 d hηU)
  have hcfν : ∀ ν, cf ν ≠ 0 := fun ν => by
    rw [hc ν]; exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (hℓ0 ν) (hℓ0 0))) hcf0
  have hordc : ∀ ν (Q : C), C.ord (cf ν) Q =
      d * (C.ord (ℓ ν) Q - C.ord (ℓ 0) Q) + C.ord (cf 0) Q := fun ν Q => by
    rw [hc ν, Scheme.ord_mul (pow_ne_zero _ (div_ne_zero (hℓ0 ν) (hℓ0 0))) hcf0,
      ord_pow_eq (div_ne_zero (hℓ0 ν) (hℓ0 0)), ord_div_eq (hℓ0 ν) (hℓ0 0)]
  set h := ℓ 0 ^ d * (cf 0)⁻¹ with hh_def
  have hh : h ≠ 0 := mul_ne_zero (pow_ne_zero _ (hℓ0 0)) (inv_ne_zero hcf0)
  have hordh : ∀ Q : C, C.ord h Q = d * C.ord (ℓ 0) Q - C.ord (cf 0) Q := fun Q => by
    rw [hh_def, Scheme.ord_mul (pow_ne_zero _ (hℓ0 0)) (inv_ne_zero hcf0),
      ord_pow_eq (hℓ0 0), ord_inv_eq hcf0]
    ring
  -- the divisor of `s` is `d N P + div h`
  have hD : Stacks.Zeta.sectionDivisor f M s hs =
      closedDivisor (((N * d : ℕ) : ℤ) • P) + Stacks.Zeta.divOf f hh := by
    ext Q
    rw [Finsupp.add_apply, Stacks.Zeta.divOf_apply, closedDivisor_apply,
      Stacks.Zeta.sectionDivisor_apply]
    obtain ⟨ν, hν⟩ := exists_mem_nonvanishingLocus_vojtaCoordinatePow φNP d Q.1
    set Z := Stacks.Zeta.primeDivisorOfClosedPoint f Q
    have hZ : Z.genericPoint = Q.1 := PrimeDivisor.genericPoint_ofCoheightOne _ _
    have : IsDiscreteValuationRing (C.presheaf.stalk Z.genericPoint) :=
      Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one f _
        (PrimeDivisor.coheight_genericPoint Z)
    have hord := ord_genericCoord_add_eq_zero M s hs Z (vojtaCoordinatePow φNP d ν)
      (by rw [hZ]; exact (Stacks.NonvanishingOpen.mem_nonvanishingOpen _ _ _ _).mpr hν)
    rw [hZ] at hord
    -- `ord_Q ℓ_ν = -N P(Q)`, as `ℓ_ν` has the least order at `Q`
    have key := ord_eq_neg_of_forall_ord_le k f P hPclosed hP N (by omega) ℓ hℓ0 hspan Q ν
      fun μ => by
        have hm := (Stacks.Zeta.genericCoord_mem C M s hs (vojtaCoordinatePow φNP d μ)
          Z).resolve_left (hcfν μ)
        rw [hZ] at hm
        have e1 := hordc μ Q.1
        have e2 := hordc ν Q.1
        change 0 ≤ C.ord (cf μ) Q.1 + _ at hm
        change C.ord (cf ν) Q.1 + _ = 0 at hord
        exact le_of_mul_le_mul_left (by linarith) hd0
    have e1 := hordc ν Q.1
    have e2 := hordh Q.1
    change orderOfVanishingMeromorphic C M s hs Z = _
    rw [e2, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    have : orderOfVanishingMeromorphic C M s hs Z = - C.ord (cf ν) Q.1 := by
      change C.ord (cf ν) Q.1 + _ = 0 at hord
      omega
    rw [this, e1, key]
    ring
  have e1 := Stacks.Zeta.finrank_rrSpace_sectionDivisor f M s hs
  rw [hD, Stacks.Zeta.finrank_rrSpace_add_divOf] at e1
  have e2 := finrank_cohomologyOverField_zero f M
  have e3 := finrank_rrSpace_smul f P hPclosed hP ((N * d : ℕ) : ℤ) (by push_cast; omega)
  rw [← e2, ← e1, e3]
  push_cast
  ring

/-- **`k(C)` and `k(C)` are linearly disjoint in `k(C × C)`**: products of `k`-linearly
independent families pulled back along the two projections are `k`-linearly independent. -/
private theorem linearIndependent_mul_functionFieldMap (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] [IsIntegral (pullback f f)]
    {ι κ : Type*} (a : ι → C.functionField) (b : κ → C.functionField) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    LinearIndependent k a → LinearIndependent k b →
      LinearIndependent k (fun pq : ι × κ => functionFieldMap (pullback.fst f f) (a pq.1) *
        functionFieldMap (pullback.snd f f) (b pq.2)) := by
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro ha hb
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint C)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  let := affineAlgebra k f U
  have : IsScalarTower k Γ(C, U) C.functionField := .of_algebraMap_eq fun c => by
    change C.presheaf.germ ⊤ (genericPoint C) trivial
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) =
      C.presheaf.germ U (genericPoint C) hηU
        (C.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have := functionField_isFractionRing_of_isAffineOpen C U hU
  have hK := isDomain_tensorProduct_of_isFractionRing (A := Γ(C, U)) (K := C.functionField)
    (isDomain_tensorProduct_of_isAffineOpen k f hU)
  have hinj := injective_lift_functionFieldMapAlgHom k f hK
  have : Module.Free k C.functionField := Module.Free.of_divisionRing k _
  have : Module.Flat k C.functionField := Module.Flat.of_free
  have hli := (ha.tmul_of_flat_left hb).map' (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)).toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  exact hli

/-- **The lower bound** `dim {F(ξ, ξ')} ≥ (N δ₁ + 1 - g)(N δ₂ + 1 - g)`. -/
private theorem le_finrank_range_affineEvaluation (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n : ℕ} (hn : n = N - genus f)
    (ℓ : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P) Q})
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          C.presheaf.germ _ (genericPoint C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    [IsIntegral (pullback f f)]
    (δ₁ δ₂ : ℕ)
    (hδ₀ : Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) =>
      vojtaFormRestriction
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) δ₁ δ₂
        (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom))
    (hNδ₁ : 2 * (genus f : ℤ) - 2 < N * δ₁) (hNδ₂ : 2 * (genus f : ℤ) - 2 < N * δ₂)
    (j : Fin (n + 1)) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    ((N : ℤ) * δ₁ + 1 - genus f) * (N * δ₂ + 1 - genus f) ≤
      (finrank k (LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂))) : ℤ) := by
  classical
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro pr₁ pr₂
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : (pullback f f).Over (Spec (.of k)) := ⟨pullback.fst f f ≫ f⟩
  set π := projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) with hπ
  set ψ := pullback.map f f π π φNP φNP (𝟙 _) (by simp [π, hφNP]) (by simp [π, hφNP]) with hψ
  have h₁ : ψ ≫ pullback.fst π π = pullback.fst f f ≫ φNP := pullback.lift_fst _ _ _
  have h₂ : ψ ≫ pullback.snd π π = pullback.snd f f ≫ φNP := pullback.lift_snd _ _ _
  obtain ⟨hη, -⟩ := hφℓ j j
  have : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
      projChart.{u} n j) := ⟨⟨_, hη⟩⟩
  have : Nonempty (chartOne φNP j) := ⟨⟨_, hη⟩⟩
  set W := ψ ⁻¹ᵁ chartOpen (Spec (.of k)) n j with hW
  have : Nonempty W :=
    (nonempty_preimage_chartOpen j φNP (pullback.fst f f) (pullback.snd f f) ψ h₁ h₂).to_subtype
  have hWnv := preimage_chartOpen_le_nonvanishingOpen ψ j δ₁ δ₂
  -- every coordinate of a section of `ψ^*𝒪(δ₁, δ₂)` is a value `F(ξ, ξ')`
  have hmem : ∀ t, coord k _ (baseSec ψ δ₁ δ₂ j j) hWnv t ∈
      LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂)) := by
    intro t
    obtain ⟨G, hG⟩ := hδ₀ t
    have hσ : ψ ≫ pullback.fst π π ≫ π = pullback.fst f f ≫ f := by
      rw [← Category.assoc, h₁, Category.assoc, hφNP]
    have hc₀ : ∀ a, algebraMap k (pullback f f : Scheme.{u}).functionField
        ((Scheme.ΓSpecIso (.of k)).hom.hom a) =
          (pullback f f : Scheme.{u}).presheaf.germ ⊤ (genericPoint _) trivial
            ((ψ ≫ pullback.fst π π ≫ π).appTop a) := by
      intro a
      rw [hσ]
      change ((pullback f f : Scheme.{u}).presheaf.germ ⊤ (genericPoint _) trivial).hom
        ((pullback.fst f f ≫ f).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom a))) = _
      have e := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
      simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
        RingHom.id_apply] at e
      rw [e]
    have hPm : (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom).map
        (Scheme.ΓSpecIso (.of k)).hom.hom = G.1 := by
      rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
        MvPolynomial.map_id]
    have key := germ_div_vojtaFormRestriction j φNP (pullback.fst f f) (pullback.snd f f) ψ h₁ h₂
      pr₁ pr₂ (fun _ => rfl) (fun _ => rfl) (Scheme.ΓSpecIso (.of k)).hom.hom hc₀ δ₁ δ₂
      (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom)
      (fun d hd => G.2 fun h => hd (by rw [MvPolynomial.coeff_map, h, map_zero]))
      (by rw [hPm]; exact G.2) hWnv
    have hx : (fun ν => C.germToFunctionField _
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
          (projRatio.{u} n j ν))) = fun ν => ℓ ν / ℓ j := funext fun ν => by
      obtain ⟨_, h⟩ := hφℓ ν j
      exact h
    rw [hx, affineEvaluation_div pr₁ pr₂ ℓ j (hli.ne_zero j)] at key
    refine ⟨⟨(G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom).map (Scheme.ΓSpecIso (.of k)).hom.hom,
      by rw [hPm]; exact G.2⟩, ?_⟩
    rw [← hG]
    exact key.symm
  -- the charts of `C` and their preimages in `C × C`
  have hU₁ := chartOne_le_nvOpen φNP j δ₁
  have hU₂ := chartOne_le_nvOpen φNP j δ₂
  have hW₁ : W ≤ pullback.fst f f ⁻¹ᵁ chartOne φNP j := fun x hx => by
    have h := hx.1
    have e : (pullback.fst π π).base (ψ.base x) = φNP.base ((pullback.fst f f).base x) :=
      congrArg (fun h : (pullback f f : Scheme.{u}) ⟶ _ => h.base x) h₁
    change (projectiveSpaceOver.toIntegralAtUniverse n _).base
      (φNP.base ((pullback.fst f f).base x)) ∈ projChart.{u} n j
    rw [← e]
    exact h
  have hW₂ : W ≤ pullback.snd f f ⁻¹ᵁ chartOne φNP j := fun x hx => by
    have h := hx.2
    have e : (pullback.snd π π).base (ψ.base x) = φNP.base ((pullback.snd f f).base x) :=
      congrArg (fun h : (pullback f f : Scheme.{u}) ⟶ _ => h.base x) h₂
    change (projectiveSpaceOver.toIntegralAtUniverse n _).base
      (φNP.base ((pullback.snd f f).base x)) ∈ projChart.{u} n j
    rw [← e]
    exact h
  set s' := Stacks.ProductFamilyTwist.prodSection
    (pullbackGlobalSections (pullback.fst f f) _ (vojtaCoordinatePow φNP δ₁ j))
    (pullbackGlobalSections (pullback.snd f f) _ (vojtaCoordinatePow φNP δ₂ j)) with hs'
  have hW' : W ≤ Stacks.ProjectiveFromSections.nvOpen _ s' := by
    rw [hs', Stacks.ProductFamilyTwist.nvOpen_prodSection, Stacks.ProjectiveFromSections.nvOpen,
      Stacks.ProjectiveFromSections.nvOpen,
      Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections,
      Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.nonvanishingOpen_pullbackGlobalSections]
    exact le_inf (hW₁.trans (Scheme.Hom.preimage_mono _ hU₁))
      (hW₂.trans (Scheme.Hom.preimage_mono _ hU₂))
  -- `ψ^*𝒪(δ₁, δ₂) ≅ pr₁^* φ^*𝒪(δ₁) ⊗ pr₂^* φ^*𝒪(δ₂)`
  let A : ℕ → (projectiveSpaceOver n (Spec (.of k))).Modules := fun d =>
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj (projTwist.{u} n d)
  let e₁ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback (pullback.fst π π)).obj
      (A δ₁)) ≅ (Scheme.Modules.pullback (pullback.fst f f)).obj (twistPb φNP δ₁) :=
    (Scheme.Modules.pullbackComp ψ (pullback.fst π π)).app _ ≪≫
      (Scheme.Modules.pullbackCongr h₁).app _ ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f f) φNP).app _).symm
  let e₂ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback (pullback.snd π π)).obj
      (A δ₂)) ≅ (Scheme.Modules.pullback (pullback.snd f f)).obj (twistPb φNP δ₂) :=
    (Scheme.Modules.pullbackComp ψ (pullback.snd π π)).app _ ≪≫
      (Scheme.Modules.pullbackCongr h₂).app _ ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f f) φNP).app _).symm
  let e := Stacks.VeryAmpleFixedTwist.pullbackTensorMonoidalIso ψ
    ((Scheme.Modules.pullback (pullback.fst π π)).obj (A δ₁))
    ((Scheme.Modules.pullback (pullback.snd π π)).obj (A δ₂)) ≪≫
      tensorIso (C := (pullback f f : Scheme.{u}).Modules) e₁ e₂
  let T' : (pullback f f : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback (pullback.fst f f)).obj (twistPb φNP δ₁) ⊗
      (Scheme.Modules.pullback (pullback.snd f f)).obj (twistPb φNP δ₂)
  let T : (pullback f f : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback (pullback.fst π π)).obj (A δ₁) ⊗
      (Scheme.Modules.pullback (pullback.snd π π)).obj (A δ₂))
  let E : T' ⟶ T := e.inv
  let Eh : T ⟶ T' := e.hom
  -- the coordinates of the box products
  set coT := coord k _ (baseSec ψ δ₁ δ₂ j j) hWnv with hcoT
  set u₀ := coT (E.app ⊤ s') with hu₀
  have hbox : ∀ σ τ, coT (E.app ⊤ (Stacks.ProductFamilyTwist.prodSection
      (pullbackGlobalSections (pullback.fst f f) _ σ)
      (pullbackGlobalSections (pullback.snd f f) _ τ))) =
      pr₁ (coord k _ _ hU₁ σ) * pr₂ (coord k _ _ hU₂ τ) * u₀ := fun σ τ => by
    rw [hcoT, coord_map k _ _ hWnv E s' hW',
      coord_prodSection k (pullback.fst f f) (pullback.snd f f) _ _ _ _ hU₁ hU₂ hW₁ hW₂ hW']
    rfl
  have hs'0 : s' ≠ 0 := by
    intro h0
    have h1 : coord k _ s' hW' s' = 1 := by
      rw [coord_eq k _ s' hW' (a := 1) (one_smul _ _).symm, map_one]
    have h2 := congrArg (coord k _ s' hW') h0
    rw [h1, map_zero] at h2
    exact one_ne_zero h2
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    have h1 : E.app ⊤ s' = 0 := coord_injective k _ _ hWnv (h0.trans (map_zero _).symm)
    have h2 : Eh.app ⊤ (E.app ⊤ s') = s' := by
      change (E ≫ Eh).app ⊤ s' = s'
      rw [show E ≫ Eh = 𝟙 _ from e.inv_hom_id]
      rfl
    rw [h1, map_zero] at h2
    exact hs'0 h2.symm
  -- `k`-bases of `H⁰(C, φ^*𝒪(δᵢ))`
  have hd₁ := finrank_twistPb k f hg P hPclosed hP N hN hn ℓ hli hspan φNP hφNP hφℓ δ₁ hNδ₁
  have hd₂ := finrank_twistPb k f hg P hPclosed hP N hN hn ℓ hli hspan φNP hφNP hφℓ δ₂ hNδ₂
  have hg0 : (2 : ℤ) ≤ genus f := by exact_mod_cast hg
  have : FiniteDimensional k Γ(twistPb φNP δ₁, ⊤) := FiniteDimensional.of_finrank_pos (by omega)
  have : FiniteDimensional k Γ(twistPb φNP δ₂, ⊤) := FiniteDimensional.of_finrank_pos (by omega)
  let b₁ := Module.finBasis k Γ(twistPb φNP δ₁, ⊤)
  let b₂ := Module.finBasis k Γ(twistPb φNP δ₂, ⊤)
  have hli₁ : LinearIndependent k (fun p => coord k _ _ hU₁ (b₁ p)) :=
    b₁.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (coord_injective k _ _ hU₁))
  have hli₂ : LinearIndependent k (fun q => coord k _ _ hU₂ (b₂ q)) :=
    b₂.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (coord_injective k _ _ hU₂))
  have hli₁₂ := linearIndependent_mul_functionFieldMap k f _ _ hli₁ hli₂
  have hliv : LinearIndependent k (fun pq : Fin (finrank k Γ(twistPb φNP δ₁, ⊤)) ×
      Fin (finrank k Γ(twistPb φNP δ₂, ⊤)) => pr₁ (coord k _ _ hU₁ (b₁ pq.1)) *
      pr₂ (coord k _ _ hU₂ (b₂ pq.2)) * u₀) :=
    hli₁₂.map' (LinearMap.mulRight k u₀) (LinearMap.ker_eq_bot.mpr fun x y h =>
      mul_right_cancel₀ hu₀ h)
  -- they are values `F(ξ, ξ')`
  have hℓ : ∀ ν, InL ((N : ℤ) • P) (ℓ ν) := fun ν =>
    (mem_span_iff_inL hspan).1 (Submodule.subset_span ⟨ν, rfl⟩)
  have := finiteDimensional_range_affineEvaluation k f P hPclosed hP N ℓ hℓ j
    (hli.ne_zero j) pr₁ pr₂ δ₁ δ₂ (by omega) (by omega)
  let v : Fin (finrank k Γ(twistPb φNP δ₁, ⊤)) × Fin (finrank k Γ(twistPb φNP δ₂, ⊤)) →
      LinearMap.range (affineEvaluation pr₁ pr₂ ℓ j (δ₁, δ₂)) := fun pq =>
    ⟨pr₁ (coord k _ _ hU₁ (b₁ pq.1)) * pr₂ (coord k _ _ hU₂ (b₂ pq.2)) * u₀, by
      rw [← hbox]; exact hmem _⟩
  have hv : LinearIndependent k v := LinearIndependent.of_comp (Submodule.subtype _) hliv
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  rw [← hd₁, ← hd₂]
  exact_mod_cast hcard

end LowerBound

/-- For a geometrically integral `f : C ⟶ Spec k`, the fibre product `C ×_k C` is integral. -/
public instance isIntegral_pullback_self {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [GeometricallyIntegral f] : IsIntegral (pullback f f) := by
  have : GeometricallyIntegral (pullback.fst f f ≫ f) := Cube.geometricallyIntegral_fst_comp f f
  exact GeometricallyIntegral.isIntegral_of_subsingleton (pullback.fst f f ≫ f)

/-- **The dimension of `U₀`.** Let `C` be a smooth projective geometrically integral curve of
genus `g ≥ 2` over a number field `k`, `P` a divisor of degree one, `N ≥ 2g + 1`, `n = N - g`,
`ℓ` a `k`-basis of `L(NP) = H⁰(C, 𝒪(NP))`, `φNP : C ⟶ ℙⁿ_k` the closed immersion it defines and
`ψ = φNP × φNP`. If every global section of `ψ^*𝒪(δ₁, δ₂)` is the restriction
(`Faltings.vojtaFormRestriction`) of a form of bidegree `(δ₁, δ₂)` over `k`, and
`N δ₁, N δ₂ > 2g - 2`, then the space `affineEvaluationTuples pr₁ pr₂ ℓ j (δ₁, δ₂) (Fin (m + 1))`
has dimension `(m + 1)(N²δ₁δ₂ - N(g - 1)(δ₁ + δ₂) + (g - 1)²)`, which is at most
`(m + 1) N² δ₁ δ₂`. -/
@[faltings "lem_bvs_dim_u0"]
public theorem finrank_affineEvaluationTuples (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n : ℕ} (hn : n = N - genus f)
    (ℓ : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P) Q})
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          C.presheaf.germ _ (genericPoint C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    (δ₁ δ₂ : ℕ)
    (hδ₀ : Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) =>
      vojtaFormRestriction
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) δ₁ δ₂
        (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom))
    (hNδ₁ : 2 * (genus f : ℤ) - 2 < N * δ₁) (hNδ₂ : 2 * (genus f : ℤ) - 2 < N * δ₂)
    (m : ℕ) (j : Fin (n + 1)) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    (finrank k (affineEvaluationTuples pr₁ pr₂ ℓ j (δ₁, δ₂) (Fin (m + 1))) : ℤ) =
        (m + 1) * ((N : ℤ) ^ 2 * δ₁ * δ₂ - N * (genus f - 1) * (δ₁ + δ₂) +
          ((genus f : ℤ) - 1) ^ 2) ∧
      (m + 1) * ((N : ℤ) ^ 2 * δ₁ * δ₂ - N * (genus f - 1) * (δ₁ + δ₂) +
          ((genus f : ℤ) - 1) ^ 2) ≤ (m + 1) * (N : ℤ) ^ 2 * δ₁ * δ₂ := by
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro pr₁ pr₂
  have hℓ : ∀ ν, InL ((N : ℤ) • P) (ℓ ν) := fun ν =>
    (mem_span_iff_inL hspan).1 (Submodule.subset_span ⟨ν, rfl⟩)
  have hj : ℓ j ≠ 0 := hli.ne_zero j
  have hupper := finrank_range_affineEvaluation_le k f P hPclosed hP N ℓ hℓ j hj pr₁ pr₂ δ₁ δ₂
    (by omega) (by omega)
  have hlower := le_finrank_range_affineEvaluation k f hg P hPclosed hP N hN hn ℓ hli hspan φNP
    hφNP hφℓ δ₁ δ₂ hδ₀ hNδ₁ hNδ₂ j
  have := finiteDimensional_range_affineEvaluation k f P hPclosed hP N ℓ hℓ j hj pr₁ pr₂ δ₁ δ₂
    (by omega) (by omega)
  have hdim : (finrank k (affineEvaluationTuples pr₁ pr₂ ℓ j (δ₁, δ₂) (Fin (m + 1))) : ℤ) =
      (m + 1) * ((N * δ₁ + 1 - genus f) * (N * δ₂ + 1 - genus f)) := by
    rw [affineEvaluationTuples, finrank_pi_univ_const, Fintype.card_fin]
    push_cast
    rw [le_antisymm hupper hlower]
  rw [hdim]
  refine ⟨by ring, ?_⟩
  have hg0 : (2 : ℤ) ≤ genus f := by exact_mod_cast hg
  have h : ((N : ℤ) * δ₁ + 1 - genus f) * (N * δ₂ + 1 - genus f) ≤ (N * δ₁) * (N * δ₂) :=
    mul_le_mul (by omega) (by omega) (by omega) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℤ) ≤ m + 1)]

end Faltings.BombieriVojta
