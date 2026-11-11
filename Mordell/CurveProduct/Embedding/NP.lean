module

public import Mordell.Curve.PointClass
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints

/-!
# The embedding `φ_{NP}`

Let `(C, P)` be a curve over a field `k` with a divisor `P = ∑ nₓ x` of degree one, let `g` be
the genus of `C` and let `N ≥ 2g + 1`. Let `L` be an invertible `𝒪_C`-module of class
`N · [𝒪_C(P)] = N · ∑ nₓ [𝒪_C(x)]` in `Pic(C)`, that is `L ≅ 𝒪_C(NP)`, and let `x₀, …, xₙ` be a
`k`-basis of `H⁰(C, L) = Γ(C, L)`. Then `n = N - g`, the sections `x₀, …, xₙ` generate `L`, and
the morphism `φ_{NP} : C ⟶ ℙⁿ_k` they define is a closed immersion, together with an
isomorphism `φ_{NP}^* 𝒪(1) ≅ L` carrying the `i`-th homogeneous coordinate to `xᵢ`. In
particular `NP` is linearly equivalent to the hyperplane section `{T₀ = 0}` of `C` in this
embedding, the divisor of `x₀`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.finrank_globalSections_of_picardClass`: Riemann–Roch for
  `𝒪_C(NP)`, `dim_k Γ(C, 𝒪_C(NP)) = N + 1 - g` for `N ≥ 2g - 1`.
* `Faltings.finrank_cohomologyOverField_zero_eq_finrank_sections`:
  `dim_k H⁰(X, M) = dim_k Γ(X, M)`.
* `Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver`: a `k`-basis of
  `H⁰(C, 𝒪_C(NP))` has `N - g + 1` elements and defines a closed immersion `C ⟶ ℙⁿ_k` over `k`
  pulling `𝒪(1)` back to `𝒪_C(NP)`.

## Implementation notes

The divisor `P` need not be effective, so `𝒪_C(NP)` is specified by its class: `L` is any
invertible module whose class in `Pic(C)` is `N • ∑ nₓ [𝒪_C(x)]`, each closed point `x` of the
smooth curve being an effective Cartier divisor. Any two such `L` are isomorphic.

The `k`-module structure on `Γ(C, L)` is restriction of scalars along `k → Γ(C, 𝒪_C)`, the ring
map of the structure morphism
(`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule`).
The morphism defined by the sections is `Stacks.ProjectiveFromSections.toProjectiveSpaceOver`,
which lies over the structure morphism by
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst`; it lands in `ℙⁿ_k = ℙⁿ_ℤ ×_ℤ Spec k`,
and `𝒪(1)` on it is pulled back from the twisting sheaf of `ℙⁿ_ℤ`, so the comparison is stated
on the pull-back of `Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse` along the
composite to the integral model, pinned on the homogeneous coordinates
(`Stacks.TwistPullbackPinned.pullbackCoordSection`).

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 01NE], [Stacks Project, Tag 0FCY]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable {k : Type u} [Field k]

/-- The class `N · ∑ nₓ [𝒪_C(x)]` of `𝒪_C(NP)` has degree `N`, as `deg P = 1`. -/
lemma CurveWithDegreeOneDivisor.invertibleCurveDegree_eq_of_picardClass
    (X : CurveWithDegreeOneDivisor k) (hdim : topologicalKrullDim X.C ≤ 1) (N : ℕ)
    (L : X.C.Modules)
    [hLi : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L hLi =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    invertibleCurveDegree k X.f hdim L = N := by
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  rw [← invertibleCurveDegreeHom_picardClass k X.f hdim L hLi, hL, map_zsmul,
    map_finsuppSum (invertibleCurveDegreeHom k X.f hdim), smul_eq_mul]
  refine (congrArg _ ?_).trans (mul_one _)
  rw [← X.degree_P]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_zsmul, X.invertibleCurveDegreeHom_picardClass_pointIdeal hdim, smul_eq_mul]

/-- `H⁰(X, M)` and `Γ(X, M)` have the same dimension over `k`, for a scheme `X` over `k`. -/
lemma finrank_cohomologyOverField_zero_eq_finrank_sections {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (M : X.Modules) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    Module.finrank k (cohomologyOverField k f M 0) = Module.finrank k Γ(M, ⊤) := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
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

/-- Riemann–Roch for an invertible `L` of degree `N ≥ 2g - 1`: as `H¹(C, L) = 0`,
`dim_k Γ(C, L) = N + 1 - g`. -/
lemma CurveWithDegreeOneDivisor.finrank_globalSections_eq_of_invertibleCurveDegree
    (X : CurveWithDegreeOneDivisor k) (hdim : topologicalKrullDim X.C ≤ 1) (N : ℕ)
    (L : X.C.Modules)
    [hLi : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L]
    (hN : 2 * (genus X.f : ℤ) - 1 ≤ N)
    (hdeg : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      invertibleCurveDegree k X.f hdim L = N) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    (Module.finrank k Γ(L, ⊤) : ℤ) = N + 1 - genus X.f := by
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k X.f
  haveI := ModuleCat.subsingleton_of_isZero
    (isZero_cohomologyOverField_one_of_geometricallyIntegral k X.f L hLi (by rwa [hdeg]))
  have := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k X.f hdim L
  rw [finrank_cohomologyOverField_zero_eq_finrank_sections,
    Module.finrank_zero_of_subsingleton (M := cohomologyOverField k X.f L 1), hdeg] at this
  simpa using this

/-- **Riemann–Roch for `𝒪_C(NP)`.** If `N ≥ 2g - 1` and `L` is an invertible `𝒪_C`-module of
class `N • ∑ nₓ [𝒪_C(x)]`, then `dim_k Γ(C, L) = N + 1 - g`. -/
theorem CurveWithDegreeOneDivisor.finrank_globalSections_of_picardClass
    (X : CurveWithDegreeOneDivisor k) (N : ℕ) (hN : 2 * (genus X.f : ℤ) - 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    (Module.finrank k Γ(L, ⊤) : ℤ) = N + 1 - genus X.f := by
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv
  have hdim : topologicalKrullDim X.C ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)).le
  exact X.finrank_globalSections_eq_of_invertibleCurveDegree hdim N L hN
    (X.invertibleCurveDegree_eq_of_picardClass hdim N L hL)

/-- **The embedding `φ_{NP}`.** Let `X = (C, P)` be a curve over `k` with a divisor
`P = ∑ nₓ x` of degree one, of genus `g`, let `N ≥ 2g + 1`, let `L ≅ 𝒪_C(NP)` be an invertible
`𝒪_C`-module of class `N • ∑ nₓ [𝒪_C(x)]`, and let `x₀, …, xₙ` be a `k`-basis of `Γ(C, L)`.
Then `n = N - g`, the sections `xᵢ` generate `L`, the morphism `φ_{NP} : C ⟶ ℙⁿ_k` over `k`
they define is a closed immersion, and there is an isomorphism `φ_{NP}^* 𝒪(1) ≅ L` sending the
`i`-th homogeneous coordinate to `xᵢ`. -/
@[faltings "lem_nt_np_embedding"]
theorem CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver
    (X : CurveWithDegreeOneDivisor k) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) :
    letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
    ∀ {n : ℕ} (x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤)),
      n = N - genus X.f ∧
      ∃ hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x,
        IsClosedImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f) ∧
        ∃ α : (Scheme.Modules.pullback
            (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f ≫
              projectiveSpaceOver.toIntegralAtUniverse n _)).obj
                (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ⟶ L,
          IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
            (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f ≫
              projectiveSpaceOver.toIntegralAtUniverse n _) i) = x i := by
  intro n x
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have hdim1 : topologicalKrullDim X.C = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.f)
  haveI : Stacks.SheafOfModules.IsInvertible X.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k X.f
  have hdeg := X.invertibleCurveDegree_eq_of_picardClass hdim1.le N L hL
  letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  have hb := X.finrank_globalSections_of_picardClass N (by omega) L hL
  rw [Module.finrank_eq_card_basis x, Fintype.card_fin] at hb
  refine ⟨by omega, ?_⟩
  let S : CohenMacaulayCurveSituation.{u} :=
    { k := k, X := X.C, f := X.f, dimension_one := hdim1 }
  haveI : IsIntegral S.X := (inferInstance : IsIntegral X.C)
  haveI : GeometricallyIntegral S.f := (inferInstance : GeometricallyIntegral X.f)
  have hgen : Stacks.ProjectiveFromSections.GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
    generatesStalks_id_of_isGeneratedByGlobalSections L
      (S.isGeneratedByGlobalSections_of_two_mul_genus_le L (by
        change 2 * (genus X.f : ℤ) ≤ invertibleCurveDegree k X.f hdim1.le L
        rw [hdeg]
        omega))
  have hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x :=
    generatesStalks_fin_of_mem_span X.f L (⇑x) id hgen x.mem_span
  refine ⟨hx, ?_, ?_⟩
  · obtain ⟨θ, hθ⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver (⇑x) hx X.f
    haveI : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
      projectiveSpaceOver_isProper n (Spec (.of k))
    refine isClosedImmersion_of_pinned_of_span_of_surjectsOnDegreeTwo_baseChange X.f
      (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k)))
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f)
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst ⇑x hx X.f) _ L θ
      (fun i : ULift.{u} (Fin (n + 1)) =>
        pullbackSectionTop (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)
          (Stacks.TwistPullbackPinned.coordGlobalSection.{u} n i.down))
      (fun i : ULift.{u} (Fin (n + 1)) => x i.down) (fun i => hθ i.down)
      (fun σ => Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩)
        (x.mem_span σ))
      fun X' g' f' h => ?_
    have : IsIntegral (S.ofIsPullback h).X := S.isIntegral_ofIsPullback h
    refine (S.ofIsPullback h).surjectsOnDegreeTwo_of_two_mul_genus_add_one_le _ ?_
    rw [S.invertibleCurveDegree_ofIsPullback h L]
    change 2 * (genus f' : ℤ) + 1 ≤ invertibleCurveDegree k X.f hdim1.le L
    rw [genus_baseChange k _ g' f' X.f h, hdeg]
    omega
  · obtain ⟨α, hiso, hα⟩ := exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse (⇑x) hx
    have hsnd := Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd (⇑x) hx X.f
    refine ⟨(Scheme.Modules.pullbackCongr hsnd).hom.app _ ≫ α, inferInstance, fun i => ?_⟩
    rw [← hα i]
    change α.app ⊤ (((Scheme.Modules.pullbackCongr hsnd).hom.app _).app ⊤ _) = _
    rw [pullbackCoordSection_eq, pullbackCoordSection_eq]
    exact congrArg (α.app ⊤) (pullbackSectionTop_congr hsnd _ _)

end Faltings
