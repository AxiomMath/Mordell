module
public import Mordell.BombieriVojta.Projection.Basic
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.Curve.Normal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreMorphism.NonContractedFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts

/-!
# The projections `π_a` are finite

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `D` a divisor of degree `N ≥ 2g + 1` supported on closed points (the source's `NP`, with `P`
of degree one), and `x₀, …, xₙ` a `k`-basis of the
Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))` inside the function field `k(C)`. For `a ∈ {1, …, n}`
let `π_a = (x₀ : x_a) : C ⤏ ℙ¹_k`. If the basis satisfies (G1), that is `x₀` and `x_a` have no
common zero as sections of `𝒪(D)`, then `(x₀ : x_a)` is defined at every point of `C`, so `π_a`
extends to a morphism `C ⟶ ℙ¹_k`; it is non-constant because `x₀` and `x_a` are linearly
independent, and a non-constant morphism of smooth projective curves is finite.

## Main results

* `Faltings.BombieriVojta.exists_isFinite_toRationalMap_eq_projectionToProjectiveLine`: under
  (G1), for every `a ∈ {1, …, n}` the rational map `π_a` is induced by a finite morphism
  `C ⟶ ℙ¹_k`.

## Implementation notes

"`π_a` is a finite morphism" is stated as: there is a morphism `φ : C ⟶ ℙ¹_k` with
`IsFinite φ` whose rational map `φ.toRationalMap` is `π_a`. As in
`Faltings.BombieriSiegel.SatisfiesG1`, sections of `𝒪(D)` are rational functions, `D` is a
`C →₀ ℤ`, `L(D)` is `{g | g = 0 ∨ ∀ Q closed, 0 ≤ ord_Q g + D(Q)}` (the form of
`Faltings.BombieriSiegel.IsGenericBasis.span_eq`), and `k(C)` is a `k`-algebra through
`AlgebraicGeometry.functionFieldAlgebra k f`. The index `a ∈ {1, …, n}` is `a : Fin n`,
used as `a.succ`, as in `Faltings.BombieriVojta.projectionToProjectiveLine`.

The source deduces from (G1) that `π_a` is everywhere defined. Here that is instead the extension
theorem for rational maps out of a normal curve into a proper variety ([Stacks, Tag 0BXZ]), which
needs no hypothesis on the basis, so (G1) is carried but not used. The extension `φ` is proper,
and a proper non-constant morphism out of an integral scheme of dimension one is finite
([Hartshorne, II.6.8]). If `φ` were constant, its value would be the image of the generic point,
which lies in the chart `D₊(T₀) ≅ 𝔸¹_k` because `x₀ ≠ 0`; the coordinate `T₁ / T₀` would then pull
back to a global function on `C` with germ `x_a / x₀` at the generic point. The global functions
of a proper geometrically integral `k`-scheme are the constants, so `x_a / x₀ ∈ k`, contradicting
the linear independence of `x₀` and `x_a`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
-/

open AlgebraicGeometry CategoryTheory Faltings.BombieriSiegel

universe u

namespace Faltings.BombieriVojta

attribute [local instance] MvPolynomial.gradedAlgebra in
open Stacks.SectionsToProjectiveSpace in
/-- A morphism `φ : C ⟶ ℙ¹_k` from a proper geometrically integral `k`-scheme whose restriction
to `Spec k(C)` is the point `(s₀ : s₁)`, with `s₀` a unit and `s₁ / s₀` not a constant, is not
constant. -/
private lemma exists_apply_ne_of_fromSpecStalk_comp_eq (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsProper f] [GeometricallyIntegral f]
    (φ : C ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (s : Fin 2 → Γ(Spec (.of C.functionField), ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (hs0 : IsUnit (s 0))
    (hφ : C.fromSpecStalk (genericPoint C) ≫ φ =
      toProjectiveSpaceOver s hs (C.fromSpecStalk (genericPoint C) ≫ f))
    (hind : ∀ c : k, s 1 ≠
      (C.fromSpecStalk (genericPoint C)).appTop (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) *
        s 0)
    (y : projectiveSpaceOver 1 (Spec (.of k))) : ∃ z, φ z ≠ y := by
  by_contra! hy
  set j := C.fromSpecStalk (genericPoint C) with hj
  let 𝒜 := coordGrading.{u} 1
  have hX0 : (MvPolynomial.X 0 : coordRing.{u} 1) ∈ 𝒜 1 := X_mem_coordGrading_one 0
  have hX1 : (MvPolynomial.X 1 : coordRing.{u} 1) ∈ 𝒜 (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact X_mem_coordGrading_one 1
  let ψ := φ ≫ projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k))
  have hg : j ≫ ψ = toProjectiveSpaceAtUniverse s hs := by
    simp only [ψ, ← Category.assoc, hφ, toProjectiveSpaceOver_snd]
  have hpre : toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) = ⊤ := by
    rw [preimage_basicOpen]
    exact Scheme.basicOpen_of_isUnit _ hs0
  have hψ : ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) = ⊤ := by
    refine top_unique fun z _ => ?_
    let pt : Spec (C.presheaf.stalk (genericPoint C)) :=
      IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))
    have h1 : ψ z = (j ≫ ψ) pt := by
      simp only [ψ, Scheme.Hom.comp_apply, hy]
    rw [hg] at h1
    have h2 : pt ∈ toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) := by
      rw [hpre]; trivial
    change ψ z ∈ Proj.basicOpen 𝒜 (MvPolynomial.X 0)
    rwa [h1]
  have := isIso_globalSections_of_geometricallyIntegral k f
  let a0 := HomogeneousLocalization.Away.mk 𝒜 hX0 1 (MvPolynomial.X 1) hX1
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)).2
    ((Proj.awayToSection 𝒜 (MvPolynomial.X 0) ≫ ψ.appLE _ ⊤ hψ.ge) a0)
  refine hind c ?_
  set W := (Spec (.of C.functionField)).basicOpen (sectionsHom s (MvPolynomial.X 0)) with hW
  have hWtop : W = ⊤ := by
    rw [hW, sectionsHom_X]; exact Scheme.basicOpen_of_isUnit _ hs0
  have : Nonempty W := by
    rw [hWtop]
    exact ⟨⟨IsLocalRing.closedPoint C.functionField, trivial⟩⟩
  apply map_injective_of_isIntegral (Spec (.of C.functionField)) (homOfLE (le_top : W ≤ ⊤))
  have hchart := Stacks.LinearSystemScheme.awayToSection_comp_appLE_fromOfGlobalSections
    (𝒜 := 𝒜) (sectionsHom s) (map_irrelevant_eq_top s hs) one_pos hX0
  have hval := congrArg (fun F => F.hom a0) hchart
  simp only [a0, CommRingCat.hom_ofHom] at hval
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk] at hval
  have hmor : ψ.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X 0)) ⊤ hψ.ge ≫ j.appTop ≫
      (Spec (.of C.functionField)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op =
      (Proj.fromOfGlobalSections 𝒜 (sectionsHom s) (map_irrelevant_eq_top s hs)).appLE
        (Proj.basicOpen 𝒜 (MvPolynomial.X 0)) W
        (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 (sectionsHom s)
          (map_irrelevant_eq_top s hs) one_pos hX0).ge := by
    rw [show j.appTop ≫ (Spec (.of C.functionField)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op =
      j.appLE ⊤ W le_top from rfl]
    refine (Scheme.Hom.appLE_comp_appLE j ψ _ _ _ _ _).trans ?_
    congr 1
  have hE := congrArg (fun F => F.hom ((Proj.awayToSection 𝒜 (MvPolynomial.X 0)).hom a0)) hmor
  have key : (Spec (.of C.functionField)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
      (j.appTop (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) =
      Stacks.ProjGlobalSectionsAppTop.resTop W (sectionsHom s (MvPolynomial.X 1)) *
        Stacks.ProjGlobalSectionsAppTop.resTopBasicOpenInv (sectionsHom s (MvPolynomial.X 0)) ^ 1 :=
    Eq.trans (congrArg (fun t => (Spec (.of C.functionField)).presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op (j.appTop t)) hc) (Eq.trans rfl (hE.trans hval))
  rw [map_mul, key]
  have h0 := (Stacks.ProjGlobalSectionsAppTop.isUnit_resTop_basicOpen
    (sectionsHom s (MvPolynomial.X 0))).val_inv_mul
  rw [← sectionsHom_X s 0, ← sectionsHom_X s 1, pow_one, mul_assoc]
  exact (mul_right_eq_self₀.mpr (Or.inl h0)).symm

/-- A proper morphism out of an integral scheme of dimension at most one which is not constant is
finite. -/
private lemma isFinite_of_forall_exists_apply_ne {C Y : Scheme.{u}} (φ : C ⟶ Y) [IsProper φ]
    [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1) (h : ∀ y, ∃ z, φ z ≠ y) : IsFinite φ := by
  refine φ.isFinite_of_forall_genericPointsOne_exists_ne hdim fun ξ hξ => ?_
  obtain ⟨z, hz⟩ := h (φ ξ)
  refine ⟨z, ?_, hz⟩
  have hcomp : closure ({ξ} : Set C) ∈ irreducibleComponents C :=
    (Stacks.AlgebraicGeometry.ComponentDegrees.mem_genericPointsOne_iff.mp hξ).1
  exact hcomp.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _) (Set.mem_univ z)

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `D` a divisor of degree `N ≥ 2g + 1` on closed points, and `x₀, …, xₙ` a `k`-basis of
`L(D)` satisfying (G1). Then for every `a ∈ {1, …, n}` the projection `π_a = (x₀ : x_a) : C ⤏ ℙ¹_k`
is induced by a finite morphism `C ⟶ ℙ¹_k`. -/
@[faltings "lem_bvs_projection_finite"]
public theorem exists_isFinite_toRationalMap_eq_projectionToProjectiveLine (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x) (a : Fin n) :
    ∃ φ : C ⟶ projectiveSpaceOver 1 (Spec (.of k)), IsFinite φ ∧
      φ.toRationalMap = projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a := by
  let := functionFieldAlgebra k f
  have : IsProper (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
    isProper_projectiveSpaceOver 1 (Spec (.of k))
  have : IsProperVariety k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
    { (isCurve_projectiveSpaceOver_one k).toIsVariety with }
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have hover := isOver_projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a
  set π := projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a with hπ
  have : IsCurve k (Over.mk f).hom := ‹IsCurve k f›
  have : IsNormal (Over.mk f).left := Faltings.FunctionField.isNormal_of_smooth k f
  have : IsProperVariety k
      (Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))).hom :=
    ‹IsProperVariety k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))›
  obtain ⟨φ', hφ'⟩ := (toRationalMap_bijective k (Over.mk f)
    (Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)))).2
    ⟨π, hover⟩
  have hφrat := congrArg Subtype.val hφ'
  refine ⟨φ'.left, ?_, hφrat⟩
  have : IsProper φ'.left := by
    have : IsProper (φ'.left ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [show φ'.left ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f from
        Over.w φ']
      infer_instance
    exact IsProper.of_comp φ'.left (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
  let s : Fin 2 → Γ(Spec (.of C.functionField), ⊤) :=
    fun i => (Scheme.ΓSpecIso (.of C.functionField)).inv (![x 0, x a.succ] i)
  have hs0 : IsUnit (s 0) :=
    (Ne.isUnit (hli.ne_zero 0)).map (Scheme.ΓSpecIso (.of C.functionField)).inv.hom
  have hs : Ideal.span (Set.range s) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) hs0
  have hφ : C.fromSpecStalk (genericPoint C) ≫ φ'.left =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver s hs
        (C.fromSpecStalk (genericPoint C) ≫ f) := by
    have h1 := projectionToProjectiveLine_fromFunctionField k f hg D hDcl N hN
      hD x hli hspan a
    have hφrat' : φ'.left.toRationalMap = π := hφrat
    rw [← hπ, ← hφrat'] at h1
    simpa using h1
  have hind : ∀ c : k, s 1 ≠ (C.fromSpecStalk (genericPoint C)).appTop
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) * s 0 := by
    intro c hc
    simp only [s, Scheme.fromSpecStalk_appTop, CommRingCat.comp_apply, homOfLE_refl, op_id,
      Matrix.cons_val_one, Matrix.cons_val_zero] at hc
    have h : x a.succ = algebraMap k C.functionField c * x 0 := by
      replace hc : (Scheme.ΓSpecIso (.of C.functionField)).inv.hom (x a.succ) =
          (Scheme.ΓSpecIso (.of C.functionField)).inv.hom
            (algebraMap k C.functionField c * x 0) := by
        rwa [RingHom.map_mul]
      simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] using
        congrArg (Scheme.ΓSpecIso (.of C.functionField)).hom.hom hc
    exact Fin.succ_ne_zero a (hli.eq_of_smul_apply_eq_smul_apply 1 c _ _ one_ne_zero
      (by rw [one_smul, Algebra.smul_def, h]))
  exact isFinite_of_forall_exists_apply_ne φ'.left
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
    (exists_apply_ne_of_fromSpecStalk_comp_eq k f φ'.left s hs hs0 hφ hind)

end Faltings.BombieriVojta
