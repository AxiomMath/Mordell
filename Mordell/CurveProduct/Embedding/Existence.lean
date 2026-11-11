module

public import Mordell.Attr
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Height.DiagonalLowerBound
public import Mordell.BombieriVojta.Height.Lemma2
public import Mordell.CurveProduct.Embedding.NP
public import Mordell.CurveProduct.Embedding.B
public import Mordell.CurveProduct.Intersection
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist

/-!
# Existence of the auxiliary embeddings `φ_{NP}` and `φ_B`

Over any field, an invertible sheaf of class `N [P]` (`N ≥ 2g + 1`) has a basis of global sections
defining a closed immersion of `C`, and for all large `s` the same holds for the class
`B = s (P × C) + s (C × P) − Δ'` on `C ×_k C`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

/-! ### The embeddings -/

section Embeddings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

variable {K : Type u} [Field K]

/-- The embedding `φ_{NP}` exists: an invertible sheaf of class `N [P]` with a basis of global
sections defining a closed immersion. -/
public lemma exists_basis_isClosedImmersion_np (Y : CurveWithDegreeOneDivisor K) (N : ℕ)
    (hN : 2 * genus Y.f + 1 ≤ N) :
    ∃ (n : ℕ) (L : Y.C.Modules) (hLinv : Stacks.Ample.IsInvertibleModule Y.C L),
      Stacks.SheafOfModules.picardClass Y.C.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.C.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
        (N : ℤ) • Y.classP ∧
      letI : Y.C.Over (Spec (.of K)) := ⟨Y.f⟩
      ∃ (x : Module.Basis (Fin (n + 1)) K Γ(L, ⊤))
        (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
        IsClosedImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx Y.f) := by
  have : Smooth Y.f := SmoothOfRelativeDimension.smooth 1 Y.f
  have : IsCurve K Y.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one Y.f
  have hdim := (IsCurve.topologicalKrullDim_eq_one (k := K) (f := Y.f)).le
  obtain ⟨L, hLinv, hL⟩ : ∃ (L : Y.C.Modules) (hLinv : Stacks.Ample.IsInvertibleModule Y.C L),
      Stacks.SheafOfModules.picardClass Y.C.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.C.toRingedSpace) L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
        (N : ℤ) • Y.classP :=
    ⟨_, (Stacks.Picard.picardRepresentative Y.C.toRingedSpace ((N : ℤ) • Y.classP)).property,
      Stacks.Picard.classOf_picardRepresentative Y.C.toRingedSpace _⟩
  let : Y.C.Over (Spec (.of K)) := ⟨Y.f⟩
  have hLi : Stacks.SheafOfModules.IsInvertible Y.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.C.toRingedSpace) L := hLinv
  have hdeg : invertibleCurveDegree K Y.f hdim L = N := by
    rw [← invertibleCurveDegreeHom_picardClass K Y.f hdim L hLi]
    refine (congrArg (invertibleCurveDegreeHom K Y.f hdim) hL).trans ?_
    rw [AddMonoidHom.map_zsmul, Y.invertibleCurveDegreeHom_classP, smul_eq_mul, mul_one]
  have hb := Y.finrank_globalSections_eq_of_invertibleCurveDegree hdim N L (by omega) hdeg
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K Γ(L, ⊤) = n + 1 :=
    Nat.exists_eq_add_one.2 (by omega)
  have : Module.Finite K Γ(L, ⊤) := Module.finite_of_finrank_eq_succ hn
  let x : Module.Basis (Fin (n + 1)) K Γ(L, ⊤) := Module.finBasisOfFinrankEq K _ hn
  obtain ⟨-, hx, hxi, -⟩ := Y.isClosedImmersion_toProjectiveSpaceOver N hN L hL x
  exact ⟨n, L, hLinv, hL, x, hx, hxi⟩

/-- The embedding `φ_B` exists for all large `s`. -/
public lemma exists_basis_isClosedImmersion_b (Y : CurveWithDegreeOneDivisor K) :
    ∃ s₀ : ℤ, ∀ s : ℤ, s₀ ≤ s →
      ∃ (m : ℕ) (M : (pullback Y.f Y.f).Modules)
        (hMinv : Stacks.Ample.IsInvertibleModule _ M),
        Stacks.SheafOfModules.picardClass (pullback Y.f Y.f).presheaf
            (Stacks.RingedSpace.structureIsSheaf (pullback Y.f Y.f).toRingedSpace) M
            (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
          Y.vojtaClass s s (-1) ∧
        letI : (pullback Y.f Y.f).Over (Spec (.of K)) := ⟨pullback.fst Y.f Y.f ≫ Y.f⟩
        ∃ (y : Module.Basis (Fin (m + 1)) K Γ(M, ⊤))
          (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y),
          IsClosedImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
            (pullback.fst Y.f Y.f ≫ Y.f)) := by
  obtain ⟨s₀, hs₀⟩ := Y.isClosedImmersion_toProjectiveSpaceOver_vojtaClass
  refine ⟨s₀, fun s hs => ?_⟩
  obtain ⟨M, hMinv, hM⟩ : ∃ (M : (pullback Y.f Y.f).Modules)
      (hMinv : Stacks.Ample.IsInvertibleModule _ M),
      Stacks.SheafOfModules.picardClass (pullback Y.f Y.f).presheaf
          (Stacks.RingedSpace.structureIsSheaf (pullback Y.f Y.f).toRingedSpace) M
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
        Y.vojtaClass s s (-1) :=
    ⟨_, (Stacks.Picard.picardRepresentative (pullback Y.f Y.f).toRingedSpace
      (Y.vojtaClass s s (-1))).property,
      Stacks.Picard.classOf_picardRepresentative (pullback Y.f Y.f).toRingedSpace _⟩
  let : (pullback Y.f Y.f).Over (Spec (.of K)) := ⟨pullback.fst Y.f Y.f ≫ Y.f⟩
  obtain ⟨-, hpos, hall⟩ := hs₀ s hs M hM
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank K Γ(M, ⊤) = m + 1 := Nat.exists_eq_add_one.2 hpos
  have : Module.Finite K Γ(M, ⊤) := Module.finite_of_finrank_eq_succ hm
  let y : Module.Basis (Fin (m + 1)) K Γ(M, ⊤) := Module.finBasisOfFinrankEq K _ hm
  obtain ⟨hy, hyi, -⟩ := hall y
  exact ⟨m, M, hMinv, hM, y, hy, hyi⟩

end Embeddings

end Faltings
