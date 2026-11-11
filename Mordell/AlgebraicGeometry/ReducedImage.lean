module

public import Mordell.Jacobian.BaseChange
public import Mordell.AbelianVariety.TheoremOfTheSquare
public import Mordell.Jacobian.Theta.BaseChange
public import Mordell.AbelianVariety.PicZero
public import Mordell.Jacobian.Theta.PullbackTranslate
public import Mordell.Jacobian.Theta.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist
public import Mordell.Jacobian.AbelJacobiBaseChange

/-!
# Reduced scheme-theoretic images and closed points of residue degree one

A nonempty quasi-compact scheme locally of finite type over an algebraically closed field has a
closed point of residue degree one; the comap of a reduced ideal sheaf along a flat morphism with
reduced fibres is reduced; and two set-level lemmas on preimages of supports and images.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.RigidifiedPicard
open scoped MonObj

universe u

namespace Faltings

/-- A nonempty quasi-compact scheme locally of finite type over an algebraically closed field has
a closed point of residue degree one. -/
public lemma exists_closedPoint_residueDegree_eq_one {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [CompactSpace X]
    [Nonempty X] : ∃ x : {x : X // IsClosed ({x} : Set X)}, f.residueDegree x.1 = 1 := by
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  refine ⟨⟨x, hx⟩, ?_⟩
  have hbij : Function.Bijective (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1
      (inferInstanceAs (IsIso (residueFieldIsoBase f x hx).inv))
  have hfac : Spec.preimage (X.fromSpecResidueField x ≫ f) =
      Spec.preimage ((Spec (.of K)).fromSpecResidueField (f x)) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [hfac, CommRingCat.hom_comp, RingHom.coe_comp] at hbij
  have hsurj : Function.Surjective (f.residueFieldMap x).hom := hbij.2.of_comp
  unfold Scheme.Hom.residueDegree
  let := (f.residueFieldMap x).hom.toAlgebra
  let e := LinearEquiv.ofBijective (Algebra.linearMap ((Spec (.of K)).residueField (f x))
    (X.residueField x)) ⟨(f.residueFieldMap x).hom.injective, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_self]

/-! ### Flat base change of a reduced scheme-theoretic image -/

/-- **Flat base change preserves reducedness of a scheme-theoretic image** when the base change of
the source is reduced: for a quasi-compact `σ : W ⟶ Y` and a flat `φ : Y' ⟶ Y` with `W ×_Y Y'`
reduced, the inverse image under `φ` of the scheme-theoretic image of `σ` is reduced. The
morphism `W ⟶ im σ` is scheme-theoretically dominant, and stays so after the flat base change
to `φ⁻¹(im σ)`, whose source is `W ×_Y Y'`. -/
public lemma isReduced_comap_ker_of_flat {W Y Y' : Scheme.{u}} (σ : W ⟶ Y) [QuasiCompact σ]
    (φ : Y' ⟶ Y) [Flat φ] [IsReduced (pullback σ φ)] :
    IsReduced (σ.ker.comap φ).subscheme := by
  have := toImage_isSchemeTheoreticallyDominant σ
  let h := pullback.snd φ σ.ker.subschemeι
  have hsq : IsPullback (pullback.fst σ.toImage h) (pullback.snd σ.toImage h ≫ pullback.fst φ _)
      (σ.toImage ≫ σ.imageι) φ :=
    (IsPullback.of_hasPullback σ.toImage h).paste_vert (IsPullback.of_hasPullback φ _).flip
  rw [σ.toImage_imageι] at hsq
  have : IsReduced (pullback σ.toImage h) :=
    isReduced_of_isOpenImmersion (hsq.isoPullback.hom)
  have : IsReduced (pullback φ σ.ker.subschemeι) :=
    IsSchemeTheoreticallyDominant.isReduced (pullback.snd σ.toImage h)
  exact isReduced_of_isOpenImmersion (σ.ker.comapIso φ).hom

/-- Two reduced closed subschemes with the same support agree, in the form needed for an
inverse image. -/
public lemma eq_comap_of_preimage_support_eq {Y Y' : Scheme.{u}} (Z : Y'.IdealSheafData)
    [IsReduced Z.subscheme] (D : Y.IdealSheafData) (φ : Y' ⟶ Y)
    [IsReduced (D.comap φ).subscheme]
    (h : φ ⁻¹' (D.support : Set Y) = Z.support) : Z = D.comap φ := by
  have hsupp : (D.comap φ).support = Z.support := by
    ext1
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, h]
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme (D.comap φ) _ hsupp]

/-- The preimage of `S` under `τ ≫ f` is `S'` when the preimage of `S` under `f` is the image of
`S'` under the injective `τ`. -/
public lemma preimage_comp_eq_of_preimage_eq_image {α β δ : Type*} {τ : α → β} {f : β → δ}
    (hτ : Function.Injective τ) {S : Set δ} {S' : Set α} (h : f ⁻¹' S = τ '' S') :
    (f ∘ τ) ⁻¹' S = S' := by
  rw [Set.preimage_comp, h, hτ.preimage_image]

end Faltings
