module
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Jacobian.Basic
public import Mordell.Jacobian.PicZeroRigidified
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Proper
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FiniteStageContinuity
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor

/-!
# Existence and uniqueness of the Jacobian

Let `(C, P)` be a curve over a field `k` with a rational divisor `P` of degree one. A Jacobian of
`C` is an abelian variety `J` over `k` with a morphism `ι : P⁰_C ⟶ J(-)` that is bijective on the
`k`-schemes `T` with `C(T) ≠ ∅`. Then `C` has a Jacobian, and it is unique up to unique
isomorphism: for two Jacobians `(J, ι)` and `(J', ι')` there is exactly one isomorphism
`e : J ≅ J'` of `k`-schemes with `yoneda.map e.hom ∘ ι = ι'`.

*Uniqueness.* For Jacobians `A`, `B` the composite `ι_B ∘ ι_A⁻¹` is defined on `k`-schemes with a
`C`-point; at `A.J ×_k C` it descends along the fpqc projection `A.J ×_k C ⟶ A.J`.

*Existence.* Over a finite extension `L/k` over which `C` has a point and the translates of a
cohomology chart meet every field-valued point, the rigidified `Pic⁰` of `C_L` is represented by
an abelian variety `V` [Stacks, Tag 0B9Q]. The descent datum on `V` coming from the representation
is effective because `V` is projective, giving `J` over `k`. Finally `P⁰_C` is an fpqc sheaf on
the pointed `k`-schemes, so `J` represents it there, and the representation extends to a morphism
of functors on all `k`-schemes by descent along `T ×_k C ⟶ T`.

## Main results

* `Faltings.Jacobian.nonempty_and_existsUnique_iso`: a curve with a rational divisor of degree
  one has a Jacobian, and any two Jacobians are isomorphic by a unique isomorphism compatible
  with their morphisms `ι`.

The description of `P⁰_C` as a quotient, its rigidification, and the comparison
`Faltings.relativePicZeroFunctor.rigidifiedIso` with the rigidified `Pic⁰` of `C_E` are in
`Mordell.Jacobian.PicZeroRigidified`.

## Implementation notes

An isomorphism of Jacobians `(J, ι) ≅ (J', ι')` is an isomorphism `e : J ≅ J'` in
`Over (Spec k)` such that `ι ≫ yoneda.map e.hom = ι'`. That `e` respects the group laws is not
part of the statement: it follows, since `e` commutes with the bijections `ι(T)`.

The finite extension `L` is found by working over an algebraic closure `Ω` of the residue field of
a closed point, where finitely many chart translates cover [Stacks, Tag 0B9Y], and descending the
finitely many classes involved to a finite subextension.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Theorem 1.6, Remark 1.4 and Section 1.
* [Stacks] The Stacks Project, Tags 0B9Q, 0B9Y.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Faltings

section Uniqueness

/-! ### Uniqueness of the Jacobian -/

variable {k : Type u} [Field k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
  [IsSmoothProjectiveCurve k f]

/-- The `k`-scheme `T ×_k C`. -/
private noncomputable abbrev prodCurve (f : C ⟶ Spec (.of k)) (T : Over (Spec (.of k))) :
    Over (Spec (.of k)) :=
  Over.mk (pullback.fst T.hom f ≫ T.hom)

/-- The projection `T ×_k C ⟶ T`. -/
private noncomputable abbrev prodCurveFst (f : C ⟶ Spec (.of k)) (T : Over (Spec (.of k))) :
    prodCurve f T ⟶ T :=
  Over.homMk (pullback.fst T.hom f)

/-- The projection `T ×_k C ⟶ C`, a `C`-point of `T ×_k C`. -/
private noncomputable abbrev prodCurveSnd (f : C ⟶ Spec (.of k)) (T : Over (Spec (.of k))) :
    prodCurve f T ⟶ Over.mk f :=
  Over.homMk (pullback.snd T.hom f) pullback.condition.symm

private theorem effectiveEpi_prodCurveFst (T : Over (Spec (.of k))) :
    EffectiveEpi (prodCurveFst f T).left :=
  Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat (pullback.fst T.hom f)

/-- Morphisms out of `T` are determined after pulling back to `T ×_k C`. -/
private theorem prodCurveFst_cancel {T Y : Over (Spec (.of k))} {g h : T ⟶ Y}
    (hgh : prodCurveFst f T ≫ g = prodCurveFst f T ≫ h) : g = h := by
  have := effectiveEpi_prodCurveFst (f := f) T
  ext1
  exact (cancel_epi (prodCurveFst f T).left).1 (congrArg CommaMorphism.left hgh)

/-- The comparison `ι_B ∘ ι_A⁻¹`, on `k`-schemes with a `C`-point. -/
private noncomputable def compare (A B : Jacobian k f) (T : Over (Spec (.of k)))
    (hT : Nonempty (T ⟶ Over.mk f)) (y : T ⟶ A.J) : T ⟶ B.J :=
  haveI := A.isIso_app T hT
  B.ι.app (op T) (inv (A.ι.app (op T)) y)

private theorem compare_ι (A B : Jacobian k f) (T : Over (Spec (.of k)))
    (hT : Nonempty (T ⟶ Over.mk f)) (x) :
    compare A B T hT (A.ι.app (op T) x) = B.ι.app (op T) x := by
  have := A.isIso_app T hT
  simp only [compare]
  congr 1
  exact IsIso.hom_inv_id_apply (A.ι.app (op T)) x

private theorem compare_comp (A B : Jacobian k f) {Z T : Over (Spec (.of k))} (g : Z ⟶ T)
    (hT : Nonempty (T ⟶ Over.mk f)) (y : T ⟶ A.J) :
    compare A B Z ⟨g ≫ hT.some⟩ (g ≫ y) = g ≫ compare A B T hT y := by
  have := A.isIso_app T hT
  obtain ⟨x, rfl⟩ : ∃ x, A.ι.app (op T) x = y :=
    ⟨inv (A.ι.app (op T)) y, IsIso.inv_hom_id_apply (A.ι.app (op T)) y⟩
  rw [compare_ι]
  have hA := NatTrans.naturality_apply A.ι g.op x
  have hB := NatTrans.naturality_apply B.ι g.op x
  rw [show (ConcreteCategory.hom ((yoneda.obj A.J).map g.op))
      ((ConcreteCategory.hom (A.ι.app (op T))) x) = g ≫ A.ι.app (op T) x from rfl] at hA
  rw [show (ConcreteCategory.hom ((yoneda.obj B.J).map g.op))
      ((ConcreteCategory.hom (B.ι.app (op T))) x) = g ≫ B.ι.app (op T) x from rfl] at hB
  rw [← hA, compare_ι, hB]

/-- A `C`-point of `T` lets `T` map to `T ×_k C` over `T`. -/
private noncomputable abbrev prodCurveLift {S T : Over (Spec (.of k))} (y : S ⟶ T)
    (c : S ⟶ Over.mk f) : S ⟶ prodCurve f T :=
  Over.homMk (pullback.lift y.left c.left ((Over.w y).trans (Over.w c).symm))
    (by simp only [Over.mk_hom, pullback.lift_fst_assoc]; exact Over.w y)

omit [IsSmoothProjectiveCurve k f] in
private theorem prodCurveLift_fst {S T : Over (Spec (.of k))} (y : S ⟶ T) (c : S ⟶ Over.mk f) :
    prodCurveLift y c ≫ prodCurveFst f T = y := by
  ext1; exact pullback.lift_fst _ _ _

/-- The comparison `ι_B ∘ ι_A⁻¹` at `A.J ×_k C` applied to the projection agrees on the two
legs of any pair of morphisms equalised by the projection. -/
private theorem compare_prodCurveFst_eq (A B : Jacobian k f) {Z : Scheme.{u}}
    (g₁ g₂ : Z ⟶ (prodCurve f A.J).left)
    (h : g₁ ≫ (prodCurveFst f A.J).left = g₂ ≫ (prodCurveFst f A.J).left) :
    g₁ ≫ (compare A B (prodCurve f A.J) ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J)).left =
      g₂ ≫ (compare A B (prodCurve f A.J) ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J)).left := by
  have hw : g₂ ≫ (prodCurve f A.J).hom = g₁ ≫ (prodCurve f A.J).hom := by
    change g₂ ≫ (prodCurveFst f A.J).left ≫ A.J.hom = g₁ ≫ (prodCurveFst f A.J).left ≫ A.J.hom
    rw [← Category.assoc, ← h, Category.assoc]
  let g₁' : Over.mk (g₁ ≫ (prodCurve f A.J).hom) ⟶ prodCurve f A.J := Over.homMk g₁ rfl
  let g₂' : Over.mk (g₁ ≫ (prodCurve f A.J).hom) ⟶ prodCurve f A.J := Over.homMk g₂ hw
  have hg : g₁' ≫ prodCurveFst f A.J = g₂' ≫ prodCurveFst f A.J := by
    ext1; exact h
  have h₁ := compare_comp A B g₁' ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J)
  have h₂ := compare_comp A B g₂' ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J)
  rw [hg] at h₁
  exact congrArg CommaMorphism.left (h₁.symm.trans h₂)

/-- The comparison morphism `A.J ⟶ B.J` of two Jacobians, descended from `A.J ×_k C`. -/
private noncomputable def homOf (A B : Jacobian k f) : A.J ⟶ B.J :=
  haveI := effectiveEpi_prodCurveFst (f := f) A.J
  Over.homMk (EffectiveEpi.desc (prodCurveFst f A.J).left
    (compare A B (prodCurve f A.J) ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J)).left
    (fun g₁ g₂ h => compare_prodCurveFst_eq A B g₁ g₂ h))
    (by
      apply (cancel_epi (prodCurveFst f A.J).left).1
      rw [← Category.assoc, EffectiveEpi.fac]
      exact Over.w _)

private theorem prodCurveFst_homOf (A B : Jacobian k f) :
    prodCurveFst f A.J ≫ homOf A B =
      compare A B (prodCurve f A.J) ⟨prodCurveSnd f A.J⟩ (prodCurveFst f A.J) := by
  have := effectiveEpi_prodCurveFst (f := f) A.J
  ext1
  rw [Over.comp_left]
  simp only [homOf, Over.homMk_left]
  exact EffectiveEpi.fac _ _ fun g₁ g₂ h => compare_prodCurveFst_eq A B g₁ g₂ h

private theorem comp_homOf (A B : Jacobian k f) {S : Over (Spec (.of k))}
    (hS : Nonempty (S ⟶ Over.mk f)) (y : S ⟶ A.J) :
    y ≫ homOf A B = compare A B S hS y := by
  conv_lhs => rw [← prodCurveLift_fst y hS.some, Category.assoc, prodCurveFst_homOf,
    ← compare_comp, prodCurveLift_fst]

private theorem compare_compare (A B : Jacobian k f) {S : Over (Spec (.of k))}
    (hS : Nonempty (S ⟶ Over.mk f)) (y : S ⟶ A.J) :
    compare B A S hS (compare A B S hS y) = y := by
  have := A.isIso_app S hS
  obtain ⟨x, rfl⟩ : ∃ x, A.ι.app (op S) x = y :=
    ⟨inv (A.ι.app (op S)) y, IsIso.inv_hom_id_apply (A.ι.app (op S)) y⟩
  rw [compare_ι, compare_ι]

private theorem homOf_homOf (A B : Jacobian k f) : homOf A B ≫ homOf B A = 𝟙 A.J := by
  apply prodCurveFst_cancel (f := f)
  rw [← Category.assoc, prodCurveFst_homOf, comp_homOf B A ⟨prodCurveSnd f A.J⟩,
    compare_compare, Category.comp_id]

private theorem ι_comp_homOf (A B : Jacobian k f) : A.ι ≫ yoneda.map (homOf A B) = B.ι := by
  ext T x
  change A.ι.app T x ≫ homOf A B = B.ι.app T x
  apply prodCurveFst_cancel (f := f)
  have hA := NatTrans.naturality_apply A.ι (prodCurveFst f T.unop).op x
  have hB := NatTrans.naturality_apply B.ι (prodCurveFst f T.unop).op x
  rw [show (ConcreteCategory.hom ((yoneda.obj A.J).map (prodCurveFst f T.unop).op))
      ((ConcreteCategory.hom (A.ι.app T)) x) = prodCurveFst f T.unop ≫ A.ι.app T x from rfl]
    at hA
  rw [show (ConcreteCategory.hom ((yoneda.obj B.J).map (prodCurveFst f T.unop).op))
      ((ConcreteCategory.hom (B.ι.app T)) x) = prodCurveFst f T.unop ≫ B.ι.app T x from rfl]
    at hB
  rw [← Category.assoc, ← hA, ← hB, comp_homOf A B ⟨prodCurveSnd f T.unop⟩, compare_ι]

/-- Two Jacobians are isomorphic by a unique isomorphism compatible with their `ι`. -/
private theorem existsUnique_iso (A B : Jacobian k f) :
    ∃! e : A.J ≅ B.J, A.ι ≫ yoneda.map e.hom = B.ι := by
  refine ⟨⟨homOf A B, homOf B A, homOf_homOf A B, homOf_homOf B A⟩, ι_comp_homOf A B, ?_⟩
  intro e he
  ext1
  change e.hom = homOf A B
  apply prodCurveFst_cancel (f := f)
  have hT : Nonempty (prodCurve f A.J ⟶ Over.mk f) := ⟨prodCurveSnd f A.J⟩
  rw [comp_homOf A B hT]
  have := A.isIso_app _ hT
  obtain ⟨x, hx⟩ : ∃ x, A.ι.app (op (prodCurve f A.J)) x = prodCurveFst f A.J :=
    ⟨_, IsIso.inv_hom_id_apply (A.ι.app (op (prodCurve f A.J))) (prodCurveFst f A.J)⟩
  rw [← hx, compare_ι, ← he]
  rfl

end Uniqueness

/-- A representation of a presheaf `G` of sets on `S`-schemes by an `S`-scheme `J`, on the
`S`-schemes `T` admitting a morphism to `Y`: bijections `G(T) ≃ J(T)`, natural in `T`. -/
private structure RepOn {S : Scheme.{u}} (Y : Over S) (G : (Over S)ᵒᵖ ⥤ Type u)
    (J : Over S) where
  /-- The bijection at an `S`-scheme admitting a morphism to `Y`. -/
  equiv : ∀ T : Over S, Nonempty (T ⟶ Y) → (G.obj (op T) ≃ (T ⟶ J))
  /-- Naturality. -/
  naturality : ∀ {Z T : Over S} (g : Z ⟶ T) (hT : Nonempty (T ⟶ Y)) (x : G.obj (op T)),
    equiv Z ⟨g ≫ hT.some⟩ (G.map g.op x) = g ≫ equiv T hT x

section Descent

/-! ### Descent along a finite locally free morphism -/

variable {S X : Scheme.{u}} (f : X ⟶ S) (V : Over X) (G : (Over S)ᵒᵖ ⥤ Type u)
  (Θ : ∀ W : Over S, (W ⟶ (Over.map f).obj V) → G.obj (op W))
  (hΘ : ∀ {W' W : Over S} (h : W' ⟶ W) (a : W ⟶ (Over.map f).obj V),
    Θ W' (h ≫ a) = G.map h.op (Θ W a))
  (hbij : ∀ (W : Over S) (x : W ⟶ Over.mk f) (y : G.obj (op W)),
    ∃! a : W ⟶ (Over.map f).obj V, a ≫ structureMap f V = x ∧ Θ W a = y)

include hbij in
private theorem eq_of_Θ {W : Over S} (a b : W ⟶ (Over.map f).obj V)
    (h₁ : a ≫ structureMap f V = b ≫ structureMap f V) (h₂ : Θ W a = Θ W b) : a = b :=
  (hbij W _ (Θ W a)).unique ⟨rfl, rfl⟩ ⟨h₁.symm, h₂.symm⟩

private noncomputable def glue (W : Over S) (x : W ⟶ Over.mk f) (y : G.obj (op W)) :
    W ⟶ (Over.map f).obj V :=
  (hbij W x y).exists.choose

private theorem glue_spec (W : Over S) (x : W ⟶ Over.mk f) (y : G.obj (op W)) :
    glue f V G Θ hbij W x y ≫ structureMap f V = x ∧ Θ W (glue f V G Θ hbij W x y) = y :=
  (hbij W x y).exists.choose_spec

/-- The `V`-component of the gluing map `V ×_S X ⟶ X ×_S V`. -/
private noncomputable abbrev ψ₀ : (Over.map f).obj V ⨯ Over.mk f ⟶ (Over.map f).obj V :=
  glue f V G Θ hbij _ prod.snd (Θ _ prod.fst)

private noncomputable abbrev ψ₁ : Over.mk f ⨯ (Over.map f).obj V ⟶ (Over.map f).obj V :=
  glue f V G Θ hbij _ prod.fst (Θ _ prod.snd)

private noncomputable abbrev φfwd :
    (Over.map f).obj V ⨯ Over.mk f ⟶ Over.mk f ⨯ (Over.map f).obj V :=
  prod.lift (prod.fst ≫ structureMap f V) (ψ₀ f V G Θ hbij)

private noncomputable abbrev φbwd :
    Over.mk f ⨯ (Over.map f).obj V ⟶ (Over.map f).obj V ⨯ Over.mk f :=
  prod.lift (ψ₁ f V G Θ hbij) (prod.snd ≫ structureMap f V)

include hΘ in
private theorem φfwd_φbwd : φfwd f V G Θ hbij ≫ φbwd f V G Θ hbij = 𝟙 _ := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
    apply eq_of_Θ f V G Θ hbij
    · simp only [Category.assoc, (glue_spec f V G Θ hbij _ _ _).1, prod.lift_fst]
    · rw [hΘ, (glue_spec f V G Θ hbij _ _ _).2, ← hΘ, prod.lift_snd,
        (glue_spec f V G Θ hbij _ _ _).2]
  · rw [Category.assoc, prod.lift_snd, ← Category.assoc, prod.lift_snd,
      (glue_spec f V G Θ hbij _ _ _).1, Category.id_comp]

include hΘ in
private theorem φbwd_φfwd : φbwd f V G Θ hbij ≫ φfwd f V G Θ hbij = 𝟙 _ := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.lift_fst, ← Category.assoc, prod.lift_fst,
      (glue_spec f V G Θ hbij _ _ _).1, Category.id_comp]
  · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
    apply eq_of_Θ f V G Θ hbij
    · simp only [Category.assoc, (glue_spec f V G Θ hbij _ _ _).1, prod.lift_snd]
    · rw [hΘ, (glue_spec f V G Θ hbij _ _ _).2, ← hΘ, prod.lift_fst,
        (glue_spec f V G Θ hbij _ _ _).2]

include hΘ in
private theorem Θ_comp_ψ₀ {W : Over S} (h : W ⟶ (Over.map f).obj V ⨯ Over.mk f) :
    Θ W (h ≫ ψ₀ f V G Θ hbij) = Θ W (h ≫ prod.fst) := by
  rw [hΘ, hΘ, (glue_spec f V G Θ hbij _ _ _).2]

include hΘ in
private theorem cocycle : prod.map (φfwd f V G Θ hbij) (𝟙 (Over.mk f)) ≫
    prodMapLastTwo (φfwd f V G Θ hbij) = prodMapFirstThird (φfwd f V G Θ hbij) := by
  apply prod.hom_ext
  · apply prod.hom_ext
    · simp [prodMapLastTwo, prodMapFirstThird]
    · simp [prodMapLastTwo, prodMapFirstThird, (glue_spec f V G Θ hbij _ _ _).1]
  · simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv, prod.comp_lift,
      prod.map_fst, Category.comp_id, prod.map_snd_assoc, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.mk_fst, BinaryFan.mk_snd, limit.lift_π_assoc, pair_obj_right, pair_obj_left,
      Category.assoc, prod.map_fst_assoc, prodMapFirstThird, prod.braiding_hom, prod.map_snd]
    apply eq_of_Θ f V G Θ hbij
    · simp [(glue_spec f V G Θ hbij _ _ _).1]
    · rw [← Category.assoc, Θ_comp_ψ₀ f V G Θ hΘ hbij, Θ_comp_ψ₀ f V G Θ hΘ hbij]
      simp only [Category.assoc, prod.lift_fst, prod.map_fst_assoc, prod.lift_snd]
      rw [Θ_comp_ψ₀ f V G Θ hΘ hbij]

/-- The gluing isomorphism `V ×_S X ≅ X ×_S V` over `X ×_S X` built from `Θ`. -/
private noncomputable def gluingIso :
    Over.mk (prod.map (structureMap f V) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f V)) where
  hom := Over.homMk (φfwd f V G Θ hbij) (by
    apply prod.hom_ext
    · simp
    · simp [(glue_spec f V G Θ hbij _ _ _).1])
  inv := Over.homMk (φbwd f V G Θ hbij) (by
    apply prod.hom_ext
    · simp [(glue_spec f V G Θ hbij _ _ _).1]
    · simp)
  hom_inv_id := by ext1; exact φfwd_φbwd f V G Θ hΘ hbij
  inv_hom_id := by ext1; exact φbwd_φfwd f V G Θ hΘ hbij

/-- The descent datum on `V` relative to `f` built from `Θ`. -/
private noncomputable def datum : DescentDatum f :=
  DescentDatum.mk' V (gluingIso f V G Θ hΘ hbij) (cocycle f V G Θ hΘ hbij)

end Descent

section Canonical

/-! ### Points of the canonical descent datum -/

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The point `(j, x)` of the canonical descent datum of `J`. -/
private noncomputable def canPt (J : Over S) {W : Over S} (j : W ⟶ J) (x : W ⟶ Over.mk f) :
    W ⟶ (Over.map f).obj (((DescentData.canonicalFunctor f).obj J).obj ()) :=
  Over.homMk (pullback.lift (f := J.hom) (g := f) j.left x.left
      ((Over.w j).trans (Over.w x).symm) ≫ (DescentData.canonicalObjIso f J).inv.left) (by
    have hw := Over.w (DescentData.canonicalObjIso f J).inv
    simp only [Over.map_obj_hom, Category.assoc]
    rw [← Category.assoc _ _ f, hw]
    erw [pullback.lift_snd_assoc]
    exact Over.w x)

private theorem canPt_structureMap (J : Over S) {W : Over S} (j : W ⟶ J)
    (x : W ⟶ Over.mk f) :
    canPt f J j x ≫ structureMap f _ = x := by
  ext1
  have hw := Over.w (DescentData.canonicalObjIso f J).inv
  simp only [canPt, Over.comp_left, Over.homMk_left, Category.assoc]
  rw [hw]
  erw [pullback.lift_snd]

private theorem canPt_proj (J : Over S) {W : Over S} (j : W ⟶ J) (x : W ⟶ Over.mk f) :
    (canPt f J j x).left ≫ DescentData.canonicalProjection f J = j.left := by
  simp only [canPt, Over.homMk_left, DescentData.canonicalProjection, Category.assoc]
  rw [← Category.assoc (DescentData.canonicalObjIso f J).inv.left, ← Over.comp_left,
    Iso.inv_hom_id, Over.id_left, Category.id_comp]
  erw [pullback.lift_fst]

/-- The gluing isomorphism of a canonical descent datum leaves the projection to `J` unchanged,
read on products in `Over S`. -/
private theorem canGluing_proj (J : Over S) :
    (((DescentData.canonicalFunctor f).obj J).gluing () ()).hom.left.left ≫
        (prod.snd : Over.mk f ⨯ (Over.map f).obj (((DescentData.canonicalFunctor f).obj J).obj ())
          ⟶ _).left ≫ DescentData.canonicalProjection f J =
      (prod.fst : (Over.map f).obj (((DescentData.canonicalFunctor f).obj J).obj ()) ⨯ Over.mk f
          ⟶ _).left ≫ DescentData.canonicalProjection f J := by
  have h := DescentData.canonicalFunctor_gluingPullbackIso_hom_snd_projection f J
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, Category.assoc] at h
  erw [Over.prodLeftIsoPullback_hom_snd_assoc] at h
  rw [← cancel_epi (Over.prodLeftIsoPullback
    ((Over.map f).obj (((DescentData.canonicalFunctor f).obj J).obj ())) (Over.mk f)).inv,
    Over.prodLeftIsoPullback_inv_fst_assoc]
  exact h

/-- **The gluing isomorphism of a canonical descent datum swaps the base coordinates** of a
point `(j, x)`. -/
private theorem lift_canPt_gluing (J : Over S) {W : Over S} (j : W ⟶ J) (x₁ x₂ : W ⟶ Over.mk f) :
    prod.lift (canPt f J j x₁) x₂ ≫
        (((DescentData.canonicalFunctor f).obj J).gluing () ()).hom.left =
      prod.lift x₁ (canPt f J j x₂) := by
  apply prod.hom_ext
  · rw [Category.assoc, DescentData.gluing_hom_fst, prod.lift_fst_assoc, prod.lift_fst,
      canPt_structureMap]
  · rw [prod.lift_snd]
    ext1
    apply DescentData.canonical_hom_ext f J
    · rw [canPt_proj, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
        canGluing_proj, ← Category.assoc, ← Over.comp_left, prod.lift_fst, canPt_proj]
    · have h := congrArg CommaMorphism.left
        (DescentData.gluing_hom_snd_structureMap ((DescentData.canonicalFunctor f).obj J) () ())
      simp only [Over.comp_left, Over.homMk_left] at h
      have h₂ := congrArg CommaMorphism.left (canPt_structureMap f J j x₂)
      simp only [Over.comp_left, Over.homMk_left] at h₂
      rw [h₂, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h,
        ← Over.comp_left, prod.lift_snd]

end Canonical

section DescentTheorem

/-! ### Representations descend along a finite locally free surjection -/

variable {S X : Scheme.{u}} (f : X ⟶ S) (V : Over X) (G : (Over S)ᵒᵖ ⥤ Type u)
  (Θ : ∀ W : Over S, (W ⟶ (Over.map f).obj V) → G.obj (op W))
  (hΘ : ∀ {W' W : Over S} (h : W' ⟶ W) (a : W ⟶ (Over.map f).obj V),
    Θ W' (h ≫ a) = G.map h.op (Θ W a))
  (hbij : ∀ (W : Over S) (x : W ⟶ Over.mk f) (y : G.obj (op W)),
    ∃! a : W ⟶ (Over.map f).obj V, a ≫ structureMap f V = x ∧ Θ W a = y)

private theorem canonicalProjection_comp (J : Over S) :
    DescentData.canonicalProjection f J ≫ J.hom =
      (((DescentData.canonicalFunctor f).obj J).obj ()).hom ≫ f := by
  have hw := Over.w (DescentData.canonicalObjIso f J).hom
  simp only [DescentData.canonicalProjection, Category.assoc, pullback.condition]
  rw [← Category.assoc]
  exact congrArg (· ≫ f) hw

private theorem canPt_comp (J : Over S) {W' W : Over S} (g : W' ⟶ W) (j : W ⟶ J)
    (x : W ⟶ Over.mk f) : canPt f J (g ≫ j) (g ≫ x) = g ≫ canPt f J j x := by
  ext1
  apply DescentData.canonical_hom_ext f J
  · rw [canPt_proj, Over.comp_left, Over.comp_left, Category.assoc, canPt_proj]
  · have h₁ := congrArg CommaMorphism.left (canPt_structureMap f J (g ≫ j) (g ≫ x))
    have h₂ := congrArg CommaMorphism.left (canPt_structureMap f J j x)
    simp only [Over.comp_left, Over.homMk_left] at h₁ h₂
    rw [h₁, Over.comp_left, Category.assoc, h₂]

include hΘ hbij in
/-- **Descent along a finite locally free surjection.** Let `f : X ⟶ S` be finite locally free
and surjective, and let a presheaf `G` on `S`-schemes be represented, on `S`-schemes with an
`X`-structure, by a projective `X`-scheme `V`, compatibly with every `X`-structure. Then `G` is
represented on the `S`-schemes admitting a morphism to `X` by an `S`-scheme `J` with `J_X ≅ V`. -/
private theorem exists_repOn_of_isFiniteLocallyFree [Surjective f]
    [Stacks.Morphisms.IsFiniteLocallyFree f] (hV : IsProjective V.hom) :
    ∃ J : Over S, Nonempty (RepOn (Over.mk f) G J) ∧
      Nonempty ((((DescentData.canonicalFunctor f).obj J).obj ()) ≅ V) := by
  obtain ⟨J, ⟨θ⟩⟩ := DescentDatum.isEffective_of_isProjective (datum f V G Θ hΘ hbij) hV
  let θ₀ : ((DescentData.canonicalFunctor f).obj J).obj () ≅ V :=
    (DescentDatum.forget f).mapIso θ
  let a : ∀ {W : Over S}, (W ⟶ J) → (W ⟶ Over.mk f) → (W ⟶ (Over.map f).obj V) :=
    fun j x => canPt f J j x ≫ (Over.map f).map θ₀.hom
  have ha₁ : ∀ {W : Over S} (j : W ⟶ J) (x : W ⟶ Over.mk f), a j x ≫ structureMap f V = x := by
    intro W j x
    have : (Over.map f).map θ₀.hom ≫ structureMap f V = structureMap f _ := by
      ext1; exact Over.w θ₀.hom
    simp only [a, Category.assoc, this, canPt_structureMap]
  have hkey : ∀ {W : Over S} (j : W ⟶ J) (x₁ x₂ : W ⟶ Over.mk f),
      Θ W (a j x₁) = Θ W (a j x₂) := by
    intro W j x₁ x₂
    have hcomm := θ.hom.comm () ()
    have h := congrArg (fun t => prod.lift (canPt f J j x₁) x₂ ≫ t ≫ prod.snd) hcomm
    change prod.lift (canPt f J j x₁) x₂ ≫ (prod.map ((Over.map f).map θ₀.hom) (𝟙 _) ≫
      (gluingIso f V G Θ hΘ hbij).hom.left) ≫ prod.snd =
      prod.lift (canPt f J j x₁) x₂ ≫
        ((((DescentData.canonicalFunctor f).obj J).gluing () ()).hom.left ≫
          prod.map (𝟙 _) ((Over.map f).map θ₀.hom)) ≫ prod.snd at h
    have e1 : prod.lift (canPt f J j x₁) x₂ ≫ prod.map ((Over.map f).map θ₀.hom) (𝟙 (Over.mk f)) =
        prod.lift (a j x₁) x₂ := by
      apply prod.hom_ext <;> simp [a]
    simp only [Category.assoc, prod.map_snd] at h
    rw [← Category.assoc (prod.lift (canPt f J j x₁) x₂) (prod.map _ _), e1,
      ← Category.assoc (prod.lift (canPt f J j x₁) x₂), lift_canPt_gluing, prod.lift_snd_assoc] at h
    simp only [gluingIso, Over.homMk_left, prod.lift_snd] at h
    change Θ W (a j x₁) = Θ W (canPt f J j x₂ ≫ (Over.map f).map θ₀.hom)
    rw [← h, Θ_comp_ψ₀ f V G Θ hΘ hbij, prod.lift_fst]
  have hinj : ∀ {W : Over S} (j j' : W ⟶ J) (x : W ⟶ Over.mk f), a j x = a j' x → j = j' := by
    intro W j j' x h
    have h' : canPt f J j x = canPt f J j' x := (cancel_mono ((Over.map f).map θ₀.hom)).1 h
    ext1
    rw [← canPt_proj f J j x, ← canPt_proj f J j' x, h']
  have hsurj : ∀ {W : Over S} (b : W ⟶ (Over.map f).obj V) (x : W ⟶ Over.mk f),
      b ≫ structureMap f V = x → ∃ j, a j x = b := by
    intro W b x hb
    let c := b ≫ (Over.map f).map θ₀.inv
    have hc : c ≫ structureMap f _ = x := by
      have : (Over.map f).map θ₀.inv ≫ structureMap f _ = structureMap f V := by
        ext1; exact Over.w θ₀.inv
      simp only [c, Category.assoc, this, hb]
    refine ⟨Over.homMk (c.left ≫ DescentData.canonicalProjection f J) ?_, ?_⟩
    · rw [Category.assoc, canonicalProjection_comp, ← Category.assoc]
      exact Over.w c
    · have : canPt f J (Over.homMk (c.left ≫ DescentData.canonicalProjection f J) (by
          rw [Category.assoc, canonicalProjection_comp, ← Category.assoc]
          exact Over.w c)) x = c := by
        ext1
        apply DescentData.canonical_hom_ext f J
        · rw [canPt_proj]; rfl
        · have h₁ := congrArg CommaMorphism.left (canPt_structureMap f J
            (Over.homMk (c.left ≫ DescentData.canonicalProjection f J) (by
              rw [Category.assoc, canonicalProjection_comp, ← Category.assoc]
              exact Over.w c)) x)
          have h₂ := congrArg CommaMorphism.left hc
          simp only [Over.comp_left, Over.homMk_left] at h₁ h₂
          rw [h₁, h₂]
      simp only [a, this, c, Category.assoc]
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
  let fwd : ∀ (W : Over S), (W ⟶ Over.mk f) → (W ⟶ J) → G.obj (op W) :=
    fun W x j => Θ W (a j x)
  have hbij' : ∀ (W : Over S) (x : W ⟶ Over.mk f), Function.Bijective (fwd W x) := by
    intro W x
    refine ⟨fun j j' h => hinj j j' x (eq_of_Θ f V G Θ hbij _ _ (by rw [ha₁, ha₁]) h),
      fun y => ?_⟩
    obtain ⟨j, hj⟩ := hsurj (glue f V G Θ hbij W x y) x (glue_spec f V G Θ hbij W x y).1
    exact ⟨j, by simp only [fwd, hj, (glue_spec f V G Θ hbij W x y).2]⟩
  refine ⟨J, ⟨{
    equiv := fun W hW => (Equiv.ofBijective _ (hbij' W hW.some)).symm
    naturality := fun {Z T} g hT y => ?_ }⟩, ⟨θ₀⟩⟩
  rw [Equiv.symm_apply_eq]
  obtain ⟨j, rfl⟩ := (hbij' T hT.some).2 y
  rw [Equiv.ofBijective_symm_apply_apply]
  change G.map g.op (Θ T (a j hT.some)) = Θ Z (a (g ≫ j) _)
  rw [hkey (g ≫ j) _ (g ≫ hT.some)]
  simp only [a, canPt_comp, Category.assoc, hΘ]

end DescentTheorem

section Sheafify

/-! ### The representation of the descent-sheafification -/

variable {S : Scheme.{u}} (Y : Over S)

/-- The `S`-scheme `T ×_S Y`. -/
private noncomputable abbrev prodY (T : Over S) : Over S :=
  Over.mk (pullback.fst T.hom Y.hom ≫ T.hom)

/-- The projection `T ×_S Y ⟶ T`. -/
private noncomputable abbrev prodYFst (T : Over S) : prodY Y T ⟶ T :=
  Over.homMk (pullback.fst T.hom Y.hom)

/-- The projection `T ×_S Y ⟶ Y`. -/
private noncomputable abbrev prodYSnd (T : Over S) : prodY Y T ⟶ Y :=
  Over.homMk (pullback.snd T.hom Y.hom) pullback.condition.symm

/-- The morphism `(y, c) : W ⟶ T ×_S Y`. -/
private noncomputable abbrev prodYLift {W T : Over S} (y : W ⟶ T) (c : W ⟶ Y) : W ⟶ prodY Y T :=
  Over.homMk (pullback.lift (f := T.hom) (g := Y.hom) y.left c.left
    ((Over.w y).trans (Over.w c).symm))
    (by simp only [Over.mk_hom, pullback.lift_fst_assoc]; exact Over.w y)

private theorem prodYLift_fst {W T : Over S} (y : W ⟶ T) (c : W ⟶ Y) :
    prodYLift Y y c ≫ prodYFst Y T = y := by
  ext1; exact pullback.lift_fst _ _ _

private theorem prodYLift_snd {W T : Over S} (y : W ⟶ T) (c : W ⟶ Y) :
    prodYLift Y y c ≫ prodYSnd Y T = c := by
  ext1; exact pullback.lift_snd _ _ _

/-- The base change `T' ×_S Y ⟶ T ×_S Y` of `h : T' ⟶ T`. -/
private noncomputable abbrev prodYMap {T' T : Over S} (h : T' ⟶ T) : prodY Y T' ⟶ prodY Y T :=
  prodYLift Y (prodYFst Y T' ≫ h) (prodYSnd Y T')

variable (G : (Over S)ᵒᵖ ⥤ Type u)

/-- An element of `G(T ×_S Y)` whose two pullbacks to any `Z` equalised by the projection to `T`
agree. -/
private def IsCompat (T : Over S) (z : G.obj (op (prodY Y T))) : Prop :=
  ∀ ⦃Z : Over S⦄ (g₁ g₂ : Z ⟶ prodY Y T), g₁ ≫ prodYFst Y T = g₂ ≫ prodYFst Y T →
    G.map g₁.op z = G.map g₂.op z

private theorem isCompat_map {T' T : Over S} (h : T' ⟶ T) (z : G.obj (op (prodY Y T)))
    (hz : IsCompat Y G T z) : IsCompat Y G T' (G.map (prodYMap Y h).op z) := by
  intro Z g₁ g₂ hg
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  apply hz
  simp only [Category.assoc, prodYLift_fst, reassoc_of% hg]

variable [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom]

private theorem effectiveEpi_prodYFst (T : Over S) : EffectiveEpi (prodYFst Y T).left :=
  Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat (pullback.fst T.hom Y.hom)

private theorem prodYFst_cancel {T Z : Over S} {g h : T ⟶ Z}
    (hgh : prodYFst Y T ≫ g = prodYFst Y T ≫ h) : g = h := by
  have := effectiveEpi_prodYFst Y T
  ext1
  exact (cancel_epi (prodYFst Y T).left).1 (congrArg CommaMorphism.left hgh)

variable {G} {J : Over S} (R : RepOn Y G J)

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem RepOn.naturality' {Z T : Over S} (g : Z ⟶ T) (hZ : Nonempty (Z ⟶ Y))
    (hT : Nonempty (T ⟶ Y)) (x : G.obj (op T)) :
    R.equiv Z hZ (G.map g.op x) = g ≫ R.equiv T hT x :=
  R.naturality g hT x

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem RepOn.symm_naturality {Z T : Over S} (g : Z ⟶ T) (hZ : Nonempty (Z ⟶ Y))
    (hT : Nonempty (T ⟶ Y)) (j : T ⟶ J) :
    (R.equiv Z hZ).symm (g ≫ j) = G.map g.op ((R.equiv T hT).symm j) := by
  rw [Equiv.symm_apply_eq, R.naturality' Y g hZ hT, Equiv.apply_symm_apply]

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem RepOn.desc_condition (T : Over S) (z : G.obj (op (prodY Y T)))
    (hz : IsCompat Y G T z) {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (prodY Y T).left)
    (h : g₁ ≫ (prodYFst Y T).left = g₂ ≫ (prodYFst Y T).left) :
    g₁ ≫ (R.equiv (prodY Y T) ⟨prodYSnd Y T⟩ z).left =
      g₂ ≫ (R.equiv (prodY Y T) ⟨prodYSnd Y T⟩ z).left := by
  have hw : g₂ ≫ (prodY Y T).hom = g₁ ≫ (prodY Y T).hom := by
    change g₂ ≫ (prodYFst Y T).left ≫ T.hom = g₁ ≫ (prodYFst Y T).left ≫ T.hom
    rw [← Category.assoc, ← h, Category.assoc]
  let g₁' : Over.mk (g₁ ≫ (prodY Y T).hom) ⟶ prodY Y T := Over.homMk g₁ rfl
  let g₂' : Over.mk (g₁ ≫ (prodY Y T).hom) ⟶ prodY Y T := Over.homMk g₂ hw
  have hg : g₁' ≫ prodYFst Y T = g₂' ≫ prodYFst Y T := by
    ext1; exact h
  have hZ : Nonempty (Over.mk (g₁ ≫ (prodY Y T).hom) ⟶ Y) := ⟨g₁' ≫ prodYSnd Y T⟩
  have h₁ := R.naturality' Y g₁' hZ ⟨prodYSnd Y T⟩ z
  have h₂ := R.naturality' Y g₂' hZ ⟨prodYSnd Y T⟩ z
  rw [hz g₁' g₂' hg, h₂] at h₁
  exact congrArg CommaMorphism.left h₁.symm

/-- The descended morphism `T ⟶ J` of a compatible element. -/
private noncomputable def RepOn.descend (T : Over S) (z : G.obj (op (prodY Y T)))
    (hz : IsCompat Y G T z) : T ⟶ J :=
  haveI := effectiveEpi_prodYFst Y T
  Over.homMk (EffectiveEpi.desc (prodYFst Y T).left
    (R.equiv (prodY Y T) ⟨prodYSnd Y T⟩ z).left
    (fun g₁ g₂ h => R.desc_condition Y T z hz g₁ g₂ h))
    (by
      apply (cancel_epi (prodYFst Y T).left).1
      rw [← Category.assoc, EffectiveEpi.fac]
      exact Over.w _)

private theorem RepOn.prodYFst_descend (T : Over S) (z : G.obj (op (prodY Y T)))
    (hz : IsCompat Y G T z) :
    prodYFst Y T ≫ R.descend Y T z hz = R.equiv (prodY Y T) ⟨prodYSnd Y T⟩ z := by
  have := effectiveEpi_prodYFst Y T
  ext1
  rw [Over.comp_left]
  simp only [RepOn.descend, Over.homMk_left]
  exact EffectiveEpi.fac _ _ fun g₁ g₂ h => R.desc_condition Y T z hz g₁ g₂ h

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem RepOn.isCompat_symm (T : Over S) (j : T ⟶ J) :
    IsCompat Y G T ((R.equiv (prodY Y T) ⟨prodYSnd Y T⟩).symm (prodYFst Y T ≫ j)) := by
  intro Z g₁ g₂ hg
  have hZ : Nonempty (Z ⟶ Y) := ⟨g₁ ≫ prodYSnd Y T⟩
  rw [← R.symm_naturality Y g₁ hZ, ← R.symm_naturality Y g₂ hZ, ← Category.assoc,
    ← Category.assoc, hg]

/-- **`J` represents the compatible elements on all `S`-schemes.** -/
private noncomputable def RepOn.compatEquiv (T : Over S) :
    {z : G.obj (op (prodY Y T)) // IsCompat Y G T z} ≃ (T ⟶ J) where
  toFun z := R.descend Y T z.1 z.2
  invFun j := ⟨(R.equiv (prodY Y T) ⟨prodYSnd Y T⟩).symm (prodYFst Y T ≫ j),
    R.isCompat_symm Y T j⟩
  left_inv z := by
    ext1
    simp only [R.prodYFst_descend, Equiv.symm_apply_apply]
  right_inv j := by
    apply prodYFst_cancel Y
    rw [R.prodYFst_descend, Equiv.apply_symm_apply]

private theorem RepOn.compatEquiv_naturality {T' T : Over S} (h : T' ⟶ T)
    (z : {z : G.obj (op (prodY Y T)) // IsCompat Y G T z}) :
    R.compatEquiv Y T' ⟨G.map (prodYMap Y h).op z.1, isCompat_map Y G h z.1 z.2⟩ =
      h ≫ R.compatEquiv Y T z := by
  apply prodYFst_cancel Y
  change prodYFst Y T' ≫ R.descend Y T' (G.map (prodYMap Y h).op z.1)
    (isCompat_map Y G h z.1 z.2) = prodYFst Y T' ≫ h ≫ R.descend Y T z.1 z.2
  rw [R.prodYFst_descend, R.naturality' Y (prodYMap Y h) ⟨prodYSnd Y T'⟩ ⟨prodYSnd Y T⟩,
    ← R.prodYFst_descend Y T z.1 z.2, ← Category.assoc, ← Category.assoc, prodYLift_fst]

end Sheafify

section SheafifyGroup

/-! ### The group structure on the descended representing object -/

variable {S : Scheme.{u}} (Y : Over S) [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom]
  (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem prodY_hom_ext {W T : Over S} {a b : W ⟶ prodY Y T}
    (h₁ : a ≫ prodYFst Y T = b ≫ prodYFst Y T) (h₂ : a ≫ prodYSnd Y T = b ≫ prodYSnd Y T) :
    a = b := by
  ext1
  exact pullback.hom_ext (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem prodYMap_id (T : Over S) : prodYMap Y (𝟙 T) = 𝟙 (prodY Y T) := by
  apply prodY_hom_ext Y <;> simp [prodYLift_fst, prodYLift_snd]

omit [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] in
private theorem prodYMap_comp {T'' T' T : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) :
    prodYMap Y (h' ≫ h) = prodYMap Y h' ≫ prodYMap Y h := by
  apply prodY_hom_ext Y
  · have e : prodYMap Y h' ≫ prodYFst Y T' = prodYFst Y T'' ≫ h' := prodYLift_fst _ _ _
    rw [prodYLift_fst, Category.assoc, prodYLift_fst, reassoc_of% e]
  · rw [prodYLift_snd, Category.assoc, prodYLift_snd, prodYLift_snd]

/-- The compatible elements of `G(T ×_S Y)`, a subgroup. -/
private def compatSubgroup (T : Over S) : AddSubgroup (G.obj (op (prodY Y T))) where
  carrier := {z | IsCompat Y (G ⋙ forget AddCommGrpCat) T z}
  zero_mem' := by
    intro Z g₁ g₂ _
    change (G.map g₁.op).hom 0 = (G.map g₂.op).hom 0
    simp
  add_mem' := by
    intro a b ha hb Z g₁ g₂ hg
    change (G.map g₁.op).hom (a + b) = (G.map g₂.op).hom (a + b)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (ha g₁ g₂ hg) (hb g₁ g₂ hg)
  neg_mem' := by
    intro a ha Z g₁ g₂ hg
    change (G.map g₁.op).hom (-a) = (G.map g₂.op).hom (-a)
    rw [map_neg, map_neg]
    exact congrArg (- ·) (ha g₁ g₂ hg)

/-- Pullback of compatible elements along `T' ⟶ T`. -/
private noncomputable def compatMap {T' T : Over S} (h : T' ⟶ T) :
    compatSubgroup Y G T →+ compatSubgroup Y G T' :=
  ((G.map (prodYMap Y h).op).hom.comp (compatSubgroup Y G T).subtype).codRestrict _
    fun z => isCompat_map Y (G ⋙ forget AddCommGrpCat) h z.1 z.2

/-- The compatible elements, as a presheaf of groups. -/
private noncomputable def compatFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Multiplicative (compatSubgroup Y G T.unop))
  map h := GrpCat.ofHom (AddMonoidHom.toMultiplicative (compatMap Y G h.unop))
  map_id T := by
    ext z
    apply Subtype.ext
    change (G.map (prodYMap Y (𝟙 T.unop)).op).hom z.1 = z.1
    rw [prodYMap_id, op_id, G.map_id]
    rfl
  map_comp h h' := by
    ext z
    apply Subtype.ext
    change (G.map (prodYMap Y (h'.unop ≫ h.unop)).op).hom z.1 =
      (G.map (prodYMap Y h'.unop).op).hom ((G.map (prodYMap Y h.unop).op).hom z.1)
    rw [prodYMap_comp, op_comp, G.map_comp]
    rfl

variable {G} {J : Over S} (R : RepOn Y (G ⋙ forget AddCommGrpCat) J)

/-- The group structure on `J` making it represent the compatible elements. -/
@[instance_reducible]
private noncomputable def RepOn.grpObj : GrpObj J :=
  GrpObj.ofRepresentableBy J (compatFunctor Y G)
    { homEquiv := fun {T} =>
        ((R.compatEquiv Y T).symm.trans (Equiv.refl _) : (T ⟶ J) ≃ _)
      homEquiv_comp := fun {T' T} h j => by
        apply (R.compatEquiv Y T').injective
        change R.compatEquiv Y T' ((R.compatEquiv Y T').symm (h ≫ j)) =
          R.compatEquiv Y T' ⟨_, isCompat_map Y _ h _ ((R.compatEquiv Y T).symm j).2⟩
        rw [Equiv.apply_symm_apply, R.compatEquiv_naturality, Equiv.apply_symm_apply] }

open CartesianMonoidalCategory in
open scoped MonObj in
/-- For the group law on `X` making it represent a group-valued presheaf `F`, the representing
bijection `(T ⟶ X) ≃ F(T)` is multiplicative. -/
private theorem representableBy_homEquiv_mul {D : Type*} [Category D]
    [CartesianMonoidalCategory D] (X : D) (F : Dᵒᵖ ⥤ GrpCat)
    (α : (F ⋙ forget GrpCat).RepresentableBy X) {T : D} (f g : T ⟶ X) :
    letI := GrpObj.ofRepresentableBy X F α
    (α.homEquiv (f * g) : F.obj (op T)) = (α.homEquiv f : F.obj (op T)) * α.homEquiv g := by
  let := GrpObj.ofRepresentableBy X F α
  rw [Hom.mul_def]
  change α.homEquiv (lift f g ≫ α.homEquiv.symm (_ * _)) = _
  rw [α.homEquiv_comp, Equiv.apply_symm_apply]
  change (F.map (lift f g).op).hom (_ * _) = _
  rw [map_mul]
  change (F ⋙ forget GrpCat).map (lift f g).op (α.homEquiv (fst X X)) *
    (F ⋙ forget GrpCat).map (lift f g).op (α.homEquiv (snd X X)) = _
  rw [← α.homEquiv_comp, ← α.homEquiv_comp, lift_fst, lift_snd]

open scoped MonObj in
/-- For the group law `RepOn.grpObj` on `J`, the descent bijection of `RepOn.compatEquiv` sends
sums of compatible elements to products. -/
private theorem RepOn.compatEquiv_add (T : Over S)
    (z₁ z₂ : {z : G.obj (op (prodY Y T)) // IsCompat Y (G ⋙ forget AddCommGrpCat) T z}) :
    letI := R.grpObj Y
    R.compatEquiv Y T ⟨z₁.1 + z₂.1, (compatSubgroup Y G T).add_mem z₁.2 z₂.2⟩ =
      R.compatEquiv Y T z₁ * R.compatEquiv Y T z₂ := by
  let := R.grpObj Y
  apply (R.compatEquiv Y T).symm.injective
  rw [Equiv.symm_apply_apply]
  have h := representableBy_homEquiv_mul J (compatFunctor Y G)
    { homEquiv := fun {T} =>
        ((R.compatEquiv Y T).symm.trans (Equiv.refl _) : (T ⟶ J) ≃ _)
      homEquiv_comp := fun {T' T} h j => by
        apply (R.compatEquiv Y T').injective
        change R.compatEquiv Y T' ((R.compatEquiv Y T').symm (h ≫ j)) =
          R.compatEquiv Y T' ⟨_, isCompat_map Y _ h _ ((R.compatEquiv Y T).symm j).2⟩
        rw [Equiv.apply_symm_apply, R.compatEquiv_naturality, Equiv.apply_symm_apply] }
    (R.compatEquiv Y T z₁) (R.compatEquiv Y T z₂)
  change ((R.compatEquiv Y T).symm _ : Multiplicative (compatSubgroup Y G T)) = _ at h
  apply Subtype.ext
  rw [show (R.compatEquiv Y T).symm (R.compatEquiv Y T z₁ * R.compatEquiv Y T z₂) =
    (Multiplicative.toAdd ((R.compatEquiv Y T).symm (R.compatEquiv Y T z₁ * R.compatEquiv Y T z₂) :
      Multiplicative (compatSubgroup Y G T)) : compatSubgroup Y G T) from rfl, h]
  change z₁.1 + z₂.1 = ((R.compatEquiv Y T).symm (R.compatEquiv Y T z₁)).1 +
    ((R.compatEquiv Y T).symm (R.compatEquiv Y T z₂)).1
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

end SheafifyGroup

section SheafCondition

/-! ### Extending a representation to all `S`-schemes -/

variable {S : Scheme.{u}} (Y : Over S) {G : (Over S)ᵒᵖ ⥤ Type u} {J : Over S}

private theorem isCompat_map_fst (T : Over S) (x : G.obj (op T)) :
    IsCompat Y G T (G.map (prodYFst Y T).op x) := by
  intro Z g₁ g₂ hg
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    hg]

/-- The comparison of `G(T)` with the compatible elements of `G(T ×_S Y)`. -/
private noncomputable def toCompat (T : Over S) (x : G.obj (op T)) :
    {z : G.obj (op (prodY Y T)) // IsCompat Y G T z} :=
  ⟨G.map (prodYFst Y T).op x, isCompat_map_fst Y T x⟩

private theorem toCompat_naturality {T' T : Over S} (h : T' ⟶ T) (x : G.obj (op T)) :
    (⟨G.map (prodYMap Y h).op (toCompat Y T x).1, isCompat_map Y G h _ (toCompat Y T x).2⟩ :
      {z // IsCompat Y G T' z}) = toCompat Y T' (G.map h.op x) := by
  apply Subtype.ext
  simp only [toCompat]
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    prodYLift_fst]

variable [Flat Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom] (R : RepOn Y G J)

/-- **A representation on the `S`-schemes over `Y` extends to all `S`-schemes**, as the morphism
of functors `G ⟶ J(-)` sending `x ∈ G(T)` to the descent of its image in `J(T ×_S Y)`. -/
private noncomputable def RepOn.toYoneda : G ⟶ yoneda.obj J where
  app T := TypeCat.ofHom fun x => R.compatEquiv Y T.unop (toCompat Y T.unop x)
  naturality T T' h := by
    ext x
    change R.compatEquiv Y T'.unop (toCompat Y T'.unop (G.map h x)) =
      h.unop ≫ R.compatEquiv Y T.unop (toCompat Y T.unop x)
    rw [← R.compatEquiv_naturality Y h.unop, toCompat_naturality]
    rfl

private theorem RepOn.toYoneda_app (T : Over S) (hT : Nonempty (T ⟶ Y)) (x : G.obj (op T)) :
    (R.toYoneda Y).app (op T) x = R.equiv T hT x := by
  apply prodYFst_cancel Y
  change prodYFst Y T ≫ R.descend Y T _ (isCompat_map_fst Y T x) = _
  rw [R.prodYFst_descend]
  exact R.naturality' Y _ _ hT x

private theorem RepOn.isIso_toYoneda_app (T : Over S) (hT : Nonempty (T ⟶ Y)) :
    IsIso ((R.toYoneda Y).app (op T)) := by
  rw [isIso_iff_bijective]
  convert (R.equiv T hT).bijective
  exact funext (R.toYoneda_app Y T hT)

/-- If `G` satisfies descent along `T ×_S Y ⟶ T` for the `T` admitting a morphism to `Y'`, a
representation on the `S`-schemes over `Y` is one on the `S`-schemes over `Y'`. -/
private noncomputable def RepOn.ofSheafCondition (Y' : Over S)
    (hsh : ∀ T : Over S, Nonempty (T ⟶ Y') → Function.Bijective (toCompat Y (G := G) T)) :
    RepOn Y' G J where
  equiv T hT := (Equiv.ofBijective _ (hsh T hT)).trans (R.compatEquiv Y T)
  naturality {Z T} g hT x := by
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
    rw [← R.compatEquiv_naturality Y g, toCompat_naturality]

end SheafCondition

section SheafConditionGroup

/-! ### Additivity of the extended representation -/

open scoped MonObj in
/-- If the bijections of a representation of a group-valued presheaf are multiplicative, so is
its extension `RepOn.toYoneda` to all `S`-schemes. -/
private theorem RepOn.toYoneda_add {S : Scheme.{u}} (Y : Over S) [Flat Y.hom] [Surjective Y.hom]
    [QuasiCompact Y.hom] {G' : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {J : Over S} [GrpObj J]
    (R' : RepOn Y (G' ⋙ forget AddCommGrpCat) J)
    (hR : ∀ (T : Over S) (hT : Nonempty (T ⟶ Y)) (x y : G'.obj (op T)),
      R'.equiv T hT (x + y) =
        @HMul.hMul (T ⟶ J) (T ⟶ J) (T ⟶ J) _ (R'.equiv T hT x) (R'.equiv T hT y))
    (T : (Over S)ᵒᵖ) (x y : G'.obj T) :
    (R'.toYoneda Y).app T (x + y) =
      @HMul.hMul (T.unop ⟶ J) (T.unop ⟶ J) (T.unop ⟶ J) _
        ((R'.toYoneda Y).app T x) ((R'.toYoneda Y).app T y) := by
  obtain ⟨T⟩ := T
  have nat : ∀ z : G'.obj (op T), prodYFst Y T ≫ (R'.toYoneda Y).app (op T) z =
      R'.equiv (prodY Y T) ⟨prodYSnd Y T⟩ ((G'.map (prodYFst Y T).op).hom z) := by
    intro z
    rw [← R'.toYoneda_app Y _ ⟨prodYSnd Y T⟩]
    have h := NatTrans.naturality_apply (R'.toYoneda Y) (prodYFst Y T).op z
    exact h.symm
  apply prodYFst_cancel Y
  rw [MonObj.comp_mul, nat, nat, nat, map_add, hR]

end SheafConditionGroup

open scoped MonObj in
/-- **A representation of `P⁰_C` on the `k`-schemes with a `C`-point by an abelian variety, with
multiplicative bijections, is a Jacobian.** -/
private theorem nonempty_jacobian_of_repOn {k : Type u} [Field k] {C : Scheme.{u}}
    {f : C ⟶ Spec (.of k)} [IsSmoothProjectiveCurve k f] (J : Over (Spec (.of k)))
    [GrpObj J] (hJ : IsAbelianVariety k J)
    (R : RepOn (Over.mk f) (relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) J)
    (hR : ∀ (T : Over (Spec (.of k))) (hT : Nonempty (T ⟶ Over.mk f))
      (x y : (relativePicZeroFunctor k f).obj (op T)),
      R.equiv T hT (x + y) =
        @HMul.hMul (T ⟶ J) (T ⟶ J) (T ⟶ J) _ (R.equiv T hT x) (R.equiv T hT y)) :
    Nonempty (Jacobian k f) :=
  have : Flat (Over.mk f).hom := inferInstanceAs (Flat f)
  have : Surjective (Over.mk f).hom := inferInstanceAs (Surjective f)
  have : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  ⟨⟨J, hJ, R.toYoneda _, RepOn.toYoneda_add _ R hR, R.isIso_toYoneda_app _⟩⟩

open relativePicZeroFunctor

section FieldExtension

/-! ### Field extensions -/

private theorem specMap_comp_specMap (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    specMap L M ≫ specMap K L = specMap K M := by
  rw [specMap, specMap, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- **Geometric integrality descends along an algebraic field extension.** -/
public theorem geometricallyIntegral_of_pullback_specMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (h : GeometricallyIntegral (pullback.snd f (specMap k L))) : GeometricallyIntegral f := by
  rw [geometricallyIntegral_iff_isIntegral_pullback]
  intro K _ _
  let M := AlgebraicClosure K
  let φ : L →ₐ[k] M := IsAlgClosed.lift
  let : Algebra L M := φ.toRingHom.toAlgebra
  have : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hM : IsIntegral (pullback f (specMap k M)) := by
    have := (geometricallyIntegral_iff_isIntegral_pullback _).1 h M
    exact IsIntegral.of_isIso ((pullbackLeftPullbackSndIso f (specMap k L) (specMap L M)).hom ≫
      (pullback.congrHom rfl (specMap_comp_specMap k L M)).hom)
  have e : pullback (pullback.snd f (specMap k K)) (specMap K M) ≅ pullback f (specMap k M) :=
    pullbackLeftPullbackSndIso f (specMap k K) (specMap K M) ≪≫
      pullback.congrHom rfl (specMap_comp_specMap k K M)
  have : IsIntegral (pullback (pullback.snd f (specMap k K)) (specMap K M)) :=
    IsIntegral.of_isIso e.inv
  have : IsSchemeTheoreticallyDominant (specMap K M) := .of_isDominant _
  have : IsReduced (pullback f (specMap k K) : Scheme.{u}) :=
    IsSchemeTheoreticallyDominant.isReduced (pullback.fst (pullback.snd f (specMap k K))
      (specMap K M))
  have : IrreducibleSpace (pullback f (specMap k K) : Scheme.{u}) :=
    Function.Surjective.irreducibleSpace
      (pullback.fst (pullback.snd f (specMap k K)) (specMap K M)).continuous
      (pullback.fst (pullback.snd f (specMap k K)) (specMap K M)).surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end FieldExtension

namespace relativePicZeroFunctor

section RelBase

/-! ### `C ×_k T` as a curve over `T` -/

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (T : Over (Spec (.of k)))

open Stacks.RigidifiedPicard Stacks.Picard

/-- The terminal `T`-scheme. -/
private noncomputable abbrev relTop : Over T.left := Over.mk (𝟙 T.left)

/-- The structure morphism of a `T`-scheme, as a morphism to the terminal `T`-scheme. -/
private noncomputable abbrev relToTop (U : Over T.left) : U ⟶ relTop T :=
  Over.homMk U.hom (Category.comp_id _)

/-- The structure morphism of a `T`-scheme, as a morphism of `k`-schemes to `T`. -/
private noncomputable abbrev relToT (U : Over T.left) : forgetBase T U ⟶ T :=
  Over.homMk U.hom rfl

/-- `(C ×_k T) ×_T T ≅ C ×_k T`. -/
private noncomputable abbrev relTopHom : bc (bcProj f T) (relTop T) ⟶ bc f T :=
  pullback.fst (bcProj f T) (relTop T).hom

omit [IsSmoothProjectiveCurve k f] in
private theorem bcMap_relToTop (U : Over T.left) :
    bcMap (bcProj f T) (relToTop T U) ≫ relTopHom f T =
      (bcForgetIso f T U).hom ≫ bcMap f (relToT T U) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcMap_fst, bcForgetIso_hom_fst]
  · simp only [Category.assoc, bcMap_snd, Over.homMk_left]
    rw [show relTopHom f T ≫ pullback.snd f T.hom = bcProj (bcProj f T) (relTop T) from
      (pullback.condition (f := bcProj f T) (g := (relTop T).hom)).trans (Category.comp_id _),
      bcMap_snd]
    simp only [bcForgetIso_hom_snd_assoc, Over.homMk_left]

omit [IsSmoothProjectiveCurve k f] in
private theorem bcSection_relTopHom (c : T ⟶ Over.mk f) :
    bcSection (bcProj f T) (pointSection f T c) (pointSection_bcProj f T c) (relTop T) ≫
      relTopHom f T = pointSection f T c :=
  (bcSection_comp_fst _ _ _ _).trans (Category.id_comp _)

end RelBase

end relativePicZeroFunctor

section SheafPicZero

/-! ### Descent of `P⁰_C` along a flat covering, at the pointed `k`-schemes -/

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

open Stacks.RigidifiedPicard Stacks.Picard

private theorem pointSection_degreeZeroMap {T U : Over (Spec (.of k))} (g : T ⟶ U)
    (c : U ⟶ Over.mk f)
    (z : degreeZero f U) (hz : smallSchemePullbackClassHom (pointSection f U c) z.1 = 0) :
    smallSchemePullbackClassHom (pointSection f T (g ≫ c)) (degreeZeroMap f g z).1 = 0 := by
  change smallSchemePullbackClassHom (pointSection f T (g ≫ c))
    (smallSchemePullbackClassHom (bcMap f g) z.1) = 0
  rw [smallSchemePullbackClassHom_comp, pointSection_bcMap, ← smallSchemePullbackClassHom_comp, hz,
    map_zero]

variable {S' : Scheme.{u}} (π : S' ⟶ Spec (.of k)) [Flat π] [Surjective π] [QuasiCompact π]

/-- The covering `T ×_k S' ⟶ T`, as a `T`-scheme. -/
private noncomputable abbrev relCover (T : Over (Spec (.of k))) : Over T.left :=
  Over.mk (prodYFst (Over.mk π) T).left

omit [IsSmoothProjectiveCurve k f] in
private theorem relCover_mem (T : Over (Spec (.of k))) :
    Presieve.ofArrows (fun _ : PUnit.{u + 2} => bc (bcProj f T) (relCover π T))
      (fun _ => bcMap (bcProj f T) (relToTop T (relCover π T))) ∈
      Scheme.fpqcPrecoverage.{u} (bc (bcProj f T) (relTop T)) := by
  have hb := bcMap_isPullback_proj (bcProj f T) (relToTop T (relCover π T))
  have : Flat (relToTop T (relCover π T)).left :=
    inferInstanceAs (Flat (pullback.fst T.hom π))
  have : Surjective (relToTop T (relCover π T)).left :=
    inferInstanceAs (Surjective (pullback.fst T.hom π))
  have : QuasiCompact (relToTop T (relCover π T)).left :=
    inferInstanceAs (QuasiCompact (pullback.fst T.hom π))
  have : Flat (bcMap (bcProj f T) (relToTop T (relCover π T))) :=
    MorphismProperty.of_isPullback (P := @Flat) hb.flip ‹_›
  have : Surjective (bcMap (bcProj f T) (relToTop T (relCover π T))) :=
    MorphismProperty.of_isPullback (P := @Surjective) hb.flip ‹_›
  have : QuasiCompact (bcMap (bcProj f T) (relToTop T (relCover π T))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hb.flip ‹_›
  rw [Presieve.ofArrows_pUnit]
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

omit [IsSmoothProjectiveCurve k f] in
private theorem relCover_mem' (T : Over (Spec (.of k))) :
    Presieve.ofArrows (fun _ : PUnit.{1} => bc (bcProj f T) (relCover π T))
      (fun _ => bcMap (bcProj f T) (relToTop T (relCover π T))) ∈
      Scheme.fpqcPrecoverage.{u} (bc (bcProj f T) (relTop T)) := by
  have h := relCover_mem f π T
  rw [Presieve.ofArrows_pUnit] at h ⊢
  exact h

omit [IsSmoothProjectiveCurve k f] in
private theorem isIso_relTopHom (T : Over (Spec (.of k))) : IsIso (relTopHom f T) := by
  have : IsIso (relTop T).hom := inferInstanceAs (IsIso (𝟙 T.left))
  exact inferInstanceAs (IsIso (pullback.fst (bcProj f T) (relTop T).hom))

private theorem schemePullbackClass_injective_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    Function.Injective (schemePullbackClass e) := by
  intro a b h
  have := congrArg (schemePullbackClass (inv e)) h
  rwa [schemePullbackClass_comp, schemePullbackClass_comp, IsIso.inv_hom_id,
    schemePullbackClass_id, schemePullbackClass_id] at this

/-- **Separatedness of `P⁰_C`** at a pointed `k`-scheme, for a flat covering. -/
private theorem injective_toCompat (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) :
    Function.Injective (toCompat (Over.mk π)
      (G := relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) T) := by
  intro x x' hxx'
  induction x using QuotientAddGroup.induction_on with | H z => ?_
  induction x' using QuotientAddGroup.induction_on with | H z' => ?_
  rw [← mk_rigidify f T c z, ← mk_rigidify f T c z'] at hxx' ⊢
  set zr := rigidify f T c z
  set zr' := rigidify f T c z'
  have hzr := pointSection_rigidify f T c z
  have hzr' := pointSection_rigidify f T c z'
  have h1 := congrArg Subtype.val hxx'
  change (QuotientAddGroup.mk (degreeZeroMap f (prodYFst (Over.mk π) T) zr) :
      degreeZero f _ ⧸ baseClasses f _) =
    QuotientAddGroup.mk (degreeZeroMap f (prodYFst (Over.mk π) T) zr') at h1
  have hpz := eq_of_mk_eq_of_pointSection_eq_zero f _ (prodYFst (Over.mk π) T ≫ c) h1
    (pointSection_degreeZeroMap f _ c zr hzr) (pointSection_degreeZeroMap f _ c zr' hzr')
  have := isIso_relTopHom f T
  have key := eq_of_section_eq (bcProj f T) (pointSection f T c) (pointSection_bcProj f T c)
    (isIso_c_bcProj_bcProj f T) (g := fun _ : PUnit.{1} => relToTop T (relCover π T))
    (relCover_mem' f π T)
    (schemePullbackClass (relTopHom f T) (smallEquiv (bc f T) zr.1))
    (schemePullbackClass (relTopHom f T) (smallEquiv (bc f T) zr'.1))
    (by
      rw [schemePullbackClass_comp, schemePullbackClass_comp, bcSection_relTopHom,
        ← smallEquiv_smallSchemePullbackClassHom, ← smallEquiv_smallSchemePullbackClassHom, hzr,
        hzr'])
    (fun _ => by
      rw [schemePullbackClass_comp, schemePullbackClass_comp, bcMap_relToTop,
        ← schemePullbackClass_comp, ← schemePullbackClass_comp,
        ← smallEquiv_smallSchemePullbackClassHom (bcMap f (relToT T (relCover π T))) zr.1,
        ← smallEquiv_smallSchemePullbackClassHom (bcMap f (relToT T (relCover π T))) zr'.1]
      exact congrArg (fun w => schemePullbackClass (bcForgetIso f T (relCover π T)).hom
        (smallEquiv.{u} _ w)) (congrArg Subtype.val hpz))
  have h2 := (smallEquiv (bc f T)).injective (schemePullbackClass_injective_of_isIso _ key)
  rw [show zr = zr' from Subtype.ext h2]

/-- **Gluing for `P⁰_C`** at a pointed `k`-scheme, for a flat covering. -/
private theorem surjective_toCompat (T : Over (Spec (.of k))) (c : T ⟶ Over.mk f) :
    Function.Surjective (toCompat (Over.mk π)
      (G := relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) T) := by
  rintro ⟨ζ, hζ⟩
  induction ζ using QuotientAddGroup.induction_on with | H z' => ?_
  let U := relCover π T
  let z'' : degreeZero f (forgetBase T U) := z'
  let c' : forgetBase T U ⟶ Over.mk f := forgetBasePoint f T c U
  let zr := rigidify f _ c' z''
  have hzr : smallSchemePullbackClassHom (pointSection f _ c') zr.1 = 0 :=
    pointSection_rigidify f _ c' z''
  have hmk : (QuotientAddGroup.mk zr : degreeZero f _ ⧸ baseClasses f _) =
      QuotientAddGroup.mk z'' :=
    mk_rigidify f _ c' z''
  let x := schemePullbackClass (bcForgetIso f T U).hom (smallEquiv (bc f (forgetBase T U)) zr.1)
  have hx0 : schemePullbackClass
      (bcSection (bcProj f T) (pointSection f T c) (pointSection_bcProj f T c) U) x = 0 := by
    have h := smallEquiv_smallSchemePullbackClassHom (pointSection f _ c') zr.1
    rw [hzr, map_zero] at h
    rw [schemePullbackClass_comp, bcSection_bcForgetIso]
    exact h.symm
  have hagree : ∀ (V : Over T.left) (i j : PUnit.{u + 2}) (a : V ⟶ U) (b : V ⟶ U),
      a ≫ relToTop T U = b ≫ relToTop T U →
      schemePullbackClass (bcMap (bcProj f T) a) x =
        schemePullbackClass (bcMap (bcProj f T) b) x := by
    intro V _ _ a b _
    have hab : forgetBaseMap T a ≫ relToT T U = forgetBaseMap T b ≫ relToT T U := by
      ext1
      exact (Over.w a).trans (Over.w b).symm
    have hcomp : (QuotientAddGroup.mk (degreeZeroMap f (forgetBaseMap T a) z'') :
        degreeZero f _ ⧸ baseClasses f _) =
        QuotientAddGroup.mk (degreeZeroMap f (forgetBaseMap T b) z'') :=
      hζ (forgetBaseMap T a) (forgetBaseMap T b) hab
    have hca : forgetBaseMap T b ≫ c' = forgetBaseMap T a ≫ c' := by
      ext1
      change b.left ≫ (U.hom ≫ c.left) = a.left ≫ (U.hom ≫ c.left)
      rw [← Category.assoc, ← Category.assoc, Over.w a, Over.w b]
    have hra := pointSection_degreeZeroMap f (forgetBaseMap T a) c' zr hzr
    have hrb := pointSection_degreeZeroMap f (forgetBaseMap T b) c' zr hzr
    rw [hca] at hrb
    have hcomp' : (QuotientAddGroup.mk (degreeZeroMap f (forgetBaseMap T a) zr) :
        degreeZero f _ ⧸ baseClasses f _) =
        QuotientAddGroup.mk (degreeZeroMap f (forgetBaseMap T b) zr) := by
      rw [← map_mk, ← map_mk, hmk]
      exact hcomp
    have heq := eq_of_mk_eq_of_pointSection_eq_zero f _ (forgetBaseMap T a ≫ c') hcomp' hra hrb
    rw [schemePullbackClass_comp, schemePullbackClass_comp, bcMap_bcForgetIso, bcMap_bcForgetIso,
      ← schemePullbackClass_comp, ← schemePullbackClass_comp,
      ← smallEquiv_smallSchemePullbackClassHom (bcMap f (forgetBaseMap T a)) zr.1,
      ← smallEquiv_smallSchemePullbackClassHom (bcMap f (forgetBaseMap T b)) zr.1]
    exact congrArg (fun w => schemePullbackClass (bcForgetIso f T V).hom (smallEquiv.{u} _ w))
      (congrArg Subtype.val heq)
  obtain ⟨w, hw⟩ := exists_glue (bcProj f T) (pointSection f T c) (pointSection_bcProj f T c)
    (isIso_c_bcProj_bcProj f T) (g := fun _ : PUnit.{u + 2} => relToTop T U) (relCover_mem f π T)
    (fun _ => x) (fun _ => hx0) hagree
  have := isIso_relTopHom f T
  let z₀ := (smallEquiv (bc f T)).symm (schemePullbackClass (inv (relTopHom f T)) w)
  have e : bcMap (bcProj f T) (relToTop T U) =
      (bcForgetIso f T U).hom ≫ bcMap f (relToT T U) ≫ inv (relTopHom f T) := by
    rw [← Category.assoc, ← bcMap_relToTop, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hz₀ : smallSchemePullbackClassHom (bcMap f (relToT T U)) z₀ = zr.1 := by
    apply (smallEquiv.{u} _).injective
    apply schemePullbackClass_injective_of_isIso (bcForgetIso f T U).hom
    have h1 := hw PUnit.unit
    rw [e, ← schemePullbackClass_comp, ← schemePullbackClass_comp] at h1
    rw [smallEquiv_smallSchemePullbackClassHom, AddEquiv.apply_symm_apply]
    exact h1
  have : Surjective (relToT T U).left := inferInstanceAs (Surjective (pullback.fst T.hom π))
  have hdeg : z₀ ∈ degreeZero f T := by
    rw [AddMonoidHom.mem_ker]
    funext t
    obtain ⟨t', rfl⟩ := (relToT T U).left.surjective t
    have h := congrFun (degree_smallSchemePullbackClassHom_bcMap f
        (topologicalKrullDim_fiber_le_one f) (relToT T U) z₀) t'
    rw [hz₀, AddMonoidHom.mem_ker.1 zr.2] at h
    exact h.symm
  refine ⟨QuotientAddGroup.mk ⟨z₀, hdeg⟩, Subtype.ext ?_⟩
  change (QuotientAddGroup.mk (degreeZeroMap f (relToT T U) ⟨z₀, hdeg⟩) :
      degreeZero f _ ⧸ baseClasses f _) =
    QuotientAddGroup.mk z''
  rw [← hmk]
  congr 1
  exact Subtype.ext hz₀

end SheafPicZero

section RepConversion

/-! ### From a representation on `X`-schemes to the data of the descent theorem -/

variable {S X : Scheme.{u}} (f : X ⟶ S) (V : Over X) (G : (Over S)ᵒᵖ ⥤ Type u)
  (Ψ : yoneda.obj V ≅ (Over.map f).op ⋙ G)

/-- An `S`-scheme with an `X`-structure `x` is `(Over.map f).obj` of the `X`-scheme `x`. -/
private noncomputable def overMapIso {W : Over S} (x : W ⟶ Over.mk f) :
    W ≅ (Over.map f).obj (Over.mk x.left) :=
  Over.isoMk (Iso.refl _) (by simpa using Over.w x)

/-- Morphisms to `V` over a fixed `X`-structure, as morphisms of `X`-schemes. -/
private noncomputable def overHomEquiv (W : Over S) (x : W ⟶ Over.mk f) :
    {a : W ⟶ (Over.map f).obj V // a ≫ structureMap f V = x} ≃ (Over.mk x.left ⟶ V) where
  toFun a := Over.homMk a.1.left (congrArg CommaMorphism.left a.2)
  invFun b := ⟨Over.homMk b.left (by
      change b.left ≫ V.hom ≫ f = W.hom
      rw [← Category.assoc, Over.w b]
      exact Over.w x), by ext1; exact Over.w b⟩
  left_inv a := by ext1; rfl
  right_inv b := by ext1; rfl

/-- The bijection of a representation at an `S`-scheme with an `X`-structure. -/
private noncomputable def repEquiv (W : Over S) (x : W ⟶ Over.mk f) :
    {a : W ⟶ (Over.map f).obj V // a ≫ structureMap f V = x} ≃ G.obj (op W) :=
  (overHomEquiv f V W x).trans ((Ψ.app (op (Over.mk x.left))).toEquiv.trans
    (G.mapIso (overMapIso f x).op).toEquiv)

private theorem repEquiv_congr (W : Over S) {x x' : W ⟶ Over.mk f} (h : x = x')
    (a : W ⟶ (Over.map f).obj V) (ha : a ≫ structureMap f V = x)
    (ha' : a ≫ structureMap f V = x') :
    repEquiv f V G Ψ W x ⟨a, ha⟩ = repEquiv f V G Ψ W x' ⟨a, ha'⟩ := by
  subst h; rfl

/-- The map `Θ` of a representation. -/
private noncomputable def repTheta (W : Over S) (a : W ⟶ (Over.map f).obj V) : G.obj (op W) :=
  repEquiv f V G Ψ W (a ≫ structureMap f V) ⟨a, rfl⟩

private theorem repTheta_naturality {W' W : Over S} (h : W' ⟶ W) (a : W ⟶ (Over.map f).obj V) :
    repTheta f V G Ψ W' (h ≫ a) = G.map h.op (repTheta f V G Ψ W a) := by
  let hU : Over.mk (h ≫ a ≫ structureMap f V).left ⟶ Over.mk (a ≫ structureMap f V).left :=
    Over.homMk h.left (by simp)
  have e1 : overHomEquiv f V W' (h ≫ a ≫ structureMap f V) ⟨h ≫ a, (Category.assoc _ _ _)⟩ =
      hU ≫ overHomEquiv f V W (a ≫ structureMap f V) ⟨a, rfl⟩ := by
    ext1; rfl
  have e2 : (overMapIso f (h ≫ a ≫ structureMap f V)).hom ≫ (Over.map f).map hU =
      h ≫ (overMapIso f (a ≫ structureMap f V)).hom := by
    ext1; simp [overMapIso]; rfl
  have hnat : Ψ.hom.app (op (Over.mk (h ≫ a ≫ structureMap f V).left))
      (hU ≫ overHomEquiv f V W (a ≫ structureMap f V) ⟨a, rfl⟩) =
      G.map ((Over.map f).map hU).op
        (Ψ.hom.app (op (Over.mk (a ≫ structureMap f V).left))
          (overHomEquiv f V W (a ≫ structureMap f V) ⟨a, rfl⟩)) :=
    NatTrans.naturality_apply Ψ.hom hU.op _
  unfold repTheta
  rw [repEquiv_congr f V G Ψ W' (Category.assoc _ _ _) (h ≫ a) rfl (Category.assoc _ _ _)]
  change G.map (overMapIso f (h ≫ a ≫ structureMap f V)).hom.op
      (Ψ.hom.app (op (Over.mk (h ≫ a ≫ structureMap f V).left))
        (overHomEquiv f V W' (h ≫ a ≫ structureMap f V) ⟨h ≫ a, Category.assoc _ _ _⟩)) =
    G.map h.op (G.map (overMapIso f (a ≫ structureMap f V)).hom.op
      (Ψ.hom.app (op (Over.mk (a ≫ structureMap f V).left))
        (overHomEquiv f V W (a ≫ structureMap f V) ⟨a, rfl⟩)))
  rw [e1, hnat, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
    ← op_comp, e2]

private theorem repTheta_existsUnique (W : Over S) (x : W ⟶ Over.mk f) (y : G.obj (op W)) :
    ∃! a : W ⟶ (Over.map f).obj V, a ≫ structureMap f V = x ∧ repTheta f V G Ψ W a = y := by
  refine ⟨((repEquiv f V G Ψ W x).symm y).1, ⟨((repEquiv f V G Ψ W x).symm y).2, ?_⟩, ?_⟩
  · rw [repTheta, repEquiv_congr f V G Ψ W ((repEquiv f V G Ψ W x).symm y).2 _ rfl
      ((repEquiv f V G Ψ W x).symm y).2]
    exact Equiv.apply_symm_apply _ y
  · rintro a ⟨ha, hy⟩
    rw [repTheta, repEquiv_congr f V G Ψ W ha a rfl ha] at hy
    exact congrArg Subtype.val ((Equiv.symm_apply_eq _).2 hy.symm).symm

end RepConversion

namespace relativePicZeroFunctor

section BaseCurve

/-! ### The curve `C_E` over a field extension `E` -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (E : Type u) [Field E] [Algebra k E]

open Stacks.RigidifiedPicard

/-- **A curve has a point over a finite extension**: the residue field of a closed point. -/
private theorem exists_finite_point : ∃ (E : Type u) (_ : Field E) (_ : Algebra k E)
    (_ : FiniteDimensional k E), Nonempty (Over.mk (specMap k E) ⟶ Over.mk f) := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).1 inferInstance
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := C) isClosed_univ
    ⟨(inferInstance : Nonempty C).some, trivial⟩
  let φ : CommRingCat.of k ⟶ C.residueField x := Spec.preimage (C.fromSpecResidueField x ≫ f)
  let : Algebra k (C.residueField x) := φ.hom.toAlgebra
  have hspec : specMap k (C.residueField x) = C.fromSpecResidueField x ≫ f :=
    Spec.map_preimage _
  have : IsClosedImmersion (C.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : LocallyOfFiniteType (C.fromSpecResidueField x) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp inferInstance).2
  have hcomp : LocallyOfFiniteType (C.fromSpecResidueField x ≫ f) := inferInstance
  rw [← hspec, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (C.residueField x) := hcomp
  have : FiniteDimensional k (C.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  exact ⟨C.residueField x, inferInstance, inferInstance, this,
    ⟨Over.homMk (C.fromSpecResidueField x) hspec.symm⟩⟩

end BaseCurve

section PointedTransport

/-! ### The rigidified `Pic⁰` of `C_E` at a point of `C_E` as Faltings' `P⁰_C` -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f] (E : Type u) [Field E] [Algebra k E]
  (c₀ : Over.mk (specMap k E) ⟶ Over.mk f)

open Stacks.RigidifiedPicard Stacks.Picard

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- The open chart subfunctor of the rigidified `Pic⁰` of `C_E` attached to a class `θ`. -/
private noncomputable abbrev chartE (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E)))) :=
  cohomologySubfunctorZero (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
      (pointSection f _ c₀)
    (pointSection_bcProj f _ c₀)
        (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ

/-- The condition of [Stacks, Tag 0B9Q] (2)(c): the translates of the chart by `E`-points meet
every field-valued point. -/
private def TranslatesMeet (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E)))) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra E K]
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (fieldExtensionPoint E K))),
    ∃ r : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of E))))),
      (rigidified k f E c₀).map (Over.homMk (fieldExtensionPoint E K).hom).op r * x ∈
        (chartE k f E c₀ θ).obj (op (fieldExtensionPoint E K))

/-- **[Stacks, Tag 0B9Q] for the rigidified `Pic⁰` of `C_E`**: given a class `θ` of degree the
genus whose chart translates meet every field-valued point, the functor is represented by a smooth
group scheme. -/
private theorem exists_grp_iso_rigidified
    (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E))))
    (hθ : ∀ s, relativeInvertibleDegreeHomAt (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ =
      genus (curveOver k f E))
    (hfield : TranslatesMeet k f E c₀ θ) :
    ∃ A : Grp (Over (Spec (.of E))), Nonempty (yonedaGrp.obj A ≅ rigidified k f E c₀) ∧
      Smooth A.X.hom := by
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  have := smooth_curveOver k f E
  have hproj := isProjectiveMorphism_curveOver k f E
  let HH : ∀ d : ℕ, Σ H : Over (Spec (.of E)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (curveOver k f E)) H d := fun d =>
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk (curveOver k f E)) hproj d).some
  obtain ⟨A, ⟨e⟩, hP⟩ := exists_grp_iso_functorZero (curveOver k f E)
      (topologicalKrullDim_fiber_curveOver_le_one k f E)
    (pointSection f _ c₀) (pointSection_bcProj f _ c₀)
        (isIso_c_bcProj_bcProj f (Over.mk (specMap k E)))
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ hθ (HH (genus (curveOver k f E))).2
    (fun T c => Stacks.WeilCohomology.cohomologyLocusDivisorExistence E (curveOver k f E) T c)
    (fun T Z Z' => Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness E
        (curveOver k f E) T Z Z')
    hfield
  let : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  exact ⟨A, ⟨e⟩, hP @Smooth (smooth_of_represents (curveOver k f E) (fun d => (HH d).1)
    (fun d => (HH d).2) (genus (curveOver k f E)))⟩

/-- **The Jacobian over `E`**, given a class `θ` of degree the genus whose chart translates meet
every field-valued point: an abelian variety over `E` representing `P⁰_C` on `E`-schemes. -/
private theorem exists_rep_of_translatesMeet
    (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E))))
    (hθ : ∀ s, relativeInvertibleDegreeHomAt (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ =
      genus (curveOver k f E))
    (hfield : TranslatesMeet k f E c₀ θ) :
    ∃ (V : Over (Spec (.of E))) (_ : GrpObj V) (_ : IsAbelianVariety E V),
      Nonempty (yoneda.obj V ≅
        (Over.map (specMap k E)).op ⋙ relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) := by
  obtain ⟨A, ⟨e⟩, _⟩ := exists_grp_iso_rigidified k f E c₀ θ hθ hfield
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  have := smooth_curveOver k f E
  have hAV := isAbelianVariety_of_iso_functorZero_field (curveOver k f E)
      (topologicalKrullDim_fiber_curveOver_le_one k f E)
    (pointSection f _ c₀) (pointSection_bcProj f _ c₀) e (topologicalKrullDim_curveOver k f E)
  exact ⟨A.X, inferInstance, hAV, ⟨representingIsoOfGrp A e ≪≫ rigidifiedIso k f E c₀⟩⟩

include c₀ in
/-- **A class of degree the genus** on `C_E`, from a point of `C_E`: `g` times the point. -/
private theorem exists_theta : ∃ θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E))),
    ∀ s, relativeInvertibleDegreeHomAt (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ =
      genus (curveOver k f E) := by
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  have := smooth_curveOver k f E
  have hσ := pointSection_bcProj f (Over.mk (specMap k E)) c₀
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections E (curveOver k f E)
  have := GenusOne.isEffectiveCartierDivisor (curveOver k f E) h0 _ hσ
  refine ⟨genus (curveOver k f E) • Stacks.Divisors.picardClass
    (Scheme.IdealSheafData.vanishingIdeal (⟨{GenusOne.point (pointSection f _ c₀)},
      GenusOne.isClosed_point (curveOver k f E) _ hσ⟩ : TopologicalSpace.Closeds _)), fun s => ?_⟩
  rw [relativeInvertibleDegreeHomAt_spec (curveOver k f E) (topologicalKrullDim_curveOver k f E),
    map_nsmul, invertibleCurveDegreeHom_divisorPicardClass_point E (curveOver k f E)
      (topologicalKrullDim_curveOver k f E) h0 _ hσ, nsmul_eq_mul, mul_one]

/-- **[Stacks, Tag 0B9Y]**: over a separably closed field the chart translates meet every
field-valued point. -/
private theorem translatesMeet_of_isSepClosed [IsSepClosed E]
    (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E))))
    (hθ : ∀ s, relativeInvertibleDegreeHomAt (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ =
      genus (curveOver k f E)) :
    TranslatesMeet k f E c₀ θ := by
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  have := smooth_curveOver k f E
  have := isCurve_curveOver k f E
  have hθ' : invertibleCurveDegreeHom E (curveOver k f E)
      (IsCurve.topologicalKrullDim_eq_one (k := E) (f := curveOver k f E)).le θ =
      genus (curveOver k f E) := by
    obtain ⟨s⟩ : Nonempty (Spec (.of E)) := inferInstance
    rw [← relativeInvertibleDegreeHomAt_spec (curveOver k f E) _
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ]
    exact hθ s
  intro K _ _ x
  exact exists_translate_mem_cohomologySubfunctorZero (curveOver k f E)
    (topologicalKrullDim_curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
        (pointSection f _ c₀)
    (pointSection_bcProj f _ c₀) θ
    (fun L _ _ c hc => Stacks.WeilCohomology.prescribedCohomologyTranslate_of_isSepClosed E
      (curveOver k f E) L c _ hc θ hθ') K x

open scoped CategoryTheory.MonObj in
/-- **Finitely many translates suffice** over a separably closed field: there is a finite set of
`E`-points whose chart translates meet every field-valued point. -/
private theorem exists_finite_translates [IsSepClosed E]
    (θ : Stacks.Picard.ofScheme (bc f (Over.mk (specMap k E))))
    (hθ : ∀ s, relativeInvertibleDegreeHomAt (curveOver k f E)
        (topologicalKrullDim_fiber_curveOver_le_one k f E) s θ =
      genus (curveOver k f E)) :
    ∃ R : Finset ((rigidified k f E c₀ ⋙ forget GrpCat).obj
        (op (Over.mk (𝟙 (Spec (.of E)))))),
      ∀ (K : Type u) [Field K] [Algebra E K]
        (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (fieldExtensionPoint E K))),
        ∃ r ∈ R, (rigidified k f E c₀).map (Over.homMk (fieldExtensionPoint E K).hom).op r * x ∈
          (chartE k f E c₀ θ).obj (op (fieldExtensionPoint E K)) := by
  classical
  have hfield := translatesMeet_of_isSepClosed k f E c₀ θ hθ
  obtain ⟨A, ⟨e⟩, _⟩ := exists_grp_iso_rigidified k f E c₀ θ hθ hfield
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := geometricallyIrreducible_curveOver k f E
  have := smooth_curveOver k f E
  have hproj := isProjectiveMorphism_curveOver k f E
  let HH : Σ H : Over (Spec (.of E)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (curveOver k f E)) H
        (genus (curveOver k f E)) :=
    (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
      (Over.mk (curveOver k f E)) hproj _).some
  obtain ⟨W, ⟨Rep⟩⟩ := exists_representableBy_cohomologySubfunctorZero (curveOver k f E)
    (topologicalKrullDim_fiber_curveOver_le_one k f E) (pointSection f _ c₀)
        (pointSection_bcProj f _ c₀)
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ HH.2 hθ
    (fun T c => Stacks.WeilCohomology.cohomologyLocusDivisorExistence E (curveOver k f E) T c)
    (fun T Z Z' => Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness E
        (curveOver k f E) T Z Z')
  have hopen := isOpenImmersion_presheaf_cohomologySubfunctorZero (curveOver k f E)
      (topologicalKrullDim_fiber_curveOver_le_one k f E)
    (pointSection f _ c₀) (pointSection_bcProj f _ c₀)
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ
  obtain ⟨Y, ⟨eY⟩⟩ : ∃ Y, Nonempty (yoneda.obj Y ≅ (chartE k f E c₀ θ).toFunctor) :=
    ⟨_, ⟨Functor.representableByEquiv Rep⟩⟩
  obtain ⟨j, _, hj⟩ := exists_isOpenImmersion_chart A e (chartE k f E c₀ θ) _
    eY hopen
  have hcov := exists_translate_mem_range A e (chartE k f E c₀ θ) _
    eY j hj hfield
  have hAV := isAbelianVariety_of_iso_functorZero_field (curveOver k f E)
      (topologicalKrullDim_fiber_curveOver_le_one k f E)
    (pointSection f _ c₀) (pointSection_bcProj f _ c₀) e (topologicalKrullDim_curveOver k f E)
  have : CompactSpace A.X.left := (quasiCompact_iff_compactSpace A.X.hom).1 inferInstance
  have hopen_r : ∀ r : Over.mk (𝟙 (Spec (.of E))) ⟶ A.X,
      IsOpen (Set.range (j ≫ grpTranslate A r).left) := fun r => by
    have : IsOpenImmersion (j ≫ grpTranslate A r).left := by
      rw [Over.comp_left]; infer_instance
    exact (j ≫ grpTranslate A r).left.isOpenEmbedding.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun r => Set.range (j ≫ grpTranslate A r).left) hopen_r
    (fun a _ => Set.mem_iUnion.2 (hcov a))
  refine ⟨t.image (fun r => (e.hom.app (op _)).hom r⁻¹), fun K _ _ x => ?_⟩
  let V := fieldExtensionPoint E K
  let ξ : V ⟶ A.X := (e.inv.app (op V)).hom x
  have hξ : (e.hom.app (op V)).hom ξ = x := by simp [ξ]
  let p : V.left := show PrimeSpectrum K from IsLocalRing.closedPoint K
  obtain ⟨r, hrt, hr⟩ : ∃ r ∈ t, ξ.left p ∈ Set.range (j ≫ grpTranslate A r).left := by
    obtain ⟨r, hrt, hr⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ξ.left p)))
    exact ⟨r, hrt, hr⟩
  have hsub : Subsingleton V.left := inferInstanceAs (Subsingleton (Spec (.of K)))
  have hrange : Set.range ξ.left ⊆ Set.range (j ≫ grpTranslate A r).left := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p]
    exact hr
  have : IsOpenImmersion (j ≫ grpTranslate A r).left := by
    rw [Over.comp_left]; infer_instance
  let ℓ := IsOpenImmersion.lift (j ≫ grpTranslate A r).left ξ.left hrange
  have hℓ : ℓ ≫ (j ≫ grpTranslate A r).left = ξ.left := IsOpenImmersion.lift_fac _ _ _
  let ℓ' : V ⟶ Y := Over.homMk ℓ (by
    have h1 := Over.w (j ≫ grpTranslate A r)
    have h2 := Over.w ξ
    rw [← h1, ← Category.assoc, hℓ, h2])
  have hℓ' : ℓ' ≫ j ≫ grpTranslate A r = ξ := by ext1; exact hℓ
  have h1 : ℓ' ≫ j = ξ ≫ grpTranslate A r⁻¹ := by
    rw [← hℓ', Category.assoc, Category.assoc, grpTranslate_comp_grpTranslate, inv_mul_cancel,
      grpTranslate_one, Category.comp_id]
  have h2 : ξ ≫ grpTranslate A r⁻¹ = (grpToBase V ≫ r⁻¹) * ξ := comp_grpTranslate A ξ r⁻¹
  have hmem : (representingIsoOfGrp A e).hom.app (op V) (ℓ' ≫ j) ∈
      (chartE k f E c₀ θ).obj (op V) := by
    have h3 : (representingIsoOfGrp A e).hom.app (op V) (ℓ' ≫ j) =
        (chartE k f E c₀ θ).ι.app (op V) (eY.hom.app (op V) ℓ') :=
      congrArg (fun φ => (ConcreteCategory.hom (φ.app (op V))) ℓ') hj
    rw [h3]
    exact (eY.hom.app (op V) ℓ').2
  have hval : (representingIsoOfGrp A e).hom.app (op V) (ℓ' ≫ j) =
      (rigidified k f E c₀).map (Over.homMk (fieldExtensionPoint E K).hom).op
        ((e.hom.app (op (Over.mk (𝟙 (Spec (.of E)))))).hom r⁻¹) * x := by
    rw [h1, h2]
    refine (map_mul (e.hom.app (op V)).hom
      (show (yonedaGrp.obj A).obj (op V) from grpToBase V ≫ r⁻¹)
      (show (yonedaGrp.obj A).obj (op V) from ξ)).trans ?_
    rw [hξ]
    congr 1
    have hn := congrArg (fun φ : (yonedaGrp.obj A).obj (op (Over.mk (𝟙 (Spec (.of E))))) ⟶
      (rigidified k f E c₀).obj (op V) => φ r⁻¹) (e.hom.naturality (grpToBase V).op)
    simp only [ConcreteCategory.comp_apply] at hn
    exact hn
  exact ⟨_, Finset.mem_image_of_mem _ hrt, hval ▸ hmem⟩

end PointedTransport

end relativePicZeroFunctor

section ChartTransport

/-! ### The chart condition is invariant under isomorphism -/

open Stacks.RigidifiedPicard Stacks.Picard AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- The condition "`Rπ_* ℒ` is invertible in degree `0`" is invariant under base change along an
isomorphism. -/
private theorem hasDerivedPushforwardRank_iff_of_isPullback {Y T Y' T' : Scheme.{u}}
    (π : Y ⟶ T) [Flat π] [IsProper π] (hfp : FinitePresentation π) {h : T' ⟶ T} [IsIso h]
    {π' : Y' ⟶ T'} {h' : Y' ⟶ Y} (hpb : IsPullback h' π' π h) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    HasDerivedPushforwardRank π L 0 1 ↔
      HasDerivedPushforwardRank π' ((Scheme.Modules.pullback h').obj L) 0 1 := by
  obtain ⟨U, hU⟩ := exists_opens_factorsThrough_iff_invertible_of_baseChange
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward π hfp L hL
  rw [← hU h π' h' hpb]
  have : IsIso (𝟙 Y) := IsIso.id _
  have : IsIso (𝟙 T) := IsIso.id _
  have h2 := hU (𝟙 T) π (𝟙 Y) (IsPullback.of_horiz_isIso ⟨by simp⟩)
  rw [hasDerivedPushforwardRank_congr ((Scheme.Modules.pullbackId Y).app L)] at h2
  refine Iff.trans h2.symm ?_
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨h ≫ g, by rw [Category.assoc, hg, Category.comp_id]⟩
  · rintro ⟨g, hg⟩
    exact ⟨inv h ≫ g, by rw [Category.assoc, hg, IsIso.inv_hom_id]⟩

end ChartTransport

section FiniteStage

/-! ### The translate condition over a finite extension -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

open Stacks.RigidifiedPicard Stacks.Picard AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- The degree on the fibres of `C_T ⟶ T` is natural in `T`. -/
private theorem relDeg_bcMap {T U : Over (Spec (.of k))} (g : T ⟶ U) (z : ofScheme (bc f U))
    (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T)
        (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) T)
        t (schemePullbackClass (bcMap f g) z) =
      relativeInvertibleDegreeHomAt (bcProj f U)
        (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) U)
            (g.left t) z := by
  have := congrFun (degree_smallSchemePullbackClassHom_bcMap f
      (topologicalKrullDim_fiber_le_one f) g
    ((smallEquiv.{u} _).symm z)) t
  rw [Function.comp_apply, degree_apply, degree_apply, smallEquiv_smallSchemePullbackClassHom,
    AddEquiv.apply_symm_apply] at this
  exact this

/-- **The chart condition descends along a morphism to a one-point base.** -/
private theorem hasInvertibleDirectImage_of_bcMap {T' T : Over (Spec (.of k))} (g : T' ⟶ T)
    (hT : Subsingleton T.left) (hT' : Nonempty T'.left) (z : ofScheme (bc f T))
    (h : HasInvertibleDirectImage f T' (schemePullbackClass (bcMap f g) z)) :
    HasInvertibleDirectImage f T z := by
  obtain ⟨U, hU⟩ := exists_opens_isCohomologyClass_iff f
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0 T z
  rw [← isCohomologyClass_zero_iff, hU] at h
  have h1 := hU T (𝟙 T)
  rw [bcMap_id, schemePullbackClass_id, isCohomologyClass_zero_iff] at h1
  rw [h1]
  obtain ⟨t'⟩ := hT'
  have ht : g.left t' ∈ (U : Set T.left) := h ⟨t', rfl⟩
  rintro _ ⟨t, rfl⟩
  rwa [Subsingleton.elim ((𝟙 T : T ⟶ T).left t) (g.left t')]

variable (E : Type u) [Field E] [Algebra k E] (c₀ : Over.mk (specMap k E) ⟶ Over.mk f)

/-- The class on `C ×_k U` of an element of the rigidified `Pic⁰` of `C_E` at an `E`-scheme
`U`. -/
private noncomputable def classE {U : Over (Spec (.of E))}
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) :
    ofScheme (bc f (forgetBase (Over.mk (specMap k E)) U)) :=
  schemePullbackClass (bcForgetIso f (Over.mk (specMap k E)) U).inv
    (classOfZero (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
        (pointSection f _ c₀) (pointSection_bcProj f _ c₀) x)

private theorem classE_mul {U : Over (Spec (.of E))}
    (x y : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) :
    classE k f E c₀ (x * y) = classE k f E c₀ x + classE k f E c₀ y := by
  rw [classE, classE, classE, classOfZero_mul, schemePullbackClass_add]

private theorem classE_map {U' U : Over (Spec (.of E))} (g : U' ⟶ U)
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) :
    classE k f E c₀ (ConcreteCategory.hom ((rigidified k f E c₀).map g.op) x) =
      schemePullbackClass (bcMap f (forgetBaseMap (Over.mk (specMap k E)) g))
          (classE k f E c₀ x) := by
  rw [classE, classE, classOfZero_map', schemePullbackClass_comp, schemePullbackClass_comp,
    bcForgetIso_inv_bcMap]
  rfl

private theorem relDeg_classE {U : Over (Spec (.of E))}
    (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) (t : U.left) :
    relativeInvertibleDegreeHomAt (bcProj f (forgetBase (Over.mk (specMap k E)) U))
      (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) t
          (classE k f E c₀ x) = 0 := by
  have h : degree f (topologicalKrullDim_fiber_le_one f) (forgetBase (Over.mk (specMap k E)) U)
      (smallSchemePullbackClassHom (bcForgetIso f (Over.mk (specMap k E)) U).inv
        (Multiplicative.toAdd x).1.1) = 0 := by
    rw [degree_bcForgetIso_inv]
    exact funext ((mem_groupZero_iff _ _ _ _ _ _).1 (Multiplicative.toAdd x).2)
  have := congrFun h t
  rw [degree_apply, smallEquiv_smallSchemePullbackClassHom] at this
  exact this

/-- Over a one-point `E`-scheme every class of degree zero comes from the rigidified `Pic⁰`. -/
private theorem exists_classE_eq {U : Over (Spec (.of E))} (hU : Subsingleton U.left)
    (hU' : Nonempty U.left) (z : ofScheme (bc f (forgetBase (Over.mk (specMap k E)) U)))
    (hz : ∀ t, relativeInvertibleDegreeHomAt (bcProj f (forgetBase (Over.mk (specMap k E)) U))
      (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) t z = 0) :
    ∃ x, classE k f E c₀ x = z := by
  have := hU
  have := hU'
  have hc : schemePullbackClass (bcSection (curveOver k f E) (pointSection f _ c₀)
      (pointSection_bcProj f _ c₀) U)
      (schemePullbackClass (bcForgetIso f (Over.mk (specMap k E)) U).hom z) = 0 :=
    Stacks.Picard.eq_zero_of_subsingleton _
  have hdeg : ∀ t : U.left, relativeInvertibleDegreeHomAt (bcProj (curveOver k f E) U)
      (topologicalKrullDim_fiber_bcProj_le (curveOver k f E)
          (topologicalKrullDim_fiber_curveOver_le_one k f E) U) t
        (schemePullbackClass (bcForgetIso f (Over.mk (specMap k E)) U).hom z) = 0 := by
    intro t
    have h := congrFun (degree_bcForgetIso_inv k f E U
      ((smallEquiv.{u} _).symm
        (schemePullbackClass (bcForgetIso f (Over.mk (specMap k E)) U).hom z))) t
    rw [degree_apply, degree_apply, smallEquiv_smallSchemePullbackClassHom,
      AddEquiv.apply_symm_apply, schemePullbackClass_comp, Iso.inv_hom_id,
      schemePullbackClass_id, hz] at h
    exact h.symm
  refine ⟨mkZero (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
      (pointSection f _ c₀) (pointSection_bcProj f _ c₀) _ hc
    hdeg, ?_⟩
  rw [classE, classOfZero_mkZero, schemePullbackClass_comp, Iso.inv_hom_id,
    schemePullbackClass_id]

omit [IsSmoothProjectiveCurve k f] in
private theorem bcForgetIso_inv_fst (U : Over (Spec (.of E))) :
    (bcForgetIso f (Over.mk (specMap k E)) U).inv ≫ pullback.fst (curveOver k f E) U.hom =
      bcMap f (relToT (Over.mk (specMap k E)) U) := by
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, bcForgetIso_hom_fst]
  · rw [Category.assoc, show bcMap f (relToT (Over.mk (specMap k E)) U) ≫
        pullback.snd f (Over.mk (specMap k E)).hom =
        pullback.snd f (forgetBase (Over.mk (specMap k E)) U).hom ≫ U.hom from bcMap_snd f _,
      ← Category.assoc, bcForgetIso_hom_snd]
    exact pullback.condition

/-- **The chart condition on `C_E`, read on `C ×_k U`.** -/
private theorem mem_chartE_iff (θ : ofScheme (bc f (Over.mk (specMap k E))))
    {U : Over (Spec (.of E))} (x : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op U)) :
    x ∈ (chartE k f E c₀ θ).obj (op U) ↔
      HasInvertibleDirectImage f (forgetBase (Over.mk (specMap k E)) U)
        (classE k f E c₀ x + schemePullbackClass (bcMap f (relToT _ U)) θ) := by
  have := smoothOfRelativeDimension_curveOver k f E
  have := isProper_curveOver k f E
  have := smooth_curveOver k f E
  have hsq : IsPullback (bcForgetIso f (Over.mk (specMap k E)) U).inv
      (bcProj f (forgetBase (Over.mk (specMap k E)) U)) (bcProj (curveOver k f E) U) (𝟙 U.left) :=
    haveI : IsIso (𝟙 U.left) := IsIso.id _
    IsPullback.of_horiz_isIso ⟨by erw [Category.comp_id]; rw [Iso.inv_comp_eq, bcForgetIso_hom_snd]⟩
  have : IsIso (𝟙 U.left) := IsIso.id _
  refine (hasDerivedPushforwardRank_iff_of_isPullback (bcProj (curveOver k f E) U)
    (finitePresentation_bcProj _ U) hsq _
    (Stacks.Picard.picardRepresentative _ _).property).trans ?_
  obtain ⟨e⟩ := nonempty_iso_pullback_picardRepresentative
      (bcForgetIso f (Over.mk (specMap k E)) U).inv
    (classOfZero (curveOver k f E) (topologicalKrullDim_fiber_curveOver_le_one k f E)
        (pointSection f _ c₀) (pointSection_bcProj f _ c₀) x +
      schemePullbackClass (pullback.fst (curveOver k f E) U.hom) θ)
  refine (hasDerivedPushforwardRank_congr e).trans ?_
  rw [schemePullbackClass_add, schemePullbackClass_comp, bcForgetIso_inv_fst]
  rfl

/-- The morphism `C_E ⟶ C ×_k E` comparing the two copies of `E` as a `k`-scheme. -/
private noncomputable abbrev topHom :
    Over.mk (specMap k E) ⟶ forgetBase (Over.mk (specMap k E)) (Over.mk (𝟙 (Spec (.of E)))) :=
  Over.homMk (𝟙 _) (by simp)

/-- The class on `C_E` of an `E`-point of the rigidified `Pic⁰` of `C_E`. -/
private noncomputable def topClass
    (r : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of E)))))) :
    ofScheme (bc f (Over.mk (specMap k E))) :=
  schemePullbackClass (bcMap f (topHom k E)) (classE k f E c₀ r)

private theorem classE_map_top {U : Over (Spec (.of E))} (φ : U ⟶ Over.mk (𝟙 (Spec (.of E))))
    (r : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of E)))))) :
    classE k f E c₀ (ConcreteCategory.hom ((rigidified k f E c₀).map φ.op) r) =
      schemePullbackClass (bcMap f (relToT (Over.mk (specMap k E)) U)) (topClass k f E c₀ r) := by
  rw [classE_map, topClass, schemePullbackClass_comp, ← bcMap_comp]
  congr 2
  ext1
  simpa using Over.w φ

private theorem exists_topClass_eq (y : ofScheme (bc f (Over.mk (specMap k E))))
    (hy : ∀ t, relativeInvertibleDegreeHomAt (bcProj f (Over.mk (specMap k E)))
      (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) t y = 0) :
    ∃ r, topClass k f E c₀ r = y := by
  obtain ⟨r, hr⟩ := exists_classE_eq k f E c₀ (U := Over.mk (𝟙 (Spec (.of E))))
    (inferInstanceAs (Subsingleton (PrimeSpectrum E)))
    (inferInstanceAs (Nonempty (PrimeSpectrum E)))
    (schemePullbackClass (bcMap f (relToT _ _)) y)
    (fun t => by rw [relDeg_bcMap]; exact hy _)
  refine ⟨r, ?_⟩
  rw [topClass, hr, schemePullbackClass_comp, ← bcMap_comp]
  have : topHom k E ≫ relToT (Over.mk (specMap k E)) (Over.mk (𝟙 (Spec (.of E)))) = 𝟙 _ := by
    ext1; simp
  rw [this, bcMap_id, schemePullbackClass_id]

private theorem relDeg_topClass
    (r : (rigidified k f E c₀ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of E))))))
    (t : Spec (.of E)) :
    relativeInvertibleDegreeHomAt (bcProj f (Over.mk (specMap k E)))
      (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) t
          (topClass k f E c₀ r) = 0 := by
  rw [topClass, relDeg_bcMap]
  exact relDeg_classE k f E c₀ r _

end FiniteStage

section FiniteStageExistence

/-! ### A finite extension over which the translates meet every field-valued point -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

open Stacks.RigidifiedPicard Stacks.Picard

/-- The `k`-morphism `Spec B ⟶ Spec A` of a `k`-algebra map `A → B`. -/
private noncomputable abbrev specHom {A B : Type u} [Field A] [Field B] [Algebra k A]
    [Algebra k B] (φ : A →ₐ[k] B) : Over.mk (specMap k B) ⟶ Over.mk (specMap k A) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : A →+* B))) (by
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.comp_algebraMap])

/-- **Picard classes of `C_Ω` descend to a finite stage**, for `Ω/k` algebraic. -/
private theorem exists_intermediateField_eq {Ω : Type u} [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (y : ofScheme (bc f (Over.mk (specMap k Ω)))) :
    ∃ (E : IntermediateField k Ω) (_ : FiniteDimensional k E)
      (w : ofScheme (bc f (Over.mk (specMap k E)))),
      schemePullbackClass (bcMap f (specHom k E.val)) w = y := by
  have : CompactSpace (Over.mk f).left := (quasiCompact_iff_compactSpace f).1 inferInstance
  have : QuasiSeparatedSpace (Over.mk f).left := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨E, hE, p, w, h1, h2, h3⟩ :=
    exists_finiteSubextension_schemePullbackClass_eq (Over.mk f) (K := Ω) y
  refine ⟨E, hE, w, ?_⟩
  have hp : p = bcMap f (specHom k E.val) := by
    apply pullback.hom_ext
    · exact h1.trans (bcMap_fst f (specHom k E.val)).symm
    · exact h2.trans (bcMap_snd f (specHom k E.val)).symm
  rwa [← hp]

/-- The `k`-morphism `Spec Ω ⟶ Spec L` of a tower `k ⊆ L ⊆ Ω`. -/
private noncomputable abbrev specOver (L Ω : Type u) [Field L] [Field Ω] [Algebra k L]
    [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] :
    Over.mk (specMap k Ω) ⟶ Over.mk (specMap k L) :=
  Over.homMk (specMap L Ω) (specMap_comp_specMap k L Ω)

/-- **The translate condition descends to a finite stage.** If the classes of finitely many
`Ω`-points and the class `θ` of `C_Ω` are pulled back from `C_L`, and their chart translates meet
every field-valued point over `Ω`, then the translate condition holds over `L`. -/
private theorem translatesMeet_of_pullback (L Ω : Type u) [Field L] [Field Ω] [Algebra k L]
    [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [Algebra.IsAlgebraic L Ω]
    (cL : Over.mk (specMap k L) ⟶ Over.mk f) (cΩ : Over.mk (specMap k Ω) ⟶ Over.mk f)
    (θL : ofScheme (bc f (Over.mk (specMap k L)))) (θΩ : ofScheme (bc f (Over.mk (specMap k Ω))))
    (hθ : schemePullbackClass (bcMap f (specOver k L Ω)) θL = θΩ)
    (R : Finset ((rigidified k f Ω cΩ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of Ω)))))))
    (hR : ∀ (K : Type u) [Field K] [Algebra Ω K]
      (x : (rigidified k f Ω cΩ ⋙ forget GrpCat).obj (op (fieldExtensionPoint Ω K))),
      ∃ r ∈ R, (rigidified k f Ω cΩ).map (Over.homMk (fieldExtensionPoint Ω K).hom).op r * x ∈
        (chartE k f Ω cΩ θΩ).obj (op (fieldExtensionPoint Ω K)))
    (rL : ∀ r ∈ R, (rigidified k f L cL ⋙ forget GrpCat).obj
      (op (Over.mk (𝟙 (Spec (.of L))))))
    (hrL : ∀ r (hr : r ∈ R), schemePullbackClass (bcMap f (specOver k L Ω))
      (topClass k f L cL (rL r hr)) = topClass k f Ω cΩ r) :
    TranslatesMeet k f L cL θL := by
  intro K _ _ x
  let M := AlgebraicClosure K
  have : FaithfulSMul L M :=
    (faithfulSMul_iff_algebraMap_injective L M).2 (algebraMap L M).injective
  have : FaithfulSMul L Ω :=
    (faithfulSMul_iff_algebraMap_injective L Ω).2 (algebraMap L Ω).injective
  have : Module.IsTorsionFree L M := FaithfulSMul.to_isTorsionFree L M
  have : Module.IsTorsionFree L Ω := FaithfulSMul.to_isTorsionFree L Ω
  let ι : Ω →ₐ[L] M := IsAlgClosed.lift
  have hι : ∀ a : L, ι (algebraMap L Ω a) = algebraMap K M (algebraMap L K a) := fun a =>
    (ι.commutes a).trans (IsScalarTower.algebraMap_apply L K M a)
  let : Algebra Ω M := ι.toRingHom.toAlgebra
  have hsq : specMap K M ≫ specMap L K = specMap Ω M ≫ specMap L Ω := by
    simp only [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change algebraMap K M (algebraMap L K a) = ι (algebraMap L Ω a)
    exact (hι a).symm
  have hm : specMap K M ≫ (forgetBase (Over.mk (specMap k L)) (fieldExtensionPoint L K)).hom =
      (forgetBase (Over.mk (specMap k Ω)) (fieldExtensionPoint Ω M)).hom := by
    change specMap K M ≫ specMap L K ≫ specMap k L = specMap Ω M ≫ specMap k Ω
    rw [← Category.assoc, hsq, Category.assoc, specMap_comp_specMap]
  obtain ⟨m, hmT⟩ : ∃ m : forgetBase (Over.mk (specMap k Ω)) (fieldExtensionPoint Ω M) ⟶
      forgetBase (Over.mk (specMap k L)) (fieldExtensionPoint L K),
      m ≫ relToT (Over.mk (specMap k L)) (fieldExtensionPoint L K) =
        relToT (Over.mk (specMap k Ω)) (fieldExtensionPoint Ω M) ≫ specOver k L Ω :=
    ⟨Over.homMk (specMap K M) hm, by
      ext1
      exact hsq⟩
  obtain ⟨x', hx'⟩ := exists_classE_eq k f Ω cΩ (U := fieldExtensionPoint Ω M)
    (inferInstanceAs (Subsingleton (PrimeSpectrum M)))
    (inferInstanceAs (Nonempty (PrimeSpectrum M)))
    (schemePullbackClass (bcMap f m) (classE k f L cL x))
    (fun t => by rw [relDeg_bcMap]; exact relDeg_classE k f L cL x _)
  obtain ⟨r, hr, hmem⟩ := hR M x'
  refine ⟨rL r hr, ?_⟩
  rw [mem_chartE_iff, classE_mul, classE_map_top] at hmem ⊢
  refine hasInvertibleDirectImage_of_bcMap k f m
    (inferInstanceAs (Subsingleton (PrimeSpectrum K)))
    (inferInstanceAs (Nonempty (PrimeSpectrum M))) _ ?_
  convert hmem using 2
  rw [schemePullbackClass_add, schemePullbackClass_add, ← hx', schemePullbackClass_comp,
    schemePullbackClass_comp, ← bcMap_comp, hmT, bcMap_comp, ← schemePullbackClass_comp,
    ← schemePullbackClass_comp, hrL, hθ]

private theorem exists_finite_translatesMeet : ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
    (_ : FiniteDimensional k L) (c : Over.mk (specMap k L) ⟶ Over.mk f)
    (θ : ofScheme (bc f (Over.mk (specMap k L)))),
    (∀ s, relativeInvertibleDegreeHomAt (curveOver k f L)
        (topologicalKrullDim_fiber_curveOver_le_one k f L) s θ =
      genus (curveOver k f L)) ∧ TranslatesMeet k f L c θ := by
  classical
  obtain ⟨L₀, _, _, _, ⟨c₀⟩⟩ := exists_finite_point k f
  let Ω := AlgebraicClosure L₀
  have : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k L₀ Ω
  let ι₀ : L₀ →ₐ[k] Ω := IsScalarTower.toAlgHom k L₀ Ω
  let cΩ := specHom k ι₀ ≫ c₀
  obtain ⟨θΩ, hθΩ⟩ := exists_theta k f Ω cΩ
  obtain ⟨R, hR⟩ := exists_finite_translates k f Ω cΩ θΩ hθΩ
  choose E hE w hw using fun r => exists_intermediateField_eq k f (topClass k f Ω cΩ r)
  obtain ⟨Eθ, _, wθ, hwθ⟩ := exists_intermediateField_eq k f θΩ
  have : FiniteDimensional k ι₀.fieldRange :=
    LinearEquiv.finiteDimensional ι₀.equivFieldRange.toLinearEquiv
  have : ∀ r, FiniteDimensional k (E r) := hE
  let Lf : IntermediateField k Ω := (ι₀.fieldRange ⊔ ⨆ r ∈ R, E r) ⊔ Eθ
  have : FiniteDimensional k ↥(⨆ r ∈ R, E r : IntermediateField k Ω) :=
    IntermediateField.finiteDimensional_iSup_of_finset
  have : FiniteDimensional k ↥(ι₀.fieldRange ⊔ ⨆ r ∈ R, E r : IntermediateField k Ω) :=
    IntermediateField.finiteDimensional_sup _ _
  have : FiniteDimensional k Lf := IntermediateField.finiteDimensional_sup _ _
  have h₀ : ι₀.fieldRange ≤ Lf := le_sup_left.trans le_sup_left
  have hER : ∀ r ∈ R, E r ≤ Lf := fun r hr =>
    (le_iSup₂ (f := fun r (_ : r ∈ R) => E r) r hr).trans (le_sup_right.trans le_sup_left)
  have hθle : Eθ ≤ Lf := le_sup_right
  let φ₀ : L₀ →ₐ[k] Lf := (IntermediateField.inclusion h₀).comp ι₀.equivFieldRange.toAlgHom
  let cL : Over.mk (specMap k Lf) ⟶ Over.mk f := specHom k φ₀ ≫ c₀
  let gΩL := specOver k Lf Ω
  have hpull : ∀ (E' : IntermediateField k Ω) (h : E' ≤ Lf)
      (w' : ofScheme (bc f (Over.mk (specMap k E')))),
      schemePullbackClass (bcMap f gΩL)
          (schemePullbackClass (bcMap f (specHom k (IntermediateField.inclusion h))) w') =
        schemePullbackClass (bcMap f (specHom k E'.val)) w' := by
    intro E' h w'
    have : specOver k Lf Ω ≫ specHom k (IntermediateField.inclusion h) = specHom k E'.val := by
      ext1
      simp only [Over.comp_left, Over.homMk_left, specMap]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [schemePullbackClass_comp, ← bcMap_comp, this]
  let θL := schemePullbackClass (bcMap f (specHom k (IntermediateField.inclusion hθle))) wθ
  have hθL' : schemePullbackClass (bcMap f gΩL) θL = θΩ := (hpull _ _ _).trans hwθ
  obtain ⟨tΩ⟩ : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hdegL : ∀ (y : ofScheme (bc f (Over.mk (specMap k Lf)))) (s : Spec (.of Lf)),
      relativeInvertibleDegreeHomAt (bcProj f (Over.mk (specMap k Lf)))
        (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) s y =
      relativeInvertibleDegreeHomAt (bcProj f (Over.mk (specMap k Ω)))
        (topologicalKrullDim_fiber_bcProj_le f (topologicalKrullDim_fiber_le_one f) _) tΩ
          (schemePullbackClass (bcMap f gΩL) y) := by
    intro y s
    have : Subsingleton (Spec (.of Lf)) := inferInstanceAs (Subsingleton (PrimeSpectrum Lf))
    rw [relDeg_bcMap, Subsingleton.elim s (gΩL.left tΩ)]
  have hθL : ∀ s, relativeInvertibleDegreeHomAt (curveOver k f Lf)
      (topologicalKrullDim_fiber_curveOver_le_one k f Lf) s θL =
      genus (curveOver k f Lf) := by
    intro s
    have h1 := hdegL θL s
    rw [hθL'] at h1
    have h2 := hθΩ tΩ
    have h3 : genus (curveOver k f Lf) = genus (curveOver k f Ω) :=
      (genus_bc_spec f (specMap k Lf)).trans (genus_bc_spec f (specMap k Ω)).symm
    rw [h3, ← h2]
    exact h1
  have hrL : ∀ r ∈ R, ∃ rL, schemePullbackClass (bcMap f gΩL) (topClass k f Lf cL rL) =
      topClass k f Ω cΩ r := by
    intro r hr
    obtain ⟨rL, hrL⟩ := exists_topClass_eq k f Lf cL
      (schemePullbackClass (bcMap f (specHom k (IntermediateField.inclusion (hER r hr)))) (w r))
      (fun s => by
        rw [hdegL, hpull, hw]
        exact relDeg_topClass k f Ω cΩ r tΩ)
    exact ⟨rL, by rw [hrL, hpull, hw]⟩
  choose rL hrL using hrL
  have : Algebra.IsAlgebraic Lf Ω := Algebra.IsAlgebraic.tower_top (K := k) Lf
  exact ⟨Lf, inferInstance, inferInstance, inferInstance, cL, θL, hθL,
    translatesMeet_of_pullback k f Lf Ω cL cΩ θL θΩ hθL' R hR rL hrL⟩

end FiniteStageExistence

section Existence

/-! ### Existence -/

variable (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

private theorem isFiniteLocallyFree_specMap (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] : Stacks.Morphisms.IsFiniteLocallyFree (specMap k L) := by
  have := isFiniteLocallyFreeOfRank_SpecMap_algebraMap k L
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (Module.finrank k L)

/-- **The Jacobian over a finite extension.** There is a finite extension `L/k` and an abelian
variety `V` over `L` representing `P⁰_C` on `L`-schemes. -/
private theorem exists_finite_rep : ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
    (_ : FiniteDimensional k L) (V : Over (Spec (.of L))) (_ : GrpObj V)
    (_ : IsAbelianVariety L V),
    Nonempty (yoneda.obj V ≅
      (Over.map (specMap k L)).op ⋙ relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) := by
  obtain ⟨L, _, _, _, c, θ, hθ, hT⟩ := exists_finite_translatesMeet k f
  obtain ⟨V, _, hV, ⟨e⟩⟩ := exists_rep_of_translatesMeet k f L c θ hθ hT
  exact ⟨L, inferInstance, inferInstance, inferInstance, V, inferInstance, hV, ⟨e⟩⟩

/-- **Descent of `P⁰_C` along a finite field extension**, at the `k`-schemes with a `C`-point. -/
private theorem bijective_toCompat (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    (T : Over (Spec (.of k))) (hT : Nonempty (T ⟶ Over.mk f)) :
    Function.Bijective (toCompat (Over.mk (specMap k L))
      (G := relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) T) :=
  ⟨injective_toCompat f (specMap k L) T hT.some, surjective_toCompat f (specMap k L) T hT.some⟩

/-- **Abelian varieties descend along a finite field extension.** -/
private theorem isAbelianVariety_of_descent (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] (J : Over (Spec (.of k))) [GrpObj J] (V : Over (Spec (.of L)))
    [GrpObj V] [IsAbelianVariety L V]
    (e : ((DescentData.canonicalFunctor (specMap k L)).obj J).obj () ≅ V) :
    IsAbelianVariety k J := by
  let ε : (Over.pullback (specMap k L)).obj J ≅ V :=
    (DescentData.canonicalObjIso (specMap k L) J).symm ≪≫ e
  have hsnd : pullback.snd J.hom (specMap k L) = ε.hom.left ≫ V.hom := (Over.w ε.hom).symm
  have hP : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso], P V.hom →
      P (pullback.snd J.hom (specMap k L)) := by
    intro P _ h
    rw [hsnd]
    exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 h
  have hproper : IsProper J.hom := isProper_of_fieldExtension k L J.hom (hP @IsProper inferInstance)
  have hgi : GeometricallyIntegral J.hom :=
    geometricallyIntegral_of_pullback_specMap J.hom L
      (@hP @GeometricallyIntegral
        (MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @GeometricallyIntegral))
        inferInstance)
  have hint : IsIntegral J.left := self_of_isIntegral_of_geometrically hgi.geometrically_isIntegral
  have hvar : IsVariety k J.hom :=
    { toIsIntegral := hint, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  have hpv : IsProperVariety k J.hom := (isProperVariety_iff k J.hom).2 ⟨hvar, hproper⟩
  exact { toIsProperVariety := hpv, toGeometricallyIntegral := hgi }

open scoped MonObj in
/-- **Every curve over a field has a Jacobian.** -/
private theorem nonempty_jacobian : Nonempty (Jacobian k f) := by
  obtain ⟨L, _, _, _, V, _, _, ⟨Ψ⟩⟩ := exists_finite_rep k f
  have := isFiniteLocallyFree_specMap k L
  obtain ⟨J, ⟨R⟩, ⟨e⟩⟩ := exists_repOn_of_isFiniteLocallyFree (specMap k L) V
    (relativePicZeroFunctor k f ⋙ forget AddCommGrpCat) (repTheta (specMap k L) V _ Ψ)
    (repTheta_naturality (specMap k L) V _ Ψ) (repTheta_existsUnique (specMap k L) V _ Ψ)
    (isProjective_of_isAbelianVariety L V)
  have : Flat (Over.mk (specMap k L)).hom := inferInstanceAs (Flat (specMap k L))
  have : Surjective (Over.mk (specMap k L)).hom := inferInstanceAs (Surjective (specMap k L))
  have : QuasiCompact (Over.mk (specMap k L)).hom :=
    inferInstanceAs (QuasiCompact (specMap k L))
  let := R.grpObj (Over.mk (specMap k L))
  refine nonempty_jacobian_of_repOn J (isAbelianVariety_of_descent k L J V e)
    (R.ofSheafCondition (Over.mk (specMap k L)) (Over.mk f) (bijective_toCompat k f L)) ?_
  intro T hT x y
  change R.compatEquiv _ T (toCompat _ T (x + y)) =
    R.compatEquiv _ T (toCompat _ T x) * R.compatEquiv _ T (toCompat _ T y)
  rw [← R.compatEquiv_add]
  congr 1
  exact Subtype.ext (map_add ((relativePicZeroFunctor k f).map
    (prodYFst (Over.mk (specMap k L)) T).op).hom x y)

end Existence

/-- A curve `X.f : X.C ⟶ Spec k` with a rational divisor of degree one has a Jacobian, and it is
unique up to unique isomorphism: for any two Jacobians `A` and `B` there is a unique
isomorphism `e : A.J ≅ B.J` of `k`-schemes with `A.ι ≫ yoneda.map e.hom = B.ι`. -/
@[faltings "lem_nt_jacobian_exists"]
public theorem Jacobian.nonempty_and_existsUnique_iso (k : Type u) [Field k]
    (X : CurveWithDegreeOneDivisor k) :
    Nonempty (Jacobian k X.f) ∧
      ∀ A B : Jacobian k X.f, ∃! e : A.J ≅ B.J, A.ι ≫ yoneda.map e.hom = B.ι :=
  ⟨nonempty_jacobian k X.f, existsUnique_iso⟩

end Faltings
