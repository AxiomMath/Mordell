module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.SegreProdIso.Main
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec

/-!
# An even ample class on an abelian variety

Let `A` be an abelian variety over a field `F`. Then `A` has an ample invertible sheaf `ℳ` that is
even, `[-1]^*ℳ ≅ ℳ`, together with a closed immersion `φ : A → ℙⁿ_F` and an `r ≥ 1` with
`φ^*𝒪(1) ≅ ℳ^{⊗ r}`. For the proof, take an ample `ℒ` (`A` is projective). Then `ℳ = ℒ ⊗ [-1]^*ℒ`
is ample and even, and some power of it is very ample.

We state this through the embedding. There is a closed immersion `φ : A → ℙⁿ_F` over `F` and an
automorphism `σ` of `ℙⁿ_F` over `F` such that `φ ∘ [-1] = σ ∘ φ`. This is equivalent to the form
above. Given `φ` and `σ`, put `ℳ = φ^*𝒪(1)` and `r = 1`: `ℳ` is very ample, hence ample, and
`[-1]^*ℳ ≅ φ^*σ^*𝒪(1) ≅ φ^*𝒪(1) = ℳ`, because every automorphism of `ℙⁿ_F` over `F` lies in
`PGL_{n+1}(F)` and fixes `𝒪(1)`. Conversely, if `ℳ^{⊗ r}` is very ample and even, embed `A` by
the complete linear system `|ℳ^{⊗ r}|`. Pullback along `[-1]`, followed by an isomorphism
`[-1]^*ℳ^{⊗ r} ≅ ℳ^{⊗ r}`, is a linear automorphism of `H⁰(A, ℳ^{⊗ r})`, and this automorphism
gives `σ`.

## Main results

* `Faltings.exists_isClosedImmersion_proj_inv_comp_eq_comp`: an abelian variety over `F` has a
  closed immersion into `ℙⁿ_F` over `F` under which `[-1]` is induced by an automorphism of
  `ℙⁿ_F` over `F`.

## Implementation notes

An abelian variety over `F` is `A : Over (Spec F)` with a `CategoryTheory.GrpObj` structure such
that `A.hom` is proper and geometrically integral. Its inversion `[-1]` is `ι[A]`. Projective space
`ℙⁿ_F` is `projectiveSpaceOver n (Spec F)`, the base change to `Spec F` of the integral model
`Proj ℤ[T₀, …, Tₙ]`, with its structure morphism to `Spec F`.

The proof follows the source. `A` is projective over `F` (Stacks, Tag 0BFA), so there is a
closed immersion `ψ : A → ℙⁿ_F` with `ψ^*𝒪(1) = ℒ` ample. The morphism `(ψ, ψ ∘ [-1])` into
`ℙⁿ_F ×_F ℙⁿ_F` followed by the Segre embedding into `ℙ^{n² + 2n}_F` is a closed immersion, and
it pulls `𝒪(1)` back to `ℳ = ℒ ⊗ [-1]^*ℒ`. Since `[-1] ∘ [-1] = id`, composing with `[-1]`
exchanges the two factors, and under the Segre embedding the exchange of the factors is the
linear automorphism `z_{ij} ↦ z_{ji}` of `ℙ^{n² + 2n}`.

The Segre embedding is built over the integral model of projective space, as `Proj` of the Segre
product `S = ⨁_d ℤ[x]_d ⊗ ℤ[y]_d`. The exchange of the two factors is first identified with the
morphism of `Proj S` induced by the graded involution of `S` exchanging the `x` and the `y`
variables, by comparing the two glued Segre projections on the standard charts `D₊(x_i y_j)`.
The Segre presentation `ℤ[z_{ij}] → S` intertwines that involution with the transposition
`z_{ij} ↦ z_{ji}`, which gives the automorphism of the integral model of `ℙ^{n² + 2n}`, and its
base change to `Spec F` is `σ`.

## References

* [The Stacks Project][stacks], Tags 0BFA, 0890, 01VU, 02NP, 01WD, 04XV
* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 2
-/

@[expose] public section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped MonObj

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.RingTheory.SegreProduct.gradingGradedAlgebra

namespace Faltings

open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection

section Algebra

variable (R : Type*) [CommRing R] (X : Type*)

private lemma isWeightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M] {w : τ → M}
    {f : σ → τ} {p : MvPolynomial σ R} {m : M} (h : IsWeightedHomogeneous (w ∘ f) p m) :
    IsWeightedHomogeneous w (rename f p) m := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  simp_rw [rename_monomial]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => isWeightedHomogeneous_monomial _ _ _ ?_
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • w i)
    (fun _ => zero_smul ℕ _) (fun _ _ _ => add_smul _ _ _)]
  have := h (mem_support_iff.mp hd)
  rw [Finsupp.weight_apply] at this
  exact this

private lemma rename_swap_mem_gradePiece {n : ℕ} {p : MvPolynomial (X ⊕ X) R}
    (hp : p ∈ gradePiece R X X n) : rename Sum.swap p ∈ gradePiece R X X n := by
  refine ⟨isWeightedHomogeneous_rename R ?_, isWeightedHomogeneous_rename R ?_⟩
  · have : weightLeft X X ∘ Sum.swap = weightRight X X := by
      funext i; cases i <;> rfl
    rw [this]; exact hp.2
  · have : weightRight X X ∘ Sum.swap = weightLeft X X := by
      funext i; cases i <;> rfl
    rw [this]; exact hp.1

private lemma rename_swap_mem_segre {p : MvPolynomial (X ⊕ X) R} (hp : p ∈ segre R X X) :
    rename Sum.swap p ∈ segre R X X := by
  rw [mem_segre_iff] at hp ⊢
  exact Submodule.iSup_induction (motive := fun p =>
      rename Sum.swap p ∈ ⨆ n : ℕ, gradePiece R X X n) _ hp
    (fun n x hx => Submodule.mem_iSup_of_mem n (rename_swap_mem_gradePiece R X hx))
    (by simp) (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)

/-- The involution of the Segre product exchanging the two groups of variables. -/
private noncomputable def segreSwap : segre R X X →ₐ[R] segre R X X :=
  ((rename Sum.swap).comp (segre R X X).val).codRestrict (segre R X X)
    fun x => rename_swap_mem_segre R X x.2

private lemma coe_segreSwap (x : segre R X X) :
    (segreSwap R X x : MvPolynomial (X ⊕ X) R) = rename Sum.swap (x : MvPolynomial (X ⊕ X) R) :=
  rfl

/-- The involution of the Segre product, as a graded ring homomorphism. -/
private noncomputable def segreSwapGraded : grading R X X →+*ᵍ grading R X X where
  toRingHom := (segreSwap R X).toRingHom
  map_mem {_ _} hx := rename_swap_mem_gradePiece R X hx

/-- The involution of the polynomial ring on `X × X` exchanging the coordinates of the index. -/
private noncomputable def pairSwapGraded :
    homogeneousSubmodule (X × X) R →+*ᵍ homogeneousSubmodule (X × X) R where
  toRingHom := (rename (R := R) Prod.swap).toRingHom
  map_mem {_ _} hx := (mem_homogeneousSubmodule _ _).mpr
    (IsHomogeneous.rename_isHomogeneous ((mem_homogeneousSubmodule _ _).mp hx))

private lemma segreSwapGraded_comp_substLeftGraded (c : X) :
    (segreSwapGraded R X).comp (substLeftGraded R X X c) = substRightGraded R X X c := by
  have h : (segreSwap R X).comp (substLeft R X X c) = substRight R X X c := by
    refine MvPolynomial.algHom_ext fun i => ?_
    apply Subtype.ext
    simp [coe_segreSwap, gen_eq, mul_comm]
  exact GradedRingHom.ext fun x => AlgHom.congr_fun h x

private lemma segreSwapGraded_comp_presentation :
    (segreSwapGraded R X).comp (presentation R X X) =
      (presentation R X X).comp (pairSwapGraded R X) := by
  have h : (segreSwap R X).comp (presentationAlgHom R X X) =
      (presentationAlgHom R X X).comp (rename Prod.swap) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    apply Subtype.ext
    simp [coe_segreSwap, val_presentationAlgHom, gen_eq, mul_comm]
  exact GradedRingHom.ext fun x => AlgHom.congr_fun h x

private lemma segreSwapGraded_comp_self :
    (segreSwapGraded R X).comp (segreSwapGraded R X) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => Subtype.ext ?_
  change rename Sum.swap (rename Sum.swap (x : MvPolynomial (X ⊕ X) R)) = x
  rw [rename_rename]
  have : (Sum.swap ∘ Sum.swap : X ⊕ X → X ⊕ X) = id := by funext i; cases i <;> rfl
  rw [this, rename_id_apply]

private lemma pairSwapGraded_comp_self :
    (pairSwapGraded R X).comp (pairSwapGraded R X) = GradedRingHom.id _ := by
  refine GradedRingHom.ext fun x => ?_
  change rename Prod.swap (rename Prod.swap x) = x
  rw [rename_rename]
  have : (Prod.swap ∘ Prod.swap : X × X → X × X) = id := by funext i; rfl
  rw [this, rename_id_apply]

end Algebra

section Geometry

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
  Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.SegreGlue
  Stacks.AlgebraicGeometry.SegreProjection

private lemma surjective_gradedAddHom_of_comp_self {A : Type u} {σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (ψ : 𝒜 →+*ᵍ 𝒜)
    (h : ψ.comp ψ = GradedRingHom.id 𝒜) (d : ℕ) :
    Function.Surjective (GradedRingHom.gradedAddHom ψ d) := fun y =>
  ⟨GradedRingHom.gradedAddHom ψ d y, Subtype.ext (DFunLike.congr_fun h y.1)⟩

private lemma mapDomain_eq_top_of_comp_self {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (ψ : 𝒜 →+*ᵍ 𝒜)
    (h : ψ.comp ψ = GradedRingHom.id 𝒜) : mapDomain 𝒜 𝒜 ψ = ⊤ :=
  Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective 𝒜 𝒜 ψ
    (.of_forall (surjective_gradedAddHom_of_comp_self 𝒜 ψ h))

private lemma mapHomOfTop_comp_self {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (ψ : 𝒜 →+*ᵍ 𝒜)
    (h : ψ.comp ψ = GradedRingHom.id 𝒜) :
    mapHomOfTop 𝒜 𝒜 ψ (mapDomain_eq_top_of_comp_self 𝒜 ψ h) ≫
      mapHomOfTop 𝒜 𝒜 ψ (mapDomain_eq_top_of_comp_self 𝒜 ψ h) = 𝟙 _ := by
  have hid : (GradedRingHom.id 𝒜).comp (GradedRingHom.id 𝒜) = GradedRingHom.id 𝒜 := rfl
  have hc : mapDomain 𝒜 𝒜 (ψ.comp ψ) = ⊤ := h ▸ mapDomain_eq_top_of_comp_self 𝒜 _ hid
  calc _ = mapHomOfTop 𝒜 𝒜 (ψ.comp ψ) hc :=
        (Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top 𝒜 𝒜 𝒜 ψ ψ
          _ _ hc).symm
    _ = mapHomOfTop 𝒜 𝒜 (GradedRingHom.id 𝒜) (mapDomain_eq_top_of_comp_self 𝒜 _ hid) :=
        Stacks.AlgebraicGeometry.ProjPolynomialSections.mapHomOfTop_congr _ _ h _ _
    _ = 𝟙 _ := by
        rw [mapHomOfTop_eq_map 𝒜 𝒜 (GradedRingHom.id 𝒜) (by simp), Proj.map_id]

private lemma mapDomain_comp_eq_top {A B C : Type u} {σ τ υ : Type u} [CommRing A] [CommRing B]
    [CommRing C] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [SetLike υ C] [AddSubgroupClass υ C] (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜]
    [GradedRing ℬ] [GradedRing 𝒞] (φ : 𝒜 →+*ᵍ ℬ) (ρ : ℬ →+*ᵍ 𝒞)
    (hφ : ∀ᶠ d : ℕ in Filter.atTop, Function.Surjective (GradedRingHom.gradedAddHom φ d))
    (hρ : ∀ᶠ d : ℕ in Filter.atTop, Function.Surjective (GradedRingHom.gradedAddHom ρ d)) :
    mapDomain 𝒜 𝒞 (ρ.comp φ) = ⊤ :=
  Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective 𝒜 𝒞 _
    ((hφ.and hρ).mono fun d hd y => by
      obtain ⟨x, hx⟩ := (hd.2.comp hd.1) y
      exact ⟨x, Subtype.ext (congrArg Subtype.val hx)⟩)

variable (R : Type u) [CommRing R] (X : Type v)

/-- The involution of `Proj` of the Segre product exchanging the two factors. -/
private noncomputable def segreSwapProj :
    AlgebraicGeometry.Proj (grading R X X) ⟶ AlgebraicGeometry.Proj (grading R X X) :=
  mapHomOfTop _ _ (segreSwapGraded R X)
    (mapDomain_eq_top_of_comp_self _ _ (segreSwapGraded_comp_self R X))

private lemma segreSwapProj_comp_self : segreSwapProj R X ≫ segreSwapProj R X = 𝟙 _ :=
  mapHomOfTop_comp_self _ _ (segreSwapGraded_comp_self R X)

private lemma segreSwapProj_comp_projLeftGlued :
    segreSwapProj R X ≫ projLeftGlued R X X = projRightGlued R X X := by
  refine ((AlgebraicGeometry.Proj (grading R X X)).openCoverOfIsOpenCover _
    (TopologicalSpace.IsOpenCover.mk
      (iSup_basicOpen_substRightGraded_X_eq_top R X X))).hom_ext _ _ fun (p : X × X) => ?_
  change (AlgebraicGeometry.Proj.basicOpen (grading R X X)
      (substRightGraded R X X p.1 (MvPolynomial.X p.2))).ι ≫ _ =
    (AlgebraicGeometry.Proj.basicOpen (grading R X X)
      (substRightGraded R X X p.1 (MvPolynomial.X p.2))).ι ≫ _
  rw [ι_projRightGlued]
  have key : ∀ (ψ : homogeneousSubmodule X R →+*ᵍ grading R X X)
      (_ : (segreSwapGraded R X).comp (substLeftGraded R X X p.1) = ψ),
      (AlgebraicGeometry.Proj.basicOpen (grading R X X) (ψ (MvPolynomial.X p.2))).ι ≫
        segreSwapProj R X ≫ projLeftGlued R X X =
      mapAwayHom _ _ ψ one_pos (X_mem R X p.2) := by
    rintro ψ rfl
    rw [mapAwayHom_comp, ← ι_projLeftGlued R X X (p.2, p.1)]
    simp only [← Category.assoc]
    rw [mapAwayHomRes_ι]
    congr 1
    exact (ι_mapHomOfTop (grading R X X) (grading R X X) (segreSwapGraded R X)
      (mapDomain_eq_top_of_comp_self _ _ (segreSwapGraded_comp_self R X)) one_pos
      (mem_of_mem _ _ (substLeftGraded R X X p.1) (X_mem R X p.2)))
  exact key _ (segreSwapGraded_comp_substLeftGraded R X p.1)

private lemma segreSwapProj_comp_projRightGlued :
    segreSwapProj R X ≫ projRightGlued R X X = projLeftGlued R X X := by
  rw [← segreSwapProj_comp_projLeftGlued, ← Category.assoc, segreSwapProj_comp_self,
    Category.id_comp]

end Geometry

section Integral

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.RelativeProj
  Stacks.AlgebraicGeometry.SegreGlue Stacks.AlgebraicGeometry.SegreClosedImmersion

variable (R : Type u) [CommRing R] (X : Type v)

/-- The involution of `Proj` of the polynomial ring on `X × X` exchanging the coordinates of the
index. -/
private noncomputable def pairSwapProj :
    AlgebraicGeometry.Proj (homogeneousSubmodule (X × X) R) ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (X × X) R) :=
  mapHomOfTop _ _ (pairSwapGraded R X)
    (mapDomain_eq_top_of_comp_self _ _ (pairSwapGraded_comp_self R X))

private lemma pairSwapProj_comp_self : pairSwapProj R X ≫ pairSwapProj R X = 𝟙 _ :=
  mapHomOfTop_comp_self _ _ (pairSwapGraded_comp_self R X)

private lemma segreSwapProj_comp_segreProjMap :
    segreSwapProj R X ≫ segreProjMap R X X = segreProjMap R X X ≫ pairSwapProj R X := by
  have h1 := mapDomain_comp_eq_top _ _ _ (presentation R X X) (segreSwapGraded R X)
    (eventually_surjective_gradedAddHom R X X)
    (Filter.Eventually.of_forall (surjective_gradedAddHom_of_comp_self _ _
      (segreSwapGraded_comp_self R X)))
  have h2 := mapDomain_comp_eq_top _ _ _ (pairSwapGraded R X) (presentation R X X)
    (Filter.Eventually.of_forall (surjective_gradedAddHom_of_comp_self _ _
      (pairSwapGraded_comp_self R X)))
    (eventually_surjective_gradedAddHom R X X)
  have hp : mapDomain _ _ (presentation R X X) = ⊤ :=
    Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective _ _ _
      (eventually_surjective_gradedAddHom R X X)
  exact ((Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top _ _ _
      (presentation R X X) (segreSwapGraded R X) hp
      (mapDomain_eq_top_of_comp_self _ _ (segreSwapGraded_comp_self R X)) h1).symm.trans
    (Stacks.AlgebraicGeometry.ProjPolynomialSections.mapHomOfTop_congr _ _
      (segreSwapGraded_comp_presentation R X) h1 h2)).trans
    (Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top _ _ _
      (pairSwapGraded R X) (presentation R X X)
      (mapDomain_eq_top_of_comp_self _ _ (pairSwapGraded_comp_self R X)) hp h2)

variable (n : ℕ)

/-- The exchange of the two factors of `ℙⁿ ×_ℤ ℙⁿ`. -/
private noncomputable def factorSwap :
    projectiveSpaceOver n (projectiveSpaceAtUniverse.{u} n) ⟶
      projectiveSpaceOver n (projectiveSpaceAtUniverse.{u} n) :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _) (terminal.hom_ext _ _)

/-- `segreSwapProj` on the named `Proj` of the Segre product of two copies of `ℤ[x₀, …, xₙ]`. -/
private noncomputable def segreSwapSegre :
    projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (n + 1)) ⟶
      projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (n + 1)) :=
  segreSwapProj (ULift.{u} ℤ) (Fin (n + 1))

private lemma segreSwapSegre_comp_segreProd :
    segreSwapSegre n ≫ segreProd.{u} n n = segreProd.{u} n n ≫ factorSwap n := by
  have e1 : segreProd.{u} n n ≫ pullback.fst _ _ =
      projLeftGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (n + 1)) :=
    pullback.lift_fst _ _ _
  have e2 : segreProd.{u} n n ≫ pullback.snd _ _ =
      projRightGlued (ULift.{u} ℤ) (Fin (n + 1)) (Fin (n + 1)) :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, e1, Category.assoc, factorSwap, pullback.lift_fst, e2]
    exact segreSwapProj_comp_projLeftGlued _ _
  · rw [Category.assoc, e2, Category.assoc, factorSwap, pullback.lift_snd, e1]
    exact segreSwapProj_comp_projRightGlued _ _

end Integral

section Assembly

open Stacks.AlgebraicGeometry.SegreGlue Stacks.AlgebraicGeometry.SegreClosedImmersion
  Stacks.AlgebraicGeometry.ProjPoly

variable (n : ℕ)

/-- The involution of `Proj ℤ[x_{ij}]` exchanging the coordinates of the index, as an
isomorphism. -/
private noncomputable def pairSwapIso :
    projPoly (ULift.{u} ℤ) (Fin (n + 1) × Fin (n + 1)) ≅
      projPoly (ULift.{u} ℤ) (Fin (n + 1) × Fin (n + 1)) where
  hom := pairSwapProj (ULift.{u} ℤ) (Fin (n + 1))
  inv := pairSwapProj (ULift.{u} ℤ) (Fin (n + 1))
  hom_inv_id := pairSwapProj_comp_self _ _
  inv_hom_id := pairSwapProj_comp_self _ _

/-- The linear automorphism of the integral model of `ℙ^{n² + 2n}` exchanging the coordinates
`z_{ij}` and `z_{ji}`. -/
private noncomputable def transposeIso :
    projectiveSpaceAtUniverse.{u} (n * n + n + n) ≅ projectiveSpaceAtUniverse.{u} (n * n + n + n) :=
  (segreTargetIso n n).symm ≪≫ pairSwapIso n ≪≫ segreTargetIso n n

private lemma segreSwapSegre_comp_absoluteSegreHom :
    segreSwapSegre n ≫ absoluteSegreHom.{u} n n =
      absoluteSegreHom.{u} n n ≫ (transposeIso n).hom := by
  simp only [absoluteSegreHom, transposeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have h := congrArg (· ≫ (segreTargetIso n n).hom)
    (segreSwapProj_comp_segreProjMap (ULift.{u} ℤ) (Fin (n + 1)))
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

/-- The automorphism of `ℙ^{n² + 2n}_S` exchanging the coordinates `z_{ij}` and `z_{ji}`. -/
private noncomputable def transposeIsoOver (S : Scheme.{u}) :
    projectiveSpaceOver (n * n + n + n) S ≅ projectiveSpaceOver (n * n + n + n) S where
  hom := pullback.map _ _ _ _ (𝟙 _) (transposeIso n).hom (𝟙 _) (terminal.hom_ext _ _)
    (terminal.hom_ext _ _)
  inv := pullback.map _ _ _ _ (𝟙 _) (transposeIso n).inv (𝟙 _) (terminal.hom_ext _ _)
    (terminal.hom_ext _ _)
  hom_inv_id := by
    simp only [pullback.map_comp, Iso.hom_inv_id, Category.comp_id, pullback.map_id]
  inv_hom_id := by
    simp only [pullback.map_comp, Iso.inv_hom_id, Category.comp_id, pullback.map_id]

private lemma transposeIsoOver_hom_fst (S : Scheme.{u}) :
    (transposeIsoOver n S).hom ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private lemma transposeIsoOver_hom_snd (S : Scheme.{u}) :
    (transposeIsoOver n S).hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (transposeIso n).hom :=
  pullback.lift_snd _ _ _

end Assembly

/-- A morphism `(f, l ≫ m)` into a fibre product is a monomorphism when `m` is one and some
`(f, l ≫ r)` is: both determine `f` and `l`. -/
private lemma mono_pullback_lift_comp {C : Type*} [Category C] {X Y P Q S W : C} {f : X ⟶ S}
    {l : X ⟶ Y} {r : Y ⟶ P} {m : Y ⟶ Q} {u : S ⟶ W} {v : P ⟶ W} {v' : Q ⟶ W} [HasPullback u v]
    [HasPullback u v'] [Mono m] (w : f ≫ u = (l ≫ r) ≫ v) (w' : f ≫ u = (l ≫ m) ≫ v')
    (hr : Mono (pullback.lift f (l ≫ r) w)) : Mono (pullback.lift f (l ≫ m) w') := by
  refine ⟨fun g h hgh => ?_⟩
  have h1 : g ≫ f = h ≫ f := by
    simpa only [Category.assoc, pullback.lift_fst] using hgh =≫ pullback.fst _ _
  have h2 : g ≫ l = h ≫ l := (cancel_mono m).mp <| by
    simpa only [Category.assoc, pullback.lift_snd] using hgh =≫ pullback.snd _ _
  refine (cancel_mono (pullback.lift f (l ≫ r) w)).mp (pullback.hom_ext ?_ ?_) <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, h1, reassoc_of% h2]

/-- An abelian variety over a field has a closed immersion into some `ℙⁿ` over the field
(Stacks, Tag 0BFA). -/
private lemma exists_embedding {F : Type u} [Field F]
    (A : Over (Spec (.of F))) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom] :
    ∃ (n : ℕ) (ψ : A.left ⟶ projectiveSpaceOver n (Spec (.of F))),
      IsClosedImmersion ψ ∧ ψ ≫ pullback.fst _ _ = A.hom := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety F A.hom := .mk (toIsVariety := .mk)
  have : IsAbelianVariety F A := ⟨⟩
  have h := isProjective_of_isAbelianVariety F A
  rw [isProjective_iff_isProjectiveMorphism_of_isAffine] at h
  exact h

open Stacks.AlgebraicGeometry.SegreGlue Stacks.AlgebraicGeometry.SegreClosedImmersion in
/-- An abelian variety `A` over a field `F` admits a closed immersion `φ : A → ℙⁿ_F` over `F`
together with an automorphism `σ` of `ℙⁿ_F` over `F` such that `φ ∘ [-1] = σ ∘ φ`. In particular
`ℳ = φ^*𝒪(1)` is an ample invertible sheaf with `[-1]^*ℳ ≅ ℳ`. -/
@[faltings "lem_mw_even_ample_class"]
theorem exists_isClosedImmersion_proj_inv_comp_eq_comp {F : Type u} [Field F]
    (A : Over (Spec (.of F))) [GrpObj A] [IsProper A.hom] [GeometricallyIntegral A.hom] :
    ∃ (n : ℕ) (φ : A.left ⟶ projectiveSpaceOver n (Spec (.of F)))
      (σ : projectiveSpaceOver n (Spec (.of F)) ≅ projectiveSpaceOver n (Spec (.of F))),
      IsClosedImmersion φ ∧
      φ ≫ (projectiveSpaceOver n (Spec (.of F)) ↘ Spec (.of F)) = A.hom ∧
      σ.hom ≫ (projectiveSpaceOver n (Spec (.of F)) ↘ Spec (.of F)) =
        (projectiveSpaceOver n (Spec (.of F)) ↘ Spec (.of F)) ∧
      ι[A].left ≫ φ = φ ≫ σ.hom := by
  obtain ⟨n, ψ, hψ, hψA⟩ := exists_embedding A
  have : IsIso (segreProd.{u} n n) := Stacks.AlgebraicGeometry.SegreProdIso.isIso_segreProd n n
  set N := n * n + n + n
  let ψ' : A.left ⟶ projectiveSpaceAtUniverse.{u} n := ψ ≫ pullback.snd _ _
  let L : A.left ⟶ projectiveSpaceOver n (projectiveSpaceAtUniverse.{u} n) :=
    pullback.lift ψ' (ι[A].left ≫ ψ') (terminal.hom_ext _ _)
  let φℤ : A.left ⟶ projectiveSpaceAtUniverse.{u} N :=
    L ≫ inv (segreProd.{u} n n) ≫ absoluteSegreHom.{u} n n
  let φ₁ : A.left ⟶ projectiveSpaceOver N (Spec (.of F)) :=
    pullback.lift A.hom φℤ (terminal.hom_ext _ _)
  have hι : ι[A].left ≫ ι[A].left = 𝟙 _ := by
    rw [← Over.comp_left, GrpObj.inv_comp_inv]; rfl
  have hφ₁ : φ₁ ≫ pullback.fst _ _ = A.hom := pullback.lift_fst _ _ _
  have hL : ι[A].left ≫ L = L ≫ factorSwap n := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, factorSwap, pullback.lift_fst, pullback.lift_fst,
        pullback.lift_snd]
    · rw [Category.assoc, Category.assoc, factorSwap, pullback.lift_snd, pullback.lift_snd,
        pullback.lift_fst, ← Category.assoc, hι, Category.id_comp]
  have hswap : factorSwap n ≫ inv (segreProd.{u} n n) =
      inv (segreProd.{u} n n) ≫ segreSwapSegre n := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← segreSwapSegre_comp_segreProd, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hφℤ : ι[A].left ≫ φℤ = φℤ ≫ (transposeIso n).hom := by
    simp only [φℤ]
    rw [reassoc_of% hL, reassoc_of% hswap, segreSwapSegre_comp_absoluteSegreHom]
    simp only [Category.assoc]
  have heq : ι[A].left ≫ φ₁ = φ₁ ≫ (transposeIsoOver n _).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, transposeIsoOver_hom_fst, hφ₁, Over.w]
    · rw [Category.assoc, Category.assoc, transposeIsoOver_hom_snd, pullback.lift_snd,
        pullback.lift_snd_assoc, hφℤ]
  have hcl : IsClosedImmersion φ₁ := by
    have : IsSeparated (pullback.fst (terminal.from (Spec (.of F)))
        (terminal.from (projectiveSpaceAtUniverse.{u} N))) :=
      (isProper_projectiveSpaceOver N _).toIsSeparated
    have : IsProper (φ₁ ≫ pullback.fst _ _) := hφ₁ ▸ inferInstance
    have : IsProper φ₁ := IsProper.of_comp φ₁ (pullback.fst _ _)
    have : Mono φ₁ := by
      have : IsClosedImmersion (absoluteSegreHom.{u} n n) := isClosedImmersion_absoluteSegreHom n n
      have hψL : ψ = pullback.lift A.hom (L ≫ pullback.fst _ _) (terminal.hom_ext _ _) :=
        pullback.hom_ext (by rw [pullback.lift_fst, hψA])
          (by rw [pullback.lift_snd, pullback.lift_fst])
      exact mono_pullback_lift_comp (m := inv (segreProd.{u} n n) ≫ absoluteSegreHom.{u} n n)
        (terminal.hom_ext _ _) _ (by rw [← hψL]; infer_instance)
    exact (IsClosedImmersion.iff_isProper_and_mono φ₁).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨N, φ₁, transposeIsoOver n _, hcl, hφ₁, transposeIsoOver_hom_fst n _, heq⟩

end Faltings
