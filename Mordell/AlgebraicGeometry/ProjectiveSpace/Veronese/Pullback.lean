module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic

/-!
# Pullback of `𝒪(1)` under the Veronese map

Let `e ≥ 1`. The Veronese morphism of degree `e`, `Φ_e : ℙⁿ ⟶ ℙᴺ` with
`N + 1 = binom (n + e) n`, has as homogeneous coordinates `y_J` the monomials `x^J` of degree `e`.
It pulls the hyperplane sheaf back to the twisting sheaf of degree `e`: `Φ_e^* 𝒪(1) ≅ 𝒪(e)` as
modules on `ℙⁿ`.

The proof factors `Φ_e` as `Proj ℤ[x] ≅ Proj ℤ[x]^{(e)} ⟶ Proj ℤ[y]`: the Veronese isomorphism,
followed by `Proj` of the graded surjection `ℤ[y] → ℤ[x]^{(e)}`, `y_{σ J} ↦ x^J`, onto the
Veronese subring graded by `ℤ[x]^{(e)}_m = ℤ[x]_{me}`. The first identifies `𝒪(e)` with the
pullback of `𝒪(1)`, and `Proj` of a graded surjection generated in degree one pulls `𝒪(1)` back
to `𝒪(1)`. That `Φ_e` is this composite is checked on the charts `D₊(x_i)`, where both are `Spec`
of a ring map out of `ℤ[y]_{(y_{σ (e • eᵢ)})}` determined by its values `x^J / x_i ^ e` on the
affine coordinates.

## Main results

* `Faltings.nonempty_pullback_veronese_twistingSheafAtUniverse_iso`: `Φ_e^* 𝒪(1) ≅ 𝒪(e)` on the
  integral model `ℙⁿ_ℤ`.

## Implementation notes

The statement is made on the integral models
`AlgebraicGeometry.projectiveSpaceAtUniverse n = Proj ℤ[x₀, …, xₙ]`, with
`𝒪(1) = Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse N` on `ℙᴺ_ℤ` and
`𝒪(e) = ProjectiveSpectrum.Proj.twistingSheaf _ e` on `ℙⁿ_ℤ`; projective space over any base `S`
and its hyperplane sheaf are pulled back from these, so the isomorphism over `S` follows by
pullback. The Veronese morphism `V` is pinned, as in
`Faltings.ProjectiveEmbedding.exists_veronese`, by its charts: for an ordering `σ` of the monomials
of degree `e`, `V` maps `D₊(x_i)` into `D₊(y_{σ (e • eᵢ)})` and pulls `y_{σ J} / y_{σ (e • eᵢ)}`
back to `x^J / x_i ^ e`. These conditions determine `V`. The source works over `Q̄`.

## References

* [Hartshorne, *Algebraic Geometry*, II Ex. 5.13][hartshorne1977]
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open Stacks.AmpleProjectiveImmersion
open Stacks.Veronese (veroneseSubring veroneseGrading veronesePower)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Faltings

variable {R : Type u} [CommRing R] {ι κ : Type*} {e : ℕ}
  (σ : {I : ι →₀ ℕ // I.degree = e} ≃ κ)

private theorem veroneseAlgHom_mem_veroneseSubring (p : MvPolynomial κ R) :
    veroneseAlgHom σ p ∈ veroneseSubring (homogeneousSubmodule ι R) e := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine Stacks.Veronese.mem_veroneseSubring_of_mem _ (n := 0) ?_
    rw [veroneseAlgHom, aeval_C, algebraMap_eq, zero_mul]
    exact (mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ _)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p k hp =>
    rw [map_mul]
    refine mul_mem hp (Stacks.Veronese.mem_veroneseSubring_of_mem _ (n := 1) ?_)
    rw [veroneseAlgHom, aeval_X, one_mul]
    exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (σ.symm k).2)

/-- `y_{σ J} ↦ x^J`, into the Veronese subring `R[x]^{(e)}`. -/
private noncomputable def veroneseHom :
    MvPolynomial κ R →+* veroneseSubring (homogeneousSubmodule ι R) e :=
  (veroneseAlgHom σ).toRingHom.codRestrict _ (veroneseAlgHom_mem_veroneseSubring σ)

/-- `y_{σ J} ↦ x^J` as a graded map `R[y] → R[x]^{(e)}`. -/
private noncomputable def veroneseGradedHom :
    homogeneousSubmodule κ R →+*ᵍ veroneseGrading (homogeneousSubmodule ι R) e where
  toRingHom := veroneseHom σ
  map_mem hp := veroneseAlgHom_mem σ hp

private theorem veroneseGradedHom_apply (p : MvPolynomial κ R) :
    ((veroneseGradedHom σ p : veroneseSubring (homogeneousSubmodule ι R) e) :
      MvPolynomial ι R) = veroneseAlgHom σ p := rfl

private theorem veroneseGradedHom_surjective :
    Function.Surjective (veroneseGradedHom (R := R) σ) := by
  rintro ⟨y, hy⟩
  have : y ∈ (veroneseAlgHom (R := R) σ).toRingHom.range.toAddSubgroup := by
    rw [Stacks.Veronese.mem_veroneseSubring_iff] at hy
    refine (AddSubgroup.closure_le _).2 ?_ hy
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hx
    obtain ⟨p, -, hp⟩ := exists_mem_eq σ m hm
    exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := this
  exact ⟨p, Subtype.ext hp⟩

/-- The Veronese subring of a graded ring is graded, for a positive degree supplied as a `Fact`. -/
private noncomputable abbrev veroneseGradedRing {A : Type*} [CommRing A] {τ : Type*} [SetLike τ A]
    [AddSubgroupClass τ A] (𝒜 : ℕ → τ) [GradedRing 𝒜] (d : ℕ) [Fact (0 < d)] :
    GradedRing (veroneseGrading 𝒜 d) :=
  Stacks.Veronese.veroneseGradingGradedRing 𝒜 d Fact.out

attribute [local instance] veroneseGradedRing

/-- Ring maps out of the chart `ℤ[x]_{(x_k)}` agreeing on the affine coordinates `x_j / x_k`
are equal. -/
private theorem away_X_ringHom_ext {N : ℕ} (k : Fin (N + 1)) {T : Type*} [CommRing T]
    {φ ρ : Away (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) (X k) →+* T}
    (h : ∀ j, φ (Away.mk _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ k)) 1 (X j)
        ((mem_homogeneousSubmodule _ _).2 (by simpa using isHomogeneous_X _ j))) =
      ρ (Away.mk _ ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ k)) 1 (X j)
        ((mem_homogeneousSubmodule _ _).2 (by simpa using isHomogeneous_X _ j)))) :
    φ = ρ := by
  open Stacks.AlgebraicGeometry.ProjPolyChart in
  have key : φ.comp (chartHom (ULift.{u} ℤ) N k) = ρ.comp (chartHom (ULift.{u} ℤ) N k) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have hφ : ∀ ψ : ULift.{u} ℤ →+* T, ψ r = (r.down : T) := fun ψ => by
        conv_lhs => rw [show r = ((r.down : ℤ) : ULift.{u} ℤ) from ULift.ext (by simp)]
        exact map_intCast ψ _
      simp only [RingHom.comp_apply, chartHom_C]
      exact (hφ (φ.comp (coeffToAway _ N k))).trans (hφ (ρ.comp (coeffToAway _ N k))).symm
    · simp only [RingHom.comp_apply, chartHom_X]
      exact h j.1
  open Stacks.AlgebraicGeometry.ProjPolyChart in
  ext z
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) N k z
  exact congrArg (fun f => f p) key

section Charts

variable {n N e : ℕ} [Fact (0 < e)] (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = e} ≃ Fin (N + 1))

omit [Fact (0 < e)] in
private theorem veronesePower_eq (i : Fin (n + 1)) :
    veronesePower (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) e (X i)
        (X_mem (ULift.{u} ℤ) i) =
      veroneseGradedHom (R := ULift.{u} ℤ) σ (X (σ (singleIdx i))) * 1 := by
  rw [mul_one]
  apply Subtype.ext
  rw [Stacks.Veronese.coe_veronesePower, veroneseGradedHom_apply, veroneseAlgHom_X,
    X_pow_eq_monomial]

/-- The ring map of the Veronese morphism on the chart `D₊(x_i) ⟶ D₊(y_{σ (e • eᵢ)})`. -/
private noncomputable def chartRingHom (i : Fin (n + 1)) :
    Away (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) (X (σ (singleIdx i))) →+*
      Away (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i) :=
  (Stacks.Veronese.veroneseAwayEquiv _ e (X i) (X_mem (ULift.{u} ℤ) i) Fact.out).toRingHom.comp
    ((awayMap (veroneseGrading _ e) SetLike.GradedOne.one_mem (veronesePower_eq σ i)).comp
      (Away.map (veroneseGradedHom (R := ULift.{u} ℤ) σ) (X (σ (singleIdx i)))))

private theorem chartRingHom_mk (i : Fin (n + 1)) (J : {I : Fin (n + 1) →₀ ℕ // I.degree = e}) :
    chartRingHom σ i (Away.mk _ (X_mem (ULift.{u} ℤ) _) 1 (X (σ J))
        ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _))) =
      Away.mk _ (X_mem (ULift.{u} ℤ) i) e (monomial J.1 1)
        ((mem_homogeneousSubmodule _ _).2
          (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2))) := by
  simp only [chartRingHom, RingHom.comp_apply, Away.map_mk, awayMap_mk]
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    Stacks.Veronese.veroneseAwayEquiv_mk (hxS := by
      simp only [smul_eq_mul, mul_one, one_mul, one_pow, veroneseGradedHom_apply,
        veroneseAlgHom_X]
      exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ J.2))]
  refine away_mk_congr _ _ (one_mul e) ?_ _ _
  rw [one_pow, mul_one, veroneseGradedHom_apply, veroneseAlgHom_X]

private theorem veroneseGradedHom_irrelevant :
    HomogeneousIdeal.irrelevant
        (veroneseGrading (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) e) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))).map
        (veroneseGradedHom σ) :=
  Proj.irrelevant_le_map_of_surjective _ (veroneseGradedHom_surjective σ)

/-- The Veronese morphism `Proj ℤ[x] ≅ Proj ℤ[x]^{(e)} ⟶ Proj ℤ[y]`. -/
private noncomputable def veroneseModel :
    AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) :=
  (Stacks.Veronese.veroneseProjIso _ e Fact.out).hom ≫
    Proj.map (veroneseGradedHom σ) (veroneseGradedHom_irrelevant σ)

private theorem awayι_comp_veroneseModel (i : Fin (n + 1)) :
    Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i) (X_mem (ULift.{u} ℤ) i)
        one_pos ≫ veroneseModel σ =
      Spec.map (CommRingCat.ofHom (chartRingHom σ i)) ≫
        Proj.awayι _ (X (σ (singleIdx i))) (X_mem (ULift.{u} ℤ) _) one_pos := by
  rw [veroneseModel, ← Category.assoc]
  erw [Stacks.Veronese.awayι_comp_veroneseProjHom]
  have h := Proj.SpecMap_awayMap_awayι (veroneseGrading
    (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) e)
    ((veroneseGradedHom σ).2 (X_mem (ULift.{u} ℤ) (σ (singleIdx i)))) one_pos
    SetLike.GradedOne.one_mem (veronesePower_eq σ i)
  erw [← h]
  rw [Category.assoc, Category.assoc]
  erw [Proj.awayι_comp_map (veroneseGradedHom σ) (veroneseGradedHom_irrelevant σ) one_pos
    (X (σ (singleIdx i))) (X_mem (ULift.{u} ℤ) _)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

/-- **The Veronese morphism is determined by its charts.** A morphism `V` mapping each chart
`D₊(x_i)` into `D₊(y_{σ (e • eᵢ)})` and pulling `y_{σ J} / y_{σ (e • eᵢ)}` back to
`x^J / x_i ^ e` is `veroneseModel σ`. -/
private theorem eq_veroneseModel
    (V : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hV : ∀ i : Fin (n + 1),
      ∃ g : Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))) ⟶
          Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)))),
        g ≫ Proj.awayι (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) one_pos =
          Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) one_pos ≫ V ∧
        ∀ J : {I : Fin (n + 1) →₀ ℕ // I.degree = e},
          g.appTop ((Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) 1
                (MvPolynomial.X (σ J))
                ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))) =
            (Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) e (monomial J.1 1)
                ((mem_homogeneousSubmodule _ _).2
                  (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2))))) :
    V = veroneseModel σ := by
  refine (Proj.affineOpenCoverOfIrrelevantLESpan
    (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) X (X_mem (ULift.{u} ℤ)) (fun _ => one_pos)
    (Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_span_X _ n)).openCover.hom_ext _ _
    fun (i : Fin (n + 1)) => ?_
  obtain ⟨g, hg, hgJ⟩ := hV i
  change Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i) (X_mem (ULift.{u} ℤ) i)
      one_pos ≫ V =
    Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i) (X_mem (ULift.{u} ℤ) i)
      one_pos ≫ veroneseModel σ
  rw [awayι_comp_veroneseModel]
  erw [← hg]
  congr 1
  obtain ⟨φ, rfl⟩ : ∃ φ, g = Spec.map φ := ⟨Spec.preimage g, (Spec.map_preimage g).symm⟩
  congr 1
  ext1
  refine away_X_ringHom_ext _ fun j => ?_
  obtain ⟨J, rfl⟩ := σ.surjective j
  have h2 := congrArg (fun f => f.hom (Away.mk _ (X_mem (ULift.{u} ℤ) _) 1 (X (σ J))
        ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _))))
    (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h4 := congrArg (Scheme.ΓSpecIso _).hom.hom (h2.trans (hgJ J))
  simp only [Iso.inv_hom_id_apply] at h4
  rw [h4, CommRingCat.hom_ofHom, chartRingHom_mk]

/-- **`V^* 𝒪(1) ≅ 𝒪(e)` for the Veronese morphism of integral models.** The isomorphism
`Proj ℤ[x] ≅ Proj ℤ[x]^{(e)}` identifies `𝒪(e)` with the pullback of `𝒪(1)`, and the graded
surjection `ℤ[y] → ℤ[x]^{(e)}` pulls `𝒪(1)` back to `𝒪(1)`. -/
private noncomputable def pullbackVeroneseModelIso :
    (Scheme.Modules.pullback (veroneseModel σ)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ)) 1) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ) :=
  ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (Stacks.Veronese.veroneseProjIso _ e Fact.out).hom).mapIso
      (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
        (veroneseGradedHom σ) (veroneseGradedHom_irrelevant σ) (veroneseGradedHom_surjective σ)
        (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top _ _) 1) ≪≫
    (Stacks.Veronese.veroneseTwistingSheafIso _ e Fact.out 1).symm ≪≫
    eqToIso (by rw [one_mul])

end Charts

/-- **Pullback of `𝒪(1)` under the Veronese map.** Let `V : ℙⁿ_ℤ ⟶ ℙᴺ_ℤ` be the Veronese
morphism of degree `e`, whose coordinates are the monomials of degree `e` ordered by `σ`, given on
the charts `D₊(x_i)` by `y_{σ J} / y_{σ (e • eᵢ)} ↦ x^J / x_i ^ e`. Then `V^* 𝒪(1) ≅ 𝒪(e)`. -/
@[faltings "lem_ht_veronese_pullback"]
public theorem nonempty_pullback_veronese_twistingSheafAtUniverse_iso
    {n : ℕ} (e : ℕ) (he : 1 ≤ e) (N : ℕ)
    (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = e} ≃ Fin (N + 1))
    (V : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N)
    (hV : ∀ i : Fin (n + 1),
      ∃ g : Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))) ⟶
          Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)))),
        g ≫ Proj.awayι (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) one_pos =
          Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) one_pos ≫ V ∧
        ∀ J : {I : Fin (n + 1) →₀ ℕ // I.degree = e},
          g.appTop ((Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) 1
                (MvPolynomial.X (σ J))
                ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))) =
            (Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) e (monomial J.1 1)
                ((mem_homogeneousSubmodule _ _).2
                  (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2))))) :
    Nonempty ((Scheme.Modules.pullback V).obj (twistingSheafAtUniverse.{u} N) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ)) := by
  have : Fact (0 < e) := ⟨he⟩
  obtain rfl := eq_veroneseModel σ V hV
  exact ⟨pullbackVeroneseModelIso σ⟩

end Faltings
