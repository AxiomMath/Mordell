module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Height.Basic
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import Mordell.BombieriVojta.Height.VeroneseB
public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Height
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Embedding
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.CompositeEmbedding
public import Mordell.Height.Weil.Veronese
public import Mordell.CurveProduct.VojtaClass
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import Mordell.BombieriVojta.Height.SegreVeroneseClass

/-!
# `h_V` is a Weil height for `V`

Let `(C, P)` be a curve of genus `g ≥ 2` over a field `k` algebraic over `ℚ` with a divisor `P`
of degree one, with the auxiliary data of Bombieri's Section 3: an integer `s ≥ 1`, a projective
embedding `φ_B` of `C × C`, an integer `N ≥ 2g + 1` and a projective embedding `φ_{NP}` of `C`. For
integers `d₁, d₂, d` with `d ≥ 1`, `δ₁ = d₁ + s d ≥ 1` and `δ₂ = d₂ + s d ≥ 1`, let
`ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ (φ_{NP} × φ_{NP})` be the Segre–Veronese composite of `φ_{NP} × φ_{NP}`
and `φ_{NdB} = Φ_{Nd} ∘ φ_B` the Veronese composite of degree `N d` of `φ_B`. Then the height
`h_V` of `Faltings.CurveWithDegreeOneDivisor.vojtaHeight` satisfies, for every pair `(z, w)` of
`k`-points of `C`, the exact equality
`N h_V(z, w) = h_{ψ_{δ₁,δ₂}}(z, w) - h(φ_{NdB}(z, w))`.
Thus `N h_V` is the height attached to the formal difference `ψ_{δ₁,δ₂} - φ_{NdB}` of projective
embeddings.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.mul_vojtaHeight_eq_height_sub_height`: the identity
  `N h_V = h_{ψ_{δ₁,δ₂}} - h_{φ_{NdB}}`.

## Implementation notes

The embeddings `φ_{NP}`, `φ_B` are pinned as the morphisms
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of a `k`-basis of the global sections of
an invertible sheaf of class `N • [𝒪(P)]`, resp.
`Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)` (the class of `B`).
The embedding `ψ_{δ₁,δ₂}` is an argument, pinned by hypotheses in the form in which
`Faltings.exists_isClosedImmersion_segreVeronese_comp` produces it, and its height is
`Faltings.ProjectiveEmbedding.height`. The underlying morphism of `ψ` is
`(φ_{NP} ×_k φ_{NP}) ≫ v`. Here `v` is a `k`-morphism `ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` whose value at the
`k`-point `([c], [c'])` is `Faltings.segreVeroneseComposite k δ₁ δ₂ h₁ h₂ id ([c], [c'])`, with
the coordinates of the target ordered by an enumeration `e`. The Veronese composite `φ_{NdB}` is
`Faltings.CurveWithDegreeOneDivisor.veroneseDB` of degree `N d`, a projective embedding of
`C ×_k C` whose target coordinates, the monomials of degree `N d`, are listed by an ordering `σ`,
and its height is `Faltings.ProjectiveEmbedding.height`. The degrees `δ₁`, `δ₂`
are natural numbers given with their defining equations in `ℤ`. The integer `d ≥ 1` is a natural
number, so that the Veronese degree `N d` is one too.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 619
-/

open Faltings (top_le_preimage_projectiveSpacePoint)

open Faltings.CurveWithDegreeOneDivisor (exists_eq_projectiveSpacePoint_of_eq_one)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SectionsToProjectiveSpace
open scoped LinearAlgebra.Projectivization
open Faltings

universe u

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

namespace Faltings

section

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section Veronese

/-- In the localization at the powers of `f`, the fraction `x^J / f^{|J|}` is the product of the
powers `(x_j / f)^{J_j}`. -/
private theorem localization_mk_finsuppProd {A ι : Type*} [CommRing A] (f : A) (x : ι → A)
    (J : ι →₀ ℕ) :
    Localization.mk (J.prod fun j m => x j ^ m)
        (⟨f ^ (J.sum fun _ m => m), ⟨_, rfl⟩⟩ : Submonoid.powers f) =
      J.prod fun j m => (Localization.mk (x j) (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f)) ^ m := by
  classical
  induction J using Finsupp.induction with
  | zero => simp
  | single_add a b g ha hb ih =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), ← ih,
      Localization.mk_pow, Localization.mk_mul]
    congr 1
    apply Subtype.ext
    simp [Finsupp.sum_add_index', pow_add]

variable {k : Type u} [Field k] {n : ℕ}

/-- In the chart ring `ℤ[T]_{(Tᵢ)}`, the fraction `T^J / Tᵢ^{|J|}` is the product of the powers
`(T_j / T_i)^{J_j}`. -/
private theorem away_mk_monomial (i : Fin (n + 1)) (J : Fin (n + 1) →₀ ℕ) (e : ℕ)
    (hJ : J.degree = e)
    (hmem : MvPolynomial.monomial J (1 : ULift.{u} ℤ) ∈ polyGrading (ULift.{u} ℤ) n (e • 1)) :
    Away.mk (polyGrading (ULift.{u} ℤ) n) (X_mem_one (ULift.{u} ℤ) n i) e
        (MvPolynomial.monomial J 1) hmem =
      J.prod fun j m => Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j ^ m := by
  have hval : ∀ x : Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i), x.val =
      algebraMap _ (Localization (Submonoid.powers (MvPolynomial.X i))) x := fun _ => rfl
  apply HomogeneousLocalization.val_injective
  rw [hval (J.prod _), map_finsuppProd]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply,
    Stacks.ProjectiveSpaceChartRatio.coordFracAt, Away.val_mk, pow_one]
  rw [← localization_mk_finsuppProd, MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  congr 2
  rw [← hJ, Finsupp.degree]
  rfl

/-- The chart `D₊(Tᵢ)` of `ℙⁿ_ℤ` pulls back to everything along its own inclusion. -/
private theorem top_le_preimage_awayι (i : Fin (n + 1)) :
    ⊤ ≤ Proj.awayι (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
        (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos ⁻¹ᵁ
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) := by
  rw [← Proj.opensRange_awayι _ _ (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos]
  exact fun x _ => ⟨x, rfl⟩

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse in
/-- A point `Spec θ ≫ awayι` of `ℙⁿ_ℤ` lies in the chart `D₊(Tᵢ)`. -/
private theorem top_le_preimage_specMap_comp_awayι {R : CommRingCat.{u}} (i : Fin (n + 1))
    (θ : CommRingCat.of (Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) ⟶ R) :
    ⊤ ≤ (Spec.map θ ≫ Proj.awayι (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
      (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos : Spec R ⟶ projectiveSpaceAtUniverse.{u} n)
        ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i) :=
  fun _ _ => top_le_preimage_awayι i trivial

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse in
/-- On a point `Spec θ ≫ awayι` of the chart `D₊(Tᵢ)` of `ℙⁿ_ℤ`, the chart value is `θ` of the
fraction. -/
private theorem intVal_specMap_comp_awayι (i : Fin (n + 1))
    (θ : CommRingCat.of (Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)) ⟶
      CommRingCat.of k) (j : Fin (n + 1)) :
    intVal (Spec.map θ ≫ Proj.awayι (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
      (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos) i (top_le_preimage_specMap_comp_awayι i θ) j =
      θ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j) := by
  unfold intVal
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map θ) _ _ ⊤ ⊤ (top_le_preimage_awayι i) le_top]
  rw [CommRingCat.comp_apply,
    Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection]
  erw [Stacks.ProjectiveSpaceChartRatio.appLE_top_top]
  have := congrArg (fun g => (Scheme.ΓSpecIso (.of k)).hom (g.hom
    (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j)))
    (Scheme.ΓSpecIso_inv_naturality θ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [← this]
  simp

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse in
open MvPolynomial in
/-- **The chart values of the Veronese image of a point.** Let `V : ℙⁿ_ℤ ⟶ ℙᴺ_ℤ` restrict on the
chart `D₊(Tᵢ)` to a morphism `g` into `D₊(y_{σ(e eᵢ)})` sending `y_{σ J} / y_{σ(e eᵢ)}` to
`T^J / Tᵢ^e`. Then the image under `V` of the point with coordinates `t`, `tᵢ = 1`, lies in
`D₊(y_{σ(e eᵢ)})`, with chart values `t^{σ⁻¹ j}`. -/
private theorem exists_intVal_projectiveSpacePoint_comp {N : ℕ} (e : ℕ)
    (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = e} ≃ Fin (N + 1))
    (V : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} N) (i : Fin (n + 1))
    (g : Spec (.of (HomogeneousLocalization.Away
          (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i))) ⟶
        Spec (.of (HomogeneousLocalization.Away
          (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)))))
    (hg : g ≫ Proj.awayι (homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
          ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) one_pos =
        Proj.awayι (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)
          ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) one_pos ≫ V)
    (hgJ : ∀ J : {I : Fin (n + 1) →₀ ℕ // I.degree = e},
      g.appTop ((Scheme.ΓSpecIso _).inv
          (HomogeneousLocalization.Away.mk _
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ _)) 1
            (MvPolynomial.X (σ J))
            ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))) =
        (Scheme.ΓSpecIso _).inv
          (HomogeneousLocalization.Away.mk _
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X _ i)) e (monomial J.1 1)
            ((mem_homogeneousSubmodule _ _).2
              (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2)))))
    (t : Fin (n + 1) → k) (hts : Ideal.span (Set.range t) = ⊤) (hti : t i = 1) :
    ∃ h : ⊤ ≤ (projectiveSpacePoint (R := .of k) t hts ≫ V) ⁻¹ᵁ
        Proj.basicOpen (polyGrading (ULift.{u} ℤ) N)
          (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩)),
      ∀ j, intVal (projectiveSpacePoint (R := .of k) t hts ≫ V) _ h j =
        (σ.symm j).1.prod fun l m => t l ^ m := by
  classical
  have h0 := top_le_preimage_projectiveSpacePoint t hts i hti
  have H : Set.range (projectiveSpacePoint (R := .of k) t hts).base ⊆
      Set.range (Proj.awayι (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
        (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos).base := by
    rintro _ ⟨a, rfl⟩
    have h1 := h0 (show a ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial)
    rw [← Proj.opensRange_awayι _ _ (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos] at h1
    rwa [← Scheme.Hom.coe_opensRange]
  set θ := Spec.preimage (IsOpenImmersion.lift _ _ H)
  have hθ : Spec.map θ ≫ Proj.awayι (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i)
      (X_mem_one (ULift.{u} ℤ) n i) Nat.one_pos = projectiveSpacePoint (R := .of k) t hts := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hθv : ∀ j, θ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) n i j) =
      t j := fun j => by
    rw [← intVal_specMap_comp_awayι i θ j,
      ← congrFun (intVal_projectiveSpacePoint t hts i hti h0) j]
    exact congrFun (intVal_congr hθ rfl _ h0) j
  obtain ⟨γ, rfl⟩ : ∃ γ, Spec.map γ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  have hγ : ∀ J : {I : Fin (n + 1) →₀ ℕ // I.degree = e},
      γ.hom (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) N
          (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩) (σ J)) =
        Away.mk (polyGrading (ULift.{u} ℤ) n) (X_mem_one (ULift.{u} ℤ) n i) e (monomial J.1 1)
          ((mem_homogeneousSubmodule _ _).2
            (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2))) := by
    intro J
    have nat := Scheme.ΓSpecIso_inv_naturality γ
    have h3 : (Scheme.ΓSpecIso _).inv.hom (γ.hom
        (Stacks.ProjectiveSpaceChartRatio.coordFracAt (ULift.{u} ℤ) N
          (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩) (σ J))) =
        (Scheme.ΓSpecIso _).inv.hom (Away.mk (polyGrading (ULift.{u} ℤ) n)
          (X_mem_one (ULift.{u} ℤ) n i) e (monomial J.1 1)
          ((mem_homogeneousSubmodule _ _).2
            (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2)))) := by
      rw [← hgJ J]
      exact ConcreteCategory.congr_hom nat _
    simpa using congrArg (Scheme.ΓSpecIso _).hom.hom h3
  have hcomp : projectiveSpacePoint (R := .of k) t hts ≫ V =
      Spec.map (γ ≫ θ) ≫ Proj.awayι (polyGrading (ULift.{u} ℤ) N)
        (MvPolynomial.X (σ ⟨Finsupp.single i e, Finsupp.degree_single i e⟩))
        (X_mem_one (ULift.{u} ℤ) N _) Nat.one_pos := by
    rw [← hθ, Category.assoc, ← hg, Spec.map_comp, Category.assoc]
  have h2 := top_le_preimage_specMap_comp_awayι _ (γ ≫ θ)
  refine ⟨hcomp ▸ h2, fun j => ?_⟩
  rw [congrFun (intVal_congr hcomp rfl _ h2) j, intVal_specMap_comp_awayι, CommRingCat.comp_apply]
  obtain ⟨J, rfl⟩ := σ.surjective j
  rw [hγ J, Equiv.symm_apply_apply, away_mk_monomial i J.1 e J.2, map_finsuppProd]
  simp [hθv]

end Veronese

section Heights

variable {k : Type u} [Field k]

private theorem ne_zero_of_span_range_eq_top {ι : Type*} {c : ι → k}
    (h : Ideal.span (Set.range c) = ⊤) : c ≠ 0 := by
  rintro rfl
  exact top_ne_bot (h.symm.trans (Ideal.span_eq_bot.2 (by rintro _ ⟨_, rfl⟩; rfl)))

private theorem span_range_eq_top_of_ne_zero {ι : Type*} {c : ι → k} (h : c ≠ 0) :
    Ideal.span (Set.range c) = ⊤ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ne.isUnit hi)

/-- The homogeneous coordinates of a `k`-point of `ℙⁿ_k` are its chart values in any chart of
`ℙⁿ_ℤ` containing its image. -/
private theorem kPointProjectivization_eq_mk_of_intVal_eq {n : ℕ}
    (y : Spec (.of k) ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hy : y ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
    (z : Spec (.of k) ⟶ projectiveSpaceAtUniverse.{u} n)
    (hz : y ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) = z) (i : Fin (n + 1))
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X i))
    (v : Fin (n + 1) → k) (hval : intVal z i h = v) (hv : v ≠ 0) :
    kPointProjectivization y hy = Projectivization.mk k v hv := by
  subst hz hval
  obtain ⟨_, heq⟩ := kPointProjectivization_eq_mk_intVal y hy i h
  exact heq

/-- The height of a `k`-point whose image lies over the point `[t]` of `ℙⁿ_ℤ` is `h([t])`. -/
private theorem height_eq_weilHeight_of_comp_eq [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f] {n : ℕ}
    (φ : ProjectiveEmbedding f n) (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _})
    (t : Fin (n + 1) → k) (hts : Ideal.span (Set.range t) = ⊤)
    (h : p.1 ≫ φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) t hts) :
    φ.height p = weilHeight (Projectivization.mk k t (ne_zero_of_span_range_eq_top hts)) := by
  rw [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization,
    kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint _ _ t hts _
      (by rw [Category.assoc]; exact h)]

variable [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]

/-- The Veronese point `[x^I]_{|I| = δ}` of `x`, in any order of the monomials, has height
`δ h(x)`. -/
private theorem weilHeight_mk_finsuppProd_rep {n : ℕ} (δ : ℕ) (hδ : 1 ≤ δ)
    [Fintype {I : Fin (n + 1) →₀ ℕ // I.degree = δ}]
    [LinearOrder {I : Fin (n + 1) →₀ ℕ // I.degree = δ}] (x : ℙ k (Fin (n + 1) → k))
    (hP : (fun I : {I : Fin (n + 1) →₀ ℕ // I.degree = δ} => I.1.prod fun i m => x.rep i ^ m) ≠
      0) :
    weilHeight (Projectivization.mk k _ hP) = δ * weilHeight x := by
  rw [← veroneseMap_mk k δ hδ x.rep x.rep_nonzero hP, Projectivization.mk_rep,
    weilHeight_veroneseMap]

/-- The point `[t^{σ⁻¹ j}]_j` of the monomials of degree `δ` in `t`, ordered by `σ`, has height
`δ h([t])`. -/
private theorem weilHeight_mk_finsuppProd_symm {n M : ℕ} (δ : ℕ) (hδ : 1 ≤ δ)
    (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = δ} ≃ Fin (M + 1)) (t : Fin (n + 1) → k)
    (ht : t ≠ 0) (hu : (fun j => (σ.symm j).1.prod fun l m => t l ^ m) ≠ 0) :
    weilHeight (Projectivization.mk k (fun j => (σ.symm j).1.prod fun l m => t l ^ m) hu) =
      δ * weilHeight (Projectivization.mk k t ht) := by
  let _ : Fintype {I : Fin (n + 1) →₀ ℕ // I.degree = δ} := Fintype.ofEquiv _ σ.symm
  let _ : LinearOrder {I : Fin (n + 1) →₀ ℕ // I.degree = δ} := LinearOrder.lift' σ σ.injective
  have hv : (fun I : {I : Fin (n + 1) →₀ ℕ // I.degree = δ} => I.1.prod fun l m => t l ^ m) ≠
      0 := fun h => hu (by funext j; exact congrFun h (σ.symm j))
  exact (weilHeight_mk_comp_equiv σ.symm _ hv hu).trans
    ((congrArg weilHeight (veroneseMap_mk k δ hδ t ht hv).symm).trans
      (weilHeight_veroneseMap δ hδ _))

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] in
/-- A `k`-point `p` of `X` whose image under `φ` lies over the point `[t]` of `ℙⁿ_ℤ` is sent by
`φ` to the point `(id, [t])` of `ℙⁿ_k = Spec k ×_ℤ ℙⁿ_ℤ`. -/
private theorem comp_hom_eq_lift {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] {n : ℕ} (φ : ProjectiveEmbedding f n)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) (t : Fin (n + 1) → k)
    (hts : Ideal.span (Set.range t) = ⊤)
    (h : p.1 ≫ φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) t hts) :
    p.1 ≫ φ.hom =
      pullback.lift (𝟙 _) (projectiveSpacePoint (R := .of k) t hts) (terminal.hom_ext _ _) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    exact (congrArg (p.1 ≫ ·) φ.hom_over).trans p.2
  · rw [pullback.lift_snd, Category.assoc]
    exact h

omit [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] in
/-- The vector of monomials of degree `δ` in the homogeneous coordinates of a point is nonzero. -/
private theorem finsuppProd_rep_ne_zero {n : ℕ} (δ : ℕ) (x : ℙ k (Fin (n + 1) → k)) :
    (fun a : {a : Fin (n + 1) →₀ ℕ // a.degree = δ} => a.1.prod fun i m => x.rep i ^ m) ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  have := congrFun h0 ⟨Finsupp.single i δ, by simp⟩
  rw [Finsupp.prod_single_index (by simp)] at this
  exact pow_ne_zero δ hi this

/-- **The height of the Segre–Veronese embedding.** Let `ψ` be the embedding of `X × X` whose
morphism is `v ∘ (φ × φ)`, where `v` sends `([x], [y])` to `[x^a y^b]_{|a| = δ₁, |b| = δ₂}`
(ordered by `e`). If `φ(z) = [x]` and `φ(w) = [y]`, then
`h_ψ(z, w) = δ₁ h([x]) + δ₂ h([y])`. -/
private theorem height_segreVeronese {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] [IsProjectiveVariety k (pullback.fst f f ≫ f)]
    [Smooth (pullback.fst f f ≫ f)] {n r : ℕ} (φ : ProjectiveEmbedding f n) {δ₁ δ₂ : ℕ}
    (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    (e : Fin (r + 1) ≃
      {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂})
    (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
    (hv : ∀ (c c' : Fin (n + 1) → k) (hc : c ≠ 0) (hc' : c' ≠ 0)
      (hcs : Ideal.span (Set.range c) = ⊤) (hcs' : Ideal.span (Set.range c') = ⊤)
      (w : {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂} →
        k) (hw : w ≠ 0) (hws : Ideal.span (Set.range (w ∘ e)) = ⊤),
      segreVeroneseComposite k δ₁ δ₂ h₁ h₂ id (.mk k c hc, .mk k c' hc') = .mk k w hw →
        pullback.lift
            (pullback.lift (𝟙 _) (projectiveSpacePoint (R := .of k) c hcs)
              (terminal.hom_ext _ _))
            (pullback.lift (𝟙 _) (projectiveSpacePoint (R := .of k) c' hcs')
              (terminal.hom_ext _ _))
            ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm) ≫ v ≫
              projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
          projectiveSpacePoint (R := .of k) (w ∘ e) hws)
    (ψ : ProjectiveEmbedding (pullback.fst f f ≫ f) r)
    (hψ : ψ.hom = pullback.map f f _ _ φ.hom φ.hom (𝟙 _)
      (by simp [φ.hom_over]) (by simp [φ.hom_over]) ≫ v)
    (z w : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _})
    (tz : Fin (n + 1) → k) (hzs : Ideal.span (Set.range tz) = ⊤)
    (hz : z.1 ≫ φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) tz hzs)
    (tw : Fin (n + 1) → k) (hws : Ideal.span (Set.range tw) = ⊤)
    (hw : w.1 ≫ φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) tw hws) :
    ψ.height ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm), by rw [pullback.lift_fst_assoc, z.2]⟩ =
      δ₁ * weilHeight (Projectivization.mk k tz (ne_zero_of_span_range_eq_top hzs)) +
        δ₂ * weilHeight (Projectivization.mk k tw (ne_zero_of_span_range_eq_top hws)) := by
  classical
  have hz0 := ne_zero_of_span_range_eq_top hzs
  have hw0 := ne_zero_of_span_range_eq_top hws
  have : Finite {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} :=
    (Finsupp.finite_of_degree_eq δ₁).to_subtype
  have : Finite {a : Fin (n + 1) →₀ ℕ // a.degree = δ₂} :=
    (Finsupp.finite_of_degree_eq δ₂).to_subtype
  let _ : Fintype {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} := Fintype.ofFinite _
  let _ : Fintype {a : Fin (n + 1) →₀ ℕ // a.degree = δ₂} := Fintype.ofFinite _
  let _ : LinearOrder {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let _ : LinearOrder {a : Fin (n + 1) →₀ ℕ // a.degree = δ₂} :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hP := finsuppProd_rep_ne_zero δ₁ (Projectivization.mk k tz hz0)
  have hQ := finsuppProd_rep_ne_zero δ₂ (Projectivization.mk k tw hw0)
  set W := fun ab : {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} ×
      {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂} =>
    (ab.1.1.prod fun i m => (Projectivization.mk k tz hz0).rep i ^ m) *
      ab.2.1.prod fun j m => (Projectivization.mk k tw hw0).rep j ^ m
  have hW : W ≠ 0 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hP
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hQ
    exact Function.ne_iff.mpr ⟨(a, b), mul_ne_zero ha hb⟩
  have hWe : W ∘ e ≠ 0 := fun h0 => hW (by
    funext ab
    obtain ⟨l, rfl⟩ := e.surjective ab
    exact congrFun h0 l)
  have hWs := span_range_eq_top_of_ne_zero hWe
  have hpsi : (pullback.lift z.1 w.1 (z.2.trans w.2.symm) ≫ ψ.hom) ≫
      projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
        projectiveSpacePoint (R := .of k) (W ∘ e) hWs := by
    rw [← hv tz tw hz0 hw0 hzs hws W hW hWs rfl, hψ]
    simp only [Category.assoc]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact (comp_hom_eq_lift φ z tz hzs hz).trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (comp_hom_eq_lift φ w tw hws hw).trans (pullback.lift_snd _ _ _).symm
  rw [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization,
    kPointProjectivization_eq_mk_of_eq_projectiveSpacePoint _ _ _ hWs hWe hpsi,
    ← weilHeight_mk_finsuppProd_rep δ₁ h₁ _ hP, ← weilHeight_mk_finsuppProd_rep δ₂ h₂ _ hQ]
  exact weilHeight_mk_mul_comp_equiv e _ _ hP hQ hWe

/-- **The height of a Veronese composite.** If `φ(p)` lies over the point `[t]` of `ℙⁿ_ℤ`, the
Veronese composite of degree `D` of `φ` has height `D h([t])` at `p`. -/
private theorem height_exists_veronese {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] {n : ℕ} (φ : ProjectiveEmbedding f n) (D : ℕ)
    (hD : 1 ≤ D) {M : ℕ} (σ : {I : Fin (n + 1) →₀ ℕ // I.degree = D} ≃ Fin (M + 1))
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) (t : Fin (n + 1) → k)
    (hts : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1)) (hti : t i = 1)
    (hp : p.1 ≫ φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of k) t hts) :
    (φ.exists_veronese D hD M σ).choose_spec.choose.height p =
      D * weilHeight (Projectivization.mk k t (ne_zero_of_span_range_eq_top hts)) := by
  have hspec := (φ.exists_veronese D hD M σ).choose_spec.choose_spec
  obtain ⟨g, hg, hgJ⟩ := hspec.1 i
  obtain ⟨hh, hval⟩ := exists_intVal_projectiveSpacePoint_comp D σ _ i g hg hgJ t hts hti
  have hu : (fun j => (σ.symm j).1.prod fun l m => t l ^ m) ≠ 0 := fun h0 => by
    have := congrFun h0 (σ ⟨Finsupp.single i D, Finsupp.degree_single i D⟩)
    rw [Equiv.symm_apply_apply, Finsupp.prod_single_index (by simp), hti, one_pow] at this
    exact one_ne_zero this
  have hcomp : (p.1 ≫ (φ.exists_veronese D hD M σ).choose_spec.choose.hom) ≫
      projectiveSpaceOver.toIntegralAtUniverse M (Spec (.of k)) =
        projectiveSpacePoint (R := .of k) t hts ≫ (φ.exists_veronese D hD M σ).choose := by
    rw [Category.assoc, hspec.2, ← hp]
    simp only [Category.assoc]
  rw [ProjectiveEmbedding.height_eq_weilHeight_kPointProjectivization,
    kPointProjectivization_eq_mk_of_intVal_eq _ _ _ hcomp _ hh _ (funext hval) hu,
    weilHeight_mk_finsuppProd_symm D hD σ t _ hu]

end Heights

end

/-- **`h_V` is a Weil height for `V`.** Let `X = (C, P)` be a curve with a divisor of degree
one over a field `k` algebraic over `ℚ`, `φNP` a projective embedding of `C`, `φB` one of
`C ×_k C`, given by `k`-bases of the global sections of invertible sheaves of classes
`N • [𝒪(P)]` and `vojtaClass X s s (-1)`, of genus `g ≥ 2`, `s ≥ 1`, `N ≥ 2g + 1`, `d ≥ 1`, and
`δ₁ = d₁ + s d ≥ 1`, `δ₂ = d₂ + s d ≥ 1`. Let `ψ` be the Segre–Veronese composite
`v ∘ (φNP ×_k φNP)` of bidegree `(δ₁, δ₂)`, and `φ_{NdB} = X.veroneseDB φB (N * d) _ M σ` the
Veronese composite of degree `N d` of `φB`. Then for all `k`-points `z, w` of `C`
`N · vojtaHeight X φNP φB s N d₁ d₂ d z w = h_ψ(z, w) - h_{φ_{NdB}}(z, w)`. -/
@[faltings "prop_bv_height_vojta_is_weil_height"]
public theorem CurveWithDegreeOneDivisor.mul_vojtaHeight_eq_height_sub_height {k : Type u}
    [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) {n m : ℕ}
    (φNP : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (s : ℤ) (hs : 1 ≤ s) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (LB : (pullback X.f X.f).Modules) [hLBinv : Stacks.Ample.IsInvertibleModule _ LB]
    (hM : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) LB
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ LB hLBinv) =
      X.vojtaClass s s (-1))
    (hφ : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
      letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
      (∃ (x : Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
        (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
        φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f) ∧
      ∃ (y : Module.Basis (Fin (m + 1)) k Γ(LB, ⊤))
        (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y),
        φB.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
          (pullback.fst X.f X.f ≫ X.f))
    (d₁ d₂ : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (δ₁ δ₂ : ℕ) (hδ₁ : (δ₁ : ℤ) = d₁ + s * d) (hδ₂ : (δ₂ : ℤ) = d₂ + s * d)
    (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    {r : ℕ}
    (e : Fin (r + 1) ≃
      {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂})
    (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
    (hv : ∀ (c c' : Fin (n + 1) → k) (hc : c ≠ 0) (hc' : c' ≠ 0)
      (hcs : Ideal.span (Set.range c) = ⊤) (hcs' : Ideal.span (Set.range c') = ⊤)
      (w : {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂} →
        k) (hw : w ≠ 0) (hws : Ideal.span (Set.range (w ∘ e)) = ⊤),
      segreVeroneseComposite k δ₁ δ₂ h₁ h₂ id (.mk k c hc, .mk k c' hc') = .mk k w hw →
        pullback.lift
            (pullback.lift (𝟙 _) (projectiveSpacePoint (R := .of k) c hcs)
              (terminal.hom_ext _ _))
            (pullback.lift (𝟙 _) (projectiveSpacePoint (R := .of k) c' hcs')
              (terminal.hom_ext _ _))
            ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm) ≫ v ≫
              projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
          projectiveSpacePoint (R := .of k) (w ∘ e) hws)
    (ψ : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) r)
    (hψ : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ψ.hom = pullback.map X.f X.f _ _ φNP.hom φNP.hom (𝟙 _)
      (by simp [φNP.hom_over]) (by simp [φNP.hom_over]) ≫ v)
    {M : ℕ} (σ : {I : Fin (m + 1) →₀ ℕ // I.degree = N * d} ≃ Fin (M + 1))
    (z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _}) :
    haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
    haveI : SmoothOfRelativeDimension 2 (pullback.fst X.f X.f ≫ X.f) :=
      (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
    haveI : Smooth (pullback.fst X.f X.f ≫ X.f) :=
      SmoothOfRelativeDimension.smooth 2 (pullback.fst X.f X.f ≫ X.f)
    N * X.vojtaHeight φNP φB s N d₁ d₂ d z w =
      ψ.height ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
          by rw [pullback.lift_fst_assoc, z.2]⟩ -
        (X.veroneseDB φB (N * d) (Nat.mul_le_mul ((Nat.le_add_left 1 _).trans hN) hd) M σ).height
          ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
            by rw [pullback.lift_fst_assoc, z.2]⟩ := by
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  have := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
  have : Smooth (pullback.fst X.f X.f ≫ X.f) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨-, tz, hzs, -, hz⟩ := exists_eq_projectiveSpacePoint_of_eq_one
    (z.1 ≫ φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  obtain ⟨-, tw, hws, -, hw⟩ := exists_eq_projectiveSpacePoint_of_eq_one
    (w.1 ≫ φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  obtain ⟨ip, tp, hps, hpi, hp⟩ := exists_eq_projectiveSpacePoint_of_eq_one
    (pullback.lift z.1 w.1 (z.2.trans w.2.symm) ≫ φB.hom ≫
      projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
  rw [height_segreVeronese φNP h₁ h₂ e v hv ψ hψ z w tz hzs hz tw hws hw,
    show (X.veroneseDB φB _ _ M σ).height _ = _ from
      height_exists_veronese φB _ (Nat.mul_le_mul ((Nat.le_add_left 1 _).trans hN) hd) σ _ tp
        hps ip hpi hp,
    CurveWithDegreeOneDivisor.vojtaHeight, height_eq_weilHeight_of_comp_eq φNP z tz hzs hz,
    height_eq_weilHeight_of_comp_eq φNP w tw hws hw,
    height_eq_weilHeight_of_comp_eq φB _ tp hps hp]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← hδ₁, ← hδ₂]
  field_simp
  push_cast
  ring

end Faltings
