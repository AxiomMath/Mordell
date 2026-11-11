module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.BasicUnconditional
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Morphism

/-!
# The Segre–Veronese composite of a projective embedding is a projective embedding

Let `k` be a number field, `X` a smooth projective geometrically integral curve of genus
`g ≥ 2` over `k` with a divisor `P` of degree one, and `φ : X ⟶ ℙⁿ_k` a closed immersion over
`k` (in Bombieri's setting `φ = φ_{NP}`). Then `ψ = φ ×_k φ : X ×_k X ⟶ ℙⁿ_k ×_k ℙⁿ_k` is a
closed immersion, being a product of closed immersions. For `δ₁, δ₂ ≥ 1` the Segre–Veronese
morphism `v_{δ₁,δ₂} : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙ^{M-1}_k`, given by all monomials `x^a x'^b` of bidegree
`(δ₁, δ₂)`, is a closed immersion (Veronese embeddings of the two factors followed by the Segre
embedding) defined over `k`. Hence `ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ ψ` is a closed immersion
`X ×_k X ⟶ ℙ^{M-1}_k` over `k`: a projective embedding of `X ×_k X` defined over `k`.

## Main results

* `Faltings.exists_isClosedImmersion_segreVeronese_comp`: for every enumeration of the monomials
  of bidegree `(δ₁, δ₂)` there is a `k`-morphism `v_{δ₁,δ₂}` sending the `K`-point
  `([c], [c'])` to the point `Faltings.segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id ([c], [c'])`, for
  every field `K` over `k`, and `v_{δ₁,δ₂} ∘ (φ ×_k φ)` is a closed immersion over `k`.

## Implementation notes

`ℙʳ_k` is `projectiveSpaceOver r (Spec k)`, the base change of `ℙʳ_ℤ`. The morphism `v_{δ₁,δ₂}`
is characterized by its values on `K`-points for all fields `K` over `k`, where it is the map
`Faltings.segreVeroneseComposite` with `ψ = id`; since `ℙⁿ_k ×_k ℙⁿ_k` is reduced and of finite
type over `k`, this determines it. A `K`-point with homogeneous coordinates `c` is
`projectiveSpacePoint c` on the integral model, lifted over `Spec K ⟶ Spec k`. The homogeneous
coordinates of the target are indexed through an enumeration `e` of the monomials of bidegree
`(δ₁, δ₂)`; the statement holds for every enumeration. That the composite is defined over `k`
is that it is a morphism over `Spec k`.

The morphism `v_{δ₁,δ₂}` is built on the integral model, as the morphism
`Faltings.segreVeroneseHom : Y ⟶ ℙʳ_ℤ` attached to any pair of morphisms `Y ⟶ ℙⁿ_ℤ`, glued from
the product charts `D₊(x_i) × D₊(y_j)`: there it is the morphism of the family
`x^a y^b / (x_i^{δ₁} y_j^{δ₂})`, which spans the unit ideal, and on an overlap two such families
differ by the unit `(x_{i'}/x_i)^{δ₁} (y_{j'}/y_j)^{δ₂}`. It is natural in `Y`. On the chart
`D₊(z_{(δ₁ e_i, δ₂ e_j)})` of the target the coordinates include the ratios `x_k / x_i` and
`y_l / y_j`, which recover both factors, so `v_{δ₁,δ₂}` is injective on pairs of morphisms, that
is, a monomorphism. Rather than composing Veronese and Segre embeddings, the composite
`v_{δ₁,δ₂} ∘ (φ ×_k φ)` is then a closed immersion as a monomorphism from a scheme proper over
`k` (`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`).

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 3, p. 619][bombieri1990]
-/

open Faltings.CurveWithDegreeOneDivisor (basicOpen_coord coord coord_self eq_of_toPSAU_eq
  eq_toPSAU_coord hom_ext_piece isOpenCover_piece piece piece_fst piece_snd preimage_ι_comp_eq_top
  projectiveSpacePoint_congr)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings

variable {n : ℕ}

/-! ### Monomials with one exponent lowered -/

section Monomial

variable {R : Type*} [CommRing R] {δ₁ δ₂ : ℕ}

/-- The exponents of `x_i ^ (δ₁ - 1) x_k y_j ^ δ₂`. -/
private noncomputable def edge₁ (h₁ : 1 ≤ δ₁) (δ₂ : ℕ) (i k j : Fin (n + 1)) :
    BidegreeExponent n δ₁ δ₂ :=
  (⟨Finsupp.single i (δ₁ - 1) + Finsupp.single k 1, by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]; omega⟩,
    ⟨Finsupp.single j δ₂, by simp⟩)

private theorem bidegreeMonomial_edge₁ (h₁ : 1 ≤ δ₁) (x y : Fin (n + 1) → R)
    (i k j : Fin (n + 1)) :
    bidegreeMonomial x y (edge₁ h₁ δ₂ i k j) = x i ^ (δ₁ - 1) * x k * y j ^ δ₂ := by
  simp only [bidegreeMonomial, edge₁]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun k e => x k ^ e) (pow_zero _),
    Finsupp.prod_single_index (h := fun k e => x k ^ e) (pow_zero _),
    Finsupp.prod_single_index (h := fun k e => y k ^ e) (pow_zero _), pow_one]

/-- The exponents of `x_i ^ δ₁ y_j ^ (δ₂ - 1) y_l`. -/
private noncomputable def edge₂ (δ₁ : ℕ) (h₂ : 1 ≤ δ₂) (i j l : Fin (n + 1)) :
    BidegreeExponent n δ₁ δ₂ :=
  (⟨Finsupp.single i δ₁, by simp⟩,
    ⟨Finsupp.single j (δ₂ - 1) + Finsupp.single l 1, by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]; omega⟩)

private theorem bidegreeMonomial_edge₂ (h₂ : 1 ≤ δ₂) (x y : Fin (n + 1) → R)
    (i j l : Fin (n + 1)) :
    bidegreeMonomial x y (edge₂ δ₁ h₂ i j l) = x i ^ δ₁ * (y j ^ (δ₂ - 1) * y l) := by
  simp only [bidegreeMonomial, edge₂]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun k e => x k ^ e) (pow_zero _),
    Finsupp.prod_single_index (h := fun k e => y k ^ e) (pow_zero _),
    Finsupp.prod_single_index (h := fun k e => y k ^ e) (pow_zero _), pow_one]

end Monomial

/-! ### Injectivity of the Segre–Veronese morphism -/

section Properties

variable {δ₁ δ₂ r : ℕ} (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)
variable {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n)

private theorem piece_le_preimage_segreVeroneseHom (i j : Fin (n + 1)) :
    piece f₁ f₂ (i, j) ≤
      segreVeroneseHom e f₁ f₂ ⁻¹ᵁ chartOpen.{u} (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) := by
  intro y hy
  have hpre : ((piece f₁ f₂ (i, j)).ι ≫ segreVeroneseHom e f₁ f₂) ⁻¹ᵁ
      chartOpen.{u} (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) = ⊤ := by
    rw [ι_segreVeroneseHom, preimage_basicOpen, svLocal_corner, Scheme.basicOpen_one]
  exact hpre.ge (x := ⟨y, hy⟩) trivial

private theorem preimage_segreVeroneseHom_le_piece (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    (i j : Fin (n + 1)) :
    segreVeroneseHom e f₁ f₂ ⁻¹ᵁ chartOpen.{u} (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) ≤
      piece f₁ f₂ (i, j) := by
  intro y hy
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp ((isOpenCover_piece f₁ f₂).ge trivial)
  have hle : ((piece f₁ f₂ q).ι ≫ segreVeroneseHom e f₁ f₂) ⁻¹ᵁ
      chartOpen.{u} (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) ≤
      ((piece f₁ f₂ q).ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} i ⊓
        ((piece f₁ f₂ q).ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} j := by
    rw [ι_segreVeroneseHom, preimage_basicOpen]
    simp only [svLocal, Equiv.apply_symm_apply, bidegreeMonomial_corner]
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ (show 0 < δ₁ by omega),
      Scheme.basicOpen_pow _ _ (show 0 < δ₂ by omega), basicOpen_coord, basicOpen_coord]
  exact hle (x := ⟨y, hq⟩) hy

/-- **The Segre–Veronese morphism is injective on pairs of morphisms**, for `δ₁, δ₂ ≥ 1`: on
the chart `D₊(z_{(δ₁ e_i, δ₂ e_j)})` its coordinates include the ratios `x_k / x_i` and
`y_l / y_j`, which recover both factors. -/
public theorem segreVeroneseHom_injective (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) :
    Function.Injective fun f : (Y ⟶ projectiveSpaceAtUniverse.{u} n) ×
      (Y ⟶ projectiveSpaceAtUniverse.{u} n) => segreVeroneseHom e f.1 f.2 := by
  rintro ⟨f₁, f₂⟩ ⟨f₁', f₂'⟩ (heq : segreVeroneseHom e f₁ f₂ = segreVeroneseHom e f₁' f₂')
  have key : ∀ p : Fin (n + 1) × Fin (n + 1),
      (piece f₁ f₂ p).ι ≫ f₁ = (piece f₁ f₂ p).ι ≫ f₁' ∧
        (piece f₁ f₂ p).ι ≫ f₂ = (piece f₁ f₂ p).ι ≫ f₂' := by
    rintro ⟨i, j⟩
    have hle : piece f₁ f₂ (i, j) ≤ piece f₁' f₂' (i, j) :=
      (piece_le_preimage_segreVeroneseHom e f₁ f₂ i j).trans
        (heq ▸ preimage_segreVeroneseHom_le_piece e f₁' f₂' h₁ h₂ i j)
    have k₁ : ((piece f₁ f₂ (i, j)).ι ≫ f₁') ⁻¹ᵁ chartOpen.{u} i = ⊤ :=
      preimage_ι_comp_eq_top f₁' _ (hle.trans inf_le_left)
    have k₂ : ((piece f₁ f₂ (i, j)).ι ≫ f₂') ⁻¹ᵁ chartOpen.{u} j = ⊤ :=
      preimage_ι_comp_eq_top f₂' _ (hle.trans inf_le_right)
    have hA := ι_segreVeroneseHom e f₁ f₂ (i, j)
    have hB := comp_segreVeroneseHom_chart e f₁' f₂' (piece f₁ f₂ (i, j)).ι i j k₁ k₂
    rw [← heq, hA] at hB
    have hfam := eq_of_toPSAU_eq _ _ _ _ hB (e.symm (BidegreeExponent.corner δ₁ δ₂ i j))
      (svLocal_corner e _ _ i j _ _) (svLocal_corner e _ _ i j _ _)
    have c₁ : coord ((piece f₁ f₂ (i, j)).ι ≫ f₁) i (piece_fst f₁ f₂ (i, j)) =
        coord ((piece f₁ f₂ (i, j)).ι ≫ f₁') i k₁ := by
      funext k
      have := congrFun hfam (e.symm (edge₁ h₁ δ₂ i k j))
      simpa only [svLocal, Equiv.apply_symm_apply, bidegreeMonomial_edge₁, coord_self, one_pow,
        one_mul, mul_one] using this
    have c₂ : coord ((piece f₁ f₂ (i, j)).ι ≫ f₂) j (piece_snd f₁ f₂ (i, j)) =
        coord ((piece f₁ f₂ (i, j)).ι ≫ f₂') j k₂ := by
      funext l
      have := congrFun hfam (e.symm (edge₂ δ₁ h₂ i j l))
      simpa only [svLocal, Equiv.apply_symm_apply, bidegreeMonomial_edge₂, coord_self, one_pow,
        one_mul, mul_one] using this
    constructor
    · rw [eq_toPSAU_coord ((piece f₁ f₂ (i, j)).ι ≫ f₁) i (piece_fst f₁ f₂ (i, j)),
        eq_toPSAU_coord ((piece f₁ f₂ (i, j)).ι ≫ f₁') i k₁]
      exact toProjectiveSpaceAtUniverse_congr c₁ _ _
    · rw [eq_toPSAU_coord ((piece f₁ f₂ (i, j)).ι ≫ f₂) j (piece_snd f₁ f₂ (i, j)),
        eq_toPSAU_coord ((piece f₁ f₂ (i, j)).ι ≫ f₂') j k₂]
      exact toProjectiveSpaceAtUniverse_congr c₂ _ _
  exact Prod.ext (hom_ext_piece f₁ f₂ fun p => (key p).1) (hom_ext_piece f₁ f₂ fun p => (key p).2)

end Properties

/-- **The Segre–Veronese morphism over a base `S`**: a monomorphism
`ℙⁿ_S ×_S ℙⁿ_S ⟶ ℙʳ_S` over `S` whose projection to the integral model is `segreVeroneseHom`. -/
private theorem exists_segreVeronese_over (S : Scheme.{u}) {δ₁ δ₂ r : ℕ}
    (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) :
    ∃ v : pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S) ⟶
        projectiveSpaceOver r S,
      v ≫ (projectiveSpaceOver r S ↘ S) = pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S) ∧
      v ≫ projectiveSpaceOver.toIntegralAtUniverse r S =
        segreVeroneseHom e (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
          (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S) ∧ Mono v := by
  refine ⟨pullback.lift (pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S))
    (segreVeroneseHom e (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
      (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S))
    (terminal.hom_ext _ _), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  constructor
  intro T a b hab
  have h1 : a ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S) =
      b ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n S ↘ S) := by
    have := congrArg (· ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} r))) hab
    simpa only [Category.assoc, pullback.lift_fst] using this
  have h2 := congrArg (· ≫ projectiveSpaceOver.toIntegralAtUniverse r S) hab
  simp only [Category.assoc, pullback.lift_snd] at h2
  rw [← segreVeroneseHom_comp, ← segreVeroneseHom_comp] at h2
  obtain ⟨k1, k2⟩ :=
    Prod.ext_iff.1 (segreVeroneseHom_injective e h₁ h₂ (a₁ := (_, _)) (a₂ := (_, _)) h2)
  have h1' : a ≫ pullback.snd _ _ ≫ (projectiveSpaceOver n S ↘ S) =
      b ≫ pullback.snd _ _ ≫ (projectiveSpaceOver n S ↘ S) := by
    rwa [← pullback.condition]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rwa [Category.assoc, Category.assoc]
    · simpa only [Category.assoc] using k1
  · apply pullback.hom_ext
    · rwa [Category.assoc, Category.assoc]
    · simpa only [Category.assoc] using k2

private theorem mono_pullback_map {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback f₁ f₂] [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [Mono i₁] [Mono i₂] :
    Mono (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  constructor
  intro T a b hab
  have h1 := congrArg (· ≫ pullback.fst g₁ g₂) hab
  have h2 := congrArg (· ≫ pullback.snd g₁ g₂) hab
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h1 h2
  apply pullback.hom_ext
  · rw [← cancel_mono i₁]
    simpa only [Category.assoc] using h1
  · rw [← cancel_mono i₂]
    simpa only [Category.assoc] using h2

/-- Let `X` be a smooth projective geometrically integral curve of genus `≥ 2` over a number
field `k` with a divisor `P` of degree one, let `φ : X ⟶ ℙⁿ_k` be a closed immersion over `k`
and `δ₁, δ₂ ≥ 1`. For every
enumeration `e` of the monomials of bidegree `(δ₁, δ₂)` there is a `k`-morphism
`v_{δ₁,δ₂} : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` whose value at the `K`-point `([c], [c'])`, for every field
`K` over `k`, is `segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id ([c], [c'])`, and such that
`ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ (φ ×_k φ) : X ×_k X ⟶ ℙʳ_k` is a closed immersion over `k`. -/
@[faltings "lem_bv_segre_veronese_embedding"]
public theorem exists_isClosedImmersion_segreVeronese_comp (k : Type u) [Field k]
    [NumberField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] (hg : 2 ≤ genus f)
    (P : X →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set X))
    (hP : ∑ᶠ Q : X, P Q * (f.residueDegree Q : ℤ) = 1) {n : ℕ}
    (φ : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφ : φ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f) [IsClosedImmersion φ]
    (δ₁ δ₂ : ℕ) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (r : ℕ)
    (e : Fin (r + 1) ≃
      {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂}) :
    ∃ v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)),
      v ≫ (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) =
          pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ∧
        (∀ (K : Type u) [Field K] [Algebra k K] (c c' : Fin (n + 1) → K) (hc : c ≠ 0)
          (hc' : c' ≠ 0) (hcs : Ideal.span (Set.range c) = ⊤)
          (hcs' : Ideal.span (Set.range c') = ⊤)
          (w : {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂} →
            K) (hw : w ≠ 0) (hws : Ideal.span (Set.range (w ∘ e)) = ⊤),
          segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id (.mk K c hc, .mk K c' hc') = .mk K w hw →
            pullback.lift
                (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
                  (projectiveSpacePoint (R := .of K) c hcs) (terminal.hom_ext _ _))
                (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
                  (projectiveSpacePoint (R := .of K) c' hcs') (terminal.hom_ext _ _))
                ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm) ≫ v ≫
                  projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
              projectiveSpacePoint (R := .of K) (w ∘ e) hws) ∧
        IsClosedImmersion
          (pullback.map f f _ _ φ φ (𝟙 _) (by simp [hφ]) (by simp [hφ]) ≫ v) ∧
        (pullback.map f f _ _ φ φ (𝟙 _) (by simp [hφ]) (by simp [hφ]) ≫ v) ≫
            (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) = pullback.fst f f ≫ f := by
  obtain ⟨v, hv₁, hv₂, hmono⟩ := exists_segreVeronese_over (Spec (.of k)) e h₁ h₂
  have hover : (pullback.map f f _ _ φ φ (𝟙 _) (by simp [hφ]) (by simp [hφ]) ≫ v) ≫
      (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) = pullback.fst f f ≫ f := by
    rw [Category.assoc, hv₁, ← Category.assoc, pullback.lift_fst, Category.assoc, hφ]
  refine ⟨v, hv₁, ?_, ?_, hover⟩
  · intro K _ _ c c' hc hc' hcs hcs' w hw hws hsv
    obtain ⟨ν, hν⟩ := exists_unit_of_segreVeroneseComposite h₁ h₂ K c c' hc hc' w hw hsv
    have key : ∀ (T : Scheme.{u}) (a b : T ⟶ projectiveSpaceOver n (Spec (.of k)))
        (h : a ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
          b ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))),
        pullback.lift a b h ≫ v ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
          segreVeroneseHom e (a ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
            (b ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) := by
      intro T a b h
      rw [hv₂, ← segreVeroneseHom_comp, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    refine (key _ _ _ _).trans ?_
    simp only [pullback.lift_snd]
    have hw' : w ∘ e = fun m => (ν : K) * bidegreeMonomial c c' (e m) := funext fun m => hν _
    have hs : Ideal.span (Set.range fun m => bidegreeMonomial c c' (e m)) = ⊤ := by
      rwa [← span_range_unit_smul ν, ← hw']
    rw [projectiveSpacePoint_congr (R := CommRingCat.of K) hw' hws (by rwa [← hw']),
      projectiveSpacePoint_unit_mul (R := CommRingCat.of K) ν _ hs]
    exact segreVeroneseHom_projectiveSpacePoint (R := CommRingCat.of K) e c c' hcs hcs' hs
  · rw [IsClosedImmersion.iff_isProper_and_mono]
    constructor
    · have : IsProper ((pullback.map f f _ _ φ φ (𝟙 _) (by simp [hφ]) (by simp [hφ]) ≫ v) ≫
          (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k))) := by
        rw [hover]; infer_instance
      exact IsProper.of_comp _ (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k))
    · exact @mono_comp _ _ _ _ _ _ (mono_pullback_map _ _ _ _ _ _ _ _ _) _ hmono

end Faltings
