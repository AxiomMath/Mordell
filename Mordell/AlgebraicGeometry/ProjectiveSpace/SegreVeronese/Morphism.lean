module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.ChartCoordinates
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The Segre–Veronese morphism of a pair of morphisms to `ℙⁿ_ℤ`

For `f₁, f₂ : Y ⟶ ℙⁿ_ℤ` and an enumeration `e` of the monomials of bidegree `(δ₁, δ₂)`, the
morphism `Faltings.segreVeroneseHom e f₁ f₂ : Y ⟶ ℙʳ_ℤ`, glued from the product charts
`f₁⁻¹ D₊(x_i) ∩ f₂⁻¹ D₊(y_j)`, where it is the morphism of the family
`x^a y^b / (x_i^{δ₁} y_j^{δ₂})`. It is natural in `Y`, it is the morphism of the monomials on
morphisms given by spanning families, and a morphism `ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` pinned on
field-valued points by `Faltings.segreVeroneseComposite` projects to it
(`Faltings.comp_toIntegral_eq_segreVeroneseHom`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings.CurveWithDegreeOneDivisor

variable {n : ℕ}

section Monomial

variable {R : Type*} [CommRing R]

/-- Scaling every variable by `c` scales the monomial `x^a` by `c ^ deg a`. -/
public theorem prod_mul_pow (a : Fin (n + 1) →₀ ℕ) (c : R) (x : Fin (n + 1) → R) :
    (a.prod fun k e => (c * x k) ^ e) = c ^ a.degree * a.prod fun k e => x k ^ e := by
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  simp only [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

end Monomial

/-! ### Product charts of a pair of morphisms to `ℙⁿ_ℤ` -/

section Charts

variable {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n)

/-- Every point of `ℙⁿ_ℤ` lies in some standard chart `D₊(x_j)`. -/
public theorem mem_chartOpen (y : projectiveSpaceAtUniverse.{u} n) :
    ∃ j, y ∈ chartOpen.{u} j :=
  TopologicalSpace.Opens.mem_iSup.mp
    ((Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n).ge trivial)

/-- The product chart `f₁⁻¹ D₊(x_i) ∩ f₂⁻¹ D₊(x_j)`. -/
@[expose] public noncomputable def piece (p : Fin (n + 1) × Fin (n + 1)) : Y.Opens :=
  f₁ ⁻¹ᵁ chartOpen.{u} p.1 ⊓ f₂ ⁻¹ᵁ chartOpen.{u} p.2

/-- The product charts `f₁⁻¹ D₊(x_i) ∩ f₂⁻¹ D₊(x_j)` cover `Y`. -/
public theorem isOpenCover_piece : TopologicalSpace.IsOpenCover (piece f₁ f₂) := by
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro y _
  obtain ⟨i, hi⟩ := mem_chartOpen (f₁.base y)
  obtain ⟨j, hj⟩ := mem_chartOpen (f₂.base y)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), ⟨hi, hj⟩⟩

/-- On the product chart of `(i, j)`, `f₁` lands in the chart `D₊(x_i)`. -/
public theorem piece_fst (p : Fin (n + 1) × Fin (n + 1)) :
    ((piece f₁ f₂ p).ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} p.1 = ⊤ :=
  preimage_ι_comp_eq_top f₁ _ inf_le_left

/-- On the product chart of `(i, j)`, `f₂` lands in the chart `D₊(x_j)`. -/
public theorem piece_snd (p : Fin (n + 1) × Fin (n + 1)) :
    ((piece f₁ f₂ p).ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} p.2 = ⊤ :=
  preimage_ι_comp_eq_top f₂ _ inf_le_right

/-- Two morphisms out of `Y` agreeing on every product chart are equal. -/
public theorem hom_ext_piece {T : Scheme.{u}} {a b : Y ⟶ T}
    (h : ∀ p, (piece f₁ f₂ p).ι ≫ a = (piece f₁ f₂ p).ι ≫ b) : a = b :=
  (Y.openCoverOfIsOpenCover _ (isOpenCover_piece f₁ f₂)).hom_ext _ _ h

end Charts

/-- The change-of-chart factor `(x_{i'} / x_i)^{δ₁} (y_{j'} / y_j)^{δ₂}` is a unit. -/
public theorem isUnit_svLocal_factor {δ₁ δ₂ : ℕ} {Z : Scheme.{u}}
    (g₁ g₂ : Z ⟶ projectiveSpaceAtUniverse.{u} n) (i j i' j' : Fin (n + 1))
    (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤)
    (h₁' : g₁ ⁻¹ᵁ chartOpen.{u} i' = ⊤) (h₂' : g₂ ⁻¹ᵁ chartOpen.{u} j' = ⊤) :
    IsUnit (coord g₁ i h₁ i' ^ δ₁ * coord g₂ j h₂ j' ^ δ₂) :=
  ((isUnit_coord g₁ i i' h₁ h₁').pow _).mul ((isUnit_coord g₂ j j' h₂ h₂').pow _)

/-- Two spanning families with a common coordinate equal to `1` and the same morphism to
projective space are equal. -/
public theorem eq_of_toPSAU_eq {Z : Scheme.{u}} {m : ℕ} (s s' : Fin (m + 1) → Γ(Z, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (hs' : Ideal.span (Set.range s') = ⊤)
    (heq : toProjectiveSpaceAtUniverse s hs = toProjectiveSpaceAtUniverse s' hs')
    (i : Fin (m + 1)) (hi : s i = 1) (hi' : s' i = 1) : s = s' := by
  have h : toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ chartOpen.{u} i = ⊤ := by
    rw [preimage_basicOpen, hi, Scheme.basicOpen_one]
  have h' : toProjectiveSpaceAtUniverse s' hs' ⁻¹ᵁ chartOpen.{u} i = ⊤ := by
    rw [preimage_basicOpen, hi', Scheme.basicOpen_one]
  funext l
  have e1 := mul_coord_of_eq s hs _ rfl i h l
  have e2 := mul_coord_of_eq s' hs' _ rfl i h' l
  rw [hi, one_mul] at e1
  rw [hi', one_mul] at e2
  rw [← e1, ← e2, coord_congr heq]

/-- The `R`-point of `ℙᵐ` of equal coordinate vectors is the same. -/
public theorem projectiveSpacePoint_congr {R : CommRingCat.{u}} {m : ℕ} {c c' : Fin (m + 1) → R}
    (h : c = c') (hc : Ideal.span (Set.range c) = ⊤) (hc' : Ideal.span (Set.range c') = ⊤) :
    projectiveSpacePoint c hc = projectiveSpacePoint c' hc' := by
  subst h; rfl

/-! ### Field-valued points -/

/-- A morphism from the spectrum of a field to `ℙⁿ_ℤ` is the point of homogeneous coordinates
`c` with some `c j = 1`. -/
public theorem exists_eq_projectiveSpacePoint_of_eq_one {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ projectiveSpaceAtUniverse.{u} n) :
    ∃ (j : Fin (n + 1)) (c : Fin (n + 1) → K) (hc : Ideal.span (Set.range c) = ⊤),
      c j = 1 ∧ t = projectiveSpacePoint (R := .of K) c hc := by
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨j, hj⟩ := mem_chartOpen (t.base p)
  have h : t ⁻¹ᵁ chartOpen.{u} j = ⊤ := by
    rw [eq_top_iff]
    intro q _
    rw [Subsingleton.elim q p]
    exact hj
  set c : Fin (n + 1) → K := fun l => (Scheme.ΓSpecIso (.of K)).hom (coord t j h l)
  have hc1 : c j = 1 := by simp [c, coord_self]
  have hc : Ideal.span (Set.range c) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) (by rw [hc1]; exact isUnit_one)
  refine ⟨j, c, hc, hc1, ?_⟩
  rw [eq_toPSAU_coord t j h, projectiveSpacePoint]
  exact toProjectiveSpaceAtUniverse_congr (funext fun l => by simp [c]) _ _

/-- A morphism from the spectrum of a field to `ℙⁿ_ℤ` is the point of some homogeneous
coordinates. -/
public theorem exists_eq_projectiveSpacePoint {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ projectiveSpaceAtUniverse.{u} n) :
    ∃ (c : Fin (n + 1) → K) (hc : Ideal.span (Set.range c) = ⊤),
      t = projectiveSpacePoint (R := .of K) c hc := by
  obtain ⟨-, c, hc, -, h⟩ := exists_eq_projectiveSpacePoint_of_eq_one t
  exact ⟨c, hc, h⟩

end Faltings.CurveWithDegreeOneDivisor

open Faltings.CurveWithDegreeOneDivisor (coord coord_comp coord_mul_coord coord_self
  exists_eq_projectiveSpacePoint hom_ext_piece isOpenCover_piece isUnit_of_basicOpen_eq_top
  isUnit_svLocal_factor mul_coord_of_eq piece piece_fst piece_snd preimage_comp_eq_top
  preimage_ι_comp_eq_top prod_mul_pow projectiveSpacePoint_congr)

namespace Faltings

variable {n : ℕ}

/-! ### Monomials of bidegree `(δ₁, δ₂)` -/

/-- The exponents `(a, b)` of the monomials `x^a y^b` of bidegree `(δ₁, δ₂)` in two sets of
`n + 1` variables: pairs of exponent vectors of total degrees `δ₁` and `δ₂`. -/
public abbrev BidegreeExponent (n δ₁ δ₂ : ℕ) : Type :=
  {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂}

section Monomial

variable {R S : Type*} [CommRing R] [CommRing S] {δ₁ δ₂ : ℕ}

/-- The monomial `x^a y^b = ∏ₖ x_k ^ a_k * ∏ₗ y_l ^ b_l` of exponents `(a, b)`. -/
@[expose] public def bidegreeMonomial (x y : Fin (n + 1) → R) (ab : BidegreeExponent n δ₁ δ₂) :
    R :=
  (ab.1.1.prod fun k e => x k ^ e) * ab.2.1.prod fun l e => y l ^ e

/-- A ring homomorphism maps the monomial `x^a y^b` to the monomial of the images. -/
public theorem map_bidegreeMonomial (φ : R →+* S) (x y : Fin (n + 1) → R)
    (ab : BidegreeExponent n δ₁ δ₂) :
    φ (bidegreeMonomial x y ab) = bidegreeMonomial (fun k => φ (x k)) (fun l => φ (y l)) ab := by
  simp only [bidegreeMonomial, map_mul, map_finsuppProd, map_pow]

/-- Scaling `x` by `c` and `y` by `d` scales `x^a y^b` by `c ^ δ₁ d ^ δ₂`. -/
public theorem bidegreeMonomial_const_mul (c d : R) (x y : Fin (n + 1) → R)
    (ab : BidegreeExponent n δ₁ δ₂) :
    bidegreeMonomial (fun k => c * x k) (fun l => d * y l) ab =
      c ^ δ₁ * d ^ δ₂ * bidegreeMonomial x y ab := by
  simp only [bidegreeMonomial, prod_mul_pow, ab.1.2, ab.2.2]
  ring

/-- The exponents of `x_i ^ δ₁ y_j ^ δ₂`. -/
@[expose] public noncomputable def BidegreeExponent.corner (δ₁ δ₂ : ℕ) (i j : Fin (n + 1)) :
    BidegreeExponent n δ₁ δ₂ :=
  (⟨Finsupp.single i δ₁, by simp⟩, ⟨Finsupp.single j δ₂, by simp⟩)

/-- The corner monomial of exponents `(δ₁ eᵢ, δ₂ eⱼ)` is `x_i ^ δ₁ * y_j ^ δ₂`. -/
@[simp]
public theorem bidegreeMonomial_corner (x y : Fin (n + 1) → R) (i j : Fin (n + 1)) :
    bidegreeMonomial x y (BidegreeExponent.corner δ₁ δ₂ i j) = x i ^ δ₁ * y j ^ δ₂ := by
  simp [bidegreeMonomial, BidegreeExponent.corner, Finsupp.prod_single_index]
end Monomial

/-! ### The Segre–Veronese coordinates on a product chart -/

section Local

variable {δ₁ δ₂ r : ℕ} (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)

/-- The coordinates `x^a y^b / (x_i^δ₁ y_j^δ₂)` of a pair of morphisms landing in the charts `i`
and `j`. -/
@[expose] public noncomputable def svLocal {Z : Scheme.{u}}
    (g₁ g₂ : Z ⟶ projectiveSpaceAtUniverse.{u} n)
    (i j : Fin (n + 1)) (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    Fin (r + 1) → Γ(Z, ⊤) :=
  fun m => bidegreeMonomial (coord g₁ i h₁) (coord g₂ j h₂) (e m)

variable {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ projectiveSpaceAtUniverse.{u} n)

public theorem svLocal_corner (i j : Fin (n + 1)) (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤)
    (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    svLocal e g₁ g₂ i j h₁ h₂ (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) = 1 := by
  simp [svLocal, bidegreeMonomial_corner, coord_self]

public theorem span_svLocal (i j : Fin (n + 1)) (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤)
    (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    Ideal.span (Set.range (svLocal e g₁ g₂ i j h₁ h₂)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨e.symm (BidegreeExponent.corner δ₁ δ₂ i j), rfl⟩)
    (by rw [svLocal_corner]; exact isUnit_one)

public theorem appTop_svLocal {Z' : Scheme.{u}} (g : Z' ⟶ Z) (i j : Fin (n + 1))
    (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    (fun m => g.appTop (svLocal e g₁ g₂ i j h₁ h₂ m)) =
      svLocal e (g ≫ g₁) (g ≫ g₂) i j (preimage_comp_eq_top g g₁ i h₁)
        (preimage_comp_eq_top g g₂ j h₂) := by
  funext m
  simp only [svLocal, map_bidegreeMonomial]
  congr 1
  · funext k; rw [coord_comp g g₁ i h₁]
  · funext k; rw [coord_comp g g₂ j h₂]

public theorem svLocal_congr {g₁ g₂ g₁' g₂' : Z ⟶ projectiveSpaceAtUniverse.{u} n}
    (e₁ : g₁ = g₁') (e₂ : g₂ = g₂') (i j : Fin (n + 1))
    (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤)
    (h₁' : g₁' ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂' : g₂' ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    svLocal e g₁ g₂ i j h₁ h₂ = svLocal e g₁' g₂' i j h₁' h₂' := by
  subst e₁ e₂; rfl

public theorem svLocal_change (i j i' j' : Fin (n + 1)) (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤)
    (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤) (h₁' : g₁ ⁻¹ᵁ chartOpen.{u} i' = ⊤)
    (h₂' : g₂ ⁻¹ᵁ chartOpen.{u} j' = ⊤) :
    svLocal e g₁ g₂ i j h₁ h₂ = fun m =>
      (coord g₁ i h₁ i' ^ δ₁ * coord g₂ j h₂ j' ^ δ₂) * svLocal e g₁ g₂ i' j' h₁' h₂' m := by
  funext m
  simp only [svLocal]
  rw [← bidegreeMonomial_const_mul]
  congr 1
  · funext k; rw [coord_mul_coord]
  · funext k; rw [coord_mul_coord]

end Local

/-! ### Glueing the Segre–Veronese morphism -/

section Glue

variable {δ₁ δ₂ r : ℕ} (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)
variable {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n)

/-- Restricting the local Segre–Veronese coordinates of a chart `V` to a smaller open `U`
gives the local coordinates of `U`. -/
private theorem resOfLE_svLocal {U V : Y.Opens} (hUV : U ≤ V) (i j : Fin (n + 1))
    (h₁ : (V.ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : (V.ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} j = ⊤)
    (h₁' : (U.ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂' : (U.ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} j = ⊤)
    (m : Fin (r + 1)) :
    resOfLE hUV (svLocal e (V.ι ≫ f₁) (V.ι ≫ f₂) i j h₁ h₂ m) =
      svLocal e (U.ι ≫ f₁) (U.ι ≫ f₂) i j h₁' h₂' m :=
  congrFun ((appTop_svLocal e _ _ (Y.homOfLE hUV) i j _ _).trans
    (svLocal_congr e (by rw [← Category.assoc, Scheme.homOfLE_ι])
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) _ _ _ _ _ _)) m

private theorem exists_segreVeroneseHom : ∃ g : Y ⟶ projectiveSpaceAtUniverse.{u} r, ∀ p,
    (piece f₁ f₂ p).ι ≫ g = toProjectiveSpaceAtUniverse
      (svLocal e ((piece f₁ f₂ p).ι ≫ f₁) ((piece f₁ f₂ p).ι ≫ f₂) p.1 p.2
        (piece_fst f₁ f₂ p) (piece_snd f₁ f₂ p))
      (span_svLocal e _ _ p.1 p.2 (piece_fst f₁ f₂ p) (piece_snd f₁ f₂ p)) := by
  refine exists_hom_of_cover_general Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality
    Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance (piece f₁ f₂) (isOpenCover_piece f₁ f₂)
    _ _ ?_
  intro p q
  have hW1 : ((piece f₁ f₂ p ⊓ piece f₁ f₂ q).ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} p.1 = ⊤ :=
    preimage_ι_comp_eq_top f₁ _ (inf_le_left.trans inf_le_left)
  have hW2 : ((piece f₁ f₂ p ⊓ piece f₁ f₂ q).ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} p.2 = ⊤ :=
    preimage_ι_comp_eq_top f₂ _ (inf_le_left.trans inf_le_right)
  have hW1' : ((piece f₁ f₂ p ⊓ piece f₁ f₂ q).ι ≫ f₁) ⁻¹ᵁ chartOpen.{u} q.1 = ⊤ :=
    preimage_ι_comp_eq_top f₁ _ (inf_le_right.trans inf_le_left)
  have hW2' : ((piece f₁ f₂ p ⊓ piece f₁ f₂ q).ι ≫ f₂) ⁻¹ᵁ chartOpen.{u} q.2 = ⊤ :=
    preimage_ι_comp_eq_top f₂ _ (inf_le_right.trans inf_le_right)
  refine ⟨(isUnit_svLocal_factor (δ₁ := δ₁) (δ₂ := δ₂) _ _ p.1 p.2 q.1 q.2
    hW1 hW2 hW1' hW2').unit, fun m => ?_⟩
  rw [resOfLE_svLocal e f₁ f₂ inf_le_left _ _ _ _ hW1 hW2,
    resOfLE_svLocal e f₁ f₂ inf_le_right _ _ _ _ hW1' hW2', IsUnit.unit_spec]
  exact congrFun (svLocal_change e _ _ p.1 p.2 q.1 q.2 hW1 hW2 hW1' hW2') m

/-- **The Segre–Veronese morphism** `v_{δ₁,δ₂}(f₁, f₂) : Y ⟶ ℙʳ_ℤ` of a pair of morphisms
`f₁, f₂ : Y ⟶ ℙⁿ_ℤ`, the coordinates of `ℙʳ_ℤ` being indexed by the monomials of bidegree
`(δ₁, δ₂)` through `e`. On the product chart `f₁⁻¹ D₊(x_i) ∩ f₂⁻¹ D₊(y_j)` it is the morphism of
the family `x^a y^b / (x_i^{δ₁} y_j^{δ₂})` (`Faltings.comp_segreVeroneseHom`), and on morphisms
given by spanning families it is the morphism of the monomials in them
(`Faltings.segreVeroneseHom_of_eq`). -/
public noncomputable def segreVeroneseHom : Y ⟶ projectiveSpaceAtUniverse.{u} r :=
  (exists_segreVeroneseHom e f₁ f₂).choose

public theorem ι_segreVeroneseHom (p : Fin (n + 1) × Fin (n + 1)) :
    (piece f₁ f₂ p).ι ≫ segreVeroneseHom e f₁ f₂ = toProjectiveSpaceAtUniverse
      (svLocal e ((piece f₁ f₂ p).ι ≫ f₁) ((piece f₁ f₂ p).ι ≫ f₂) p.1 p.2
        (piece_fst f₁ f₂ p) (piece_snd f₁ f₂ p))
      (span_svLocal e _ _ p.1 p.2 (piece_fst f₁ f₂ p) (piece_snd f₁ f₂ p)) :=
  (exists_segreVeroneseHom e f₁ f₂).choose_spec p

/-- The Segre–Veronese morphism on a morphism landing in a product chart. -/
public theorem comp_segreVeroneseHom_chart {Z : Scheme.{u}} (g : Z ⟶ Y) (i j : Fin (n + 1))
    (h₁ : (g ≫ f₁) ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : (g ≫ f₂) ⁻¹ᵁ chartOpen.{u} j = ⊤) :
    g ≫ segreVeroneseHom e f₁ f₂ =
      toProjectiveSpaceAtUniverse (svLocal e (g ≫ f₁) (g ≫ f₂) i j h₁ h₂)
        (span_svLocal e _ _ i j h₁ h₂) := by
  have hr : Set.range g.base ⊆ Set.range (piece f₁ f₂ (i, j)).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact ⟨h₁.ge trivial, h₂.ge trivial⟩
  have hg' : IsOpenImmersion.lift (piece f₁ f₂ (i, j)).ι g hr ≫ (piece f₁ f₂ (i, j)).ι = g :=
    IsOpenImmersion.lift_fac _ _ _
  have hfam := appTop_svLocal e _ _ (IsOpenImmersion.lift (piece f₁ f₂ (i, j)).ι g hr) i j
    (piece_fst f₁ f₂ (i, j)) (piece_snd f₁ f₂ (i, j))
  have hfam' := hfam.trans (svLocal_congr e (by rw [← Category.assoc, hg'])
    (by rw [← Category.assoc, hg']) _ _ _ _ h₁ h₂)
  conv_lhs => rw [← hg', Category.assoc, ι_segreVeroneseHom e f₁ f₂ (i, j)]
  rw [Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _
    (by rw [hfam']; exact span_svLocal e _ _ i j h₁ h₂)]
  exact toProjectiveSpaceAtUniverse_congr hfam' _ _

end Glue

/-! ### Properties of the Segre–Veronese morphism -/

section Properties

variable {δ₁ δ₂ r : ℕ} (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)

/-- On morphisms given by spanning families, the local Segre–Veronese coordinates define the
morphism of the monomials. -/
private theorem toPSAU_svLocal_of_eq {Z : Scheme.{u}}
    (g₁ g₂ : Z ⟶ projectiveSpaceAtUniverse.{u} n)
    (t₁ t₂ : Fin (n + 1) → Γ(Z, ⊤)) (ht₁ : Ideal.span (Set.range t₁) = ⊤)
    (ht₂ : Ideal.span (Set.range t₂) = ⊤) (hg₁ : g₁ = toProjectiveSpaceAtUniverse t₁ ht₁)
    (hg₂ : g₂ = toProjectiveSpaceAtUniverse t₂ ht₂) (i j : Fin (n + 1))
    (h₁ : g₁ ⁻¹ᵁ chartOpen.{u} i = ⊤) (h₂ : g₂ ⁻¹ᵁ chartOpen.{u} j = ⊤)
    (ht : Ideal.span (Set.range fun m => bidegreeMonomial t₁ t₂ (e m)) = ⊤) :
    toProjectiveSpaceAtUniverse (svLocal e g₁ g₂ i j h₁ h₂) (span_svLocal e _ _ i j h₁ h₂) =
      toProjectiveSpaceAtUniverse (fun m => bidegreeMonomial t₁ t₂ (e m)) ht := by
  have hu₁ : IsUnit (t₁ i) := isUnit_of_basicOpen_eq_top _ (by
    rwa [← preimage_basicOpen t₁ ht₁ i, ← hg₁])
  have hu₂ : IsUnit (t₂ j) := isUnit_of_basicOpen_eq_top _ (by
    rwa [← preimage_basicOpen t₂ ht₂ j, ← hg₂])
  have hfam : (fun m => bidegreeMonomial t₁ t₂ (e m)) =
      fun m => (t₁ i ^ δ₁ * t₂ j ^ δ₂) * svLocal e g₁ g₂ i j h₁ h₂ m := by
    funext m
    simp only [svLocal]
    rw [← bidegreeMonomial_const_mul]
    congr 1
    · funext k; rw [mul_coord_of_eq t₁ ht₁ g₁ hg₁ i h₁ k]
    · funext k; rw [mul_coord_of_eq t₂ ht₂ g₂ hg₂ j h₂ k]
  rw [toProjectiveSpaceAtUniverse_congr hfam _ (by rwa [← hfam])]
  exact (Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance ((hu₁.pow _).mul (hu₂.pow _)).unit
    _ _ _).symm

variable {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n)

/-- **The Segre–Veronese morphism of two morphisms given by spanning families is the morphism of
the monomials in them.** -/
public theorem segreVeroneseHom_of_eq (s₁ s₂ : Fin (n + 1) → Γ(Y, ⊤))
    (hs₁ : Ideal.span (Set.range s₁) = ⊤) (hs₂ : Ideal.span (Set.range s₂) = ⊤)
    (hf₁ : f₁ = toProjectiveSpaceAtUniverse s₁ hs₁)
    (hf₂ : f₂ = toProjectiveSpaceAtUniverse s₂ hs₂)
    (hs : Ideal.span (Set.range fun m => bidegreeMonomial s₁ s₂ (e m)) = ⊤) :
    segreVeroneseHom e f₁ f₂ =
      toProjectiveSpaceAtUniverse (fun m => bidegreeMonomial s₁ s₂ (e m)) hs := by
  refine hom_ext_piece f₁ f₂ fun p => ?_
  have hfam : (fun m => (piece f₁ f₂ p).ι.appTop (bidegreeMonomial s₁ s₂ (e m))) =
      fun m => bidegreeMonomial (fun k => (piece f₁ f₂ p).ι.appTop (s₁ k))
        (fun l => (piece f₁ f₂ p).ι.appTop (s₂ l)) (e m) := by
    funext m; rw [map_bidegreeMonomial]
  have hspan : Ideal.span (Set.range fun m =>
      bidegreeMonomial (fun k => (piece f₁ f₂ p).ι.appTop (s₁ k))
        (fun l => (piece f₁ f₂ p).ι.appTop (s₂ l)) (e m)) = ⊤ := by
    rw [← hfam]; exact span_range_comp _ _ hs
  rw [ι_segreVeroneseHom, Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _
    (by rwa [hfam]), toProjectiveSpaceAtUniverse_congr hfam _ hspan]
  exact toPSAU_svLocal_of_eq e _ _ _ _ (span_range_comp _ _ hs₁) (span_range_comp _ _ hs₂)
    (by rw [hf₁]; exact Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ _)
    (by rw [hf₂]; exact Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ _)
    _ _ _ _ hspan

/-- **Naturality of the Segre–Veronese morphism in the source.** -/
public theorem segreVeroneseHom_comp {Z : Scheme.{u}} (g : Z ⟶ Y) :
    segreVeroneseHom e (g ≫ f₁) (g ≫ f₂) = g ≫ segreVeroneseHom e f₁ f₂ := by
  refine hom_ext_piece (g ≫ f₁) (g ≫ f₂) fun p => ?_
  rw [ι_segreVeroneseHom]
  conv_rhs => rw [← Category.assoc, comp_segreVeroneseHom_chart e f₁ f₂ _ p.1 p.2
    (by rw [Category.assoc]; exact piece_fst (g ≫ f₁) (g ≫ f₂) p)
    (by rw [Category.assoc]; exact piece_snd (g ≫ f₁) (g ≫ f₂) p)]
  exact toProjectiveSpaceAtUniverse_congr (svLocal_congr e (Category.assoc _ _ _).symm
    (Category.assoc _ _ _).symm _ _ _ _ _ _) _ _

/-- **The Segre–Veronese morphism on a morphism whose two components are given by spanning
families** `t₁, t₂` is the morphism of the monomials in them. When `g` lands in the product
chart `f₁⁻¹ D₊(x_i) ∩ f₂⁻¹ D₊(y_j)` and `t₁, t₂` are the ratios `x_k / x_i`, `y_l / y_j`, this
is the family `x^a y^b / (x_i^{δ₁} y_j^{δ₂})`. -/
public theorem comp_segreVeroneseHom {Z : Scheme.{u}} (g : Z ⟶ Y) (t₁ t₂ : Fin (n + 1) → Γ(Z, ⊤))
    (ht₁ : Ideal.span (Set.range t₁) = ⊤) (ht₂ : Ideal.span (Set.range t₂) = ⊤)
    (hg₁ : g ≫ f₁ = toProjectiveSpaceAtUniverse t₁ ht₁)
    (hg₂ : g ≫ f₂ = toProjectiveSpaceAtUniverse t₂ ht₂)
    (ht : Ideal.span (Set.range fun m => bidegreeMonomial t₁ t₂ (e m)) = ⊤) :
    g ≫ segreVeroneseHom e f₁ f₂ =
      toProjectiveSpaceAtUniverse (fun m => bidegreeMonomial t₁ t₂ (e m)) ht := by
  rw [← segreVeroneseHom_comp]
  exact segreVeroneseHom_of_eq e _ _ t₁ t₂ ht₁ ht₂ hg₁ hg₂ ht

/-- **The Segre–Veronese morphism at a pair of `R`-points** is the `R`-point of the monomials. -/
public theorem segreVeroneseHom_projectiveSpacePoint {R : CommRingCat.{u}} (c c' : Fin (n + 1) → R)
    (hc : Ideal.span (Set.range c) = ⊤) (hc' : Ideal.span (Set.range c') = ⊤)
    (hs : Ideal.span (Set.range fun m => bidegreeMonomial c c' (e m)) = ⊤) :
    segreVeroneseHom e (projectiveSpacePoint c hc) (projectiveSpacePoint c' hc') =
      projectiveSpacePoint (fun m => bidegreeMonomial c c' (e m)) hs := by
  have hfun : (fun m => (Scheme.ΓSpecIso R).inv.hom (bidegreeMonomial c c' (e m))) =
      fun m => bidegreeMonomial (fun i => (Scheme.ΓSpecIso R).inv.hom (c i))
        (fun i => (Scheme.ΓSpecIso R).inv.hom (c' i)) (e m) := by
    funext m; rw [map_bidegreeMonomial]
  have hs' := span_range_ΓSpecIso_inv _ hs
  unfold projectiveSpacePoint
  rw [toProjectiveSpaceAtUniverse_congr hfun _ (by rwa [← hfun])]
  exact segreVeroneseHom_of_eq e _ _ _ _ _ _ rfl rfl _

end Properties

/-- The value of the Segre–Veronese map on points is the monomial vector up to a unit. -/
public theorem exists_unit_of_segreVeroneseComposite {δ₁ δ₂ : ℕ} (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    (K : Type*) [Field K] (c c' : Fin (n + 1) → K) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (w : BidegreeExponent n δ₁ δ₂ → K) (hw : w ≠ 0)
    (h : Faltings.segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id
      (Projectivization.mk K c hc, Projectivization.mk K c' hc') = Projectivization.mk K w hw) :
    ∃ ν : Kˣ, ∀ ab, w ab = ν * bidegreeMonomial c c' ab := by
  obtain ⟨μ, hμ⟩ := Projectivization.exists_smul_eq_mk_rep K c hc
  obtain ⟨μ', hμ'⟩ := Projectivization.exists_smul_eq_mk_rep K c' hc'
  simp only [Faltings.segreVeroneseComposite, id] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp h.symm
  refine ⟨a * μ ^ δ₁ * μ' ^ δ₂, fun ab => ?_⟩
  have hab := congrFun ha ab
  rw [← hμ, ← hμ'] at hab
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hab
  have hm : ((ab.1.1.prod fun i k => ((μ : K) * c i) ^ k) *
      ab.2.1.prod fun j k => ((μ' : K) * c' j) ^ k) =
      bidegreeMonomial (fun i => (μ : K) * c i) (fun j => (μ' : K) * c' j) ab := rfl
  rw [hm, bidegreeMonomial_const_mul] at hab
  rw [← hab]
  push_cast
  ring

/-! ### Field-valued points -/

/-- The pinning of a Segre–Veronese morphism at one field-valued point. -/
private theorem comp_toIntegral_eq_segreVeroneseHom_of_field {k : Type u} [Field k] {δ₁ δ₂ r : ℕ}
    (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)
    (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
    (hv : ∀ (K : Type u) [Field K] [Algebra k K] (c c' : Fin (n + 1) → K) (hc : c ≠ 0)
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
              projectiveSpacePoint (R := .of K) (w ∘ e) hws)
    {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) :
    t ≫ v ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
      t ≫ segreVeroneseHom e
        (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) := by
  let _ : Algebra k K := (Spec.preimage (t ≫ pullback.fst _ _ ≫
    (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))).hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k K)) = t ≫ pullback.fst _ _ ≫
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [← Spec.map_preimage (t ≫ pullback.fst _ _ ≫
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))]
    rfl
  obtain ⟨c, hcs, hca⟩ := exists_eq_projectiveSpacePoint
    (t ≫ pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  obtain ⟨c', hcs', hcb⟩ := exists_eq_projectiveSpacePoint
    (t ≫ pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
  have hne : ∀ d : Fin (n + 1) → K, Ideal.span (Set.range d) = ⊤ → d ≠ 0 := by
    rintro d hd rfl
    have : Ideal.span (Set.range (0 : Fin (n + 1) → K)) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨i, rfl⟩; rfl
    exact bot_ne_top (this.symm.trans hd)
  have hc := hne c hcs
  have hc' := hne c' hcs'
  set P := segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id (.mk K c hc, .mk K c' hc')
  have hws : Ideal.span (Set.range (P.rep ∘ e)) = ⊤ := by
    obtain ⟨ab, hab⟩ := Function.ne_iff.mp P.rep_nonzero
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨e.symm ab, by simp⟩)
      (isUnit_iff_ne_zero.mpr hab)
  have hpt := hv K c c' hc hc' hcs hcs' P.rep P.rep_nonzero hws (P.mk_rep).symm
  have hcond : t ≫ pullback.snd _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
      t ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) :=
    congrArg (t ≫ ·) pullback.condition.symm
  have ht : t = pullback.lift
      (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (projectiveSpacePoint (R := .of K) c hcs) (terminal.hom_ext _ _))
      (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (projectiveSpacePoint (R := .of K) c' hcs') (terminal.hom_ext _ _))
      ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm) := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      apply pullback.hom_ext
      · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
        rw [hspec, Category.assoc]; rfl
      · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
        rw [← hca, Category.assoc]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      apply pullback.hom_ext
      · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
        rw [hspec, Category.assoc]
        exact hcond
      · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
        rw [← hcb, Category.assoc]
  obtain ⟨ν, hν⟩ := exists_unit_of_segreVeroneseComposite h₁ h₂ K c c' hc hc' P.rep
    P.rep_nonzero (P.mk_rep).symm
  have hw' : P.rep ∘ e = fun m => (ν : K) * bidegreeMonomial c c' (e m) := funext fun m => hν _
  have hs : Ideal.span (Set.range fun m => bidegreeMonomial c c' (e m)) = ⊤ := by
    rwa [← span_range_unit_smul ν, ← hw']
  calc t ≫ v ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k))
      = projectiveSpacePoint (R := .of K) (P.rep ∘ e) hws := by rwa [ht]
    _ = projectiveSpacePoint (R := .of K) (fun m => bidegreeMonomial c c' (e m)) hs := by
      rw [projectiveSpacePoint_congr (R := CommRingCat.of K) hw' hws (by rwa [← hw']),
        projectiveSpacePoint_unit_mul (R := CommRingCat.of K) ν _ hs]
    _ = segreVeroneseHom e (projectiveSpacePoint (R := .of K) c hcs)
          (projectiveSpacePoint (R := .of K) c' hcs') :=
      (segreVeroneseHom_projectiveSpacePoint (R := CommRingCat.of K) e c c' hcs hcs' hs).symm
    _ = t ≫ segreVeroneseHom e
          (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
          (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) := by
      rw [← segreVeroneseHom_comp, ← hca, ← hcb]

/-- **A morphism pinned on field-valued points by the Segre–Veronese map is
`Faltings.segreVeroneseHom`.** If a morphism `v : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` sends every `K`-point
`([c], [c'])`, for every field `K` over `k`, to `segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id
([c], [c'])`, then its projection to `ℙʳ_ℤ` is the Segre–Veronese morphism of the two
projections; the source is reduced, being smooth over `k`. -/
public theorem comp_toIntegral_eq_segreVeroneseHom {k : Type u} [Field k] {δ₁ δ₂ r : ℕ}
    (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)
    (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
    (hv : ∀ (K : Type u) [Field K] [Algebra k K] (c c' : Fin (n + 1) → K) (hc : c ≠ 0)
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
              projectiveSpacePoint (R := .of K) (w ∘ e) hws) :
    v ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
      segreVeroneseHom e
        (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) := by
  have : IsReduced (pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) :=
    isReduced_of_smooth_of_isAffine (pullback.fst _ _ ≫
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
  refine ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ => ?_) (terminal.hom_ext _ _)
  exact comp_toIntegral_eq_segreVeroneseHom_of_field h₁ h₂ e v hv
    (K := ((pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).residueField x))
    ((pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).fromSpecResidueField x)

end Faltings
