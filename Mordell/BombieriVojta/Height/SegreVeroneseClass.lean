module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Machine.EmbeddingGroup
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.BasicUnconditional
public import Mordell.AlgebraicGeometry.ProjectiveSpace.ChartCoordinates
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Morphism
public import Mordell.AlgebraicGeometry.TensorPowerSections

/-!
# The class of the Segre–Veronese embedding `ψ_{δ₁,δ₂}`

Let `(C, P)` be a curve over an algebraic extension `k` of `ℚ` with a divisor `P` of degree
one, of genus `g ≥ 2`, let `N ≥ 2g + 1` and let `φ_{NP} : C ⟶ ℙⁿ_k` be a projective embedding
with `φ_{NP}^* 𝒪(1) ≅ 𝒪_C(NP)`. For `δ₁, δ₂ ≥ 1` let `v_{δ₁,δ₂} : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` be the
Segre–Veronese morphism given by all monomials of bidegree `(δ₁, δ₂)` and
`ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ (φ_{NP} ×_k φ_{NP})`. Since `v_{δ₁,δ₂}^* 𝒪(1) = 𝒪(δ₁, δ₂)`, the class
of `ψ_{δ₁,δ₂}` in `Pic(C ×_k C)` is
`δ₁ pr₁^*[𝒪_C(NP)] + δ₂ pr₂^*[𝒪_C(NP)] = [𝒪(δ₁ (NP) × C + δ₂ C × (NP))]`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.embeddingClass_segreVeronese_eq_vojtaClass`:
  `cl(ψ_{δ₁,δ₂}) = [𝒪(δ₁ N (P × C) + δ₂ N (C × P))]`.

## Implementation notes

The class `cl` of a projective embedding is `Faltings.embeddingClass`, the class of the
pull-back of `𝒪(1)`. The divisor class `δ₁ (NP) × C + δ₂ C × (NP)` is
`Faltings.CurveWithDegreeOneDivisor.vojtaClass` at `(δ₁ N, δ₂ N, 0)`. The embedding
`ψ_{δ₁,δ₂}` is a projective embedding of `C ×_k C` whose underlying morphism is
`(φ_{NP} ×_k φ_{NP}) ≫ v`, for a morphism `v` over `k` whose value at every `K`-point
`([c], [c'])`, for every field `K` over `k`, is `Faltings.segreVeroneseComposite` with `ψ = id`;
this determines `v`, and such `v` exists by
`Faltings.exists_isClosedImmersion_segreVeronese_comp`. The hypothesis on `φ_{NP}` is that its
class is `N [P]`, with `[P] = ∑ nₓ [𝒪_C(x)]`. That `C ×_k C` is a smooth projective variety
over `k` is taken as instance arguments; both hold for every curve.

The morphism `v` is only pinned by its values on field-valued points. Since `ℙⁿ_k ×_k ℙⁿ_k` is
smooth over `k`, hence reduced, and `ℙʳ_ℤ` is separated, `v` followed by the projection to the
integral model `ℙʳ_ℤ` is determined by its values at the residue fields, where it agrees with the
Segre–Veronese morphism `sv = Faltings.segreVeroneseHom` glued from the product charts
`D₊(x_i) × D₊(y_j)` with coordinates `x^a y^b / x_i^{δ₁} y_j^{δ₂}`. For morphisms
`f₁, f₂ : Y ⟶ ℙⁿ_ℤ` the monomials `x^a y^b` in the pulled-back coordinates are global sections of
`(f₁^* 𝒪(1))^{⊗ δ₁} ⊗ (f₂^* 𝒪(1))^{⊗ δ₂}` generating it, and on the open where `x^a y^b` does
not vanish `sv(f₁, f₂)` is the morphism of the ratios `x^{a'} y^{b'} / x^a y^b`. The twist
identification of [Stacks, Tag 01NE] then gives
`sv(f₁, f₂)^* 𝒪(1) ≅ (f₁^* 𝒪(1))^{⊗ δ₁} ⊗ (f₂^* 𝒪(1))^{⊗ δ₂}`, which is `v^* 𝒪(1) = 𝒪(δ₁, δ₂)`
pulled back along `φ ×_k φ`. The tensor power `M^{⊗ (k + 1)}` is the iterated tensor product
`M ⊗ (M ⊗ (⋯ ⊗ M))`, and a monomial of degree `k + 1` is the product along a word in the variables
in which each variable occurs as often as its exponent.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 3, p. 619][bombieri1990]
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings.CurveWithDegreeOneDivisor

section Helpers

variable {n : ℕ}

/-! ### The Segre–Veronese morphism pulls `𝒪(1)` back to `𝒪(δ₁, δ₂)` -/

section Twist

open Stacks.ProjectiveFromSections Stacks.SectionProduct Stacks.TwistPullbackPinned Opposite

attribute [local instance] isInvertibleModule_powMod

variable {Y : Scheme.{u}} {A B : Y.Modules} [Stacks.Ample.IsInvertibleModule Y A]
  [Stacks.Ample.IsInvertibleModule Y B]
  (x : Fin (n + 1) → Γ(A, ⊤)) (y : Fin (n + 1) → Γ(B, ⊤)) {δ₁ δ₂ k₁ k₂ : ℕ}
  (hk₁ : δ₁ = k₁ + 1) (hk₂ : δ₂ = k₂ + 1)

/-- The monomial `x^a y^b`, a global section of `A^{⊗ δ₁} ⊗ B^{⊗ δ₂}`. -/
private noncomputable def svSec (ab : BidegreeExponent n δ₁ δ₂) :
    Γ(Scheme.Modules.tensorObj (powMod A k₁) (powMod B k₂), ⊤) :=
  tsec ⊤ (powSec x k₁ (word ab.1 hk₁)) (powSec y k₂ (word ab.2 hk₂))

/-- The section `x_i ^ δ₁ y_j ^ δ₂` of `A^{⊗ δ₁} ⊗ B^{⊗ δ₂}`. -/
@[expose] public noncomputable abbrev svBase (k₁ k₂ : ℕ) (i j : Fin (n + 1)) :
    Γ(Scheme.Modules.tensorObj (powMod A k₁) (powMod B k₂), ⊤) :=
  tsec ⊤ (powSec x k₁ fun _ => i) (powSec y k₂ fun _ => j)

omit [Stacks.Ample.IsInvertibleModule Y A] [Stacks.Ample.IsInvertibleModule Y B] in
private theorem svSec_corner (i j : Fin (n + 1)) :
    svSec x y hk₁ hk₂ (BidegreeExponent.corner δ₁ δ₂ i j) = svBase x y k₁ k₂ i j := by
  simp only [svSec, svBase, BidegreeExponent.corner]
  congr 2
  · exact funext (word_single i _ hk₁)
  · exact funext (word_single j _ hk₂)

private theorem resT_svSec {i j : Fin (n + 1)} {W : Y.Opens} (hi : W ≤ nvOpen A (x i))
    (hj : W ≤ nvOpen B (y j)) (ab : BidegreeExponent n δ₁ δ₂) :
    resT W (svSec x y hk₁ hk₂ ab) =
      bidegreeMonomial (fun l => div (x i) hi (resT W (x l)))
        (fun l => div (y j) hj (resT W (y l))) ab •
        resT W (svBase x y k₁ k₂ i j) := by
  rw [svSec, resT_tsec, resT_tsec, resT_powSec x hi, resT_powSec y hj, tsec_smul_smul,
    prod_word (fun l => div (x i) hi (resT W (x l))),
    prod_word (fun l => div (y j) hj (resT W (y l)))]
  rfl

private theorem nvOpen_svSec_le (ab : BidegreeExponent n δ₁ δ₂) :
    nvOpen _ (svSec x y hk₁ hk₂ ab) ≤
      nvOpen A (x (word ab.1 hk₁ 0)) ⊓ nvOpen B (y (word ab.2 hk₂ 0)) :=
  (nvOpen_tensorSectionsAt _ _ _ _).le.trans
    (inf_le_inf (nvOpen_powSec_le x _ _) (nvOpen_powSec_le y _ _))

/-- The section `x_i ^ δ₁ y_j ^ δ₂` does not vanish where `x_i` and `y_j` do not vanish. -/
public theorem le_nvOpen_svBase (i j : Fin (n + 1)) :
    nvOpen A (x i) ⊓ nvOpen B (y j) ≤ nvOpen _ (svBase x y k₁ k₂ i j) :=
  (inf_le_inf (le_nvOpen_powSec_const x i k₁) (le_nvOpen_powSec_const y j k₂)).trans
    (nvOpen_tensorSectionsAt _ _ _ _).ge

end Twist

/-! ### The twist identification for `sv` -/

section TwistIso

open Stacks.ProjectiveFromSections Stacks.SectionProduct Stacks.TwistPullbackPinned
  Stacks.AmpleProjectiveImmersion Opposite

attribute [local instance] isInvertibleModule_powMod

/-- **`sv(f₁, f₂)^* 𝒪(1) ≅ (f₁^* 𝒪(1))^{⊗ δ₁} ⊗ (f₂^* 𝒪(1))^{⊗ δ₂}`.** The monomials `x^a y^b` in
the pulled-back coordinates generate the right-hand side, and on the open where `x^a y^b` does
not vanish `sv(f₁, f₂)` is the morphism of the ratios `x^{a'} y^{b'} / x^a y^b`; so this is the
twist identification of [Stacks, Tag 01NE] at that family. -/
public theorem nonempty_pullback_segreVeroneseHom_iso {Y : Scheme.{u}} {δ₁ δ₂ k₁ k₂ r : ℕ}
    (hk₁ : δ₁ = k₁ + 1) (hk₂ : δ₂ = k₂ + 1) (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂)
    (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n) :
    Nonempty ((Scheme.Modules.pullback (segreVeroneseHom e f₁ f₂)).obj
        (twistingSheafAtUniverse.{u} r) ≅
      Scheme.Modules.tensorObj
        (powMod ((Scheme.Modules.pullback f₁).obj (twistingSheafAtUniverse.{u} n)) k₁)
        (powMod ((Scheme.Modules.pullback f₂).obj (twistingSheafAtUniverse.{u} n)) k₂)) := by
  set x := pullbackCoordSection.{u} f₁
  set y := pullbackCoordSection.{u} f₂
  set s := fun m => svSec x y hk₁ hk₂ (e m) with hs_def
  have hcov : TopologicalSpace.IsOpenCover (nvCover s) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro p _
    obtain ⟨i, hi⟩ := mem_chartOpen (f₁.base p)
    obtain ⟨j, hj⟩ := mem_chartOpen (f₂.base p)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm (BidegreeExponent.corner δ₁ δ₂ i j), ?_⟩
    change p ∈ nvOpen _ (svSec x y hk₁ hk₂ (e (e.symm (BidegreeExponent.corner δ₁ δ₂ i j))))
    rw [Equiv.apply_symm_apply, svSec_corner]
    refine le_nvOpen_svBase x y i j ⟨?_, ?_⟩
    · exact (Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection f₁ i).ge hi
    · exact (Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection f₂ j).ge hj
  have hpin : ∀ m, (nvCover s m).ι ≫ segreVeroneseHom e f₁ f₂ =
      toProjectiveSpaceAtUniverse (chartRatio s m) (span_range_chartRatio s m) := by
    intro m
    set W := nvCover s m
    set i := word (e m).1 hk₁ 0
    set j := word (e m).2 hk₂ 0
    have hW : W ≤ nvOpen _ (x i) ⊓ nvOpen _ (y j) := nvOpen_svSec_le x y hk₁ hk₂ (e m)
    have hWi : W ≤ nvCover x i := hW.trans inf_le_left
    have hWj : W ≤ nvCover y j := hW.trans inf_le_right
    set ρx : Fin (n + 1) → Γ(Y, W) := fun l => div (x i) hWi (resT W (x l))
    set ρy : Fin (n + 1) → Γ(Y, W) := fun l => div (y j) hWj (resT W (y l))
    have hρx : ∀ l, resO hWi (ratio x i l) = ρx l :=
      fun l => eq_div (x i) hWi (resO_ratio_smul x hWi l)
    have hρy : ∀ l, resO hWj (ratio y j l) = ρy l :=
      fun l => eq_div (y j) hWj (resO_ratio_smul y hWj l)
    have hρxi : ρx i = 1 := (eq_div (x i) hWi (one_smul _ _)).symm
    have hρyj : ρy j = 1 := (eq_div (y j) hWj (one_smul _ _)).symm
    set φ : Γ(Y, W) →+* Γ(W.toScheme, ⊤) := W.topIso.inv.hom
    set t₁ : Fin (n + 1) → Γ(W.toScheme, ⊤) := fun l => φ (ρx l)
    set t₂ : Fin (n + 1) → Γ(W.toScheme, ⊤) := fun l => φ (ρy l)
    have ht₁ : Ideal.span (Set.range t₁) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        (by simp only [t₁, hρxi, map_one, isUnit_one])
    have ht₂ : Ideal.span (Set.range t₂) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩)
        (by simp only [t₂, hρyj, map_one, isUnit_one])
    have hfam₁ : (fun l => (Y.homOfLE hWi).appTop (chartRatio x i l)) = t₁ :=
      funext fun l =>
        (Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv hWi (ratio x i l)).trans
        (congrArg φ (hρx l))
    have hfam₂ : (fun l => (Y.homOfLE hWj).appTop (chartRatio y j l)) = t₂ :=
      funext fun l =>
        (Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv hWj (ratio y j l)).trans
        (congrArg φ (hρy l))
    have hf₁ : W.ι ≫ f₁ = toProjectiveSpaceAtUniverse t₁ ht₁ := by
      rw [← Scheme.homOfLE_ι Y hWi, Category.assoc, Stacks.ProjectiveSpaceModuli.taut_pin f₁ i,
        Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ (by rw [hfam₁]; exact ht₁)]
      exact toProjectiveSpaceAtUniverse_congr hfam₁ _ _
    have hf₂ : W.ι ≫ f₂ = toProjectiveSpaceAtUniverse t₂ ht₂ := by
      rw [← Scheme.homOfLE_ι Y hWj, Category.assoc, Stacks.ProjectiveSpaceModuli.taut_pin f₂ j,
        Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ (by rw [hfam₂]; exact ht₂)]
      exact toProjectiveSpaceAtUniverse_congr hfam₂ _ _
    have hmono : Ideal.span (Set.range fun m' => bidegreeMonomial t₁ t₂ (e m')) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _
        (Ideal.subset_span ⟨e.symm (BidegreeExponent.corner δ₁ δ₂ i j), rfl⟩)
        (by simp only [Equiv.apply_symm_apply, bidegreeMonomial_corner, t₁, t₂, hρxi, hρyj, map_one,
          one_pow, mul_one, isUnit_one])
    have hsv : W.ι ≫ segreVeroneseHom e f₁ f₂ =
        toProjectiveSpaceAtUniverse (fun m' => bidegreeMonomial t₁ t₂ (e m')) hmono := by
      rw [← segreVeroneseHom_comp]
      exact segreVeroneseHom_of_eq e _ _ t₁ t₂ ht₁ ht₂ hf₁ hf₂ hmono
    set c : BidegreeExponent n δ₁ δ₂ → Γ(Y, W) := fun ab => bidegreeMonomial ρx ρy ab
    have hres : ∀ ab, resT W (svSec x y hk₁ hk₂ ab) = c ab • resT W (svBase x y k₁ k₂ i j) :=
      resT_svSec x y hk₁ hk₂ hWi hWj
    have hbase : W ≤ nvOpen _ (svBase x y k₁ k₂ i j) := hW.trans (le_nvOpen_svBase x y i j)
    have hkey : ∀ m', c (e m') = ratio s m m' * c (e m) := by
      intro m'
      apply eq_of_smul_eq_smul _ hbase
      rw [← hres, mul_smul, ← hres]
      exact (ratio_smul s m m').symm
    have hcorner : c (BidegreeExponent.corner δ₁ δ₂ i j) = 1 := by
      simp only [c, bidegreeMonomial_corner, hρxi, hρyj, one_pow, mul_one]
    have h1 : ratio s m (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)) * c (e m) = 1 := by
      rw [← hkey, Equiv.apply_symm_apply, hcorner]
    have hunit : IsUnit (c (e m)) :=
      ⟨⟨c (e m), ratio s m (e.symm (BidegreeExponent.corner δ₁ δ₂ i j)),
        by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    have hfam : (fun m' => bidegreeMonomial t₁ t₂ (e m')) =
        fun m' => ((hunit.map φ).unit : Γ(W.toScheme, ⊤)) * chartRatio s m m' := by
      funext m'
      rw [IsUnit.unit_spec, ← map_bidegreeMonomial φ ρx ρy (e m'), mul_comm]
      change φ (c (e m')) = φ (ratio s m m') * φ (c (e m))
      rw [hkey, map_mul]
    rw [hsv, toProjectiveSpaceAtUniverse_congr hfam _ (by rw [← hfam]; exact hmono)]
    exact Stacks.ProjGlobalSectionsAppTop.hasUnitInvariance _ _ _ _
  obtain ⟨α, hα, -⟩ :=
    exists_iso_pullback_twistingSheafAtUniverse s (segreVeroneseHom e f₁ f₂) hcov hpin
  exact ⟨asIso α⟩

end TwistIso

/-! ### Classes in the Picard group -/

section Picard

open Stacks.SectionProduct Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned

attribute [local instance] isInvertibleModule_powMod

variable {Y : Scheme.{u}}

private theorem isInvertible_of_isInvertibleModule (M : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y M] :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry Y.presheaf _ M h

private theorem picardClass_tensorObj (M N : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule Y N] :
    Y.picardClass (Scheme.Modules.tensorObj M N) (isInvertible_of_isInvertibleModule _) =
      Y.picardClass M (isInvertible_of_isInvertibleModule M) +
        Y.picardClass N (isInvertible_of_isInvertibleModule N) :=
  (Y.picardClass_tensorSheaf M N _ _ _).symm

private theorem picardClass_powMod (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] :
    ∀ k : ℕ, Y.picardClass (powMod A k) (isInvertible_of_isInvertibleModule _) =
      (k + 1) • Y.picardClass A (isInvertible_of_isInvertibleModule A)
  | 0 => by rw [zero_add, one_smul]; rfl
  | k + 1 => by
      rw [show Y.picardClass (powMod A (k + 1)) (isInvertible_of_isInvertibleModule _) =
          Y.picardClass (Scheme.Modules.tensorObj A (powMod A k))
            (isInvertible_of_isInvertibleModule _) from rfl,
        picardClass_tensorObj, picardClass_powMod A k, add_smul (k + 1) 1, one_smul, add_comm]

/-- The class of a pullback, in the spelling `Scheme.Modules.pullback`. -/
private theorem pullbackPicardClass_eq_picardClass {X : Scheme.{u}} (φ : Y ⟶ X)
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (h : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf
      ((Scheme.Modules.pullback φ).obj L)) :
    Stacks.SheafOfModules.pullbackPicardClass φ L hL =
      Y.picardClass ((Scheme.Modules.pullback φ).obj L) h :=
  (Y.picardClass_eq_iff _ _ _ _).mpr
    ⟨(((Scheme.Modules.pullbackPushforwardAdjunction φ).leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        φ.toLRSHom.toShHom)).app L).symm⟩

/-- Pulling back the class of `ψ^* L` along `φ` gives the class of `(φ ≫ ψ)^* L`. -/
private theorem schemePullbackClassHom_pullbackPicardClass {X Z : Scheme.{u}} (φ : Y ⟶ X)
    (ψ : X ⟶ Z) (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatIsSheaf L) :
    Stacks.Picard.schemePullbackClassHom φ (Stacks.SheafOfModules.pullbackPicardClass ψ L hL) =
      Stacks.SheafOfModules.pullbackPicardClass (φ ≫ ψ) L hL := by
  have := hL
  rw [Stacks.SheafOfModules.pullbackPicardClass_comp φ ψ L hL
    (Stacks.RingedSpace.modulePullback_isInvertible _ L)]
  exact Stacks.Picard.pullbackClass_classOf _ _ _

/-- The class of `g^* 𝒪(1)` for `g : W ⟶ ℙᵐ_S`, computed on the integral model `ℙᵐ_ℤ`. -/
private theorem pullbackPicardClass_twistOver {S W : Scheme.{u}} {m : ℕ}
    (g : W ⟶ projectiveSpaceOver m S) :
    Stacks.SheafOfModules.pullbackPicardClass g
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver m S 1)
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver m S 1) =
      W.picardClass
        ((Scheme.Modules.pullback (g ≫ projectiveSpaceOver.toIntegralAtUniverse m S)).obj
          (twistingSheafAtUniverse.{u} m)) (isInvertible_of_isInvertibleModule _) := by
  have := @Stacks.InvertiblePullback.isInvertibleModule_pullback _ _ g _
    (isInvertibleModule_pullback_twistingSheafAtUniverse
      (projectiveSpaceOver.toIntegralAtUniverse m S))
  rw [pullbackPicardClass_eq_picardClass g _ _ (isInvertible_of_isInvertibleModule _)]
  exact (W.picardClass_eq_iff _ _ _ _).mpr ⟨(Scheme.Modules.pullbackComp g _).app _⟩

/-- **`sv(f₁, f₂)^* 𝒪(1)` has class `δ₁ [f₁^* 𝒪(1)] + δ₂ [f₂^* 𝒪(1)]`**, for `δ₁, δ₂ ≥ 1`. -/
private theorem picardClass_pullback_segreVeroneseHom {δ₁ δ₂ r : ℕ} (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂)
    (e : Fin (r + 1) ≃ BidegreeExponent n δ₁ δ₂) (f₁ f₂ : Y ⟶ projectiveSpaceAtUniverse.{u} n) :
    Y.picardClass ((Scheme.Modules.pullback (segreVeroneseHom e f₁ f₂)).obj
        (twistingSheafAtUniverse.{u} r)) (isInvertible_of_isInvertibleModule _) =
      δ₁ • Y.picardClass ((Scheme.Modules.pullback f₁).obj (twistingSheafAtUniverse.{u} n))
          (isInvertible_of_isInvertibleModule _) +
        δ₂ • Y.picardClass ((Scheme.Modules.pullback f₂).obj (twistingSheafAtUniverse.{u} n))
          (isInvertible_of_isInvertibleModule _) := by
  obtain ⟨α⟩ := nonempty_pullback_segreVeroneseHom_iso (Nat.sub_add_cancel h₁).symm
    (Nat.sub_add_cancel h₂).symm e f₁ f₂
  rw [(Y.picardClass_eq_iff _ _ _ (isInvertible_of_isInvertibleModule _)).mpr ⟨α⟩,
    picardClass_tensorObj, picardClass_powMod, picardClass_powMod, Nat.sub_add_cancel h₁,
    Nat.sub_add_cancel h₂]

end Picard

end Helpers

/-- **Class of the Segre–Veronese embedding.** Let `X = (C, P)` be a curve of genus `≥ 2` over
an algebraic extension `k` of `ℚ` with a divisor `P` of degree one, let `N ≥ 2g + 1` and let
`φ : C ⟶ ℙⁿ_k` be a projective embedding of class `N [P]`. Let `δ₁, δ₂ ≥ 1`, let `e` enumerate
the monomials of bidegree `(δ₁, δ₂)`, let `v : ℙⁿ_k ×_k ℙⁿ_k ⟶ ℙʳ_k` be the Segre–Veronese
morphism over `k` (its value at the `K`-point `([c], [c'])` being
`segreVeroneseComposite K δ₁ δ₂ h₁ h₂ id ([c], [c'])`), and let `ψ` be the projective embedding
`(φ ×_k φ) ≫ v` of `C ×_k C`. Then `cl(ψ) = δ₁ N (P × C) + δ₂ N (C × P)` in `Pic(C ×_k C)`. -/
@[faltings "lem_bv_class_segre_veronese"]
public theorem embeddingClass_segreVeronese_eq_vojtaClass {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ}
    (φ : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (hφ : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      embeddingClass X.f (FreeAbelianGroup.of ⟨n, φ⟩) =
        (N : ℤ) • X.P.sum fun x m =>
          haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
          haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
          m • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (δ₁ δ₂ : ℕ) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) {r : ℕ}
    (e : Fin (r + 1) ≃
      {a : Fin (n + 1) →₀ ℕ // a.degree = δ₁} × {b : Fin (n + 1) →₀ ℕ // b.degree = δ₂})
    (v : pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ⟶
          projectiveSpaceOver r (Spec (.of k)))
    (hv_over : v ≫ (projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
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
    [IsProjectiveVariety k (pullback.fst X.f X.f ≫ X.f)] [Smooth (pullback.fst X.f X.f ≫ X.f)]
    (ψ : ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) r)
    (hψ : ψ.hom = pullback.map X.f X.f _ _ φ.hom φ.hom (𝟙 _) (by simp [φ.hom_over])
      (by simp [φ.hom_over]) ≫ v) :
    embeddingClass (pullback.fst X.f X.f ≫ X.f) (FreeAbelianGroup.of ⟨r, ψ⟩) =
      X.vojtaClass ((δ₁ : ℤ) * N) ((δ₂ : ℤ) * N) 0 := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have hsv : ψ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse r (Spec (.of k)) =
      segreVeroneseHom e (pullback.fst X.f X.f ≫ φ.hom ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
        (pullback.snd X.f X.f ≫ φ.hom ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) := by
    rw [hψ, Category.assoc, comp_toIntegral_eq_segreVeroneseHom h₁ h₂ e v hv,
      ← segreVeroneseHom_comp]
    congr 1 <;> simp only [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc]
  have hpr : ∀ pr : pullback X.f X.f ⟶ X.C,
      (pullback X.f X.f).picardClass ((Scheme.Modules.pullback (pr ≫ φ.hom ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n))
        (isInvertible_of_isInvertibleModule _) =
      Stacks.Picard.schemePullbackClassHom pr
        (embeddingClass X.f (FreeAbelianGroup.of ⟨n, φ⟩)) := fun pr => by
    simp only [embeddingClass, FreeAbelianGroup.lift_apply_of]
    rw [schemePullbackClassHom_pullbackPicardClass, pullbackPicardClass_twistOver, Category.assoc]
  simp only [embeddingClass, FreeAbelianGroup.lift_apply_of]
  rw [pullbackPicardClass_twistOver, hsv, picardClass_pullback_segreVeroneseHom h₁ h₂, hpr, hpr,
    hφ, CurveWithDegreeOneDivisor.vojtaClass, zero_smul, add_zero, map_zsmul, map_zsmul,
    ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]

end Faltings.CurveWithDegreeOneDivisor
