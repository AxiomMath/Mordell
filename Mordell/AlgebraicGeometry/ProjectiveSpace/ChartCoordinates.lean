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

/-!
# Ratio coordinates of morphisms to a chart of `ℙⁿ`

For a morphism `f : Y ⟶ ℙⁿ_ℤ` landing in the standard chart `D₊(T_i)`: its lift to the chart, the
coordinates `T_l / T_i` as global functions on `Y`, and how they compose, multiply and generate.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings.CurveWithDegreeOneDivisor

section Helpers

variable {n : ℕ}

/-! ### Morphisms to a chart of `ℙⁿ` and their ratio coordinates -/

/-- If `f` maps `Y` into the `i`-th chart, the range of `f` lies in the range of the chart's
inclusion. -/
public theorem range_subset_of_preimage_eq_top {Y : Scheme.{u}}
    (f : Y ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) :
    Set.range f.base ⊆ Set.range (chartOpen.{u} i).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  exact h.ge trivial

/-- The factorization of a morphism landing in the `i`-th chart through that chart. -/
@[expose] public noncomputable def chartLift {Y : Scheme.{u}}
    (f : Y ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) :
    Y ⟶ (chartOpen.{u} i).toScheme :=
  IsOpenImmersion.lift (chartOpen.{u} i).ι f (range_subset_of_preimage_eq_top f i h)

/-- The lift of `f` to the `i`-th chart, followed by the chart's inclusion, is `f`. -/
public theorem chartLift_ι {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) :
    chartLift f i h ≫ (chartOpen.{u} i).ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The pulled back ratio coordinates `T_l / T_i` of a morphism landing in the `i`-th chart. -/
@[expose] public noncomputable def coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (l : Fin (n + 1)) : Γ(Y, ⊤) :=
  (chartLift f i h).appTop (chartRatio.{u} i l)

/-- The ratio coordinate `T_i / T_i` in the `i`-th chart is `1`. -/
public theorem coord_self {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) : coord f i h i = 1 := by
  simp only [coord, chartRatio_self, map_one]

/-- The ratio coordinates of `f` in the `i`-th chart generate the unit ideal of `Γ(Y, ⊤)`. -/
public theorem span_coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) :
    Ideal.span (Set.range (coord f i h)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    (by rw [coord_self]; exact isUnit_one)

/-- A morphism landing in the `i`-th chart is the morphism to `ℙⁿ` given by its ratio
coordinates. -/
public theorem eq_toPSAU_coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) :
    f = toProjectiveSpaceAtUniverse (coord f i h) (span_coord f i h) := by
  conv_lhs => rw [← chartLift_ι f i h, chartOpen_ι_eq]
  exact Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ _

/-- Equal morphisms have equal ratio coordinates. -/
public theorem coord_congr {Y : Scheme.{u}} {f f' : Y ⟶ projectiveSpaceAtUniverse.{u} n}
    (hf : f = f') (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤)
    (h' : f' ⁻¹ᵁ chartOpen.{u} i = ⊤) : coord f i h = coord f' i h' := by
  subst hf; rfl

/-- If `f` maps `Y` into the `i`-th chart, then so does `g ≫ f` map `Z`. -/
public theorem preimage_comp_eq_top {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (f : Y ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) : (g ≫ f) ⁻¹ᵁ chartOpen.{u} i = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]

/-- The ratio coordinates of `g ≫ f` are the pullbacks along `g` of those of `f`. -/
public theorem coord_comp {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (f : Y ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (h' : (g ≫ f) ⁻¹ᵁ chartOpen.{u} i = ⊤) (l : Fin (n + 1)) :
    coord (g ≫ f) i h' l = g.appTop (coord f i h l) := by
  have : chartLift (g ≫ f) i h' = g ≫ chartLift f i h := by
    rw [← cancel_mono (chartOpen.{u} i).ι, chartLift_ι, Category.assoc, chartLift_ι]
  simp only [coord, this, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Pulling a global section back along the inclusion of an open `V` is its restriction to `V`,
read through `V.topIso`. -/
public theorem ι_appTop_eq {Y : Scheme.{u}} (V : Y.Opens) (a : Γ(Y, ⊤)) :
    V.ι.appTop a = V.topIso.inv (Stacks.ProjGlobalSectionsAppTop.resTop V a) := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (ConcreteCategory.congr_hom (Y.presheaf.map_comp _ _) a)

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The pulled back ratio coordinates of the morphism of a spanning family.** If `f` is the
morphism of `s` and lands in the `i`-th chart, then `s i * (T_l / T_i) = s l`. -/
public theorem mul_coord_of_eq {Y : Scheme.{u}} (s : Fin (n + 1) → Γ(Y, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (hf : f = toProjectiveSpaceAtUniverse s hs) (i : Fin (n + 1))
    (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (l : Fin (n + 1)) :
    s i * coord f i h l = s l := by
  subst hf
  rw [← sectionsHom_X s i, ← sectionsHom_X s l]
  set V := Y.basicOpen (sectionsHom s (MvPolynomial.X i)) with hVdef
  have hV : V = ⊤ := by rw [hVdef, sectionsHom_X, ← preimage_basicOpen s hs i]; exact h
  have hiso : IsIso V.ι := by rw [hV, ← Scheme.topIso_hom]; infer_instance
  have hinj : Function.Injective V.ι.appTop := by
    intro x y hxy
    have h1 : ∀ z, (inv V.ι).appTop (V.ι.appTop z) = z := fun z => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
        Scheme.Hom.id_appTop]
      rfl
    rw [← h1 x, ← h1 y, hxy]
  apply hinj
  have hle : V ≤ toProjectiveSpaceAtUniverse s hs ⁻¹ᵁ chartOpen.{u} i :=
    (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom s)
          (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one i)).ge
  have key : V.ι ≫ chartLift (toProjectiveSpaceAtUniverse s hs) i h =
      (toProjectiveSpaceAtUniverse s hs).resLE (chartOpen.{u} i) V hle := by
    rw [← cancel_mono (chartOpen.{u} i).ι, Category.assoc, chartLift_ι, Scheme.Hom.resLE_comp_ι]
  have hres := resLE_toProjectiveSpaceAtUniverse s hs i
  have happ := Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop
    (coordGrading.{u} n) (sectionsHom s) Nat.one_pos (X_mem_coordGrading_one i)
  have hc : V.ι.appTop (coord (toProjectiveSpaceAtUniverse s hs) i h l) =
      V.topIso.inv (Stacks.ProjGlobalSectionsAppTop.projAwayHom (coordGrading.{u} n)
        (sectionsHom s) (HomogeneousLocalization.Away.mk (coordGrading.{u} n)
          (X_mem_coordGrading_one i) 1 (MvPolynomial.X l) (X_mem_coordGrading_smul l))) := by
    rw [coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, key, hres]
    exact ConcreteCategory.congr_hom happ _
  rw [map_mul, hc, Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk, ι_appTop_eq,
    ι_appTop_eq, ← map_mul, pow_one, ← mul_assoc,
    mul_comm (Stacks.ProjGlobalSectionsAppTop.resTop _ _),
    mul_assoc, IsUnit.mul_val_inv, mul_one]

/-- Ratio coordinates in two charts satisfy `(T_i' / T_i) * (T_l / T_i') = T_l / T_i`. -/
public theorem coord_mul_coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i i' : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (h' : f ⁻¹ᵁ chartOpen.{u} i' = ⊤)
    (l : Fin (n + 1)) : coord f i h i' * coord f i' h' l = coord f i h l :=
  mul_coord_of_eq (coord f i h) (span_coord f i h) f (eq_toPSAU_coord f i h) i' h' l

/-- If `f` lands in both the `i`-th and the `i'`-th chart, then `T_i' / T_i` is a unit. -/
public theorem isUnit_coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i i' : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (h' : f ⁻¹ᵁ chartOpen.{u} i' = ⊤) :
    IsUnit (coord f i h i') :=
  IsUnit.of_mul_eq_one (coord f i' h' i) (by rw [coord_mul_coord, coord_self])

/-- The basic open of the ratio coordinate `T_l / T_i` is the preimage of the `l`-th chart. -/
public theorem basicOpen_coord {Y : Scheme.{u}} (f : Y ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) (h : f ⁻¹ᵁ chartOpen.{u} i = ⊤) (l : Fin (n + 1)) :
    Y.basicOpen (coord f i h l) = f ⁻¹ᵁ chartOpen.{u} l := by
  conv_rhs => rw [eq_toPSAU_coord f i h]
  exact (preimage_basicOpen _ _ l).symm

/-- A global section whose basic open is the whole scheme is a unit. -/
public theorem isUnit_of_basicOpen_eq_top {Y : Scheme.{u}} (a : Γ(Y, ⊤))
    (h : Y.basicOpen a = ⊤) : IsUnit a := by
  have hu := Y.toRingedSpace.isUnit_res_basicOpen a
  have h2 : (Y.presheaf.map (homOfLE h.ge).op)
      ((Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op) a) = a := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    exact ConcreteCategory.congr_hom (Y.presheaf.map_id _) a
  rw [← h2]
  exact hu.map _

/-- If `U ≤ f ⁻¹ᵁ V`, then `U.ι ≫ f` maps all of `U` into `V`. -/
public theorem preimage_ι_comp_eq_top {Y X : Scheme.{u}} {U : Y.Opens} (f : Y ⟶ X)
    (V : X.Opens) (h : U ≤ f ⁻¹ᵁ V) : (U.ι ≫ f) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, eq_top_iff]
  exact fun x _ => h x.2

end Helpers

end Faltings.CurveWithDegreeOneDivisor
