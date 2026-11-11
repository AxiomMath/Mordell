module
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.BombieriVojta.Projection.Finite
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSections
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.OrderComparison
public import Mordell.Curve.Topology
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import Mordell.Curve.DegreeOverRationalSubfield

/-!
# The affine part of `π_{ab}`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P₁` a divisor of degree one supported on closed points (the source's `P`), `N ≥ 2g + 1`,
and `x₀, …, xₙ` a `k`-basis of `L(N P₁)` inside `k(C)`. Let `U = {x₀ ≠ 0} ⊆ C` be the locus
where the section `x₀` of `𝒪(N P₁)` has no zero, and for `a, b ∈ {1, …, n}` let
`π_{ab} = (x₀ : x_a ; x'₀ : x'_b) : C ×_k C ⤏ ℙ¹_k ×_k ℙ¹_k` be the product projection. If the
basis satisfies (G1), then `π_{ab}` is a morphism and
`π_{ab}⁻¹(𝔸¹ × 𝔸¹) = U × U`, where `𝔸¹ = {T₀ ≠ 0} ⊆ ℙ¹_k`.

The proof works one factor at a time. For `c ∈ {1, …, n}` let `φ_c : C ⟶ ℙ¹_k` be the morphism
inducing `π_c = (x₀ : x_c)`. If `φ_c Q ∈ D₊(T₀)`, the pull-back `x_c / x₀` of `T₁ / T₀` is regular
at `Q`, so `ord_Q x₀ ≤ ord_Q x_c` and (G1) forces `ord_Q x₀ + (N P₁)(Q) = 0`; otherwise
`φ_c Q ∈ D₊(T₁)` and the pull-back `x₀ / x_c` of `T₀ / T₁` lies in the maximal ideal of `𝒪_{C,Q}`,
so `ord_Q x₀ + (N P₁)(Q) > ord_Q x_c + (N P₁)(Q) ≥ 0`. Hence `φ_c⁻¹(𝔸¹) = U`. The product
`φ_a ×_k φ_b` induces `π_{ab}`, and the preimage of `𝔸¹ × 𝔸¹` under it is `U × U`.

## Main results

* `Faltings.BombieriVojta.exists_toRationalMap_eq_productProjectionToProjectiveLine_and_preimage`:
  `π_{ab}` is induced by a morphism `φ`, and `φ⁻¹(𝔸¹ × 𝔸¹) = U × U`.

## Implementation notes

As in `Faltings.BombieriVojta.productProjectionToProjectiveLine`, sections of `𝒪(N P₁)` are
rational functions in `L(N P₁) ⊆ k(C)`, and the section `x₀` vanishes at `Q` when
`0 < ord_Q x₀ + (N P₁)(Q)`; so `U` is the set of points `Q` with `ord_Q x₀ + (N P₁)(Q) ≤ 0`. At the
generic point both terms are `0`, so the generic point lies in `U`. The chart `𝔸¹ ⊆ ℙ¹_k` is the
preimage of the standard open `D₊(T₀)` of `Proj ℤ[T₀, T₁]` under the projection to the integral
model, and `𝔸¹ × 𝔸¹` is the intersection of the preimages of `𝔸¹` under the two projections of
`ℙ¹_k ×_k ℙ¹_k`; likewise `U × U` is the intersection of the preimages of `U` under the two
projections of `C ×_k C`. The rational map `π_{ab}` is pinned as `φ.toRationalMap`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open Faltings.FunctionField (coheight_genericPoint_ne_one)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Faltings.BombieriVojta

open Faltings.BombieriSiegel Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section Charts

/-- The `i`-th standard chart `D₊(Tᵢ)` of `ℙ¹_S`. -/
@[expose] public noncomputable abbrev chartP1 (S : Scheme.{u}) (i : Fin 2) :
    (projectiveSpaceOver 1 S).Opens :=
  projectiveSpaceOver.toIntegralAtUniverse 1 S ⁻¹ᵁ
    Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)

/-- The coordinate `T_m` of `ℙ¹` is homogeneous of degree `1 • 1`. -/
public lemma X_mem_coordGrading_one_smul (m : Fin 2) :
    (MvPolynomial.X m : coordRing.{u} 1) ∈ coordGrading.{u} 1 (1 • 1) := by
  rw [smul_eq_mul, mul_one]
  exact X_mem_coordGrading_one m

/-- The affine coordinate `T_m / T_i` on the chart `D₊(Tᵢ)` of `ℙ¹_S`. -/
@[expose] public noncomputable def ratioSection (S : Scheme.{u}) (i m : Fin 2) :
    Γ(projectiveSpaceOver 1 S, chartP1 S i) :=
  (projectiveSpaceOver.toIntegralAtUniverse 1 S).appLE
    (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) (chartP1 S i) le_rfl
    ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.Away.mk (coordGrading.{u} 1) (X_mem_coordGrading_one i) 1
        (MvPolynomial.X m) (X_mem_coordGrading_one_smul m)))

/-- Equal morphisms of schemes have equal `appLE` maps. -/
public lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The preimage of the chart `D₊(Tᵢ)` under the morphism of the sections `s` is the
nonvanishing locus of `sᵢ`. -/
public lemma preimage_chartP1 {X S : Scheme.{u}} (s : Fin 2 → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (g : X ⟶ S) (i : Fin 2) :
    toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 S i = X.basicOpen (s i) := by
  change (toProjectiveSpaceOver s hs g ≫ projectiveSpaceOver.toIntegralAtUniverse 1 S) ⁻¹ᵁ
    Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i) = _
  rw [toProjectiveSpaceOver_snd]
  exact preimage_basicOpen s hs i

/-- The pull-back of `T_m / T_i` by the morphism of the sections `s` is `s_m / s_i`. -/
private lemma appLE_ratioSection {X S : Scheme.{u}} (s : Fin 2 → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (g : X ⟶ S) (i : Fin 2) (hi : IsUnit (s i))
    (m : Fin 2) (h : ⊤ ≤ toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 S i) :
    (toProjectiveSpaceOver s hs g).appLE (chartP1 S i) ⊤ h (ratioSection S i m) =
      s m * ↑hi.unit⁻¹ := by
  set G := toProjectiveSpaceAtUniverse s hs with hGdef
  have hG : toProjectiveSpaceOver s hs g ≫ projectiveSpaceOver.toIntegralAtUniverse 1 S = G :=
    toProjectiveSpaceOver_snd s hs g
  have hle : (⊤ : X.Opens) ≤ G ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i) := by
    rw [← hG]
    exact h
  let v := HomogeneousLocalization.Away.mk (coordGrading.{u} 1) (X_mem_coordGrading_one i) 1
    (MvPolynomial.X m) (X_mem_coordGrading_one_smul m)
  have h1 : (toProjectiveSpaceOver s hs g).appLE (chartP1 S i) ⊤ h (ratioSection S i m) =
      G.appLE (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) ⊤ hle
        ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom v) :=
    (congrArg (fun φ => φ.hom ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom v))
      (Scheme.Hom.appLE_comp_appLE (toProjectiveSpaceOver s hs g)
        (projectiveSpaceOver.toIntegralAtUniverse 1 S)
        (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) (chartP1 S i) ⊤ le_rfl h)).trans
      (congrArg
        (fun φ => φ.hom ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom v))
        (appLE_eq_of_eq hG (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) ⊤ h))
  set W := X.basicOpen (sectionsHom s (MvPolynomial.X i)) with hWdef
  have hW : W = ⊤ := by
    rw [hWdef, sectionsHom_X]
    exact Scheme.basicOpen_of_isUnit _ hi
  have hinj : Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    clear_value W
    subst hW
    simpa using Function.injective_id
  apply hinj
  have hchart := Stacks.LinearSystemScheme.awayToSection_comp_appLE_fromOfGlobalSections
    (𝒜 := coordGrading.{u} 1) (sectionsHom s) (map_irrelevant_eq_top s hs) one_pos
    (X_mem_coordGrading_one i)
  have hval := congrArg (fun F => F.hom v) hchart
  simp only [v, CommRingCat.hom_ofHom] at hval
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk] at hval
  have h2 := congrArg
    (fun φ => φ.hom ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom v))
    (Scheme.Hom.appLE_map G hle (homOfLE (le_top : W ≤ ⊤)).op)
  refine (congrArg _ h1).trans (h2.trans (hval.trans ?_))
  have e0 : sectionsHom s (MvPolynomial.X i) * (↑hi.unit⁻¹ : Γ(X, ⊤)) = 1 := by
    rw [sectionsHom_X]; exact hi.mul_val_inv
  have e2 : Stacks.ProjGlobalSectionsAppTop.resTopBasicOpenInv (sectionsHom s (MvPolynomial.X i)) =
      (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (↑hi.unit⁻¹) := by
    symm
    apply Units.eq_inv_of_mul_eq_one_left
    rw [IsUnit.unit_spec, ← map_mul, e0, map_one]
  rw [e2, pow_one, map_mul]
  exact congrArg (· * _) (congrArg (Stacks.ProjGlobalSectionsAppTop.resTop W) (sectionsHom_X s m))

/-- The coordinate charts `D₊(T₀)` and `D₊(T₁)` cover `ℙ¹_S`. -/
private lemma mem_chartP1_zero_or_one (S : Scheme.{u}) (y : projectiveSpaceOver 1 S) :
    y ∈ chartP1 S 0 ∨ y ∈ chartP1 S 1 := by
  have h : y ∈ ⨆ i, Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.coordChart 1 S i := by
    rw [Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.iSup_coordChart_eq_top]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- Off the chart `D₊(T₀)`, the affine coordinate `T₀ / T₁` of the chart `D₊(T₁)` vanishes. -/
private lemma not_isUnit_germ_ratioSection (S : Scheme.{u}) (y : projectiveSpaceOver 1 S)
    (hy : y ∈ chartP1 S 1) (hy0 : y ∉ chartP1 S 0) :
    ¬IsUnit ((projectiveSpaceOver 1 S).presheaf.germ (chartP1 S 1) y hy
      (ratioSection S 1 0)) := by
  intro hu
  set ψ := projectiveSpaceOver.toIntegralAtUniverse 1 S with hψ
  have hz : ψ y ∈ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X 1) := hy
  let t := HomogeneousLocalization.Away.mk (coordGrading.{u} 1) (X_mem_coordGrading_one 1) 1
    (MvPolynomial.X 0) (X_mem_coordGrading_one_smul 0)
  have h1 : (projectiveSpaceOver 1 S).presheaf.germ (chartP1 S 1) y hy (ratioSection S 1 0) =
      ψ.stalkMap y ((projectiveSpaceAtUniverse.{u} 1).presheaf.germ _ (ψ y) hz
        ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom t)) := by
    have hr : ratioSection S 1 0 =
        ψ.app _ ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom t) :=
      (congrArg (fun F => F.hom
        ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom t))
        (Scheme.Hom.app_eq_appLE (f := ψ)
          (U := Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X 1)))).symm
    rw [hr]
    exact (Scheme.Hom.germ_stalkMap_apply ψ _ y hz _).symm
  rw [h1] at hu
  have hu' := (isUnit_map_iff (ψ.stalkMap y).hom _).mp hu
  have h2 := congrArg (fun F => F.hom t)
    (ProjectiveSpectrum.Proj.awayToSection_germ (coordGrading.{u} 1) (MvPolynomial.X 1) (ψ y) hz)
  erw [h2] at hu'
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hu'
  have h3 := (isUnit_map_iff (Proj.stalkIso' (coordGrading.{u} 1) (ψ y)).symm _).mp hu'
  apply hy0
  change ψ y ∈ Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X 0)
  refine (Proj.mem_basicOpen (coordGrading.{u} 1) (MvPolynomial.X 0) (ψ y)).mpr fun hmem => ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at h3
  simp only [t, HomogeneousLocalization.Away.mk] at h3
  erw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk] at h3
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at h3
  exact h3 hmem

end Charts

section FieldPoint

variable {F : Type u} [Field F] {S : Scheme.{u}} (x' : Fin 2 → F) (hx' : ∀ m, x' m ≠ 0)
  (g : Spec (.of F) ⟶ S)

/-- Over a field `F`, the inverse of the unit `x_i` of `Γ(Spec F, ⊤)` is read in `F` as
`(x_i)⁻¹`. -/
public lemma ΓSpecIso_hom_unit_inv {i : Fin 2}
    (hi : IsUnit ((Scheme.ΓSpecIso (.of F)).inv (x' i))) :
    (Scheme.ΓSpecIso (.of F)).hom ↑hi.unit⁻¹ = (x' i)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have e := congrArg (Scheme.ΓSpecIso (.of F)).hom.hom hi.val_inv_mul
  rwa [map_mul, map_one, Iso.inv_hom_id_apply] at e

include hx' in
/-- Over a field `F`, the pull-back of `T_m / T_i` by the `F`-point `(x₀ : x₁)` is `x_m / x_i`. -/
private lemma ΓSpecIso_appLE_ratioSection (i m : Fin 2)
    (hs : Ideal.span (Set.range fun m => (Scheme.ΓSpecIso (.of F)).inv (x' m)) = ⊤)
    (h : ⊤ ≤ toProjectiveSpaceOver _ hs g ⁻¹ᵁ chartP1 S i) :
    (Scheme.ΓSpecIso (.of F)).hom
        ((toProjectiveSpaceOver _ hs g).appLE (chartP1 S i) ⊤ h (ratioSection S i m)) =
      x' m * (x' i)⁻¹ := by
  have hi : IsUnit ((Scheme.ΓSpecIso (.of F)).inv (x' i)) :=
    (Ne.isUnit (hx' i)).map (Scheme.ΓSpecIso (.of F)).inv.hom
  rw [appLE_ratioSection _ hs g i hi m h, map_mul, ΓSpecIso_hom_unit_inv x' hi,
    Iso.inv_hom_id_apply]

end FieldPoint

section Curve

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A rational function regular at `x` has non-negative order at `x`. -/
public lemma ord_algebraMap_stalk_nonneg (x : X) (r : X.presheaf.stalk x) :
    0 ≤ X.ord (algebraMap _ X.functionField r) x := by
  by_cases hx : Order.coheight x = 1
  · by_cases hr : r = 0
    · simp [hr]
    have hf : algebraMap _ X.functionField r ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    rw [Scheme.le_ord_iff hx hf]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    exact Ring.ordFrac_ge_one_of_ne_zero hr
  · simp [hx]

/-- The order of the inverse: `Stacks.Chow.ord_inv_functionField` with the point first. -/
public lemma ord_inv (x : X) {f : X.functionField} (hf : f ≠ 0) :
    X.ord f⁻¹ x = -X.ord f x :=
  Stacks.Chow.ord_inv_functionField hf x

/-- The pull-back of a section `r` of `𝒪_Y`, read in the function field `k(X)`, is its pull-back
to the generic point. -/
public lemma germToFunctionField_app {Y : Scheme.{u}} (φ : X ⟶ Y) (V : Y.Opens)
    [hV : Nonempty (φ ⁻¹ᵁ V)] (h : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ φ) ⁻¹ᵁ V)
    (r : Γ(Y, V)) :
    X.germToFunctionField (φ ⁻¹ᵁ V) (φ.app V r) =
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom
        ((X.fromSpecStalk (genericPoint X) ≫ φ).appLE V ⊤ h r) := by
  have hη : genericPoint X ∈ φ ⁻¹ᵁ V :=
    ((genericPoint_spec X).mem_open_set_iff (φ ⁻¹ᵁ V).isOpen).mpr (by simpa using hV)
  have key : φ.app V ≫ X.presheaf.germ (φ ⁻¹ᵁ V) (genericPoint X) hη =
      (X.fromSpecStalk (genericPoint X) ≫ φ).appLE V ⊤ h ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ V (φ ⁻¹ᵁ V) ⊤ le_rfl h, ← Scheme.Hom.app_eq_appLE]
    simp only [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hη, Category.assoc,
      ← Functor.map_comp]
    have e : ∀ g : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ⟶ ⊤,
        (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map g.op = 𝟙 _ := fun g => by
      rw [Subsingleton.elim g (𝟙 _), op_id, CategoryTheory.Functor.map_id]
    simp only [← op_comp]
    erw [e, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun F => F.hom r) key

/-- The germ at `Q ∈ X` of the pull-back of a section `r` of `𝒪_Y` near `φ Q`, read in the
function field `k(X)`, is the pull-back of `r` to the generic point. -/
public lemma algebraMap_stalkMap_germ {Y : Scheme.{u}} (φ : X ⟶ Y) (Q : X) (V : Y.Opens)
    (hQ : φ Q ∈ V) (h : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ φ) ⁻¹ᵁ V) (r : Γ(Y, V)) :
    algebraMap (X.presheaf.stalk Q) X.functionField
        (φ.stalkMap Q (Y.presheaf.germ V (φ Q) hQ r)) =
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom
        ((X.fromSpecStalk (genericPoint X) ≫ φ).appLE V ⊤ h r) := by
  have : Nonempty (φ ⁻¹ᵁ V) := ⟨⟨Q, hQ⟩⟩
  rw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact germToFunctionField_app φ V h r

/-- If `y / z` is regular at `x`, then `ord_x z ≤ ord_x y`. -/
public lemma ord_le_of_algebraMap_eq_mul_inv (x : X) {y z : X.functionField} (hy : y ≠ 0)
    (hz : z ≠ 0) (r : X.presheaf.stalk x) (h : algebraMap _ X.functionField r = y * z⁻¹) :
    X.ord z x ≤ X.ord y x := by
  have := ord_algebraMap_stalk_nonneg x r
  rw [h, Scheme.ord_mul hy (inv_ne_zero hz), ord_inv x hz] at this
  omega

/-- At a point of coheight one, a nonzero non-unit of the local ring has positive order. -/
private lemma ord_pos_of_not_isUnit {x : X} (hx : Order.coheight x = 1)
    {r : X.presheaf.stalk x} (hr0 : r ≠ 0) (hr : ¬IsUnit r) :
    0 < X.ord (algebraMap _ X.functionField r) x := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    Stacks.Chow.krullDimLE_one_stalk_of_coheight_eq_one hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk x) (mem_nonZeroDivisors_of_ne_zero hr0))
  rw [Stacks.Chow.ord_algebraMap_eq_ringOrd hx hr0 hm.symm, Nat.cast_pos]
  by_contra hle
  have hm0 : Ring.ord (X.presheaf.stalk x) r = 0 := by
    simp [← hm, Nat.eq_zero_of_not_pos hle]
  exact hr (Ideal.span_singleton_eq_top.mp
    (Ideal.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp hm0)))

end Curve

/-- The morphism to projective space attached to a family of sections is natural in the source:
precomposing with `g` gives the morphism of the pulled-back sections. -/
public theorem comp_toProjectiveSpaceAtUniverse {X Y : Scheme.{u}} {n : ℕ} (g : Y ⟶ X)
    (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (hgs : Ideal.span (Set.range fun i => g.appTop (s i)) = ⊤) :
    g ≫ toProjectiveSpaceAtUniverse s hs =
      toProjectiveSpaceAtUniverse (fun i => g.appTop (s i)) hgs := by
  have key : g.appTop.hom.comp (sectionsHom s) = sectionsHom (fun i => g.appTop (s i)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp)
    simp [sectionsHom, coeffHom]
  unfold toProjectiveSpaceAtUniverse
  refine (ModuliEllipticCurves.Weierstrass.comp_fromOfGlobalSections _ g _ _
    (key ▸ map_irrelevant_eq_top _ hgs)).trans ?_
  congr 1

/-- The morphism `X ⟶ ℙⁿ_S` attached to a family of sections is natural in the source. -/
public theorem comp_toProjectiveSpaceOver {X Y S : Scheme.{u}} {n : ℕ} (g : Y ⟶ X)
    (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (hgs : Ideal.span (Set.range fun i => g.appTop (s i)) = ⊤) (b : X ⟶ S) :
    g ≫ toProjectiveSpaceOver s hs b =
      toProjectiveSpaceOver (fun i => g.appTop (s i)) hgs (g ≫ b) := by
  apply pullback.hom_ext
  · simp
  · simpa using comp_toProjectiveSpaceAtUniverse g s hs hgs

/-- Composing the point `(s₀ : s₁)` of `ℙ¹` over the generic point of `C` with a dominant
morphism `pr : X ⟶ C` of integral schemes gives the point `(pr^* s₀ : pr^* s₁)` over the generic
point of `X`. -/
public theorem fromSpecStalk_comp_comp_eq_toProjectiveSpaceOver {S C X : Scheme.{u}}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ S) (pr : X ⟶ C) [IsDominant pr]
    (φ : C ⟶ projectiveSpaceOver 1 S) (s₀ s₁ : C.functionField)
    (hs : Ideal.span (Set.range fun i =>
      (Scheme.ΓSpecIso (.of C.functionField)).inv (![s₀, s₁] i)) = ⊤)
    (hφ : C.fromSpecStalk (genericPoint C) ≫ φ =
      toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of C.functionField)).inv (![s₀, s₁] i)) hs
        (C.fromSpecStalk (genericPoint C) ≫ f))
    (hs' : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv
      (![functionFieldMap pr s₀, functionFieldMap pr s₁] i)) = ⊤) :
    X.fromSpecStalk (genericPoint X) ≫ pr ≫ φ =
      toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv
          (![functionFieldMap pr s₀, functionFieldMap pr s₁] i)) hs'
        (X.fromSpecStalk (genericPoint X) ≫ pr ≫ f) := by
  have hpr := functionFieldMap_fromSpecStalk pr
  have hsec : (fun i => (Spec.map (CommRingCat.ofHom (functionFieldMap pr))).appTop
      ((Scheme.ΓSpecIso (.of C.functionField)).inv (![s₀, s₁] i))) =
      fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv
        (![functionFieldMap pr s₀, functionFieldMap pr s₁] i) := by
    funext i
    have h := congrArg
      (fun F : CommRingCat.of C.functionField ⟶ Γ(Spec (.of X.functionField), ⊤) =>
        F (![s₀, s₁] i))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (functionFieldMap pr)))
    simp only [CommRingCat.comp_apply] at h
    rw [← h]
    fin_cases i <;> rfl
  rw [← reassoc_of% hpr, hφ, comp_toProjectiveSpaceOver _ _ hs (hsec ▸ hs')]
  congr 1
  rw [reassoc_of% hpr]

section Projection

variable {k : Type u} [Field k] [NumberField k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)}
  [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f]
  [IsLocallyNoetherian C] {hg : 2 ≤ genus f} {D : C →₀ ℤ}
  {hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C)} {N : ℕ} {hN : 2 * genus f + 1 ≤ N}
  {hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N} {n : ℕ} {x : Fin (n + 1) → C.functionField}
  {hli : letI := functionFieldAlgebra k f; LinearIndependent k x}
  {hspan : letI := functionFieldAlgebra k f
    ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
      {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q}}
  {c : Fin n} {φ : C ⟶ projectiveSpaceOver 1 (Spec (.of k))}

/-- A morphism inducing `π_c` is a morphism over `k`. -/
public theorem comp_structureMap_of_toRationalMap_eq
    (hφ : φ.toRationalMap = projectionToProjectiveLine k f hg D hDcl N hN hD x hli
        hspan c) :
    φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have h := isOver_projectionToProjectiveLine k f hg D hDcl N hN hD x hli
      hspan c
  rw [← hφ] at h
  rw [← cancel_epi C.topIso.hom]
  exact (Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp h).comp_over

/-- A morphism inducing `π_c` is the point `(x₀ : x_c)` over the generic point of `C`. -/
public theorem fromSpecStalk_comp_of_toRationalMap_eq
    (hφ : φ.toRationalMap = projectionToProjectiveLine k f hg D hDcl N hN hD x hli
        hspan c) :
    C.fromSpecStalk (genericPoint C) ≫ φ =
      toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of C.functionField)).inv (![x 0, x c.succ] i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (letI := functionFieldAlgebra k f; hli.ne_zero 0)).map
            (Scheme.ΓSpecIso (.of C.functionField)).inv.hom))
        (C.fromSpecStalk _ ≫ f) := by
  have h := projectionToProjectiveLine_fromFunctionField k f hg D hDcl N hN hD x hli
      hspan c
  rw [← hφ] at h
  simpa using h

/-- Under (G1), the preimage of the chart `𝔸¹ = D₊(T₀)` under the morphism inducing `π_c` is the
locus where the section `x₀` of `𝒪(D)` does not vanish. -/
private lemma coe_preimage_chartP1_zero
    (hG1 : SatisfiesG1 k f D x)
    (hφ : φ.toRationalMap = projectionToProjectiveLine k f hg D hDcl N hN hD x hli
        hspan c) :
    ((φ ⁻¹ᵁ chartP1 (Spec (.of k)) 0 : C.Opens) : Set C) =
      {Q | C.ord (x 0) Q + D Q ≤ 0} := by
  let := functionFieldAlgebra k f
  let x' : Fin 2 → C.functionField := ![x 0, x c.succ]
  have hx' : ∀ m, x' m ≠ 0 := by
    intro m
    fin_cases m
    · exact hli.ne_zero 0
    · exact hli.ne_zero c.succ
  let s : Fin 2 → Γ(Spec (.of C.functionField), ⊤) :=
    fun m => (Scheme.ΓSpecIso (.of C.functionField)).inv (x' m)
  have hsU : ∀ m, IsUnit (s m) := fun m =>
    (Ne.isUnit (hx' m)).map (Scheme.ΓSpecIso (.of C.functionField)).inv.hom
  have hs : Ideal.span (Set.range s) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) (hsU 0)
  have hjφ : C.fromSpecStalk (genericPoint C) ≫ φ =
      toProjectiveSpaceOver s hs (C.fromSpecStalk (genericPoint C) ≫ f) :=
    fromSpecStalk_comp_of_toRationalMap_eq (hD := hD) (hspan := hspan) hφ
  set g := C.fromSpecStalk (genericPoint C) ≫ f with hgdef
  have hpre : ∀ i, ⊤ ≤ toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 (Spec (.of k)) i := fun i => by
    rw [preimage_chartP1]
    exact (Scheme.basicOpen_of_isUnit _ (hsU i)).ge
  have hpre' : ∀ i, ⊤ ≤ (C.fromSpecStalk (genericPoint C) ≫ φ) ⁻¹ᵁ chartP1 (Spec (.of k)) i :=
    fun i => by rw [hjφ]; exact hpre i
  have hratio : ∀ (i m : Fin 2) (Q : C) (hy : φ Q ∈ chartP1 (Spec (.of k)) i),
      algebraMap (C.presheaf.stalk Q) C.functionField ((φ.stalkMap Q).hom
        ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy (ratioSection _ i m))) =
        x' m * (x' i)⁻¹ := by
    intro i m Q hy
    refine (algebraMap_stalkMap_germ φ Q _ hy (hpre' i) _).trans ?_
    refine (congrArg (fun F => (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).hom
      (F.hom (ratioSection _ i m))) (appLE_eq_of_eq hjφ _ _ (hpre' i))).trans ?_
    exact ΓSpecIso_appLE_ratioSection x' hx' g i m hs (hpre i)
  have hmem : ∀ j Q, 0 ≤ C.ord (x j) Q + D Q := ord_add_nonneg_of_span_eq f hDcl hli hspan
  have hco := Faltings.FunctionField.coheight_genericPoint_ne_one C
  ext Q
  change φ Q ∈ chartP1 (Spec (.of k)) 0 ↔ C.ord (x 0) Q + D Q ≤ 0
  by_cases hQη : Q = genericPoint C
  · rw [hQη]
    have h1 : φ (genericPoint C) ∈ chartP1 (Spec (.of k)) 0 := by
      let pt : Spec (C.presheaf.stalk (genericPoint C)) :=
        IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))
      have := hpre' 0 (show pt ∈ ⊤ from trivial)
      change (C.fromSpecStalk (genericPoint C) ≫ φ) pt ∈ chartP1 (Spec (.of k)) 0 at this
      rwa [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at this
    have h2 : D (genericPoint C) = 0 := by
      refine Finsupp.notMem_support_iff.1 fun hη => ?_
      have hcl := hDcl _ hη
      have hmem (a : C) : a = genericPoint C :=
        ((genericPoint_spec C).specializes (Set.mem_univ a)).mem_closed hcl rfl
      have : Subsingleton C := ⟨fun a b => by rw [hmem a, hmem b]⟩
      have h0 := topologicalKrullDim_zero_of_discreteTopology C
      rw [IsCurve.topologicalKrullDim_eq_one (f := f)] at h0
      exact absurd h0 (by decide)
    simp only [h1, h2, add_zero, Scheme.ord_eq_zero_of_coheight_neq_one hco, le_refl]
  have hQc : IsClosed ({Q} : Set C) :=
    Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f hQη
  have hcoQ : Order.coheight Q = 1 := IsCurve.coheight_eq_one f hQη
  have hGQ := hG1 c.succ (Fin.succ_ne_zero c) Q hQc
  have h0 := hmem 0 Q
  have hc := hmem c.succ Q
  constructor
  · intro hy
    have hle := ord_le_of_algebraMap_eq_mul_inv Q (hx' 1) (hx' 0) _ (hratio 0 1 Q hy)
    change C.ord (x 0) Q ≤ C.ord (x c.succ) Q at hle
    omega
  · intro hle
    by_contra hy
    have hy1 := (mem_chartP1_zero_or_one _ (φ Q)).resolve_left hy
    set r := (φ.stalkMap Q).hom
      ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy1 (ratioSection _ 1 0))
      with hr
    have hrat := hratio 1 0 Q hy1
    rw [← hr] at hrat
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, map_zero] at hrat
      exact mul_ne_zero (hx' 0) (inv_ne_zero (hx' 1)) hrat.symm
    have hrn : ¬IsUnit r := fun hu => not_isUnit_germ_ratioSection _ (φ Q) hy1 hy
      ((isUnit_map_iff (φ.stalkMap Q).hom _).mp hu)
    have hpos := ord_pos_of_not_isUnit hcoQ hr0 hrn
    rw [hrat, Scheme.ord_mul (hx' 0) (inv_ne_zero (hx' 1)), ord_inv Q (hx' 1)] at hpos
    change 0 < C.ord (x 0) Q + -C.ord (x c.succ) Q at hpos
    omega

end Projection

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `P₁` a divisor of degree one on closed points, `N ≥ 2g + 1`, and `x₀, …, xₙ` a
`k`-basis of `L(N P₁)` satisfying (G1). For `a, b ∈ {1, …, n}`, the product projection
`π_{ab} : C ×_k C ⤏ ℙ¹_k ×_k ℙ¹_k` is induced by a morphism `φ`, and the preimage under `φ` of
`𝔸¹ × 𝔸¹`, with `𝔸¹ = {T₀ ≠ 0}`, is `U × U`, where `U = {Q | ord_Q x₀ + (N P₁)(Q) ≤ 0}` is the
locus where the section `x₀` of `𝒪(N P₁)` does not vanish. -/
@[faltings "lem_bvs_affine_preimage"]
public theorem exists_toRationalMap_eq_productProjectionToProjectiveLine_and_preimage
    (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (a b : Fin n) :
    let P1 := projectiveSpaceOver 1 (Spec (.of k))
    let A1 : P1.Opens := projectiveSpaceOver.toIntegralAtUniverse 1 (Spec (.of k)) ⁻¹ᵁ
      Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} 1) (MvPolynomial.X 0)
    let U : Set C := {Q | C.ord (x 0) Q + ((N : ℤ) • P₁) Q ≤ 0}
    ∃ φ : pullback f f ⟶ pullback (P1 ↘ Spec (.of k)) (P1 ↘ Spec (.of k)),
      φ.toRationalMap =
        productProjectionToProjectiveLine k f hg P₁ hP₁cl hP₁ N hN x hli hspan a b ∧
      SetLike.coe (φ ⁻¹ᵁ (pullback.fst (P1 ↘ Spec (.of k)) (P1 ↘ Spec (.of k)) ⁻¹ᵁ A1 ⊓
          pullback.snd (P1 ↘ Spec (.of k)) (P1 ↘ Spec (.of k)) ⁻¹ᵁ A1)) =
        pullback.fst f f ⁻¹' U ∩ pullback.snd f f ⁻¹' U := by
  intro P1 A1 U
  have hDcl := isClosed_of_mem_support_smul hP₁cl (N : ℤ)
  have hD := finsum_smul_mul_residueDegree f hP₁ (N : ℤ)
  obtain ⟨φa, -, hra⟩ := exists_isFinite_toRationalMap_eq_projectionToProjectiveLine k f hg _
    hDcl N hN hD x hli hspan hG1 a
  obtain ⟨φb, -, hrb⟩ := exists_isFinite_toRationalMap_eq_projectionToProjectiveLine k f hg _
    hDcl N hN hD x hli hspan hG1 b
  have hoa := comp_structureMap_of_toRationalMap_eq (hD := hD) (hspan := hspan) hra
  have hob := comp_structureMap_of_toRationalMap_eq (hD := hD) (hspan := hspan) hrb
  refine ⟨pullback.map f f _ _ φa φb (𝟙 _) (by simpa using hoa.symm)
    (by simpa using hob.symm), ?_, ?_⟩
  · apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [productProjectionToProjectiveLine, Scheme.RationalMap.fromFunctionField_ofFunctionField,
      Scheme.RationalMap.fromFunctionField_toRationalMap]
    simp only [Scheme.PartialMap.fromFunctionField,
      Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]
    apply pullback.hom_ext
    · refine ((Category.assoc _ _ _).trans ?_).trans (pullback.lift_fst _ _ _).symm
      refine (congrArg _ (pullback.lift_fst _ _ _)).trans ?_
      exact fromSpecStalk_comp_comp_eq_toProjectiveSpaceOver f _ φa _ _ _
        (fromSpecStalk_comp_of_toRationalMap_eq (hD := hD) (hspan := hspan) hra) _
    · refine ((Category.assoc _ _ _).trans ?_).trans (pullback.lift_snd _ _ _).symm
      refine (congrArg _ (pullback.lift_snd _ _ _)).trans ?_
      rw [pullback.condition]
      exact fromSpecStalk_comp_comp_eq_toProjectiveSpaceOver f _ φb _ _ _
        (fromSpecStalk_comp_of_toRationalMap_eq (hD := hD) (hspan := hspan) hrb) _
  · ext z
    change (_ ∈ A1 ∧ _ ∈ A1) ↔ (pullback.fst f f z ∈ U ∧ pullback.snd f f z ∈ U)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_snd,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact and_congr
      (Set.ext_iff.mp (coe_preimage_chartP1_zero (hD := hD) (hspan := hspan) hG1 hra) _)
      (Set.ext_iff.mp (coe_preimage_chartP1_zero (hD := hD) (hspan := hspan) hG1 hrb) _)

end Faltings.BombieriVojta
