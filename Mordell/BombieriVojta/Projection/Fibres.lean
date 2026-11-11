module
public import Mordell.BombieriVojta.Projection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import Mordell.BombieriVojta.Projection.ProductAffine

/-!
# The fibres of the projections `π_a`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `D` a divisor of degree `N ≥ 2g + 1` supported on closed points (the source's `NP`, with `P`
of degree one), and `x₀, …, xₙ` a `k`-basis of the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))`
inside the function field `k(C)`. For `a ∈ {1, …, n}`
let `π_a = (x₀ : x_a) : C → ℙ¹_k`, a morphism when the basis satisfies (G1). For a `k`-point
`c = (c₀ : c₁)` of `ℙ¹_k`, the divisor `π_a^*(c)` is the divisor of zeros of the section
`c₁x₀ − c₀x_a` of `𝒪(D)`: the point `c` is the zero of the linear form `c₁X₀ − c₀X₁`, whose
pull-back is `c₁x₀ − c₀x_a`, and by (G1) the charts `x₀ ≠ 0` and `x_a ≠ 0` cover `C`.

## Main results

* `Faltings.BombieriVojta.pullback_projectionToProjectiveLine_point_eq_zeros`: under (G1), for
  the morphism `φ : C ⟶ ℙ¹_k` inducing `π_a` and every closed point `Q` of `C`, the multiplicity
  of `φ^*(c)` at `Q` is `ord_Q(c₁x₀ − c₀x_a) + D(Q)`.

## Implementation notes

The divisor `φ^*(c)` is described pointwise. At a closed point `Q` with `φ Q = c` its
multiplicity is `ord_Q(φ^♯ϖ)` for any generator `ϖ` of the maximal ideal of the stalk
`𝒪_{ℙ¹, c}` (a local equation of `c`), read in `k(C)` through the stalk at `Q`; at a closed
point with `φ Q ≠ c` it is `0`. The `k`-point `c` is the image of the morphism
`Spec k ⟶ ℙ¹_k` attached to the global sections `c₀, c₁` of `Spec k`
(`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver`), which span the unit ideal as
`c ≠ 0`. As in `Faltings.BombieriSiegel.SatisfiesG1`, sections of `𝒪(D)` are rational
functions, `D` is a `C →₀ ℤ`, and the divisor of zeros of the section `s` is
`Q ↦ ord_Q s + D(Q)`. The morphism `φ` is any morphism with `φ.toRationalMap = π_a`; one
exists by `Faltings.BombieriVojta.exists_isFinite_toRationalMap_eq_projectionToProjectiveLine`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 629
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriVojta

open Faltings.BombieriSiegel Stacks.SectionsToProjectiveSpace

section Charts

attribute [local instance] MvPolynomial.gradedAlgebra

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
    rwa [← hG]
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
  have hW : W = ⊤ := by rw [hWdef, sectionsHom_X]; exact Scheme.basicOpen_of_isUnit _ hi
  have hinj : Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    clear_value W; subst hW; simpa using Function.injective_id
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

/-- The structure morphism `ℙ¹_S ⟶ S` pulls back sections of `S` to the chart `D₊(Tᵢ)`. -/
private noncomputable abbrev baseSection (S : Scheme.{u}) (i : Fin 2) :
    Γ(S, ⊤) →+* Γ(projectiveSpaceOver 1 S, chartP1 S i) :=
  ((pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1))).appLE ⊤
    (chartP1 S i) le_top).hom

/-- The pull-back of a section of the base by the morphism of the sections `s` over `g` is its
pull-back by `g`. -/
private lemma appLE_baseSection {X S : Scheme.{u}} (s : Fin 2 → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (g : X ⟶ S) (i : Fin 2)
    (h : ⊤ ≤ toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 S i) (a : Γ(S, ⊤)) :
    (toProjectiveSpaceOver s hs g).appLE (chartP1 S i) ⊤ h (baseSection S i a) =
      g.appLE ⊤ ⊤ le_top a :=
  (congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE (toProjectiveSpaceOver s hs g)
    (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1)))
    ⊤ (chartP1 S i) ⊤ le_top h)).trans
    (congrArg (fun φ => φ.hom a) (appLE_eq_of_eq (toProjectiveSpaceOver_fst s hs g) ⊤ ⊤ _))

/-- `Tᵢ / Tᵢ = 1` on the chart `D₊(Tᵢ)`. -/
private lemma ratioSection_self (S : Scheme.{u}) (i : Fin 2) : ratioSection S i i = 1 := by
  have : HomogeneousLocalization.Away.mk (coordGrading.{u} 1) (X_mem_coordGrading_one i) 1
      (MvPolynomial.X i) (X_mem_coordGrading_one_smul i) = 1 := by
    ext
    simp [HomogeneousLocalization.Away.val_mk]
  rw [ratioSection, this, map_one]
  exact map_one _

/-- In a pushout square of commutative rings, the corner is generated by the images of the two
sides. -/
private lemma mem_closure_of_isPushout {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (p : P) :
    p ∈ Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) := by
  set T := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  let inl' : B →+* T := inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩)
  let inr' : C →+* T := inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩)
  have hw : f ≫ CommRingCat.ofHom inl' = g ≫ CommRingCat.ofHom inr' := by
    ext a
    exact congrArg (fun φ => φ.hom a) h.w
  let d := h.desc (CommRingCat.ofHom inl') (CommRingCat.ofHom inr') hw
  have hd : d ≫ CommRingCat.ofHom T.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc]; ext b; rfl
    · rw [← Category.assoc, h.inr_desc]; ext c; rfl
  have := congrArg (fun φ => φ.hom p) hd
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  rw [← this]
  exact (d.hom p).2

/-- The image of a polynomial with coefficients in `ℤ` under a ring homomorphism lies in the
subring generated by the images of the variables. -/
private lemma mem_closure_range_of_mvPolynomial {σ T : Type*} [CommRing T]
    (F : MvPolynomial σ (ULift.{u} ℤ) →+* T) (p : MvPolynomial σ (ULift.{u} ℤ)) :
    F p ∈ Subring.closure (Set.range fun j => F (MvPolynomial.X j)) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hr : r = ((r.down : ℤ) : ULift.{u} ℤ) := by ext; simp
    rw [hr, map_intCast, map_intCast]
    exact intCast_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul]; exact mul_mem hp (Subring.subset_closure ⟨j, rfl⟩)

/-- The image of an element of the chart ring `ℤ[T₀, T₁]_{(Tᵢ)}` under a ring homomorphism lies in
the subring generated by the images of the affine coordinates. -/
private lemma mem_closure_range_chartCoord {T : Type*} [CommRing T] (i : Fin 2)
    (ψ : HomogeneousLocalization.Away (coordGrading.{u} 1) (MvPolynomial.X i) →+* T)
    (b : HomogeneousLocalization.Away (coordGrading.{u} 1) (MvPolynomial.X i)) :
    ψ b ∈ Subring.closure (Set.range fun j =>
      ψ (Stacks.AlgebraicGeometry.ProjPolyChart.chartCoord (ULift.{u} ℤ) 1 i j)) := by
  obtain ⟨p, rfl⟩ := Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_surjective (ULift.{u} ℤ) 1 i b
  refine Subring.closure_mono ?_
    (mem_closure_range_of_mvPolynomial (ψ.comp
      (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom (ULift.{u} ℤ) 1 i)) p)
  rintro _ ⟨j, rfl⟩
  exact ⟨j, by
    simp only [RingHom.comp_apply, Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X]⟩

/-- The sections of `ℙ¹_S` over the chart `D₊(Tᵢ)` are generated, over the sections of the
affine base `S`, by the affine coordinates `T_m / T_i`. -/
private lemma mem_closure_chartP1 (S : Scheme.{u}) [IsAffine S] (i : Fin 2)
    (r : Γ(projectiveSpaceOver 1 S, chartP1 S i)) :
    r ∈ Subring.closure (Set.range (baseSection S i) ∪ Set.range (ratioSection S i)) := by
  have H : IsPullback
      (pullback.snd (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1)))
      (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1)))
      (terminal.from (projectiveSpaceAtUniverse.{u} 1)) (terminal.from S) :=
    (IsPullback.of_hasPullback _ _).flip
  have hD : IsAffineOpen (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_coordGrading_one i) one_pos
  have hUY : chartP1 S i = pullback.snd (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} 1)) ⁻¹ᵁ
        Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i) ⊓
      pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1)) ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have hP := (isIso_pushoutSection_iff H (le_top : (⊤ : S.Opens) ≤ _)
    (le_top : Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i) ≤ _) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY (isAffineOpen_top _) (isAffineOpen_top _) hD)
  refine (Subring.closure_le.mpr ?_) (mem_closure_of_isPushout hP r)
  rintro _ (⟨z, rfl⟩ | ⟨a, rfl⟩)
  · obtain ⟨b, rfl⟩ : ∃ b, (Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom b = z :=
      ⟨(Proj.basicOpenIsoAway (coordGrading.{u} 1) (MvPolynomial.X i)
        (X_mem_coordGrading_one i) one_pos).inv z,
        congrArg (fun φ => φ.hom z) (Proj.basicOpenIsoAway (coordGrading.{u} 1)
          (MvPolynomial.X i) (X_mem_coordGrading_one i) one_pos).inv_hom_id⟩
    refine Subring.closure_mono ?_ (mem_closure_range_chartCoord i
      (((pullback.snd (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1))).appLE
        (Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)) (chartP1 S i)
          (by rw [hUY]; exact inf_le_left)).hom.comp
        (Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom) b)
    rintro _ ⟨j, rfl⟩
    exact Or.inr ⟨j.1, rfl⟩
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)

/-- If `ev ∘ κ = id` and `R` is generated by the image of `κ` and a set `G` of elements each
congruent modulo `I` to `κ (ev g)`, then every `r` is congruent modulo `I` to `κ (ev r)`. -/
private lemma sub_mem_of_mem_closure {F R : Type*} [CommRing F] [CommRing R] (κ : F →+* R)
    (ev : R →+* F) (hev : ∀ a, ev (κ a) = a) (G : Set R) (I : Ideal R)
    (hG : ∀ g ∈ G, g - κ (ev g) ∈ I) (r : R) (hr : r ∈ Subring.closure (Set.range κ ∪ G)) :
    r - κ (ev r) ∈ I := by
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | hx
    · rw [hev, sub_self]; exact I.zero_mem
    · exact hG x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_sub_add_comm]; exact I.add_mem hx hy
  | neg x _ hx => rw [map_neg, map_neg, ← neg_add', neg_mem_iff, ← sub_eq_add_neg]; exact hx
  | mul x y _ _ hx hy =>
    have : x * y - κ (ev (x * y)) = x * (y - κ (ev y)) + κ (ev y) * (x - κ (ev x)) := by
      rw [map_mul, map_mul]; ring
    rw [this]
    exact I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hx)

/-- The kernel of a retraction `ev` of `κ : F → R` is principal, generated by `l`, when `R` is
generated over `F` by elements congruent modulo `l` to their image. -/
private lemma ker_eq_span_singleton {F R : Type*} [CommRing F] [CommRing R] (κ : F →+* R)
    (ev : R →+* F) (hev : ∀ a, ev (κ a) = a) (G : Set R)
    (hgen : ∀ r, r ∈ Subring.closure (Set.range κ ∪ G)) (l : R) (hl : ev l = 0)
    (hG : ∀ g ∈ G, g - κ (ev g) ∈ Ideal.span {l}) : RingHom.ker ev = Ideal.span {l} := by
  refine le_antisymm (fun r hr => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr hl)
  have := sub_mem_of_mem_closure κ ev hev G _ hG r (hgen r)
  rwa [RingHom.mem_ker.mp hr, map_zero, sub_zero] at this

/-- The chart `D₊(Tᵢ)` of `ℙ¹_S` over an affine base is affine. -/
private lemma isAffineOpen_chartP1 (S : Scheme.{u}) [IsAffine S] (i : Fin 2) :
    IsAffineOpen (chartP1 S i) := by
  have : IsAffineHom ((chartP1 S i).ι ≫ (projectiveSpaceOver 1 S ↘ S)) :=
    Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.isAffineHom_coordChart_structureMorphism 1 S i
  exact isAffine_of_isAffineHom ((chartP1 S i).ι ≫ (projectiveSpaceOver 1 S ↘ S))

/-- The linear form `a₁T₀ − a₀T₁`, divided by `Tᵢ`, on the chart `D₊(Tᵢ)` of `ℙ¹_S`. -/
private noncomputable def chartLinearForm (S : Scheme.{u}) (a : Fin 2 → Γ(S, ⊤)) (i : Fin 2) :
    Γ(projectiveSpaceOver 1 S, chartP1 S i) :=
  baseSection S i (a 1) * ratioSection S i 0 - baseSection S i (a 0) * ratioSection S i 1

/-- The pull-back of `(a₁T₀ − a₀T₁)/Tᵢ` by the morphism of the sections `s` over `g` is
`(g^*a₁ · s₀ − g^*a₀ · s₁)/sᵢ`. -/
private lemma appLE_chartLinearForm {X S : Scheme.{u}} (s : Fin 2 → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) (g : X ⟶ S) (i : Fin 2) (hi : IsUnit (s i))
    (h : ⊤ ≤ toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 S i) (a : Fin 2 → Γ(S, ⊤)) :
    (toProjectiveSpaceOver s hs g).appLE (chartP1 S i) ⊤ h (chartLinearForm S a i) =
      (g.appLE ⊤ ⊤ le_top (a 1) * s 0 - g.appLE ⊤ ⊤ le_top (a 0) * s 1) * ↑hi.unit⁻¹ := by
  rw [chartLinearForm, map_sub, map_mul, map_mul, appLE_baseSection, appLE_baseSection,
    appLE_ratioSection s hs g i hi, appLE_ratioSection s hs g i hi]
  ring

end Charts

section FieldPoint

variable {F : Type u} [Field F] {S : Scheme.{u}} (x' : Fin 2 → F) (hx' : ∀ m, x' m ≠ 0)
  (g : Spec (.of F) ⟶ S)

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

include hx' in
/-- Over a field `F`, the pull-back of `(a₁T₀ − a₀T₁)/T_i` by the `F`-point `(x₀ : x₁)` over
`g` is `(g^*a₁ · x₀ − g^*a₀ · x₁)/x_i`. -/
private lemma ΓSpecIso_appLE_chartLinearForm (i : Fin 2)
    (hs : Ideal.span (Set.range fun m => (Scheme.ΓSpecIso (.of F)).inv (x' m)) = ⊤)
    (h : ⊤ ≤ toProjectiveSpaceOver _ hs g ⁻¹ᵁ chartP1 S i) (a : Fin 2 → Γ(S, ⊤)) :
    (Scheme.ΓSpecIso (.of F)).hom
        ((toProjectiveSpaceOver _ hs g).appLE (chartP1 S i) ⊤ h (chartLinearForm S a i)) =
      ((Scheme.ΓSpecIso (.of F)).hom (g.appLE ⊤ ⊤ le_top (a 1)) * x' 0 -
        (Scheme.ΓSpecIso (.of F)).hom (g.appLE ⊤ ⊤ le_top (a 0)) * x' 1) * (x' i)⁻¹ := by
  have hi : IsUnit ((Scheme.ΓSpecIso (.of F)).inv (x' i)) :=
    (Ne.isUnit (hx' i)).map (Scheme.ΓSpecIso (.of F)).inv.hom
  rw [appLE_chartLinearForm _ hs g i hi h, map_mul, map_sub, map_mul, map_mul,
    ΓSpecIso_hom_unit_inv x' hi, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

end FieldPoint

section Points

variable (k : Type u) [Field k]

private lemma isField_Γ_Spec : IsField Γ(Spec (.of k), ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv

/-- The sections `c₀, c₁` of `Spec k` attached to `c : Fin 2 → k`. -/
private noncomputable abbrev pointSections (c : Fin 2 → k) : Fin 2 → Γ(Spec (.of k), ⊤) :=
  fun m => (Scheme.ΓSpecIso (.of k)).inv (c m)

private lemma span_pointSections {c : Fin 2 → k} (hc : c ≠ 0) :
    Ideal.span (Set.range (pointSections k c)) = ⊤ :=
  (Function.ne_iff.mp hc).elim fun i hi =>
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      ((Ne.isUnit hi).map (Scheme.ΓSpecIso (.of k)).inv.hom)

private lemma isUnit_pointSections {c : Fin 2 → k} {m : Fin 2} (hm : c m ≠ 0) :
    IsUnit (pointSections k c m) :=
  (Ne.isUnit hm).map (Scheme.ΓSpecIso (.of k)).inv.hom

variable {k} in
/-- The `k`-point `(c₀ : c₁)` of `ℙ¹_k`, as a morphism `Spec k ⟶ ℙ¹_k`. -/
private noncomputable abbrev pointP1 {c : Fin 2 → k} (hc : c ≠ 0) :
    Spec (.of k) ⟶ projectiveSpaceOver 1 (Spec (.of k)) :=
  toProjectiveSpaceOver (pointSections k c) (span_pointSections k hc) (𝟙 _)

variable {k}

/-- If the `k`-point `(c₀ : c₁)` lies in the chart `D₊(Tᵢ)` then `cᵢ ≠ 0`. -/
private lemma ne_zero_of_pointP1_mem {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (pt : Spec (.of k)) (hpt : pointP1 hc pt ∈ chartP1 (Spec (.of k)) i) : c i ≠ 0 := by
  intro h0
  have : pt ∈ pointP1 hc ⁻¹ᵁ chartP1 (Spec (.of k)) i := hpt
  rw [preimage_chartP1] at this
  simp [pointSections, h0, Scheme.basicOpen_zero] at this

/-- Evaluating at the `k`-point `c` is a retraction of the structure map on the chart. -/
private lemma appLE_pointP1_baseSection {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (h : ⊤ ≤ pointP1 hc ⁻¹ᵁ chartP1 (Spec (.of k)) i) (a : Γ(Spec (.of k), ⊤)) :
    (pointP1 hc).appLE (chartP1 (Spec (.of k)) i) ⊤ h (baseSection _ i a) = a :=
  (appLE_baseSection _ _ _ i h a).trans (by simp [Scheme.Hom.appLE])

/-- If the `k`-point `(c₀ : c₁)` has `cᵢ ≠ 0` it lies in the chart `D₊(Tᵢ)`. -/
private lemma le_preimage_chartP1_pointP1 {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (hi : c i ≠ 0) : ⊤ ≤ pointP1 hc ⁻¹ᵁ chartP1 (Spec (.of k)) i := by
  rw [preimage_chartP1]
  exact (Scheme.basicOpen_of_isUnit _ (isUnit_pointSections k hi)).ge

/-- The kernel of the evaluation at the `k`-point `c = (c₀ : c₁)` of the sections of `ℙ¹_k` over
the chart `D₊(Tᵢ)` is generated by `(c₁T₀ − c₀T₁)/Tᵢ`. -/
private lemma ker_appLE_pointP1 {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2} (hi : c i ≠ 0)
    (h : ⊤ ≤ pointP1 hc ⁻¹ᵁ chartP1 (Spec (.of k)) i) :
    RingHom.ker ((pointP1 hc).appLE (chartP1 (Spec (.of k)) i) ⊤ h).hom =
      Ideal.span {chartLinearForm (Spec (.of k)) (pointSections k c) i} := by
  have hsi : IsUnit (pointSections k c i) := isUnit_pointSections k hi
  have hid : ∀ a : Γ(Spec (.of k), ⊤), Scheme.Hom.appLE (𝟙 (Spec (.of k))) ⊤ ⊤ le_top a = a :=
    fun a => by simp [Scheme.Hom.appLE]
  have hev := appLE_pointP1_baseSection hc h
  refine ker_eq_span_singleton (baseSection _ i) _ hev (Set.range (ratioSection _ i))
    (mem_closure_chartP1 _ i) _ ?_ ?_
  · rw [appLE_chartLinearForm _ _ _ i hsi h, hid, hid]; ring
  · rintro _ ⟨m, rfl⟩
    rw [appLE_ratioSection _ _ _ i hsi m h, map_mul]
    have hu : baseSection (Spec (.of k)) i ↑hsi.unit⁻¹ *
        baseSection (Spec (.of k)) i (pointSections k c i) = 1 := by
      rw [← map_mul, hsi.val_inv_mul, map_one]
    have h0 := ratioSection_self (Spec (.of k)) i
    have hu' : pointSections k c i * ↑hsi.unit⁻¹ = 1 := hsi.mul_val_inv
    rw [Ideal.mem_span_singleton']
    fin_cases i <;> fin_cases m
    · refine ⟨0, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue] at hu hu' h0 ⊢
      rw [h0, zero_mul, ← map_mul, hu', map_one, sub_self]
    · refine ⟨-baseSection (Spec (.of k)) 0 ↑hsi.unit⁻¹, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at hu h0 ⊢
      rw [chartLinearForm, h0]
      linear_combination ratioSection (Spec (.of k)) 0 1 * hu
    · refine ⟨baseSection (Spec (.of k)) 1 ↑hsi.unit⁻¹, ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at hu h0 ⊢
      rw [chartLinearForm, h0]
      linear_combination ratioSection (Spec (.of k)) 1 0 * hu
    · refine ⟨0, ?_⟩
      simp only [Fin.mk_one, Fin.isValue] at hu hu' h0 ⊢
      rw [h0, zero_mul, ← map_mul, hu', map_one, sub_self]

/-- The prime ideal of the `k`-point `c` in the chart `D₊(Tᵢ)` is the kernel of evaluation at
`c`. -/
private lemma primeIdealOf_pointP1 {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (h : ⊤ ≤ pointP1 hc ⁻¹ᵁ chartP1 (Spec (.of k)) i) (pt : Spec (.of k)) :
    ((isAffineOpen_chartP1 _ i).primeIdealOf ⟨pointP1 hc pt, h trivial⟩).asIdeal =
      RingHom.ker ((pointP1 hc).appLE (chartP1 (Spec (.of k)) i) ⊤ h).hom := by
  rw [← IsAffineOpen.comap_primeIdealOf_appLE (chartP1 _ i) (isAffineOpen_chartP1 _ i) ⊤
    (isAffineOpen_top _) h (trivial : pt ∈ ⊤), PrimeSpectrum.comap_asIdeal]
  let := (isField_Γ_Spec k).toField
  rw [Ideal.eq_bot_of_prime ((isAffineOpen_top (Spec (.of k))).primeIdealOf ⟨pt, trivial⟩).asIdeal,
    RingHom.ker_eq_comap_bot]

/-- At the `k`-point `c = (c₀ : c₁)` of `ℙ¹_k`, lying in the chart `D₊(Tᵢ)`, the local equation
`(c₁T₀ − c₀T₁)/Tᵢ` generates the maximal ideal of the stalk. -/
private lemma maximalIdeal_stalk_pointP1 {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (y : projectiveSpaceOver 1 (Spec (.of k))) (hy : y ∈ chartP1 (Spec (.of k)) i)
    (hyc : y ∈ Set.range (pointP1 hc)) :
    IsLocalRing.maximalIdeal ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.stalk y) =
      Ideal.span (Singleton.singleton ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ
        (chartP1 _ i) y hy (chartLinearForm _ (pointSections k c) i))) := by
  obtain ⟨pt, rfl⟩ := hyc
  have hi := ne_zero_of_pointP1_mem hc pt hy
  have h := le_preimage_chartP1_pointP1 hc hi
  let := TopCat.Presheaf.algebra_section_stalk (projectiveSpaceOver 1 (Spec (.of k))).presheaf
    (⟨pointP1 hc pt, hy⟩ : chartP1 (Spec (.of k)) i)
  have := (isAffineOpen_chartP1 _ i).isLocalization_stalk ⟨pointP1 hc pt, hy⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    ((isAffineOpen_chartP1 _ i).primeIdealOf ⟨_, hy⟩).asIdeal, primeIdealOf_pointP1 hc h pt,
    ker_appLE_pointP1 hc hi h, Ideal.map_span, Set.image_singleton]
  rfl

/-- At a point `y` of the chart `D₊(Tᵢ)` of `ℙ¹_k` other than the `k`-point `c = (c₀ : c₁)`, the
local equation `(c₁T₀ − c₀T₁)/Tᵢ` of `c` is a unit of the stalk. -/
private lemma isUnit_germ_chartLinearForm {c : Fin 2 → k} (hc : c ≠ 0) {i : Fin 2}
    (y : projectiveSpaceOver 1 (Spec (.of k))) (hy : y ∈ chartP1 (Spec (.of k)) i)
    (hyc : y ∉ Set.range (pointP1 hc)) :
    IsUnit ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ (chartP1 _ i) y hy
      (chartLinearForm _ (pointSections k c) i)) := by
  let := TopCat.Presheaf.algebra_section_stalk (projectiveSpaceOver 1 (Spec (.of k))).presheaf
    (⟨y, hy⟩ : chartP1 (Spec (.of k)) i)
  have := (isAffineOpen_chartP1 _ i).isLocalization_stalk ⟨y, hy⟩
  refine (IsLocalization.AtPrime.isUnit_to_map_iff _
    ((isAffineOpen_chartP1 _ i).primeIdealOf ⟨y, hy⟩).asIdeal _).mpr fun hmem => ?_
  have hne := ((isAffineOpen_chartP1 _ i).primeIdealOf ⟨y, hy⟩).isPrime.ne_top
  by_cases hi : c i = 0
  · have h0 := ratioSection_self (Spec (.of k)) i
    have hsi : pointSections k c i = 0 := by simp [pointSections, hi]
    refine hne (Ideal.eq_top_of_isUnit_mem _ hmem ?_)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue] at hi hsi h0 ⊢
      have h1 : c 1 ≠ 0 := fun h1 => hc (funext fun m => by fin_cases m <;> simp [hi, h1])
      rw [chartLinearForm, h0, hsi, map_zero, zero_mul, sub_zero, mul_one]
      exact (isUnit_pointSections k h1).map _
    · simp only [Fin.mk_one, Fin.isValue] at hi hsi h0 ⊢
      have h1 : c 0 ≠ 0 := fun h1 => hc (funext fun m => by fin_cases m <;> simp [hi, h1])
      rw [chartLinearForm, h0, hsi, map_zero, zero_mul, zero_sub, mul_one, IsUnit.neg_iff]
      exact (isUnit_pointSections k h1).map _
  · have h := le_preimage_chartP1_pointP1 hc hi
    let pt : Spec (.of k) := Nonempty.some inferInstance
    have hmax :
        (RingHom.ker ((pointP1 hc).appLE (chartP1 (Spec (.of k)) i) ⊤ h).hom).IsMaximal := by
      let := (isField_Γ_Spec k).toField
      exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨_, appLE_pointP1_baseSection hc h a⟩
    have hle : RingHom.ker ((pointP1 hc).appLE (chartP1 (Spec (.of k)) i) ⊤ h).hom ≤
        ((isAffineOpen_chartP1 _ i).primeIdealOf ⟨y, hy⟩).asIdeal := by
      rw [ker_appLE_pointP1 hc hi h, Ideal.span_le, Set.singleton_subset_iff]
      exact hmem
    have hp : (isAffineOpen_chartP1 _ i).primeIdealOf ⟨pointP1 hc pt, h trivial⟩ =
        (isAffineOpen_chartP1 _ i).primeIdealOf ⟨y, hy⟩ :=
      PrimeSpectrum.ext ((primeIdealOf_pointP1 hc h pt).trans (hmax.eq_of_le hne hle))
    have := congrArg (isAffineOpen_chartP1 _ i).fromSpec hp
    rw [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at this
    exact hyc ⟨pt, this⟩

end Points

section Curve

variable {X : Scheme.{u}} [IsIntegral X]

variable [IsLocallyNoetherian X]

/-- A rational function which is a unit at `x` has order `0` at `x`. -/
private lemma ord_algebraMap_stalk_of_isUnit (x : X) {r : X.presheaf.stalk x} (hr : IsUnit r) :
    X.ord (algebraMap _ X.functionField r) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hf : algebraMap _ X.functionField r ≠ 0 := (hr.map _).ne_zero
    rw [Scheme.ord_eq_iff hx hf]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    exact Ring.ordFrac_of_isUnit hr
  · simp [hx]

/-- If `ϖ` and `ℓ` generate the same principal ideal of `R`, their images under a ring hom
`ψ : R → 𝒪_{X,x}` have the same order at `x` in `k(X)`. -/
private lemma ord_algebraMap_eq_of_span_eq {R : Type*} [CommRing R] (x : X)
    (ψ : R →+* X.presheaf.stalk x) {ϖ ℓ : R} (h : Ideal.span {ϖ} = Ideal.span {ℓ})
    (hℓ : algebraMap _ X.functionField (ψ ℓ) ≠ 0) :
    X.ord (algebraMap _ X.functionField (ψ ϖ)) x =
      X.ord (algebraMap _ X.functionField (ψ ℓ)) x := by
  set pb := (algebraMap (X.presheaf.stalk x) X.functionField).comp ψ
  change X.ord (pb ϖ) x = X.ord (pb ℓ) x
  change pb ℓ ≠ 0 at hℓ
  have hnn : ∀ r, 0 ≤ X.ord (pb r) x := fun r => ord_algebraMap_stalk_nonneg x (ψ r)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self ϖ)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self ℓ)
  have hv' : pb v * pb ϖ = pb ℓ := by rw [← map_mul, hv]
  have hu' : pb u * pb ℓ = pb ϖ := by rw [← map_mul, hu]
  have hϖ0 : pb ϖ ≠ 0 := fun h0 => hℓ (by rw [← hv', h0, mul_zero])
  have hu0 : pb u ≠ 0 := fun h0 => hϖ0 (by rw [← hu', h0, zero_mul])
  have hv0 : pb v ≠ 0 := fun h0 => hℓ (by rw [← hv', h0, zero_mul])
  have e1 := congrArg (X.ord · x) hu'
  have e2 := congrArg (X.ord · x) hv'
  rw [Scheme.ord_mul hu0 hℓ] at e1
  rw [Scheme.ord_mul hv0 hϖ0] at e2
  have := hnn u
  have := hnn v
  omega

/-- Let `y₀, y₁` be sections of `𝒪(D)` near `x` without a common zero at `x`. If `yᵢ` has the
least order of the two at `x`, then `ord_x yᵢ + D(x) = 0`. -/
private lemma ord_add_eq_zero_of_forall_le (x : X) (y : Fin 2 → X.functionField) (d : ℤ)
    (i : Fin 2) (hle : ∀ m, X.ord (y i) x ≤ X.ord (y m) x) (hmem : ∀ m, 0 ≤ X.ord (y m) x + d)
    (hG : ¬(0 < X.ord (y 0) x + d ∧ 0 < X.ord (y 1) x + d)) : X.ord (y i) x + d = 0 := by
  have := hle 0
  have := hle 1
  have := hmem i
  omega

end Curve

/-- For linearly independent `x₀, …, xₙ`, `a ∈ {1, …, n}` and `c ≠ 0`, the combination
`c₁x₀ − c₀x_a` is nonzero. -/
private lemma smul_sub_smul_ne_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {n : ℕ}
    {x : Fin (n + 1) → V} (hli : LinearIndependent k x) (a : Fin n) {c : Fin 2 → k}
    (hc : c ≠ 0) : c 1 • x 0 - c 0 • x a.succ ≠ 0 := by
  intro hw0
  have hne : (0 : Fin (n + 1)) ≠ a.succ := (Fin.succ_ne_zero a).symm
  have hinj : Function.Injective ![(0 : Fin (n + 1)), a.succ] := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> first | rfl | exact absurd hpq hne | exact absurd hpq.symm hne
  have hpair : LinearIndependent k ![x 0, x a.succ] := by
    have := hli.comp _ hinj
    convert this using 1
    ext m
    fin_cases m <;> rfl
  have h2 := LinearIndependent.pair_iff.mp hpair (c 1) (-c 0) (by
    rw [neg_smul, ← sub_eq_add_neg]; exact hw0)
  apply hc
  funext m
  fin_cases m
  · simpa using h2.2
  · simpa using h2.1

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `D` a divisor of degree `N ≥ 2g + 1` on closed points, and `x₀, …, xₙ` a `k`-basis of
`L(D)` satisfying (G1). Let `a ∈ {1, …, n}`, let `φ : C ⟶ ℙ¹_k` be the morphism inducing
`π_a = (x₀ : x_a)`, and let `c = (c₀ : c₁)` be a `k`-point of `ℙ¹_k`. Then `φ^*(c)` is the divisor
of zeros of the section `c₁x₀ − c₀x_a` of `𝒪(D)`: at a closed point `Q` of `C` over `c`, the order
at `Q` of the pull-back of any local equation `ϖ` of `c` is `ord_Q(c₁x₀ − c₀x_a) + D(Q)`, and at
a closed point not over `c` the section `c₁x₀ − c₀x_a` of `𝒪(D)` does not vanish. -/
@[faltings "lem_bvs_projection_fibres"]
public theorem pullback_projectionToProjectiveLine_point_eq_zeros (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x) (a : Fin n)
    (φ : C ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hφ : φ.toRationalMap = projectionToProjectiveLine k f hg D hDcl N hN hD x hli hspan a)
    (c : Fin 2 → k) (hc : c ≠ 0) (Q : C) (hQ : IsClosed ({Q} : Set C)) :
    letI := functionFieldAlgebra k f
    (φ Q ∈ Set.range (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of k)).inv (c i))
        ((Function.ne_iff.mp hc).elim fun i hi =>
          Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
            ((Ne.isUnit hi).map (Scheme.ΓSpecIso (.of k)).inv.hom))
        (𝟙 (Spec (.of k)))) →
      ∀ ϖ : (projectiveSpaceOver 1 (Spec (.of k))).presheaf.stalk (φ Q),
        IsLocalRing.maximalIdeal _ = Ideal.span {ϖ} →
        C.ord (algebraMap (C.presheaf.stalk Q) C.functionField (φ.stalkMap Q ϖ)) Q =
          C.ord (c 1 • x 0 - c 0 • x a.succ) Q + D Q) ∧
    (φ Q ∉ Set.range (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of k)).inv (c i))
        ((Function.ne_iff.mp hc).elim fun i hi =>
          Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
            ((Ne.isUnit hi).map (Scheme.ΓSpecIso (.of k)).inv.hom))
        (𝟙 (Spec (.of k)))) →
      C.ord (c 1 • x 0 - c 0 • x a.succ) Q + D Q = 0) := by
  let := functionFieldAlgebra k f
  -- the point `(x₀ : x_a)` of `ℙ¹` over `k(C)`
  let x' : Fin 2 → C.functionField := ![x 0, x a.succ]
  have hx' : ∀ m, x' m ≠ 0 := by
    intro m
    fin_cases m
    · exact hli.ne_zero 0
    · exact hli.ne_zero a.succ
  let s : Fin 2 → Γ(Spec (.of C.functionField), ⊤) :=
    fun m => (Scheme.ΓSpecIso (.of C.functionField)).inv (x' m)
  have hsU : ∀ m, IsUnit (s m) := fun m =>
    (Ne.isUnit (hx' m)).map (Scheme.ΓSpecIso (.of C.functionField)).inv.hom
  have hs : Ideal.span (Set.range s) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) (hsU 0)
  have hjφ : C.fromSpecStalk (genericPoint C) ≫ φ =
      toProjectiveSpaceOver s hs (C.fromSpecStalk (genericPoint C) ≫ f) :=
    fromSpecStalk_comp_of_toRationalMap_eq hφ
  set g := C.fromSpecStalk (genericPoint C) ≫ f with hgdef
  set w : C.functionField := c 1 • x 0 - c 0 • x a.succ with hwdef
  -- the chart `D₊(Tᵢ)` containing `φ Q`
  obtain ⟨i, hy⟩ : ∃ i, φ Q ∈ chartP1 (Spec (.of k)) i := by
    have := Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.iSup_coordChart_eq_top 1 (Spec (.of k))
    have hmem : φ Q ∈ (⊤ : (projectiveSpaceOver 1 (Spec (.of k))).Opens) := trivial
    rwa [← this, TopologicalSpace.Opens.mem_iSup] at hmem
  have hpre : ⊤ ≤ toProjectiveSpaceOver s hs g ⁻¹ᵁ chartP1 (Spec (.of k)) i := by
    rw [preimage_chartP1]; exact (Scheme.basicOpen_of_isUnit _ (hsU i)).ge
  have hpre' : ⊤ ≤ (C.fromSpecStalk (genericPoint C) ≫ φ) ⁻¹ᵁ chartP1 (Spec (.of k)) i := by
    rwa [hjφ]
  -- pulling back sections of the chart to `k(C)`
  let γ : Γ(Spec (.of C.functionField), ⊤) →+* C.functionField :=
    (Scheme.ΓSpecIso (.of C.functionField)).hom.hom
  let pb : (projectiveSpaceOver 1 (Spec (.of k))).presheaf.stalk (φ Q) →+* C.functionField :=
    (algebraMap (C.presheaf.stalk Q) C.functionField).comp (φ.stalkMap Q).hom
  have hpb : ∀ r, pb ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy r) =
      γ ((toProjectiveSpaceOver s hs g).appLE (chartP1 (Spec (.of k)) i) ⊤ hpre r) := fun r =>
    (algebraMap_stalkMap_germ φ Q _ hy hpre' r).trans
      (congrArg (fun F => (Scheme.ΓSpecIso (.of C.functionField)).hom (F.hom r))
        (appLE_eq_of_eq hjφ _ _ hpre'))
  have hconst : ∀ t : k, γ (g.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of k)).inv t)) =
      algebraMap k C.functionField t := by
    intro t
    have : Nonempty (f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)) := ⟨⟨genericPoint C, trivial⟩⟩
    exact (germToFunctionField_app f ⊤ le_top _).symm
  have hratio : ∀ m, pb ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy
      (ratioSection _ i m)) = x' m * (x' i)⁻¹ := fun m =>
    (hpb _).trans (ΓSpecIso_appLE_ratioSection x' hx' g i m hs hpre)
  have hlin : pb ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy
      (chartLinearForm _ (pointSections k c) i)) = w * (x' i)⁻¹ := by
    refine (hpb _).trans ((ΓSpecIso_appLE_chartLinearForm x' hx' g i hs hpre _).trans ?_)
    rw [hconst, hconst, hwdef, Algebra.smul_def, Algebra.smul_def]
    rfl
  -- orders
  have hw : w ≠ 0 := smul_sub_smul_ne_zero hli a hc
  have hmem (j) : 0 ≤ C.ord (x j) Q + D Q := ord_add_nonneg_of_span_eq f hDcl hli hspan j Q
  have hord : C.ord (x' i) Q + D Q = 0 :=
    ord_add_eq_zero_of_forall_le Q x' (D Q) i
      (fun m => ord_le_of_algebraMap_eq_mul_inv Q (hx' m) (hx' i) ((φ.stalkMap Q).hom
        ((projectiveSpaceOver 1 (Spec (.of k))).presheaf.germ _ (φ Q) hy (ratioSection _ i m)))
        (hratio m))
      (fun m => by fin_cases m <;> exact hmem _) (hG1 a.succ (Fin.succ_ne_zero a) Q hQ)
  have hordlin : C.ord (w * (x' i)⁻¹) Q = C.ord w Q + D Q := by
    rw [Scheme.ord_mul hw (inv_ne_zero (hx' i)), ord_inv Q (hx' i)]
    omega
  have hlin0 : w * (x' i)⁻¹ ≠ 0 := mul_ne_zero hw (inv_ne_zero (hx' i))
  refine ⟨fun hyc ϖ hϖ => ?_, fun hyc => ?_⟩
  · have hmax := maximalIdeal_stalk_pointP1 hc (φ Q) hy hyc
    rw [hϖ] at hmax
    refine (ord_algebraMap_eq_of_span_eq Q (φ.stalkMap Q).hom hmax ?_).trans ?_
    · exact (hlin.trans rfl).symm ▸ hlin0
    · exact (congrArg (C.ord · Q) hlin).trans hordlin
  · have hunit := isUnit_germ_chartLinearForm hc (φ Q) hy hyc
    have h0 := ord_algebraMap_stalk_of_isUnit Q (RingHom.isUnit_map (φ.stalkMap Q).hom hunit)
    exact hordlin.symm.trans ((congrArg (C.ord · Q) hlin).symm.trans h0)

end Faltings.BombieriVojta
