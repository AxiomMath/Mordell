module

public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.Height.Weil.SubVector
public import Mordell.Height.Machine.IsomorphicPullbacks
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.AlgebraicGeometry.ProjectiveSpace.ChartRatio

/-!
# Heights are bounded below off the zeros of a section

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), `L` a line bundle on `X`, `s ∈ H⁰(X, L)` a global section, and `φ : X ⟶ ℙⁿ_k`,
`ψ : X ⟶ ℙᵐ_k` projective embeddings with `ψ^* 𝒪(1) ≅ L ⊗ φ^* 𝒪(1)`. Then there is a constant
`C` with `h_ψ(p) ≥ h_φ(p) - C` for every `k`-point `p` of `X` at which `s` does not vanish.

## Main results

* `Faltings.ProjectiveEmbedding.exists_height_sub_le_height_of_mem_nonvanishingLocus`: the
  lower bound `h_φ(p) - C ≤ h_ψ(p)` off the zeros of `s`.

## Implementation notes

A line bundle is an `L : X.Modules` with `Stacks.Ample.IsInvertibleModule X L`, a global section
is an element of `Γ(L, ⊤)`, and `s(p) ≠ 0` for a `k`-point `p : Spec k ⟶ X` means that the image
of `p` lies in `Stacks.Ample.nonvanishingLocus L s`, the points where the germ of `s` is not in
`𝔪ₓ Lₓ`. The tensor product of `𝒪_X`-modules is `Stacks.RelativeVeryAmple.tensorModules`, and
`𝒪(1)` on `ℙⁿ_k` is `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec k)`.
Heights are `Faltings.ProjectiveEmbedding.height`.

The proof follows the source. The sections `s ⊗ φ^* T₀, …, s ⊗ φ^* Tₙ` and the images of
`ψ^* T₀, …, ψ^* Tₘ` in `L ⊗ φ^* 𝒪(1)` have no common zero, so they define a morphism
`χ : X ⟶ ℙ^{n+m+1}_k` with `χ^* 𝒪(1) ≅ ψ^* 𝒪(1)`, and `h ∘ χ - h_ψ` is bounded. At a
`k`-point `p` with `s(p) ≠ 0`, some `s ⊗ φ^* T_j` does not vanish at `p`; in the chart `D₊(T_j)`
the first block of affine coordinates of `χ(p)` is the vector of affine coordinates of `φ(p)`,
so `h_φ(p) ≤ h(χ(p))` by the height of a sub-vector. The homogeneous coordinates of a `k`-point
of `ℙʳ_k` are compared through its affine chart values `(T_j / T_i)(p)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

open Faltings.BombieriVojta.HeightLowerBound (coordPoint_kPoint kPoint)

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section Sections

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {X : Scheme.{u}} {r : ℕ}

/-- **Two morphisms to projective space with the same chart functions.** If `β : t^* 𝒪(1) ≅ M`
and, over an open `W` mapping into `D₊(Tᵢ)` under `t` and into `D₊(T_{i'})` under `t'`, the
sections `β (t^* T_j)` and `β (t^* T_i)` satisfy the transition identity of `t'` for `T_{j'}` and
`T_{i'}`, then the pull-backs of `T_j / T_i` along `t` and of `T_{j'} / T_{i'}` along `t'` agree
on `W`. -/
private theorem appLE_coordFracAt_eq_of_resT {r' : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M]
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ M)
    (i j : Fin (r + 1)) (i' j' : Fin (r' + 1)) {W : X.Opens}
    (hW : W ≤ (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i))
    (hW' : W ≤ (t' ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X i'))
    (h : resT W (β.hom.app ⊤ (coordSection t j)) =
      (t' ≫ (polynomialComparison k r').iso.hom).appLE _ W hW'
          ((Proj.awayToSection (polyGrading k r') (MvPolynomial.X i')).hom
            (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r' i' j')) •
        resT W (β.hom.app ⊤ (coordSection t i))) :
    (t ≫ (polynomialComparison k r).iso.hom).appLE _ W hW
        ((Proj.awayToSection (polyGrading k r) (MvPolynomial.X i)).hom
          (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r i j)) =
      (t' ≫ (polynomialComparison k r').iso.hom).appLE _ W hW'
        ((Proj.awayToSection (polyGrading k r') (MvPolynomial.X i')).hom
          (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r' i' j')) := by
  have hnv : W ≤ nvOpen M (β.hom.app ⊤ (coordSection t i)) := by
    intro x hx
    change x ∈ Stacks.Ample.nonvanishingLocus M (β.hom.app ⊤ (coordSection t i))
    rw [show β.hom.app ⊤ (coordSection t i) = β.hom.val.app (Opposite.op ⊤) (coordSection t i)
      from rfl, Cube.nonvanishingLocus_hom_app_top_of_iso, mem_nonvanishingLocus_coordSection_iff]
    exact hW hx
  exact eq_of_smul_eq_smul _ hnv ((resT_hom_app_coordSection t β.hom i j hW).symm.trans h)

end Sections

section TensorSections

open Stacks.ProjectiveFromSections

variable {X : Scheme.{u}}

/-- The tensor product `a ⊗ b ∈ Γ(A ⊗ B, ⊤)` of two global sections. -/
private noncomputable def tmulSection (A B : X.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    Γ(Stacks.RelativeVeryAmple.tensorModules X A B, ⊤) :=
  Stacks.NonvanishingSpelling.sectionsEquiv X (Stacks.RelativeVeryAmple.tensorModules X A B)
    (tensorSections A B ((Stacks.NonvanishingSpelling.sectionsEquiv X A).symm a)
      ((Stacks.NonvanishingSpelling.sectionsEquiv X B).symm b))

/-- `X_{a ⊗ b} = X_a ∩ X_b`. -/
private theorem nonvanishingLocus_tmulSection (A B : X.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    Stacks.Ample.nonvanishingLocus _ (tmulSection A B a b) =
      Stacks.Ample.nonvanishingLocus A a ∩ Stacks.Ample.nonvanishingLocus B b := by
  set σ := (Stacks.NonvanishingSpelling.sectionsEquiv X A).symm a
  set τ := (Stacks.NonvanishingSpelling.sectionsEquiv X B).symm b
  refine Set.ext fun x => ?_
  refine Iff.trans (Set.ext_iff.mp
    (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq X
      (Stacks.RelativeVeryAmple.tensorModules X A B) (tensorSections A B σ τ)) x).symm ?_
  refine Iff.trans (tensorSections_nonvanishing_iff σ τ x) (and_congr ?_ ?_)
  · exact Set.ext_iff.mp
      (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X A a) x
  · exact Set.ext_iff.mp
      (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X B b) x

/-- Over an open `W`, `a ⊗ b` restricts to the image of `a|_W ⊗ b|_W`. -/
private theorem resT_tmulSection (A B : X.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) (W : X.Opens) :
    resT W (tmulSection A B a b) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B
        (Opposite.op W) (resT W a ⊗ₜ resT W b) :=
  PresheafOfModules.sections_property (tensorSections A B
    ((Stacks.NonvanishingSpelling.sectionsEquiv X A).symm a)
    ((Stacks.NonvanishingSpelling.sectionsEquiv X B).symm b)) (homOfLE (le_top : W ≤ ⊤)).op

/-- A relation `b = c • b'` over `W` gives `a ⊗ b = c • (a ⊗ b')` over `W`. -/
private theorem resT_tmulSection_eq_smul (A B : X.Modules) (a : Γ(A, ⊤)) (b b' : Γ(B, ⊤))
    (W : X.Opens) (c : Γ(X, W)) (h : resT W b = c • resT W b') :
    resT W (tmulSection A B a b) = c • resT W (tmulSection A B a b') := by
  rw [resT_tmulSection, resT_tmulSection, h]
  let c' : X.toRingedSpace.presheaf.obj (Opposite.op W) := c
  exact (congrArg _ ((TensorProduct.mk _ _ _ (resT W a)).map_smul c' (resT W b'))).trans
    (map_smul _ c' _)

end TensorSections

section Geometry

open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Chart values of two morphisms related through a line bundle.** -/
private theorem chartVal_comp_eq_of_resT {r r' : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M]
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k))) (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (β : (Scheme.Modules.pullback t).obj (projectiveSpaceTwistingSheaf r (Spec (.of k))) ≅ M)
    (p : Spec (.of k) ⟶ X) (i j : Fin (r + 1)) (i' j' : Fin (r' + 1))
    (hi : ⊤ ≤ ((p ≫ t) ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i))
    (hi' : ⊤ ≤ ((p ≫ t') ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X i'))
    (h : ∀ (W : X.Opens) (hW' : W ≤ (t' ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
        Proj.basicOpen (polyGrading k r') (MvPolynomial.X i')),
      resT W (β.hom.app ⊤ (coordSection t j)) =
        (t' ≫ (polynomialComparison k r').iso.hom).appLE _ W hW'
            ((Proj.awayToSection (polyGrading k r') (MvPolynomial.X i')).hom
              (Stacks.ProjectiveSpaceChartRatio.coordFracAt k r' i' j')) •
          resT W (β.hom.app ⊤ (coordSection t i))) :
    chartVal _ i hi j = chartVal _ i' hi' j' := by
  set W := (t ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i) ⊓
    (t' ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X i')
  have hp : ⊤ ≤ p ⁻¹ᵁ W := fun a ha => ⟨by simpa using hi ha, by simpa using hi' ha⟩
  rw [chartVal_eq_of_comp p _ _ (Category.assoc _ _ _).symm i hi inf_le_left hp j,
    chartVal_eq_of_comp p _ _ (Category.assoc _ _ _).symm i' hi' inf_le_right hp j',
    appLE_coordFracAt_eq_of_resT t t' β i j i' j' inf_le_left inf_le_right (h W inf_le_right)]

/-- **Height of a sub-block of chart coordinates.** If the chart values of `p ≫ t` in `D₊(Tᵢ)`
are a sub-family `j ↦ v (ι j)` of the chart values `v` of `p ≫ t'` in `D₊(T_{i'})`, then
`h(t(p)) ≤ h(t'(p))`. -/
private theorem weilHeight_coordPoint_kPoint_le [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    {f : X ⟶ Spec (.of k)} {r r' : ℕ}
    (t : X ⟶ projectiveSpaceOver r (Spec (.of k)))
    (ht : t ≫ projectiveSpaceOver r (Spec (.of k)) ↘ Spec (.of k) = f)
    (t' : X ⟶ projectiveSpaceOver r' (Spec (.of k)))
    (ht' : t' ≫ projectiveSpaceOver r' (Spec (.of k)) ↘ Spec (.of k) = f)
    (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}) (ι : Fin (r + 1) → Fin (r' + 1))
    (i : Fin (r + 1)) (hi : ⊤ ≤ ((p.1 ≫ t) ≫ (polynomialComparison k r).iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r) (MvPolynomial.X i))
    (i' : Fin (r' + 1)) (hi' : ⊤ ≤ ((p.1 ≫ t') ≫ (polynomialComparison k r').iso.hom) ⁻¹ᵁ
      Proj.basicOpen (polyGrading k r') (MvPolynomial.X i'))
    (h : chartVal _ i' hi' ∘ ι = chartVal _ i hi) :
    weilHeight (coordPoint (kPoint t ht p)) ≤
      weilHeight (coordPoint (kPoint t' ht' p)) := by
  have hv : chartVal _ i' hi' ∘ ι ≠ 0 := h ▸ chartVal_ne_zero _ i hi
  rw [coordPoint_kPoint t ht p i hi, coordPoint_kPoint t' ht' p i' hi',
    ← mk_congr h hv (chartVal_ne_zero _ i hi)]
  exact weilHeight_mk_comp_le _ ι hv

end Geometry

/-- **Positivity off the zeros of a section.** Let `X` be a smooth projective variety over a
field `k` algebraic over `ℚ`, `L` a line bundle on `X`, `s` a global section of `L`, and `φ`, `ψ`
projective embeddings of `X` with `ψ^* 𝒪(1) ≅ L ⊗ φ^* 𝒪(1)`. Then there is a constant `C` with
`h_φ(p) - C ≤ h_ψ(p)` for every `k`-point `p` of `X` at which `s` does not vanish. -/
@[faltings "lem_ht_positivity_off_section"]
public theorem ProjectiveEmbedding.exists_height_sub_le_height_of_mem_nonvanishingLocus
    {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) {n m : ℕ}
    (φ : ProjectiveEmbedding f n) (ψ : ProjectiveEmbedding f m)
    (e : (Scheme.Modules.pullback ψ.hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf m (Spec (.of k))) ≅
      Stacks.RelativeVeryAmple.tensorModules X L ((Scheme.Modules.pullback φ.hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))))) :
    ∃ C : ℝ, ∀ p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _},
      Set.range p.1.base ⊆ Stacks.Ample.nonvanishingLocus L s →
        φ.height p - C ≤ ψ.height p := by
  classical
  set L' := (Scheme.Modules.pullback φ.hom).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k)))
  set M := Stacks.RelativeVeryAmple.tensorModules X L L'
  have : Stacks.Ample.IsInvertibleModule X M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X L L'
  let u : Fin (n + 1 + (m + 1)) → Γ(M, ⊤) :=
    Fin.append (fun j => tmulSection L L' s (coordSection φ.hom j))
      fun l => e.hom.app ⊤ (coordSection ψ.hom l)
  have huφ : ∀ j, u (Fin.castAdd (m + 1) j) = tmulSection L L' s (coordSection φ.hom j) :=
    Fin.append_left _ _
  have hu : ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus M (u j) := fun x => by
    obtain ⟨l, hl⟩ := exists_mem_basicOpen ψ.hom x
    refine ⟨Fin.natAdd (n + 1) l, ?_⟩
    rw [show u (Fin.natAdd (n + 1) l) = _ from Fin.append_right _ _ l,
      show e.hom.app ⊤ (coordSection ψ.hom l) =
        e.hom.val.app (Opposite.op ⊤) (coordSection ψ.hom l) from rfl,
      Cube.nonvanishingLocus_hom_app_top_of_iso, mem_nonvanishingLocus_coordSection_iff]
    exact hl
  obtain ⟨χ, hχ, α, hα⟩ :=
    exists_hom_and_iso_pullback_projectiveSpaceTwistingSheaf f M (r := n + 1 + m) u hu
  obtain ⟨C, hC⟩ := exists_abs_weilHeight_sub_le_of_pullback_iso χ hχ ψ.hom ψ.hom_over
    (α ≪≫ e.symm)
  refine ⟨C, fun p hp => ?_⟩
  obtain ⟨j, hj⟩ := exists_mem_basicOpen φ.hom (p.1.base default)
  have hjχ : (χ ≫ (polynomialComparison k (n + 1 + m)).iso.hom).base (p.1.base default) ∈
      Proj.basicOpen (polyGrading k (n + 1 + m)) (MvPolynomial.X (Fin.castAdd (m + 1) j)) := by
    have h1 : p.1.base default ∈ Stacks.Ample.nonvanishingLocus M (u (Fin.castAdd (m + 1) j)) := by
      rw [huφ, nonvanishingLocus_tmulSection]
      exact ⟨hp ⟨default, rfl⟩, (mem_nonvanishingLocus_coordSection_iff φ.hom j _).2 hj⟩
    rw [← hα] at h1
    rwa [← mem_nonvanishingLocus_coordSection_iff, ← Cube.nonvanishingLocus_hom_app_top_of_iso α]
  have hle := weilHeight_coordPoint_kPoint_le φ.hom φ.hom_over χ hχ p (Fin.castAdd (m + 1)) j
    (top_le_preimage_of_mem _ hj) _ (top_le_preimage_of_mem _ hjχ) <| funext fun j' =>
      chartVal_comp_eq_of_resT χ φ.hom α p.1 _ _ j j' _ _ fun W hW' => by
        rw [hα, hα, huφ, huφ]
        exact resT_tmulSection_eq_smul _ _ _ _ _ W _ (resT_coordSection φ.hom j j' hW')
  have hb := (abs_le.mp (hC p.1 p.2 (kPoint χ hχ p) (kPoint ψ.hom ψ.hom_over p) rfl rfl)).2
  change weilHeight (coordPoint (kPoint φ.hom φ.hom_over p)) - C ≤
    weilHeight (coordPoint (kPoint ψ.hom ψ.hom_over p))
  linarith

end Faltings
