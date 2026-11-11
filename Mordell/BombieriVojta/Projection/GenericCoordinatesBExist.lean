module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Projection.GenericCoordinatesB
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import Mordell.Curve.Topology
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.AlgebraicGeometry.NormalScheme.Integrality
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.PolynomialModel
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic

/-!
# Generic coordinates for `φ_B` exist

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, with a divisor `P` of degree one, and let `Y = C ×_k C` with projections `pr₁, pr₂` and
diagonal `Δ`. Let `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` (`s ≥ 1`) be very ample,
`y₀, …, yₘ` a basis of `H⁰(Y, 𝒪(B))` giving the embedding `φ_B : Y → ℙᵐ`, with divisors of
zeros `Dᵢ`. Let `N ≥ 2g + 1`, `n = N - g`, and `x₀, …, xₙ` a *generic* basis of
`H⁰(C, 𝒪(N P))` giving the embedding `φ_{NP} : C → ℙⁿ`; then every
`π_{ab} = (x₀ : x_a ; x₀' : x_b')`, `1 ≤ a, b ≤ n`, is a finite morphism `Y → ℙ¹ × ℙ¹`.

After composing `φ_B` with a suitable projective automorphism `g ∈ GL_{m+1}(k)` of `ℙᵐ`, which
replaces the basis `y` by `yᵢ' = ∑ⱼ gᵢⱼ yⱼ` and does not change the linear system `|B|`, the
coordinates `y'` are generic for the projections, in the sense of Bombieri's Section 9: for all
`a, b ≠ 0`, with `π = π_{ab}`, (G1) `π_* D_i'` and `π_* D_0'` (`i ≠ 0`), and `π_* D_1'` and
`π_* D_2'`, have no common component, (G2) no component of `π_* D_i'` (`i ≠ 0`) lies in
`(∞ × ℙ¹) ∪ (ℙ¹ × ∞)`, and (G3) over each point of `𝔸¹ × 𝔸¹` some `y_i'`, `i ≠ 0`, vanishes
at no point of the fibre of `π`.

Following Bombieri, the rows of `g` are chosen one at a time, in the order `y'₀ = y₀`, `y'₂`,
`y'₁`, `y'₃`, `y'₄, …, y'ₘ`, each avoiding the span of the earlier ones and finitely many proper
subspaces. For a point `p` of `Y` some coordinate `yⱼ` does not vanish at `p` (a chart `D₊(Xⱼ)` of
`φ_B` contains `p`), so the coefficient vectors of the sections vanishing along a prime divisor
through `p` form a proper subspace. The finitely many points to avoid are:

* the prime divisors along which some `ξ_a` or `ξ'_b` has a pole, giving (G2);
* the poles of functions `r_{q'} ∈ k(ξ_a, ξ'_b)` with a pole along a component `q'` of `D₀`, giving
  (G1) for `D₀`;
* for `y'₁`, the zeros of polynomials `G_{q'}(ξ_a, ξ'_b)` vanishing along a component `q'` of `D₂`,
  giving (G1) for `D₁, D₂`;
* for `y'₃`, the points over the finitely many maximal ideals `𝔪` of `k[ξ_a, ξ'_b]` containing the
  primes of a component of `D₁` and of a component of `D₂`, giving (G3).

The existence of `r_{q'}` and `G_{q'}` uses that the affine chart `W = π_{ab}⁻¹(𝔸²)` has a ring of
sections finite over `k[ξ_a, ξ'_b]`, so that no prime divisor is contracted; the finiteness of the
maximal ideals in the last item is the fact that two distinct nonzero primes of the two-dimensional
ring `k[ξ_a, ξ'_b]` lie in only finitely many maximal ideals. The index `3` exists because `m ≥ 3`:
the fibres of `pr₁` over two distinct closed points are disjoint curves on `Y`, and by Krull's
height theorem two curves in `ℙ²` meet.

## Main results

* `Faltings.exists_isGenericForProjections_map`: there is `g ∈ GL_{m+1}(k)` such that the
  basis `yᵢ' = ∑ⱼ gᵢⱼ yⱼ` of `H⁰(Y, 𝒪(B))` gives an embedding `φ_B'` of `Y` in `ℙᵐ` and is
  generic for the projections `π_{ab}`.

## Implementation notes

The data are written as in `Faltings.exists_neronPairing_abelJacobi_le`, which takes the
genericity of `y` as its hypothesis (B): the curve is a `Faltings.CurveWithDegreeOneDivisor`,
`Y` is `pullback X.f X.f`, projective space is `AlgebraicGeometry.projectiveSpaceOver`, and `B`
is written through the divisor `P` of degree one. Divisors are written through the order of
vanishing `AlgebraicGeometry.Scheme.ord`: a section `y` of `𝒪(B)` is a rational function with
`div y + B ≥ 0`, and its divisor of zeros is `div y + B`. The genericity of `x` is
`Faltings.BombieriSiegel.IsGenericBasis` for the divisor `N P`. The embedding `φ_{NP}` is a
closed immersion `C → ℙⁿ_k` over `k` pulling `T_ν / T_j` back to `x_ν / x_j` on its charts, and
the embedding `φ_B` given by `y` is a closed immersion `Y → ℙᵐ_k` over `k` which at the generic
point is the point `[y₀ : … : yₘ]`
(`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver`).

The conditions (G1)–(G3) are stated on `Y` over `k`. For a codimension-one point `w` of `Y` the
image `π(w)` is a prime divisor of `ℙ¹ × ℙ¹`, and the order of vanishing at `w` restricts on
`k(ξ_a, ξ'_b)` to a positive multiple of that at `π(w)`, where `ξ_a = pr₁^*(x_a / x₀)` and
`ξ'_b = pr₂^*(x_b / x₀)`. So `π(w) ≠ π(w')` exactly when some `r ∈ k(ξ_a, ξ'_b)` has
`ord_w r ≥ 0 > ord_{w'} r`, and `π(w)` lies at infinity exactly when `ord_w ξ_a < 0` or
`ord_w ξ'_b < 0`. A point of `𝔸¹ × 𝔸¹` up to conjugacy is a maximal ideal `𝔪` of
`k[ξ_a, ξ'_b] = MvPolynomial (Fin 2) k`, and a point `q` of `Y` lies over it when every non-zero
`r ∈ 𝔪` vanishes at `q` (the zero polynomial, whose order is `0` by convention, is excluded).
Since the `Dᵢ` are defined over `k`, these conditions over `k` are the source's conditions over
`k̄`.

The rows of `g` are integral vectors: the avoidance is done in `ℚᵐ⁺¹` and denominators are cleared.
The new embedding is `φ_B` followed by the automorphism `Tᵢ ↦ ∑ⱼ gᵢⱼ Tⱼ` of `Proj k[T₀, …, Tₘ]`,
read on `ℙᵐ_k` through the comparison `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare` of the
two models of projective space; at the generic point it is the point `[y'₀ : … : y'ₘ]`, because the
morphism of a family of sections is the morphism of its evaluation homomorphism on the polynomial
model. Prime divisors are points of codimension one, and a section `y` of `𝒪(B)` vanishes along `q`
when `ord_q y + B(q) > 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 618, and
  Section 9, pp. 632–633
-/

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order

universe u

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

/-- The generic point of an integral scheme lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A point of `Proj R[X₀, …, Xₙ]` lies in some chart `D₊(Xⱼ)`. -/
private theorem exists_X_notMem {R : Type u} [CommRing R] {n : ℕ}
    (y : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    ∃ j, MvPolynomial.X j ∉ y.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  apply y.not_irrelevant_le
  intro f hf
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hf
  change f ∈ y.asHomogeneousIdeal.toIdeal
  have h0 : f.coeff 0 = 0 := by
    have h1 : MvPolynomial.homogeneousComponent 0 f = 0 := by
      rw [← MvPolynomial.decomposition.decompose'_apply]
      exact hf
    rwa [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  have hspan : f ∈ Ideal.span (MvPolynomial.X '' Set.univ) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (MvPolynomial.mem_support_iff.mp hm) h0
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ _, hi⟩
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨j, -, rfl⟩
  exact h j

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Regular points of `ξ_a` lie in the chart `D₊(X₀)`.** Let `φ : C ⟶ Proj R[X₀, …, Xₙ]` be a
morphism from a normal curve whose restriction to `φ⁻¹ D₊(X₀)` has coordinate functions
`x j / x 0`, where the `x j` are sections of `𝒪(E)` with `x 0, x a` without common zero. If
`x a / x 0` is regular at `c`, then `φ c ∈ D₊(X₀)`. -/
private theorem mem_preimage_proj_basicOpen_of_mem_range {k : Type u} [Field k] {C : Scheme.{u}}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] (f₀ : C ⟶ Spec (.of k)) [IsCurve k f₀]
    {n : ℕ} (E : C → ℤ) (x : Fin (n + 1) → C.functionField) (hx : ∀ j, x j ≠ 0)
    (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z) {R : Type u} [CommRing R]
    (φ : C ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (hφ_ne : ((φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) : C.Opens) : Set C).Nonempty)
    (hφ : ∀ [Nonempty (φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0))] (j : Fin (n + 1)),
      C.germToFunctionField _ (φ.app _ (Proj.awayToSection _ (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R 0)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X R j)))) = x j / x 0)
    {a : Fin (n + 1)}
    (hG1 : ∀ z, Order.coheight z = 1 → C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    {c : C} (hc : x a / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField)) :
    c ∈ φ ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  by_contra hc0
  have hcg : c ≠ genericPoint C := fun h => hc0 (h ▸ genericPoint_mem_of_nonempty _ hφ_ne)
  have hc1 : Order.coheight c = 1 := IsCurve.coheight_eq_one f₀ hcg
  have hord : 0 ≤ C.ord (x a / x 0) c :=
    (ord_nonneg_iff hc1 (div_ne_zero (hx a) (hx 0))).mpr hc
  rw [ord_div (hx a) (hx 0)] at hord
  have h0 : C.ord (x 0) c + E c = 0 := by
    rcases hG1 c hc1 with h | h
    · exact h
    · have := hxE 0 c
      omega
  have hreg : ∀ j, x j / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) :=
    fun j => by
      refine (ord_nonneg_iff hc1 (div_ne_zero (hx j) (hx 0))).mp ?_
      rw [ord_div (hx j) (hx 0)]
      have := hxE j c
      omega
  have hy0 : MvPolynomial.X 0 ∈ (φ c).asHomogeneousIdeal := by
    by_contra h
    exact hc0 h
  obtain ⟨j, hj⟩ := exists_X_notMem (φ c)
  have hcj : c ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := hj
  have hX : ∀ i, MvPolynomial.X i ∈ 𝒜 1 := fun i =>
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R i)
  have hX' : ∀ i, MvPolynomial.X i ∈ 𝒜 (1 • 1) := fun i => by simpa using hX i
  have hnu : ¬ IsUnit (C.presheaf.germ _ c hcj (φ.app _ (Proj.awayToSection 𝒜 (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X 0) (hX' 0))))) := by
    rw [(Scheme.Hom.germ_stalkMap_apply φ _ c hcj _).symm]
    intro hu
    have hu' := isUnit_of_map_unit (φ.stalkMap c).hom _ hu
    exact ((isUnit_germ_awayToSection_iff 𝒜 (hX j) 1 _ (hX' 0) (φ c) hj).mp hu') hy0
  have hg0 : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0) :=
    genericPoint_mem_of_nonempty _ hφ_ne
  have hgj : genericPoint C ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) :=
    genericPoint_mem_of_nonempty _ ⟨c, hcj⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X 0)) := ⟨⟨_, hg0⟩⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) := ⟨⟨_, hgj⟩⟩
  have hrel : C.germToFunctionField _ (φ.app _ (Proj.awayToSection 𝒜 (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk 𝒜 (hX j) 1 (MvPolynomial.X 0) (hX' 0)))) *
        (x j / x 0) = 1 := by
    rw [← hφ j]
    change C.presheaf.germ _ (genericPoint C) hgj _ * C.presheaf.germ _ (genericPoint C) hg0 _ = 1
    rw [(Scheme.Hom.germ_stalkMap_apply φ _ _ hgj _).symm,
      (Scheme.Hom.germ_stalkMap_apply φ _ _ hg0 _).symm, ← RingHom.map_mul]
    exact (congrArg (φ.stalkMap (genericPoint C))
      (germ_mul_germ_awayToSection 𝒜 (hX j) (hX 0) (hX' j) (hX' 0) (φ (genericPoint C)) hgj
        hg0)).trans (map_one _)
  obtain ⟨t, ht⟩ := hreg j
  apply hnu
  refine isUnit_iff_exists_inv.mpr ⟨t, ?_⟩
  apply IsFractionRing.injective (C.presheaf.stalk c) C.functionField
  rw [map_mul, ht, Scheme.algebraMap_germ_eq_germToFunctionField, hrel, map_one]

section LinAlg

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A vector avoiding a proper subspace and a finite set of proper subspaces. -/
private theorem exists_notMem_of_finite {𝒮 : Set (Submodule ℚ V)} (h𝒮 : 𝒮.Finite)
    (hprop : ∀ S ∈ 𝒮, S ≠ ⊤) (W : Submodule ℚ V) (hW : W ≠ ⊤) :
    ∃ c, c ∉ W ∧ ∀ S ∈ 𝒮, c ∉ S := by
  have : Finite 𝒮 := h𝒮.to_subtype
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (K := ℚ)
    (fun o : Option 𝒮 => o.elim W (fun S => S.1)) (fun o => by
      cases o with
      | none => exact hW
      | some S => exact hprop S.1 S.2)
  exact ⟨c, hc none, fun S hS => hc (some ⟨S, hS⟩)⟩

/-- The span of fewer than `finrank V` vectors is a proper subspace. -/
private theorem span_range_ne_top [FiniteDimensional ℚ V] {r : ℕ} (v : Fin r → V)
    (hr : r < Module.finrank ℚ V) : Submodule.span ℚ (Set.range v) ≠ ⊤ := by
  intro h
  have h1 := finrank_range_le_card (R := ℚ) (b := v)
  rw [Set.finrank, h, finrank_top] at h1
  simp at h1
  omega

/-- Clearing denominators in a rational vector. -/
private theorem exists_int_smul {n : ℕ} (w : Fin n → ℚ) :
    ∃ (d : ℚ) (z : Fin n → ℤ), d ≠ 0 ∧ ∀ j, (z j : ℚ) = d * w j := by
  refine ⟨∏ l, ((w l).den : ℚ), fun j => (w j).num * ∏ l ∈ Finset.univ.erase j, ((w l).den : ℤ),
    ?_, fun j => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (w l).den_nz
  · push_cast
    rw [← Finset.mul_prod_erase Finset.univ (fun l => ((w l).den : ℚ)) (Finset.mem_univ j)]
    have := Rat.mul_den_eq_num (w j)
    calc ((w j).num : ℚ) * ∏ l ∈ Finset.univ.erase j, ((w l).den : ℚ)
        = (w j * (w j).den) * ∏ l ∈ Finset.univ.erase j, ((w l).den : ℚ) := by rw [this]
      _ = _ := by ring

/-- **The rational vectors whose combination vanishes at a point.** Let `R → K` be an injective
map from a local ring to a field of characteristic zero whose image contains `ℚ`, and `u` a family
in the image with `u j = 1`. The rational `c` with `∑ cᵢ uᵢ` in the image of the maximal ideal form
a proper subspace, and off it `∑ cᵢ uᵢ` is the image of a unit. -/
private theorem exists_submodule_of_isLocalRing (R K : Type*) [CommRing R] [IsLocalRing R]
    [Field K] [CharZero K] [Algebra R K] (hinj : Function.Injective (algebraMap R K)) {n : ℕ}
    (u : Fin n → K) (hu : ∀ i, u i ∈ Set.range (algebraMap R K))
    (hQ : ∀ q : ℚ, (q : K) ∈ Set.range (algebraMap R K)) {j : Fin n} (hj : u j = 1) :
    ∃ S : Submodule ℚ (Fin n → ℚ), S ≠ ⊤ ∧
      ∀ c ∉ S, ∃ t : R, IsUnit t ∧ algebraMap R K t = ∑ i, (c i : K) * u i := by
  classical
  let S : Submodule ℚ (Fin n → ℚ) :=
    { carrier := {c | ∃ t ∈ IsLocalRing.maximalIdeal R, algebraMap R K t = ∑ i, (c i : K) * u i}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro c c' ⟨t, ht, htc⟩ ⟨t', ht', htc'⟩
        refine ⟨t + t', add_mem ht ht', ?_⟩
        rw [map_add, htc, htc', ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Rat.cast_add]
        ring
      smul_mem' := by
        rintro q c ⟨t, ht, htc⟩
        obtain ⟨tq, htq⟩ := hQ q
        refine ⟨tq * t, Ideal.mul_mem_left _ _ ht, ?_⟩
        rw [map_mul, htq, htc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
        ring }
  have hrange : ∀ c : Fin n → ℚ, ∑ i, (c i : K) * u i ∈ (algebraMap R K).range := by
    intro c
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (hu i)
    exact hQ (c i)
  refine ⟨S, fun htop => ?_, fun c hc => ?_⟩
  · have hmem : (Pi.single j 1 : Fin n → ℚ) ∈ S := htop ▸ Submodule.mem_top
    obtain ⟨t, ht, htc⟩ := hmem
    have h1 : algebraMap R K t = 1 := by
      rw [htc, Finset.sum_eq_single j (fun i _ hij => by simp [hij])
        (by simp)]
      simp [hj]
    rw [← map_one (algebraMap R K)] at h1
    rw [hinj h1] at ht
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr ht)
  · obtain ⟨t, ht⟩ := hrange c
    refine ⟨t, ?_, ht⟩
    by_contra hnu
    exact hc ⟨t, (IsLocalRing.mem_maximalIdeal t).mpr hnu, ht⟩

end LinAlg

section CommAlg

/-- In a Noetherian domain of dimension at most two, two distinct nonzero primes lie together in
only finitely many maximal ideals. -/
private theorem finite_setOf_isMaximal_sup_le {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A ≤ 2) {P₁ P₂ : Ideal A} [P₁.IsPrime]
    [P₂.IsPrime] (h₁ : P₁ ≠ ⊥) (h₂ : P₂ ≠ ⊥) (h12 : P₁ ≠ P₂) :
    {𝔪 : Ideal A | 𝔪.IsMaximal ∧ P₁ ⊔ P₂ ≤ 𝔪}.Finite := by
  have hmax : ∀ Q : Ideal A, Q.IsPrime → P₁ ⊔ P₂ ≤ Q → Q.IsMaximal := by
    intro Q hQ hle
    have hlt : ∃ P : Ideal A, P.IsPrime ∧ P ≠ ⊥ ∧ P < Q := by
      by_cases hQ1 : P₁ = Q
      · refine ⟨P₂, inferInstance, h₂, lt_of_le_of_ne (le_sup_right.trans hle) ?_⟩
        rintro rfl
        exact h12 hQ1
      · exact ⟨P₁, inferInstance, h₁, lt_of_le_of_ne (le_sup_left.trans hle) hQ1⟩
    obtain ⟨P, hP, hP0, hPQ⟩ := hlt
    have hb : (⊥ : Ideal A) < P := bot_lt_iff_ne_bot.mpr hP0
    have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hb
    have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hPQ
    rw [Ideal.height_bot] at e1
    by_contra hnm
    obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    have hQM' : Q < M := lt_of_le_of_ne hQM (fun h => hnm (h ▸ hM))
    have e3 := Ideal.height_add_one_le_of_lt_of_isPrime hQM'
    have e4 := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    have : (3 : ℕ∞) ≤ M.height := by
      calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
        _ ≤ P.height + 1 + 1 := by gcongr
        _ ≤ Q.height + 1 := by gcongr
        _ ≤ M.height := e3
    have h3 : ((3 : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
      calc ((3 : ℕ∞) : WithBot ℕ∞) ≤ (M.height : WithBot ℕ∞) := by exact_mod_cast this
        _ ≤ ringKrullDim A := e4
        _ ≤ 2 := hdim
    exact absurd h3 (by decide)
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (P₁ ⊔ P₂)).subset ?_
  rintro 𝔪 ⟨h𝔪, hle⟩
  refine ⟨⟨h𝔪.isPrime, hle⟩, fun Q ⟨hQ, hIQ⟩ hQ𝔪 => ?_⟩
  exact ((hmax Q hQ hIQ).eq_of_le h𝔪.ne_top hQ𝔪).symm.le

end CommAlg

section ProjDim

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {m : ℕ}

/-- A point of `Proj k[X₀, …, Xₘ]` lies inside the irrelevant ideal. -/
private theorem toIdeal_le_irrelevant
    (w : ProjectiveSpectrum (homogeneousSubmodule (Fin (m + 1)) k)) :
    w.asHomogeneousIdeal.toIdeal ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal := by
  intro f hf
  have := w.isPrime
  have h0 : (DirectSum.decompose (homogeneousSubmodule (Fin (m + 1)) k) f 0 :
      MvPolynomial (Fin (m + 1)) k) ∈ w.asHomogeneousIdeal.toIdeal :=
    w.asHomogeneousIdeal.isHomogeneous 0 hf
  have hC : (DirectSum.decompose (homogeneousSubmodule (Fin (m + 1)) k) f 0 :
      MvPolynomial (Fin (m + 1)) k) = C (f.coeff 0) := by
    rw [← MvPolynomial.homogeneousComponent_zero]
    exact MvPolynomial.decomposition.decompose'_apply f 0
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker]
  change (DirectSum.decompose (homogeneousSubmodule (Fin (m + 1)) k) f 0 :
      MvPolynomial (Fin (m + 1)) k) = 0
  rw [hC] at h0 ⊢
  by_contra hne
  have hc : f.coeff 0 ≠ 0 := fun h => hne (by rw [h, C_0])
  exact this.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (hc.isUnit.map (C : k →+* _)))

/-- The irrelevant ideal of `k[X₀, …, Xₘ]` has height at most `m + 1`. -/
private theorem height_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal.height ≤
      ((m + 1 : ℕ) : ℕ∞) := by
  have hirr :
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal.IsPrime :=
    RingHom.ker_isPrime _
  have hdim : ringKrullDim (MvPolynomial (Fin (m + 1)) k) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have := Ideal.height_le_ringKrullDim_of_ne_top hirr.ne_top
  rw [hdim] at this
  exact_mod_cast this

/-- A point of `Proj k[X₀, …, Xₘ]` lies strictly inside the irrelevant ideal. -/
private theorem toIdeal_lt_irrelevant
    (w : ProjectiveSpectrum (homogeneousSubmodule (Fin (m + 1)) k)) :
    w.asHomogeneousIdeal.toIdeal <
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal := by
  refine lt_of_le_of_ne (toIdeal_le_irrelevant w) fun h => w.not_irrelevant_le ?_
  intro x hx
  change x ∈ w.asHomogeneousIdeal.toIdeal
  rw [h]
  exact hx

/-- If `z < w` in `Proj k[X₀, …, Xₘ]`, the height of `z` is at least two less than that of the
irrelevant ideal. -/
private theorem height_add_two_le_of_lt
    {z w : ProjectiveSpectrum (homogeneousSubmodule (Fin (m + 1)) k)} (hzw : z < w) :
    z.asHomogeneousIdeal.toIdeal.height + 1 + 1 ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal.height := by
  have := z.isPrime
  have := w.isPrime
  have hirr :
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).toIdeal.IsPrime :=
    RingHom.ker_isPrime _
  have hlt : z.asHomogeneousIdeal.toIdeal < w.asHomogeneousIdeal.toIdeal :=
    lt_of_le_of_ne hzw.le (fun h => hzw.ne (ProjectiveSpectrum.ext
      (HomogeneousIdeal.toIdeal_injective h)))
  calc z.asHomogeneousIdeal.toIdeal.height + 1 + 1
      ≤ w.asHomogeneousIdeal.toIdeal.height + 1 := by
        gcongr; exact Ideal.height_add_one_le_of_lt_of_isPrime hlt
    _ ≤ _ := Ideal.height_add_one_le_of_lt_of_isPrime (toIdeal_lt_irrelevant w)

/-- **Two disjoint curves in `ℙᵐ` force `m ≥ 3`.** If two non-generic, non-closed points of
`Proj k[X₀, …, Xₘ]` have disjoint closures, then `m ≥ 3`: in `ℙ²` (or smaller) two curves meet,
by Krull's height theorem. -/
private theorem three_le_of_disjoint
    (z₁ z₂ w₁ w₂ : ProjectiveSpectrum (homogeneousSubmodule (Fin (m + 1)) k))
    (h₁ : z₁ < w₁) (h₂ : z₂ < w₂)
    (hz₁ : z₁.asHomogeneousIdeal.toIdeal ≠ ⊥) (hz₂ : z₂.asHomogeneousIdeal.toIdeal ≠ ⊥)
    (hdisj : ∀ w : ProjectiveSpectrum (homogeneousSubmodule (Fin (m + 1)) k),
      ¬ (z₁ ≤ w ∧ z₂ ≤ w)) :
    3 ≤ m := by
  classical
  set 𝒜 := homogeneousSubmodule (Fin (m + 1)) k
  set irr := (HomogeneousIdeal.irrelevant 𝒜).toIdeal with hirrdef
  have hirr : irr.IsPrime := RingHom.ker_isPrime _
  have hpos : ∀ z : ProjectiveSpectrum 𝒜, z.asHomogeneousIdeal.toIdeal ≠ ⊥ →
      1 ≤ z.asHomogeneousIdeal.toIdeal.height := by
    intro z hz
    have := z.isPrime
    rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hz
  have k₁ := height_add_two_le_of_lt h₁
  by_contra hm
  push Not at hm
  have hm' : ((m + 1 : ℕ) : ℕ∞) ≤ 3 := by exact_mod_cast (show m + 1 ≤ 3 by omega)
  have hone : ∀ z : ProjectiveSpectrum 𝒜, 1 ≤ z.asHomogeneousIdeal.toIdeal.height →
      z.asHomogeneousIdeal.toIdeal.height + 1 + 1 ≤ irr.height →
      z.asHomogeneousIdeal.toIdeal.height = 1 := by
    intro z h1 h2
    have h3 : z.asHomogeneousIdeal.toIdeal.height + 1 + 1 ≤ 3 :=
      h2.trans (height_irrelevant_le.trans hm')
    have hne : z.asHomogeneousIdeal.toIdeal.height ≠ ⊤ := by
      intro h; rw [h] at h3; simp at h3
    obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hh] at h1 h3 ⊢
    have : (h + 1 + 1 : ℕ∞) ≤ ((3 : ℕ) : ℕ∞) := by exact_mod_cast h3
    have h1' : 1 ≤ h := by exact_mod_cast h1
    have : h + 1 + 1 ≤ 3 := by exact_mod_cast this
    norm_cast
    omega
  have := z₁.isPrime
  have := z₂.isPrime
  obtain ⟨F₁, hF₁⟩ : ∃ F, z₁.asHomogeneousIdeal.toIdeal = Ideal.span {F} :=
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (hone z₁ (hpos z₁ hz₁) k₁)).1
  obtain ⟨F₂, hF₂⟩ : ∃ F, z₂.asHomogeneousIdeal.toIdeal = Ideal.span {F} :=
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      (hone z₂ (hpos z₂ hz₂) (height_add_two_le_of_lt h₂))).1
  set I := Ideal.span (({F₁, F₂} : Finset (MvPolynomial (Fin (m + 1)) k)) :
    Set (MvPolynomial (Fin (m + 1)) k)) with hIdef
  have hI1 : z₁.asHomogeneousIdeal.toIdeal ≤ I := by
    rw [hF₁]
    exact Ideal.span_mono (by simp)
  have hI2 : z₂.asHomogeneousIdeal.toIdeal ≤ I := by
    rw [hF₂]
    exact Ideal.span_mono (by simp)
  have hIirr : I ≤ irr := by
    rw [hIdef, Ideal.span_le]
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (toIdeal_le_irrelevant z₁) (hF₁ ▸ Ideal.subset_span rfl)
    · exact (toIdeal_le_irrelevant z₂) (hF₂ ▸ Ideal.subset_span rfl)
  obtain ⟨𝔮, h𝔮, h𝔮irr⟩ := Ideal.exists_minimalPrimes_le hIirr
  have := h𝔮.1.1
  have hcore : HomogeneousIdeal.irrelevant 𝒜 ≤ Ideal.homogeneousCore 𝒜 𝔮 := by
    by_contra hnot
    exact hdisj ⟨Ideal.homogeneousCore 𝒜 𝔮, this.homogeneousCore, hnot⟩
      ⟨(Ideal.homogeneousCore.gc 𝒜 _ _).mp (hI1.trans h𝔮.1.2),
        (Ideal.homogeneousCore.gc 𝒜 _ _).mp (hI2.trans h𝔮.1.2)⟩
  have h𝔮eq : 𝔮 = irr := le_antisymm h𝔮irr
    ((show (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ (Ideal.homogeneousCore 𝒜 𝔮).toIdeal
      from hcore).trans (Ideal.toIdeal_homogeneousCore_le 𝒜 𝔮))
  have hK := Ideal.height_le_card_of_mem_minimalPrimes_span_finset h𝔮
  rw [h𝔮eq] at hK
  have hcard : (({F₁, F₂} : Finset (MvPolynomial (Fin (m + 1)) k)).card : ℕ∞) ≤ 2 := by
    exact_mod_cast Finset.card_le_two
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := by
    calc (1 : ℕ∞) + 1 + 1 ≤ z₁.asHomogeneousIdeal.toIdeal.height + 1 + 1 := by
          gcongr; exact hpos z₁ hz₁
      _ ≤ irr.height := k₁
      _ ≤ _ := hK
      _ ≤ 2 := hcard
  exact absurd this (by decide)

end ProjDim

section ProjGerm

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The germ at `y ∈ D₊(s)` of the section `a / s` of `Proj`, read in the homogeneous
localization at `y`, is the fraction `a / s`. -/
private theorem val_stalkIso'_germ_awayToSection {s : A} (hs : s ∈ 𝒜 1) (a : A)
    (ha : a ∈ 𝒜 (1 • 1)) (y : AlgebraicGeometry.Proj 𝒜) (hy : y ∈ Proj.basicOpen 𝒜 s) :
    (Proj.stalkIso' 𝒜 y ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 s) y hy
      (Proj.awayToSection 𝒜 s (Away.mk 𝒜 hs 1 a ha)))).val =
      Localization.mk a ⟨s, hy⟩ := by
  have e := congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 s y hy).hom
    (Away.mk 𝒜 hs 1 a ha))
  change (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 s) y hy
    (Proj.awayToSection 𝒜 s (Away.mk 𝒜 hs 1 a ha)) = _ at e
  rw [e, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  change (Proj.stalkIso' 𝒜 y ((Proj.stalkIso' 𝒜 y).symm _)).val = _
  rw [RingEquiv.apply_symm_apply]
  change Localization.mk a ⟨s ^ 1, _⟩ = _
  congr 1
  exact Subtype.ext (pow_one s)

end ProjGerm

section Subst

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {m : ℕ}

/-- The linear substitution `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` of `k[X₀, …, Xₘ]`. -/
private noncomputable def linSubst (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) :
    MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin (m + 1)) k :=
  aeval fun i => ∑ j, C (M i j) * X j

private theorem linSubst_X (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (i : Fin (m + 1)) :
    linSubst M (X i) = ∑ j, C (M i j) * X j :=
  aeval_X _ _

private theorem isHomogeneous_linSubst_X (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (i : Fin (m + 1)) : (∑ j, C (M i j) * X j : MvPolynomial (Fin (m + 1)) k).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => by simpa using isHomogeneous_C_mul_X (M i j) j

private theorem linSubst_mem (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) {d : ℕ}
    {x : MvPolynomial (Fin (m + 1)) k} (hx : x ∈ homogeneousSubmodule (Fin (m + 1)) k d) :
    linSubst M x ∈ homogeneousSubmodule (Fin (m + 1)) k d := by
  rw [mem_homogeneousSubmodule] at hx ⊢
  have := hx.eval₂ C (fun i => ∑ j, C (M i j) * X j)
    (fun r => isHomogeneous_C _ r) (isHomogeneous_linSubst_X M)
  have e : linSubst M x = eval₂ C (fun i => ∑ j, C (M i j) * X j) x := by
    rw [linSubst, aeval_def, MvPolynomial.algebraMap_eq]
  rw [e]
  simpa using this

/-- The linear substitution as a graded ring endomorphism. -/
private noncomputable def linSubstHom (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) :
    homogeneousSubmodule (Fin (m + 1)) k →+*ᵍ homogeneousSubmodule (Fin (m + 1)) k where
  toRingHom := (linSubst M).toRingHom
  map_mem := linSubst_mem M

private theorem linSubstHom_apply (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (x : MvPolynomial (Fin (m + 1)) k) : linSubstHom M x = linSubst M x := rfl

private theorem linSubst_comp (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) :
    (linSubst M).comp (linSubst N) = linSubst (N * M) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, linSubst_X, linSubst_X, map_sum]
  simp only [map_mul, linSubst_X, Finset.mul_sum, Matrix.mul_apply,
    Finset.sum_mul, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show linSubst M (C (N i j)) = C (N i j) by
    rw [linSubst, aeval_C, MvPolynomial.algebraMap_eq], ← mul_assoc, ← C_mul]

private theorem linSubst_one : linSubst (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
    AlgHom.id k _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [linSubst_X, AlgHom.id_apply, Finset.sum_eq_single i (fun j _ hji => by
    simp [Ne.symm hji]) (by simp)]
  simp

private theorem linSubstHom_comp (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (h : N * M = 1) :
    (linSubstHom M).comp (linSubstHom N) = GradedRingHom.id _ := by
  refine DFunLike.ext _ _ fun x => ?_
  change (linSubst M) ((linSubst N) x) = x
  rw [← AlgHom.comp_apply, linSubst_comp, h, linSubst_one, AlgHom.id_apply]

private theorem irrelevant_le_map_linSubstHom (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : N * M = 1) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) k)).map (linSubstHom M) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi y hy
  have e : y = linSubstHom M (linSubstHom N y) := by
    rw [← GradedRingHom.comp_apply, linSubstHom_comp M N h]; rfl
  rw [e]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hi (linSubst_mem N hy))

end Subst

section ProjMap

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {m : ℕ}

private theorem proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f g : 𝒜 →+*ᵍ ℬ} (h : f = g) (hf) (hg) :
    Proj.map f hf = Proj.map g hg := by
  subst h; rfl

/-- The automorphism of `ℙᵐ_k` given by a linear substitution `M` with inverse `N`. -/
private noncomputable def projSubst (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (h : N * M = 1) :
    AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (m + 1)) k) ⟶
      AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (m + 1)) k) :=
  Proj.map (linSubstHom M) (irrelevant_le_map_linSubstHom M N h)

private theorem projSubst_comp (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (h : N * M = 1)
    (h' : M * N = 1) : projSubst M N h ≫ projSubst N M h' = 𝟙 _ := by
  rw [projSubst, projSubst, ← Proj.map_comp]
  exact (proj_map_congr (linSubstHom_comp M N h) _ _).trans Proj.map_id

private theorem isIso_projSubst (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (h : N * M = 1)
    (h' : M * N = 1) : IsIso (projSubst M N h) :=
  ⟨⟨projSubst N M h', projSubst_comp M N h h', projSubst_comp N M h' h⟩⟩

private theorem projSubst_toSpecZero (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (h : N * M = 1) :
    projSubst M N h ≫ Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (homogeneousSubmodule (Fin (m + 1)) k 0))) =
    Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (homogeneousSubmodule (Fin (m + 1)) k 0))) := by
  refine (Proj.mapAffineOpenCover (linSubstHom M)
    (irrelevant_le_map_linSubstHom M N h)).openCover.hom_ext _ _ fun s => ?_
  obtain ⟨i, a, ha⟩ := s
  change Proj.awayι _ (linSubstHom M a) ((linSubstHom M).map_mem ha) i.pos ≫ _ =
    Proj.awayι _ (linSubstHom M a) ((linSubstHom M).map_mem ha) i.pos ≫ _
  rw [projSubst, Proj.awayι_comp_map_assoc (linSubstHom M) _ i.pos a ha,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  change (HomogeneousLocalization.map (linSubstHom M) _ (fromZeroRingHom _ _ _)).val =
    (fromZeroRingHom _ _ _).val
  rw [fromZeroRingHom, fromZeroRingHom]
  erw [HomogeneousLocalization.map_mk]
  simp only [val_mk]
  congr 1
  · change linSubst M (algebraMap k _ c : MvPolynomial (Fin (m + 1)) k) = _
    rw [AlgHom.commutes]
    rfl
  · exact Subtype.ext (map_one (linSubst M))

/-- The automorphism `projSubst` lies over `Spec k`, for the structure morphism
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`. -/
private theorem projSubst_projToSpecCoeff (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : N * M = 1) :
    projSubst M N h ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k m =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k m := by
  rw [Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff,
    Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap]
  exact projSubst_toSpecZero M N h

/-- The pull-back of a linear substitution `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` to an evaluation homomorphism is
the evaluation at the substituted values. -/
private theorem eval₂Hom_comp_linSubstHom {B : Type*} [CommRing B] (κ : k →+* B)
    (r : Fin (m + 1) → B) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) k) :
    (MvPolynomial.eval₂Hom κ r).comp (linSubstHom M).toRingHom =
      MvPolynomial.eval₂Hom κ fun i => ∑ j, κ (M i j) * r j := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · change MvPolynomial.eval₂Hom κ r (linSubst M (C c)) = _
    rw [linSubst, aeval_C, MvPolynomial.algebraMap_eq, eval₂Hom_C, eval₂Hom_C]
  · change MvPolynomial.eval₂Hom κ r (linSubst M (X i)) = _
    rw [linSubst_X, map_sum, eval₂Hom_X']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, eval₂Hom_C, eval₂Hom_X']

end ProjMap

/-- **The generic point of a fibre over a closed point has codimension one.** -/
private theorem coheight_eq_one_of_isGenericPoint {k : Type u} [Field k] {C Y : Scheme.{u}}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (pr : Y ⟶ C)
    (ι : C.functionField →+* Y.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = Y.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    {c : C} (hc : c ≠ genericPoint C) {e : Y} (he : IsGenericPoint e (pr.base ⁻¹' {c})) :
    coheight e = 1 := by
  have hc1 : coheight c = 1 := IsCurve.coheight_eq_one f hc
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hc1
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk c)
  have hemem : pr e = c := he.mem
  subst hemem
  have ht0 : t ≠ 0 := ht.ne_zero
  have htm : t ∈ IsLocalRing.maximalIdeal _ := ht.not_isUnit
  set t' := pr.stalkMap e t
  have ht'm : t' ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk e) :=
    map_nonunit (pr.stalkMap e).hom t htm
  have htK : algebraMap (C.presheaf.stalk (pr e)) C.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht0
  have ht'K : algebraMap (Y.presheaf.stalk e) Y.functionField t' =
      ι (algebraMap (C.presheaf.stalk (pr e)) C.functionField t) :=
    algebraMap_stalkMap pr ι hι e t
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht'K
    exact htK (ι.injective (ht'K.symm.trans (map_zero ι).symm))
  obtain ⟨w, hwe, hw1, hwpos⟩ := exists_ord_pos_of_mem_maximalIdeal e ht'0 ht'm
  rw [ht'K] at hwpos
  have hpw : pr w ≠ genericPoint C := by
    intro hpw
    have hinv : (algebraMap (C.presheaf.stalk (pr e)) C.functionField t)⁻¹ ∈
        Set.range (algebraMap (C.presheaf.stalk (pr w)) C.functionField) := by
      rw [hpw]
      refine ⟨(algebraMap (C.presheaf.stalk (pr e)) C.functionField t)⁻¹, ?_⟩
      change (C.presheaf.stalkSpecializes _).hom _ = _
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    obtain ⟨s, hs⟩ := hinv
    have hreg : ι (algebraMap (C.presheaf.stalk (pr e)) C.functionField t)⁻¹ ∈
        Set.range (algebraMap (Y.presheaf.stalk w) Y.functionField) :=
      ⟨pr.stalkMap w s, by rw [algebraMap_stalkMap pr ι hι w s, hs]⟩
    have hι0 : ι (algebraMap (C.presheaf.stalk (pr e)) C.functionField t) ≠ 0 :=
      (map_ne_zero_iff _ ι.injective).mpr htK
    have hnn := (ord_nonneg_iff hw1 (by rw [map_inv₀]; exact inv_ne_zero hι0)).mpr hreg
    rw [map_inv₀, Stacks.Chow.ord_inv_functionField hι0] at hnn
    omega
  have hcl : IsClosed ({pr w} : Set C) :=
    Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f hpw
  have hspec : pr w ⤳ pr e := hwe.map pr.base.hom.continuous
  have hpwe : pr e = pr w := hspec.mem_closed hcl rfl
  have hew : e ⤳ w := by
    rw [specializes_iff_mem_closure, he.def]
    exact hpwe.symm
  rw [← (Specializes.antisymm hwe hew).eq]
  exact hw1

/-- In a domain, a height-one prime containing a nonzero element `b` is minimal over `(b)`. -/
private theorem mem_minimalPrimes_span_singleton_of_height_eq_one {R : Type*} [CommRing R]
    [IsDomain R] {b : R} (hb : b ≠ 0) {P : Ideal R} [P.IsPrime] (hP1 : P.height = 1)
    (hbP : b ∈ P) : P ∈ (Ideal.span {b}).minimalPrimes := by
  refine ⟨⟨‹_›, (Ideal.span_singleton_le_iff_mem _).mpr hbP⟩, fun Q ⟨hQ, hbQ⟩ hQP => ?_⟩
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hne (h ▸ le_rfl))
  have e := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hP1] at e
  have hQ0 : Q.height = 0 := by
    have hne' : Q.height ≠ ⊤ := fun h => by rw [h] at e; simp at e
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne'
    rw [← hn] at e ⊢
    have : n + 1 ≤ 1 := by exact_mod_cast e
    norm_cast
    omega
  rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
  rw [hQ0] at hbQ
  exact hb ((Ideal.mem_bot).mp (hbQ (Ideal.mem_span_singleton_self b)))

/-- On a nonempty affine open of a normal Noetherian integral scheme, a nonzero rational function
has nonzero order at only finitely many codimension-one points. -/
private theorem finite_setOf_ord_ne_zero_of_isAffineOpen {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {h : X.functionField} (hh : h ≠ 0) :
    {q : X | q ∈ U ∧ coheight q = 1 ∧ X.ord h q ≠ 0}.Finite := by
  have : IsDomain Γ(X, U) := IsIntegral.component_integral U
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) h
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hh
  have hsK : X.germToFunctionField U s ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective U)).mpr hs0
  have haK : X.germToFunctionField U a ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective U)).mpr ha0
  set M : Set (Ideal Γ(X, U)) := (Ideal.span {a}).minimalPrimes ∪ (Ideal.span {s}).minimalPrimes
  have hM : M.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).union
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)
  have hM' : {P : PrimeSpectrum Γ(X, U) | P.asIdeal ∈ M}.Finite :=
    hM.preimage (fun P _ Q _ h => PrimeSpectrum.ext h)
  refine (hM'.image hU.fromSpec.base).subset ?_
  rintro q ⟨hqU, hq1, hqord⟩
  refine ⟨hU.primeIdealOf ⟨q, hqU⟩, ?_, hU.fromSpec_primeIdealOf ⟨q, hqU⟩⟩
  have hP1 : (hU.primeIdealOf ⟨q, hqU⟩).asIdeal.height = 1 := by
    rw [← coheight_eq_height_primeIdealOf hU hqU]; exact hq1
  by_cases haP : a ∈ (hU.primeIdealOf ⟨q, hqU⟩).asIdeal
  · exact Or.inl (mem_minimalPrimes_span_singleton_of_height_eq_one ha0 hP1 haP)
  by_cases hsP : s ∈ (hU.primeIdealOf ⟨q, hqU⟩).asIdeal
  · exact Or.inr (mem_minimalPrimes_span_singleton_of_height_eq_one hs0 hP1 hsP)
  exfalso
  apply hqord
  change X.ord (X.germToFunctionField U a / X.germToFunctionField U s) q = 0
  have hdiv0 : X.germToFunctionField U a / X.germToFunctionField U s ≠ 0 := div_ne_zero haK hsK
  have h1 : 0 ≤ X.ord (X.germToFunctionField U a / X.germToFunctionField U s) q := by
    refine (ord_nonneg_iff hq1 hdiv0).mpr ((mem_range_stalk_iff hU hqU _).mpr ⟨a, s, hsP, ?_⟩)
    rw [div_mul_cancel₀ _ hsK]
  have h2 : 0 ≤ X.ord (X.germToFunctionField U a / X.germToFunctionField U s)⁻¹ q := by
    refine (ord_nonneg_iff hq1 (inv_ne_zero hdiv0)).mpr
      ((mem_range_stalk_iff hU hqU _).mpr ⟨s, a, haP, ?_⟩)
    rw [inv_div, div_mul_cancel₀ _ haK]
  rw [Stacks.Chow.ord_inv_functionField hdiv0] at h2
  omega

/-- **Finiteness of a principal divisor.** On a quasi-compact normal Noetherian integral scheme, a
nonzero rational function has nonzero order at only finitely many codimension-one points. -/
private theorem finite_setOf_ord_ne_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {h : X.functionField} (hh : h ≠ 0) :
    {q : X | coheight q = 1 ∧ X.ord h q ≠ 0}.Finite := by
  have hpick : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hpick
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  have hfin : ∀ x ∈ (t : Set X),
      {q : X | q ∈ V x ∧ coheight q = 1 ∧ X.ord h q ≠ 0}.Finite := fun x _ => by
    have : Nonempty (V x) := ⟨⟨x, hxV x⟩⟩
    exact finite_setOf_ord_ne_zero_of_isAffineOpen (hV x) hh
  refine (Set.Finite.biUnion (t := fun x => {q : X | q ∈ V x ∧ coheight q = 1 ∧ X.ord h q ≠ 0})
    t.finite_toSet hfin).subset ?_
  · rintro q ⟨hq1, hq⟩
    obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ q))
    exact Set.mem_biUnion hx ⟨hqx, hq1, hq⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The open `pr₁⁻¹ C₀ ∩ pr₂⁻¹ C₀` of `C × C`, where `C₀ = φ⁻¹ D₊(X₀)`. -/
private noncomputable abbrev chartOpen {R : Type u} [CommRing R] {C Y : Scheme.{u}}
    (pr₁ pr₂ : Y ⟶ C) {n : ℕ}
    (φNP : C ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    Y.Opens :=
  pr₁ ⁻¹ᵁ (φNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0)) ⊓
    pr₂ ⁻¹ᵁ (φNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0))

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The affine chart `W = π_{ab}⁻¹(𝔸²)`.** For `a, b ≠ 0` the open `W = pr₁⁻¹ C₀ ∩ pr₂⁻¹ C₀`,
`C₀ = φ⁻¹ D₊(X₀)`, is affine, its ring of sections is finite over `k[ξ_a, ξ'_b]`, and it contains
every point at which `ξ_a` and `ξ'_b` are regular. -/
private theorem exists_affine_chart {k : Type u} [Field k] {C Y : Scheme.{u}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    [LocallyOfFiniteType f]
    [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {pr₁ pr₂ : Y ⟶ C} (hY : IsPullback pr₁ pr₂ f f)
    [IsIntegral Y] [IsLocallyNoetherian Y] [Algebra k Y.functionField]
    (hkY : ∀ c : k, algebraMap k Y.functionField c =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →+* Y.functionField)
    (hι₁ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₁ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₁ (C.germToFunctionField V t) = Y.germToFunctionField (pr₁ ⁻¹ᵁ V) (pr₁.app V t))
    (hι₂ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₂ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₂ (C.germToFunctionField V t) = Y.germToFunctionField (pr₂ ⁻¹ᵁ V) (pr₂.app V t))
    {n : ℕ} (E : C → ℤ) (x : Fin (n + 1) → C.functionField) (hx0 : ∀ j, x j ≠ 0)
    (hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z) {R : Type u} [CommRing R]
    (φNP : C ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsAffineHom φNP]
    (hφNP_ne : ((φNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) : C.Opens) : Set C).Nonempty)
    (hφNP : ∀ [Nonempty (φNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0))] (j : Fin (n + 1)),
      C.germToFunctionField _ (φNP.app _ (Proj.awayToSection _ (MvPolynomial.X 0)
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R 0)) 1
          (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
            MvPolynomial.isHomogeneous_X R j)))) = x j / x 0)
    (hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0)
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (_ : IsAffineOpen (chartOpen pr₁ pr₂ φNP)) (_ : Nonempty (chartOpen pr₁ pr₂ φNP))
      (φ : MvPolynomial (Fin 2) k →+* Γ(Y, chartOpen pr₁ pr₂ φNP)),
      (∀ r, algebraMap Γ(Y, chartOpen pr₁ pr₂ φNP) Y.functionField (φ r) =
        MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) ∧ φ.Finite ∧
      ∀ q : Y, ι₁ (x a / x 0) ∈ Set.range (algebraMap (Y.presheaf.stalk q) Y.functionField) →
        ι₂ (x b / x 0) ∈ Set.range (algebraMap (Y.presheaf.stalk q) Y.functionField) →
        q ∈ chartOpen pr₁ pr₂ φNP := by
  classical
  set f₀ := f
  set C₀ : C.Opens := φNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) with hC₀def
  have hC₀ne : Nonempty C₀ := ⟨⟨_, hφNP_ne.some_mem⟩⟩
  have hC₀ : IsAffineOpen C₀ :=
    (Proj.isAffineOpen_basicOpen _ (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R 0))
      Nat.one_pos).preimage φNP
  have hchart : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ c : C,
      x a' / x 0 ∈ Set.range (algebraMap (C.presheaf.stalk c) C.functionField) → c ∈ C₀ :=
    fun a' ha' c hc => mem_preimage_proj_basicOpen_of_mem_range f₀ E x hx0 hxE φNP hφNP_ne hφNP
      (hNG1 a' ha') hc
  have hint : ∀ a' : Fin (n + 1), a' ≠ 0 → ∀ s : Γ(C, C₀), C.germToFunctionField C₀ s ∈
      integralClosure (Algebra.adjoin k {x a' / x 0}) C.functionField :=
    fun a' ha' => germToFunctionField_mem_integralClosure f₀ hkC _ C₀ (hchart a' ha')
  set sec : Fin (n + 1) → Γ(C, C₀) := fun j => φNP.app _ (Proj.awayToSection _ (MvPolynomial.X 0)
    (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R 0)) 1
      (MvPolynomial.X j) (by simpa [MvPolynomial.mem_homogeneousSubmodule] using
        MvPolynomial.isHomogeneous_X R j))) with hsecdef
  have hsec : ∀ j, C.germToFunctionField C₀ (sec j) = x j / x 0 := fun j => hφNP j
  set W : Y.Opens := pr₁ ⁻¹ᵁ C₀ ⊓ pr₂ ⁻¹ᵁ C₀ with hWdef
  have hC₀top : C₀ ≤ f₀ ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  have hW : IsAffineOpen W :=
    isAffineOpen_of_isPullback hY (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top hC₀top hWdef
  have hWne : Nonempty W := by
    obtain ⟨c, hc⟩ := hφNP_ne
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f₀) (g := f₀) c c rfl
    refine ⟨⟨hY.isoPullback.inv z, ?_, ?_⟩⟩
    · change pr₁ (hY.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hY.isoPullback_inv_fst, hz1]
      exact hc
    · change pr₂ (hY.isoPullback.inv z) ∈ C₀
      rw [← Scheme.Hom.comp_apply, hY.isoPullback_inv_snd, hz2]
      exact hc
  have : Nonempty (pr₁ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.1⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ C₀) := ⟨⟨hWne.some.1, hWne.some.2.2⟩⟩
  have : IsDomain Γ(Y, W) := IsIntegral.component_integral W
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W hW
  have : LocallyOfFiniteType pr₁ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hY.flip inferInstance
  have hBL : ∀ b : Γ(Y, W), algebraMap Γ(Y, W) Y.functionField b = Y.germToFunctionField W b :=
    fun _ => rfl
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨hWne.some.1, trivial⟩⟩
  have hgermLE : ∀ {V : Y.Opens} [Nonempty V] (h : W ≤ V) (t : Γ(Y, V)),
      Y.germToFunctionField W (Y.presheaf.map (homOfLE h).op t) = Y.germToFunctionField V t :=
    fun h t => Y.presheaf.germ_res_apply (homOfLE h) _ _ t
  set κ : k →+* Γ(Y, W) := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (pr₁ ≫ f₀).appLE ⊤ W (fun _ _ => trivial)).hom with hκdef
  have hκ : ∀ c, algebraMap Γ(Y, W) Y.functionField (κ c) = algebraMap k Y.functionField c := by
    intro c
    rw [hkY c, hBL]
    exact hgermLE le_top _
  have hpr₁ : ∀ s : Γ(C, C₀),
      algebraMap Γ(Y, W) Y.functionField (pr₁.appLE C₀ W inf_le_left s) =
        ι₁ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₁ C₀ s, hBL]
    exact hgermLE inf_le_left _
  have hpr₂ : ∀ s : Γ(C, C₀),
      algebraMap Γ(Y, W) Y.functionField (pr₂.appLE C₀ W inf_le_right s) =
        ι₂ (C.germToFunctionField C₀ s) := by
    intro s
    rw [hι₂ C₀ s, hBL]
    exact hgermLE inf_le_right _
  set ta := pr₁.appLE C₀ W inf_le_left (sec a)
  set tb := pr₂.appLE C₀ W inf_le_right (sec b)
  set φ : MvPolynomial (Fin 2) k →+* Γ(Y, W) := MvPolynomial.eval₂Hom κ ![ta, tb]
  let : Algebra (MvPolynomial (Fin 2) k) Γ(Y, W) := φ.toAlgebra
  let : Algebra (MvPolynomial (Fin 2) k) Y.functionField :=
    (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)]).toRingHom.toAlgebra
  have hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.C c) =
      algebraMap k Y.functionField c := fun c => MvPolynomial.aeval_C _ c
  have hRLa : algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0) := by
    change MvPolynomial.aeval _ (MvPolynomial.X 0) = _
    rw [MvPolynomial.aeval_X]; rfl
  have hRLb : algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0) := by
    change MvPolynomial.aeval _ (MvPolynomial.X 1) = _
    rw [MvPolynomial.aeval_X]; rfl
  have hRBa : algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.X 0) = ta :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBb : algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.X 1) = tb :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have hRBc : ∀ c, algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.C c) = κ c :=
    fun c => MvPolynomial.eval₂Hom_C _ _ _
  have hRBL : algebraMap (MvPolynomial (Fin 2) k) Y.functionField =
      (algebraMap Γ(Y, W) Y.functionField).comp (algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · change algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.C c) =
        algebraMap Γ(Y, W) Y.functionField
          (algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.C c))
      rw [hRBc, hRL₀, hκ]
    · fin_cases j
      · change algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.X 0) =
          algebraMap Γ(Y, W) Y.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.X 0))
        rw [hRBa, hRLa, hpr₁, hsec]
      · change algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.X 1) =
          algebraMap Γ(Y, W) Y.functionField
            (algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) (MvPolynomial.X 1))
        rw [hRBb, hRLb, hpr₂, hsec]
  have : IsScalarTower (MvPolynomial (Fin 2) k) Γ(Y, W) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [hRBL]; rfl
  have : Nonempty (⊤ : C.Opens) := ⟨⟨pr₁ hWne.some.1, trivial⟩⟩
  have : Nonempty (pr₁ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hWne.some.1, trivial⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ (⊤ : C.Opens)) := ⟨⟨hWne.some.1, trivial⟩⟩
  have hι₁k : ∀ c, ι₁ (algebraMap k C.functionField c) = algebraMap k Y.functionField c := by
    intro c
    rw [hkC c, hkY c]
    exact (hι₁ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  have hι₂k : ∀ c, ι₂ (algebraMap k C.functionField c) = algebraMap k Y.functionField c := by
    intro c
    rw [hkC c, hkY c, hY.w]
    exact (hι₂ ⊤ _).trans (by rw [Scheme.Hom.comp_appTop]; rfl)
  let ι₁' : C.functionField →ₐ[k] Y.functionField := { ι₁ with commutes' := hι₁k }
  let ι₂' : C.functionField →ₐ[k] Y.functionField := { ι₂ with commutes' := hι₂k }
  have hintOf : ∀ (ι' : C.functionField →ₐ[k] Y.functionField) (a' : Fin (n + 1)), a' ≠ 0 →
      ∀ j : Fin 2, algebraMap (MvPolynomial (Fin 2) k) Y.functionField (MvPolynomial.X j) =
        ι' (x a' / x 0) → ∀ t : Γ(C, C₀) → Γ(Y, W),
      (∀ s, algebraMap Γ(Y, W) Y.functionField (t s) = ι' (C.germToFunctionField C₀ s)) →
      ∀ s, IsIntegral (MvPolynomial (Fin 2) k) (t s) := by
    intro ι' a' ha' j hj t ht s
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (MvPolynomial (Fin 2) k) Γ(Y, W) Y.functionField)
      (IsFractionRing.injective Γ(Y, W) Y.functionField)).mp ?_
    change IsIntegral _ (algebraMap Γ(Y, W) Y.functionField (t s))
    rw [ht]
    exact isIntegral_map_of_mem_integralClosure ι' _ ⟨_, hj⟩ (fun c => ⟨_, hRL₀ c⟩)
      (hint a' ha' s)
  have : Algebra.IsIntegral (MvPolynomial (Fin 2) k) Γ(Y, W) := ⟨fun y => mem_of_isPushout
    (isPushout_appLE_of_isPullback_inter hY (isAffineOpen_top (Spec (.of k))) hC₀ hC₀ hC₀top
      hC₀top hWdef inf_le_left inf_le_right)
    (integralClosure (MvPolynomial (Fin 2) k) Γ(Y, W)).toSubring
    (hintOf ι₁' a ha 0 hRLa _ hpr₁) (hintOf ι₂' b hb 1 hRLb _ hpr₂) y⟩
  let : Algebra k Γ(Y, W) := κ.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin 2) k) Γ(Y, W) :=
    IsScalarTower.of_algebraMap_eq fun c => (hRBc c).symm
  have : Algebra.FiniteType k Γ(Y, W) := by
    have h1 := (pr₁ ≫ f₀).finiteType_appLE (isAffineOpen_top (Spec (.of k))) hW
      (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ fun y =>
        ⟨(Scheme.ΓSpecIso (.of k)).hom y, by simp⟩
    exact h1.comp h2
  have : Algebra.FiniteType (MvPolynomial (Fin 2) k) Γ(Y, W) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin 2) k) Γ(Y, W)
  have hfin : Module.Finite (MvPolynomial (Fin 2) k) Γ(Y, W) := Algebra.IsIntegral.finite
  refine ⟨hW, hWne, φ, fun r => ?_, hfin, fun q hqa hqb => ?_⟩
  · change algebraMap Γ(Y, W) Y.functionField (algebraMap (MvPolynomial (Fin 2) k) Γ(Y, W) r) =
      algebraMap (MvPolynomial (Fin 2) k) Y.functionField r
    rw [hRBL]; rfl
  · exact ⟨hchart a ha _ (mem_range_stalk_of_map_mem_range f₀ pr₁ ι₁ hι₁ q hqa),
      hchart b hb _ (mem_range_stalk_of_map_mem_range f₀ pr₂ ι₂ hι₂ q hqb)⟩

section Chart

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [Algebra k Y.functionField] {ξ : Fin 2 → Y.functionField}
  {W : Y.Opens} (hW : IsAffineOpen W) [Nonempty W]
  {φ : MvPolynomial (Fin 2) k →+* Γ(Y, W)}
  (hφK : ∀ r, algebraMap Γ(Y, W) Y.functionField (φ r) = MvPolynomial.aeval ξ r)

include hW hφK

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- For a point `q` of the chart, `r(ξ)` vanishes at `q` exactly when `r` lies over the prime of
`q`. -/
private theorem mem_comap_primeIdealOf_iff {q : Y} (hqW : q ∈ W) (r : MvPolynomial (Fin 2) k) :
    r ∈ (hW.primeIdealOf ⟨q, hqW⟩).asIdeal.comap φ ↔
      ∃ t ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk q),
        algebraMap (Y.presheaf.stalk q) Y.functionField t = MvPolynomial.aeval ξ r := by
  rw [mem_maximalIdeal_stalk_iff hW hqW]
  constructor
  · intro hr
    refine ⟨φ r, 1, hr, fun h => (hW.primeIdealOf ⟨q, hqW⟩).isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [map_one, mul_one, ← hφK]; rfl
  · rintro ⟨a', s', ha', hs', has'⟩
    have : IsFractionRing Γ(Y, W) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y W hW
    have hrs : φ r * s' = a' := by
      apply IsFractionRing.injective Γ(Y, W) Y.functionField
      rw [map_mul, hφK]
      exact has'
    have : φ r * s' ∈ (hW.primeIdealOf ⟨q, hqW⟩).asIdeal := hrs ▸ ha'
    exact ((hW.primeIdealOf ⟨q, hqW⟩).isPrime.mem_or_mem this).resolve_right hs'

/-- At a codimension-one point `q` of the chart, a polynomial `r` with `r(ξ) ≠ 0` lies over the
prime of `q` exactly when `r(ξ)` has positive order at `q`. -/
private theorem mem_comap_primeIdealOf_iff_ord {q : Y} (hqW : q ∈ W) (hq1 : coheight q = 1)
    {r : MvPolynomial (Fin 2) k} (hr : MvPolynomial.aeval ξ r ≠ 0) :
    r ∈ (hW.primeIdealOf ⟨q, hqW⟩).asIdeal.comap φ ↔ 0 < Y.ord (MvPolynomial.aeval ξ r) q := by
  rw [mem_comap_primeIdealOf_iff hW hφK hqW, ord_pos_iff hq1 hr]

/-- **A codimension-one point of the chart is not contracted.** Some polynomial `G` with
`G(ξ) ≠ 0` vanishes at `q`. -/
private theorem exists_aeval_ne_zero_ord_pos (hφfin : φ.Finite) {q : Y} (hqW : q ∈ W)
    (hq1 : coheight q = 1) :
    ∃ G : MvPolynomial (Fin 2) k, MvPolynomial.aeval ξ G ≠ 0 ∧
      0 < Y.ord (MvPolynomial.aeval ξ G) q := by
  have : IsDomain Γ(Y, W) := IsIntegral.component_integral W
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W hW
  set Q := (hW.primeIdealOf ⟨q, hqW⟩).asIdeal
  have hQ1 : Q.height = 1 := by rw [← coheight_eq_height_primeIdealOf hW hqW]; exact hq1
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQ1
  obtain ⟨b, hbQ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  let R := MvPolynomial (Fin 2) k ⧸ RingHom.ker φ
  let : Algebra R Γ(Y, W) := (RingHom.kerLift φ).toAlgebra
  let : Algebra (MvPolynomial (Fin 2) k) Γ(Y, W) := φ.toAlgebra
  have : IsScalarTower (MvPolynomial (Fin 2) k) R Γ(Y, W) :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.kerLift_mk φ r).symm
  have : IsDomain R := RingHom.kerLift_injective φ |>.isDomain _
  have hbint : IsIntegral (MvPolynomial (Fin 2) k) b := hφfin.to_isIntegral b
  have hbint' : IsIntegral R b := hbint.tower_top
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hb0 hbQ hbint')
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hφG : φ G ≠ 0 := by
    intro h
    exact hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr ((RingHom.mem_ker).mpr h))
  have hGK : MvPolynomial.aeval ξ G ≠ 0 := by
    rw [← hφK]
    exact (map_ne_zero_iff _ (IsFractionRing.injective Γ(Y, W) Y.functionField)).mpr hφG
  refine ⟨G, hGK, (mem_comap_primeIdealOf_iff_ord hW hφK hqW hq1 hGK).mp ?_⟩
  exact hxQ

/-- **Points over a maximal ideal.** Let `𝔪` be a maximal ideal of `k[ξ_a, ξ'_b]`, `ξ` regular
somewhere over it in the sense of orders, and let the chart contain every point at which `ξ` is
regular. A point `p` over `𝔪` lies in the chart, with prime lying over `𝔪`. -/
private theorem exists_mem_comap_eq (κ : ∀ y : Y, k →+* Y.presheaf.stalk y)
    (hκ : ∀ y, (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (κ y) =
      algebraMap k Y.functionField)
    (hWmem : ∀ q : Y, ξ 0 ∈ Set.range (algebraMap (Y.presheaf.stalk q) Y.functionField) →
      ξ 1 ∈ Set.range (algebraMap (Y.presheaf.stalk q) Y.functionField) → q ∈ W)
    {𝔪 : Ideal (MvPolynomial (Fin 2) k)} (h𝔪 : 𝔪.IsMaximal) {p : Y}
    (hp : ∀ r ∈ 𝔪, r ≠ 0 →
      (∀ q, q ⤳ p → Order.coheight q = 1 → 0 ≤ Y.ord (MvPolynomial.aeval ξ r) q) ∧
      ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧ 0 < Y.ord (MvPolynomial.aeval ξ r) q) :
    ∃ hpW : p ∈ W, (hW.primeIdealOf ⟨p, hpW⟩).asIdeal.comap φ = 𝔪 := by
  let Ω := MvPolynomial (Fin 2) k ⧸ 𝔪
  let : Field Ω := Ideal.Quotient.field 𝔪
  have : Module.Finite k Ω := finite_of_finite_type_of_isJacobsonRing k Ω
  have : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.of_finite k Ω
  set pt : Fin 2 → Ω := fun j => Ideal.Quotient.mk 𝔪 (MvPolynomial.X j)
  have hpt : ∀ r, MvPolynomial.aeval pt r = Ideal.Quotient.mk 𝔪 r := by
    intro r
    have : (MvPolynomial.aeval pt : MvPolynomial (Fin 2) k →ₐ[k] Ω) =
        Ideal.Quotient.mkₐ k 𝔪 := MvPolynomial.algHom_ext fun j => by simp [pt]; rfl
    exact congr($this r)
  have hreg := mem_range_stalk_of_forall_aeval κ hκ pt ξ p fun r hr => by
    have hr𝔪 : r ∈ 𝔪 := Ideal.Quotient.eq_zero_iff_mem.mp ((hpt r).symm.trans hr)
    by_cases hr0 : r = 0
    · intro w _ _; rw [hr0, map_zero, Scheme.ord_zero]; rfl
    · exact (hp r hr𝔪 hr0).1
  have hpW : p ∈ W := hWmem p (hreg 0) (hreg 1)
  refine ⟨hpW, ?_⟩
  have hle : 𝔪 ≤ (hW.primeIdealOf ⟨p, hpW⟩).asIdeal.comap φ := by
    intro r hr
    by_cases hr0 : r = 0
    · rw [hr0]; exact zero_mem _
    rw [mem_comap_primeIdealOf_iff hW hφK hpW]
    obtain ⟨h1, h2⟩ := hp r hr hr0
    exact (exists_mem_maximalIdeal_iff_ord p _).mp ⟨h1, Or.inr h2⟩
  exact (h𝔪.eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Algebra k Y.functionField] [Nonempty W]
  hφK in
/-- Only finitely many points of the chart have prime lying over a given maximal ideal. -/
private theorem finite_setOf_comap_eq (hφfin : φ.Finite) (𝔪 : Ideal (MvPolynomial (Fin 2) k)) :
    {p : Y | ∃ hpW : p ∈ W, (hW.primeIdealOf ⟨p, hpW⟩).asIdeal.comap φ = 𝔪}.Finite := by
  let : Algebra (MvPolynomial (Fin 2) k) Γ(Y, W) := φ.toAlgebra
  have : Module.Finite (MvPolynomial (Fin 2) k) Γ(Y, W) := hφfin
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := MvPolynomial (Fin 2) k)
    (S := Γ(Y, W)) 𝔪
  have hfin' : {P : PrimeSpectrum Γ(Y, W) | P.asIdeal ∈ 𝔪.primesOver Γ(Y, W)}.Finite :=
    hfin.preimage (fun P _ Q _ h => PrimeSpectrum.ext h)
  refine (hfin'.image hW.fromSpec.base).subset ?_
  rintro p ⟨hpW, hp𝔪⟩
  refine ⟨hW.primeIdealOf ⟨p, hpW⟩, ⟨inferInstance, ⟨hp𝔪.symm⟩⟩,
    hW.fromSpec_primeIdealOf ⟨p, hpW⟩⟩

end Chart

section Cover

open HomogeneousLocalization

/-- On `D₊(s) ∩ D₊(t)` for `s, t` of degree one, the germs of the sections `a / t`, `a / s` and
`s / t` satisfy `a / t = (a / s) (s / t)`. -/
private theorem germ_awayToSection_eq_mul {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {s t a : A} (hs : s ∈ 𝒜 1)
    (ht : t ∈ 𝒜 1) (hs' : s ∈ 𝒜 (1 • 1)) (ha : a ∈ 𝒜 (1 • 1)) (y : AlgebraicGeometry.Proj 𝒜)
    (hys : y ∈ Proj.basicOpen 𝒜 s) (hyt : y ∈ Proj.basicOpen 𝒜 t) :
    (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 t) y hyt
        (Proj.awayToSection 𝒜 t (Away.mk 𝒜 ht 1 a ha)) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 s) y hys
          (Proj.awayToSection 𝒜 s (Away.mk 𝒜 hs 1 a ha)) *
        (AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 t) y hyt
          (Proj.awayToSection 𝒜 t (Away.mk 𝒜 ht 1 s hs')) := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  apply (Proj.stalkIso' 𝒜 y).injective
  apply HomogeneousLocalization.val_injective
  erw [map_mul]
  rw [val_mul, val_stalkIso'_germ_awayToSection, val_stalkIso'_germ_awayToSection,
    val_stalkIso'_germ_awayToSection, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

section XMem

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {m : ℕ}

private theorem X_mem_one (i : Fin (m + 1)) :
    (X i : MvPolynomial (Fin (m + 1)) R) ∈ homogeneousSubmodule (Fin (m + 1)) R 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R i)

private theorem X_mem_one' (i : Fin (m + 1)) :
    (X i : MvPolynomial (Fin (m + 1)) R) ∈ homogeneousSubmodule (Fin (m + 1)) R (1 • 1) := by
  simpa using X_mem_one (R := R) i

end XMem

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The generic point lies in the chart `D₊(X₀)`.** If `φ : X ⟶ Proj R[X₀, …, Xₙ]` pulls
`X₀ / Xⱼ` back to `x₀ / xⱼ` on every chart `φ⁻¹ D₊(Xⱼ)` that is nonempty, and `x₀ ≠ 0`, then
`φ⁻¹ D₊(X₀)` is nonempty. -/
private theorem nonempty_preimage_basicOpen_zero {R : Type u} [CommRing R] {Z : Scheme.{u}}
    [IsIntegral Z] {n : ℕ} (φ : Z ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) R))
    (x : Fin (n + 1) → Z.functionField) (hx : ∀ j, x j ≠ 0)
    (hφ : ∀ (j : Fin (n + 1)) [Nonempty (φ ⁻¹ᵁ Proj.basicOpen _ (X j))],
      Z.germToFunctionField _ (φ.app _ (Proj.awayToSection _ (X j)
        (Away.mk (homogeneousSubmodule (Fin (n + 1)) R) (X_mem_one j) 1 (X 0) (X_mem_one' 0)))) =
        x 0 / x j) :
    ((φ ⁻¹ᵁ Proj.basicOpen _ (X 0) : Z.Opens) : Set Z).Nonempty := by
  set 𝒜 := homogeneousSubmodule (Fin (n + 1)) R
  obtain ⟨j, hj⟩ := exists_X_notMem (φ (genericPoint Z))
  have hηj : genericPoint Z ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) := hj
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X j)) := ⟨⟨_, hηj⟩⟩
  have h := hφ j
  change Z.presheaf.germ _ (genericPoint Z) hηj _ = _ at h
  rw [← Scheme.Hom.germ_stalkMap_apply φ _ _ hηj] at h
  have hu : IsUnit (φ.stalkMap (genericPoint Z)
      ((AlgebraicGeometry.Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (X j)) _ hj
        (Proj.awayToSection 𝒜 (X j) (Away.mk 𝒜 (X_mem_one j) 1 (X 0) (X_mem_one' 0))))) := by
    rw [h]
    exact (div_ne_zero (hx 0) (hx j)).isUnit
  have hu' := isUnit_of_map_unit (φ.stalkMap (genericPoint Z)).hom _ hu
  exact ⟨genericPoint Z,
    (isUnit_germ_awayToSection_iff 𝒜 (X_mem_one j) 1 _ (X_mem_one' 0) _ hj).mp hu'⟩

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Every point lies in a chart of `φ_B`.** If `φ : Y ⟶ Proj R[X₀, …, Xₘ]` pulls `Xᵢ / X₀`
back to `fᵢ / f₀` at the generic point, every point `p` of `Y` has an index `j` with all
`fᵢ / fⱼ` regular at `p`. -/
private theorem exists_forall_div_mem_range {R : Type u} [CommRing R] {Y : Scheme.{u}}
    [IsIntegral Y] {m : ℕ} (φ : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (m + 1)) R))
    (fy : Fin (m + 1) → Y.functionField) (hfy : ∀ i, fy i ≠ 0)
    (hη0 : genericPoint Y ∈ φ ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) R) (X 0))
    (hφ : ∀ i : Fin (m + 1), Y.presheaf.germ _ (genericPoint Y) hη0 (φ.app _
      (Proj.awayToSection _ (X 0)
        (Away.mk (homogeneousSubmodule (Fin (m + 1)) R) (X_mem_one 0) 1 (X i) (X_mem_one' i)))) =
        fy i / fy 0)
    (p : Y) :
    ∃ j, ∀ i, fy i / fy j ∈ Set.range (algebraMap (Y.presheaf.stalk p) Y.functionField) := by
  set 𝒜 := homogeneousSubmodule (Fin (m + 1)) R
  obtain ⟨j, hj⟩ := exists_X_notMem (φ p)
  have hpj : p ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) := hj
  have hηj : genericPoint Y ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) :=
    genericPoint_mem_of_nonempty _ ⟨p, hpj⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0)) := ⟨⟨_, hη0⟩⟩
  have : Nonempty (φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X j)) := ⟨⟨_, hηj⟩⟩
  set e : Fin (m + 1) → Y.functionField := fun i => Y.germToFunctionField _
    (φ.app _ (Proj.awayToSection 𝒜 (X j) (Away.mk 𝒜 (X_mem_one j) 1 (X i) (X_mem_one' i))))
    with he
  have hy0 : φ (genericPoint Y) ∈ Proj.basicOpen 𝒜 (X 0) := hη0
  have hyj : φ (genericPoint Y) ∈ Proj.basicOpen 𝒜 (X j) := hηj
  have hstalk : ∀ (l : Fin (m + 1)) (i : Fin (m + 1)) (hy : φ (genericPoint Y) ∈
      Proj.basicOpen 𝒜 (X l)) (hη : genericPoint Y ∈ φ ⁻¹ᵁ Proj.basicOpen 𝒜 (X l)),
      φ.stalkMap (genericPoint Y) ((AlgebraicGeometry.Proj 𝒜).presheaf.germ _ _ hy
        (Proj.awayToSection 𝒜 (X l) (Away.mk 𝒜 (X_mem_one l) 1 (X i) (X_mem_one' i)))) =
      Y.presheaf.germ _ (genericPoint Y) hη
        (φ.app _ (Proj.awayToSection 𝒜 (X l) (Away.mk 𝒜 (X_mem_one l) 1 (X i) (X_mem_one' i)))) :=
    fun l i hy hη => Scheme.Hom.germ_stalkMap_apply φ _ _ hy _
  have h1 : ∀ i, e i = fy i / fy 0 * e 0 := by
    intro i
    have := congrArg (φ.stalkMap (genericPoint Y)) (germ_awayToSection_eq_mul 𝒜 (X_mem_one 0)
      (X_mem_one j) (X_mem_one' 0) (X_mem_one' i) _ hy0 hyj)
    rw [map_mul, hstalk j i hyj hηj, hstalk 0 i hy0 hη0, hstalk j 0 hyj hηj] at this
    calc e i = Y.presheaf.germ _ _ hηj (φ.app _ (Proj.awayToSection 𝒜 (X j)
          (Away.mk 𝒜 (X_mem_one j) 1 (X i) (X_mem_one' i)))) := rfl
      _ = _ := this
      _ = fy i / fy 0 * e 0 := by rw [← hφ i]
  have h2 : e 0 * (fy j / fy 0) = 1 := by
    have := congrArg (φ.stalkMap (genericPoint Y)) (germ_mul_germ_awayToSection 𝒜 (X_mem_one j)
      (X_mem_one 0) (X_mem_one' j) (X_mem_one' 0) _ hyj hy0)
    rw [map_mul, map_one, hstalk j 0 hyj hηj, hstalk 0 j hy0 hη0] at this
    rw [← hφ j]
    exact this
  have he0 : e 0 = fy 0 / fy j := by
    field_simp [hfy j, hfy 0] at h2 ⊢
    linear_combination h2
  refine ⟨j, fun i => ⟨(Y.presheaf.germ _ p hpj) (φ.app _ (Proj.awayToSection 𝒜 (X j)
    (Away.mk 𝒜 (X_mem_one j) 1 (X i) (X_mem_one' i)))), ?_⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  change e i = _
  rw [h1 i, he0]
  field_simp [hfy j, hfy 0]

end Cover

/-- **Sections not vanishing at a point.** Let `fⱼ` be a basis of sections of `𝒪(D)` with no
common zero along any prime divisor, and let all `fᵢ / fⱼ` be regular at `p`. The rational
vectors `c` for which the section `∑ cᵢ fᵢ` vanishes along a prime divisor through `p` lie in a
proper subspace. -/
private theorem exists_submodule_forall_ord_add_eq_zero {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Algebra k Y.functionField]
    [CharZero Y.functionField] [CharZero k]
    (κ : ∀ y : Y, k →+* Y.presheaf.stalk y)
    (hκ : ∀ y, (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (κ y) =
      algebraMap k Y.functionField)
    (D : Y → ℤ) {m : ℕ} (fy : Fin (m + 1) → Y.functionField) (hfy : ∀ i, fy i ≠ 0)
    (hD : ∀ i q, 0 ≤ Y.ord (fy i) q + D q)
    (hbpf : ∀ q, Order.coheight q = 1 → ∃ i, Y.ord (fy i) q + D q = 0)
    (p : Y) (j : Fin (m + 1))
    (hj : ∀ i, fy i / fy j ∈ Set.range (algebraMap (Y.presheaf.stalk p) Y.functionField)) :
    ∃ S : Submodule ℚ (Fin (m + 1) → ℚ), S ≠ ⊤ ∧ ∀ c ∉ S,
      (∑ i, (c i : Y.functionField) * fy i) ≠ 0 ∧
      ∀ q, q ⤳ p → Order.coheight q = 1 →
        Y.ord (∑ i, (c i : Y.functionField) * fy i) q + D q = 0 := by
  have hQ : ∀ q : ℚ, (q : Y.functionField) ∈
      Set.range (algebraMap (Y.presheaf.stalk p) Y.functionField) := fun q =>
    ⟨κ p (q : k), by rw [← RingHom.comp_apply, hκ, map_ratCast]⟩
  have hjj : fy j / fy j = 1 := div_self (hfy j)
  obtain ⟨S, hS, hSc⟩ := exists_submodule_of_isLocalRing (Y.presheaf.stalk p) Y.functionField
    (IsFractionRing.injective _ _) (fun i => fy i / fy j) hj hQ hjj
  refine ⟨S, hS, fun c hc => ?_⟩
  obtain ⟨t, htu, ht⟩ := hSc c hc
  have hsum : ∑ i, (c i : Y.functionField) * (fy i / fy j) =
      (∑ i, (c i : Y.functionField) * fy i) / fy j := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at ht
  have ht0 : algebraMap (Y.presheaf.stalk p) Y.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr htu.ne_zero
  have hℓ0 : (∑ i, (c i : Y.functionField) * fy i) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at ht
    exact ht0 ht
  refine ⟨hℓ0, fun q hqp hq1 => ?_⟩
  have hu : Y.ord ((∑ i, (c i : Y.functionField) * fy i) / fy j) q = 0 := by
    rw [← ht, ← algebraMap_stalkSpecializes hqp]
    exact ord_algebraMap_of_isUnit hq1 (htu.map _)
  rw [ord_div hℓ0 (hfy j)] at hu
  obtain ⟨i₀, hi₀⟩ := hbpf q hq1
  have hreg := mem_range_stalk_of_specializes hqp (hj i₀)
  have hnn := (ord_nonneg_iff hq1 (div_ne_zero (hfy i₀) (hfy j))).mpr hreg
  rw [ord_div (hfy i₀) (hfy j)] at hnn
  have := hD j q
  omega

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **`C × C` does not embed in `ℙ²`.** If `Y = C ×_k C` for a curve `C` with a closed point
`σ₀`, a closed immersion `Y ⟶ ℙᵐ_k` forces `m ≥ 3`: the fibres of `pr₁` over two distinct
closed points are disjoint curves, and two curves in `ℙ²` meet. -/
private theorem three_le_of_isClosedImmersion {k : Type u} [Field k] {C Y : Scheme.{u}}
    [IsIntegral C]
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] [LocallyOfFiniteType f]
    {pr₁ pr₂ : Y ⟶ C} (hY : IsPullback pr₁ pr₂ f f) {σ₀ : C} (hσ₀ : IsClosed ({σ₀} : Set C))
    (hση : σ₀ ≠ genericPoint C) {m : ℕ}
    (φ : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion φ] : 3 ≤ m := by
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace f
  have hUo : IsOpen ({σ₀}ᶜ : Set C) := hσ₀.isOpen_compl
  obtain ⟨Q, hQU, hQc⟩ := nonempty_inter_closedPoints (Z := ({σ₀}ᶜ : Set C))
    ⟨genericPoint C, fun h => hση (Set.mem_singleton_iff.mp h).symm⟩ hUo.isLocallyClosed
  have hQσ : Q ≠ σ₀ := hQU
  have hQcl : IsClosed ({Q} : Set C) := hQc
  have hpt : ∀ c : C, ∃ y : Y, pr₁ y = c ∧ pr₂ y = genericPoint C := by
    intro c
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) c
      (genericPoint C) (Subsingleton.elim _ _)
    refine ⟨hY.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hY.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, hY.isoPullback_inv_snd, hz2]
  obtain ⟨y₁, hy₁, hy₁'⟩ := hpt σ₀
  obtain ⟨y₂, hy₂, hy₂'⟩ := hpt Q
  have hcl : ∀ (y : Y) (c : C), IsClosed ({c} : Set C) → pr₁ y = c →
      closure ({y} : Set Y) ⊆ pr₁.base ⁻¹' {c} := fun y c hc hyc =>
    closure_minimal (by simpa using hyc) (hc.preimage pr₁.base.hom.continuous)
  have hdisj : Disjoint (closure ({y₁} : Set Y)) (closure ({y₂} : Set Y)) := by
    refine Set.disjoint_left.mpr fun u hu1 hu2 => hQσ ?_
    have h1 := hcl y₁ σ₀ hσ₀ hy₁ hu1
    have h2 := hcl y₂ Q hQcl hy₂ hu2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    rw [← h1, ← h2]
  have : IsProper pr₂ := MorphismProperty.of_isPullback (P := @IsProper) hY inferInstance
  have hη : ¬ IsClosed ({genericPoint C} : Set C) := by
    intro h
    have := (genericPoint_spec C).specializes (Set.mem_univ σ₀)
    exact hση (this.mem_closed h rfl)
  have hnc : ∀ y : Y, pr₂ y = genericPoint C → ∃ z ∈ closure ({y} : Set Y), z ≠ y := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hcly : closure ({y} : Set Y) = {y} :=
      Set.Subset.antisymm (fun z hz => hcon z hz) subset_closure
    have : IsClosed ({y} : Set Y) := hcly ▸ isClosed_closure
    apply hη
    have := pr₂.isClosedMap _ this
    rwa [Set.image_singleton, hy] at this
  obtain ⟨z₁, hz₁, hz₁y⟩ := hnc y₁ hy₁'
  obtain ⟨z₂, hz₂, hz₂y⟩ := hnc y₂ hy₂'
  set 𝒜 := homogeneousSubmodule (Fin (m + 1)) k
  have hemb : Topology.IsClosedEmbedding φ.base := φ.isClosedEmbedding
  have hclim : ∀ y : Y, closure ({φ y} : Set (AlgebraicGeometry.Proj 𝒜)) =
      φ.base '' closure ({y} : Set Y) := by
    intro y
    rw [← Set.image_singleton, hemb.closure_image_eq]
  have hle : ∀ (y z : Y), z ∈ closure ({y} : Set Y) →
      (show ProjectiveSpectrum 𝒜 from φ y) ≤ (show ProjectiveSpectrum 𝒜 from φ z) := by
    intro y z hz
    rw [ProjectiveSpectrum.le_iff_mem_closure]
    change φ z ∈ closure ({φ y} : Set (AlgebraicGeometry.Proj 𝒜))
    rw [hclim]
    exact ⟨z, hz, rfl⟩
  have hmem : ∀ (y : Y) (w : ProjectiveSpectrum 𝒜),
      (show ProjectiveSpectrum 𝒜 from φ y) ≤ w → ∃ u ∈ closure ({y} : Set Y), φ u = w := by
    intro y w hw
    rw [ProjectiveSpectrum.le_iff_mem_closure] at hw
    change w ∈ closure ({φ y} : Set (AlgebraicGeometry.Proj 𝒜)) at hw
    rw [hclim] at hw
    exact hw
  have hlt : ∀ (y z : Y), z ∈ closure ({y} : Set Y) → z ≠ y →
      (show ProjectiveSpectrum 𝒜 from φ y) < (show ProjectiveSpectrum 𝒜 from φ z) := by
    intro y z hz hzy
    exact lt_of_le_of_ne (hle y z hz) fun h => hzy (hemb.injective h).symm
  have hdisj' : ∀ w : ProjectiveSpectrum 𝒜,
      ¬ ((show ProjectiveSpectrum 𝒜 from φ y₁) ≤ w ∧
        (show ProjectiveSpectrum 𝒜 from φ y₂) ≤ w) := by
    rintro w ⟨h1, h2⟩
    obtain ⟨u₁, hu₁, rfl⟩ := hmem y₁ w h1
    obtain ⟨u₂, hu₂, hu⟩ := hmem y₂ _ h2
    rw [hemb.injective hu] at hu₂
    exact Set.disjoint_left.mp hdisj hu₁ hu₂
  have hbot : ∀ (y y' : Y), Disjoint (closure ({y} : Set Y)) (closure ({y'} : Set Y)) →
      (show ProjectiveSpectrum 𝒜 from φ y).asHomogeneousIdeal.toIdeal ≠ ⊥ := by
    intro y y' hd h0
    have hle' : (show ProjectiveSpectrum 𝒜 from φ y) ≤ (show ProjectiveSpectrum 𝒜 from φ y') := by
      change (show ProjectiveSpectrum 𝒜 from φ y).asHomogeneousIdeal.toIdeal ≤ _
      rw [h0]; exact bot_le
    obtain ⟨u, hu, hu'⟩ := hmem y _ hle'
    rw [hemb.injective hu'] at hu
    exact Set.disjoint_left.mp hd hu (subset_closure rfl)
  exact three_le_of_disjoint _ _ _ _ (hlt y₁ z₁ hz₁ hz₁y) (hlt y₂ z₂ hz₂ hz₂y)
    (hbot y₁ y₂ hdisj) (hbot y₂ y₁ hdisj.symm) hdisj'

/-- A closed point of a curve is not its generic point. -/
private theorem ne_genericPoint_of_isClosed {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] {c : C} (hc : IsClosed ({c} : Set C)) :
    c ≠ genericPoint C := by
  intro h
  have hcl' : IsClosed ({genericPoint C} : Set C) := h ▸ hc
  have hsub : Subsingleton C := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({genericPoint C} : Set C) :=
      ((genericPoint_spec C).specializes (Set.mem_univ a)).mem_closed hcl' rfl
    have hb : b ∈ ({genericPoint C} : Set C) :=
      ((genericPoint_spec C).specializes (Set.mem_univ b)).mem_closed hcl' rfl
    rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  have h0 := topologicalKrullDim_zero_of_discreteTopology C
  rw [IsCurve.topologicalKrullDim_eq_one (f := f)] at h0
  exact absurd h0 (by decide)

/-- A rational vector whose entries are integers. -/
private abbrev IsIntVec {n : ℕ} (c : Fin n → ℚ) : Prop := ∃ z : Fin n → ℤ, c = fun j => (z j : ℚ)

/-- **An integral vector avoiding a proper subspace and finitely many proper subspaces.** -/
private theorem exists_intVec_notMem_of_finite {n : ℕ} {𝒮 : Set (Submodule ℚ (Fin n → ℚ))}
    (h𝒮 : 𝒮.Finite) (hprop : ∀ S ∈ 𝒮, S ≠ ⊤) (W : Submodule ℚ (Fin n → ℚ)) (hW : W ≠ ⊤) :
    ∃ c, IsIntVec c ∧ c ∉ W ∧ ∀ S ∈ 𝒮, c ∉ S := by
  obtain ⟨c, hcW, hcS⟩ := exists_notMem_of_finite h𝒮 hprop W hW
  obtain ⟨d, z, hd, hz⟩ := exists_int_smul c
  have hc' : (fun j => (z j : ℚ)) = d • c := by
    funext j; rw [hz j]; rfl
  have hnot : ∀ S : Submodule ℚ (Fin n → ℚ), c ∉ S → (fun j => (z j : ℚ)) ∉ S := by
    intro S hcS' hmem
    apply hcS'
    have := S.smul_mem d⁻¹ hmem
    rwa [hc', smul_smul, inv_mul_cancel₀ hd, one_smul] at this
  exact ⟨_, ⟨z, rfl⟩, hnot W hcW, fun S hS => hnot S (hcS S hS)⟩

/-- **Extending an independent family of integral vectors while avoiding finitely many proper
subspaces.** -/
private theorem exists_linearIndependent_extend_int {N : ℕ}
    {𝒮 : Set (Submodule ℚ (Fin N → ℚ))} (h𝒮 : 𝒮.Finite) (hprop : ∀ S ∈ 𝒮, S ≠ ⊤) {r : ℕ}
    (v : Fin r → Fin N → ℚ) (hv : LinearIndependent ℚ v) (hvint : ∀ i, IsIntVec (v i)) :
    ∀ n, r ≤ n → n ≤ N →
    ∃ w : Fin n → Fin N → ℚ, LinearIndependent ℚ w ∧ (∀ i, IsIntVec (w i)) ∧
      (∀ (h : r ≤ n) (i : Fin r), w (Fin.castLE h i) = v i) ∧
      ∀ i : Fin n, r ≤ i.val → ∀ S ∈ 𝒮, w i ∉ S := by
  intro n hrn
  induction n, hrn using Nat.le_induction with
  | base =>
    intro _
    refine ⟨v, hv, hvint, fun h i => by simp, fun i hi => absurd i.2 (by omega)⟩
  | succ n hrn ih =>
    intro hn
    obtain ⟨w, hw, hwint, hwv, hwS⟩ := ih (by omega)
    obtain ⟨x, hxint, hx, hxS⟩ := exists_intVec_notMem_of_finite h𝒮 hprop _
      (span_range_ne_top w (by simpa using hn))
    refine ⟨Fin.snoc w x, linearIndependent_finSnoc.mpr ⟨hw, hx⟩,
      Fin.lastCases (by simpa using hxint) fun i => by simpa using hwint i, fun h i => ?_,
      Fin.lastCases (fun _ => by simpa using hxS) fun i hi => by simpa using hwS i hi⟩
    have : (Fin.castLE h i : Fin (n + 1)) = Fin.castSucc (Fin.castLE hrn i) := rfl
    rw [this, Fin.snoc_castSucc, hwv]

/-- An integral matrix whose rows are linearly independent over `ℚ` is invertible over any field of
characteristic zero. -/
private theorem isUnit_map_intCast_of_linearIndependent {n : ℕ} (g : Matrix (Fin n) (Fin n) ℤ)
    (hg : LinearIndependent ℚ fun i j => (g i j : ℚ)) (k : Type*) [Field k] [CharZero k] :
    IsUnit (g.map (Int.cast : ℤ → k)) := by
  have hrow : LinearIndependent ℚ (g.map (Int.cast : ℤ → ℚ)).row := hg
  have hdetQ : (g.map (Int.cast : ℤ → ℚ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero
  have hdetZ : g.det ≠ 0 := by
    intro h0
    apply hdetQ
    rw [show (g.map (Int.cast : ℤ → ℚ)) = (Int.castRingHom ℚ).mapMatrix g from rfl,
      ← RingHom.map_det, h0, map_zero]
  rw [Matrix.isUnit_iff_isUnit_det]
  refine Ne.isUnit ?_
  rw [show (g.map (Int.cast : ℤ → k)) = (Int.castRingHom k).mapMatrix g from rfl, ← RingHom.map_det]
  simpa using hdetZ

section Charts

open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

/-- The sections of `Spec 𝒪_{Y,x} ⟶ Y` over an open `W` are the germs at `x`, restricted. -/
private theorem fromSpecStalk_appLE_apply {Y : Scheme.{u}} (x : Y) {U : Y.Opens} (hx : x ∈ U)
    {W : (Spec (Y.presheaf.stalk x)).Opens} (e : W ≤ Y.fromSpecStalk x ⁻¹ᵁ U) (t : Γ(Y, U)) :
    (Y.fromSpecStalk x).appLE U W e t = resTop W ((Scheme.ΓSpecIso _).inv
      (Y.presheaf.germ U x hx t)) := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [CommRingCat.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The affine coordinates of a morphism to `ℙʳ` at the generic point.** If `φ : Y ⟶ ℙʳ_S`
restricts at the generic point to the point `(s₀ : … : s_r)` with `s₀ ≠ 0`, then the generic
point lies in `φ⁻¹ D₊(T₀)`, and the pull-back of `T_ν / T₀` has germ `s_ν / s₀` there. -/
private theorem exists_germ_app_ratio_eq_div {Y S : Scheme.{u}} [IsIntegral Y] {r : ℕ}
    (φ : Y ⟶ projectiveSpaceOver r S) (s : Fin (r + 1) → Y.functionField) (hs0 : s 0 ≠ 0)
    (hspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) = ⊤)
    (σ : Spec (.of Y.functionField) ⟶ S)
    (hφ : Y.fromSpecStalk (genericPoint Y) ≫ φ =
      toProjectiveSpaceOver (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i)) hspan σ) :
    ∃ h : genericPoint Y ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse r S ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)), ∀ ν : Fin (r + 1),
      Y.presheaf.germ _ (genericPoint Y) h (φ.app _
        ((projectiveSpaceOver.toIntegralAtUniverse r S).app _
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X _ 0) 1
              (MvPolynomial.X ν) (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
        s ν / s 0 := by
  set j := Y.fromSpecStalk (genericPoint Y) with hj
  set sK : Fin (r + 1) → Γ(Spec (.of Y.functionField), ⊤) :=
    fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (s i) with hsK
  set B := Proj.basicOpen (coordGrading.{u} r) (MvPolynomial.X 0) with hBdef
  have hX0 : (MvPolynomial.X 0 : coordRing.{u} r) ∈ coordGrading.{u} r 1 :=
    X_mem_coordGrading_one 0
  set ψ' := φ ≫ projectiveSpaceOver.toIntegralAtUniverse r S with hψ'
  have hg : j ≫ ψ' = toProjectiveSpaceAtUniverse sK hspan := by
    rw [hψ', ← Category.assoc, hφ, toProjectiveSpaceOver_snd]
  have hunit : IsUnit (sK 0) := (Ne.isUnit hs0).map _
  have hpre : toProjectiveSpaceAtUniverse sK hspan ⁻¹ᵁ B = ⊤ := by
    rw [hBdef, preimage_basicOpen]
    exact Scheme.basicOpen_of_isUnit _ hunit
  have hpre' : j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) = ⊤ := by
    change (j ≫ ψ') ⁻¹ᵁ B = ⊤
    rw [hg, hpre]
  have hmem : genericPoint Y ∈ ψ' ⁻¹ᵁ B := by
    have h2 : IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)) ∈ j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) := by
      rw [hpre']; trivial
    have h3 : j (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
      Scheme.fromSpecStalk_closedPoint
    rw [← h3]
    exact h2
  refine ⟨hmem, fun ν => ?_⟩
  set W := (Spec (.of Y.functionField)).basicOpen (sectionsHom sK (MvPolynomial.X 0)) with hW
  have hWtop : W = ⊤ := by
    rw [hW, sectionsHom_X]
    exact Scheme.basicOpen_of_isUnit _ hunit
  have : Nonempty W := by
    rw [hWtop]
    exact ⟨⟨IsLocalRing.closedPoint Y.functionField, trivial⟩⟩
  have hinjF : Function.Injective (fun z : Y.functionField =>
      resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv z)) :=
    (map_injective_of_isIntegral _ (homOfLE le_top)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Y.functionField)).inv).1
  have hle : W ≤ j ⁻¹ᵁ (ψ' ⁻¹ᵁ B) := by
    rw [hpre']
    exact le_top
  have hXν : (MvPolynomial.X ν : coordRing.{u} r) ∈ coordGrading.{u} r (1 • 1) := by
    rw [smul_eq_mul, mul_one]; exact X_mem_coordGrading_one ν
  set a := HomogeneousLocalization.Away.mk (coordGrading.{u} r) hX0 1 (MvPolynomial.X ν) hXν
    with ha
  apply hinjF
  dsimp only
  refine Eq.trans (fromSpecStalk_appLE_apply (genericPoint Y) hmem hle
    (ψ'.app B (Proj.awayToSection (coordGrading.{u} r) (MvPolynomial.X 0) a))).symm ?_
  have hc : ∀ (g g' : Spec (.of Y.functionField) ⟶ projectiveSpaceAtUniverse.{u} r) (h : g = g')
      (e : W ≤ g ⁻¹ᵁ B), g.appLE B W e = g'.appLE B W (h ▸ e) := by
    intro g g' h e
    subst h
    rfl
  have h2 : ψ'.app B ≫ j.appLE _ W hle =
      (toProjectiveSpaceAtUniverse sK hspan).appLE B W (hg ▸ hle) :=
    (Scheme.Hom.comp_appLE j ψ' B W hle).symm.trans (hc _ _ hg hle)
  have h3 := Stacks.LinearSystemScheme.awayToSection_comp_appLE_fromOfGlobalSections
    (𝒜 := coordGrading.{u} r) (sectionsHom sK) (map_irrelevant_eq_top sK hspan) one_pos hX0
  have h4 : (j.appLE _ W hle) (ψ'.app B (Proj.awayToSection (coordGrading.{u} r)
      (MvPolynomial.X 0) a)) = Stacks.ProjGlobalSectionsAppTop.projAwayHom (coordGrading.{u} r)
        (sectionsHom sK) a := by
    have h5 := congrArg (fun F => F.hom a) h3
    simp only [CommRingCat.hom_ofHom] at h5
    rw [← h5]
    change (ψ'.app B ≫ j.appLE _ W hle) _ = _
    rw [h2]
    rfl
  rw [h4, Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk, pow_one]
  have hu : resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
      resTop W (sectionsHom sK (MvPolynomial.X 0)) = 1 :=
    (isUnit_resTop_basicOpen (sectionsHom sK (MvPolynomial.X 0))).val_inv_mul
  have hv : resTop W (sK 0) *
      resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹) = 1 := by
    rw [← map_mul, hsK, ← map_mul, mul_inv_cancel₀ hs0, map_one, map_one]
  have e : ∀ i, resTop W (sectionsHom sK (MvPolynomial.X i)) = resTop W (sK i) := fun i => by
    rw [sectionsHom_X]
  change resTop W (sectionsHom sK (MvPolynomial.X ν)) *
    resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) = _
  rw [e ν, div_eq_mul_inv, map_mul, map_mul]
  congr 1
  calc resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0))
      = resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
          (resTop W (sK 0) * resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹)) := by
        rw [hv, mul_one]
    _ = (resTopBasicOpenInv (sectionsHom sK (MvPolynomial.X 0)) *
          resTop W (sectionsHom sK (MvPolynomial.X 0))) *
          resTop W ((Scheme.ΓSpecIso (.of Y.functionField)).inv (s 0)⁻¹) := by
        rw [e 0, mul_assoc]
    _ = _ := by rw [hu, one_mul]

end Charts

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The morphism of a spanning family of sections, read in the polynomial model over `k`.**
For `b : X ⟶ Spec k` and global sections `r₀, …, rₘ` of `𝒪_X` spanning the unit ideal, the
morphism `X ⟶ ℙᵐ_k` they give is the morphism `X ⟶ Proj k[T₀, …, Tₘ]` of the evaluation
`Tᵢ ↦ rᵢ` followed by the comparison of the two models of `ℙᵐ_k`. -/
private theorem toProjectiveSpaceOver_eq_fromOfGlobalSections_comp {k : Type u} [CommRing k]
    {X : Scheme.{u}} {m : ℕ} (b : X ⟶ Spec (.of k)) (r : Fin (m + 1) → Γ(X, ⊤))
    (hr : Ideal.span (Set.range r) = ⊤) :
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver r hr b =
      Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k)
          (MvPolynomial.eval₂Hom (Stacks.ProjectiveSpaceChartRatio.baseRingHom b) r)
          (Stacks.ProjectiveSpaceChartRatio.map_irrelevant_eval₂Hom_eq_top _ r hr) ≫
        Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m := by
  refine pullback.hom_ext ?_ ?_
  · rw [Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst, Category.assoc,
      Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst,
      Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_comp_projToSpecCoeff _ r hr,
      Stacks.ProjectiveSpaceChartRatio.toSpecΓ_SpecMap_baseRingHom]
  · rw [Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd, Category.assoc,
      Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_snd,
      Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_comp_coordinateProjMap _ r hr]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **A linear automorphism of `ℙᵐ_k` pulls `𝒪(1)` back to `𝒪(1)`.** The automorphism
`Tᵢ ↦ ∑ⱼ gᵢⱼ Tⱼ`, read on `ℙᵐ_k` through the comparison `projCompare` with `Proj k[T₀, …, Tₘ]`,
pulls the hyperplane sheaf (the pull-back of the integral `𝒪(1)`) back to itself: on the
polynomial model the hyperplane sheaf is `𝒪(1)` (`hasPolyTwistTransport`), and a surjective graded
endomorphism of a ring generated in degree one pulls `𝒪(1)` back to `𝒪(1)` (`pullbackTwistIso`). -/
private theorem nonempty_pullback_projSubst_twistingSheaf_iso {k : Type u} [Field k] {m : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin (m + 1)) k) :
    Nonempty ((Scheme.Modules.pullback
        (inv (Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m) ≫
          projSubst (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) _ (Units.inv_mul g) ≫
          Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m)).obj
        ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)) ≅
      (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)) := by
  set c := Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m with hc
  have hct : c ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)) =
      Stacks.ProjectiveCohomology.projModelMap m (Stacks.ProjectiveCohomology.fromULiftInt k) := by
    refine (Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_snd k m).trans ?_
    rw [Stacks.AlgebraicGeometry.ProjBaseChange.coordinateProjMap_eq_projMap]
    exact proj_map_congr (GradedRingHom.ext fun _ => rfl) _ _
  obtain ⟨F₀⟩ := Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport k m 1
  have F := (Scheme.Modules.pullbackComp c
      (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).app _ ≪≫
    (Scheme.Modules.pullbackCongr hct).app _ ≪≫ F₀
  have hsurj : Function.Surjective
      (linSubstHom (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) : MvPolynomial (Fin (m + 1)) k →
        MvPolynomial (Fin (m + 1)) k) := fun x =>
    ⟨linSubst (↑g⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) x, by
      rw [linSubstHom_apply, ← AlgHom.comp_apply, linSubst_comp, Units.inv_mul, linSubst_one]
      rfl⟩
  have G := Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
    (linSubstHom (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
    (irrelevant_le_map_linSubstHom _ _ (Units.inv_mul g)) hsurj
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (m + 1)) k) 1
  exact ⟨((Scheme.Modules.pullbackComp (inv c)
      (projSubst (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) _ (Units.inv_mul g) ≫ c)).app _).symm ≪≫
    (Scheme.Modules.pullback (inv c)).mapIso
      (((Scheme.Modules.pullbackComp
        (projSubst (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) _ (Units.inv_mul g)) c).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso F ≪≫ G ≪≫ F.symm) ≪≫
    (Scheme.Modules.pullbackComp (inv c) c).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id c)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **A linear change of the coordinates of an embedding.** Let `φB : Y ⟶ ℙᵐ_k` be a closed
immersion over `k` which at the generic point of the integral scheme `Y` is the point
`[y₀ : … : yₘ]`, and let `g ∈ GL_{m+1}(k)` with `y'₀ ≠ 0`, where `y'ᵢ = ∑ⱼ gᵢⱼ yⱼ`. Then `φB`
followed by the automorphism `Tᵢ ↦ ∑ⱼ gᵢⱼ Tⱼ` of `ℙᵐ_k` is a closed immersion over `k` which at
the generic point is `[y'₀ : … : y'ₘ]`. -/
private theorem exists_isClosedImmersion_comp_eq_toProjectiveSpaceOver {k : Type u} [Field k]
    {C Y : Scheme.{u}} [IsIntegral Y] (f : C ⟶ Spec (.of k)) (pr₁ : Y ⟶ C)
    [Algebra k Y.functionField]
    (hkY : ∀ c : k, algebraMap k Y.functionField c =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    {m : ℕ} (fy : Fin (m + 1) → Y.functionField) (hfy0 : fy 0 ≠ 0)
    (φB : Y ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pr₁ ≫ f)
    [IsClosedImmersion φB]
    (hφBy : Y.fromSpecStalk (genericPoint Y) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit hfy0).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
        (Y.fromSpecStalk _ ≫ pr₁ ≫ f))
    (g : Matrix.GeneralLinearGroup (Fin (m + 1)) k)
    (hg0 : (∑ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) 0 j • fy j) ≠ 0) :
    ∃ φB' : Y ⟶ projectiveSpaceOver m (Spec (.of k)),
      IsClosedImmersion φB' ∧
      φB' ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pr₁ ≫ f ∧
      Nonempty ((Scheme.Modules.pullback φB').obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)) ≅
        (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1))) ∧
      ∃ hspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv
          (∑ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j • fy j)) = ⊤,
        Y.fromSpecStalk (genericPoint Y) ≫ φB' =
          Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
            (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv
              (∑ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j • fy j)) hspan
            (Y.fromSpecStalk _ ≫ pr₁ ≫ f) := by
  set gk : Matrix (Fin (m + 1)) (Fin (m + 1)) k := ↑g with hgk
  have hN : (↑g⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * gk = 1 := Units.inv_mul g
  have hN' : gk * (↑g⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = 1 := Units.mul_inv g
  have := isIso_projSubst gk _ hN hN'
  set cmp := Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m with hcmp
  refine ⟨φB ≫ inv cmp ≫ projSubst gk _ hN ≫ cmp, inferInstance, ?_, ?_, ?_⟩
  · have hφB' : φB ≫ pullback.fst _ _ = pr₁ ≫ f := hφB
    change (φB ≫ inv cmp ≫ projSubst gk _ hN ≫ cmp) ≫ pullback.fst _ _ = pr₁ ≫ f
    have hinv : inv cmp ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k m =
        pullback.fst _ _ := by
      rw [IsIso.inv_comp_eq, hcmp, Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst]
    rw [Category.assoc, Category.assoc, Category.assoc,
      Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst, projSubst_projToSpecCoeff, hinv,
      hφB']
  · obtain ⟨e⟩ := nonempty_pullback_projSubst_twistingSheaf_iso g
    exact ⟨((Scheme.Modules.pullbackComp φB (inv cmp ≫ projSubst gk _ hN ≫ cmp)).app _).symm ≪≫
      (Scheme.Modules.pullback φB).mapIso e⟩
  · set κB := Stacks.ProjectiveSpaceChartRatio.baseRingHom
      (Y.fromSpecStalk (genericPoint Y) ≫ pr₁ ≫ f) with hκB
    have hid : ∀ (R : CommRingCat.{u}) (t : Γ(Spec R, ⊤)),
        (Spec R).presheaf.map (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op t = t := by
      intro R t
      rw [show (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
        CategoryTheory.Functor.map_id]
      rfl
    have hκK : ∀ c : k,
        κB c = (Scheme.ΓSpecIso (.of Y.functionField)).inv (algebraMap k Y.functionField c) := by
      intro c
      rw [hkY c, hκB, Stacks.ProjectiveSpaceChartRatio.baseRingHom]
      change (Y.fromSpecStalk (genericPoint Y)).appTop ((pr₁ ≫ f).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c)) = _
      rw [Scheme.fromSpecStalk_appTop]
      exact hid _ _
    have hr' : ∀ i, (Scheme.ΓSpecIso (.of Y.functionField)).inv (∑ j, gk i j • fy j) =
        ∑ j, κB (gk i j) * (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy j) := by
      intro i
      change (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom (∑ j, gk i j • fy j) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, map_mul, hκK]
    have hspan' : Ideal.span (Set.range fun i =>
        (Scheme.ΓSpecIso (.of Y.functionField)).inv (∑ j, gk i j • fy j)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
        ((Ne.isUnit hg0).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom)
    refine ⟨hspan', ?_⟩
    have hcomp : (MvPolynomial.eval₂Hom κB fun i =>
          (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy i)).comp (linSubstHom gk).toRingHom =
        MvPolynomial.eval₂Hom κB fun i =>
          (Scheme.ΓSpecIso (.of Y.functionField)).inv (∑ j, gk i j • fy j) := by
      rw [eval₂Hom_comp_linSubstHom]
      congr 1
      funext i
      rw [hr' i]
    rw [toProjectiveSpaceOver_eq_fromOfGlobalSections_comp _ _ hspan', ← Category.assoc, hφBy,
      toProjectiveSpaceOver_eq_fromOfGlobalSections_comp, Category.assoc,
      IsIso.hom_inv_id_assoc, ← Category.assoc, projSubst,
      Proj.fromOfGlobalSections_comp_map _ _ _ _
        (hcomp ▸ Stacks.ProjectiveSpaceChartRatio.map_irrelevant_eval₂Hom_eq_top _ _ hspan')]
    congr 1
    exact Proj.fromOfGlobalSections_congr hcomp _ _

/-- Linear independence is kept by an invertible change of basis `vᵢ' = ∑ⱼ gᵢⱼ vⱼ`. -/
private theorem linearIndependent_sum_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} {v : Fin m → V} (hv : LinearIndependent K v)
    (g : Matrix.GeneralLinearGroup (Fin m) K) :
    LinearIndependent K fun i => ∑ j, (g : Matrix (Fin m) (Fin m) K) i j • v j := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  have h1 : Matrix.vecMul c (g : Matrix (Fin m) (Fin m) K) = 0 := funext fun j => by
    refine hv (fun j => ∑ i, c i * (g : Matrix (Fin m) (Fin m) K) i j) ?_ j
    rw [← hc]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have h3 : c = Matrix.vecMul (Matrix.vecMul c (g : Matrix (Fin m) (Fin m) K))
      (↑g⁻¹ : Matrix (Fin m) (Fin m) K) := by
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  intro i
  have := congrFun h3 i
  rw [h1, Matrix.zero_vecMul] at this
  exact this

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **The sections `∑ cᵢ yᵢ` with rational coefficients.** For a basis `fy` of `H⁰(Y, 𝒪(B))`
without base points along prime divisors, and `ℓ c = ∑ cᵢ fyᵢ`: `ℓ c ≠ 0` for `c ≠ 0`, `ℓ c` is a
section of `𝒪(B)`, its divisor of zeros is supported in codimension one at finitely many points,
and at every point `p` the vectors `c` for which `ℓ c` vanishes along a prime divisor through `p`
lie in a proper subspace. -/
private theorem sections_facts (k : Type u) [Field k] [NumberField k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    {Y : Scheme.{u}} {pr₁ pr₂ : Y ⟶ C} (hY : IsPullback pr₁ pr₂ f f)
    [IsIntegral Y] [IsLocallyNoetherian Y] [Algebra k Y.functionField]
    (hkY : ∀ c : k, algebraMap k Y.functionField c =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →+* Y.functionField)
    (hι₁ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₁ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₁ (C.germToFunctionField V t) = Y.germToFunctionField (pr₁ ⁻¹ᵁ V) (pr₁.app V t))
    (hι₂ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₂ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₂ (C.germToFunctionField V t) = Y.germToFunctionField (pr₂ ⁻¹ᵁ V) (pr₂.app V t))
    (s : ℕ) {eΔ : Y} (DB : Y → ℤ)
    (hDB : ∀ q, DB q = (s + 1 : ℤ) * P₁.sum (fun c a =>
        if IsGenericPoint q (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a =>
        if IsGenericPoint q (pr₂.base ⁻¹' {c}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (fy : Fin (m + 1) → Y.functionField) (hfy : ∀ i, fy i ≠ 0)
    (hD : ∀ i q, 0 ≤ Y.ord (fy i) q + DB q)
    (hfli : LinearIndependent k fy)
    (hfbpf : ∀ q, Order.coheight q = 1 → ∃ i, Y.ord (fy i) q + DB q = 0)
    (φB : Y ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφBy : Y.fromSpecStalk (genericPoint Y) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hfy 0)).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
        (Y.fromSpecStalk _ ≫ pr₁ ≫ f)) :
    (∀ c : Fin (m + 1) → ℚ, c ≠ 0 → ∑ i, (c i : Y.functionField) * fy i ≠ 0) ∧
    (∀ c : Fin (m + 1) → ℚ, ∑ i, (c i : Y.functionField) * fy i ≠ 0 →
      ∀ q, 0 ≤ Y.ord (∑ i, (c i : Y.functionField) * fy i) q + DB q) ∧
    (∀ (c : Fin (m + 1) → ℚ) q, 0 < Y.ord (∑ i, (c i : Y.functionField) * fy i) q + DB q →
      Order.coheight q = 1) ∧
    (∀ c : Fin (m + 1) → ℚ, ∑ i, (c i : Y.functionField) * fy i ≠ 0 →
      {q | 0 < Y.ord (∑ i, (c i : Y.functionField) * fy i) q + DB q}.Finite) ∧
    ∀ p : Y, ∃ S : Submodule ℚ (Fin (m + 1) → ℚ), S ≠ ⊤ ∧ ∀ c ∉ S,
      ∑ i, (c i : Y.functionField) * fy i ≠ 0 ∧
      ∀ q, q ⤳ p → Order.coheight q = 1 →
        Y.ord (∑ i, (c i : Y.functionField) * fy i) q + DB q = 0 := by
  have : IsProper f := (inferInstance : IsProperVariety k f).toIsProper
  have : IsNormal C := isNormal_of_smooth_over_field f
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hY.flip inferInstance
  have : IsNormal Y := isNormal_of_smooth_over_field (pr₁ ≫ f)
  have : IsProper pr₁ := MorphismProperty.of_isPullback (P := @IsProper) hY.flip inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (pr₁ ≫ f)
  have : CharZero Y.functionField :=
    charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  set G : Set Y := {q | ∃ c ∈ P₁.support,
    IsGenericPoint q (pr₁.base ⁻¹' {c}) ∨ IsGenericPoint q (pr₂.base ⁻¹' {c})} with hGdef
  have hG1 : ∀ q ∈ G, Order.coheight q = 1 := by
    rintro q ⟨c, hc, h | h⟩
    · exact coheight_eq_one_of_isGenericPoint f pr₁ ι₁ hι₁
        (ne_genericPoint_of_isClosed f (hP₁cl c hc)) h
    · exact coheight_eq_one_of_isGenericPoint f pr₂ ι₂ hι₂
        (ne_genericPoint_of_isClosed f (hP₁cl c hc)) h
  have hGfin : G.Finite := by
    refine (P₁.support.finite_toSet.biUnion fun c _ =>
      (Set.Subsingleton.finite (s := {q : Y | IsGenericPoint q (pr₁.base ⁻¹' {c})})
        fun q hq q' hq' => hq.eq hq').union
      (Set.Subsingleton.finite (s := {q : Y | IsGenericPoint q (pr₂.base ⁻¹' {c})})
        fun q hq q' hq' => hq.eq hq')).subset ?_
    rintro q ⟨c, hc, h⟩
    exact Set.mem_biUnion hc h
  have hDBG : ∀ q, q ∉ G → DB q = -(if q = eΔ then 1 else 0) := by
    intro q hq
    have h1 : P₁.sum (fun c a => if IsGenericPoint q (pr₁.base ⁻¹' {c}) then a else 0) = 0 :=
      Finset.sum_eq_zero fun c hc => ite_eq_right_iff.mpr fun h => absurd ⟨c, hc, Or.inl h⟩ hq
    have h2 : P₁.sum (fun c a => if IsGenericPoint q (pr₂.base ⁻¹' {c}) then a else 0) = 0 :=
      Finset.sum_eq_zero fun c hc => ite_eq_right_iff.mpr fun h => absurd ⟨c, hc, Or.inr h⟩ hq
    rw [hDB q, h1, h2]
    ring
  have hDB0 : ∀ q, Order.coheight q ≠ 1 → DB q = 0 := by
    intro q hq
    have hqG : q ∉ G := fun h => hq (hG1 q h)
    have h3 := hD 0 q
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hq, zero_add, hDBG q hqG] at h3
    rw [hDBG q hqG]
    split_ifs at h3 ⊢ <;> omega
  set κ : ∀ y : Y, k →+* Y.presheaf.stalk y := fun y =>
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pr₁ ≫ f).appTop ≫ Y.presheaf.germ ⊤ y trivial).hom
    with hκdef
  have hκ : ∀ y, (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (κ y) =
      algebraMap k Y.functionField := by
    intro y
    ext c
    rw [hkY c]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := ⊤) (x := y) trivial _
  set ℓ : (Fin (m + 1) → ℚ) → Y.functionField := fun c => ∑ i, (c i : Y.functionField) * fy i
    with hℓdef
  have hℓ0 : ∀ c, c ≠ 0 → ℓ c ≠ 0 := by
    intro c hc h0
    apply hc
    have := Fintype.linearIndependent_iff.mp hfli (fun i => (c i : k)) (by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_ratCast])
    funext i
    exact_mod_cast this i
  have hℓD : ∀ c, ℓ c ≠ 0 → ∀ q, 0 ≤ Y.ord (ℓ c) q + DB q := by
    intro c hc q
    by_cases hq : Order.coheight q = 1
    · obtain ⟨j, hj⟩ := hfbpf q hq
      have hreg : ∀ i, fy i / fy j ∈ Set.range
          (algebraMap (Y.presheaf.stalk q) Y.functionField) := by
        intro i
        refine (ord_nonneg_iff hq (div_ne_zero (hfy i) (hfy j))).mp ?_
        rw [ord_div (hfy i) (hfy j)]
        have := hD i q
        omega
      have hsum : ℓ c / fy j ∈ Set.range (algebraMap (Y.presheaf.stalk q) Y.functionField) := by
        have : ℓ c / fy j = ∑ i, (c i : Y.functionField) * (fy i / fy j) := by
          rw [hℓdef, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this]
        refine Subring.sum_mem (algebraMap (Y.presheaf.stalk q) Y.functionField).range
          fun i _ => Subring.mul_mem _ ?_ (hreg i)
        exact ⟨κ q (c i : k), by rw [← RingHom.comp_apply, hκ, map_ratCast]⟩
      have := (ord_nonneg_iff hq (div_ne_zero hc (hfy j))).mpr hsum
      rw [ord_div hc (hfy j)] at this
      omega
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq, hDB0 q hq]; rfl
  have hsupp1 : ∀ c q, 0 < Y.ord (ℓ c) q + DB q → Order.coheight q = 1 := by
    intro c q hq
    by_contra h
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h, hDB0 q h] at hq
    exact lt_irrefl _ hq
  have hsuppfin : ∀ c, ℓ c ≠ 0 → {q | 0 < Y.ord (ℓ c) q + DB q}.Finite := by
    intro c hc
    refine ((finite_setOf_ord_ne_zero hc).union hGfin).subset ?_
    intro q hq
    by_cases hqG : q ∈ G
    · exact Or.inr hqG
    refine Or.inl ⟨hsupp1 c q hq, fun h0 => ?_⟩
    have : DB q ≤ 0 := by rw [hDBG q hqG]; split_ifs <;> omega
    simp only [Set.mem_ofPred_eq, h0] at hq
    omega
  obtain ⟨hηB, hgermB⟩ := exists_germ_app_ratio_eq_div φB fy (hfy 0) _ _ hφBy
  have hgood : ∀ p : Y, ∃ S : Submodule ℚ (Fin (m + 1) → ℚ), S ≠ ⊤ ∧ ∀ c ∉ S, ℓ c ≠ 0 ∧
      ∀ q, q ⤳ p → Order.coheight q = 1 → Y.ord (ℓ c) q + DB q = 0 := by
    intro p
    obtain ⟨j, hj⟩ := exists_forall_div_mem_range
      (φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) fy hfy hηB hgermB p
    exact exists_submodule_forall_ord_add_eq_zero κ hκ DB fy hfy hD hfbpf p j hj
  exact ⟨hℓ0, hℓD, hsupp1, hsuppfin, hgood⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **Generic coordinates for `φ_B`, in general form.** The statement of
`Faltings.exists_isGenericForProjections_map` for an arbitrary fibre product `Y` of a curve `C`
with itself, any nonzero divisor `P₁` on `C` with closed support (degree one is not needed), ring
homomorphisms `ι₁, ι₂`, and only the hypotheses the proof uses; the conclusion gives the pull-back
of the hyperplane sheaf along `φB'` as isomorphic to that along `φB`. -/
private theorem exists_isGenericForProjections_map_aux (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C)) (hP₁ne : P₁ ≠ 0)
    {Y : Scheme.{u}} {pr₁ pr₂ : Y ⟶ C} (hY : IsPullback pr₁ pr₂ f f)
    [IsIntegral Y] [IsLocallyNoetherian Y] [Algebra k Y.functionField]
    (hkY : ∀ c : k, algebraMap k Y.functionField c =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →+* Y.functionField)
    (hι₁ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₁ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₁ (C.germToFunctionField V t) = Y.germToFunctionField (pr₁ ⁻¹ᵁ V) (pr₁.app V t))
    (hι₂ : ∀ (V : C.Opens) [Nonempty V] [Nonempty (pr₂ ⁻¹ᵁ V)] (t : Γ(C, V)),
      ι₂ (C.germToFunctionField V t) = Y.germToFunctionField (pr₂ ⁻¹ᵁ V) (pr₂.app V t))
    (N : ℕ) {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hxgen : BombieriSiegel.IsGenericBasis k f ((N : ℤ) • P₁) x)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNPx :
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (s : ℕ) {eΔ : Y} (DB : Y → ℤ)
    (hDB : ∀ q, DB q = (s + 1 : ℤ) * P₁.sum (fun c a =>
        if IsGenericPoint q (pr₁.base ⁻¹' {c}) then a else 0) +
      (s + 1 : ℤ) * P₁.sum (fun c a =>
        if IsGenericPoint q (pr₂.base ⁻¹' {c}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (fy : Fin (m + 1) → Y.functionField) (hfy : ∀ i, fy i ≠ 0)
    (hD : ∀ i q, 0 ≤ Y.ord (fy i) q + DB q)
    (hfli : LinearIndependent k fy)
    (hfspan : ∀ h : Y.functionField, (∀ q, 0 ≤ Y.ord h q + DB q) →
      h ∈ Submodule.span k (Set.range fy))
    (hfbpf : ∀ q, Order.coheight q = 1 → ∃ i, Y.ord (fy i) q + DB q = 0)
    (φB : Y ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pr₁ ≫ f)
    [IsClosedImmersion φB]
    (hφBy : Y.fromSpecStalk (genericPoint Y) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hfy 0)).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
        (Y.fromSpecStalk _ ≫ pr₁ ≫ f)) :
    ∃ g : Matrix.GeneralLinearGroup (Fin (m + 1)) k,
      let fy' : Fin (m + 1) → Y.functionField := fun i =>
        ∑ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j • fy j
      ∃ hy' : ∀ i, fy' i ≠ 0,
      (∀ i q, 0 ≤ Y.ord (fy' i) q + DB q) ∧
      LinearIndependent k fy' ∧
      (∀ h : Y.functionField, (∀ q, 0 ≤ Y.ord h q + DB q) →
        h ∈ Submodule.span k (Set.range fy')) ∧
      (∀ q, Order.coheight q = 1 → ∃ i, Y.ord (fy' i) q + DB q = 0) ∧
      (∃ φB' : Y ⟶ projectiveSpaceOver m (Spec (.of k)),
        IsClosedImmersion φB' ∧
        φB' ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pr₁ ≫ f ∧
        Nonempty ((Scheme.Modules.pullback φB').obj
            ((Scheme.Modules.pullback
              (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)) ≅
          (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback
              (projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1))) ∧
        Y.fromSpecStalk (genericPoint Y) ≫ φB' =
          Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
            (fun i => (Scheme.ΓSpecIso (.of Y.functionField)).inv (fy' i))
            (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
              ((Ne.isUnit (hy' 0)).map (Scheme.ΓSpecIso (.of Y.functionField)).inv.hom))
            (Y.fromSpecStalk _ ≫ pr₁ ≫ f)) ∧
      (∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
        0 < Y.ord (fy' i) q + DB q → 0 < Y.ord (fy' 0) q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
          0 ≤ Y.ord r q ∧ Y.ord r q' < 0) ∧
      (∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → ∀ i j : Fin (m + 1),
        i.val = 1 → j.val = 2 → ∀ q q', 0 < Y.ord (fy' i) q + DB q →
          0 < Y.ord (fy' j) q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)},
          0 ≤ Y.ord r q ∧ Y.ord r q' < 0) ∧
      (∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
        0 < Y.ord (fy' i) q + DB q →
        0 ≤ Y.ord (ι₁ (x a / x 0)) q ∧ 0 ≤ Y.ord (ι₂ (x b / x 0)) q) ∧
      (∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 →
        ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
        ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : Y,
          (∀ r ∈ 𝔪, r ≠ 0 →
            (∀ q, q ⤳ p → Order.coheight q = 1 →
              0 ≤ Y.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) q) ∧
            ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
              0 < Y.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) q) →
          ∀ q, q ⤳ p → Order.coheight q = 1 → Y.ord (fy' i) q + DB q = 0) := by
  obtain ⟨E, hEdef⟩ : ∃ E : C →₀ ℤ, E = (N : ℤ) • P₁ := ⟨_, rfl⟩
  rw [← hEdef] at hxgen
  have : IsProper f := (inferInstance : IsProperVariety k f).toIsProper
  have : IsNormal C := isNormal_of_smooth_over_field f
  have : Smooth pr₁ := MorphismProperty.of_isPullback (P := @Smooth) hY.flip inferInstance
  have : IsNormal Y := isNormal_of_smooth_over_field (pr₁ ≫ f)
  have : IsProper pr₁ := MorphismProperty.of_isPullback (P := @IsProper) hY.flip inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (pr₁ ≫ f)
  have : CharZero Y.functionField :=
    charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  let := functionFieldAlgebra k f
  obtain ⟨c₀, hc₀⟩ := Finsupp.support_nonempty_iff.mpr hP₁ne
  have hc₀cl : IsClosed ({c₀} : Set C) := hP₁cl c₀ hc₀
  have hc₀η : c₀ ≠ genericPoint C := ne_genericPoint_of_isClosed f hc₀cl
  have hEη : E (genericPoint C) = 0 := by
    rw [hEdef, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp fun h =>
      ne_genericPoint_of_isClosed f (hP₁cl _ h) rfl, smul_zero]
  have hx0 : ∀ j, x j ≠ 0 := hxgen.linearIndependent.ne_zero
  have hxE : ∀ j z, 0 ≤ C.ord (x j) z + E z := by
    intro j z
    by_cases hz : z = genericPoint C
    · rw [hz, Scheme.ord_eq_zero_of_coheight_neq_one
        (FunctionField.coheight_genericPoint_ne_one C), zero_add, hEη]
    have hmem : x j ∈ ((Submodule.span k (Set.range x) : Submodule k C.functionField) :
        Set C.functionField) := Submodule.subset_span ⟨j, rfl⟩
    rw [hxgen.span_eq] at hmem
    rcases hmem with h | h
    · exact absurd h (hx0 j)
    · exact h z (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f hz)
  have hNG1 : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, Order.coheight z = 1 →
      C.ord (x 0) z + E z = 0 ∨ C.ord (x a) z + E z = 0 := by
    intro a ha z hz
    have hzg : z ≠ genericPoint C := fun h =>
      FunctionField.coheight_genericPoint_ne_one C (h ▸ hz)
    have := hxgen.satisfiesG1 a ha z
      (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f hzg)
    have h0 := hxE 0 z
    have ha' := hxE a z
    omega
  have hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  set ψNP : C ⟶ AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) with hψNPdef
  have hφNPa : IsAffineHom φNP := inferInstance
  have htoInta : IsAffineHom (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) :=
    inferInstance
  have : IsAffineHom ψNP := ⟨fun U hU =>
    (hU.preimage (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).preimage φNP⟩
  have hψNP : ∀ (j : Fin (n + 1)) [Nonempty (ψNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j))]
      (ν : Fin (n + 1)), C.germToFunctionField _ (ψNP.app _ (Proj.awayToSection _
        (MvPolynomial.X j) (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X_mem_one j) 1
          (MvPolynomial.X ν) (X_mem_one' ν)))) = x ν / x j :=
    fun j hj ν => @hφNPx j ν hj
  have hψNP_ne : ((ψNP ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X 0) : C.Opens) : Set C).Nonempty :=
    nonempty_preimage_basicOpen_zero ψNP x hx0 fun j _ => hψNP j 0
  have hm3 : 3 ≤ m := three_le_of_isClosedImmersion f hY hc₀cl hc₀η
    (φB ≫ inv (Stacks.AlgebraicGeometry.ProjPolyChart.projCompare k m))
  set κ : ∀ y : Y, k →+* Y.presheaf.stalk y := fun y =>
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (pr₁ ≫ f).appTop ≫ Y.presheaf.germ ⊤ y trivial).hom
    with hκdef
  have hκ : ∀ y, (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (κ y) =
      algebraMap k Y.functionField := by
    intro y
    ext c
    rw [hkY c]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := ⊤) (x := y) trivial _
  set ℓ : (Fin (m + 1) → ℚ) → Y.functionField := fun c => ∑ i, (c i : Y.functionField) * fy i
    with hℓdef
  have hfacts := sections_facts k f P₁ hP₁cl hY hkY ι₁ ι₂ hι₁ hι₂ s DB hDB fy hfy hD hfli hfbpf φB
    hφBy
  have hℓ0 : ∀ c, c ≠ 0 → ℓ c ≠ 0 := hfacts.1
  have hℓD : ∀ c, ℓ c ≠ 0 → ∀ q, 0 ≤ Y.ord (ℓ c) q + DB q := hfacts.2.1
  have hsupp1 : ∀ c q, 0 < Y.ord (ℓ c) q + DB q → Order.coheight q = 1 := hfacts.2.2.1
  have hsuppfin : ∀ c, ℓ c ≠ 0 → {q | 0 < Y.ord (ℓ c) q + DB q}.Finite := hfacts.2.2.2.1
  have hgood : ∀ p : Y, ∃ S : Submodule ℚ (Fin (m + 1) → ℚ), S ≠ ⊤ ∧ ∀ c ∉ S, ℓ c ≠ 0 ∧
      ∀ q, q ⤳ p → Order.coheight q = 1 → Y.ord (ℓ c) q + DB q = 0 := hfacts.2.2.2.2
  clear hfacts
  choose Sp hSp hSpgood using hgood
  have hfinord : ∀ h : Y.functionField, {q | Order.coheight q = 1 ∧ Y.ord h q ≠ 0}.Finite := by
    intro h
    by_cases h0 : h = 0
    · convert Set.finite_empty
      ext q
      simp [h0]
    · exact finite_setOf_ord_ne_zero h0
  set W := chartOpen pr₁ pr₂ ψNP with hWdef
  have hchart := fun (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) =>
    exists_affine_chart f hkC hY hkY ι₁ ι₂ hι₁ hι₂ E x hx0 hxE ψNP hψNP_ne
      (fun j => hψNP 0 j) hNG1 a b ha hb
  choose hW hWne φ hφK hφfin hWmem using hchart
  have hξ₁ : ∀ a, ι₁ (x a / x 0) ≠ 0 := fun a =>
    (map_ne_zero_iff _ ι₁.injective).mpr (div_ne_zero (hx0 a) (hx0 0))
  have hξ₂ : ∀ a, ι₂ (x a / x 0) ≠ 0 := fun a =>
    (map_ne_zero_iff _ ι₂.injective).mpr (div_ne_zero (hx0 a) (hx0 0))
  have hWof : ∀ (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (q : Y), Order.coheight q = 1 →
      0 ≤ Y.ord (ι₁ (x a / x 0)) q → 0 ≤ Y.ord (ι₂ (x b / x 0)) q → q ∈ W :=
    fun a b ha hb q hq h1 h2 => hWmem a b ha hb q ((ord_nonneg_iff hq (hξ₁ a)).mp h1)
      ((ord_nonneg_iff hq (hξ₂ b)).mp h2)
  have hAL : ∀ (a b : Fin (n + 1)) (r : MvPolynomial (Fin 2) k),
      MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r ∈
        IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)} := by
    intro a b r
    have h1 : MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r ∈
        Algebra.adjoin k (Set.range ![ι₁ (x a / x 0), ι₂ (x b / x 0)]) := by
      rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨r, rfl⟩
    have h2 : Set.range ![ι₁ (x a / x 0), ι₂ (x b / x 0)] =
        {ι₁ (x a / x 0), ι₂ (x b / x 0)} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [h2] at h1
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  set Taff : Set Y := {q | Order.coheight q = 1 ∧ ∃ a : Fin (n + 1), a ≠ 0 ∧
    (Y.ord (ι₁ (x a / x 0)) q < 0 ∨ Y.ord (ι₂ (x a / x 0)) q < 0)} with hTaffdef
  have hTaff : Taff.Finite := by
    refine (Set.finite_iUnion fun a : Fin (n + 1) =>
      (hfinord (ι₁ (x a / x 0))).union (hfinord (ι₂ (x a / x 0)))).subset ?_
    rintro q ⟨hq, a, -, h | h⟩
    · exact Set.mem_iUnion.mpr ⟨a, Or.inl ⟨hq, h.ne⟩⟩
    · exact Set.mem_iUnion.mpr ⟨a, Or.inr ⟨hq, h.ne⟩⟩
  have haff : ∀ q, Order.coheight q = 1 → q ∉ Taff → ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 →
      0 ≤ Y.ord (ι₁ (x a / x 0)) q ∧ 0 ≤ Y.ord (ι₂ (x b / x 0)) q := by
    intro q hq hqT a b ha hb
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hqT ⟨hq, a, ha, Or.inl (lt_of_not_ge h)⟩
    · by_contra h
      exact hqT ⟨hq, b, hb, Or.inr (lt_of_not_ge h)⟩
  have hℓe0 : ℓ (Pi.single 0 1) = fy 0 := by
    rw [hℓdef]
    simp only
    rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (by simp)]
    simp
  set S0 : Set Y := {q | 0 < Y.ord (fy 0) q + DB q} with hS0def
  have hS0 : S0.Finite := by
    have := hsuppfin (Pi.single 0 1) (by rw [hℓe0]; exact hfy 0)
    rwa [hℓe0] at this
  have hS01 : ∀ q ∈ S0, Order.coheight q = 1 := fun q hq =>
    hsupp1 (Pi.single 0 1) q (by rw [hℓe0]; exact hq)
  have hr : ∀ (a b : Fin (n + 1)) (q : Y), ∃ r : Y.functionField, r ≠ 0 ∧
      (a ≠ 0 → b ≠ 0 → Order.coheight q = 1 →
        r ∈ IntermediateField.adjoin k {ι₁ (x a / x 0), ι₂ (x b / x 0)} ∧ Y.ord r q < 0) := by
    intro a b q
    by_cases hcond : a ≠ 0 ∧ b ≠ 0 ∧ Order.coheight q = 1
    swap
    · refine ⟨1, one_ne_zero, fun ha hb hq => absurd ⟨ha, hb, hq⟩ hcond⟩
    obtain ⟨ha, hb, hq⟩ := hcond
    by_cases hqW : q ∈ W
    · have := hWne a b ha hb
      obtain ⟨G, hG0, hGpos⟩ := exists_aeval_ne_zero_ord_pos (hW a b ha hb) (hφK a b ha hb)
        (hφfin a b ha hb) hqW hq
      refine ⟨(MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] G)⁻¹, inv_ne_zero hG0,
        fun _ _ _ => ⟨IntermediateField.inv_mem _ (hAL a b G), ?_⟩⟩
      rw [Stacks.Chow.ord_inv_functionField hG0]
      omega
    · by_cases h1 : 0 ≤ Y.ord (ι₁ (x a / x 0)) q
      · by_cases h2 : 0 ≤ Y.ord (ι₂ (x b / x 0)) q
        · exact absurd (hWof a b ha hb q hq h1 h2) hqW
        · exact ⟨ι₂ (x b / x 0), hξ₂ b, fun _ _ _ =>
            ⟨IntermediateField.subset_adjoin k _ (by simp), lt_of_not_ge h2⟩⟩
      · exact ⟨ι₁ (x a / x 0), hξ₁ a, fun _ _ _ =>
          ⟨IntermediateField.subset_adjoin k _ (by simp), lt_of_not_ge h1⟩⟩
  choose rr hrr0 hrr using hr
  set T0 : Set Y := {q | Order.coheight q = 1 ∧ ∃ (a b : Fin (n + 1)) (q' : Y), q' ∈ S0 ∧
    Y.ord (rr a b q') q < 0} with hT0def
  have hT0 : T0.Finite := by
    refine (Set.finite_iUnion fun a : Fin (n + 1) => Set.finite_iUnion fun b : Fin (n + 1) =>
      hS0.biUnion fun q' _ => hfinord (rr a b q')).subset ?_
    rintro q ⟨hq, a, b, q', hq', h⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_biUnion hq' ⟨hq, h.ne⟩⟩⟩
  have hSfin : ∀ T : Set Y, T.Finite → (Sp '' T).Finite := fun T hT => hT.image _
  have hSprop : ∀ T : Set Y, ∀ S ∈ Sp '' T, S ≠ ⊤ := by
    rintro T S ⟨q, -, rfl⟩
    exact hSp q
  have hfinrank : Module.finrank ℚ (Fin (m + 1) → ℚ) = m + 1 := by simp
  have havoid : ∀ (c : Fin (m + 1) → ℚ) (T : Set Y), (∀ S ∈ Sp '' T, c ∉ S) →
      ∀ q ∈ T, Order.coheight q = 1 → Y.ord (ℓ c) q + DB q = 0 := by
    intro c T hc q hq hq1
    exact ((hSpgood q) c (hc _ ⟨q, hq, rfl⟩)).2 q le_rfl hq1
  have hnotsupp : ∀ (c : Fin (m + 1) → ℚ) (T : Set Y), (∀ S ∈ Sp '' T, c ∉ S) →
      ∀ q, 0 < Y.ord (ℓ c) q + DB q → q ∉ T := by
    intro c T hc q hq hqT
    have := havoid c T hc q hqT (hsupp1 c q hq)
    omega
  set c0 : Fin (m + 1) → ℚ := Pi.single 0 1 with hc0def
  have hc0int : IsIntVec c0 := ⟨Pi.single 0 1, by
    funext j; simp only [hc0def, Pi.single_apply]; split_ifs <;> simp⟩
  set v1 : Fin 1 → Fin (m + 1) → ℚ := fun _ => c0
  have hv1 : LinearIndependent ℚ v1 :=
    linearIndependent_unique_iff.mpr (by simp [v1, hc0def])
  obtain ⟨c2, hc2int, hc2span, hc2S⟩ := exists_intVec_notMem_of_finite
    (hSfin _ (hTaff.union hT0)) (hSprop _) _ (span_range_ne_top v1 (by rw [hfinrank]; omega))
  have hc2ne : ℓ c2 ≠ 0 := hℓ0 c2 fun h => hc2span (h ▸ zero_mem _)
  set S2 : Set Y := {q | 0 < Y.ord (ℓ c2) q + DB q} with hS2def
  have hS2 : S2.Finite := hsuppfin c2 hc2ne
  have hS2W : ∀ q ∈ S2, Order.coheight q = 1 ∧ q ∉ Taff ∧ q ∉ T0 ∧
      ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → q ∈ W := by
    intro q hq
    have hq1 := hsupp1 c2 q hq
    have hqT : q ∉ Taff := fun h => hnotsupp c2 _ hc2S q hq (Or.inl h)
    refine ⟨hq1, hqT, fun h => hnotsupp c2 _ hc2S q hq (Or.inr h), fun a b ha hb => ?_⟩
    obtain ⟨h1, h2⟩ := haff q hq1 hqT a b ha hb
    exact hWof a b ha hb q hq1 h1 h2
  have hG : ∀ (a b : Fin (n + 1)) (q : Y), ∃ G : MvPolynomial (Fin 2) k,
      ∀ (_ : a ≠ 0) (_ : b ≠ 0), Order.coheight q = 1 → q ∈ W →
        MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] G ≠ 0 ∧
        0 < Y.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] G) q := by
    intro a b q
    by_cases hcond : a ≠ 0 ∧ b ≠ 0 ∧ Order.coheight q = 1 ∧ q ∈ W
    · obtain ⟨ha, hb, hq, hqW⟩ := hcond
      have := hWne a b ha hb
      obtain ⟨G, hG0, hGpos⟩ := exists_aeval_ne_zero_ord_pos (hW a b ha hb) (hφK a b ha hb)
        (hφfin a b ha hb) hqW hq
      exact ⟨G, fun _ _ _ _ => ⟨hG0, hGpos⟩⟩
    · exact ⟨0, fun ha hb hq hqW => absurd ⟨ha, hb, hq, hqW⟩ hcond⟩
  choose GG hGG using hG
  set Tsep : Set Y := {q | Order.coheight q = 1 ∧ ∃ (a b : Fin (n + 1)) (q₂ : Y), q₂ ∈ S2 ∧
    0 < Y.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] (GG a b q₂)) q}
    with hTsepdef
  have hTsep : Tsep.Finite := by
    refine (Set.finite_iUnion fun a : Fin (n + 1) => Set.finite_iUnion fun b : Fin (n + 1) =>
      hS2.biUnion fun q₂ _ =>
        hfinord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] (GG a b q₂))).subset ?_
    rintro q ⟨hq, a, b, q₂, hq₂, h⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_biUnion hq₂ ⟨hq, h.ne'⟩⟩⟩
  set v2 : Fin 2 → Fin (m + 1) → ℚ := Fin.snoc v1 c2
  have hv2 : LinearIndependent ℚ v2 := linearIndependent_finSnoc.mpr ⟨hv1, hc2span⟩
  obtain ⟨c1, hc1int, hc1span, hc1S⟩ := exists_intVec_notMem_of_finite
    (hSfin _ ((hTaff.union hT0).union hTsep)) (hSprop _) _
    (span_range_ne_top v2 (by rw [hfinrank]; omega))
  have hc1ne : ℓ c1 ≠ 0 := hℓ0 c1 fun h => hc1span (h ▸ zero_mem _)
  set S1 : Set Y := {q | 0 < Y.ord (ℓ c1) q + DB q} with hS1def
  have hS1 : S1.Finite := hsuppfin c1 hc1ne
  have hS1W : ∀ q ∈ S1, Order.coheight q = 1 ∧ q ∉ Taff ∧ q ∉ T0 ∧ q ∉ Tsep ∧
      ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → q ∈ W := by
    intro q hq
    have hq1 := hsupp1 c1 q hq
    have hqT : q ∉ Taff := fun h => hnotsupp c1 _ hc1S q hq (Or.inl (Or.inl h))
    refine ⟨hq1, hqT, fun h => hnotsupp c1 _ hc1S q hq (Or.inl (Or.inr h)),
      fun h => hnotsupp c1 _ hc1S q hq (Or.inr h), fun a b ha hb => ?_⟩
    obtain ⟨h1, h2⟩ := haff q hq1 hqT a b ha hb
    exact hWof a b ha hb q hq1 h1 h2
  set P : ∀ (a b : Fin (n + 1)), a ≠ 0 → b ≠ 0 → Y → Ideal (MvPolynomial (Fin 2) k) :=
    fun a b ha hb q => if hq : q ∈ W then
      ((hW a b ha hb).primeIdealOf ⟨q, hq⟩).asIdeal.comap (φ a b ha hb) else ⊥ with hPdef
  have hPeq : ∀ a b ha hb q (hq : q ∈ W), P a b ha hb q =
      ((hW a b ha hb).primeIdealOf ⟨q, hq⟩).asIdeal.comap (φ a b ha hb) := by
    intro a b ha hb q hq
    simp [hPdef, hq]
  have hPmem : ∀ a b ha hb q (hq : q ∈ W), Order.coheight q = 1 →
      ∀ r : MvPolynomial (Fin 2) k,
      MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r ≠ 0 →
      (r ∈ P a b ha hb q ↔
        0 < Y.ord (MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] r) q) := by
    intro a b ha hb q hq hq1 r hr
    have := hWne a b ha hb
    rw [hPeq a b ha hb q hq]
    exact mem_comap_primeIdealOf_iff_ord (hW a b ha hb) (hφK a b ha hb) hq hq1 hr
  set F12 : ∀ (a b : Fin (n + 1)), a ≠ 0 → b ≠ 0 → Set (Ideal (MvPolynomial (Fin 2) k)) :=
    fun a b ha hb => {𝔪 | 𝔪.IsMaximal ∧ ∃ q₁ ∈ S1, ∃ q₂ ∈ S2,
      P a b ha hb q₁ ⊔ P a b ha hb q₂ ≤ 𝔪} with hF12def
  have hdim2 : ringKrullDim (MvPolynomial (Fin 2) k) ≤ 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hF12 : ∀ a b ha hb, (F12 a b ha hb).Finite := by
    intro a b ha hb
    have hpair : ∀ q₁ ∈ S1, ∀ q₂ ∈ S2,
        {𝔪 : Ideal (MvPolynomial (Fin 2) k) | 𝔪.IsMaximal ∧
          P a b ha hb q₁ ⊔ P a b ha hb q₂ ≤ 𝔪}.Finite := by
      intro q₁ hq₁ q₂ hq₂
      obtain ⟨hq₁1, -, -, hq₁sep, hq₁W⟩ := hS1W q₁ hq₁
      obtain ⟨hq₂1, -, -, hq₂W⟩ := hS2W q₂ hq₂
      have hW₁ := hq₁W a b ha hb
      have hW₂ := hq₂W a b ha hb
      have : (P a b ha hb q₁).IsPrime := by rw [hPeq a b ha hb q₁ hW₁]; exact Ideal.IsPrime.comap _
      have : (P a b ha hb q₂).IsPrime := by rw [hPeq a b ha hb q₂ hW₂]; exact Ideal.IsPrime.comap _
      obtain ⟨hG₁0, hG₁pos⟩ := hGG a b q₁ ha hb hq₁1 hW₁
      obtain ⟨hG₂0, hG₂pos⟩ := hGG a b q₂ ha hb hq₂1 hW₂
      have hG₁ := (hPmem a b ha hb q₁ hW₁ hq₁1 _ hG₁0).mpr hG₁pos
      have hG₂ := (hPmem a b ha hb q₂ hW₂ hq₂1 _ hG₂0).mpr hG₂pos
      have hne : ∀ G : MvPolynomial (Fin 2) k,
          MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)] G ≠ 0 → G ≠ 0 :=
        fun G hG h0 => hG (by rw [h0, map_zero])
      refine finite_setOf_isMaximal_sup_le hdim2 (fun h => hne _ hG₁0 ?_)
        (fun h => hne _ hG₂0 ?_) (fun h => ?_)
      · rw [h] at hG₁; exact (Ideal.mem_bot).mp hG₁
      · rw [h] at hG₂; exact (Ideal.mem_bot).mp hG₂
      · rw [← h] at hG₂
        exact hq₁sep ⟨hq₁1, a, b, q₂, hq₂, (hPmem a b ha hb q₁ hW₁ hq₁1 _ hG₂0).mp hG₂⟩
    refine (Set.Finite.biUnion (t := fun q₁ => ⋃ q₂ ∈ S2,
      {𝔪 : Ideal (MvPolynomial (Fin 2) k) | 𝔪.IsMaximal ∧
        P a b ha hb q₁ ⊔ P a b ha hb q₂ ≤ 𝔪}) hS1 fun q₁ hq₁ =>
      Set.Finite.biUnion (t := fun q₂ => {𝔪 : Ideal (MvPolynomial (Fin 2) k) | 𝔪.IsMaximal ∧
        P a b ha hb q₁ ⊔ P a b ha hb q₂ ≤ 𝔪}) hS2 fun q₂ hq₂ => hpair q₁ hq₁ q₂ hq₂).subset ?_
    rintro 𝔪 ⟨h𝔪, q₁, hq₁, q₂, hq₂, hle⟩
    exact Set.mem_biUnion hq₁ (Set.mem_biUnion hq₂ ⟨h𝔪, hle⟩)
  set S3 : Set Y := {p | ∃ (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (hpW : p ∈ W),
    ((hW a b ha hb).primeIdealOf ⟨p, hpW⟩).asIdeal.comap (φ a b ha hb) ∈ F12 a b ha hb}
    with hS3def
  have hS3 : S3.Finite := by
    have hone : ∀ (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
        (𝔪 : Ideal (MvPolynomial (Fin 2) k)),
        {p : Y | ∃ hpW : p ∈ W,
          ((hW a b ha hb).primeIdealOf ⟨p, hpW⟩).asIdeal.comap (φ a b ha hb) = 𝔪}.Finite :=
      fun a b ha hb 𝔪 => finite_setOf_comap_eq (hW a b ha hb) (hφfin a b ha hb) 𝔪
    refine (Set.finite_iUnion fun a : Fin (n + 1) => Set.finite_iUnion fun b : Fin (n + 1) =>
      Set.finite_iUnion fun ha : a ≠ 0 => Set.finite_iUnion fun hb : b ≠ 0 =>
        Set.Finite.biUnion (t := fun 𝔪 => {p : Y | ∃ hpW : p ∈ W,
          ((hW a b ha hb).primeIdealOf ⟨p, hpW⟩).asIdeal.comap (φ a b ha hb) = 𝔪})
          (hF12 a b ha hb) fun 𝔪 _ => hone a b ha hb 𝔪).subset ?_
    rintro p ⟨a, b, ha, hb, hpW, hp⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨ha,
      Set.mem_iUnion.mpr ⟨hb, Set.mem_biUnion hp ⟨hpW, rfl⟩⟩⟩⟩⟩
  set v3 : Fin 3 → Fin (m + 1) → ℚ := Fin.snoc v2 c1
  have hv3 : LinearIndependent ℚ v3 := linearIndependent_finSnoc.mpr ⟨hv2, hc1span⟩
  obtain ⟨c3, hc3int, hc3span, hc3S⟩ := exists_intVec_notMem_of_finite
    (hSfin _ ((hTaff.union hT0).union hS3)) (hSprop _) _
    (span_range_ne_top v3 (by rw [hfinrank]; omega))
  set v4 : Fin 4 → Fin (m + 1) → ℚ := Fin.snoc v3 c3
  have hv4 : LinearIndependent ℚ v4 := linearIndependent_finSnoc.mpr ⟨hv3, hc3span⟩
  have hv4val : v4 0 = c0 ∧ v4 1 = c2 ∧ v4 2 = c1 ∧ v4 3 = c3 := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    exact Fin.snoc_last (α := fun _ => Fin (m + 1) → ℚ) (p := v3) c3
  have hv4int : ∀ i, IsIntVec (v4 i) := by
    intro i
    fin_cases i
    · exact hv4val.1 ▸ hc0int
    · exact hv4val.2.1 ▸ hc2int
    · exact hv4val.2.2.1 ▸ hc1int
    · exact hv4val.2.2.2 ▸ hc3int
  obtain ⟨w, hw, hwint, hwv, hwS⟩ := exists_linearIndependent_extend_int
    (hSfin _ (hTaff.union hT0)) (hSprop _) v4 hv4 hv4int (m + 1) (by omega) le_rfl
  set i1 : Fin (m + 1) := ⟨1, by omega⟩
  set i2 : Fin (m + 1) := ⟨2, by omega⟩
  set i3 : Fin (m + 1) := ⟨3, by omega⟩
  have hw0 : w 0 = c0 := (hwv (by omega) 0).trans hv4val.1
  have hw1 : w i1 = c2 := (hwv (by omega) 1).trans hv4val.2.1
  have hw2 : w i2 = c1 := (hwv (by omega) 2).trans hv4val.2.2.1
  have hw3 : w i3 = c3 := (hwv (by omega) 3).trans hv4val.2.2.2
  set perm : Equiv.Perm (Fin (m + 1)) := Equiv.swap i1 i2
  set row : Fin (m + 1) → Fin (m + 1) → ℚ := fun i => w (perm i) with hrowdef
  have hrow0 : row 0 = c0 := by
    change w (Equiv.swap i1 i2 0) = c0
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [i1, Fin.ext_iff]) (by simp [i2, Fin.ext_iff]), hw0]
  have hrow1 : ∀ i : Fin (m + 1), i.val = 1 → row i = c1 := by
    intro i hi
    have : i = i1 := Fin.ext hi
    subst this
    change w (Equiv.swap i1 i2 i1) = c1
    rw [Equiv.swap_apply_left, hw2]
  have hrow2 : ∀ i : Fin (m + 1), i.val = 2 → row i = c2 := by
    intro i hi
    have : i = i2 := Fin.ext hi
    subst this
    change w (Equiv.swap i1 i2 i2) = c2
    rw [Equiv.swap_apply_right, hw1]
  have hrow3 : row i3 = c3 := by
    change w (Equiv.swap i1 i2 i3) = c3
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [i1, i3, Fin.ext_iff])
      (by simp [i2, i3, Fin.ext_iff]), hw3]
  have hrowS : ∀ i : Fin (m + 1), i ≠ 0 → ∀ S ∈ Sp '' (Taff ∪ T0), row i ∉ S := by
    intro i hi S hS
    by_cases h4 : 4 ≤ (perm i).val
    · exact hwS (perm i) h4 S hS
    have hpi : perm i ≠ 0 := fun h => hi (by
      have := congrArg perm h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (by simp [i1, Fin.ext_iff])
        (by simp [i2, Fin.ext_iff])] at this)
    have hval : (perm i).val = 1 ∨ (perm i).val = 2 ∨ (perm i).val = 3 := by
      have : (perm i).val ≠ 0 := fun h => hpi (Fin.ext h)
      omega
    change w (perm i) ∉ S
    rcases hval with h | h | h
    · rw [show perm i = i1 from Fin.ext h, hw1]; exact hc2S S hS
    · rw [show perm i = i2 from Fin.ext h, hw2]
      exact hc1S S (Set.image_mono Set.subset_union_left hS)
    · rw [show perm i = i3 from Fin.ext h, hw3]
      exact hc3S S (Set.image_mono Set.subset_union_left hS)
  have hrowind : LinearIndependent ℚ row := hw.comp perm perm.injective
  have hrowint : ∀ i, IsIntVec (row i) := fun i => hwint (perm i)
  choose z hz using hrowint
  set g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of z with hgdef
  have hgrow : (fun i j => (g i j : ℚ)) = row := by
    funext i j
    rw [hz i]
    rfl
  have hunit := isUnit_map_intCast_of_linearIndependent g (hgrow ▸ hrowind) k
  set gk := g.map (Int.cast : ℤ → k) with hgkdef
  have hfy' : ∀ i, ∑ j, ((hunit.unit : Matrix.GeneralLinearGroup (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j • fy j = ℓ (row i) := by
    intro i
    rw [hℓdef, IsUnit.unit_spec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, ← hgrow]
    simp [hgkdef]
  refine ⟨hunit.unit, ?_⟩
  intro fy'
  have hfy'ℓ : ∀ i, fy' i = ℓ (row i) := hfy'
  have hfy'0 : fy' 0 = fy 0 := by rw [hfy'ℓ, hrow0, hℓe0]
  have hrow0' : ∀ i, row i ≠ 0 := hrowind.ne_zero
  have hy' : ∀ i, fy' i ≠ 0 := fun i => by rw [hfy'ℓ]; exact hℓ0 _ (hrow0' i)
  have hyli' : LinearIndependent k fy' := linearIndependent_sum_smul hfli hunit.unit
  have hspan_le : Submodule.span k (Set.range fy') ≤ Submodule.span k (Set.range fy) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : FiniteDimensional k (Submodule.span k (Set.range fy)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range fy)
  have hspan_eq : Submodule.span k (Set.range fy') = Submodule.span k (Set.range fy) :=
    Submodule.eq_of_le_of_finrank_eq hspan_le
      (by rw [finrank_span_eq_card hyli', finrank_span_eq_card hfli])
  have hspanrow : Submodule.span ℚ (Set.range row) = ⊤ :=
    hrowind.span_eq_top_of_card_eq_finrank (by simp)
  obtain ⟨φB', hci, hover, he, _hspan, hφBy'⟩ :=
    exists_isClosedImmersion_comp_eq_toProjectiveSpaceOver
    f pr₁ hkY fy (hfy 0) φB hφB hφBy hunit.unit (hy' 0)
  refine ⟨hy', fun i q => ?_, hyli', fun h hh => hspan_eq ▸ hfspan h hh, fun q hq => ?_,
    ⟨φB', hci, hover, he, hφBy'⟩, ?_, ?_, ?_, ?_⟩
  · rw [hfy'ℓ]
    exact hℓD _ (hℓ0 _ (hrow0' i)) q
  · by_contra hcon
    push Not at hcon
    apply hSp q
    rw [eq_top_iff, ← hspanrow, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_contra hi
    exact hcon i (by rw [hfy'ℓ]; exact ((hSpgood q) (row i) hi).2 q le_rfl hq)
  · intro a b ha hb i hi q q' hq hq'
    rw [hfy'ℓ] at hq
    rw [hfy'0] at hq'
    have hq1 := hsupp1 (row i) q hq
    have hqT0 : q ∉ T0 := fun h => hnotsupp (row i) _ (hrowS i hi) q hq (Or.inr h)
    obtain ⟨hrL, hrneg⟩ := hrr a b q' ha hb (hS01 q' hq')
    refine ⟨rr a b q', hrL, ?_, hrneg⟩
    by_contra hneg
    exact hqT0 ⟨hq1, a, b, q', hq', lt_of_not_ge hneg⟩
  · intro a b ha hb i j hi hj q q' hq hq'
    rw [hfy'ℓ, hrow1 i hi] at hq
    rw [hfy'ℓ, hrow2 j hj] at hq'
    obtain ⟨hq1, -, -, hqsep, hqW⟩ := hS1W q hq
    obtain ⟨hq'1, -, -, hq'W⟩ := hS2W q' hq'
    have := hWne a b ha hb
    obtain ⟨hG0, hGpos⟩ := hGG a b q' ha hb hq'1 (hq'W a b ha hb)
    obtain ⟨h, hhdef⟩ : ∃ h, h = MvPolynomial.aeval ![ι₁ (x a / x 0), ι₂ (x b / x 0)]
      (GG a b q') := ⟨_, rfl⟩
    rw [← hhdef] at hG0 hGpos
    refine ⟨h⁻¹, hhdef ▸ IntermediateField.inv_mem _ (hAL a b _), ?_, ?_⟩
    · rw [Stacks.Chow.ord_inv_functionField hG0]
      have hle : Y.ord h q ≤ 0 := by
        by_contra hpos
        exact hqsep ⟨hq1, a, b, q', hq', hhdef ▸ lt_of_not_ge hpos⟩
      have hge : 0 ≤ Y.ord h q := by
        refine (ord_nonneg_iff hq1 hG0).mpr ⟨Y.presheaf.germ W q (hqW a b ha hb)
          (φ a b ha hb (GG a b q')), ?_⟩
        rw [Scheme.algebraMap_germ_eq_germToFunctionField, hhdef]
        exact hφK a b ha hb _
      omega
    · rw [Stacks.Chow.ord_inv_functionField hG0]
      omega
  · intro a b ha hb i hi q hq
    rw [hfy'ℓ] at hq
    have hq1 := hsupp1 (row i) q hq
    have hqT : q ∉ Taff := fun h => hnotsupp (row i) _ (hrowS i hi) q hq (Or.inl h)
    exact haff q hq1 hqT a b ha hb
  · intro a b ha hb 𝔪 h𝔪
    have := hWne a b ha hb
    by_cases hF : 𝔪 ∈ F12 a b ha hb
    · refine ⟨i3, fun h => by simp [i3, Fin.ext_iff] at h, fun p hp q hqp hq1 => ?_⟩
      obtain ⟨hpW, hpeq⟩ := exists_mem_comap_eq (hW a b ha hb) (hφK a b ha hb) κ hκ
        (hWmem a b ha hb) h𝔪 hp
      have hpS3 : p ∈ S3 := ⟨a, b, ha, hb, hpW, hpeq ▸ hF⟩
      rw [hfy'ℓ, hrow3]
      exact ((hSpgood p) c3 (hc3S _ ⟨p, Or.inr hpS3, rfl⟩)).2 q hqp hq1
    · by_contra hcon
      push Not at hcon
      obtain ⟨p₁, hp₁, q₁, hq₁p, hq₁1, hne₁⟩ := hcon i1 (by simp [i1, Fin.ext_iff])
      obtain ⟨p₂, hp₂, q₂, hq₂p, hq₂1, hne₂⟩ := hcon i2 (by simp [i2, Fin.ext_iff])
      rw [hfy'ℓ, hrow1 i1 rfl] at hne₁
      rw [hfy'ℓ, hrow2 i2 rfl] at hne₂
      have hq₁S : q₁ ∈ S1 := lt_of_le_of_ne (hℓD c1 hc1ne q₁) hne₁.symm
      have hq₂S : q₂ ∈ S2 := lt_of_le_of_ne (hℓD c2 hc2ne q₂) hne₂.symm
      obtain ⟨hp₁W, hp₁eq⟩ := exists_mem_comap_eq (hW a b ha hb) (hφK a b ha hb) κ hκ
        (hWmem a b ha hb) h𝔪 hp₁
      obtain ⟨hp₂W, hp₂eq⟩ := exists_mem_comap_eq (hW a b ha hb) (hφK a b ha hb) κ hκ
        (hWmem a b ha hb) h𝔪 hp₂
      have hq₁W : q₁ ∈ W := (hS1W q₁ hq₁S).2.2.2.2 a b ha hb
      have hq₂W : q₂ ∈ W := (hS2W q₂ hq₂S).2.2.2 a b ha hb
      have hle₁ : P a b ha hb q₁ ≤ 𝔪 := by
        rw [hPeq a b ha hb q₁ hq₁W, ← hp₁eq]
        exact Ideal.comap_mono
          ((specializes_iff_primeIdealOf_le (hW a b ha hb) hq₁W hp₁W).mp hq₁p)
      have hle₂ : P a b ha hb q₂ ≤ 𝔪 := by
        rw [hPeq a b ha hb q₂ hq₂W, ← hp₂eq]
        exact Ideal.comap_mono
          ((specializes_iff_primeIdealOf_le (hW a b ha hb) hq₂W hp₂W).mp hq₂p)
      exact hF ⟨h𝔪, q₁, hq₁S, q₂, hq₂S, sup_le hle₁ hle₂⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **Generic coordinates for `φ_B` exist** (Bombieri). Let `X = (C, P)` be a smooth projective
geometrically integral curve of genus `≥ 2` over a number field `k` with a divisor `P` of degree
one, `Y = C ×_k C`, and `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` very ample, `s ≥ 1`, with a
basis `y` of `H⁰(Y, 𝒪(B))` giving the embedding `φB : Y ⟶ ℙᵐ_k`. Let `N ≥ 2g + 1`,
`n = N - g`, and `x` a generic basis of `H⁰(C, 𝒪(N P))` giving the embedding `φNP`. Then there
is `g ∈ GL_{m+1}(k)` such that the basis `y' i = ∑ j, g i j • y j` gives an embedding `φB'`
and is generic for the projections `π_{a'b'} = (ξ_{a'}, ξ'_{b'})`: (G1)–(G3) hold for every
`a', b' ≠ 0`. -/
@[faltings "lem_bvr_generic_b_coordinates"]
public theorem exists_isGenericForProjections_map {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f)
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      BombieriSiegel.IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f)) :
    ∃ g : Matrix.GeneralLinearGroup (Fin (m + 1)) k,
      let y' : Fin (m + 1) → (pullback X.f X.f).functionField := fun i =>
        ∑ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j • y j
      -- `y'` is a basis of `H⁰(𝒪(B))` without base points, giving an embedding `φ_B' = g ∘ φ_B`
      ∃ hy' : ∀ i, y' i ≠ 0,
      (∀ i q, 0 ≤ (pullback X.f X.f).ord (y' i) q + DB q) ∧
      LinearIndependent k y' ∧
      (∀ h : (pullback X.f X.f).functionField,
        (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y')) ∧
      (∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
        ∃ i, (pullback X.f X.f).ord (y' i) q + DB q = 0) ∧
      (∃ (φB' : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
        (_hφB' : φB' ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
          pullback.fst X.f X.f ≫ X.f)
        (_ : IsClosedImmersion φB')
        (hinv' : Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
          (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
              MvPolynomial.gradedAlgebra
           (Scheme.Modules.pullback φB').obj
              ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
                (ProjectiveSpectrum.Proj.twistingSheaf
                  (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))),
        Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
            (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
            (letI : GradedAlgebra
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
                MvPolynomial.gradedAlgebra
             (Scheme.Modules.pullback φB').obj
                ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
                  (ProjectiveSpectrum.Proj.twistingSheaf
                    (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
            ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
              _).mpr hinv') =
          X.vojtaClass sB sB (-1) ∧
        (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
            φB' =
          Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
            (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y' i))
            (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
              ((Ne.isUnit (hy' 0)).map
                (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
            ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f)) ∧
      -- (B): the coordinates `y'` are generic for every projection `π_{a'b'}`
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
        0 < (pullback X.f X.f).ord (y' i) q + DB q →
        0 < (pullback X.f X.f).ord (y' 0) q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
          0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
        i.val = 1 → i'.val = 2 → ∀ q q',
        0 < (pullback X.f X.f).ord (y' i) q + DB q →
        0 < (pullback X.f X.f).ord (y' i') q' + DB q' →
        ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
          0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
        0 < (pullback X.f X.f).ord (y' i) q + DB q →
        0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
        0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q) ∧
      (∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
        ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
        ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
          (∀ r ∈ 𝔪, r ≠ 0 →
            (∀ q, q ⤳ p → Order.coheight q = 1 →
              0 ≤ (pullback X.f X.f).ord
                (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
            ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
              0 < (pullback X.f X.f).ord
                (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
          ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y' i) q + DB q = 0) := by
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have hP₁cl : ∀ Q ∈ (X.P.mapDomain Subtype.val).support, IsClosed ({Q} : Set X.C) := by
    intro Q hQ
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hQ)
    exact c.2
  have hP₁ne : X.P.mapDomain Subtype.val ≠ 0 := by
    intro h
    have hP0 : X.P = 0 := Finsupp.mapDomain_injective Subtype.val_injective
      (h.trans Finsupp.mapDomain_zero.symm)
    have := X.degree_P
    rw [hP0, Finsupp.sum_zero_index] at this
    exact zero_ne_one this
  have hDB' : ∀ q, DB q =
      (sB + 1 : ℤ) * (X.P.mapDomain Subtype.val).sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c}) then a else 0) +
      (sB + 1 : ℤ) * (X.P.mapDomain Subtype.val).sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c}) then a else 0) -
      (if q = eΔ then 1 else 0) := by
    intro q
    rw [hDB q, Finsupp.sum_mapDomain_index (fun _ => by simp)
        (fun _ _ _ => by split_ifs <;> simp),
      Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  obtain ⟨g, hy', hyD', hyli', hyspan', hybpf', ⟨φB', hci, hover, ⟨e⟩, hφBy'⟩, hG1, hG1', hG2,
    hG3⟩ := exists_isGenericForProjections_map_aux k X.f _ hP₁cl hP₁ne
      (IsPullback.of_hasPullback X.f X.f) hkX ι₁.toRingHom ι₂.toRingHom hι₁ hι₂ N x hx φNP
      hφNPx sB DB hDB' y hy hyD hyli hyspan hybpf φB hφB hφBy
  have hinv' := Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso e.symm
  refine ⟨g, hy', hyD', hyli', hyspan', hybpf', ⟨φB', hover, hci, hinv', ?_, hφBy'⟩, hG1, hG1',
    hG2, hG3⟩
  rw [← hφBB]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr ⟨e⟩

end Faltings
