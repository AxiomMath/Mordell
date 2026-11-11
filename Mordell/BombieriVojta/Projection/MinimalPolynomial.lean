module

public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.AlgebraicGeometry.NormalScheme.Order

/-!
# The minimal polynomial of `ξ_j` over `k(ξ_a)`

Let `C` be a smooth projective geometrically irreducible curve of genus `g ≥ 2` over a number
field `k`, let `D` be a divisor of degree `N ≥ 2g + 1` supported on closed points (the source's
`N P`, with `P` of degree one), and let `x = (x₀, …, xₙ)` be a `k`-basis of the Riemann–Roch space
`L(D) = H⁰(C, 𝒪(D))` inside `k(C)`. Write `ξ_j = x_j / x₀`.
If `x` satisfies Bombieri's conditions (G1) and (G2), then for `a ≠ j` in `{1, …, n}` the function
`ξ_j` is integral over `k[ξ_a]`, and its minimal polynomial over `k(ξ_a)` is
`X^N - A_{N-1}(ξ_a) X^{N-1} - ⋯ - A₀(ξ_a)` with `A_i ∈ k[T]` of degree at most `N - i`.

Put `ξ = ξ_a` and `η = ξ_j`. At a closed point `Q` where `ξ` is regular, `x₀` does not vanish
as a section of `𝒪(D)` (by (G1)), so `η` is regular at `Q` as well. Every valuation ring of
`k(C)` containing `k[ξ]` is either `k(C)` or the local ring of `C` at a closed point, so `η` lies
in all of them, hence in the integral closure of `k[ξ]`. As `k[ξ] ≅ k[T]` is integrally closed
with fraction field `k(ξ)`, the minimal polynomial of `η` over `k(ξ)` has coefficients in `k[ξ]`,
and its degree is `[k(C) : k(ξ)] = N` by (G2) and `Faltings.BombieriSiegel.finrank_adjoin_div_eq`.

The roles of `x₀` and `x_a` in (G1) are symmetric, so the same argument applies to
`ξ⁻¹ = x₀ / x_a` and `η / ξ = x_j / x_a`: the minimal polynomial of `η / ξ` over
`k(ξ) = k(ξ⁻¹)`, which is the minimal polynomial of `η` with roots scaled by `ξ⁻¹`, has
coefficients in `k[ξ⁻¹]`. Comparing coefficients, the coefficient `A_i(ξ)` of `X^i` in the
minimal polynomial of `η` satisfies `A_i(ξ) ξ^{i - N} ∈ k[ξ⁻¹]`, that is `deg A_i ≤ N - i`.

## Main results

* `Faltings.BombieriSiegel.minpoly_div_eq_sub_sum`: the integrality of `ξ_j` over `k[ξ_a]` and
  the shape of its minimal polynomial over `k(ξ_a)`.

## Implementation notes

The source argues with the plane model `Γ ⊂ ℙ²` of `C` given by `(x₀ : x_a : x_j)`: the degree
bound comes from the homogeneity of an equation of `Γ` of degree `N`, and integrality from the
point `(0 : 0 : 1)` lying off `Γ`. Here both are read off valuations: integrality is the
regularity of `η` wherever `ξ` is regular, and the degree bound is the same statement for the
pair `(ξ⁻¹, η / ξ)`, which is the affine chart of `Γ` at `X₁ ≠ 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 629
-/

open AlgebraicGeometry CategoryTheory IntermediateField Polynomial

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriSiegel

section Algebra

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An element integral over the subalgebra `k[ζ]` is integral over the polynomial ring `k[X]`,
acting through `X ↦ ζ`. -/
private lemma isIntegral_polynomial_of_isIntegral_adjoin {ζ θ : K}
    (h : IsIntegral (Algebra.adjoin k {ζ}) θ) :
    letI : Algebra k[X] K := (aeval ζ).toRingHom.toAlgebra
    IsIntegral k[X] θ := by
  let : Algebra k[X] K := (aeval ζ).toRingHom.toAlgebra
  let g : Algebra.adjoin k {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton k ζ⟩
  let : Algebra k[X] (Algebra.adjoin k {ζ}) := (aeval g).toRingHom.toAlgebra
  have hg : ∀ p : k[X], ((aeval g p : Algebra.adjoin k {ζ}) : K) = aeval ζ p := fun p =>
    (Polynomial.aeval_algHom_apply (Algebra.adjoin k {ζ}).val g p).symm
  have : IsScalarTower k[X] (Algebra.adjoin k {ζ}) K :=
    IsScalarTower.of_algebraMap_eq fun p => (hg p).symm
  have : Algebra.IsIntegral k[X] (Algebra.adjoin k {ζ}) := by
    refine Algebra.IsIntegral.of_surjective (Algebra.ofId k[X] (Algebra.adjoin k {ζ})) ?_
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact ⟨p, Subtype.ext (hg p)⟩
  exact isIntegral_trans θ h

/-- If `ζ` is transcendental over `k` and `θ` is integral over `k[ζ]`, then `θ` is integral over
`k(ζ)` and its minimal polynomial there has coefficients `p_i(ζ)` with `p_i ∈ k[X]`. The field
`k(ζ)` is any intermediate field equal to `k⟮ζ⟯`. -/
private lemma exists_coeff_minpoly_eq {ζ θ : K} (hζ : Transcendental k ζ)
    (hθ : IsIntegral (Algebra.adjoin k {ζ}) θ) (E : IntermediateField k K) (hE : k⟮ζ⟯ = E) :
    IsIntegral E θ ∧ ∃ p : k[X][X], ∀ i, ((minpoly E θ).coeff i : K) = aeval ζ (p.coeff i) := by
  subst hE
  let : Algebra k[X] K := (aeval ζ).toRingHom.toAlgebra
  have hθ' := isIntegral_polynomial_of_isIntegral_adjoin hθ
  let : Algebra k[X] k⟮ζ⟯ := (aeval (AdjoinSimple.gen k ζ)).toRingHom.toAlgebra
  have hgen : ∀ p : k[X], ((aeval (AdjoinSimple.gen k ζ) p : k⟮ζ⟯) : K) = aeval ζ p := fun p =>
    (Polynomial.aeval_algHom_apply k⟮ζ⟯.val (AdjoinSimple.gen k ζ) p).symm
  have : IsScalarTower k[X] k⟮ζ⟯ K := IsScalarTower.of_algebraMap_eq fun p => (hgen p).symm
  have : IsFractionRing k[X] k⟮ζ⟯ := by
    let e := RatFunc.algEquivOfTranscendental ζ hζ
    let e' : RatFunc k ≃ₐ[k[X]] k⟮ζ⟯ := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun p => by
      change e (algebraMap k[X] (RatFunc k) p) = _
      rw [RatFunc.algEquivOfTranscendental_algebraMap]
      rfl
    exact IsLocalization.isLocalization_of_algEquiv _ e'
  refine ⟨hθ'.tower_top, minpoly k[X] θ, fun i => ?_⟩
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' k⟮ζ⟯ hθ', coeff_map]
  exact hgen _

/-- If `ζ` is transcendental and `q(ζ) ζ^{-m} = q'(ζ⁻¹)` for polynomials `q`, `q'`, then
`deg q ≤ m`. -/
private lemma natDegree_le_of_aeval_mul_inv_pow_eq {ζ : K} (hζ : Transcendental k ζ)
    {q q' : k[X]} {m : ℕ} (h : aeval ζ q * ζ⁻¹ ^ m = aeval ζ⁻¹ q') : q.natDegree ≤ m := by
  have hζ0 : ζ ≠ 0 := fun h0 => hζ (h0 ▸ isAlgebraic_zero)
  let : Invertible ζ⁻¹ := invertibleOfNonzero (inv_ne_zero hζ0)
  have h1 := eval₂_reflect_mul_pow (algebraMap k K) ζ⁻¹ q'.natDegree q' le_rfl
  rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def, ← h] at h1
  have key : aeval ζ (q * Polynomial.X ^ q'.natDegree) =
      aeval ζ (reflect q'.natDegree q' * Polynomial.X ^ m) := by
    simp only [map_mul, map_pow, aeval_X]
    calc aeval ζ q * ζ ^ q'.natDegree
        = aeval ζ q * ζ⁻¹ ^ m * (ζ ^ q'.natDegree * ζ ^ m) := by
          rw [inv_pow]; field_simp
      _ = aeval ζ (reflect q'.natDegree q') * ζ⁻¹ ^ q'.natDegree *
            (ζ ^ q'.natDegree * ζ ^ m) := by
          rw [h1]
      _ = _ := by rw [inv_pow]; field_simp
  have hinj := (transcendental_iff_injective).1 hζ key
  by_cases hq : q = 0
  · simp [hq]
  have := congrArg natDegree hinj
  rw [natDegree_mul_X_pow _ hq] at this
  have h2 : (reflect q'.natDegree q' * Polynomial.X ^ m).natDegree ≤ q'.natDegree + m :=
    (natDegree_mul_le).trans (add_le_add ((natDegree_reflect_le).trans (by simp))
      (natDegree_X_pow_le m))
  omega

/-- Homogeneity of the minimal polynomial: if `ζ` is transcendental over `k`, `θ` is integral over
`k[ζ]` and `θ / ζ` is integral over `k[ζ⁻¹]`, then the coefficient of `X^i` in the minimal
polynomial of `θ` over `k(ζ)`, of degree `d`, is `p_i(ζ)` with `p_i ∈ k[X]` of degree `≤ d - i`.
The minimal polynomial of `θ / ζ` over `k(ζ) = k(ζ⁻¹)` is that of `θ` with roots scaled by `ζ⁻¹`,
so `p_i(ζ) ζ^{i - d}` is a polynomial in `ζ⁻¹`. -/
private lemma exists_coeff_minpoly_natDegree_le {ζ θ : K} (hζ : Transcendental k ζ)
    (h₀ : IsIntegral (Algebra.adjoin k {ζ}) θ) (h₁ : IsIntegral (Algebra.adjoin k {ζ⁻¹}) (θ / ζ)) :
    ∃ p : k[X][X], ∀ i, ((minpoly k⟮ζ⟯ θ).coeff i : K) = aeval ζ (p.coeff i) ∧
      (p.coeff i).natDegree ≤ (minpoly k⟮ζ⟯ θ).natDegree - i := by
  have hζ0 : AdjoinSimple.gen k ζ ≠ 0 := fun h0 =>
    hζ (by rw [show ζ = 0 from congrArg Subtype.val h0]; exact isAlgebraic_zero)
  have hE : k⟮ζ⁻¹⟯ = k⟮ζ⟯ := le_antisymm
    (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self k ζ)))
    (adjoin_simple_le_iff.2 (by simpa using inv_mem (mem_adjoin_simple_self k ζ⁻¹)))
  obtain ⟨hθ, p, hp⟩ := exists_coeff_minpoly_eq hζ h₀ _ rfl
  obtain ⟨-, p', hp'⟩ :=
    exists_coeff_minpoly_eq (fun h => hζ (IsAlgebraic.inv_iff.1 h)) h₁ _ hE
  haveI : Module.IsTorsionFree k⟮ζ⟯ K := DivisionSemiring.to_moduleIsTorsionFree
  have hscale : minpoly k⟮ζ⟯ (θ / ζ) = (minpoly k⟮ζ⟯ θ).scaleRoots (AdjoinSimple.gen k ζ)⁻¹ := by
    rw [← IsIntegrallyClosed.minpoly_smul (inv_ne_zero hζ0) hθ, Algebra.smul_def,
      div_eq_inv_mul]
    rfl
  refine ⟨p, fun i => ⟨hp i, natDegree_le_of_aeval_mul_inv_pow_eq hζ (q' := p'.coeff i) ?_⟩⟩
  rw [← hp, ← hp', hscale, coeff_scaleRoots, IntermediateField.coe_mul,
    IntermediateField.coe_pow, IntermediateField.coe_inv, AdjoinSimple.coe_gen]

/-- An element lying in every valuation subring of `K` that contains a subalgebra `A` is integral
over `A`. -/
private lemma isIntegral_of_forall_valuationSubring {A : Subalgebra k K} {η : K}
    (h : ∀ V : ValuationSubring K, (A : Set K) ⊆ V → η ∈ V) : IsIntegral A η := by
  have hmem : η ∈ (integralClosure (Subring.closure (A : Set K)) K).toSubring := by
    rw [← iInf_valuationSubring_superset]
    exact Subring.mem_iInf.2 fun V => h V.1 V.2
  have hle : Subring.closure (A : Set K) ≤ A.toSubring := Subring.closure_le.2 fun _ hy => hy
  let φ : Subring.closure (A : Set K) →+* A :=
    (Subring.closure _).subtype.codRestrict A fun y => hle y.2
  exact IsIntegral.map_of_comp_eq φ (RingHom.id _) (RingHom.ext fun _ => rfl) hmem

end Algebra

section Order

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]

/-- Let `g, h, e` lie in `L(D)` at `Q`, with `g` and `h` not both vanishing there as sections
of `𝒪(D)`. If `h / g` is regular at `Q`, then so is `e / g`: the section `g` does not vanish at
`Q`. -/
private lemma ord_div_nonneg_of_ord_div_nonneg {g h e : C.functionField} (hg : g ≠ 0)
    (hh : h ≠ 0) (he : e ≠ 0) {Q : C} {d : ℤ} (hgd : 0 ≤ C.ord g Q + d) (hhd : 0 ≤ C.ord h Q + d)
    (hed : 0 ≤ C.ord e Q + d) (hgh : ¬(0 < C.ord g Q + d ∧ 0 < C.ord h Q + d))
    (hQ : 0 ≤ C.ord (h / g) Q) : 0 ≤ C.ord (e / g) Q := by
  rw [ord_div hh hg] at hQ
  rw [ord_div he hg]
  omega

end Order

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]

variable [IsLocallyNoetherian C]

/-- A rational function lies in the local ring of a smooth curve at a non-generic point `Q` iff
its order at `Q` is non-negative. -/
public lemma mem_range_stalk_iff [Smooth f] {Q : C} (hQg : Q ≠ genericPoint C)
    (g : C.functionField) :
    g ∈ Set.range (algebraMap (C.presheaf.stalk Q) C.functionField) ↔ 0 ≤ C.ord g Q := by
  have : IsNormal C := isNormal_of_smooth_over_field f
  by_cases hg : g = 0
  · subst hg
    exact ⟨fun _ => by simp, fun _ => ⟨0, map_zero _⟩⟩
  exact (ord_nonneg_iff (IsCurve.coheight_eq_one f hQg) hg).symm

/-- On a smooth proper curve, a function `η` regular at every closed point where the
transcendental function `ξ` is regular is integral over `k[ξ]`. -/
public lemma isIntegral_adjoin_of_ord_nonneg [PerfectField k] [Smooth f] [IsProper f]
    {ξ η : C.functionField} (hξ : letI := functionFieldAlgebra k f; Transcendental k ξ)
    (h : ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord ξ Q → 0 ≤ C.ord η Q) :
    letI := functionFieldAlgebra k f
    IsIntegral (Algebra.adjoin k {ξ}) η := by
  let := functionFieldAlgebra k f
  let := Stacks.Drinfeld.ratFuncAlgebra hξ
  have := Stacks.Drinfeld.isScalarTower_ratFuncAlgebra hξ
  have : Algebra.EssFiniteType k C.functionField := Stacks.Zeta.essFiniteType_ffAlg f
  have : FunctionField k C.functionField := Stacks.Drinfeld.functionField_of_trdeg_eq_one
    (IntermediateField.fg_top _ _) (Faltings.trdeg_functionField_eq_one k f) hξ
  have : IsNormal C := Faltings.FunctionField.isNormal_of_smooth k f
  refine isIntegral_of_forall_valuationSubring fun V hV => ?_
  have hk : ∀ c : k, algebraMap k C.functionField c ∈ V := fun c =>
    hV (Subalgebra.algebraMap_mem _ c)
  have hξV : ξ ∈ V := hV (Algebra.self_mem_adjoin_singleton k ξ)
  by_cases htop : ∀ y, y ∈ V
  · exact htop η
  push Not at htop
  obtain ⟨y, hy⟩ := htop
  let w : Faltings.Place k C.functionField :=
    { toSubalgebra := { V.toSubring with algebraMap_mem' := hk }
      neg_mem' := fun hx => V.neg_mem _ hx
      mem_or_inv_mem' := V.mem_or_inv_mem
      ne_top := fun h' => hy (by
        have : y ∈ (⊤ : Subalgebra k C.functionField) := Algebra.mem_top
        rw [← h'] at this
        exact this) }
  obtain ⟨Q, ⟨hQ, hwQ⟩, -⟩ := Faltings.FunctionField.existsUnique_isClosed_place_eq_image_stalk
    k C.functionField f AlgEquiv.refl w
  have hV' : ∀ z, z ∈ V ↔ z ∈ Set.range (algebraMap (C.presheaf.stalk Q) C.functionField) :=
    fun z => by simpa [w] using Set.ext_iff.1 hwQ z
  rw [hV']
  by_cases hQg : Q = genericPoint C
  · subst hQg
    refine ⟨η, ?_⟩
    change (C.presheaf.stalkSpecializes _).hom η = η
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  exact (mem_range_stalk_iff f hQg η).2
    (h Q hQ ((mem_range_stalk_iff f hQg ξ).1 ((hV' ξ).1 hξV)))

end Curve

/-- Let `D` be a divisor of degree `N ≥ 2g + 1` supported on closed points of a curve `C` of genus
`g ≥ 2` over a number field `k`, let `x₀, …, xₙ` be a `k`-basis of the Riemann–Roch space
`L(D)` satisfying (G1) and (G2), and put `ξ_ν = x_ν / x₀`. For `a ≠ j` in `{1, …, n}`, `ξ_j` is
integral over `k[ξ_a]`, and its minimal polynomial over `k(ξ_a)` is `X^N - ∑_{i < N} A_i(ξ_a) X^i`
for polynomials `A_i ∈ k[T]` with `deg A_i ≤ N - i`. -/
@[faltings "lem_bvs_minimal_polynomial"]
public theorem minpoly_div_eq_sub_sum (k : Type u) [Field k] [NumberField k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]
    [IsProjectiveVariety k f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hlin : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x)
    (hG2 : SatisfiesG2 k f x)
    {a j : Fin (n + 1)} (ha : a ≠ 0) (hj : j ≠ 0) (haj : a ≠ j) :
    letI := functionFieldAlgebra k f
    IsIntegral (Algebra.adjoin k {x a / x 0}) (x j / x 0) ∧
      ∃ A : Fin N → k[X], (∀ i, (A i).natDegree ≤ N - i) ∧
        minpoly k⟮x a / x 0⟯ (x j / x 0) =
          Polynomial.X ^ N - ∑ i : Fin N,
            Polynomial.C (aeval (AdjoinSimple.gen k (x a / x 0)) (A i)) *
              Polynomial.X ^ (i : ℕ) := by
  classical
  let := functionFieldAlgebra k f
  have hmem : ∀ i Q, IsClosed ({Q} : Set C) → 0 ≤ C.ord (x i) Q + D Q := fun i =>
    ((Set.ext_iff.1 hspan (x i)).1 (Submodule.subset_span ⟨i, rfl⟩)).resolve_left (hlin.ne_zero i)
  have hx0 : ∀ i, x i ≠ 0 := hlin.ne_zero
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, x a / x 0 = ξ := ⟨_, rfl⟩
  obtain ⟨η, hηdef⟩ : ∃ η, x j / x 0 = η := ⟨_, rfl⟩
  rw [hξdef, hηdef]
  have : GeometricallyIntegral f := .of_geometricallyReduced_of_geometricallyIrreducible _
  have hT : Transcendental k ξ := FunctionField.transcendental_of_notMem_range f
    (hξdef ▸ div_notMem_range_algebraMap hlin ha)
  have hint := isIntegral_adjoin_of_ord_nonneg f hT (η := η) fun Q hQ h => by
    rw [← hξdef] at h
    rw [← hηdef]
    exact ord_div_nonneg_of_ord_div_nonneg (hx0 0) (hx0 a) (hx0 j) (hmem 0 Q hQ) (hmem a Q hQ)
      (hmem j Q hQ) (hG1 a ha Q hQ) h
  have hint' := isIntegral_adjoin_of_ord_nonneg f (fun h => hT (IsAlgebraic.inv_iff.1 h))
    (η := η / ξ) fun Q hQ h => by
    rw [← hξdef, inv_div] at h
    rw [← hξdef, ← hηdef, div_div_div_cancel_right₀ (hx0 0)]
    exact ord_div_nonneg_of_ord_div_nonneg (hx0 a) (hx0 0) (hx0 j) (hmem a Q hQ) (hmem 0 Q hQ)
      (hmem j Q hQ) (fun h => hG1 a ha Q hQ h.symm) h
  refine ⟨hint, ?_⟩
  have hfin : Module.finrank k⟮ξ⟯ C.functionField = N :=
    hξdef ▸ finrank_adjoin_div_eq k f hg D hDcl N hN hD x hlin hspan hG1 a ha
  have : FiniteDimensional k⟮ξ⟯ C.functionField := .of_finrank_pos (by omega)
  have hadj : k⟮ξ⟯⟮η⟯ = ⊤ := by
    apply restrictScalars_injective k
    rw [adjoin_simple_adjoin_simple, restrictScalars_top, ← hξdef, ← hηdef]
    exact hG2 a j ha hj haj
  have hηint : IsIntegral k⟮ξ⟯ η := .of_finite _ _
  have hdeg : (minpoly k⟮ξ⟯ η).natDegree = N := by
    rw [← adjoin.finrank hηint, hadj, finrank_top', hfin]
  obtain ⟨p, hp⟩ := exists_coeff_minpoly_natDegree_le hT hint hint'
  refine ⟨fun i => -p.coeff i, fun i => by simpa [hdeg] using (hp i).2, ?_⟩
  rw [(minpoly.monic hηint).as_sum, hdeg,
    ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((minpoly k⟮ξ⟯ η).coeff i) *
      Polynomial.X ^ i) N, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← neg_mul, ← Polynomial.C_neg]
  congr 2
  apply Subtype.ext
  simp only [(hp i).1, map_neg, neg_neg]
  exact aeval_algHom_apply k⟮ξ⟯.val (AdjoinSimple.gen k ξ) _

end Faltings.BombieriSiegel
