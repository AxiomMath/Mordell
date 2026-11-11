module
public import Mordell.BombieriVojta.SmallSection.U1
public import Mordell.BombieriVojta.SmallSection.DimU0
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.BombieriVojta.Projection.MonomialBasis
public import Mordell.BombieriVojta.SmallSection.DimU1

/-!
# The codimension of `U₁` in `U₀`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one, `N ≥ 2g + 1`, `n = N - g`, and `x = (x₀, …, xₙ)` a `k`-basis
of `H⁰(C, 𝒪(NP))` satisfying (G1) and (G2), defining the closed immersion `φ_{NP} : C → ℙⁿ`, with
`ψ = φ_{NP} × φ_{NP}`. Let `δ₁, δ₂ ≥ N - 1` be such that every global section of
`ψ^*𝒪(δ₁, δ₂)` is the restriction of a bihomogeneous form of bidegree `(δ₁, δ₂)` over `k` (this
holds for `δ₁, δ₂ ≥ δ₀`), and `N δ₁, N δ₂ > 2g - 2`. Then the space `U₁` of tuples of
`k`-linear combinations of the monomials `ξ_a^l ξ_a'^{l'} b_ν` has codimension at most
`(m + 1)(N³(δ₁ + δ₂)/2 + (g - 1)²)` in the space `U₀` of tuples `(F_i(ξ, ξ'))_{i=0}^m`.

This is the difference of the dimension of `U₀`,
`(m + 1)(N²δ₁δ₂ - N(g - 1)(δ₁ + δ₂) + (g - 1)²)`, and that of `U₁`,
`(m + 1)(N²δ₁δ₂ - N²(N - 3)(δ₁ + δ₂)/2 + (N(N - 3)/2)²)`.

The bound on `dim U₁` from below rests on the linear independence of the monomials
`ξ_a^l ξ_a'^{l'} ξ_b^i ξ_b'^{i'}`, proved in three steps.

* Under (G1), `[k(C) : k(ξ_a)] = N` for `ξ_a = ℓ_a / ℓ₀`, `a ≠ 0`: the divisor of zeros of
  `ξ_a` is `div(ℓ_a) + NP`, of degree `N deg P = N`.
* With (G2), `k(C) = k(ξ_a, ξ_b)`, so `1, ξ_b, …, ξ_b^{N-1}` is a basis of `k(C)` over `k(ξ_a)`;
  as `ξ_a` is transcendental over `k`, the products `ξ_a^l ξ_b^i` (`l ≥ 0`, `i < N`) are
  linearly independent over `k`.
* `k(C)` and `k(C)` are linearly disjoint in `k(C × C)`: the map `k(C) ⊗_k k(C) → k(C × C)`
  is injective, so products `pr₁^* u · pr₂^* v` of independent families are independent.

## Main results

* `Faltings.BombieriVojta.finrank_affineEvaluationTuples_sub_finrank_monomial_le`: the bound
  `dim U₀ - dim U₁ ≤ (m + 1)(N³(δ₁ + δ₂)/2 + (g - 1)²)`.

## Implementation notes

* The setting is that of `Faltings.BombieriVojta.finrank_affineEvaluationTuples`: `C × C` is
  `pullback f f` over `Spec k`, `pr₁^*, pr₂^*` are `AlgebraicGeometry.functionFieldMapAlgHom` of
  the two projections, and `δ₀` enters only through its defining property at `(δ₁, δ₂)`, the
  surjectivity of `Faltings.vojtaFormRestriction`.
* The affine coordinates are taken in the chart `x₀ ≠ 0`, the one in which (G1) is phrased. The
  coordinates `ξ₁, ξ₂` of the source are `x a / x₀`, `x b / x₀` for arbitrary distinct nonzero
  indices `a`, `b`; the source's case is `a = 1`, `b = 2`.
* The difference of dimensions is computed in `ℚ`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 631
-/

open Faltings.BombieriSiegel (div_notMem_range_algebraMap exists_basis_pow_of_adjoin_eq_top
  finrank_adjoin_div_eq finsum_smul_mul_residueDegree isClosed_of_mem_support_smul)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module IntermediateField
open scoped TensorProduct

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriVojta

universe u

/-! ### Independence of `ξ_a^l ξ_b^i` in `k(C)` -/

section FieldIndependence

/-- If `K = k(ξ, η)` has degree `N > 0` over `k(ξ)` and `ξ` is transcendental over `k`, the
products `ξ^l η^i` (`l ∈ ℕ`, `i < N`) are linearly independent over `k`. -/
private theorem linearIndependent_pow_mul_pow_of_adjoin_eq_top {k K : Type*} [Field k] [Field K]
    [Algebra k K] {ξ η : K} (hT : Transcendental k ξ) (hst : k⟮ξ, η⟯ = ⊤) {N : ℕ} (hN : 0 < N)
    (hdeg : Module.finrank k⟮ξ⟯ K = N) :
    LinearIndependent k fun p : ℕ × Fin N => ξ ^ p.1 * η ^ (p.2 : ℕ) := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_adjoin_eq_top hst hN hdeg
  have hξ : ξ ∈ k⟮ξ⟯ := mem_adjoin_simple_self k ξ
  let w : ℕ → k⟮ξ⟯ := fun l => ⟨ξ ^ l, pow_mem hξ l⟩
  have hpow : LinearIndependent k fun l : ℕ => ξ ^ l := by
    have := (Polynomial.basisMonomials k).linearIndependent.map' (Polynomial.aeval ξ).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hT))
    have e : (⇑(Polynomial.aeval (R := k) ξ).toLinearMap ∘ ⇑(Polynomial.basisMonomials k)) =
        fun l : ℕ => ξ ^ l := by
      funext l
      simp
    rwa [e] at this
  have hw : LinearIndependent k w := .of_comp (IsScalarTower.toAlgHom k k⟮ξ⟯ K).toLinearMap hpow
  convert linearIndependent_smul hw e.linearIndependent using 1
  funext p
  simp [w, he, Algebra.smul_def]

end FieldIndependence

/-! ### `k(C)` and `k(C)` are linearly disjoint in `k(C × C)` -/

section Disjoint

/-- The ring of an affine open `U` of `C`, as a `k`-algebra through `f`. -/
private noncomputable abbrev affineAlgebra (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (U : C.Opens) : Algebra k Γ(C, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- If `C ×_k C` is integral, then `Γ(U) ⊗_k Γ(U)` is a domain for every nonempty affine open `U`
of `C`: it is the ring of the nonempty open `U ×_k U` of `C ×_k C`. -/
private theorem isDomain_tensorProduct_of_isAffineOpen (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)] {U : C.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := affineAlgebra k f U
    IsDomain (Γ(C, U) ⊗[k] Γ(C, U)) := by
  letI := affineAlgebra k f U
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, U))) = hU.fromSpec ≫ f := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, ← Spec.map_comp]
    rfl
  let g : Spec (.of Γ(C, U)) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Γ(C, U)))
  let ι : (pullback g g : Scheme.{u}) ⟶ pullback f f :=
    pullback.map g g f f hU.fromSpec hU.fromSpec (𝟙 _)
      (by rw [Category.comp_id]; exact hφ) (by rw [Category.comp_id]; exact hφ)
  haveI : Nontrivial (Γ(C, U) ⊗[k] Γ(C, U)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (RingHom.injective _) (RingHom.injective _)
  haveI : Nonempty (pullback g g : Scheme.{u}) :=
    ⟨(pullbackSpecIso k Γ(C, U) Γ(C, U)).inv.base (Nonempty.some inferInstance)⟩
  haveI := isIntegral_of_isOpenImmersion ι
  haveI : IsIntegral (Spec (.of (Γ(C, U) ⊗[k] Γ(C, U)))) :=
    IsIntegral.of_isIso (pullbackSpecIso k Γ(C, U) Γ(C, U)).hom
  exact (affine_isIntegral_iff (.of (Γ(C, U) ⊗[k] Γ(C, U)))).mp inferInstance

/-- If `A ⊗_k A` is a domain, so is `K ⊗_k K` for the fraction field `K` of `A`. -/
private theorem isDomain_tensorProduct_of_isFractionRing {k A K : Type*} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] (hA : IsDomain (A ⊗[k] A)) : IsDomain (K ⊗[k] K) := by
  classical
  let ι : A ⊗[k] A →ₐ[k] K ⊗[k] K :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A K) (IsScalarTower.toAlgHom k A K)
  have hι : Function.Injective ι :=
    TensorProduct.map_injective_of_flat_flat (IsScalarTower.toAlgHom k A K).toLinearMap
      (IsScalarTower.toAlgHom k A K).toLinearMap (IsFractionRing.injective A K)
      (IsFractionRing.injective A K)
  have hne : ∀ s : nonZeroDivisors A, algebraMap A K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hden : ∀ z : K ⊗[k] K, ∃ (s t : nonZeroDivisors A) (w : A ⊗[k] A),
      z * (algebraMap A K s ⊗ₜ algebraMap A K t) = ι w := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, 1, 0, by simp⟩
    | tmul a b =>
      obtain ⟨x, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) a
      obtain ⟨y, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      refine ⟨⟨s, hs⟩, ⟨t, ht⟩, x ⊗ₜ y, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, div_mul_cancel₀ _ (hne ⟨s, hs⟩),
        div_mul_cancel₀ _ (hne ⟨t, ht⟩)]
      rfl
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨s₁, t₁, w₁, hw₁⟩ := h₁
      obtain ⟨s₂, t₂, w₂, hw₂⟩ := h₂
      refine ⟨s₁ * s₂, t₁ * t₂, w₁ * ((s₂ : A) ⊗ₜ (t₂ : A)) + w₂ * ((s₁ : A) ⊗ₜ (t₁ : A)), ?_⟩
      have e : ∀ (s t : nonZeroDivisors A), ι ((s : A) ⊗ₜ (t : A)) =
          algebraMap A K s ⊗ₜ algebraMap A K t := fun _ _ => rfl
      rw [map_add, map_mul, map_mul, e, e, ← hw₁, ← hw₂, Submonoid.coe_mul, Submonoid.coe_mul,
        map_mul, map_mul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
  have hunit : ∀ s t : nonZeroDivisors A, IsUnit (algebraMap A K s ⊗ₜ[k] algebraMap A K t) :=
    fun s t => IsUnit.of_mul_eq_one ((algebraMap A K s)⁻¹ ⊗ₜ (algebraMap A K t)⁻¹) (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hne s), mul_inv_cancel₀ (hne t),
        Algebra.TensorProduct.one_def])
  haveI : Nontrivial (K ⊗[k] K) := hι.nontrivial
  haveI : NoZeroDivisors (K ⊗[k] K) := ⟨fun {z z'} h => by
    obtain ⟨s, t, w, hw⟩ := hden z
    obtain ⟨s', t', w', hw'⟩ := hden z'
    have h0 : ι (w * w') = 0 := by
      rw [map_mul, ← hw, ← hw', mul_mul_mul_comm, h, zero_mul]
    rcases mul_eq_zero.mp (hι (h0.trans (map_zero ι).symm)) with h1 | h1
    · left
      rw [h1, map_zero] at hw
      exact (hunit s t).mul_left_eq_zero.mp hw
    · right
      rw [h1, map_zero] at hw'
      exact (hunit s' t').mul_left_eq_zero.mp hw'⟩
  exact NoZeroDivisors.to_isDomain _

/-- Two additive maps out of a tensor product that agree on pure tensors are equal. -/
private theorem tensorProduct_coe_ext {R A B S F G : Type*} [CommSemiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [AddCommMonoid S] [FunLike F (A ⊗[R] B) S]
    [FunLike G (A ⊗[R] B) S] [AddMonoidHomClass F (A ⊗[R] B) S] [AddMonoidHomClass G (A ⊗[R] B) S]
    (f : F) (g : G) (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : ⇑f = ⇑g := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If `k(C) ⊗_k k(C)` is a domain, then `a ⊗ b ↦ pr₁^* a · pr₂^* b` is injective: the local
ring of `C ×_k C` at its generic point is a localization of `k(C) ⊗_k k(C)` at a prime. -/
private theorem injective_lift_functionFieldMapAlgHom (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)]
    [IsDominant (pullback.fst f f)] [IsDominant (pullback.snd f f)]
    (hdom : letI := stalkAlgebraOver k f (genericPoint C)
      IsDomain (C.functionField ⊗[k] C.functionField)) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    Function.Injective (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)) := by
  letI := stalkAlgebraOver k f (genericPoint C)
  letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  have hx : pullback.fst f f (genericPoint (pullback f f : Scheme.{u})) = genericPoint C :=
    map_genericPoint_of_isDominant _
  have hy : pullback.snd f f (genericPoint (pullback f f : Scheme.{u})) = genericPoint C :=
    map_genericPoint_of_isDominant _
  obtain ⟨ψ₀, h₁, h₂, hloc₀⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct k f f
      (genericPoint (pullback f f : Scheme.{u}))
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensor_stalk_transport₂ k f f _ _ _ _ hx hy ψ₀ hloc₀
  have hψψ : ψ = (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)).toRingHom := by
    refine DFunLike.ext' (tensorProduct_coe_ext _ _ fun a b => ?_)
    rw [hψ, h₁, h₂]
    rfl
  have hinj : Function.Injective ψ := by
    letI := ψ.toAlgebra
    haveI := hloc
    exact IsLocalization.injective (M := (Ideal.comap ψ
      (IsLocalRing.maximalIdeal (pullback f f : Scheme.{u}).functionField)).primeCompl)
      (pullback f f : Scheme.{u}).functionField (Ideal.primeCompl_le_nonZeroDivisors _)
  rwa [hψψ] at hinj

/-- **`k(C)` and `k(C)` are linearly disjoint in `k(C × C)`**: products of `k`-linearly
independent families pulled back along the two projections are `k`-linearly independent. -/
private theorem linearIndependent_mul_functionFieldMap (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] [IsIntegral (pullback f f)]
    {ι κ : Type*} (a : ι → C.functionField) (b : κ → C.functionField) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    LinearIndependent k a → LinearIndependent k b →
      LinearIndependent k (fun pq : ι × κ =>
        functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl (a pq.1) *
          functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
            pullback.condition.symm (b pq.2)) := by
  letI := stalkAlgebraOver k f (genericPoint C)
  letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro ha hb
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint C)) isOpen_univ
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  letI := affineAlgebra k f U
  haveI : IsScalarTower k Γ(C, U) C.functionField := .of_algebraMap_eq fun c => by
    change C.presheaf.germ ⊤ (genericPoint C) trivial
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) =
      C.presheaf.germ U (genericPoint C) hηU
        (C.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  haveI := functionField_isFractionRing_of_isAffineOpen C U hU
  have hK := isDomain_tensorProduct_of_isFractionRing (A := Γ(C, U)) (K := C.functionField)
    (isDomain_tensorProduct_of_isAffineOpen k f hU)
  have hinj := injective_lift_functionFieldMapAlgHom k f hK
  haveI : Module.Free k C.functionField := Module.Free.of_divisionRing k _
  haveI : Module.Flat k C.functionField := Module.Flat.of_free
  exact (ha.tmul_of_flat_left hb).map' (Algebra.TensorProduct.lift
      (functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl)
      (functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm) (fun _ _ => Commute.all _ _)).toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)

end Disjoint

/-! ### The monomials spanning `U₁` -/

section Monomials

/-- The monomials `(pr₁ ξ)^l (pr₂ ξ)^{l'} b_ν`, `b_ν = (pr₁ η)^i (pr₂ η)^{i'}`, are linearly
independent as soon as the products `pr₁ (ξ^l η^i) · pr₂ (ξ^{l'} η^{i'})` over all `l, l' ∈ ℕ`,
`i, i' < N` are: the two families are the same up to reindexing. -/
private lemma linearIndependent_pow_mul_pow_mul_basisB_of_mul {k K L : Type*} [Field k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (ξ η : K) (N : ℕ)
    (h : LinearIndependent k fun pq : (ℕ × Fin N) × (ℕ × Fin N) =>
      pr₁ (ξ ^ pq.1.1 * η ^ (pq.1.2 : ℕ)) * pr₂ (ξ ^ pq.2.1 * η ^ (pq.2.2 : ℕ))) :
    LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ ξ ^ t.1 * pr₂ ξ ^ t.2.1 * Faltings.BombieriSiegel.basisB pr₁ pr₂ η t.2.2 := by
  let e : ℕ × ℕ × (Fin N × Fin N) → (ℕ × Fin N) × (ℕ × Fin N) := fun t =>
    ((t.1, t.2.2.1), (t.2.1, t.2.2.2))
  have he : Function.Injective e := by
    rintro ⟨l, l', i, i'⟩ ⟨m, m', j, j'⟩ h
    simp only [e, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    rfl
  convert h.comp e he using 1
  funext t
  simp only [Faltings.BombieriSiegel.basisB, Function.comp_apply, e, map_mul, map_pow]
  ring

end Monomials

/-- The arithmetic of the bound: `(N²δ₁δ₂ - N(g - 1)(δ₁ + δ₂) + (g - 1)²) -
(Nδ₁ - N(N - 3)/2)(Nδ₂ - N(N - 3)/2) ≤ N³(δ₁ + δ₂)/2 + (g - 1)²`, scaled by `m ≥ 0`. -/
private lemma dim_sub_dim_le (m N δ₁ δ₂ g : ℚ) (hm : 0 ≤ m) (hg : 1 ≤ g) (hN : 0 ≤ N)
    (hδ : 0 ≤ δ₁ + δ₂) :
    m * (N ^ 2 * δ₁ * δ₂ - N * (g - 1) * (δ₁ + δ₂) + (g - 1) ^ 2) -
        m * ((N * δ₁ - N * ((N - 3) / 2)) * (N * δ₂ - N * ((N - 3) / 2))) ≤
      m * (N ^ 3 / 2 * (δ₁ + δ₂) + (g - 1) ^ 2) := by
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ hm
  linear_combination (mul_nonneg (mul_nonneg hN (sub_nonneg.2 hg)) hδ) +
    3 / 2 * mul_nonneg (sq_nonneg N) hδ + sq_nonneg (N * ((N - 3) / 2))

/-! ### The bound -/

/-- **The dimension of `U₁`.** Under (G1) and (G2), for distinct `a, b ≠ 0` and `N - 1 ≤ δ₁, δ₂`,
`dim U₁ = (m + 1)(Nδ₁ - N(N - 3)/2)(Nδ₂ - N(N - 3)/2)`: `U₁` is `m + 1` copies of the span of the
monomials `ξ_a^l ξ_a'^{l'} ξ_b^i ξ_b'^{i'}`, which are linearly independent over `k`. -/
private lemma finrank_affineEvaluationTuplesMonomial_eq (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] [IsIntegral (pullback f f)]
    (hg : 2 ≤ genus f) (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) {N : ℕ} (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (ℓ : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : Faltings.BombieriSiegel.SatisfiesG1 k f ((N : ℤ) • P₁) ℓ)
    (hG2 : Faltings.BombieriSiegel.SatisfiesG2 k f ℓ) {δ₁ δ₂ : ℕ} (hδ₁ : N - 1 ≤ δ₁)
    (hδ₂ : N - 1 ≤ δ₂) (m : ℕ) {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    (finrank k (affineEvaluationTuplesMonomial pr₁ pr₂ ℓ 0 a b N (δ₁, δ₂) (Fin (m + 1))) : ℚ) =
      (m + 1) * ((N * δ₁ - N * ((N - 3) / 2)) * (N * δ₂ - N * ((N - 3) / 2))) := by
  letI := stalkAlgebraOver k f (genericPoint C)
  letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro pr₁ pr₂
  have hT : Transcendental k (ℓ a / ℓ 0) :=
    Faltings.FunctionField.transcendental_of_notMem_range f (div_notMem_range_algebraMap hli ha)
  have hdeg : Module.finrank k⟮ℓ a / ℓ 0⟯ C.functionField = N :=
    finrank_adjoin_div_eq k f hg _ (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) ℓ hli hspan hG1 a ha
  have hu := linearIndependent_pow_mul_pow_of_adjoin_eq_top hT (hG2 a b ha hb hab) (by omega) hdeg
  have huu := linearIndependent_mul_functionFieldMap k f _ _ hu hu
  have hv := linearIndependent_pow_mul_pow_mul_basisB_of_mul pr₁ pr₂ _ _ N huu
  have h := finrank_affineEvaluationTuplesMonomial_of_linearIndependent pr₁ pr₂ ℓ 0 a b
    (hli.ne_zero 0) hδ₁ hδ₂ hv (Fin (m + 1))
  rw [h, Fintype.card_fin]
  push_cast
  ring

/-- **The codimension of `U₁` in `U₀`.** In the setting of
`Faltings.BombieriVojta.finrank_affineEvaluationTuples`, suppose moreover that the basis `ℓ` of
`L(NP)` satisfies (G1) (`Faltings.BombieriSiegel.SatisfiesG1`) and (G2)
(`Faltings.BombieriSiegel.SatisfiesG2`), that `a`, `b` are distinct nonzero indices, and that
`δ₁, δ₂ ≥ N - 1`. Then
`dim U₀ - dim U₁ ≤ (m + 1)(N³(δ₁ + δ₂)/2 + (g - 1)²)`, where
`U₀ = affineEvaluationTuples pr₁ pr₂ ℓ 0 (δ₁, δ₂) (Fin (m + 1))` and
`U₁ = affineEvaluationTuplesMonomial pr₁ pr₂ ℓ 0 a b N (δ₁, δ₂) (Fin (m + 1))`. -/
@[faltings "lem_bvs_codim_u1"]
public theorem finrank_affineEvaluationTuples_sub_finrank_monomial_le
    (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n : ℕ} (hn : n = N - genus f)
    (ℓ : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          C.presheaf.germ _ (genericPoint C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    [IsIntegral (pullback f f)]
    (δ₁ δ₂ : ℕ)
    (hδ₀ : Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) =>
      vojtaFormRestriction
        (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) δ₁ δ₂
        (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom))
    (hNδ₁ : 2 * (genus f : ℤ) - 2 < N * δ₁) (hNδ₂ : 2 * (genus f : ℤ) - 2 < N * δ₂)
    (hG1 : Faltings.BombieriSiegel.SatisfiesG1 k f ((N : ℤ) • P₁) ℓ)
    (hG2 : Faltings.BombieriSiegel.SatisfiesG2 k f ℓ)
    (hδ₁ : N - 1 ≤ δ₁) (hδ₂ : N - 1 ≤ δ₂)
    (m : ℕ) (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    (finrank k (affineEvaluationTuples pr₁ pr₂ ℓ 0 (δ₁, δ₂) (Fin (m + 1))) : ℚ) -
        finrank k (affineEvaluationTuplesMonomial pr₁ pr₂ ℓ 0 a b N (δ₁, δ₂) (Fin (m + 1))) ≤
      (m + 1) * ((N : ℚ) ^ 3 / 2 * (δ₁ + δ₂) + ((genus f : ℚ) - 1) ^ 2) := by
  letI := stalkAlgebraOver k f (genericPoint C)
  letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  intro pr₁ pr₂
  have h0 := (finrank_affineEvaluationTuples k f hg P₁ hP₁cl hP₁ N hN hn ℓ hli hspan φNP hφNP
    hφℓ δ₁ δ₂ hδ₀ hNδ₁ hNδ₂ m 0).1
  have h1 : (finrank k (affineEvaluationTuplesMonomial pr₁ pr₂ ℓ 0 a b N (δ₁, δ₂)
      (Fin (m + 1))) : ℚ) = _ :=
    finrank_affineEvaluationTuplesMonomial_eq k f hg P₁ hP₁cl hP₁ hN ℓ hli hspan hG1 hG2
      hδ₁ hδ₂ m ha hb hab
  have h0' : (finrank k (affineEvaluationTuples pr₁ pr₂ ℓ 0 (δ₁, δ₂) (Fin (m + 1))) : ℚ) =
      (m + 1) * ((N : ℚ) ^ 2 * δ₁ * δ₂ - N * (genus f - 1) * (δ₁ + δ₂) +
        ((genus f : ℚ) - 1) ^ 2) :=
    mod_cast h0
  rw [h0', h1]
  exact dim_sub_dim_le _ _ _ _ _ (by positivity)
    (by exact_mod_cast (show 1 ≤ genus f by omega)) (by positivity) (by positivity)

end Faltings.BombieriVojta
