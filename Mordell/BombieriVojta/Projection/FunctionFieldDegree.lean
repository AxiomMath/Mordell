module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Projection.GenericBasis
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import Mordell.BombieriVojta.Projection.CoordinateRingProduct
public import Mordell.BombieriVojta.Projection.Degree
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatAtPullbackMap
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField

/-!
# The degree of `k(C × C)` over `k(ξ_a, ξ'_b)`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k` of
characteristic zero (for instance a number field, or an algebraic extension of `ℚ`), `P` a
divisor of degree one, `N ≥ 2g + 1`, and `x = (x₀, …, xₙ)` a `k`-basis of the Riemann–Roch space
`L(NP) = H⁰(C, 𝒪(NP))`. Put `ξ_a = x_a / x₀ ∈ k(C)`, and write `ξ'_b` for the function `ξ_b` on
the second factor of `C × C = C ×_k C`. If `x` satisfies (G1), then for all `a, b ∈ {1, …, n}`
the function field `k(C × C)` is a finite extension of `k(ξ_a, ξ'_b)`, of degree `N²`.

The proof runs at the level of function fields. By `Faltings.BombieriSiegel.finrank_adjoin_div_eq`,
`[k(C) : k(ξ_a)] = N` for `a ≠ 0`. Since `k` has characteristic zero and `C` is geometrically
integral, `k(C) ⊗_k k(C)` is a domain, and `g ⊗ h ↦ pr₁^* g · pr₂^* h` identifies `k(C × C)` with
its fraction field. The ring `k(C) ⊗_k k(C)` is free of rank `N²` over the image `A` of
`k(ξ_a) ⊗_k k(ξ_b)`, and `k(pr₁^* ξ_a, pr₂^* ξ_b)` is the fraction field of `A` inside
`k(C × C)`; a basis of `k(C) ⊗_k k(C)` over `A` is therefore a basis of `k(C × C)` over
`k(pr₁^* ξ_a, pr₂^* ξ_b)`.

## Main results

* `Faltings.BombieriSiegel.finrank_adjoin_pullback_eq_sq`: under (G1), `k(C × C)` is finite over
  `k(pr₁^* ξ_a, pr₂^* ξ_b)`, of degree `N²`.

## Implementation notes

The curve `C × C` is the fibre product `pullback f f` over `Spec k`; it is integral since `C` is
geometrically integral and smooth. Rational functions are pulled back along the projections by
`AlgebraicGeometry.functionFieldMap`, the map of function fields of a dominant morphism of
integral schemes. The `k`-algebra structure on `k(C × C)` is the composite
`k → k(C) → k(C × C)` through the first projection (it agrees with the one through the second
projection, as `pr₁ ≫ f = pr₂ ≫ f`). As in `Faltings.BombieriSiegel.IsGenericBasis`, sections of
`𝒪(NP)` are rational functions in `L(NP) = {g | g = 0 ∨ ∀ Q closed, 0 ≤ ord_Q g + (NP)(Q)}`, and
`P` is a divisor `P₁ : C →₀ ℤ` of degree one supported on closed points, with `NP = (N : ℤ) • P₁`.
The conclusion includes finiteness, since `finrank` is `0` for an infinite extension.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open Faltings (free_finrank_tensor_range)

open CategoryTheory Limits AlgebraicGeometry IntermediateField TensorProduct

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriSiegel

/-- The function field of a geometrically integral curve over a field of characteristic zero
stays a domain after tensoring with any field extension. -/
private theorem isDomain_functionField_tensor (k : Type u) [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [GeometricallyIntegral f] (L : Type u) [Field L] [Algebra k L] :
    letI := functionFieldAlgebra k f
    IsDomain (C.functionField ⊗[k] L) := by
  let := functionFieldAlgebra k f
  let : Algebra k (C.residueField (genericPoint C)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.Γevaluation (genericPoint C)).hom.toAlgebra
  have hgi : Algebra.IsGeometricallyIrreducible k (C.residueField (genericPoint C)) :=
    ((geometricallyIrreducible_tfae_functionField k C f (genericPoint C)
      (genericPoint_spec C)).out 1 2).mp (inferInstance : GeometricallyIrreducible f)
  let e : C.functionField ≃ₐ[k] C.residueField (genericPoint C) :=
    { RingEquiv.ofBijective (IsLocalRing.residue C.functionField)
        ⟨(IsLocalRing.residue C.functionField).injective, IsLocalRing.residue_surjective⟩ with
      commutes' := fun r => rfl }
  rw [isDomain_iff_irreducibleSpace_and_isReduced]
  refine ⟨?_, ?_⟩
  · have := (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      k _).mp hgi L
    let e' := (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv
    let h := PrimeSpectrum.homeomorphOfRingEquiv e'
    exact h.symm.surjective.irreducibleSpace h.symm.continuous
  · have h := (Algebra.isGeometricallyReduced_tfae k 1 C.functionField k
      (AlgebraicClosure k)).out 3 5
    have h3 : IsReduced (k ⊗[k] C.functionField) :=
      isReduced_of_injective (Algebra.TensorProduct.lid k C.functionField).toRingEquiv.toRingHom
        (Algebra.TensorProduct.lid k C.functionField).injective
    have := h.mp h3 L
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm k C.functionField L).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm k _ _).injective

/-- For integral schemes `X`, `Y` over `k` whose function fields have a domain as tensor product,
the map `K(X) ⊗[k] K(Y) → K(X ×_k Y)`, `a ⊗ b ↦ pr₁^* a · pr₂^* b`, exhibits `K(X ×_k Y)` as
the fraction field of `K(X) ⊗[k] K(Y)`. -/
public theorem exists_isFractionRing_tensor_functionField (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsIntegral X]
    [IsIntegral Y] [IsIntegral (pullback f g)] [iX : Algebra k X.functionField]
    [iY : Algebra k Y.functionField] (hX : iX = stalkAlgebraOver k f (genericPoint X))
    (hY : iY = stalkAlgebraOver k g (genericPoint Y))
    [IsDomain (X.functionField ⊗[k] Y.functionField)] :
    ∃ ψ : X.functionField ⊗[k] Y.functionField →+* (pullback f g).functionField,
      (∀ a b, ψ (a ⊗ₜ b) =
        functionFieldMap (pullback.fst f g) a * functionFieldMap (pullback.snd f g) b) ∧
      (letI := ψ.toAlgebra; IsFractionRing (X.functionField ⊗[k] Y.functionField)
        (pullback f g).functionField) := by
  subst hX hY
  let := stalkAlgebraOver k f (genericPoint X)
  let := stalkAlgebraOver k g (genericPoint Y)
  have hx : pullback.fst f g (genericPoint (pullback f g : Scheme.{u})) = genericPoint X :=
    map_genericPoint_of_isDominant _
  have hy : pullback.snd f g (genericPoint (pullback f g : Scheme.{u})) = genericPoint Y :=
    map_genericPoint_of_isDominant _
  obtain ⟨ψ₀, h₁, h₂, hloc₀⟩ :=
    exists_isLocalization_atPrime_stalk_pullback_tensorProduct k f g
      (genericPoint (pullback f g : Scheme.{u}))
  obtain ⟨ψ, hψ, hloc⟩ := exists_tensor_stalk_transport₂ k f g _ _ _ _ hx hy ψ₀ hloc₀
  have htmul : ∀ a b, ψ (a ⊗ₜ b) =
      functionFieldMap (pullback.fst f g) a * functionFieldMap (pullback.snd f g) b := by
    intro a b
    rw [hψ, h₁, h₂]
    rfl
  let := ψ.toAlgebra
  have hinj : Function.Injective ψ :=
    IsLocalization.injective (M := (Ideal.comap ψ
      (IsLocalRing.maximalIdeal (pullback f g).functionField)).primeCompl)
      (pullback f g).functionField (Ideal.primeCompl_le_nonZeroDivisors _)
  have hP : Ideal.comap ψ (IsLocalRing.maximalIdeal (pullback f g).functionField) = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hM : (Ideal.comap ψ (IsLocalRing.maximalIdeal (pullback f g).functionField)).primeCompl =
      nonZeroDivisors (X.functionField ⊗[k] Y.functionField) := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, hP, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  rw [IsLocalization.AtPrime, hM] at hloc
  exact ⟨ψ, htmul, hloc⟩

/-- Let `ψ : K₁ ⊗[k] K₂ → M` be a map of `k`-algebras exhibiting the field `M` as a fraction
field of its source. If `K₁` has degree `m` over `k(s)` and `K₂` has degree `m'` over
`k(t)`, then `M` has degree `m * m'` over `k(ψ (s ⊗ 1), ψ (1 ⊗ t))`. -/
private theorem finrank_adjoin_tmul_eq_mul {k K₁ K₂ M : Type*} [Field k] [Field K₁] [Field K₂]
    [Field M] [Algebra k K₁] [Algebra k K₂] [Algebra k M] (ψ : K₁ ⊗[k] K₂ →ₐ[k] M)
    (hfrac : letI := ψ.toRingHom.toAlgebra; IsFractionRing (K₁ ⊗[k] K₂) M)
    {s : K₁} {t : K₂} {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hs : Module.finrank k⟮s⟯ K₁ = m) (ht : Module.finrank k⟮t⟯ K₂ = m') :
    FiniteDimensional k⟮ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)⟯ M ∧
      Module.finrank k⟮ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)⟯ M = m * m' := by
  classical
  let := ψ.toRingHom.toAlgebra
  have hψ : Function.Injective ψ := IsFractionRing.injective (K₁ ⊗[k] K₂) M
  have hfr (z : M) : ∃ x y, ψ y ≠ 0 ∧ z = ψ x / ψ y := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := K₁ ⊗[k] K₂) z
    exact ⟨x, y, IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hy, rfl⟩
  set P := k⟮s⟯
  set Q := k⟮t⟯
  set E := k⟮ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)⟯
  have hf : letI := P.val.toRingHom.toAlgebra; Module.Free P K₁ ∧ Module.finrank P K₁ = m :=
    ⟨Module.Free.of_divisionRing _ _, hs⟩
  have hg : letI := Q.val.toRingHom.toAlgebra; Module.Free Q K₂ ∧ Module.finrank Q K₂ = m' :=
    ⟨Module.Free.of_divisionRing _ _, ht⟩
  obtain ⟨hfree, hrank⟩ := free_finrank_tensor_range P.val Q.val hm hm' hf hg _ rfl
  set A := (Algebra.TensorProduct.map P.val Q.val).range
  have : Module.Finite A (K₁ ⊗[k] K₂) := Module.finite_of_finrank_pos (hrank ▸ Nat.mul_pos hm hm')
  let bas := Module.Free.chooseBasis A (K₁ ⊗[k] K₂)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A (K₁ ⊗[k] K₂)) = m * m' := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  have hl : ∀ p ∈ P, ψ (p ⊗ₜ 1) ∈ E := by
    intro p hp
    have h1 : ψ (p ⊗ₜ 1) ∈ P.map (ψ.comp Algebra.TensorProduct.includeLeft) := ⟨p, hp, rfl⟩
    rw [adjoin_map, Set.image_singleton] at h1
    refine adjoin.mono _ _ _ ?_ h1
    simp
  have hr : ∀ q ∈ Q, ψ (1 ⊗ₜ q) ∈ E := by
    intro q hq
    have h1 : ψ (1 ⊗ₜ q) ∈ Q.map (ψ.comp Algebra.TensorProduct.includeRight) := ⟨q, hq, rfl⟩
    rw [adjoin_map, Set.image_singleton] at h1
    refine adjoin.mono _ _ _ ?_ h1
    simp
  have hAE : ∀ a ∈ A, ψ a ∈ E := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      have : (Algebra.TensorProduct.map P.val Q.val (p ⊗ₜ q) : K₁ ⊗[k] K₂) =
          ((p : K₁) ⊗ₜ (1 : K₂)) * ((1 : K₁) ⊗ₜ (q : K₂)) := by simp
      change ψ (Algebra.TensorProduct.map P.val Q.val (p ⊗ₜ q)) ∈ E
      rw [this, map_mul]
      exact mul_mem (hl _ p.2) (hr _ q.2)
    | add x y hx hy =>
      change ψ (Algebra.TensorProduct.map P.val Q.val (x + y)) ∈ E
      rw [map_add, map_add]
      exact add_mem hx hy
  have hEA : ∀ e ∈ E, ∃ a ∈ A, ∃ b ∈ A, ψ b ≠ 0 ∧ e = ψ a / ψ b := by
    intro e he
    have hsub : Subring.closure (Set.range (algebraMap k M) ∪ {ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)}) ≤
        (A.map ψ).toSubring := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | h)
      · exact (A.map ψ).algebraMap_mem r
      · rcases h with rfl | rfl
        · exact ⟨_, ⟨⟨s, mem_adjoin_simple_self k s⟩ ⊗ₜ 1, rfl⟩, by simp⟩
        · exact ⟨_, ⟨1 ⊗ₜ ⟨t, mem_adjoin_simple_self k t⟩, rfl⟩, by simp⟩
    have he' : e ∈ Subfield.closure (Set.range (algebraMap k M) ∪
        {ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)}) := by
      rwa [← adjoin_toSubfield]
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp he'
    obtain ⟨a, ha, rfl⟩ := hsub hy
    obtain ⟨b, hb, rfl⟩ := hsub hz
    by_cases hb0 : ψ b = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, by simp, by simp [hb0]⟩
    · exact ⟨a, ha, b, hb, hb0, rfl⟩
  let w : Module.Free.ChooseBasisIndex A (K₁ ⊗[k] K₂) → M := fun i => ψ (bas i)
  have hli : LinearIndependent E w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha b hb hb0 heq using fun j => hEA (g j) (g j).2
    set D := ∏ j, ψ (b j)
    have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hb0 j
    let c := fun j => a j * ∏ j' ∈ Finset.univ.erase j, b j'
    have hc : ∀ j, c j ∈ A := fun j => mul_mem (ha j) (prod_mem fun j' _ => hb j')
    have hψc : ∀ j, ψ (c j) = (g j : M) * D := by
      intro j
      simp only [c, map_mul, map_prod, D]
      rw [← Finset.mul_prod_erase Finset.univ (fun j' => ψ (b j')) (Finset.mem_univ j), heq j]
      field_simp [hb0 j]
    have hsum : ψ (∑ j, c j * bas j) = 0 := by
      rw [map_sum]
      simp only [map_mul, hψc]
      calc ∑ j, (g j : M) * D * ψ (bas j) = D * ∑ j, g j • w j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
            ring
        _ = 0 := by rw [hg, mul_zero]
    have h0 : ∑ j, (⟨c j, hc j⟩ : A) • bas j = 0 := by
      simpa [Subalgebra.smul_def] using hψ (hsum.trans (map_zero ψ).symm)
    have h1 := (Fintype.linearIndependent_iff.mp bas.linearIndependent) _ h0 i
    have hci : c i = 0 := congrArg Subtype.val h1
    have h2 : (g i : M) * D = 0 := by rw [← hψc, hci, map_zero]
    exact Subtype.ext ((mul_eq_zero.mp h2).resolve_right hD)
  have hsp : ⊤ ≤ Submodule.span E (Set.range w) := by
    set V := Submodule.span E (Set.range w)
    have hRV : ∀ x, ψ x ∈ V := by
      intro x
      have hx : ψ x = ∑ i, (⟨ψ (bas.repr x i), hAE _ (bas.repr x i).2⟩ : E) • w i := by
        conv_lhs => rw [← bas.sum_repr x]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change ψ (((bas.repr x i : A) : K₁ ⊗[k] K₂) * bas i) = _
        rw [map_mul, Algebra.smul_def, IntermediateField.algebraMap_apply]
      rw [hx]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hVV : V * V ≤ V := by
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      change ψ (bas i) * ψ (bas j) ∈ V
      rw [← map_mul]
      exact hRV _
    let S : Subalgebra E M := V.toSubalgebra (by simpa using hRV 1)
      fun x y hx hy => hVV (Submodule.mul_mem_mul hx hy)
    have hfg : (Subalgebra.toSubmodule S).FG := by
      simpa [S] using Submodule.fg_span (Set.finite_range w)
    intro z _
    obtain ⟨x, y, hy, rfl⟩ := hfr z
    have hyS : ψ y ∈ S := hRV y
    have hinv : (ψ y)⁻¹ ∈ S :=
      S.inv_mem_of_algebraic (x := ⟨ψ y, hyS⟩)
        (IsIntegral.of_mem_of_fg S hfg _ hyS).isAlgebraic
    rw [div_eq_mul_inv]
    exact S.mul_mem (hRV x) hinv
  let B := Module.Basis.mk hli hsp
  exact ⟨Module.Finite.of_basis B, by rw [Module.finrank_eq_card_basis B, hcard]⟩

/-- Let `C` be a smooth projective geometrically integral curve of genus `≥ 2` over a field `k` of
characteristic zero, `P` a divisor of degree one supported on closed points, `N ≥ 2g + 1`, and
`x₀, …, xₙ` a `k`-basis of `L(NP)` satisfying (G1) for `NP`. For `a, b ≠ 0`, with
`ξ_a = x_a / x₀`, the function field of `C ×_k C` is a finite extension of
`k(pr₁^* ξ_a, pr₂^* ξ_b)` of degree `N²`. -/
@[faltings "lem_bvs_function_field_degree"]
public theorem finrank_adjoin_pullback_eq_sq (k : Type u) [Field k] [CharZero k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x)
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) :
    letI := functionFieldAlgebra k f
    letI := ((functionFieldMap (pullback.fst f f)).comp
      (algebraMap k C.functionField)).toAlgebra
    FiniteDimensional k⟮functionFieldMap (pullback.fst f f) (x a / x 0),
        functionFieldMap (pullback.snd f f) (x b / x 0)⟯ (pullback f f).functionField ∧
      Module.finrank k⟮functionFieldMap (pullback.fst f f) (x a / x 0),
        functionFieldMap (pullback.snd f f) (x b / x 0)⟯ (pullback f f).functionField = N ^ 2 := by
  let := functionFieldAlgebra k f
  let := ((functionFieldMap (pullback.fst f f)).comp (algebraMap k C.functionField)).toAlgebra
  have hdeg : ∀ c ≠ 0, Module.finrank k⟮x c / x 0⟯ C.functionField = N := fun c hc =>
    finrank_adjoin_div_eq k f hg _ (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hx hspan hG1 c hc
  have hNpos : 0 < N := by omega
  have : IsDomain (C.functionField ⊗[k] C.functionField) := isDomain_functionField_tensor k f _
  obtain ⟨ψ, htmul, hfrac⟩ := exists_isFractionRing_tensor_functionField k f f rfl rfl
  have hl (c : C.functionField) : ψ (c ⊗ₜ 1) = functionFieldMap (pullback.fst f f) c := by
    rw [htmul, map_one, mul_one]
  have hr (c : C.functionField) : ψ (1 ⊗ₜ c) = functionFieldMap (pullback.snd f f) c := by
    rw [htmul, map_one, one_mul]
  let ψa : C.functionField ⊗[k] C.functionField →ₐ[k] (pullback f f).functionField :=
    { ψ with commutes' := fun r => hl _ }
  have key := finrank_adjoin_tmul_eq_mul ψa hfrac hNpos hNpos (hdeg a ha) (hdeg b hb)
  rwa [show ψa ((x a / x 0) ⊗ₜ 1) = _ from hl _, show ψa (1 ⊗ₜ (x b / x 0)) = _ from hr _,
    ← sq] at key

end Faltings.BombieriSiegel
