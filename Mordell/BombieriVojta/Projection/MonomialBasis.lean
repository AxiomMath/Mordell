module
public import Mordell.BombieriVojta.Projection.Degree

/-!
# A monomial basis of `k(C × C)`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `P` a divisor of degree one on `C`, `N ≥ 2g + 1`, and `x₀, …, xₙ` a `k`-basis of the
Riemann–Roch space `L(NP) = H⁰(C, 𝒪(NP))` inside `k(C)`. Write `ξ_a = x_a / x₀ ∈ k(C)`, and on
`C × C` write `ξ_a` for its pull-back along the first projection and `ξ'_a` for its pull-back
along the second. If the basis satisfies (G1) and (G2), then for `a, b, j, j' ∈ {1, …, n}` with
`j ≠ a` and `j' ≠ b`, the `N²` monomials `ξ_j^i ξ'_{j'}^{i'}`, `0 ≤ i, i' ≤ N - 1`, form a basis of
`k(C × C)` over its subfield `k(ξ_a, ξ'_b)`.

## Main results

* `Faltings.BombieriSiegel.linearIndependent_and_span_monomial_eq_top`: under (G1) and (G2), the
  family `(i, i') ↦ ξ_j^i ξ'_{j'}^{i'}` indexed by `Fin N × Fin N` is linearly independent over
  `k⟮ξ_a, ξ'_b⟯` and spans `k(C × C)`.

## Implementation notes

As in `Faltings.BombieriSiegel.finrank_adjoin_div_eq`, sections of `𝒪(NP)` are rational functions,
`P` is a divisor `P₁ : C →₀ ℤ` of degree one supported on closed points, `NP` is `(N : ℤ) • P₁`,
`L(NP)` is in the form of `Faltings.BombieriSiegel.IsGenericBasis.span_eq`, and `k(C)` is a
`k`-algebra through `AlgebraicGeometry.functionFieldAlgebra k f`.

Since `C` is geometrically integral over `k`, `k(C) ⊗_k k(C)` is a domain and the function field of
`C × C` is its field of fractions, the two projections inducing `g ↦ g ⊗ 1` and `g ↦ 1 ⊗ g`. The
field `k(C × C)` is therefore an arbitrary field `L` with `IsFractionRing (k(C) ⊗[k] k(C)) L`, a
characterisation up to unique isomorphism, and `ξ_j`, `ξ'_{j'}` are the images of `ξ_j ⊗ 1` and
`1 ⊗ ξ_{j'}` in `L`. The subfield `k(ξ_a, ξ'_b)` is `IntermediateField.adjoin k` in `L`.

The proof does not pass through the degree `[k(C × C) : k(ξ_a, ξ'_b)] = N²`. Since
`[k(C) : k(ξ_a)] = N` (`Faltings.BombieriSiegel.finrank_adjoin_div_eq`) and `k(C) = k(ξ_a, ξ_j)`
by (G2), the powers `1, ξ_j, …, ξ_j^{N-1}` form a basis of `k(C)` over `k(ξ_a)`. The products of
two such bases form a basis of `k(C) ⊗_k k(C)` over the image of `k(ξ_a) ⊗_k k(ξ_b)`, and a basis
of a domain over a subalgebra is a basis of its fraction field over the fraction field of that
subalgebra, which here is `k(ξ_a, ξ'_b)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, p. 630
-/

open AlgebraicGeometry IntermediateField TensorProduct

universe u

namespace Faltings.BombieriSiegel

/-- If `e` is a basis of `B` over `P` and `d` a basis of `B'` over `Q`, with `P → B` and
`Q → B'` injective, then the `e_i ⊗ d_j` form a basis of `B ⊗_k B'` over the image of
`P ⊗_k Q`. -/
private theorem exists_basis_tensor_range {k P Q B B' : Type*} [Field k] [CommRing P]
    [CommRing Q] [CommRing B] [CommRing B'] [Algebra k P] [Algebra k Q] [Algebra k B]
    [Algebra k B'] [Algebra P B] [Algebra Q B'] [IsScalarTower k P B] [IsScalarTower k Q B']
    (hP : Function.Injective (algebraMap P B)) (hQ : Function.Injective (algebraMap Q B'))
    {ι κ : Type*} (e : Module.Basis ι P B) (d : Module.Basis κ Q B') :
    ∃ bas : Module.Basis (ι × κ) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P B)
        (IsScalarTower.toAlgHom k Q B')).range (B ⊗[k] B'),
      ∀ i, bas i = e i.1 ⊗ₜ d i.2 := by
  classical
  set φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P B)
    (IsScalarTower.toAlgHom k Q B')
  have hφ : Function.Injective φ :=
    TensorProduct.map_injective_of_flat_flat (IsScalarTower.toAlgHom k P B).toLinearMap
      (IsScalarTower.toAlgHom k Q B').toLinearMap hP hQ
  let : Algebra (P ⊗[k] Q) (B ⊗[k] B') := φ.toRingHom.toAlgebra
  let E₀ : B ⊗[k] B' ≃ₗ[k] _ :=
    (TensorProduct.congr (e.repr.restrictScalars k) (d.repr.restrictScalars k)).trans
      (finsuppTensorFinsupp k k P Q _ _)
  have hE₀ : ∀ (p : P) (q : Q) (z : B ⊗[k] B'), E₀ ((p ⊗ₜ[k] q) • z) = (p ⊗ₜ[k] q) • E₀ z := by
    intro p q z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul b b' =>
      have h1 : (p ⊗ₜ[k] q) • (b ⊗ₜ[k] b') = (p • b) ⊗ₜ[k] (q • b') := by
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
        simp [φ, RingHom.algebraMap_toAlgebra]
      rw [h1]
      ext ⟨i, j⟩
      simp [E₀, finsuppTensorFinsupp_apply]
  let E : B ⊗[k] B' ≃ₗ[P ⊗[k] Q] _ :=
    { E₀ with
      map_smul' := fun c z => by
        induction c using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          simp only [RingHom.id_apply, add_smul] at hx hy ⊢
          rw [← hx, ← hy]
          exact E₀.map_add _ _
        | tmul p q => exact hE₀ p q z }
  let bas := Module.Basis.ofRepr E
  let ψ : P ⊗[k] Q ≃+* φ.range := (AlgEquiv.ofInjective φ hφ).toRingEquiv
  refine ⟨bas.mapCoeffs ψ (fun c z => rfl), fun i => ?_⟩
  refine (Module.Basis.mapCoeffs_apply bas ψ _ i).trans ?_
  change E₀.symm (Finsupp.single i 1) = _
  rw [Algebra.TensorProduct.one_def]
  simp [E₀, finsuppTensorFinsupp_symm_single]

/-- Let `M` be the fraction field of a domain `R` with a finite basis `b` over a subalgebra `A`,
and let `F ⊆ M` be an intermediate field each of whose elements is a quotient of images of
elements of `A`. Then the images of the `b_i` are linearly independent over `F`. -/
private theorem linearIndependent_algebraMap_basis {k R M : Type*} [Field k] [CommRing R]
    [IsDomain R] [Field M] [Algebra k R] [Algebra k M] [Algebra R M] [IsScalarTower k R M]
    [IsFractionRing R M] {A : Subalgebra k R} {ι : Type*} [Finite ι] (bas : Module.Basis ι A R)
    {F : IntermediateField k M}
    (hFA : ∀ z ∈ F, ∃ a ∈ A, ∃ b ∈ A, algebraMap R M b ≠ 0 ∧
      z = algebraMap R M a / algebraMap R M b) :
    LinearIndependent F (fun i => algebraMap R M (bas i)) := by
  classical
  have := Fintype.ofFinite ι
  set ψ := algebraMap R M
  set w := fun i => ψ (bas i)
  have hψ : Function.Injective ψ := IsFractionRing.injective R M
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha b hb hb0 heq using fun j => hFA (g j) (g j).2
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
  have hci : c i = 0 :=
    congrArg Subtype.val ((Fintype.linearIndependent_iff.mp bas.linearIndependent) _ h0 i)
  have h2 : (g i : M) * D = 0 := by rw [← hψc, hci, map_zero]
  exact Subtype.ext ((mul_eq_zero.mp h2).resolve_right hD)

/-- Let `M` be the fraction field of a domain `R` with a finite basis `b` over a subalgebra `A`,
and let `F ⊆ M` be an intermediate field containing the image of `A`. Then the images of the `b_i`
span `M` over `F`. -/
private theorem span_algebraMap_basis_eq_top {k R M : Type*} [Field k] [CommRing R] [IsDomain R]
    [Field M] [Algebra k R] [Algebra k M] [Algebra R M] [IsScalarTower k R M]
    [IsFractionRing R M] {A : Subalgebra k R} {ι : Type*} [Finite ι] (bas : Module.Basis ι A R)
    {F : IntermediateField k M} (hAF : ∀ a ∈ A, algebraMap R M a ∈ F) :
    Submodule.span F (Set.range fun i => algebraMap R M (bas i)) = ⊤ := by
  have := Fintype.ofFinite ι
  set ψ := algebraMap R M
  set w := fun i => ψ (bas i)
  refine top_le_iff.mp ?_
  set V := Submodule.span F (Set.range w)
  have hRV : ∀ x, ψ x ∈ V := by
    intro x
    have hx : ψ x = ∑ i, (⟨ψ (bas.repr x i), hAF _ (bas.repr x i).2⟩ : F) • w i := by
      conv_lhs => rw [← bas.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ψ (((bas.repr x i : A) : R) * bas i) = _
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
  let S : Subalgebra F M := V.toSubalgebra (by simpa using hRV 1)
    fun x y hx hy => hVV (Submodule.mul_mem_mul hx hy)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    simpa [S] using Submodule.fg_span (Set.finite_range w)
  intro z _
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hyS : ψ y ∈ S := hRV y
  have hinv : (ψ y)⁻¹ ∈ S :=
    S.inv_mem_of_algebraic (x := ⟨ψ y, hyS⟩)
      (IsIntegral.of_mem_of_fg S hfg _ hyS).isAlgebraic
  rw [div_eq_mul_inv]
  exact S.mul_mem (hRV x) hinv

/-- An algebra map sends `k(s)` into any intermediate field containing the image of `s`. -/
private theorem map_mem_adjoin_of_mem_adjoin_simple {k K M : Type*} [Field k] [Field K] [Field M]
    [Algebra k K] [Algebra k M] (φ : K →ₐ[k] M) {s p : K} (hp : p ∈ k⟮s⟯) {S : Set M}
    (hs : φ s ∈ S) : φ p ∈ adjoin k S := by
  have h : φ p ∈ k⟮s⟯.map φ := ⟨p, hp, rfl⟩
  rw [adjoin_map, Set.image_singleton] at h
  exact adjoin.mono _ _ _ (by simpa using hs) h

/-- Let `M` be a fraction field of `K₁ ⊗_k K₂`, let `e` be a basis of `K₁` over `k(s)` and `d` a
basis of `K₂` over `k(t)`. Then the products `(e_i ⊗ 1)(1 ⊗ d_j)` form a basis of `M` over
`k(s ⊗ 1, 1 ⊗ t)`. -/
private theorem linearIndependent_and_span_tmul_eq_top {k K₁ K₂ M : Type*} [Field k] [Field K₁]
    [Field K₂] [Field M] [Algebra k K₁] [Algebra k K₂] [Algebra k M]
    [Algebra (K₁ ⊗[k] K₂) M] [IsScalarTower k (K₁ ⊗[k] K₂) M] [IsFractionRing (K₁ ⊗[k] K₂) M]
    {s : K₁} {t : K₂} {ι κ : Type*} [Finite ι] [Finite κ]
    (e : Module.Basis ι k⟮s⟯ K₁) (d : Module.Basis κ k⟮t⟯ K₂) :
    let F := k⟮algebraMap (K₁ ⊗[k] K₂) M (s ⊗ₜ 1), algebraMap (K₁ ⊗[k] K₂) M (1 ⊗ₜ t)⟯
    let w : ι × κ → M := fun i =>
      algebraMap (K₁ ⊗[k] K₂) M (e i.1 ⊗ₜ 1) * algebraMap (K₁ ⊗[k] K₂) M (1 ⊗ₜ d i.2)
    LinearIndependent F w ∧ Submodule.span F (Set.range w) = ⊤ := by
  classical
  intro E w
  have : IsDomain (K₁ ⊗[k] K₂) :=
    Function.Injective.isDomain _ (IsFractionRing.injective (K₁ ⊗[k] K₂) M)
  let ψ := IsScalarTower.toAlgHom k (K₁ ⊗[k] K₂) M
  let A := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k k⟮s⟯ K₁)
    (IsScalarTower.toAlgHom k k⟮t⟯ K₂)).range
  obtain ⟨bas, hbas⟩ : ∃ bas : Module.Basis (ι × κ) A (K₁ ⊗[k] K₂),
      ∀ i, bas i = e i.1 ⊗ₜ d i.2 :=
    exists_basis_tensor_range (k := k) (algebraMap k⟮s⟯ K₁).injective
      (algebraMap k⟮t⟯ K₂).injective e d
  have hw : w = fun i => ψ (bas i) := by
    funext i
    rw [hbas]
    change _ * _ = algebraMap (K₁ ⊗[k] K₂) M _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hAE : ∀ a ∈ A, ψ a ∈ E := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      have : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k k⟮s⟯ K₁)
          (IsScalarTower.toAlgHom k k⟮t⟯ K₂) (p ⊗ₜ q) : K₁ ⊗[k] K₂) =
          ((p : K₁) ⊗ₜ (1 : K₂)) * ((1 : K₁) ⊗ₜ (q : K₂)) := by simp
      change ψ (Algebra.TensorProduct.map _ _ (p ⊗ₜ q)) ∈ E
      rw [this, map_mul]
      exact mul_mem
        (map_mem_adjoin_of_mem_adjoin_simple (ψ.comp Algebra.TensorProduct.includeLeft) p.2
          (by simp [ψ]))
        (map_mem_adjoin_of_mem_adjoin_simple (ψ.comp Algebra.TensorProduct.includeRight) q.2
          (by simp [ψ]))
    | add x y hx hy =>
      change ψ (Algebra.TensorProduct.map _ _ (x + y)) ∈ E
      rw [map_add, map_add]
      exact add_mem hx hy
  have hEA : ∀ e ∈ E, ∃ a ∈ A, ∃ b ∈ A, ψ b ≠ 0 ∧ e = ψ a / ψ b := by
    intro e he
    have hsub : Subring.closure (Set.range (algebraMap k M) ∪ {ψ (s ⊗ₜ 1), ψ (1 ⊗ₜ t)}) ≤
        (A.map ψ).toSubring := by
      rw [Subring.closure_le]
      rintro _ (⟨r, rfl⟩ | rfl | rfl)
      · exact (A.map ψ).algebraMap_mem r
      · exact ⟨_, ⟨⟨s, mem_adjoin_simple_self k s⟩ ⊗ₜ 1, rfl⟩, by simp⟩
      · exact ⟨_, ⟨1 ⊗ₜ ⟨t, mem_adjoin_simple_self k t⟩, rfl⟩, by simp⟩
    rw [← SetLike.mem_coe, ← coe_toSubfield, adjoin_toSubfield] at he
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp he
    obtain ⟨a, ha, rfl⟩ := hsub hy
    obtain ⟨b, hb, rfl⟩ := hsub hz
    by_cases hb0 : ψ b = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, by simp, by simp [hb0]⟩
    · exact ⟨a, ha, b, hb, hb0, rfl⟩
  rw [hw]
  exact ⟨linearIndependent_algebraMap_basis bas hEA, span_algebraMap_basis_eq_top bas hAE⟩

/-- If `K = k(s, t)` has degree `N > 0` over `k(s)`, then `1, t, …, t^{N-1}` is a basis of `K`
over `k(s)`. -/
public theorem exists_basis_pow_of_adjoin_eq_top {k K : Type*} [Field k] [Field K] [Algebra k K]
    {s t : K} (hst : k⟮s, t⟯ = ⊤) {N : ℕ} (hN : 0 < N) (hdeg : Module.finrank k⟮s⟯ K = N) :
    ∃ e : Module.Basis (Fin N) k⟮s⟯ K, ∀ i, e i = t ^ (i : ℕ) := by
  have : FiniteDimensional k⟮s⟯ K := Module.finite_of_finrank_pos (hdeg ▸ hN)
  have hint : IsIntegral k⟮s⟯ t := .of_finite _ _
  have htop : k⟮s⟯⟮t⟯ = ⊤ := by
    rw [← restrictScalars_eq_top_iff (K := k), adjoin_simple_adjoin_simple, hst]
  let pb := (adjoin.powerBasis hint).map ((equivOfEq htop).trans topEquiv)
  have hgen : pb.gen = t := by simp [pb]
  have hdim : pb.dim = N := by rw [← pb.finrank, hdeg]
  refine ⟨pb.basis.reindex (finCongr hdim), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, pb.basis_eq_pow, hgen]
  rfl

/-- Let `K` be a field over `k`, `L` a fraction field of `K ⊗_k K`, and `x₀, …, xₙ ∈ K` with
`[K : k(x_c / x₀)] = N > 0` for every `c ≠ 0`. If `K = k(x_a / x₀, x_j / x₀)` and
`K = k(x_b / x₀, x_{j'} / x₀)`, then the monomials `(ξ_j ⊗ 1)^i (1 ⊗ ξ_{j'})^{i'}`,
`(i, i') ∈ Fin N × Fin N`, form a basis of `L` over `k⟮ξ_a ⊗ 1, 1 ⊗ ξ_b⟯`. -/
private theorem linearIndependent_and_span_monomial_of_finrank_eq {k K L : Type*} [Field k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra (K ⊗[k] K) L]
    [IsScalarTower k (K ⊗[k] K) L] [IsFractionRing (K ⊗[k] K) L] {n N : ℕ} (hN : 0 < N)
    (x : Fin (n + 1) → K) (hdeg : ∀ c, c ≠ 0 → Module.finrank k⟮x c / x 0⟯ K = N)
    {a b j j' : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) (haj : k⟮x a / x 0, x j / x 0⟯ = ⊤)
    (hbj : k⟮x b / x 0, x j' / x 0⟯ = ⊤) :
    let pr₁ : K → L := fun g => algebraMap (K ⊗[k] K) L (g ⊗ₜ (1 : K))
    let pr₂ : K → L := fun g => algebraMap (K ⊗[k] K) L ((1 : K) ⊗ₜ g)
    let F := k⟮pr₁ (x a / x 0), pr₂ (x b / x 0)⟯
    let v : Fin N × Fin N → L := fun ν =>
      pr₁ (x j / x 0) ^ (ν.1 : ℕ) * pr₂ (x j' / x 0) ^ (ν.2 : ℕ)
    LinearIndependent F v ∧ Submodule.span F (Set.range v) = ⊤ := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_adjoin_eq_top haj hN (hdeg a ha)
  obtain ⟨d, hd⟩ := exists_basis_pow_of_adjoin_eq_top hbj hN (hdeg b hb)
  intro pr₁ pr₂ F v
  have hv : v = fun i => algebraMap (K ⊗[k] K) L (e i.1 ⊗ₜ 1) *
      algebraMap (K ⊗[k] K) L (1 ⊗ₜ d i.2) := by
    funext i
    simp only [v, pr₁, pr₂, he, hd, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hv]
  exact linearIndependent_and_span_tmul_eq_top e d

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `P` a divisor of degree one supported on closed points, `N ≥ 2g + 1`, and `x₀, …, xₙ` a
`k`-basis of `L(NP)` satisfying (G1) for `NP` and (G2), with `ξ_ν = x_ν / x₀`. Let `L` be a field
of fractions of `k(C) ⊗[k] k(C)`, the function field of `C × C`. For `a, b, j, j' ≠ 0` with
`j ≠ a` and `j' ≠ b`, the monomials `(ξ_j ⊗ 1)^i (1 ⊗ ξ_{j'})^{i'}`, `(i, i') ∈ Fin N × Fin N`, are
linearly independent over `k⟮ξ_a ⊗ 1, 1 ⊗ ξ_b⟯` and span `L` over it. -/
@[faltings "lem_bvs_monomial_basis"]
public theorem linearIndependent_and_span_monomial_eq_top (k : Type u) [Field k]
    [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f) (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (L : Type u) [Field L] [Algebra k L]
    [letI := functionFieldAlgebra k f; Algebra (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsScalarTower k (C.functionField ⊗[k] C.functionField) L]
    [letI := functionFieldAlgebra k f; IsFractionRing (C.functionField ⊗[k] C.functionField) L]
    (a b j j' : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (hj : j ≠ 0) (hj' : j' ≠ 0)
    (hja : j ≠ a) (hjb : j' ≠ b) :
    letI := functionFieldAlgebra k f
    let pr₁ : C.functionField → L := fun g =>
      algebraMap (C.functionField ⊗[k] C.functionField) L (g ⊗ₜ (1 : C.functionField))
    let pr₂ : C.functionField → L := fun g =>
      algebraMap (C.functionField ⊗[k] C.functionField) L ((1 : C.functionField) ⊗ₜ g)
    let F := k⟮pr₁ (x a / x 0), pr₂ (x b / x 0)⟯
    let v : Fin N × Fin N → L := fun ν =>
      pr₁ (x j / x 0) ^ (ν.1 : ℕ) * pr₂ (x j' / x 0) ^ (ν.2 : ℕ)
    LinearIndependent F v ∧ Submodule.span F (Set.range v) = ⊤ := by
  let := functionFieldAlgebra k f
  exact linearIndependent_and_span_monomial_of_finrank_eq (by omega) x
    (fun c hc => finrank_adjoin_div_eq k f hg _ (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hli hspan hG1 c hc)
    ha hb (hG2 a j ha hj hja.symm) (hG2 b j' hb hj' hjb.symm)

end Faltings.BombieriSiegel
