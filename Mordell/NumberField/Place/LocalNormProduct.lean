module

public import Mordell.NumberField.Place.LocalDegreeSum

/-!
# The global norm is the product of the local norms

Let `k ⊆ K` be number fields, `v` a place of `k` and `y ∈ K`. For each place `w` of `K` lying
over `v` the completion `K_w` is a finite extension of `k_v`, and
`∏_{w ∣ v} N_{K_w/k_v}(y) = N_{K/k}(y)` in `k_v`. This comes from the isomorphism of
`k_v`-algebras `K ⊗_k k_v ≃ ∏_{w ∣ v} K_w`.

The natural map `k_v ⊗_k K → ∏_{w ∣ v} K_w` is surjective: its image is a finite-dimensional
`k_v`-subspace, hence closed, and it contains the image of `K`, which is dense by weak
approximation (`InfinitePlace.denseRange_algebraMap_pi` for infinite `v`,
`Faltings.denseRange_embedding_pi` for finite `v`). Both sides have `k_v`-dimension
`[K : k]` by `Faltings.NumberFieldPlace.finsum_localDegree_eq_finrank`, so the map is an
isomorphism. Multiplication by `y` on `K`, written in a `k`-basis, therefore has the same
determinant as multiplication by `(y)_w` on `∏_{w ∣ v} K_w`, and the determinant of a
block-diagonal map is the product of the determinants of its blocks.

## Main results

* `Faltings.finprod_norm_completion_eq_norm`: the global norm `Algebra.norm k y` is the product
  of the local norms over the places lying over `v`, separately for finite and for infinite `v`.

## Implementation notes

A place is a finite or an infinite place (`Faltings.NumberFieldPlace`), and the completions of
the two kinds are different types, so the statement is a conjunction of the finite and the
infinite case.

The tensor product is not formed: a `k`-basis `b` of `K` identifies `k_v ⊗_k K` with
`Fin [K : k] → k_v`, and the map to `∏_{w ∣ v} K_w` is `Fintype.linearCombination` of the images
of `b`.

For an infinite place the embedding `k_v → K_w` is Mathlib's `NumberField.LiesOver.completionMap`,
through the scoped instance `NumberField.LiesOver.instAlgebraCompletion`. For a finite place
Mathlib has no map of adic completions. The statement therefore takes, for each `w ∣ v`, a ring
homomorphism `φ w : k_v →+* K_w` that is continuous and extends `k → K → K_w`. Such a map exists,
and since `k` is dense in `k_v` it is unique, so this hypothesis names the canonical embedding.

## References

* [Z. Gao, *Heights*][gao2022], Lemma 1.1.10.
* [J. Neukirch, *Algebraic Number Theory*][neukirch1999], Ch. II, Prop. 8.3.
-/

@[expose] public section

namespace Faltings

open Module NumberField IsDedekindDomain
open scoped NumberField.LiesOver

universe u v

/-- The determinant of a block-diagonal endomorphism of a finite product of finite free modules
is the product of the determinants of the blocks. -/
private theorem det_pi_heterogeneous {R : Type*} [CommRing R] :
    ∀ (ι : Type u) [Fintype ι] (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i),
      LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i) := by
  intro ι _
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ (M : ι → Type v)
      [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i),
      LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i))
    ?_ ?_ ?_ ι
  · intro α β _ e h M _ _ _ _ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h' := h (fun a => M (e a)) (fun a => f (e a))
    let E : ((a : α) → M (e a)) ≃ₗ[R] ((b : β) → M b) := LinearEquiv.piCongrLeft R M e
    rw [← Equiv.prod_comp e, ← h', ← LinearMap.det_conj _ E]
    congr 1
    ext x b
    obtain ⟨a, rfl⟩ := e.surjective b
    have h1 : ∀ y : (a : α) → M (e a), E y (e a) = y a :=
      fun y => Equiv.piCongrLeft_apply_apply M e y a
    have h2 : E.symm x a = x (e a) := by
      rw [← h1 (E.symm x), LinearEquiv.apply_symm_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h1]
    simp [h2]
  · intro M _ _ _ _ f
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact LinearMap.det_eq_one_of_subsingleton _
  · intro α _ h M _ _ _ _ f
    let E := LinearEquiv.piOptionEquivProd (R := R) (M := M)
    rw [Fintype.prod_option, ← h (fun a => M (some a)) (fun a => f (some a)),
      ← LinearMap.det_prodMap, ← LinearMap.det_conj _ E]
    congr 1

/-- The norm of an element of a finite product of finite free algebras is the product of the
norms of its components. -/
private theorem norm_pi {F : Type*} [CommRing F] {ι : Type u} [Fintype ι] {L : ι → Type v}
    [∀ i, CommRing (L i)] [∀ i, Algebra F (L i)] [∀ i, Module.Free F (L i)]
    [∀ i, Module.Finite F (L i)] (x : ∀ i, L i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  simp only [Algebra.norm_apply]
  rw [← det_pi_heterogeneous]
  congr 1

/-- The diagonal image of `K` lies in the `F`-span of the image of a `k`-basis of `K`. -/
private theorem range_subset_span_basis {k K F : Type*} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] {ι : Type u} {L : ι → Type v} [∀ i, Field (L i)]
    [∀ i, Algebra F (L i)] (ψ : ∀ i, K →+* L i)
    (hψ : ∀ i x, ψ i (algebraMap k K x) = algebraMap F (L i) (algebraMap k F x))
    {β : Type*} [Fintype β] (b : Basis β k K) :
    Set.range (fun y i => ψ i y) ⊆ Submodule.span F (Set.range fun j i => ψ i (b j)) := by
  rintro _ ⟨z, rfl⟩
  have : (fun i => ψ i z) = ∑ j, algebraMap k F (b.repr z j) • fun i => ψ i (b j) := by
    conv_lhs => rw [← b.sum_repr z]
    ext i
    simp [map_sum, Algebra.smul_def, hψ]
  change (fun i => ψ i z) ∈ _
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Let `K/k` be a finite extension, `F` an extension of `k`, and `ψ i : K → L i` embeddings
into finite extensions of `F` compatible on `k`. If the `F`-span of the diagonal image of `K` in
`∏ i, L i` is everything and `∑ i, [L i : F] = [K : k]`, then the natural map
`F ⊗_k K → ∏ i, L i` is an isomorphism, so `∏ i, N_{L i / F}(ψ i y) = N_{K/k}(y)` in `F`. -/
private theorem prod_norm_eq_algebraMap_norm {k K F : Type*} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [FiniteDimensional k K] {ι : Type u} [Fintype ι]
    {L : ι → Type v} [∀ i, Field (L i)] [∀ i, Algebra F (L i)] [∀ i, FiniteDimensional F (L i)]
    (ψ : ∀ i, K →+* L i)
    (hψ : ∀ i x, ψ i (algebraMap k K x) = algebraMap F (L i) (algebraMap k F x))
    (hspan : Submodule.span F (Set.range fun y i => ψ i y) = ⊤)
    (hdim : ∑ i, finrank F (L i) = finrank k K) (y : K) :
    ∏ i, Algebra.norm F (ψ i y) = algebraMap k F (Algebra.norm k y) := by
  classical
  rw [← norm_pi (fun i => ψ i y)]
  set n := finrank k K
  let b := Module.finBasis k K
  let ψ' : K →+* ∀ i, L i := RingHom.pi ψ
  have hψ'smul : ∀ (c : k) a, ψ' (c • a) = algebraMap k F c • ψ' a := fun c a => by
    ext i
    simp only [ψ', Algebra.smul_def, map_mul, Pi.mul_apply, Pi.smul_apply]
    change ψ i (algebraMap k K c) * ψ i a = _
    rw [hψ]
    rfl
  have hψ'sum : ∀ (c : Fin n → k), ψ' (∑ j, c j • b j) = ∑ j, algebraMap k F (c j) • ψ' (b j) := by
    intro c
    simp [map_sum, hψ'smul]
  let Ψ : (Fin n → F) →ₗ[F] (∀ i, L i) := Fintype.linearCombination F (fun j => ψ' (b j))
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hspan]
    exact Submodule.span_le.2 (range_subset_span_basis ψ hψ b)
  have hinj : Function.Injective Ψ := by
    rwa [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, hdim]
  let E := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  let M := LinearMap.toMatrix b b (Algebra.lmul k K y)
  have key' : Algebra.lmul F (∀ i, L i) (ψ' y) ∘ₗ Ψ =
      Ψ ∘ₗ Matrix.toLin' (M.map (algebraMap k F)) := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    have hyb : y * b j = ∑ i, M i j • b i := by
      simp only [M, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul]
      exact (b.sum_repr _).symm
    simp only [LinearMap.comp_apply, Ψ, LinearMap.coe_single, Fintype.linearCombination_apply,
      Algebra.coe_lmul_eq_mul, Matrix.toLin'_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, LinearMap.mul_apply']
    rw [← map_mul, hyb, hψ'sum]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, M]
  have key : Algebra.lmul F (∀ i, L i) (ψ' y) =
      (E : (Fin n → F) →ₗ[F] _) ∘ₗ Matrix.toLin' (M.map (algebraMap k F)) ∘ₗ
        (E.symm : _ →ₗ[F] _) := by
    have : (E : (Fin n → F) →ₗ[F] _) = Ψ := rfl
    rw [← LinearMap.comp_assoc, this, ← key', LinearMap.comp_assoc, ← this]
    ext x : 1
    simp
  rw [Algebra.norm_apply]
  change LinearMap.det (Algebra.lmul F (∀ i, L i) (ψ' y)) = _
  rw [key, LinearMap.det_conj, LinearMap.det_toLin', Algebra.norm_apply,
    ← LinearMap.det_toMatrix b, RingHom.map_det]
  rfl

/-- In a Hausdorff topological vector space over a complete nontrivially normed field, the span
of a finite set containing a dense set is the whole space. -/
private theorem span_eq_top_of_denseRange {F E X : Type*} [NontriviallyNormedField F]
    [CompleteSpace F] [AddCommGroup E] [Module F E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul F E] [T2Space E] {B : Set E} (hB : B.Finite) {f : X → E} (hf : DenseRange f)
    (hsub : Set.range f ⊆ Submodule.span F B) : Submodule.span F B = ⊤ := by
  have : FiniteDimensional F (Submodule.span F B) := FiniteDimensional.span_of_finite F hB
  exact eq_top_iff.2 fun x _ =>
    closure_minimal hsub (Submodule.span F B).closed_of_finiteDimensional (hf x)

/-- Let `K/k` be a finite extension, `F ⊇ k` a complete nontrivially normed field and
`ψ i : K → L i` embeddings into Hausdorff topological `F`-algebras, compatible on `k`, such that
`K` is dense in `∏ i, L i` and `∑ i, [L i : F] = [K : k]`. Then
`∏ i, N_{L i / F}(ψ i y) = N_{K/k}(y)`. -/
private theorem prod_norm_eq_algebraMap_norm_of_denseRange {k K F : Type*} [Field k] [Field K]
    [NontriviallyNormedField F] [CompleteSpace F] [Algebra k K] [Algebra k F]
    [FiniteDimensional k K] {ι : Type u} [Fintype ι] {L : ι → Type v} [∀ i, Field (L i)]
    [∀ i, Algebra F (L i)] [∀ i, TopologicalSpace (L i)] [∀ i, IsTopologicalAddGroup (L i)]
    [∀ i, ContinuousSMul F (L i)] [∀ i, T2Space (L i)] (ψ : ∀ i, K →+* L i)
    (hψ : ∀ i x, ψ i (algebraMap k K x) = algebraMap F (L i) (algebraMap k F x))
    (hdense : DenseRange fun y i => ψ i y)
    (hdim : ∀ _ : ∀ i, FiniteDimensional F (L i), ∑ i, finrank F (L i) = finrank k K) (y : K) :
    ∏ i, Algebra.norm F (ψ i y) = algebraMap k F (Algebra.norm k y) := by
  classical
  let b := Module.finBasis k K
  have hsub := range_subset_span_basis ψ hψ b
  have htop := span_eq_top_of_denseRange (Set.finite_range _) hdense hsub
  have hspan : Submodule.span F (Set.range fun y i => ψ i y) = ⊤ :=
    eq_top_iff.2 (htop ▸ Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨b j, rfl⟩))
  have : FiniteDimensional F (∀ i, L i) :=
    Module.finite_def.2 (htop ▸ Submodule.fg_span (Set.finite_range _))
  have hfin : ∀ i, FiniteDimensional F (L i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj i : (∀ i, L i) →ₗ[F] L i)
      (fun x => ⟨Pi.single i x, by simp⟩)
  exact prod_norm_eq_algebraMap_norm ψ hψ hspan (hdim hfin) y

section Places

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The global norm is the product of the local norms over the infinite places above `v`. -/
private theorem finprod_norm_infinitePlace (y : K) (v : InfinitePlace k) :
    ∏ᶠ w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)},
      (haveI : w.1.LiesOver v := w.2
      Algebra.norm v.Completion (algebraMap K w.1.Completion y)) =
      algebraMap k v.Completion (Algebra.norm k y) := by
  classical
  rw [finprod_eq_prod_of_fintype]
  let : ∀ w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)},
      Algebra v.Completion w.1.Completion := fun w =>
    @LiesOver.instAlgebraCompletion _ _ _ _ _ v w.1 w.2
  have : ∀ w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)},
      ContinuousSMul v.Completion w.1.Completion := fun w =>
    @LiesOver.instContinuousSMulCompletion _ _ _ _ _ v w.1 w.2
  have h2 : ‖(2 : v.Completion)‖ = 2 := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _), map_ofNat]
    norm_num
  let : NontriviallyNormedField v.Completion := NontriviallyNormedField.ofNormNeOne
    ⟨2, fun h => by rw [h, norm_zero] at h2; norm_num at h2, by rw [h2]; norm_num⟩
  refine prod_norm_eq_algebraMap_norm_of_denseRange (F := v.Completion)
    (L := fun w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)} =>
      w.1.Completion)
    (fun w => algebraMap K w.1.Completion) (fun w x => ?_) ?_ (fun _ => ?_) y
  · have : w.1.LiesOver v := w.2
    exact @IsScalarTower.algebraMap_apply _ _ _ _ _ _ _ _ _
      (@LiesOver.instIsScalarTowerCompletion _ _ _ _ _ v w.1 w.2) x
  · let r : (∀ w : InfinitePlace K, WithAbs w.1) →
        ∀ w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)}, WithAbs w.1.1 :=
      fun x w => x w.1
    have hr : Function.Surjective r := fun z =>
      ⟨fun w => if h : NumberFieldPlace.LiesOver (.inr w) (.inr v) then z ⟨w, h⟩ else 0, by
        ext w
        simp only [r]
        rw [dif_pos w.2]⟩
    have hrc : Continuous r := continuous_pi fun w => continuous_apply w.1
    exact (DenseRange.piMap
      (ι := {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)})
      (X := fun w => WithAbs w.1.1) (Y := fun w => w.1.Completion)
      (f := fun w x => (x : w.1.Completion))
      fun w => InfinitePlace.Completion.denseRange_coe w.1).comp
      (hr.denseRange.comp (InfinitePlace.denseRange_algebraMap_pi K) hrc)
      (Continuous.piMap fun w => InfinitePlace.Completion.continuous_coe w.1)
  · have h :=
      NumberFieldPlace.finsum_localDegree_eq_finrank (K := K) (Sum.inr v : NumberFieldPlace k)
    rw [← finsum_comp_equiv (NumberFieldPlace.infinitePlaceLiesOverEquiv v),
      finsum_eq_sum_of_fintype] at h
    exact h

open scoped Valued in
/-- The global norm is the product of the local norms over the finite places above `v`, the
completions `K_w` being `k_v`-algebras through given continuous embeddings `k_v → K_w` extending
`k → K → K_w`. -/
private theorem finprod_norm_finitePlace (y : K) (v : FinitePlace k)
    (φ : ∀ w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)},
      (FinitePlace.maximalIdeal v).adicCompletion k →+*
        (FinitePlace.maximalIdeal w.1).adicCompletion K)
    (hc : ∀ w, Continuous (φ w))
    (hφ : ∀ w x, φ w (algebraMap k _ x) = algebraMap K _ (algebraMap k K x)) :
    ∏ᶠ w, (letI := (φ w).toAlgebra
      Algebra.norm ((FinitePlace.maximalIdeal v).adicCompletion k)
        (algebraMap K ((FinitePlace.maximalIdeal w.1).adicCompletion K) y)) =
      algebraMap k _ (Algebra.norm k y) := by
  classical
  have := Fintype.ofFinite {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)}
  rw [finprod_eq_prod_of_fintype]
  let : ∀ w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)},
      Algebra ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w.1).adicCompletion K) := fun w => (φ w).toAlgebra
  have : ∀ w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)},
      ContinuousSMul ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w.1).adicCompletion K) := fun w =>
    ⟨((hc w).comp continuous_fst).mul continuous_snd⟩
  refine prod_norm_eq_algebraMap_norm_of_denseRange
    (F := (FinitePlace.maximalIdeal v).adicCompletion k)
    (L := fun w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)} =>
      (FinitePlace.maximalIdeal w.1).adicCompletion K)
    (fun w => algebraMap K _) (fun w x => (hφ w x).symm)
    (denseRange_embedding_pi (K := K) (P := fun w => FinitePlace.maximalIdeal w.1)
      fun _ _ h => Subtype.ext (FinitePlace.maximalIdeal_injective h))
    (fun _ => ?_) y
  have hloc : ∀ w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)},
      NumberFieldPlace.localDegree (.inl w.1) (.inl v) w.2 =
        finrank ((FinitePlace.maximalIdeal v).adicCompletion k)
          ((FinitePlace.maximalIdeal w.1).adicCompletion K) := by
    intro w
    have hex : ∃ ψ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
        (FinitePlace.maximalIdeal w.1).adicCompletion K, Continuous ψ ∧
          ∀ x : k, ψ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
            FinitePlace.embedding (FinitePlace.maximalIdeal w.1) (algebraMap k K x) :=
      ⟨φ w, hc w, hφ w⟩
    have huniq : hex.choose = φ w :=
      DFunLike.coe_injective <|
        (HeightOneSpectrum.denseRange_algebraMap (K := k) (FinitePlace.maximalIdeal v)).equalizer
          hex.choose_spec.1 (hc w)
          (funext fun x => (hex.choose_spec.2 x).trans (hφ w x).symm)
    simp only [NumberFieldPlace.localDegree, dif_pos hex]
    rw [huniq]
  have h := NumberFieldPlace.finsum_localDegree_eq_finrank (K := K) (Sum.inl v : NumberFieldPlace k)
  rw [← finsum_comp_equiv (NumberFieldPlace.finitePlaceLiesOverEquiv v),
    finsum_eq_sum_of_fintype] at h
  rw [← h]
  exact Finset.sum_congr rfl fun w _ => (hloc w).symm

end Places

/-- For number fields `k ⊆ K`, a place `v` of `k` and `y ∈ K`, the product over the places `w`
of `K` lying over `v` of the local norms `N_{K_w/k_v}(y)` is the global norm `N_{K/k}(y)`, viewed
in `k_v`.

For finite `v`, the embeddings `φ w : k_v → K_w` are given as the continuous ring homomorphisms
extending `k → K → K_w`. For infinite `v` they are `NumberField.LiesOver.completionMap`. -/
@[faltings "lem_ht_local_norm_product"]
theorem finprod_norm_completion_eq_norm {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (y : K) :
    (∀ (v : FinitePlace k)
      (φ : ∀ w : {w : FinitePlace K // NumberFieldPlace.LiesOver (.inl w) (.inl v)},
        (FinitePlace.maximalIdeal v).adicCompletion k →+*
          (FinitePlace.maximalIdeal w.1).adicCompletion K),
      (∀ w, Continuous (φ w)) →
      (∀ w x, φ w (algebraMap k _ x) = algebraMap K _ (algebraMap k K x)) →
      ∏ᶠ w, (letI := (φ w).toAlgebra
        Algebra.norm ((FinitePlace.maximalIdeal v).adicCompletion k)
          (algebraMap K ((FinitePlace.maximalIdeal w.1).adicCompletion K) y)) =
        algebraMap k _ (Algebra.norm k y)) ∧
    ∀ v : InfinitePlace k,
      ∏ᶠ w : {w : InfinitePlace K // NumberFieldPlace.LiesOver (.inr w) (.inr v)},
        (haveI : w.1.LiesOver v := w.2
        Algebra.norm v.Completion (algebraMap K w.1.Completion y)) =
        algebraMap k v.Completion (Algebra.norm k y) :=
  ⟨finprod_norm_finitePlace y, finprod_norm_infinitePlace y⟩

end Faltings
