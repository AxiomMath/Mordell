module

public import Mordell.NumberField.Place.LocalDegree

/-!
# Local norms in a tower

Let `k ⊆ K` be number fields, `p` a place of `ℚ`, `v` a place of `k` over `p` and `w` a place of
`K` over `v`, so that the completions form a tower `ℚ_p ⊆ k_v ⊆ K_w`. For `x ∈ k_v`,
multiplication by `x` on the `k_v`-vector space `K_w` is the scalar `x`, so
`N_{K_w/k_v}(x) = x ^ [K_w : k_v]`; by transitivity of norms,
`N_{K_w/ℚ_p}(x) = N_{k_v/ℚ_p}(x) ^ [K_w : k_v]`, where `[K_w : k_v]` is the local degree
`Faltings.NumberFieldPlace.localDegree w v h`.

## Main results

* `Faltings.NumberFieldPlace.norm_completion_eq_norm_pow_localDegree`:
  `N_{K_w/ℚ_p}(x) = N_{k_v/ℚ_p}(x) ^ [K_w : k_v]` for `x ∈ k_v`, at finite and at infinite places.
* `Faltings.norm_algebraMap_of_isScalarTower`: the underlying identity
  `N_{A/R}(x) = N_{S/R}(x) ^ [A : S]` for a tower `R → S → A` of free algebras.

## Implementation notes

The statement is the conjunction of the finite and the infinite case. At infinite places the
completions are `NumberField.InfinitePlace.Completion`, and the embeddings `ℚ_p → k_v → K_w`
and `ℚ_p → K_w` are Mathlib's `NumberField.LiesOver.completionMap`. At finite places the
completions are the adic completions, and the embeddings `ψ : ℚ_p → k_v` and `φ : k_v → K_w` are
given as the continuous ring homomorphisms extending `ℚ → k → k_v` and `k → K → K_w`, as in
`Faltings.NumberFieldPlace.localDegree`; `K_w` is a `ℚ_p`-algebra through `φ ∘ ψ`.

## References

* [Z. Gao, *Heights*][gao2022], Lemma 1.1.9.
* [J. Neukirch, *Algebraic Number Theory*][neukirch1999], Ch. II, Prop. 8.3.
-/

@[expose] public section

namespace Faltings

open NumberField
open scoped NumberField.LiesOver

/-- In a tower `R → S → A` of commutative rings with `S` free over `R` and `A` free over `S`,
`N_{A/R}(x) = N_{S/R}(x) ^ [A : S]` for `x ∈ S`. -/
theorem norm_algebraMap_of_isScalarTower {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [Module.Free R S]
    [Module.Free S A] (x : S) :
    Algebra.norm R (algebraMap S A x) = Algebra.norm R x ^ Module.finrank S A := by
  rw [← Algebra.norm_norm (S := S), Algebra.norm_algebraMap, map_pow]

/-- At finite places the local degree is `[K_w : k_v]` for *any* continuous extension
`φ : k_v → K_w` of `k → K → K_w`: such an extension is unique, `k` being dense in `k_v`. -/
private theorem localDegree_inl_eq_finrank {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] {v : FinitePlace k} {w : FinitePlace K}
    (h : NumberFieldPlace.LiesOver (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k))
    (φ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
      (FinitePlace.maximalIdeal w).adicCompletion K) (hφc : Continuous φ)
    (hφk : ∀ x : k, φ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
      FinitePlace.embedding (FinitePlace.maximalIdeal w) (algebraMap k K x)) :
    NumberFieldPlace.localDegree (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k) h =
      letI := φ.toAlgebra
      Module.finrank ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w).adicCompletion K) := by
  have hex : ∃ χ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
      (FinitePlace.maximalIdeal w).adicCompletion K, Continuous χ ∧
        ∀ x : k, χ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
          FinitePlace.embedding (FinitePlace.maximalIdeal w) (algebraMap k K x) :=
    ⟨φ, hφc, hφk⟩
  have e : hex.choose = φ := by
    obtain ⟨hc, hk⟩ := hex.choose_spec
    apply RingHom.coe_inj
    refine ((FinitePlace.maximalIdeal v).denseRange_algebraMap k).equalizer hc hφc ?_
    funext y
    simp only [Function.comp_apply, hk, hφk]
  simp only [NumberFieldPlace.localDegree, dif_pos hex]
  rw [e]

/-- For places `u ∣ v ∣ w` (with `w ∣ u`) of a tower `K → L → M`, the composite of the induced
maps of completions is the induced map `u.Completion → w.Completion`, by density of `K`. -/
private theorem completionMap_comp {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {u : InfinitePlace K} {v : InfinitePlace L} {w : InfinitePlace M}
    [v.LiesOver u] [w.LiesOver v] [w.LiesOver u] :
    (LiesOver.completionMap (v := v) (w := w)).comp (LiesOver.completionMap (v := u) (w := v)) =
      LiesOver.completionMap (v := u) (w := w) := by
  apply RingHom.coe_inj
  refine (InfinitePlace.Completion.denseRange_coe u).equalizer
    ((LiesOver.continuous_completionMap v w).comp (LiesOver.continuous_completionMap u v))
    (LiesOver.continuous_completionMap u w) ?_
  funext x
  simp only [Function.comp_apply, RingHom.coe_comp, LiesOver.completionMap_coe]
  congr 2
  apply (WithAbs.equiv w.1).injective
  simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
    ← IsScalarTower.algebraMap_apply]

/-- **Local norms in a tower.** Let `k ⊆ K` be number fields, `v` a place of `k` over the place `p`
of `ℚ` and `w` a place of `K` over `v`. For `x ∈ k_v`,
`N_{K_w/ℚ_p}(x) = N_{k_v/ℚ_p}(x) ^ [K_w : k_v]`, with
`[K_w : k_v] = NumberFieldPlace.localDegree w v hwv`.

At finite places the embeddings `ψ : ℚ_p → k_v` and `φ : k_v → K_w` are the continuous ring
homomorphisms extending `ℚ → k → k_v` and `k → K → K_w`; at infinite places they are
`NumberField.LiesOver.completionMap`. -/
@[faltings "lem_ht_local_norm_tower"]
theorem NumberFieldPlace.norm_completion_eq_norm_pow_localDegree {k K : Type*} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] :
    (∀ (p : FinitePlace ℚ) (v : FinitePlace k) (w : FinitePlace K)
      (_hvp : NumberFieldPlace.LiesOver (.inl v : NumberFieldPlace k) (.inl p : NumberFieldPlace ℚ))
      (hwv : NumberFieldPlace.LiesOver (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k))
      (ψ : (FinitePlace.maximalIdeal p).adicCompletion ℚ →+*
        (FinitePlace.maximalIdeal v).adicCompletion k)
      (φ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
        (FinitePlace.maximalIdeal w).adicCompletion K),
      Continuous ψ →
      (∀ x : ℚ, ψ (algebraMap ℚ ((FinitePlace.maximalIdeal p).adicCompletion ℚ) x) =
        FinitePlace.embedding (FinitePlace.maximalIdeal v) (algebraMap ℚ k x)) →
      Continuous φ →
      (∀ x : k, φ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
        FinitePlace.embedding (FinitePlace.maximalIdeal w) (algebraMap k K x)) →
      ∀ x : (FinitePlace.maximalIdeal v).adicCompletion k,
        (letI := (φ.comp ψ).toAlgebra;
          Algebra.norm ((FinitePlace.maximalIdeal p).adicCompletion ℚ) (φ x)) =
        (letI := ψ.toAlgebra;
          Algebra.norm ((FinitePlace.maximalIdeal p).adicCompletion ℚ) x) ^
          NumberFieldPlace.localDegree (.inl w : NumberFieldPlace K) (.inl v : NumberFieldPlace k) hwv) ∧
    ∀ (p : InfinitePlace ℚ) (v : InfinitePlace k) (w : InfinitePlace K)
      (hvp : NumberFieldPlace.LiesOver (.inr v : NumberFieldPlace k) (.inr p : NumberFieldPlace ℚ))
      (hwv : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace k))
      (hwp : NumberFieldPlace.LiesOver (.inr w : NumberFieldPlace K) (.inr p : NumberFieldPlace ℚ)) (x : v.Completion),
      (haveI : v.LiesOver p := hvp; haveI : w.LiesOver v := hwv; haveI : w.LiesOver p := hwp;
      Algebra.norm p.Completion (algebraMap v.Completion w.Completion x) =
        Algebra.norm p.Completion x ^
          NumberFieldPlace.localDegree (.inr w : NumberFieldPlace K) (.inr v : NumberFieldPlace k) hwv) := by
  refine ⟨fun p v w _ hwv ψ φ _ _ hφc hφk x => ?_, fun p v w hvp hwv hwp x => ?_⟩
  · letI := ψ.toAlgebra
    letI := φ.toAlgebra
    letI : Algebra ((FinitePlace.maximalIdeal p).adicCompletion ℚ)
      ((FinitePlace.maximalIdeal w).adicCompletion K) := (φ.comp ψ).toAlgebra
    haveI : IsScalarTower ((FinitePlace.maximalIdeal p).adicCompletion ℚ)
        ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w).adicCompletion K) :=
      .of_algebraMap_eq fun _ => rfl
    rw [localDegree_inl_eq_finrank hwv φ hφc hφk]
    exact norm_algebraMap_of_isScalarTower x
  · haveI : v.LiesOver p := hvp
    haveI : w.LiesOver v := hwv
    haveI : w.LiesOver p := hwp
    haveI : IsScalarTower p.Completion v.Completion w.Completion :=
      .of_algebraMap_eq fun y => (RingHom.congr_fun completionMap_comp y).symm
    exact norm_algebraMap_of_isScalarTower (R := p.Completion) x

end Faltings
