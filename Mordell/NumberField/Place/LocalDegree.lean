module

public import Mordell.NumberField.Place.LiesOver

/-!
# Local degrees

Let `k ⊆ K` be number fields, `v ∈ M_k` and `w ∈ M_K` with `w ∣ v`. Through the embedding
`k_v → K_w` extending `k → K → K_w`, the completion `K_w` is a finite extension of `k_v`, and the
*local degree* of `w` over `v` is `[K_w : k_v]`. For `w ∣ p ∈ M_ℚ` one writes
`n_w = [K_w : ℚ_p]`, the local degree of `w` over `p` for `ℚ ⊆ K`.

## Main definitions

* `Faltings.NumberFieldPlace.localDegree w v h`: the local degree `[K_w : k_v]` of the place `w` of
  `K` over the place `v` of `k`, where `h : w.LiesOver v`.

## Implementation notes

For infinite places `K_w` is `NumberField.InfinitePlace.Completion w`, a `k_v`-algebra through
Mathlib's `NumberField.LiesOver.completionMap` (the scoped instance
`NumberField.LiesOver.instAlgebraCompletion`), and the local degree is
`Module.finrank v.Completion w.Completion`.

For finite places `k_v` and `K_w` are the adic completions
`(FinitePlace.maximalIdeal v).adicCompletion k` and
`(FinitePlace.maximalIdeal w).adicCompletion K`, with `K → K_w` given by
`NumberField.FinitePlace.embedding`. The map `k_v → K_w` is the continuous ring homomorphism `φ`
with `φ x = FinitePlace.embedding w (algebraMap k K x)` for `x ∈ k`, and the local degree is
`Module.finrank k_v K_w` for the `k_v`-algebra structure `φ.toAlgebra`. When `w ∣ v` such a `φ`
exists (the absolute value of `w` restricts on `k` to a power of that of `v`, so `k → K_w` is
uniformly continuous and extends to the completion), and it is unique because `k` is dense in `k_v`
(`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`); the value `0` in the absence of such
a map is never taken. The local degree equals `e(w | v) f(w | v)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Lemma 1.1.8.
-/

@[expose] public section

namespace Faltings

open NumberField IsDedekindDomain
open scoped NumberField.LiesOver

open Classical in
/-- The *local degree* `[K_w : k_v]` of a place `w` of the number field `K` over a place `v` of
the subfield `k`, where `w ∣ v`. For infinite places it is `Module.finrank v.Completion
w.Completion`. For finite places it is `Module.finrank k_v K_w` of the adic completions, `K_w`
being a `k_v`-algebra through the continuous extension `k_v → K_w` of `k → K → K_w`. With
`k = ℚ` this is `n_w = [K_w : ℚ_p]` for `w ∣ p`. -/
@[faltings "def_ht_local_degree"]
noncomputable def NumberFieldPlace.localDegree {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] : (w : NumberFieldPlace K) → (v : NumberFieldPlace k) → w.LiesOver v → ℕ
  | .inl w, .inl v, _ =>
    if hφ : ∃ φ : (FinitePlace.maximalIdeal v).adicCompletion k →+*
        (FinitePlace.maximalIdeal w).adicCompletion K, Continuous φ ∧
          ∀ x : k, φ (algebraMap k ((FinitePlace.maximalIdeal v).adicCompletion k) x) =
            FinitePlace.embedding (FinitePlace.maximalIdeal w) (algebraMap k K x) then
      letI : Algebra ((FinitePlace.maximalIdeal v).adicCompletion k)
          ((FinitePlace.maximalIdeal w).adicCompletion K) := hφ.choose.toAlgebra
      Module.finrank ((FinitePlace.maximalIdeal v).adicCompletion k)
        ((FinitePlace.maximalIdeal w).adicCompletion K)
    else 0
  | .inr w, .inr v, h =>
    haveI : w.LiesOver v := h
    Module.finrank v.Completion w.Completion
  | .inl _, .inr _, h => h.elim
  | .inr _, .inl _, h => h.elim

end Faltings
