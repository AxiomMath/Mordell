module
public import Mordell.Height.Affine.LocalSize.Prod

/-!
# The local size of a power of a polynomial

Let `K` be a number field, `v` a place of `K`, and for a polynomial `f` in any number of
variables over `K` let `|f|_v` be the maximum of Bombieri's normalised absolute values `|c|_v`
of its coefficients. For every integer `e ≥ 1`,
`|f ^ e|_v ≤ (#f) ^ ((e - 1) κ_v) |f|_v ^ e`, where `#f` is the number of monomials of `f`
(`Faltings.MvPolynomial.monomialCount`) and `κ_v` is the local weight of `v`
(`Faltings.NumberField.localWeight`). At a finite place `κ_v = 0` and this is the
ultrametric inequality.

## Main results

* `Faltings.NumberField.iSup_coeff_pow_le`: `|f ^ e|_v ≤ (#f) ^ ((e - 1) κ_v) |f|_v ^ e`.

## Implementation notes

A place of `K` is a term of `InfinitePlace K ⊕ FinitePlace K`, as for `localWeight`. Bombieri's
normalised absolute value is `|c|_v = ‖c‖_w ^ (n_w / [K : ℚ])` at an infinite place `w`, with
`n_w = InfinitePlace.mult w`, and `|c|_v = ‖c‖_w ^ (1 / [K : ℚ])` at a finite place `w`, whose
Mathlib absolute value is `N(𝔭) ^ (-v_𝔭(c))`. These are the conventions of
`Faltings.affineLogHeight`; the statement writes them out, and the proof identifies them with
`Faltings.NumberField.normalizedAbs` and `Faltings.MvPolynomial.localSize`. The size `|f|_v` is
the supremum over the support of `f`; it is `0`
when `f = 0`. The exponent `(e - 1) κ_v` is real, so the power of `#f` is `Real.rpow`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 7 and 8
-/

namespace Faltings.NumberField

open _root_.NumberField Module

/-- Iterating `S (x * y) ≤ A * S x * S y` gives `S (x ^ (n + 1)) ≤ A ^ n * S x ^ (n + 1)`. -/
private lemma apply_pow_succ_le_of_le_mul {M : Type*} [Monoid M] (S : M → ℝ) {A : ℝ} {x : M}
    (hA : 0 ≤ A) (hx : 0 ≤ S x) (h : ∀ n : ℕ, S (x * x ^ n) ≤ A * S x * S (x ^ n)) (n : ℕ) :
    S (x ^ (n + 1)) ≤ A ^ n * S x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc S (x ^ (n + 1 + 1)) = S (x * x ^ (n + 1)) := by rw [pow_succ']
      _ ≤ A * S x * (A ^ n * S x ^ (n + 1)) := (h _).trans (by gcongr)
      _ = A ^ (n + 1) * S x ^ (n + 1 + 1) := by ring

/-- For a polynomial `f` over a number field `K`, a place `v` of `K` and `e ≥ 1`,
`|f ^ e|_v ≤ (#f) ^ ((e - 1) κ_v) |f|_v ^ e`, where `|·|_v` is the maximum of the normalised
absolute values of the coefficients, `#f = monomialCount f` and `κ_v = localWeight K v`. -/
@[faltings "lem_bvs_local_size_power"]
public theorem iSup_coeff_pow_le (K : Type*) [Field K] [NumberField K] {σ : Type*}
    (v : InfinitePlace K ⊕ FinitePlace K) (f : _root_.MvPolynomial σ K) {e : ℕ} (he : 1 ≤ e) :
    let absv : K → ℝ := Sum.elim (fun w c => w c ^ ((w.mult : ℝ) / finrank ℚ K))
      (fun w c => w c ^ ((1 : ℝ) / finrank ℚ K)) v
    (⨆ m : (f ^ e).support, absv ((f ^ e).coeff m)) ≤
      (Faltings.MvPolynomial.monomialCount f : ℝ) ^ (((e - 1 : ℕ) : ℝ) * localWeight K v) *
        (⨆ m : f.support, absv (f.coeff m)) ^ e := by
  intro absv
  rw [show absv = normalizedAbs v by rcases v with w | w <;> rfl]
  change MvPolynomial.localSize v (f ^ e) ≤ _ * MvPolynomial.localSize v f ^ e
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' he
  rw [Nat.add_sub_cancel, mul_comm (n : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  refine apply_pow_succ_le_of_le_mul (MvPolynomial.localSize v)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (MvPolynomial.localSize_nonneg v f) (fun k => ?_) n
  have h : MvPolynomial.localSize v (f * f ^ k) ≤
      _ * MvPolynomial.localSize v f * MvPolynomial.localSize v (f ^ k) :=
    MvPolynomial.localSize_mul_le f (f ^ k) v
  refine h.trans ?_
  gcongr
  exacts [MvPolynomial.localSize_nonneg v _, MvPolynomial.localSize_nonneg v _,
    by rcases v with w | w <;> simp only [localWeight] <;> positivity, min_le_left _ _]

end Faltings.NumberField
