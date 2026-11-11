module
public import Mordell.Polynomial.MonomialCard
public import Mordell.Height.Affine.LocalSize.Sum
public import Mordell.Height.Affine.LocalSize.Eval

/-!
# The local size of a product of polynomials

Let `K` be a number field, `v` a place of `K` and `|·|_v` Bombieri's normalised absolute value at
`v`. For a polynomial `f` in any number of variables with coefficients in `K`, let `|f|_v` be the
maximum of `|c|_v` over the coefficients `c` of `f`, and `#f` the number of its monomials
(`Faltings.MvPolynomial.monomialCount`). Each coefficient of `f₁ f₂` is a sum of at most
`μ = min(#f₁, #f₂)` products of a coefficient of `f₁` and one of `f₂`, so
`|f₁ f₂|_v ≤ μ ^ κ_v |f₁|_v |f₂|_v`, where `κ_v` is the local weight
`Faltings.NumberField.localWeight`.

## Main definitions

* `Faltings.MvPolynomial.localSize`: the local size `|f|_v` of a polynomial.

## Main results

* `Faltings.MvPolynomial.localSize_mul_le`: `|f₁ f₂|_v ≤ min(#f₁, #f₂) ^ κ_v |f₁|_v |f₂|_v`.

## Implementation notes

A place of `K` is a term of `InfinitePlace K ⊕ FinitePlace K`. Bombieri's normalised absolute
value is `|x|_v = w x ^ (n_w / [K : ℚ])` at an infinite place `w` (with `n_w = w.mult`) and
`|x|_v = w x ^ (1 / [K : ℚ])` at a finite place `w`, where `w x` is Mathlib's absolute value
(`‖σ x‖`, respectively `N(𝔭) ^ (-v_𝔭(x))`). The maximum `|f|_v` is taken over the support of `f`,
as an `iSup` of nonnegative reals; it is `0` when `f = 0`. The power `μ ^ κ_v` is a real power.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 7 and 8
-/

namespace Faltings.MvPolynomial

open _root_.NumberField Module Faltings.NumberField

@[expose] public section

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

/-- The local size `|f|_v`: the largest `|c|_v` over the coefficients `c` of `f`, and `0` for
`f = 0`. -/
noncomputable def localSize (v : InfinitePlace K ⊕ FinitePlace K)
    (f : _root_.MvPolynomial σ K) : ℝ :=
  ⨆ m : f.support, normalizedAbs v (f.coeff m)

/-- The local size `|f|_v` is nonnegative. -/
lemma localSize_nonneg (v : InfinitePlace K ⊕ FinitePlace K) (f : _root_.MvPolynomial σ K) :
    0 ≤ localSize v f :=
  Real.iSup_nonneg fun _ => normalizedAbs_nonneg v _

/-- Every coefficient of `f` has `|c|_v ≤ |f|_v`. -/
lemma normalizedAbs_coeff_le_localSize (v : InfinitePlace K ⊕ FinitePlace K)
    (f : _root_.MvPolynomial σ K) (m : σ →₀ ℕ) : normalizedAbs v (f.coeff m) ≤ localSize v f := by
  by_cases hm : m ∈ f.support
  · exact le_ciSup (f := fun m : f.support => normalizedAbs v (f.coeff m))
      (Set.finite_range _).bddAbove ⟨m, hm⟩
  · rw [_root_.MvPolynomial.notMem_support_iff.mp hm, map_zero]
    exact localSize_nonneg v f

end

section

variable {K : Type*} [Field K] [NumberField K]

/-- The one-sided bound `|f₁ f₂|_v ≤ (#f₁) ^ κ_v |f₁|_v |f₂|_v`: write `f₁ f₂` as the sum over
the monomials `c_a X^a` of `f₁` of `c_a X^a f₂`, whose coefficients have size at most
`|f₁|_v |f₂|_v`, and apply `iSup_normalizedAbs_sum_le`. -/
private lemma localSize_mul_le_left {σ : Type*} (f₁ f₂ : _root_.MvPolynomial σ K)
    (v : InfinitePlace K ⊕ FinitePlace K) :
    localSize v (f₁ * f₂) ≤
      ((monomialCount f₁ : ℕ) : ℝ) ^ NumberField.localWeight K v *
        (localSize v f₁ * localSize v f₂) := by
  rcases f₁.support.eq_empty_or_nonempty with h₁ | h₁
  · simp [localSize, _root_.MvPolynomial.support_eq_empty.mp h₁]
  let F a := AddMonoidAlgebra.coeff (_root_.MvPolynomial.monomial a (f₁.coeff a) * f₂)
  have hsum : AddMonoidAlgebra.coeff (f₁ * f₂) = ∑ a ∈ f₁.support, F a := by
    rw [← AddMonoidAlgebra.coeff_sum]
    conv_lhs => rw [f₁.as_sum, Finset.sum_mul]
  have hF (a c : σ →₀ ℕ) : normalizedAbs v (F a c) ≤ localSize v f₁ * localSize v f₂ := by
    change normalizedAbs v ((_root_.MvPolynomial.monomial a (f₁.coeff a) * f₂).coeff c) ≤ _
    rw [_root_.MvPolynomial.coeff_monomial_mul']
    split_ifs
    · rw [map_mul]
      exact mul_le_mul (normalizedAbs_coeff_le_localSize ..) (normalizedAbs_coeff_le_localSize ..)
        (normalizedAbs_nonneg ..) (localSize_nonneg ..)
    · rw [map_zero]; exact mul_nonneg (localSize_nonneg ..) (localSize_nonneg ..)
  have hP := mul_nonneg (localSize_nonneg v f₁) (localSize_nonneg v f₂)
  calc localSize v (f₁ * f₂)
      = ⨆ c : (∑ t ∈ f₁.support, F t).support, normalizedAbs v ((∑ t ∈ f₁.support, F t) c) := by
        rw [← hsum]; rfl
    _ ≤ _ := NumberField.iSup_normalizedAbs_sum_le v h₁ F
    _ ≤ _ := by
        gcongr
        exact Real.iSup_le (fun t => Real.iSup_le (fun c => hF t c) hP) hP

end

/-- For polynomials `f₁ f₂` over a number field `K` and a place `v` of `K`,
`|f₁ f₂|_v ≤ μ ^ κ_v |f₁|_v |f₂|_v` with `μ = min (#f₁) (#f₂)`, where `|f|_v` is the maximum of
Bombieri's normalised absolute values of the coefficients of `f` and `κ_v` is
`Faltings.NumberField.localWeight K v`. -/
@[faltings "lem_bvs_local_size"]
public theorem localSize_mul_le {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f₁ f₂ : _root_.MvPolynomial σ K) (v : InfinitePlace K ⊕ FinitePlace K) :
    let absv : K → ℝ := fun x =>
      Sum.elim (fun w : InfinitePlace K => w x ^ ((w.mult : ℝ) / finrank ℚ K))
        (fun w : FinitePlace K => w x ^ ((1 : ℝ) / finrank ℚ K)) v
    let size : _root_.MvPolynomial σ K → ℝ := fun f => ⨆ m : f.support, absv (f.coeff m)
    size (f₁ * f₂) ≤
      ((min (monomialCount f₁) (monomialCount f₂) : ℕ) : ℝ) ^ NumberField.localWeight K v *
        size f₁ * size f₂ := by
  intro absv size
  change localSize v (f₁ * f₂) ≤ _ * localSize v f₁ * localSize v f₂
  rw [mul_assoc]
  rcases min_choice (monomialCount f₁) (monomialCount f₂) with h | h <;> rw [h]
  · exact localSize_mul_le_left f₁ f₂ v
  · rw [mul_comm (localSize v f₁), mul_comm f₁]
    exact localSize_mul_le_left f₂ f₁ v

end Faltings.MvPolynomial
