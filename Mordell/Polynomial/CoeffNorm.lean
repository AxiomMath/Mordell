module
public import Mathlib
public import Mordell.Attr
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The `ℓ^∞`-norm of a polynomial

For a polynomial `f = ∑_I a_I t^I` in several variables with coefficients in a seminormed
commutative ring (the source takes `ℂ[t_1, …, t_n]`), its `ℓ^∞`-norm is the largest absolute
value of a coefficient, `ℓ^∞(f) = max_I |a_I|`.

## Main definitions

* `Faltings.MvPolynomial.supNorm f`: the `ℓ^∞`-norm `max_I ‖a_I‖` of `f : MvPolynomial σ R`.

## Main results

* `Faltings.MvPolynomial.norm_coeff_le_supNorm`, `Faltings.MvPolynomial.supNorm_le_iff`:
  `supNorm f` is the least upper bound of the norms of the coefficients of `f`.
* `Faltings.MvPolynomial.exists_norm_coeff_eq_supNorm`: the bound is attained at a coefficient.

## Implementation notes

The coefficients lie in an arbitrary seminormed commutative ring `R` and the variables are
indexed by an arbitrary type `σ`; the source's case is `R = ℂ`, `σ = Fin n`. The maximum is
taken over the support of `f` in `ℝ≥0` and then coerced to `ℝ`, so the zero polynomial has norm
`0`, and the value is the maximum over all monomials since the remaining coefficients vanish.
This is the several-variable analogue of `Polynomial.supNorm`.

## References

* [Z. Gao, *Heights*][gao2022], Def. 1.3.7.
* [E. Bombieri, W. Gubler, *Heights in Diophantine geometry*][bombieriGubler2006], 1.6.1.
-/

namespace Faltings

namespace MvPolynomial

/-- The `ℓ^∞`-norm `ℓ^∞(f) = max_I ‖a_I‖` of a polynomial `f = ∑_I a_I t^I`: the largest norm
of a coefficient of `f`, and `0` for the zero polynomial. -/
@[expose, faltings "def_ht_sup_norm"]
public def supNorm {σ R : Type*} [SeminormedCommRing R] (f : _root_.MvPolynomial σ R) :
    ℝ :=
  ((f.support.sup fun I => ‖f.coeff I‖₊ : NNReal) : ℝ)

section

variable {σ R : Type*} [SeminormedCommRing R]

/-- The zero polynomial has `ℓ^∞`-norm `0`. -/
@[simp]
public theorem supNorm_zero : supNorm (0 : _root_.MvPolynomial σ R) = 0 := by
  simp [supNorm]

/-- The `ℓ^∞`-norm is nonnegative. -/
public theorem supNorm_nonneg (f : _root_.MvPolynomial σ R) : 0 ≤ supNorm f :=
  NNReal.coe_nonneg _

/-- Every coefficient of `f` has norm at most `supNorm f`. -/
public theorem norm_coeff_le_supNorm (f : _root_.MvPolynomial σ R) (I : σ →₀ ℕ) :
    ‖f.coeff I‖ ≤ supNorm f := by
  by_cases hI : I ∈ f.support
  · exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun I => ‖f.coeff I‖₊) hI)
  · rw [_root_.MvPolynomial.notMem_support_iff.1 hI, norm_zero]
    exact supNorm_nonneg f

/-- `supNorm f` is the least upper bound of the norms of the coefficients of `f`. -/
public theorem supNorm_le_iff {f : _root_.MvPolynomial σ R} {C : ℝ} (hC : 0 ≤ C) :
    supNorm f ≤ C ↔ ∀ I, ‖f.coeff I‖ ≤ C := by
  refine ⟨fun h I => (norm_coeff_le_supNorm f I).trans h, fun h => ?_⟩
  lift C to NNReal using hC
  exact NNReal.coe_le_coe.2 (Finset.sup_le fun I _ => NNReal.coe_le_coe.1 (h I))

/-- The maximum defining `supNorm f` is attained: some coefficient of `f` has norm
`supNorm f` (the constant coefficient when `f = 0`). -/
public theorem exists_norm_coeff_eq_supNorm (f : _root_.MvPolynomial σ R) :
    ∃ I, ‖f.coeff I‖ = supNorm f := by
  rcases f.support.eq_empty_or_nonempty with h | h
  · exact ⟨0, by simp [_root_.MvPolynomial.support_eq_empty.1 h]⟩
  obtain ⟨I, -, hI⟩ := Finset.exists_mem_eq_sup _ h fun I => ‖f.coeff I‖₊
  exact ⟨I, by rw [supNorm, hI, coe_nnnorm]⟩

end

end MvPolynomial

end Faltings

/-!
# The `ℓ²`-norm of a complex polynomial

For a polynomial `f = ∑_I a_I t^I ∈ ℂ[t_1, …, t_n]` the `ℓ²`-norm is
`ℓ²(f) = (∑_I |a_I|²)^{1/2}`, the Euclidean norm of the (finitely supported) coefficient vector.

## Main definitions

* `Faltings.l2Norm f`: the `ℓ²`-norm `(∑_I |a_I|²)^{1/2}` of `f : MvPolynomial σ ℂ`.

## Main results

* `Faltings.l2Norm_nonneg`, `Faltings.sq_l2Norm`, `Faltings.l2Norm_zero`: basic API.

## Implementation notes

The variables are indexed by an arbitrary type `σ` rather than `Fin n`; the definition needs no
finiteness of `σ`, since the sum runs over the finite support of `f`. The square root is
`Real.sqrt`, which agrees with `x ^ (1 / 2)` on the nonnegative sum.

## References

* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006], Sec. 1.6.
-/

namespace Faltings

/-- The `ℓ²`-norm `ℓ²(f) = (∑_I |a_I|²)^{1/2}` of a polynomial `f = ∑_I a_I t^I` with complex
coefficients: the square root of the sum of the squared absolute values of its coefficients. -/
@[expose, faltings "def_ht_l2_norm"]
public noncomputable def l2Norm {σ : Type*} (f : MvPolynomial σ ℂ) : ℝ :=
  Real.sqrt (∑ I ∈ f.support, ‖f.coeff I‖ ^ 2)

variable {σ : Type*}

/-- The `ℓ²`-norm is nonnegative. -/
public theorem l2Norm_nonneg (f : MvPolynomial σ ℂ) : 0 ≤ l2Norm f :=
  Real.sqrt_nonneg _

/-- The square of the `ℓ²`-norm is the sum of the squared absolute values of the coefficients. -/
public theorem sq_l2Norm (f : MvPolynomial σ ℂ) : l2Norm f ^ 2 = ∑ I ∈ f.support, ‖f.coeff I‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The zero polynomial has `ℓ²`-norm `0`. -/
@[simp]
public theorem l2Norm_zero : l2Norm (0 : MvPolynomial σ ℂ) = 0 := by
  simp [l2Norm]

end Faltings
