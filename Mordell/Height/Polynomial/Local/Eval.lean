module

public import Mordell.Height.Polynomial.Local.Size
public import Mordell.Height.Weil.LocalHeight
public import Mordell.NumberField.NormalizedAbv.AbsoluteValue

/-!
# Local bound for values of forms

Let `K` be a number field, `w` a place of `K`, and `F = ∑_{I ∈ S} a_I x^I` a form of degree `e`
with at most `N ≥ 1` monomials. Then for every vector `x`,
`|F(x)|_w ≤ |N|_w ^ ε_w · |F|_w · |x|_w ^ e`, where `|·|_w` is the normalized absolute value
`Faltings.NumberFieldPlace.normalizedAbv`, `|F|_w` is `Faltings.NumberFieldPlace.mvPolynomialAbv`,
`|x|_w` is `Faltings.NumberFieldPlace.vectorAbv` and `ε_w` is
`Faltings.NumberFieldPlace.archimedeanIndicator`.

## Main results

* `Faltings.NumberFieldPlace.normalizedAbv_eval_le_of_isHomogeneous`: the bound above.

## Implementation notes

The variables form an arbitrary finite type `σ` rather than `Fin (n + 1)`. The single polynomial
`F` enters `Faltings.NumberFieldPlace.mvPolynomialAbv` as the one-element family
`fun _ : Unit => F`, and the monomial count `#S` is `F.support.card`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
* [Z. Gao, *Heights*][gao2022], Prop. 1.3.2.
-/

@[expose] public section

namespace Faltings

open NumberField Finset

/-- For a form `F` of degree `e` over a number field `K` with at most `N ≥ 1` monomials, and any
`x : σ → K`, `|F(x)|_w ≤ |N|_w ^ ε_w · |F|_w · |x|_w ^ e` at every place `w`. -/
@[faltings "lem_ht_local_value_bound_homogeneous"]
public theorem NumberFieldPlace.normalizedAbv_eval_le_of_isHomogeneous {K : Type*} [Field K] [NumberField K]
    {σ : Type*} [Fintype σ] (w : NumberFieldPlace K) {N e : ℕ} (hN : 1 ≤ N) {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous e) (hS : F.support.card ≤ N) (x : σ → K) :
    w.normalizedAbv (MvPolynomial.eval x F) ≤
      w.normalizedAbv (N : K) ^ w.archimedeanIndicator * w.mvPolynomialAbv (fun _ : Unit => F) *
        w.vectorAbv x ^ e := by
  have hN0 := pow_nonneg (NumberFieldPlace.normalizedAbv_nonneg w (N : K)) w.archimedeanIndicator
  rcases F.support.eq_empty_or_nonempty with h0 | hs
  · rw [MvPolynomial.support_eq_empty.1 h0, map_zero, NumberFieldPlace.normalizedAbv_zero]
    exact mul_nonneg (mul_nonneg hN0 (w.mvPolynomialAbv_nonneg _)) (pow_nonneg
      (w.vectorAbv_nonneg x) e)
  rw [MvPolynomial.eval_eq', mul_assoc]
  exact (NumberFieldPlace.normalizedAbv_sum_le w hs _).trans <| mul_le_mul
    (w.normalizedAbv_natCast_pow_le hs.card_pos hS)
    (sup'_le _ _ fun I hI => (w.normalizedAbv_coeff_mul_prod_le hF x hI).trans
      (mul_le_mul_of_nonneg_right (w.normalizedAbv_coeff_le_mvPolynomialAbv F I)
        (pow_nonneg (w.vectorAbv_nonneg x) e)))
    (le_sup'_of_le _ hs.choose_spec (NumberFieldPlace.normalizedAbv_nonneg _ _)) hN0

end Faltings
