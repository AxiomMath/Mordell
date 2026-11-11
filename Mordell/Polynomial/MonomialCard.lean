module
public import Mathlib
public import Mordell.Attr

/-!
# The number of monomials of a polynomial

For a polynomial `f` in any number of variables, `#f` is the number of monomials occurring in `f`
with non-zero coefficient, that is, the cardinality of the support of `f`.

## Main definitions

* `Faltings.MvPolynomial.monomialCount`: the number `#f` of monomials of `f` with non-zero
  coefficient.

## Implementation notes

A polynomial in any number of variables is an `MvPolynomial σ R`, for an arbitrary index type `σ`
and commutative semiring `R`; the monomials with non-zero coefficient are exactly the exponent
vectors in `MvPolynomial.support f`, so `#f = (MvPolynomial.support f).card`. The definition is an
`abbrev`, so Mathlib's API on `MvPolynomial.support` and `Finset.card` applies directly.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sections 7 and 8
-/

namespace Faltings.MvPolynomial

/-- The number `#f` of monomials occurring in the polynomial `f` with non-zero coefficient: the
cardinality of the support of `f`. -/
@[faltings "def_bvs_monomial_count"]
public abbrev monomialCount {σ R : Type*} [CommSemiring R] (f : _root_.MvPolynomial σ R) : ℕ :=
  f.support.card

end Faltings.MvPolynomial
