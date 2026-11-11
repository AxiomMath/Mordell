module
public import Mathlib
public import Mordell.Attr

/-!
# Reduced representations of the norms `Norm η_i`

In Bombieri's proof of the Mordell conjecture (Section 9), `R = k[ξ_a, ξ'_b]` is a factorial
ring with fraction field `K = k(ξ_a, ξ'_b)`. The function field `L = k(C × C)` is a finite
extension of `K`, and `η_0 = 1, η_1, …, η_m ∈ L` are the affine functions `y_i / y_0`.
Each norm `Norm_{L/K} η_i` is a fraction `U_i / V_i` with `U_i, V_i ∈ R` coprime and
`V_i ≠ 0`. This file records the predicate saying that a family `(U_i, V_i)_{0 ≤ i ≤ m}` is such a
family of reduced representations, normalised by `U_0 = V_0 = 1`.

## Main definitions

* `Faltings.IsReducedNormRepresentation`: `(U_i, V_i)_{i : Fin (m + 1)}` is a family of reduced
  representations of the norms `Algebra.norm K (η i)`.

## Implementation notes

The definition is stated for an arbitrary tower `R → K → L`: a commutative ring `R`, a field `K`
that is an `R`-algebra, and a field `L` that is a `K`-algebra. The norm is `Algebra.norm K`, and
"coprime" is Mathlib's `IsRelPrime`. Factoriality of `R`, `K` being its fraction field and `L / K`
being finite are what make such a family exist, but the definition itself does not need them.
In Bombieri's setting, `R = k[ξ_a, ξ'_b]`, `K = k(ξ_a, ξ'_b)` and `L = k(C × C)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

namespace Faltings

/-- A family `(U i, V i)_{i : Fin (m + 1)}` of pairs of elements of `R` is a family of *reduced
representations* of the norms `Algebra.norm K (η i)` when each `V i` is nonzero, `U i` and `V i`
are coprime, and `Algebra.norm K (η i) = U i / V i` in `K`, with the normalisation `U 0 = V 0 = 1`.
-/
@[faltings "def_bvr_reduced_norm_eta"]
public structure IsReducedNormRepresentation (R : Type*) {K L : Type*} [CommRing R] [Field K]
    [Field L] [Algebra R K] [Algebra K L] {m : ℕ} (η : Fin (m + 1) → L) (U V : Fin (m + 1) → R) :
    Prop where
  /-- Each denominator is nonzero. -/
  ne_zero : ∀ i, V i ≠ 0
  /-- Numerator and denominator are coprime. -/
  isRelPrime : ∀ i, IsRelPrime (U i) (V i)
  /-- The fraction `U i / V i` is the norm of `η i`. -/
  algebraNorm_eq_div : ∀ i, Algebra.norm K (η i) = algebraMap R K (U i) / algebraMap R K (V i)
  /-- The normalisation `U 0 = 1`. -/
  num_zero : U 0 = 1
  /-- The normalisation `V 0 = 1`. -/
  den_zero : V 0 = 1

end Faltings
