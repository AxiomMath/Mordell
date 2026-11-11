module
public import Mordell.Jacobian.AbelJacobi

/-!
# The theta divisor of a curve

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, of genus `g ≥ 1`,
let `(J, ι)` be a Jacobian of `C` and let `j = j_P : C ⟶ J` be the Abel–Jacobi map. The
*theta divisor* `Θ = Θ_P = W^{g-1} ⊆ J` is the image of the `(g-1)`-fold fibre power
`C^{g-1} = C ×_k ⋯ ×_k C` under the `k`-morphism
`(Q₁, …, Q_{g-1}) ↦ j(Q₁) + ⋯ + j(Q_{g-1})`, the sum being taken in the group law of `J`.
On points with values in a field it is
`Θ = {x ∈ J | x = x₁ + ⋯ + x_{g-1}, xᵢ ∈ j(C)}`, the sum of `g - 1` copies of `j(C)`.

## Main definitions

* `Faltings.thetaDivisor X A hg j hj`: the theta divisor `Θ_P ⊆ J` of the curve with
  degree-one divisor `X = (C, P)` of genus `g ≥ 1`, for the Jacobian `A = (J, ι)` and the
  Abel–Jacobi map `j = j_P`.

## Implementation notes

The theta divisor is defined as the subset `Θ` of the underlying space of `J`, the set-theoretic
image of the summation morphism `C^{g-1} ⟶ J`. A reduced closed subscheme of `J` is
determined by its underlying closed set, so `Θ` with its reduced structure is this set; that
it is closed (the summation morphism is proper, `C^{g-1}` being proper over `k`) and that it
is a prime divisor are separate results.

The fibre power `C^{g-1}` is the categorical product of `g - 1` copies of `C` in the category
of `k`-schemes, and the summation morphism is the product, in the group `Hom_k(C^{g-1}, J)`,
of the composites `prᵢ ≫ j`, taken in the order `1, …, g - 1`. Since `g - 1` is the
natural-number difference, the hypothesis `g ≥ 1` is what makes it the source's `g - 1`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Sections 5–6.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- **The theta divisor** `Θ = Θ_P = W^{g-1} ⊆ J` of a curve `X = (C, P)` with a divisor of
degree one, of genus `g ≥ 1`, for a Jacobian `A = (J, ι)` and the Abel–Jacobi map `j = j_P`:
the image of `C^{g-1}` under the `k`-morphism
`(Q₁, …, Q_{g-1}) ↦ j(Q₁) + ⋯ + j(Q_{g-1})`, as a subset of the underlying space of `J`
(which determines its reduced structure). -/
@[expose, faltings "def_nt_theta_divisor"]
public def thetaDivisor (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (_hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (_hj : IsAbelJacobiMap X A j) :
    Set A.J.left :=
  Set.range (List.ofFn fun i : Fin (genus X.f - 1) =>
    Pi.π (fun _ : Fin (genus X.f - 1) => Over.mk X.f) i ≫ j).prod.left

end Faltings
