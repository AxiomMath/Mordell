module

public import Mordell.Height.Weil.Basic
public import Mordell.Height.Weil.SubVector
public import Mordell.Height.Weil.Nonneg

/-!
# The height of a family of polynomials

Let `P = (P_i)_{i ∈ ι}` be a finite family of polynomials `P_i = ∑_I a_{i,I} x^I` over an
algebraic extension `K` of `ℚ`, not all zero. Its height `h(P)` is the Weil height of the point
of projective space whose homogeneous coordinates are the coefficients `a_{i,I}`, indexed by
the pairs `(i, I)` with `I` in the support of `P_i`. For a single nonzero polynomial this is the
height `h(P)` of `P`. The height `h(P(ξ))` of a value is not this height: it is the affine height
`Faltings.affineWeilHeight ![P.eval ξ]` of the number `P(ξ)`.

## Main definitions

* `Faltings.polynomialFamilyHeight P hP`: the height `h(P_1, …, P_r)` of a family of polynomials,
  not all zero.
* `Faltings.mvPolynomialHeight P hP`: the height `h(P)` of a nonzero polynomial.

## Main results

* `Faltings.mvPolynomialHeight_nonneg`: the height of a non-zero polynomial is non-negative.
* `Faltings.mvPolynomialHeight_congr`: the height is transported along an equality of
  polynomials.

## Implementation notes

The source takes `K = ℚ̄`, polynomials in `x_1, …, x_m` and the index set `{1, …, r}`; here the
variables are an arbitrary type `σ`, the family is indexed by an arbitrary finite type `ι`, and
`K / ℚ` is any algebraic extension. The coordinates are indexed by the finite type
`Σ i, (P i).support`. `Faltings.weilHeight` asks for a linear order on the index type, used to
normalize by the first nonzero coordinate; the order chosen here is the well-ordering
`WellOrderingRel`, through `IsWellOrder.linearOrder`. The Weil height of a projective point does
not depend on the order of its coordinates, so the choice does not affect the value.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

variable {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
  {σ ι : Type*} [Fintype ι]

/-- The height `h(P_1, …, P_r)` of a finite family `P` of polynomials over `K`, not all zero:
the Weil height `Faltings.weilHeight` of the projective point whose homogeneous coordinates are
the coefficients `(P i).coeff I`, indexed by the pairs `(i, I)` with `I ∈ (P i).support`. -/
@[faltings "def_ht_height_of_polynomial"]
public noncomputable def polynomialFamilyHeight (P : ι → MvPolynomial σ K) (hP : ∃ i, P i ≠ 0) :
    ℝ :=
  letI : LinearOrder (Σ i, (P i).support) := IsWellOrder.linearOrder WellOrderingRel
  weilHeight (Projectivization.mk K (fun p : Σ i, (P i).support => (P p.1).coeff p.2.1)
    (by
      obtain ⟨i, hi⟩ := hP
      obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.mp hi
      exact Function.ne_iff.mpr
        ⟨⟨i, I, MvPolynomial.mem_support_iff.mpr hI⟩, hI⟩))

/-- The height `h(P)` of a nonzero polynomial `P` over `K`: the height
`Faltings.polynomialFamilyHeight` of the one-element family `(P)`, that is, the Weil height of
the projective point whose homogeneous coordinates are the nonzero coefficients of `P`. -/
@[faltings "def_ht_height_of_polynomial"]
public noncomputable def mvPolynomialHeight (P : MvPolynomial σ K) (hP : P ≠ 0) : ℝ :=
  polynomialFamilyHeight (fun _ : Unit => P) ⟨(), hP⟩

/-- The height of a polynomial does not depend on the proof that it is non-zero, and is
transported along an equality of polynomials. -/
public theorem mvPolynomialHeight_congr {P Q : MvPolynomial σ K} (h : P = Q) (hP : P ≠ 0)
    (hQ : Q ≠ 0) : mvPolynomialHeight P hP = mvPolynomialHeight Q hQ := by
  subst h; rfl

/-- The height of a non-zero polynomial is non-negative. -/
public theorem mvPolynomialHeight_nonneg (P : MvPolynomial σ K) (hP : P ≠ 0) :
    0 ≤ mvPolynomialHeight P hP := by
  unfold mvPolynomialHeight polynomialFamilyHeight
  let : LinearOrder (Σ _ : Unit, P.support) := IsWellOrder.linearOrder WellOrderingRel
  exact weilHeight_nonneg _

end Faltings


/-!
# The height of a subfamily of polynomials

For a finite family `P = (P_i)_{i ∈ ι}` of polynomials over an algebraic extension `K` of `ℚ`
and any map `f : ι' → ι` from a finite type, the height of the reindexed family `P ∘ f` is at
most the height of `P`, as soon as `P ∘ f` is not identically zero. At each place the maximum of
the absolute values of the coefficients of `P ∘ f` is at most that of the coefficients of `P`
(repeated coordinates do not change it), so the inequality holds place by place. Taking `ι'` a
one-point type gives `h(P_i) ≤ h(P)` for every `i` with `P_i ≠ 0`.

## Main results

* `Faltings.polynomialFamilyHeight_comp_le`: `h(P ∘ f) ≤ h(P)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

namespace Faltings

variable {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
  {σ ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The height of a subfamily `P ∘ f` of a finite family `P` of polynomials, not all zero, is at
most the height of `P`. With `f` constant at `i`, this is `h(P_i) ≤ h(P)`, the left side being
`Faltings.mvPolynomialHeight (P i) hi`.

The coefficient vector of `P ∘ f` is the sub-vector of that of `P` indexed by
`(j, I) ↦ (f j, I)`, so this is `Faltings.weilHeight_mk_comp_le`. -/
@[faltings "lem_ht_height_subvector_polynomials"]
public theorem polynomialFamilyHeight_comp_le (P : ι → MvPolynomial σ K) (f : ι' → ι)
    (hP : ∃ j, P (f j) ≠ 0) :
    polynomialFamilyHeight (P ∘ f) hP ≤
      polynomialFamilyHeight P (let ⟨j, hj⟩ := hP; ⟨f j, hj⟩) := by
  letI : LinearOrder (Σ i, (P i).support) := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder (Σ j, ((P ∘ f) j).support) := IsWellOrder.linearOrder WellOrderingRel
  exact weilHeight_mk_comp_le (fun p : Σ i, (P i).support => (P p.1).coeff p.2.1)
    (fun q : Σ j, ((P ∘ f) j).support => (⟨f q.1, q.2⟩ : Σ i, (P i).support)) _

end Faltings
