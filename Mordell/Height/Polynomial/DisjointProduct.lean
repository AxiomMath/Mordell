module

public import Mordell.Height.Polynomial.Basic
public import Mordell.Height.Weil.Segre
public import Mordell.Height.Weil.ZeroCoordinates

/-!
# The height of a product of polynomials in disjoint variables

Let `P_1, …, P_k` be nonzero polynomials over an algebraic extension `K` of `ℚ` involving
pairwise disjoint sets of variables. Then the height is additive on their product:
`h(P_1 ⋯ P_k) = ∑_j h(P_j)`. Indeed, the monomials of the product are the products of
monomials of the factors, distinct for distinct tuples, so the coefficient point of the product
is the Segre product of the coefficient points of the factors, and the Weil height is additive
on Segre products.

## Main results

* `Faltings.mvPolynomialHeight_prod_of_pairwise_disjoint_vars`: for nonzero `P_j` with pairwise
  disjoint sets of variables `MvPolynomial.vars`, `h(∏_j P_j) = ∑_j h(P_j)`.

## Implementation notes

The source takes `K = ℚ̄`, the variables `x_1, …, x_m` and the factors indexed by
`{1, …, k}`; here `K / ℚ` is any algebraic extension, the variables are indexed by an arbitrary
type `σ` and the factors by an arbitrary finite type `ι`. "Involving pairwise disjoint sets of
variables" is `Pairwise (Disjoint on fun j => (P j).vars)`, and `h` is
`Faltings.mvPolynomialHeight`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 9.
-/

@[expose] public section

open Function MvPolynomial

namespace Faltings

section

variable {K : Type*} [Field K] {σ : Type*}

/-- An exponent in the support of `P` vanishes off the variables of `P`. -/
private lemma apply_eq_zero_of_notMem_vars {P : MvPolynomial σ K} {I : σ →₀ ℕ}
    (hI : I ∈ P.support) {x : σ} (hx : x ∉ P.vars) : I x = 0 :=
  Finsupp.notMem_support_iff.1 fun hm =>
    hx (by rw [mem_vars_iff_mem_support]; exact ⟨I, hI, hm⟩)

/-- Exponents of polynomials in disjoint variables add injectively. -/
private lemma add_injective_of_disjoint_vars {P Q : MvPolynomial σ K}
    (h : Disjoint P.vars Q.vars) {I I' J J' : σ →₀ ℕ} (hI : I ∈ P.support)
    (hI' : I' ∈ P.support) (hJ : J ∈ Q.support) (hJ' : J' ∈ Q.support)
    (he : I + J = I' + J') : I = I' ∧ J = J' := by
  obtain rfl : I = I' := Finsupp.ext fun x => by
    have hx := DFunLike.congr_fun he x
    simp only [Finsupp.add_apply] at hx
    by_cases hxP : x ∈ P.vars
    · have hxQ := Finset.disjoint_left.1 h hxP
      rwa [apply_eq_zero_of_notMem_vars hJ hxQ, apply_eq_zero_of_notMem_vars hJ' hxQ] at hx
    · rw [apply_eq_zero_of_notMem_vars hI hxP, apply_eq_zero_of_notMem_vars hI' hxP]
  exact ⟨rfl, add_left_cancel he⟩

/-- The coefficient of `P * Q` at `I + J`, for `P`, `Q` in disjoint variables and `I`, `J` in
their supports, is the product of coefficients. -/
private lemma coeff_mul_add_of_disjoint_vars {P Q : MvPolynomial σ K}
    (h : Disjoint P.vars Q.vars) {I J : σ →₀ ℕ} (hI : I ∈ P.support) (hJ : J ∈ Q.support) :
    (P * Q).coeff (I + J) = P.coeff I * Q.coeff J := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (I, J)]
  · rintro ⟨I', J'⟩ hm hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hm
    by_contra hc
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hc
    obtain ⟨rfl, rfl⟩ := add_injective_of_disjoint_vars h hI (mem_support_iff.2 h1) hJ
      (mem_support_iff.2 h2) hm.symm
    exact hne rfl
  · simp

/-- Every exponent of `P * Q` is a sum of exponents of `P` and of `Q`. -/
private lemma exists_add_of_mem_support_mul {P Q : MvPolynomial σ K} {L : σ →₀ ℕ}
    (hL : L ∈ (P * Q).support) :
    ∃ I ∈ P.support, ∃ J ∈ Q.support, I + J = L := by
  classical
  rw [mem_support_iff, coeff_mul] at hL
  obtain ⟨⟨I, J⟩, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hL
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  exact ⟨I, mem_support_iff.2 h1, J, mem_support_iff.2 h2,
    Finset.HasAntidiagonal.mem_antidiagonal.1 hm⟩

/-- The coefficient vector of a nonzero polynomial is nonzero. -/
private lemma coeff_ne_zero_of_ne_zero {P : MvPolynomial σ K} (hP : P ≠ 0) :
    (fun p : Σ _ : Unit, P.support => P.coeff p.2.1) ≠ 0 := by
  obtain ⟨I, hI⟩ := ne_zero_iff.mp hP
  exact Function.ne_iff.mpr ⟨⟨(), I, mem_support_iff.mpr hI⟩, hI⟩

variable [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

/-- The two-factor case: the coefficient point of `P * Q` is the Segre product of those of `P`
and `Q`, reindexed along the injection `(I, J) ↦ I + J` of the supports. -/
private lemma mvPolynomialHeight_mul_of_disjoint_vars {P Q : MvPolynomial σ K} (hP : P ≠ 0)
    (hQ : Q ≠ 0) (h : Disjoint P.vars Q.vars) :
    mvPolynomialHeight (P * Q) (mul_ne_zero hP hQ) =
      mvPolynomialHeight P hP + mvPolynomialHeight Q hQ := by
  classical
  let A := Σ _ : Unit, P.support
  let B := Σ _ : Unit, Q.support
  let C := Σ _ : Unit, (P * Q).support
  let : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder B := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder C := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (A × B) := IsWellOrder.linearOrder WellOrderingRel
  let e : A × B → C :=
    fun p => ⟨(), p.1.2.1 + p.2.2.1, mem_support_iff.mpr (by
      rw [coeff_mul_add_of_disjoint_vars h p.1.2.2 p.2.2.2]
      exact mul_ne_zero (mem_support_iff.mp p.1.2.2) (mem_support_iff.mp p.2.2.2))⟩
  have he : Injective e := by
    rintro ⟨⟨_, I, hI⟩, ⟨_, J, hJ⟩⟩ ⟨⟨_, I', hI'⟩, ⟨_, J', hJ'⟩⟩ hee
    obtain ⟨rfl, rfl⟩ := add_injective_of_disjoint_vars h hI hI' hJ hJ'
      (congrArg (fun c => c.2.1) hee)
    rfl
  have hext : extend e (fun p => P.coeff p.1.2.1 * Q.coeff p.2.2.1) 0 =
      fun c => (P * Q).coeff c.2.1 := by
    funext ⟨⟨⟩, L, hL⟩
    obtain ⟨I, hI, J, hJ, rfl⟩ := exists_add_of_mem_support_mul hL
    exact (he.extend_apply _ _ (⟨(), I, hI⟩, ⟨(), J, hJ⟩)).trans
      (coeff_mul_add_of_disjoint_vars h hI hJ).symm
  simp only [mvPolynomialHeight, polynomialFamilyHeight]
  rw [← weilHeight_segreMap, segreMap_mk (coeff_ne_zero_of_ne_zero hP)
    (coeff_ne_zero_of_ne_zero hQ), ← weilHeight_mk_extend_zero he]
  congr 2
  exact hext.symm

/-- The constant polynomial `1` has height `0`, by the two-factor case applied to `1 * 1`. -/
private lemma mvPolynomialHeight_one :
    mvPolynomialHeight (1 : MvPolynomial σ K) one_ne_zero = 0 := by
  have h := mvPolynomialHeight_mul_of_disjoint_vars (one_ne_zero (α := MvPolynomial σ K))
    one_ne_zero (by simp [vars_one])
  simp only [mul_one] at h
  linarith

/-- The case of a product over a finite set of indices. -/
private lemma mvPolynomialHeight_finset_prod {ι : Type*} (P : ι → MvPolynomial σ K)
    (hP : ∀ j, P j ≠ 0) (hdisj : Pairwise (Disjoint on fun j => (P j).vars)) (s : Finset ι)
    (hs : ∏ j ∈ s, P j ≠ 0) :
    mvPolynomialHeight (∏ j ∈ s, P j) hs = ∑ j ∈ s, mvPolynomialHeight (P j) (hP j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mvPolynomialHeight_one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [mvPolynomialHeight_mul_of_disjoint_vars (hP a)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hP j) (Finset.disjoint_of_subset_right (vars_prod _)
        ((Finset.disjoint_biUnion_right _ _ _).2 fun j hj => hdisj fun h => ha (h ▸ hj))), ih]

end

/-- **Height of a product in disjoint variables.** For a finite family `P` of nonzero
polynomials over an algebraic extension `K` of `ℚ` whose sets of variables
`MvPolynomial.vars` are pairwise disjoint, `h(∏_j P_j) = ∑_j h(P_j)`, where `h` is
`Faltings.mvPolynomialHeight`. -/
@[faltings "lem_ht_height_product_disjoint_variables"]
public theorem mvPolynomialHeight_prod_of_pairwise_disjoint_vars {K : Type*} [Field K]
    [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] {σ ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ K) (hP : ∀ j, P j ≠ 0)
    (hdisj : Pairwise (Disjoint on fun j => (P j).vars)) :
    mvPolynomialHeight (∏ j, P j) (Finset.prod_ne_zero_iff.mpr fun j _ => hP j) =
      ∑ j, mvPolynomialHeight (P j) (hP j) :=
  mvPolynomialHeight_finset_prod P hP hdisj Finset.univ _

end Faltings
