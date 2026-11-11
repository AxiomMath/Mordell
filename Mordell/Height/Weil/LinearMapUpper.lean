module

public import Mordell.Height.Polynomial.Eval
public import Mordell.Height.Weil.ZeroCoordinates

/-!
# Upper bound for the height under a linear map

Let `A = (a_{ji})` be a nonzero matrix over an algebraic extension `K / ℚ`, with rows indexed by
`ι'` and columns by `ι`, and let `φ = (L_j)_j`, `L_j(x) = ∑_i a_{ji} x_i`, be the induced rational
map `ℙ(K^ι) ⇢ ℙ(K^{ι'})`, defined away from the common zero locus of the `L_j`. For every point
`x` outside that locus,
`h(φ(x)) ≤ h(x) + h(A) + log #ι`,
where `h(A)` is the height of `A` viewed as a point of `ℙ(K^{ι' × ι})`.

## Main results

* `Faltings.weilHeight_linearMap_apply_le`: the bound above, for `Faltings.weilHeight`.

## Implementation notes

The point `x` is given by a nonzero representative `v : ι → K`, and "`x` lies outside the
common zero locus" is the hypothesis that `(∑_i a_{ji} v_i)_j ≠ 0`, which does not depend on the
representative. The height `Faltings.weilHeight` uses a linear order on the index type only to
choose a first nonzero coordinate, and its value does not depend on it; the product `ι' × ι`
has no canonical linear order, so an arbitrary one is taken.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

section LinForm

open MvPolynomial

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι]

/-- The linear forms `L_j = ∑_i A (j, i) x_i` attached to a matrix `A`. -/
private noncomputable def linForm (A : ι' × ι → K) (j : ι') : MvPolynomial ι K :=
  ∑ i, C (A (j, i)) * X i

private theorem isHomogeneous_linForm (A : ι' × ι → K) (j : ι') :
    (linForm A j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X K i).C_mul _

private theorem eval_linForm (A : ι' × ι → K) (j : ι') (w : ι → K) :
    (linForm A j).eval w = ∑ i, A (j, i) * w i := by
  simp [linForm]

private theorem coeff_linForm (A : ι' × ι → K) (j : ι') (I : ι →₀ ℕ) :
    (linForm A j).coeff I = ∑ i, if Finsupp.single i 1 = I then A (j, i) else 0 := by
  classical
  simp only [linForm, coeff_sum, coeff_C_mul, coeff_X', mul_ite, mul_one, mul_zero]
  exact Finset.sum_congr rfl fun i _ => by congr

private theorem coeff_linForm_single (A : ι' × ι → K) (j : ι') (i : ι) :
    (linForm A j).coeff (Finsupp.single i 1) = A (j, i) := by
  classical
  simp [coeff_linForm, Finsupp.single_left_inj one_ne_zero]

/-- Every monomial of a linear form is a single variable. -/
private theorem exists_single_eq_of_mem_support_linForm (A : ι' × ι → K) (j : ι')
    {I : ι →₀ ℕ} (hI : I ∈ (linForm A j).support) : ∃ i, Finsupp.single i 1 = I := by
  classical
  rw [mem_support_iff, coeff_linForm] at hI
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨i, by_contra fun h => hi (if_neg h)⟩

private theorem card_support_linForm_le (A : ι' × ι → K) (j : ι') :
    (linForm A j).support.card ≤ Fintype.card ι := by
  classical
  calc (linForm A j).support.card
      ≤ (Finset.univ.image fun i : ι => Finsupp.single i 1).card := Finset.card_le_card
        fun I hI => by
          obtain ⟨i, rfl⟩ := exists_single_eq_of_mem_support_linForm A j hI
          simp
    _ ≤ Fintype.card ι := Finset.card_image_le

private theorem exists_linForm_ne_zero {A : ι' × ι → K} (hA : A ≠ 0) :
    ∃ j, linForm A j ≠ 0 := by
  obtain ⟨⟨j, i⟩, h⟩ := Function.ne_iff.mp hA
  exact ⟨j, fun h' => h (by simpa [h'] using (coeff_linForm_single A j i).symm)⟩

/-- The height of the family of linear forms `(L_j)_j` is the height of the matrix `A`: the
coefficients of the `L_j` are the entries of `A`, and the zero entries of `A` (the monomials
missing from the `L_j`) do not change the height. -/
private theorem polynomialFamilyHeight_linForm [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    [Fintype ι'] [LinearOrder (ι' × ι)] (A : ι' × ι → K) (hA : A ≠ 0) :
    polynomialFamilyHeight (linForm A) (exists_linForm_ne_zero hA) =
      weilHeight (Projectivization.mk K A hA) := by
  classical
  let e : (Σ j, (linForm A j).support) → ι' × ι := fun p =>
    (p.1, (exists_single_eq_of_mem_support_linForm A p.1 p.2.2).choose)
  have he_spec (p) : Finsupp.single (e p).2 1 = p.2.1 :=
    (exists_single_eq_of_mem_support_linForm A p.1 p.2.2).choose_spec
  have hc (p : Σ j, (linForm A j).support) : (linForm A p.1).coeff p.2.1 = A (e p) := by
    rw [← he_spec p, coeff_linForm_single]
  have he : Function.Injective e := by
    rintro ⟨j, I, hI⟩ ⟨j', I', hI'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.mp h
    obtain rfl : I = I' := (he_spec _).symm.trans ((congrArg (Finsupp.single · 1) h2).trans
      (he_spec ⟨j, I', hI'⟩))
    rfl
  have hext : Function.extend e (fun p : Σ j, (linForm A j).support =>
      (linForm A p.1).coeff p.2.1) 0 = A := by
    ext ⟨j, i⟩
    by_cases hr : ∃ p, e p = (j, i)
    · obtain ⟨p, hp⟩ := hr
      rw [← hp, he.extend_apply, hc]
    · rw [Function.extend_apply' _ _ _ hr]
      by_contra hji
      have hmem : Finsupp.single i 1 ∈ (linForm A j).support := by
        rw [mem_support_iff, coeff_linForm_single]; exact Ne.symm hji
      exact hr ⟨⟨j, _, hmem⟩,
        Prod.ext rfl (Finsupp.single_left_injective one_ne_zero (he_spec ⟨j, _, hmem⟩))⟩
  letI : LinearOrder (Σ j, (linForm A j).support) := IsWellOrder.linearOrder WellOrderingRel
  rw [polynomialFamilyHeight, ← weilHeight_mk_extend_zero he]
  congr

end LinForm

/-- For a nonzero matrix `A : ι' × ι → K` over an algebraic extension `K / ℚ` and a nonzero
`v : ι → K` with `A v ≠ 0`, the height of `[A v] = φ([v])` is at most
`h([v]) + h([A]) + log #ι`. -/
@[faltings "lem_ht_linear_map_upper"]
public theorem weilHeight_linearMap_apply_le {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι ι' : Type*} [Fintype ι] [LinearOrder ι] [Fintype ι']
    [LinearOrder ι'] [LinearOrder (ι' × ι)] (A : ι' × ι → K) (hA : A ≠ 0) (v : ι → K)
    (hv : v ≠ 0) (hAv : (fun j => ∑ i, A (j, i) * v i) ≠ 0) :
    weilHeight (Projectivization.mk K (fun j => ∑ i, A (j, i) * v i) hAv) ≤
      weilHeight (Projectivization.mk K v hv) + weilHeight (Projectivization.mk K A hA) +
        Real.log (Fintype.card ι) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  have heval : (fun j => (linForm A j).eval (Projectivization.mk K v hv).rep) =
      a • fun j => ∑ i, A (j, i) * v i := by
    ext j
    simp [eval_linForm, ← ha, Finset.mul_sum, Units.smul_def, mul_left_comm]
  have hx : (fun j => (linForm A j).eval (Projectivization.mk K v hv).rep) ≠ 0 := by
    rw [heval]; exact (smul_ne_zero_iff_ne a).mpr hAv
  have h := weilHeight_eval_le (linForm A) (isHomogeneous_linForm A) (exists_linForm_ne_zero hA)
    (card_support_linForm_le A) _ hx
  rw [(Projectivization.mk_eq_mk_iff K _ _ _ _).2 ⟨a, heval.symm⟩,
    polynomialFamilyHeight_linForm A hA] at h
  simpa using h

end Faltings
