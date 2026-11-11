module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.Basic
public import Mordell.Height.Weil.Representative

/-!
# The Weil height under the Veronese map

Let `K` be an algebraic extension of `ℚ`, `ι` a finite linearly ordered type of homogeneous
coordinates and `e ≥ 1`. The Veronese map `Φ_e` sends `x = [x_i]_{i ∈ ι}` to the point
`[x^I]_{|I| = e}` of all monomials of degree `e` in the coordinates of `x`. Its height is `e`
times that of `x`: `h(Φ_e(x)) = e · h(x)`. At each place `v`, the largest of the `|x^I|_v` is
`max_j |x_j|_v ^ e`, attained at the monomial `x_j ^ e`; summing over the places gives the claim.

## Main results

* `Faltings.weilHeight_veroneseMap`: `weilHeight (veroneseMap K e he x) = e * weilHeight x`.

## Implementation notes

The target of `Faltings.veroneseMap` is indexed by the exponent vectors
`{I : ι →₀ ℕ // I.degree = e}`. The height `Faltings.weilHeight` needs this type to be finite
and linearly ordered, and Mathlib provides neither instance. Both are taken as instance arguments.
The height does not depend on the choice of order, so the statement holds for every linear order
on the exponent vectors.

## References

* [Z. Gao, *Heights*][gao2022], Prop. 1.2.14.
* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- For an absolute value `v` and a vector `y` indexed by a finite type, the largest value of
`v` on the monomials of degree `e` in `y` is `(max_j v (y j)) ^ e`, attained at `y j ^ e` for
a `j` where `v (y j)` is largest. -/
private lemma iSup_absoluteValue_monomial {F : Type*} [Field F] {ι : Type*} [Finite ι]
    [Nonempty ι] (v : AbsoluteValue F ℝ) (y : ι → F) (e : ℕ) :
    ⨆ I : {I : ι →₀ ℕ // I.degree = e}, v (I.1.prod fun i k => y i ^ k) =
      (⨆ j, v (y j)) ^ e := by
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => v (y j)
  rw [le_antisymm (ciSup_le hj₀) (le_ciSup (Finite.bddAbove_range fun j => v (y j)) j₀)]
  have hle (I : ι →₀ ℕ) : v (I.prod fun i k => y i ^ k) ≤ v (y j₀) ^ I.degree := by
    rw [Finsupp.prod, map_prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ =>
      (map_pow v _ _).trans_le (pow_le_pow_left₀ (by positivity) (hj₀ i) _)
  have : Nonempty {I : ι →₀ ℕ // I.degree = e} := ⟨⟨Finsupp.single j₀ e, by simp⟩⟩
  have hle' (I : {I : ι →₀ ℕ // I.degree = e}) := I.2 ▸ hle I.1
  exact le_antisymm (ciSup_le hle') (le_ciSup_of_le ⟨_, Set.forall_mem_range.2 hle'⟩
    ⟨Finsupp.single j₀ e, by simp⟩ (by simp [Finsupp.prod_single_index]))

/-- Over a number field, the sum of local heights of the vector of degree-`e` monomials in `y`
is `e` times that of `y`. -/
private lemma sumLocalHeight_monomial {F : Type*} [Field F] [NumberField F] {ι : Type*}
    [Finite ι] [Nonempty ι] (y : ι → F) (e : ℕ) :
    sumLocalHeight (fun I : {I : ι →₀ ℕ // I.degree = e} => I.1.prod fun i k => y i ^ k) =
      e * sumLocalHeight y := by
  rw [sumLocalHeight, sumLocalHeight, mul_finsum]
  refine finsum_congr fun w => ?_
  obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv w
  simp only [NumberFieldPlace.localHeight, NumberFieldPlace.vectorAbv, ← hv]
  rw [iSup_absoluteValue_monomial, Real.log_pow]

/-- The height of the image of a point under the Veronese map of degree `e` is `e` times its
height: `h(Φ_e(x)) = e · h(x)`, for `Faltings.veroneseMap` and the absolute logarithmic Weil
height `Faltings.weilHeight`, for every linear order on the exponent vectors `I` with
`|I| = e`. -/
@[faltings "lem_ht_veronese_height"]
public theorem weilHeight_veroneseMap {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι] [LinearOrder ι] (e : ℕ) (he : 1 ≤ e)
    [Fintype {I : ι →₀ ℕ // I.degree = e}] [LinearOrder {I : ι →₀ ℕ // I.degree = e}]
    (x : ℙ K (ι → K)) :
    weilHeight (veroneseMap K e he x) = e * weilHeight x := by
  classical
  obtain ⟨r, hr, rfl⟩ : ∃ r hr, x = Projectivization.mk K r hr :=
    ⟨x.rep, x.rep_nonzero, x.mk_rep.symm⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have : Nonempty ι := ⟨j⟩
  let F : IntermediateField ℚ K := IntermediateField.adjoin ℚ (Set.range r)
  have : Finite (Set.range r) := (Set.finite_range r).to_subtype
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin fun r _ =>
    (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  have : NumberField F := { to_finiteDimensional := by convert this; exact Subsingleton.elim _ _ }
  let y : ι → F := fun i => ⟨r i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  have hz : algebraMap F K ∘ (fun I : {I : ι →₀ ℕ // I.degree = e} =>
      I.1.prod fun i k => y i ^ k) = fun I => I.1.prod fun i k => r i ^ k := by
    funext I
    simp [map_finsuppProd, y]
  have hz0 : (fun I : {I : ι →₀ ℕ // I.degree = e} => I.1.prod fun i k => r i ^ k) ≠ 0 :=
    fun h => hj <| by
      simpa [Finsupp.prod_single_index, Nat.one_le_iff_ne_zero.1 he] using
        congr_fun h ⟨Finsupp.single j e, by simp⟩
  rw [veroneseMap_mk K e he r hr hz0, weilHeight_eq_sumLocalHeight (hz ▸ hz0) (by congr 1),
    sumLocalHeight_monomial,
    weilHeight_eq_sumLocalHeight (x := Projectivization.mk K r hr) (y := y) hr rfl]

end Faltings
