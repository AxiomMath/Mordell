module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Basic
public import Mordell.Height.Weil.Representative

/-!
# The height of a Segre product

For points `x ∈ ℙ(K^ι)` and `y ∈ ℙ(K^κ)` over an algebraic extension `K / ℚ`, the absolute
logarithmic Weil height is additive along the Segre map: `h(x ⊗ y) = h(x) + h(y)`, where
`x ⊗ y = (x_i y_j)_{(i, j)}`. At every place `w` of a number field `F` containing the
coordinates, `max_{i,j} |x_i y_j|_w = max_i |x_i|_w · max_j |y_j|_w` by multiplicativity of
`|·|_w`; taking logarithms and summing over the places gives the result, the heights being
computed from any representative.

## Main results

* `Faltings.weilHeight_segreMap`: `weilHeight (segreMap x y) = weilHeight x + weilHeight y`.

## Implementation notes

The height `Faltings.weilHeight` is defined using a linear order on the index type (to choose
the first nonzero coordinate), but its value does not depend on that order. The product
`ι × κ` carries no canonical linear order, so the result is stated for an arbitrary linear
order on `ι × κ`; the lexicographic order is one instance.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- `|a ⊗ b|_w = |a|_w |b|_w` for the vector `(a_i b_j)_{(i,j)}`. -/
private lemma vectorAbv_mul {F : Type*} [Field F] [NumberField F] {ι κ : Type*} [Finite ι]
    [Finite κ] (w : NumberFieldPlace F) (a : ι → F) (b : κ → F) :
    w.vectorAbv (fun p : ι × κ => a p.1 * b p.2) = w.vectorAbv a * w.vectorAbv b := by
  obtain ⟨v, hv⟩ := NumberFieldPlace.exists_absoluteValue_coe_eq_normalizedAbv w
  simp only [NumberFieldPlace.vectorAbv, ← hv, map_mul]
  rw [Finite.ciSup_prod, Real.iSup_mul_of_nonneg (Real.iSup_nonneg fun _ => v.nonneg _)]
  congr 1; ext i
  rw [Real.mul_iSup_of_nonneg (v.nonneg _)]

/-- `Σ_w log |a ⊗ b|_w = Σ_w log |a|_w + Σ_w log |b|_w` for nonzero `a` and `b`. -/
private lemma sumLocalHeight_mul {F : Type*} [Field F] [NumberField F] {ι κ : Type*} [Finite ι]
    [Finite κ] {a : ι → F} {b : κ → F} (ha : a ≠ 0) (hb : b ≠ 0) :
    sumLocalHeight (fun p : ι × κ => a p.1 * b p.2) = sumLocalHeight a + sumLocalHeight b := by
  unfold sumLocalHeight
  rw [← finsum_add_distrib (NumberFieldPlace.finite_support_localHeight ha)
    (NumberFieldPlace.finite_support_localHeight hb)]
  congr 1; ext w
  simp only [NumberFieldPlace.localHeight, vectorAbv_mul]
  exact Real.log_mul (w.vectorAbv_pos ha).ne' (w.vectorAbv_pos hb).ne'

/-- The vector `(a_i b_j)_{(i,j)}` is nonzero when `a` and `b` are. -/
private lemma prod_mul_ne_zero {R : Type*} [MulZeroClass R] [NoZeroDivisors R] {ι κ : Type*}
    {a : ι → R} {b : κ → R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun p : ι × κ => a p.1 * b p.2) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
  exact Function.ne_iff.mpr ⟨(i, j), mul_ne_zero hi hj⟩

/-- The height of a Segre product, computed in a number field `F ⊆ K` containing the
coordinates of the chosen representatives of `x` and `y`. -/
private lemma weilHeight_segreMap_of_numberField {K : Type*} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ]
    [LinearOrder κ] [LinearOrder (ι × κ)] {F : Type*} [Field F] [NumberField F] [Algebra F K]
    {x : ℙ K (ι → K)} {y : ℙ K (κ → K)} {a : ι → F} {b : κ → F}
    (ha : algebraMap F K ∘ a = x.rep) (hb : algebraMap F K ∘ b = y.rep) :
    weilHeight (segreMap x y) = weilHeight x + weilHeight y := by
  have hab : algebraMap F K ∘ (fun p : ι × κ => a p.1 * b p.2) =
      fun p => x.rep p.1 * y.rep p.2 := by
    rw [← ha, ← hb]; ext; simp
  rw [weilHeight_eq_sumLocalHeight (x := x) (ha ▸ x.rep_nonzero) (by simp only [ha, x.mk_rep]),
    weilHeight_eq_sumLocalHeight (x := y) (hb ▸ y.rep_nonzero) (by simp only [hb, y.mk_rep]),
    weilHeight_eq_sumLocalHeight (x := segreMap x y)
      (hab ▸ prod_mul_ne_zero x.rep_nonzero y.rep_nonzero)
      (by simp only [hab]; rfl),
    sumLocalHeight_mul (by rintro rfl; exact x.rep_nonzero (by simp [← ha]))
      (by rintro rfl; exact y.rep_nonzero (by simp [← hb]))]

/-- The Weil height is additive under the Segre map: for `x ∈ ℙ(K^ι)` and `y ∈ ℙ(K^κ)` with
`K / ℚ` algebraic, `h(x ⊗ y) = h(x) + h(y)`, for any linear order on `ι × κ`. -/
@[faltings "lem_ht_segre_veronese"]
public theorem weilHeight_segreMap {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    [LinearOrder (ι × κ)] (x : ℙ K (ι → K)) (y : ℙ K (κ → K)) :
    weilHeight (segreMap x y) = weilHeight x + weilHeight y := by
  set S : Set K := Set.range x.rep ∪ Set.range y.rep
  have : Finite S := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun r _ =>
      (Algebra.IsAlgebraic.isAlgebraic r).isIntegral
  letI : NumberField (IntermediateField.adjoin ℚ S) :=
    { to_finiteDimensional := by convert hfin; exact Subsingleton.elim _ _ }
  exact weilHeight_segreMap_of_numberField (F := IntermediateField.adjoin ℚ S)
    (a := fun i => ⟨x.rep i, IntermediateField.subset_adjoin ℚ S (Or.inl ⟨i, rfl⟩)⟩)
    (b := fun j => ⟨y.rep j, IntermediateField.subset_adjoin ℚ S (Or.inr ⟨j, rfl⟩)⟩) rfl rfl

end Faltings
