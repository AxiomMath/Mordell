module
public import Mathlib
public import Mordell.Attr

/-!
# The number of monomials of a given degree

A monomial in the variables indexed by `σ` is an exponent vector `f : σ →₀ ℕ`, and its degree is
`Finsupp.degree f = ∑ i, f i`. If `σ` has `n + 1` elements, the monomials of degree exactly `e`
correspond to the multisets of size `e` drawn from `σ`, so there are `(n + e).choose n` of them.

## Main results

* `Faltings.ncard_degree_eq`: if `Nat.card σ = n + 1`, the set
  `{f : σ →₀ ℕ | f.degree = e}` has `(n + e).choose n` elements.

## Implementation notes

The variables are indexed by an arbitrary type `σ` with `Nat.card σ = n + 1`, rather than by
`Fin (n + 1)`; this hypothesis already forces `σ` to be finite, so no `Fintype` instance is
taken. The count is `Set.ncard`, which is the honest cardinality since the set is finite
(`Finsupp.finite_of_degree_eq`). The proof identifies the set with
`Finset.univ.finsuppAntidiag e` and applies the stars-and-bars count
`Finset.card_finsuppAntidiag_nat_eq_choose`.

## References

* [Z. Gao, *Heights*][gao2022].
-/

namespace Faltings

/-- On a finite type, the finitely supported functions `σ →₀ ℕ` of total degree `e` are exactly
the elements of `univ.finsuppAntidiag e`. -/
private lemma setOf_degree_eq_finsuppAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ] (e : ℕ) :
    {f : σ →₀ ℕ | f.degree = e} = ↑((Finset.univ : Finset σ).finsuppAntidiag e) := by
  ext f
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

/-- If `σ` has `n + 1` elements, the number of monomials of degree exactly `e` in the variables
indexed by `σ` is `(n + e).choose n`. -/
@[faltings "lem_ht_monomials_exact_degree"]
public theorem ncard_degree_eq {σ : Type*} {n : ℕ} (hσ : Nat.card σ = n + 1) (e : ℕ) :
    {f : σ →₀ ℕ | f.degree = e}.ncard = (n + e).choose n := by
  have : Finite σ := Nat.finite_of_card_ne_zero (by omega)
  classical
  let _ := Fintype.ofFinite σ
  rw [setOf_degree_eq_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, ← Nat.card_eq_fintype_card, hσ,
    Nat.add_right_comm, Nat.add_sub_cancel, Nat.choose_symm_add]

end Faltings

/-!
# The number of monomials of a given bidegree

A monomial in the two sets of variables `x₀, …, xₙ` and `y₀, …, y_{n'}` is given by its
exponent vector, a finitely supported function `Fin (n + 1) ⊕ Fin (n' + 1) →₀ ℕ`. It has
bidegree `(δ₁, δ₂)` when its exponents in the `x`'s sum to `δ₁` and those in the `y`'s sum
to `δ₂`. There are `(δ₁ + n).choose n * (δ₂ + n').choose n'` such monomials: each is the
product of a monomial of degree `δ₁` in the `x`'s and one of degree `δ₂` in the `y`'s.

## Main results

* `Faltings.card_bidegree_monomials`: the number of monomials of bidegree `(δ₁, δ₂)` in
  `n + 1` and `n' + 1` variables is `(δ₁ + n).choose n * (δ₂ + n').choose n'`.

## Implementation notes

Monomials are identified with their exponent vectors, as in `MvPolynomial`, whose monomials
in the variables `Fin (n + 1) ⊕ Fin (n' + 1)` are indexed by `Fin (n + 1) ⊕ Fin (n' + 1) →₀ ℕ`.
The count is `Nat.card` of the set of exponent vectors of the given bidegree.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 6, proof of Lemma 3.
-/

namespace Faltings

/-- Monomials of bidegree `(δ₁, δ₂)` in the variables `σ ⊕ τ` are pairs of a monomial of degree
`δ₁` in `σ` and one of degree `δ₂` in `τ`. -/
private noncomputable def bidegreeEquiv {σ τ : Type*} [Fintype σ] [Fintype τ] (δ₁ δ₂ : ℕ) :
    {d : σ ⊕ τ →₀ ℕ // ∑ i, d (Sum.inl i) = δ₁ ∧ ∑ j, d (Sum.inr j) = δ₂} ≃
      {f : σ →₀ ℕ | f.degree = δ₁} × {g : τ →₀ ℕ | g.degree = δ₂} :=
  (Finsupp.sumFinsuppEquivProdFinsupp.subtypeEquiv
      (q := fun fg => fg.1.degree = δ₁ ∧ fg.2.degree = δ₂) fun d => by
    simp [Finsupp.degree_eq_sum, Finsupp.sumFinsuppEquivProdFinsupp]).trans
    (Equiv.subtypeProdEquivProd (p := fun f : σ →₀ ℕ => f.degree = δ₁)
      (q := fun g : τ →₀ ℕ => g.degree = δ₂))

/-- The number of monomials of bidegree `(δ₁, δ₂)` in the two sets of variables indexed by
`Fin (n + 1)` and `Fin (n' + 1)` is `(δ₁ + n).choose n * (δ₂ + n').choose n'`. -/
@[faltings "lem_ht_number_of_monomials"]
public theorem card_bidegree_monomials (n n' δ₁ δ₂ : ℕ) :
    Nat.card {d : Fin (n + 1) ⊕ Fin (n' + 1) →₀ ℕ //
      ∑ i, d (Sum.inl i) = δ₁ ∧ ∑ j, d (Sum.inr j) = δ₂} =
      (δ₁ + n).choose n * (δ₂ + n').choose n' := by
  rw [Nat.card_congr (bidegreeEquiv δ₁ δ₂), Nat.card_prod, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, ncard_degree_eq (n := n) (by simp), ncard_degree_eq (n := n') (by simp),
    add_comm n, add_comm n']

end Faltings

/-!
# Counting tuples of natural numbers with a given sum

For `1 ≤ a`, the number of `a`-tuples of natural numbers whose entries sum to `i` is the
stars-and-bars count `(a + i - 1).choose i`, and this is at most `(a + i).choose i ≤ 2 ^ (a + i)`.

## Main results

* `Faltings.card_antidiagonalTuple_eq_choose_and_le`: the count, together with the two bounds.

## Implementation notes

The tuples are Mathlib's `Finset.Nat.antidiagonalTuple a i`, the finset of `x : Fin a → ℕ` with
`∑ j, x j = i`. The condition `0 ≤ i` is automatic in `ℕ`. The count is deduced from
`Faltings.ncard_degree_eq`, the number of monomials of degree `i`, through
`Finsupp.equivFunOnFinite`.

## References

* [Z. Gao, *Heights*][gao2022]
-/

namespace Faltings

/-- Under `Finsupp.equivFunOnFinite`, the `(n + 1)`-tuples summing to `i` are exactly the
monomials of degree `i` in `n + 1` variables. -/
private lemma setOf_degree_eq_image_antidiagonalTuple (n i : ℕ) :
    {f : Fin (n + 1) →₀ ℕ | f.degree = i} =
      Finsupp.equivFunOnFinite.symm '' ↑(Finset.Nat.antidiagonalTuple (n + 1) i) := by
  ext f
  simp [Finsupp.degree_eq_sum, Finsupp.equivFunOnFinite.symm.image_eq_preimage_symm,
    Finset.Nat.mem_antidiagonalTuple]

/-- Stars and bars: there are `(n + i).choose i` tuples in `ℕ ^ (n + 1)` summing to `i`. -/
private lemma card_antidiagonalTuple_succ (n i : ℕ) :
    (Finset.Nat.antidiagonalTuple (n + 1) i).card = (n + i).choose i := by
  have h := ncard_degree_eq (σ := Fin (n + 1)) (n := n) (by simp) i
  rw [setOf_degree_eq_image_antidiagonalTuple, Set.ncard_image_of_injective _ (Equiv.injective _),
    Set.ncard_coe_finset] at h
  exact h.trans Nat.choose_symm_add

/-- For `1 ≤ a`, the number of `a`-tuples of natural numbers with sum `i` is
`(a + i - 1).choose i`, which is at most `(a + i).choose i`, which is at most `2 ^ (a + i)`. -/
@[faltings "lem_ht_tuple_count"]
public theorem card_antidiagonalTuple_eq_choose_and_le (a i : ℕ) (ha : 1 ≤ a) :
    (Finset.Nat.antidiagonalTuple a i).card = (a + i - 1).choose i ∧
      (a + i - 1).choose i ≤ (a + i).choose i ∧
      (a + i).choose i ≤ 2 ^ (a + i) := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact ⟨by rw [card_antidiagonalTuple_succ, Nat.add_right_comm, Nat.add_sub_cancel],
    Nat.choose_le_choose i (Nat.sub_le _ _), Nat.choose_le_two_pow _ _⟩

end Faltings
