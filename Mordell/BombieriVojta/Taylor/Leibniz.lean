module
public import Mordell.BombieriVojta.Taylor.Expansion
/-!
# Leibniz's rule for Taylor coefficients in two local parameters

Let `X` be a scheme over a field `K`, `p ∈ X(K)` a `K`-rational point whose local ring
`𝒪_{X,p}` is regular of dimension two, and `ϖ, ϖ'` a regular system of parameters at `p`. The map
sending `f ∈ 𝒪_{X,p}` to its expansion `∑ ∂_{i₁} ∂'_{i₂} f(p) ϖ^{i₁} ϖ'^{i₂}` in `K⟦ϖ, ϖ'⟧` is a
ring homomorphism, so the Taylor coefficients of a product are given by the coefficient formula
for a product of power series:
`∂_a ∂'_b (∏ₜ fₜ)(p) = ∑_{∑ aₜ = a, ∑ bₜ = b} ∏ₜ ∂_{aₜ} ∂'_{bₜ} fₜ(p)`.

## Main results

* `Faltings.BombieriVojta.taylorCoeff₂_prod`: Leibniz's rule for `taylorCoeff₂` of a finite
  product.

## Implementation notes

The expansion `F ∈ K⟦X₀, X₁⟧` of `f` is characterised by
`f ≡ ∑_{j₁, j₂ < n} F_{j₁ j₂} ϖ ^ j₁ ϖ' ^ j₂ mod 𝔪 ^ n` for all `n`, and the expansion of a
product is visibly a product of expansions; multiplicativity of `taylorCoeff₂` is therefore
uniqueness of the expansion (`Faltings.BombieriVojta.IsExpansion₂.unique`, with existence
`Faltings.BombieriVojta.exists_isExpansion₂`). Uniqueness rests on the associated graded ring
of a regular local ring being a polynomial ring ([StacksProject 00NO],
`IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra`): a form of degree `d` in
`ϖ, ϖ'` whose value lies in `𝔪 ^ (d + 1)` has all its coefficients in `𝔪`. Existence is
successive approximation, the residue field being `K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, pp. 625–626
* [StacksProject 00NO](https://stacks.math.columbia.edu/tag/00NO)
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Faltings.BombieriVojta

section Algebra

open MvPolynomial

variable {K R : Type*} [Field K] [CommRing R]

/-- `1` is an expansion of `1`. -/
private theorem isExpansion₂_one (c : K →+* R) (ϖ ϖ' : R) : IsExpansion₂ c ϖ ϖ' 1 1 := by
  rw [isExpansion₂_iff]
  intro n
  have := eval_map_sub_eval_map_mem c ϖ ϖ' (n := n) 1 (boxTrunc n 1) fun e he => by
    rw [coeff_boxTrunc_of_degree_lt _ he, coeff_one, MvPowerSeries.coeff_one]
    simp only [eq_comm]
  simpa using this

/-- The product of expansions of `f` and `g` is an expansion of `f * g`. -/
private theorem IsExpansion₂.mul {c : K →+* R} {ϖ ϖ' f g : R} {F G : MvPowerSeries (Fin 2) K}
    (hF : IsExpansion₂ c ϖ ϖ' F f) (hG : IsExpansion₂ c ϖ ϖ' G g) :
    IsExpansion₂ c ϖ ϖ' (F * G) (f * g) := by
  classical
  rw [isExpansion₂_iff] at hF hG ⊢
  intro n
  have heq : f * g - eval ![ϖ, ϖ'] (map c (boxTrunc n (F * G))) =
      (f - eval ![ϖ, ϖ'] (map c (boxTrunc n F))) * g +
      eval ![ϖ, ϖ'] (map c (boxTrunc n F)) * (g - eval ![ϖ, ϖ'] (map c (boxTrunc n G))) +
      (eval ![ϖ, ϖ'] (map c (boxTrunc n F * boxTrunc n G)) -
        eval ![ϖ, ϖ'] (map c (boxTrunc n (F * G)))) := by
    rw [map_mul, map_mul]
    ring
  rw [heq]
  refine add_mem (add_mem (Ideal.mul_mem_right _ _ (hF n)) (Ideal.mul_mem_left _ _ (hG n)))
    (eval_map_sub_eval_map_mem c ϖ ϖ' _ _ fun e he => ?_)
  rw [coeff_boxTrunc_of_degree_lt _ he, coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  have h1 : q.1.degree < n := lt_of_le_of_lt (by rw [← hq, map_add]; omega) he
  have h2 : q.2.degree < n := lt_of_le_of_lt (by rw [← hq, map_add]; omega) he
  rw [coeff_boxTrunc_of_degree_lt _ h1, coeff_boxTrunc_of_degree_lt _ h2]

/-- The product of expansions of the `f i` is an expansion of `∏ i, f i`. -/
private theorem isExpansion₂_prod {c : K →+* R} {ϖ ϖ' : R} {ι : Type*}
    (s : Finset ι) (f : ι → R) (F : ι → MvPowerSeries (Fin 2) K)
    (h : ∀ i ∈ s, IsExpansion₂ c ϖ ϖ' (F i) (f i)) :
    IsExpansion₂ c ϖ ϖ' (∏ i ∈ s, F i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isExpansion₂_one c ϖ ϖ'
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Splitting a decomposition of `(a, b)` into decompositions of `a` and of `b`. -/
private theorem sum_finsuppAntidiag_bidegree {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ℕ) (φ : ι → (Fin 2 →₀ ℕ) → K) :
    ∑ L ∈ s.finsuppAntidiag (bidegree (a, b)), ∏ i ∈ s, φ i (L i) =
      ∑ l ∈ s.finsuppAntidiag a, ∑ m ∈ s.finsuppAntidiag b,
        ∏ i ∈ s, φ i (bidegree (l i, m i)) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun L => (L.mapRange (fun g => g 0) rfl, L.mapRange (fun g => g 1) rfl))
    (fun lm => Finsupp.zipWith (fun u v => bidegree (u, v)) (by ext i; fin_cases i <;> simp)
      lm.1 lm.2) ?_ ?_ ?_ ?_ ?_
  · intro L hL
    rw [Finset.mem_finsuppAntidiag] at hL
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag, Finsupp.mapRange_apply]
    refine ⟨⟨?_, Finsupp.support_mapRange.trans hL.2⟩, ⟨?_, Finsupp.support_mapRange.trans hL.2⟩⟩
    · refine (Finset.sum_congr rfl fun i _ => Finsupp.mapRange_apply).trans ?_
      rw [← Finsupp.finsetSum_apply, hL.1, bidegree_apply_zero]
    · refine (Finset.sum_congr rfl fun i _ => Finsupp.mapRange_apply).trans ?_
      rw [← Finsupp.finsetSum_apply, hL.1, bidegree_apply_one]
  · intro lm hlm
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag] at hlm ⊢
    refine ⟨?_, (Finsupp.support_zipWith).trans (Finset.union_subset hlm.1.2 hlm.2.2)⟩
    ext k
    fin_cases k
    · simp [Finsupp.finsetSum_apply, hlm.1.1]
    · simp [Finsupp.finsetSum_apply, hlm.2.1]
  · intro L _
    ext i : 1
    simp [bidegree_apply_eq]
  · intro lm _
    ext i <;> simp
  · intro L _
    simp [bidegree_apply_eq]
end Algebra

/-- **Leibniz's rule** for the Taylor coefficients in two local parameters: at a `K`-rational
point `p` of a `K`-scheme `X` whose local ring is regular of dimension two with maximal ideal
`(ϖ, ϖ')`, the coefficient of `ϖ ^ a * ϖ' ^ b` in a product `∏_{i ∈ s} f i` is the sum, over all
decompositions `a = ∑ aᵢ` and `b = ∑ bᵢ`, of the products of the coefficients of
`ϖ ^ aᵢ * ϖ' ^ bᵢ` in the `f i`. -/
@[faltings "lem_bv_divided_leibniz"]
public theorem taylorCoeff₂_prod {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    [IsRegularLocalRing (X.presheaf.stalk (p (closedPoint K)))]
    (hdim : ringKrullDim (X.presheaf.stalk (p (closedPoint K))) = 2)
    {ϖ ϖ' : X.presheaf.stalk (p (closedPoint K))}
    (hϖ : maximalIdeal (X.presheaf.stalk (p (closedPoint K))) = Ideal.span {ϖ, ϖ'})
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → X.presheaf.stalk (p (closedPoint K)))
    (a b : ℕ) :
    taylorCoeff₂ p ϖ ϖ' (∏ i ∈ s, f i) a b =
      ∑ l ∈ s.finsuppAntidiag a, ∑ m ∈ s.finsuppAntidiag b,
        ∏ i ∈ s, taylorCoeff₂ p ϖ ϖ' (f i) (l i) (m i) := by
  classical
  let c : K →+* X.presheaf.stalk (p (closedPoint K)) := const _
  have key : ∀ g i j, taylorCoeff₂ p ϖ ϖ' g i j =
      MvPowerSeries.coeff (bidegree (i, j)) (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F g) :=
    fun g i j => rfl
  have hspec : ∀ g, IsExpansion₂ c ϖ ϖ' (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F g) g :=
    fun g => Classical.epsilon_spec <|
      exists_isExpansion₂ hϖ c (Scheme.stalkClosedPointTo p).hom (ev_const p (comp_over_eq_id p)) g
  have hprod : Classical.epsilon (fun F ↦ IsExpansion₂ c ϖ ϖ' F (∏ i ∈ s, f i)) =
      ∏ i ∈ s, Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F (f i) :=
    (hspec _).unique hdim hϖ (isExpansion₂_prod s f _ fun i _ => hspec (f i))
  simp only [key]
  rw [hprod, MvPowerSeries.coeff_prod]
  exact sum_finsuppAntidiag_bidegree s a b
    (fun i g => MvPowerSeries.coeff g (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F (f i)))

end Faltings.BombieriVojta
