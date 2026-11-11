module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.TripleFunction.AffineFunctions
public import Mordell.BombieriVojta.Taylor.Curve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import Mordell.BombieriVojta.Taylor.Expansion

/-!
# Taylor coefficients of monomials in the `ξ_{νj}`

Let `C` be a curve over a number field `K`, `p ∈ C(K)` a rational point, `ϖ` a local
uniformizing parameter at `p` and `v` a place of `K`. Let `ξ_ν` (`ν ∈ ι`) be functions regular
at `p` with `|ξ_ν(p)|_v ≤ 1` for every `ν` (in the source, `ξ_ν = ξ_{νj} = x_ν / x_j` for an
index `j` with `x_j(p) ≠ 0` and `|x_j(p)|_v` maximal), and let `ξ^l = ∏_ν ξ_ν ^ {l_ν}` be a
monomial of degree `δ = ∑_ν l_ν ≥ 1`. Writing `∂_i = ∂_i^ϖ` for the Taylor coefficients at `p`,
for every `i* ≥ 0`
`log |∂_{i*}(ξ^l)(p)|_v ≤ max_{i_λ} ∑_λ max_ν log |∂_{i_λ} ξ_ν(p)|_v + ε_v log |2^{δ + i*}|_v`,
the maximum running over the partitions `{i_λ}` of `i*`, with `log 0 = -∞`; here `ε_v` is `1`
at an archimedean place and `0` at a finite one. The proof expands `∂_{i*}(ξ^l)` by the
Leibniz rule, counts the at most `2^{δ + i*}` terms, and bounds each term by the factors of
positive index, the others having absolute value at most `1`.

## Main results

* `Faltings.BombieriVojta.logAbs_taylorCoeff_prod_pow_le`: the bound above.

## Implementation notes

* The curve is `C` over `Spec K` (the source's curve over `k ⊆ K`, after base change to `K`),
  `p` is a `K`-point over `Spec K`, and "`ϖ` is a local uniformizing parameter at `p`" is
  `maximalIdeal 𝒪_{C,p} = (ϖ)`. The Taylor coefficients are
  `Faltings.BombieriVojta.taylorCoeff`.
* The functions `ξ_ν` are given as elements of the local ring `𝒪_{C,p}`, i.e. as germs of
  functions regular at `p`; the source's `ξ_{νj} = x_ν / x_j` with `x_j(p) ≠ 0` is the case of
  the germs of `x_ν / x_j`. The value at `p` is `AlgebraicGeometry.Scheme.stalkClosedPointTo p`.
* A place is a term of `InfinitePlace K ⊕ FinitePlace K`. The normalised `log |x|_v` is
  `(n_v / [K : ℚ]) log ‖x‖_v` (with `n_v = mult v` at an infinite place and `1` at a finite
  place) for `x ≠ 0` and `⊥ = -∞` for `x = 0`, so the inequality is stated in `EReal`; the term
  `ε_v log |2^{δ + i*}|_v` is `log |2^{δ + i*}|_v` at an infinite place and `0` at a finite one.
  Partitions are `Nat.Partition i*` and the maxima are `Finset.sup`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 626
-/

open AlgebraicGeometry CategoryTheory IsLocalRing PowerSeries _root_.NumberField Module
open scoped NNReal

universe u

namespace Faltings.BombieriVojta

section Geometry

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (z : Spec (.of K) ⟶ X) [z.IsOver (Spec (.of K))]

/-- The constants of `𝒪_{X,z}`. -/
@[expose] public noncomputable abbrev constants : K →+* X.presheaf.stalk (z (closedPoint K)) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
    X.presheaf.germ ⊤ (z (closedPoint K)) trivial).hom

/-- Evaluation at a `K`-point is a retraction of the constants. -/
public lemma stalkClosedPointTo_constants (k : K) :
    (Scheme.stalkClosedPointTo z).hom (constants z k) = k :=
  ev_const z (comp_over_eq_id z) k

end Geometry

section Bound

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (N : K →*₀ ℝ≥0) (F : ι → K⟦X⟧)

/-- `max_ν N (a_m (F ν))`. -/
private noncomputable def maxCoeff (m : ℕ) : ℝ≥0 := Finset.univ.sup fun ν => N (coeff m (F ν))

/-- The maximum over the partitions `{i_λ}` of `i` of `∏_λ max_ν N (a_{i_λ} (F ν))`. -/
private noncomputable def partBound (i : ℕ) : ℝ≥0 :=
  (Finset.univ : Finset (Nat.Partition i)).sup fun π => (π.parts.map (maxCoeff N F)).prod

private lemma one_le_partBound_zero : 1 ≤ partBound N F 0 :=
  le_trans (by simp) (Finset.le_sup (f := fun π : Nat.Partition 0 =>
    (π.parts.map (maxCoeff N F)).prod) (Finset.mem_univ ⟨0, by simp, by simp⟩))

private lemma maxCoeff_mul_partBound_le {a : ℕ} (ha : 0 < a) (b : ℕ) :
    maxCoeff N F a * partBound N F b ≤ partBound N F (a + b) := by
  rw [partBound, NNReal.mul_finset_sup, Finset.sup_le_iff]
  intro π _
  let π' : Nat.Partition (a + b) := ⟨a ::ₘ π.parts, by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact ha
    · exact π.parts_pos hi, by simp [π.parts_sum]⟩
  have : maxCoeff N F a * (π.parts.map (maxCoeff N F)).prod =
      (π'.parts.map (maxCoeff N F)).prod := by simp [π']
  rw [this]
  exact Finset.le_sup (f := fun π : Nat.Partition (a + b) => (π.parts.map (maxCoeff N F)).prod)
    (Finset.mem_univ _)

variable (W : ℕ → ℕ → ℝ≥0)

/-- `G` satisfies the bound of a product of `d` factors. -/
private def Bounded (d : ℕ) (G : K⟦X⟧) : Prop :=
  ∀ i, N (coeff i G) ≤ W d i * partBound N F i

variable {N F W}

private lemma Bounded.mul (hW : ∀ d i (t : ℕ × ℕ → K),
      (∀ p ∈ Finset.HasAntidiagonal.antidiagonal i, N (t p) ≤ W d p.1 * partBound N F i) →
      N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p) ≤ W (d + 1) i * partBound N F i)
    (h0 : ∀ ν, N (constantCoeff (F ν)) ≤ 1) {d : ℕ} {G : K⟦X⟧} (hG : Bounded N F W d G)
    (ν : ι) : Bounded N F W (d + 1) (G * F ν) := by
  intro i
  rw [coeff_mul]
  refine hW d i _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_mul]
  rcases Nat.eq_zero_or_pos p.2 with h2 | h2
  · have h1 : p.1 = i := by omega
    calc N (coeff p.1 G) * N (coeff p.2 (F ν)) ≤ (W d p.1 * partBound N F p.1) * 1 := by
          gcongr
          · exact hG _
          · rw [h2, coeff_zero_eq_constantCoeff_apply]
            exact h0 ν
      _ = W d p.1 * partBound N F i := by rw [h1, mul_one]
  · calc N (coeff p.1 G) * N (coeff p.2 (F ν))
        ≤ (W d p.1 * partBound N F p.1) * maxCoeff N F p.2 := by
          gcongr
          · exact hG _
          · exact Finset.le_sup (f := fun ν => N (coeff p.2 (F ν))) (Finset.mem_univ ν)
      _ = W d p.1 * (maxCoeff N F p.2 * partBound N F p.1) := by ring
      _ ≤ W d p.1 * partBound N F (p.2 + p.1) := by
          gcongr
          exact maxCoeff_mul_partBound_le N F h2 _
      _ = W d p.1 * partBound N F i := by rw [add_comm, hp]

private lemma bounded_prod_pow (hW0 : W 0 0 = 1) (hW : ∀ d i (t : ℕ × ℕ → K),
      (∀ p ∈ Finset.HasAntidiagonal.antidiagonal i, N (t p) ≤ W d p.1 * partBound N F i) →
      N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p) ≤ W (d + 1) i * partBound N F i)
    (h0 : ∀ ν, N (constantCoeff (F ν)) ≤ 1) (l : ι → ℕ) (S : Finset ι) :
    Bounded N F W (∑ ν ∈ S, l ν) (∏ ν ∈ S, F ν ^ l ν) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa [hW0] using one_le_partBound_zero N F
    · simp [coeff_one, hi.ne']
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_comm, add_comm]
    have key : ∀ k, Bounded N F W (∑ ν ∈ S, l ν + k) ((∏ ν ∈ S, F ν ^ l ν) * F a ^ k) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        rw [pow_succ, ← mul_assoc, ← add_assoc]
        exact Bounded.mul hW h0 ihk a
    exact key _

/-- At an archimedean place the `i + 1` terms of a coefficient of a product contribute a factor
`∑_{b ≤ i} 2^{d+b} ≤ 2^{d+1+i}`. -/
private lemma hW_arch
    (hsub : ∀ (s : Finset (ℕ × ℕ)) (t : ℕ × ℕ → K), N (∑ p ∈ s, t p) ≤ ∑ p ∈ s, N (t p))
    (d i : ℕ) (t : ℕ × ℕ → K)
    (ht : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i,
      N (t p) ≤ (2 : ℝ≥0) ^ (d + p.1) * partBound N F i) :
    N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p) ≤
      (2 : ℝ≥0) ^ (d + 1 + i) * partBound N F i := by
  have geom : ∀ n, ∑ k ∈ Finset.range n, (2 : ℝ≥0) ^ (d + k) ≤ 2 ^ (d + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, pow_succ]
      calc _ ≤ (2 : ℝ≥0) ^ (d + n) + 2 ^ (d + n) := by gcongr
        _ = _ := by ring
  calc N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p)
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, (2 : ℝ≥0) ^ (d + p.1) * partBound N F i :=
        (hsub _ _).trans (Finset.sum_le_sum ht)
    _ = (∑ k ∈ Finset.range (i + 1), (2 : ℝ≥0) ^ (d + k)) * partBound N F i := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    _ ≤ (2 : ℝ≥0) ^ (d + 1 + i) * partBound N F i := by
        gcongr
        exact (geom _).trans_eq (by ring_nf)

/-- At a non-archimedean place a sum is bounded by its largest term. -/
private lemma hW_nonarch (hult : ∀ x y, N (x + y) ≤ max (N x) (N y)) (d i : ℕ)
    (t : ℕ × ℕ → K) (ht : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i,
      N (t p) ≤ (fun _ _ => (1 : ℝ≥0)) d p.1 * partBound N F i) :
    N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p) ≤
      (fun _ _ => (1 : ℝ≥0)) (d + 1) i * partBound N F i :=
  Finset.sum_induction _ (fun x => N x ≤ 1 * partBound N F i)
    (fun _ _ hx hy => (hult _ _).trans (max_le hx hy)) (by simp) ht

end Bound

section Log

/-- `t ↦ a log t` on `ℝ≥0`, with `log 0 = ⊥`. -/
private noncomputable def logNN (a : ℝ) (t : ℝ≥0) : EReal :=
  if t = 0 then ⊥ else ((a * Real.log t : ℝ) : EReal)

variable {a : ℝ}

private lemma logNN_mul (s t : ℝ≥0) : logNN a (s * t) = logNN a s + logNN a t := by
  unfold logNN
  by_cases hs : s = 0
  · simp [hs]
  by_cases ht : t = 0
  · simp [ht]
  simp only [mul_eq_zero, hs, ht, or_self, ↓reduceIte, NNReal.coe_mul]
  rw [Real.log_mul (by simpa using hs) (by simpa using ht), mul_add, EReal.coe_add]

private lemma logNN_one : logNN a 1 = 0 := by simp [logNN]

private lemma logNN_prod (m : Multiset ℝ≥0) : logNN a m.prod = (m.map (logNN a)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [logNN_one]
  | cons x m ih => simp [logNN_mul, ih]

variable (ha : 0 < a)

include ha

private lemma logNN_mono : Monotone (logNN a) := by
  intro s t hst
  unfold logNN
  by_cases hs : s = 0
  · simp [hs]
  · have ht : t ≠ 0 := ne_bot_of_le_ne_bot hs hst
    simp only [hs, ht, ↓reduceIte, EReal.coe_le_coe_iff]
    gcongr

private lemma logNN_sup {α : Type*} (s : Finset α) (f : α → ℝ≥0) :
    logNN a (s.sup f) = s.sup (logNN a ∘ f) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder _ (logNN_mono ha) (by simp [logNN])

private lemma le_one_of_logNN_nonpos {t : ℝ≥0} (h : logNN a t ≤ 0) : t ≤ 1 := by
  unfold logNN at h
  split_ifs at h with ht
  · simp [ht]
  · have h' : a * Real.log t ≤ 0 := by exact_mod_cast h
    have : Real.log t ≤ 0 := by nlinarith
    have := (Real.log_nonpos_iff (by positivity)).mp this
    exact_mod_cast this

end Log

section Final

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] {N : K →*₀ ℝ≥0} {F : ι → K⟦X⟧}
  {a : ℝ}

private lemma sup_sum_logNN (ha : 0 < a) (i : ℕ) :
    (Finset.univ : Finset (Nat.Partition i)).sup (fun π =>
      (π.parts.map fun m => Finset.univ.sup fun ν => logNN a (N (coeff m (F ν)))).sum) =
      logNN a (partBound N F i) := by
  rw [partBound, logNN_sup ha]
  congr 1
  funext π
  rw [Function.comp_apply, logNN_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro m _
  rw [Function.comp_apply, maxCoeff, logNN_sup ha]
  rfl

/-- **The bound for a monomial in power series.** If every `F ν` has constant term of size at
most `1`, and `W` bounds the growth of a coefficient of a product by one more factor, then the
`i`-th coefficient of `∏ ν, F ν ^ l ν` has `a log`-size at most the maximum over the partitions
`{i_λ}` of `i` of `∑_λ max_ν a log N (a_{i_λ} (F ν))`, plus `a log W (∑ ν, l ν) i`. -/
private lemma logNN_coeff_prod_pow_le (ha : 0 < a) {W : ℕ → ℕ → ℝ≥0} (hW0 : W 0 0 = 1)
    (hW : ∀ d i (t : ℕ × ℕ → K),
      (∀ p ∈ Finset.HasAntidiagonal.antidiagonal i, N (t p) ≤ W d p.1 * partBound N F i) →
      N (∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, t p) ≤ W (d + 1) i * partBound N F i)
    (h0 : ∀ ν, logNN a (N (constantCoeff (F ν))) ≤ 0) (l : ι → ℕ) (i : ℕ) :
    logNN a (N (coeff i (∏ ν, F ν ^ l ν))) ≤
      (Finset.univ : Finset (Nat.Partition i)).sup (fun π =>
        (π.parts.map fun m => Finset.univ.sup fun ν => logNN a (N (coeff m (F ν)))).sum) +
      logNN a (W (∑ ν, l ν) i) := by
  rw [sup_sum_logNN ha, ← logNN_mul, mul_comm]
  exact logNN_mono ha <| bounded_prod_pow hW0 hW
    (fun ν => le_one_of_logNN_nonpos ha (h0 ν)) l Finset.univ i

end Final

/-- An absolute value, as a multiplicative map to `ℝ≥0`. -/
private noncomputable def nnAbv {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : K →*₀ ℝ≥0 where
  toFun x := ⟨v x, v.nonneg x⟩
  map_zero' := NNReal.eq v.map_zero
  map_one' := NNReal.eq v.map_one
  map_mul' x y := NNReal.eq (v.map_mul x y)

private lemma coe_nnAbv {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (x : K) :
    (nnAbv v x : ℝ) = v x := rfl

/-- The normalised `log |x|_v` is `logNN a (|x|_v)`. -/
private lemma logNN_nnAbv {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (a : ℝ) (x : K) :
    (haveI := Classical.propDecidable (x = 0)
      if x = 0 then ⊥ else ((a * Real.log (v x) : ℝ) : EReal)) = logNN a (nnAbv v x) := by
  have : nnAbv v x = 0 ↔ x = 0 := by rw [← NNReal.coe_eq_zero, coe_nnAbv, v.eq_zero]
  by_cases hx : x = 0 <;> simp [hx, logNN, this, coe_nnAbv]

/-- **Taylor coefficients of a monomial.** Let `C` be a curve over a number field `K`, `p` a
`K`-point of `C` and `ϖ` a generator of the maximal ideal of `𝒪_{C,p}`. Let `ξ : ι → 𝒪_{C,p}` be
a finite family with `log |ξ_ν(p)|_v ≤ 0` for every `ν` at the place `v`, and `l : ι → ℕ` with
`∑ ν, l ν = δ ≥ 1`. Then `log |taylorCoeff p ϖ (∏ ν, ξ ν ^ l ν) i|_v` is at most the maximum over
the partitions `π` of `i` of `∑_{m ∈ π} max_ν log |taylorCoeff p ϖ (ξ ν) m|_v`, plus
`log |2 ^ (δ + i)|_v` if `v` is infinite. -/
@[faltings "lem_bv_derivative_of_monomial_bound"]
public theorem logAbs_taylorCoeff_prod_pow_le {K : Type u} [Field K] [NumberField K]
    {C : Scheme.{u}} [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))]
    (p : Spec (.of K) ⟶ C) [p.IsOver (Spec (.of K))]
    (ϖ : C.presheaf.stalk (p (closedPoint K)))
    (hϖ : maximalIdeal (C.presheaf.stalk (p (closedPoint K))) = Ideal.span {ϖ})
    (v : InfinitePlace K ⊕ FinitePlace K)
    {ι : Type*} [Fintype ι] (ξ : ι → C.presheaf.stalk (p (closedPoint K)))
    (l : ι → ℕ) (δ : ℕ) (hl : ∑ ν, l ν = δ) (hδ : 1 ≤ δ) (i : ℕ) :
    -- Bombieri's normalised `log |x|_v`, with `log 0 = ⊥`
    let logAbs : K → EReal := fun x =>
      haveI := Classical.propDecidable (x = 0)
      if x = 0 then ⊥ else
        ((Sum.elim (fun w : InfinitePlace K => (w.mult : ℝ) / finrank ℚ K * Real.log (w x))
          (fun w : FinitePlace K => 1 / finrank ℚ K * Real.log (w x)) v : ℝ) : EReal)
    (∀ ν, logAbs ((Scheme.stalkClosedPointTo p).hom (ξ ν)) ≤ 0) →
    logAbs (taylorCoeff p ϖ (∏ ν, ξ ν ^ l ν) i) ≤
      (Finset.univ : Finset (Nat.Partition i)).sup (fun π =>
          (π.parts.map fun m => Finset.univ.sup fun ν => logAbs (taylorCoeff p ϖ (ξ ν) m)).sum) +
        Sum.elim (fun _ => logAbs (2 ^ (δ + i))) (fun _ => 0) v := by
  intro logAbs hξ
  set E := curveExpansion p (comp_over_eq_id p) hϖ
  have hE : ∀ f j, taylorCoeff p ϖ f j = coeff j (E f) := fun f j =>
    (coeff_curveExpansion p (comp_over_eq_id p) hϖ f j).symm
  have hE0 : ∀ f, (Scheme.stalkClosedPointTo p).hom f = constantCoeff (E f) := fun f =>
    (constantCoeff_curveExpansion p (comp_over_eq_id p) hϖ f).symm
  simp only [hE, map_prod, map_pow] at hξ ⊢
  simp only [hE0] at hξ
  subst hl
  rcases v with w | w
  · have hlog : ∀ x, logAbs x = logNN ((w.mult : ℝ) / finrank ℚ K) (nnAbv w.1 x) :=
      fun x => logNN_nnAbv w.1 _ x
    have h2 : nnAbv w.1 (2 ^ (∑ ν, l ν + i)) = 2 ^ (∑ ν, l ν + i) := NNReal.eq <| by
      rw [coe_nnAbv, map_pow, NNReal.coe_pow]
      exact congrArg (· ^ _) (mod_cast InfinitePlace.map_natCast w 2)
    simp only [hlog, Sum.elim_inl, h2] at hξ ⊢
    exact logNN_coeff_prod_pow_le
      (div_pos (by exact_mod_cast w.mult_pos) (by exact_mod_cast finrank_pos))
      (W := fun d j => 2 ^ (d + j)) (by simp)
      (hW_arch fun s t => by rw [← NNReal.coe_le_coe, NNReal.coe_sum]; exact w.1.sum_le s t)
      hξ l i
  · have ha : 0 < 1 / (finrank ℚ K : ℝ) := by simpa using finrank_pos
    have hlog : ∀ x, logAbs x = logNN (1 / finrank ℚ K) (nnAbv w.1 x) :=
      fun x => logNN_nnAbv w.1 _ x
    simp only [hlog, Sum.elim_inr] at hξ ⊢
    simpa only [logNN_one, add_zero] using logNN_coeff_prod_pow_le ha
      (W := fun _ _ => 1) rfl (hW_nonarch fun x y => by exact_mod_cast FinitePlace.add_le w x y)
      hξ l i

end Faltings.BombieriVojta
