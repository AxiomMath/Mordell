module
public import Mordell.BombieriVojta.DerivativeEstimate.ExceptionalSet
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.Height.NPNeronNorm
public import Mordell.Curve.DegreeOverRationalSubfield
public import Mordell.Polynomial.Eisenstein.Finite
public import Mordell.Polynomial.Eisenstein.Infinite
public import Mordell.Height.Affine.Eval
public import Mordell.BombieriVojta.Taylor.AlgebraicFunction
public import Mordell.Height.Affine.Ratio
public import Mordell.CurveProduct.VojtaClass
public import Mordell.CurveProduct.Embedding.B
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorGeneration
public import Mordell.BombieriVojta.Projection.EmbeddingCoordinates

/-!
# The Taylor-coefficient term of Bombieri's Lemma 4

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `N ≥ 2g + 1`, and `x₀, …, xₙ` a generic basis of `L(NP) = H⁰(C, 𝒪(NP))`, with
`ξ_{νj} = x_ν / x_j`. Let `z ∈ C(K)` be a point, over a number field `K ⊇ k`, outside the
exceptional set `Z`, and expand the functions regular at `z` in `K⟦ς⟧`, `ς = ξ₁₀ - ξ₁₀(z)`. For
each place `v` of `K` let `j_v` be an index with `|ξ_{ν j_v}(z)|_v ≤ 1` for all `ν`. Then there
are constants `c₈, c₉` depending only on `C`, `P` and the basis such that for every `i* ≥ 0`
`∑_v max_{i_λ} ∑_λ max_ν log |∂_{i_λ} ξ_{ν j_v}(0)|_v ≤ c₈ i* |z|² + c₉ i*`,
the maximum running over the partitions `{i_λ}` of `i*` and `|z|` being the Néron norm.

The proof has two parts. In the first, the local Eisenstein bounds, applied at every place to
the shifted plane relations `p_{νj}(X, ς) = g_{νj}(X, ς + ξ₁₀(z))`, give
`log |∂_i ξ_{νj}(0)|_v ≤ i T_v`; summing over the places through the height of a polynomial
value gives `≤ i* (A₀ + A₁ h(y))`, where `y = (ξ_{a0}(z))_a`. The constants are uniform in `K`
because the plane relations over `K` are those over `k` read in `K`: `K` and `k(C)` are linearly
disjoint in `K(C_K)`. In the second part, `y` is the vector of homogeneous coordinates of
`φ_{NP}(z)` on a basis of `Γ(C, 𝒪(NP))` matching `x`, and the comparison of `h_{NP}` with the
Néron norm gives `h(y) ≤ B₀ + B₁ |z|²`.

## Main results

* `Faltings.BombieriSiegel.exists_finsum_iSup_log_dividedDerivative_le`: the bound.

## Implementation notes

The curve is a `Faltings.CurveWithDegreeOneDivisor`, and the Néron norm is read exactly as in
`Faltings.exists_abs_weilHeight_sub_neronPairing_le` and
`Faltings.exists_pos_neronPairing_ge_of_ne`: on a Jacobian `A : Faltings.Jacobian k X.f` with
Abel–Jacobi map `j` (`Faltings.IsAbelJacobiMap`) and the reduced effective Cartier divisor `D`
whose support is `Faltings.thetaDivisor`, `|z| = √⟨j z, j z⟩` with `⟨·, ·⟩ =
Faltings.neronPairing` on `J(k̄)`. The algebraic closure `k̄` is fixed before the constants,
and the `K`-point `z` is read in `C(k̄)` through a `k`-embedding `K → k̄`. The constants are
chosen before `K`.

The exceptional set `Faltings.BombieriSiegel.exceptionalSet` is a set of rational points, so the
point `z ∈ C(K)` is read on the base change: `C_K` is any `K`-scheme `fK : C_K ⟶ Spec K` with a
morphism `π : C_K ⟶ C` making a pullback square over `Spec K ⟶ Spec k`, the family `x` is
pulled back along `π` (`functionFieldMap π`), the divisor `N P` is pulled back to the divisor
`Q ↦ N P(π Q)` of `C_K` (the base change is étale over `C`, `K/k` being separable), and
`z_K : Spec K ⟶ C_K` is the `K`-point over `z`. The germs of `ξ_{10}` and of the `ξ_{ν j_v}` at
`z_K` are given as stalk elements, `ς` is `ξ₁₀ - ξ₁₀(z)` in the stalk, and the expansion of `ξ`
is `PowerSeries.mk (taylorCoeff z_K ς ξ)`, whose `i`-th divided derivative at `0` is
`constantCoeff (Faltings.PowerSeries.dividedDerivative K i _)`.

The places of `K` are `InfinitePlace K ⊕ FinitePlace K`, with Bombieri's normalised absolute
values `|·|_v` written out as in `Faltings.NumberField.iSup_normalizedAbs_sum_le`, and `∑_v` is a
`finsum`. A family `{i_λ}` with `∑ i_λ = i*` is a `Nat.Partition i*`; parts `i_λ = 0` contribute
`max_ν log |ξ_{ν j_v}(z)|_v = 0` (attained at `ν = j_v`), so omitting them changes nothing.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, proof of Lemma 6,
  p. 628, with the Errata-Corrige (1991)
-/

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open _root_.NumberField Module

universe u

namespace Faltings.BombieriSiegel

open Faltings.NumberField (normalizedAbs normalizedAbs_nonneg normalizedAbs_inl normalizedAbs_inr)

section LocalBound

open Real

variable {K : Type*} [Field K] [NumberField K]

/-- From `D ≤ B ^ l (S / A) ^ (2 l - 1)` with `B ≥ 1`,
`log D ≤ l (2 (log⁺ S + log⁺ A⁻¹) + log B)`. -/
private lemma log_le_of_le_pow_mul_div_pow {D S A B : ℝ} (hD : 0 ≤ D) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hB : 1 ≤ B) {l : ℕ} (hl : 1 ≤ l) (h : D ≤ B ^ l * (S / A) ^ (2 * l - 1)) :
    Real.log D ≤ l * (2 * (log⁺ S + log⁺ A⁻¹) + Real.log B) := by
  have hpos : 0 ≤ log⁺ S + log⁺ A⁻¹ := add_nonneg posLog_nonneg posLog_nonneg
  have hlogB := Real.log_nonneg hB
  rcases hD.eq_or_lt with rfl | hD
  · rw [Real.log_zero]; positivity
  have hSA : 0 < S / A := (div_nonneg hS hA).lt_of_ne fun h0 => by
    rw [← h0, zero_pow (by omega), mul_zero] at h
    exact hD.not_ge h
  obtain ⟨hS', hA'⟩ := (div_pos_iff.1 hSA).resolve_right fun h => hS.not_gt h.1
  have h1 := Real.log_le_log hD h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div hS'.ne' hA'.ne', Nat.cast_sub (by omega)] at h1
  have h2 : Real.log S - Real.log A ≤ log⁺ S + log⁺ A⁻¹ := by
    have h3 : Real.log A⁻¹ ≤ log⁺ A⁻¹ := le_max_right _ _
    have h4 : Real.log S ≤ log⁺ S := le_max_right _ _
    rw [Real.log_inv] at h3
    linarith
  push_cast at h1
  nlinarith [mul_le_mul_of_nonneg_left h2
    (by linarith [(Nat.one_le_cast (α := ℝ)).2 hl] : (0 : ℝ) ≤ 2 * l - 1)]

end LocalBound

section LocalBound2

open Real _root_.PowerSeries

variable {K : Type*} [Field K] [NumberField K]

private lemma iSup_rpow_eq {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {e : ℝ}
    (he : 0 < e) : (⨆ i, f i ^ e) = (⨆ i, f i) ^ e := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Real.zero_rpow he.ne']
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := f)
  have hmax : ∀ i, f i ≤ f i₀ := fun i => hi₀ ▸ Finite.le_ciSup_of_le i le_rfl
  rw [← hi₀]
  exact le_antisymm (ciSup_le fun i => Real.rpow_le_rpow (hf i) (hmax i) he.le)
    (Finite.le_ciSup_of_le i₀ le_rfl)

/-- For `p ∈ K[X, Y]` with `deg_X p ≥ 1`, discriminant non-vanishing at `0`, and a power series
root `ξ` with `|ξ(0)|_v ≤ 1`, the divided derivatives of `ξ` at `0` satisfy
`log |∂_l ξ(0)|_v ≤ l (2 (log⁺ |p|_v + log⁺ |a⁻¹|_v) + 7 κ_v log (2 deg p))`, where
`a = p_X(ξ(0), 0)`. -/
private lemma log_absV_dividedDerivative_le (p : MvPolynomial (Fin 2) K)
    (hdeg : 1 ≤ p.degreeOf 0)
    (hD : MvPolynomial.eval 0
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K 1 p)
        (Polynomial.derivative (MvPolynomial.finSuccEquiv K 1 p))
        (p.degreeOf 0) (p.degreeOf 0 - 1)) ≠ 0)
    (ξ : K⟦X⟧) (hp : MvPolynomial.aeval ![ξ, (X : K⟦X⟧)] p = 0)
    (v : InfinitePlace K ⊕ FinitePlace K) (hξ : normalizedAbs v (constantCoeff ξ) ≤ 1) {l : ℕ}
    (hl : 1 ≤ l) :
    Real.log (normalizedAbs v (constantCoeff (Faltings.PowerSeries.dividedDerivative K l ξ))) ≤
      l * (2 * (log⁺ (⨆ m : p.support, normalizedAbs v (p.coeff m)) +
        log⁺ (normalizedAbs v
          (MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p))⁻¹)) +
        7 * Faltings.NumberField.localWeight K v * Real.log (2 * p.totalDegree)) := by
  have hN : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have htd : 1 ≤ p.totalDegree := hdeg.trans (MvPolynomial.degreeOf_le_totalDegree p 0)
  rw [map_inv₀]
  rcases v with w | w
  · have hκ : 0 < (w.mult : ℝ) / finrank ℚ K :=
      div_pos (by exact_mod_cast InfinitePlace.mult_pos) hN
    have hD' : let q := MvPolynomial.finSuccEquiv K 1 p
        MvPolynomial.eval 0 (q.resultant (Polynomial.derivative q) q.natDegree
          (q.natDegree - 1)) ≠ 0 := by
      simpa only [MvPolynomial.natDegree_finSuccEquiv] using hD
    have h := Faltings.PowerSeries.normalizedAbs_constantCoeff_dividedDerivative_le_of_isInfinite
      w p hdeg hD' ξ hp hl hξ
    have h2D : w ((2 * p.totalDegree : ℕ) : K) ^ ((w.mult : ℝ) / finrank ℚ K) =
        ((2 * p.totalDegree : ℕ) : ℝ) ^ ((w.mult : ℝ) / finrank ℚ K) := by
      rw [InfinitePlace.map_natCast]
    have hB : 1 ≤ (w ((2 * p.totalDegree : ℕ) : K) ^ ((w.mult : ℝ) / finrank ℚ K)) ^ 7 := by
      rw [h2D]
      exact one_le_pow₀ (Real.one_le_rpow (by norm_cast; omega) hκ.le)
    have h' := log_le_of_le_pow_mul_div_pow (normalizedAbs_nonneg (.inl w) _)
      (Real.iSup_nonneg fun _ => normalizedAbs_nonneg (.inl w) _)
      (normalizedAbs_nonneg (.inl w) _) hB hl
      (by
        refine h.trans_eq ?_
        simp only [normalizedAbs_inl]
        push_cast
        rw [← pow_mul, mul_comm 7 l])
    refine h'.trans_eq ?_
    rw [h2D, Real.log_pow, Real.log_rpow (by norm_cast; omega)]
    simp only [Faltings.NumberField.localWeight, normalizedAbs_inl]
    push_cast
    ring
  · have he : 0 < (1 : ℝ) / finrank ℚ K := by positivity
    have hξ' : w (constantCoeff ξ) ≤ 1 := by
      by_contra hlt
      push Not at hlt
      exact absurd hξ (not_le.2 (Real.one_lt_rpow hlt he))
    have h := Faltings.PowerSeries.abv_constantCoeff_dividedDerivative_le p hdeg ξ hp hD w.1
      (fun x y => w.add_le x y) hξ' hl
    set a := MvPolynomial.eval ![constantCoeff ξ, 0] (MvPolynomial.pderiv 0 p)
    set D := constantCoeff (Faltings.PowerSeries.dividedDerivative K l ξ)
    change w D ≤ ((⨆ m : p.support, w (p.coeff m)) / w a) ^ (2 * l - 1) at h
    have hS0 : 0 ≤ ⨆ m : p.support, w (p.coeff m) := Real.iSup_nonneg fun _ => apply_nonneg _ _
    have hrp := Real.rpow_le_rpow (apply_nonneg _ _) h he.le
    have h' := log_le_of_le_pow_mul_div_pow (normalizedAbs_nonneg (.inr w) D)
      (Real.iSup_nonneg fun _ => normalizedAbs_nonneg (.inr w) _)
      (normalizedAbs_nonneg (.inr w) a) le_rfl hl
      (S := ⨆ m : p.support, normalizedAbs (.inr w) (p.coeff m))
      (by
        refine hrp.trans_eq ?_
        simp only [normalizedAbs_inr, one_pow, one_mul]
        rw [iSup_rpow_eq (fun m : p.support => w (p.coeff m)) (fun _ => apply_nonneg _ _) he,
          ← Real.div_rpow hS0 (apply_nonneg _ _), ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul (div_nonneg hS0 (apply_nonneg _ _)),
          ← Real.rpow_mul (div_nonneg hS0 (apply_nonneg _ _)), mul_comm])
    refine h'.trans_eq ?_
    simp [Faltings.NumberField.localWeight]

end LocalBound2

/-! ### The shifted plane relation `p(X, ς) = g(X, ς + c)` -/

section Shift

open Polynomial

variable {K : Type*} [Field K]

/-- The substitution `Y ↦ X₁ + c` from `K[Y]` to `K[X₀, X₁]`. -/
private noncomputable abbrev shiftInner (c : K) : K[X] →+* MvPolynomial (Fin 2) K :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 1 + MvPolynomial.C c)

/-- The shifted plane relation `p(X₀, X₁) = g(X₀, X₁ + c)` of `g ∈ K[Y][X]`. -/
private noncomputable def shiftPoly (G : K[X][X]) (c : K) : MvPolynomial (Fin 2) K :=
  G.eval₂ (shiftInner c) (MvPolynomial.X 0)

/-- The substitution `Y ↦ X₀ + c` from `K[Y]` to `K[X₀] = MvPolynomial (Fin 1) K`. -/
private noncomputable abbrev shiftOne (c : K) : K[X] →+* MvPolynomial (Fin 1) K :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 0 + MvPolynomial.C c)

private lemma shiftOne_injective (c : K) : Function.Injective (shiftOne c) := by
  let ρ : MvPolynomial (Fin 1) K →+* K[X] :=
    MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X - Polynomial.C c
  have h : ρ.comp (shiftOne c) = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [ρ]
    · simp [ρ]
  intro a b hab
  have := congrArg ρ hab
  rwa [← RingHom.comp_apply, h, ← RingHom.comp_apply, h] at this

private lemma finSuccEquiv_shiftPoly (G : K[X][X]) (c : K) :
    MvPolynomial.finSuccEquiv K 1 (shiftPoly G c) = G.map (shiftOne c) := by
  have := Polynomial.hom_eval₂ G (shiftInner c)
    ((MvPolynomial.finSuccEquiv K 1 :
      MvPolynomial (Fin (1 + 1)) K →+* (MvPolynomial (Fin 1) K)[X])) (MvPolynomial.X 0)
  rw [RingHom.coe_coe] at this
  rw [shiftPoly, Polynomial.map, this]
  congr 1
  · refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
      simp [Polynomial.algebraMap_apply]
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, RingHom.coe_coe]
      rw [map_add, show (1 : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ,
        ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
      simp [Polynomial.algebraMap_apply]
  · simp [MvPolynomial.finSuccEquiv_X_zero]

private lemma degreeOf_shiftPoly (G : K[X][X]) (c : K) :
    (shiftPoly G c).degreeOf 0 = G.natDegree := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, finSuccEquiv_shiftPoly,
    natDegree_map_eq_of_injective (shiftOne_injective c)]

private lemma eval_zero_shiftOne (c : K) (D : K[X]) :
    MvPolynomial.eval 0 (shiftOne c D) = D.eval c := by
  simp only [coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂]
  have : (MvPolynomial.eval (0 : Fin 1 → K)).comp MvPolynomial.C = RingHom.id K := by
    ext; simp
  rw [this]
  simp only [map_add, MvPolynomial.eval_X, MvPolynomial.eval_C, Pi.zero_apply, zero_add]
  rfl

/-- The discriminant of the shifted relation at `ς = 0` is that of `g` at `Y = c`. -/
private lemma eval_resultant_shiftPoly (G : K[X][X]) (c : K) :
    MvPolynomial.eval 0
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K 1 (shiftPoly G c))
        (Polynomial.derivative (MvPolynomial.finSuccEquiv K 1 (shiftPoly G c)))
        ((shiftPoly G c).degreeOf 0) ((shiftPoly G c).degreeOf 0 - 1)) =
      (G.resultant (derivative G) G.natDegree (G.natDegree - 1)).eval c := by
  rw [degreeOf_shiftPoly, finSuccEquiv_shiftPoly, derivative_map, resultant_map_map,
    eval_zero_shiftOne]

/-- Evaluation of the shifted relation: `p(u, w) = g(u, w + c)`. -/
private lemma aeval_shiftPoly {A : Type*} [CommRing A] [Algebra K A] (G : K[X][X]) (c : K)
    (u w : A) :
    MvPolynomial.aeval ![u, w] (shiftPoly G c) =
      G.eval₂ (eval₂RingHom (algebraMap K A) (w + algebraMap K A c)) u := by
  rw [shiftPoly, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂]
  congr 1
  · refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  · simp

private lemma eval₂_evalRingHom_eq (G : K[X][X]) (c a : K) :
    G.eval₂ (evalRingHom c) a = G.evalEval c a := by
  rw [evalEval, ← coe_evalRingHom c, Polynomial.eval, Polynomial.hom_eval₂]
  simp

/-- The partial derivative in `X` of the shifted relation, at `(a, b)`, is `g_X(a, b + c)`. -/
private lemma eval_pderiv_shiftPoly (G : K[X][X]) (c a b : K) :
    MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 0 (shiftPoly G c)) =
      (derivative G).evalEval (b + c) a := by
  have h1 : (![a, b] : Fin 2 → K) = Fin.cons a ![b] := by ext i; fin_cases i <;> rfl
  have h2 : (MvPolynomial.eval ![b]).comp (shiftOne c) = evalRingHom (b + c) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp
  rw [h1, MvPolynomial.eval_eq_eval_mv_eval', finSuccEquiv_pderiv_zero, finSuccEquiv_shiftPoly,
    derivative_map, Polynomial.map_map, h2, Polynomial.eval_map, eval₂_evalRingHom_eq]

/-- The index set `{(i, b, e) : X^i Y^b ∈ g, e ≤ b}` of the binomial expansion of
`g(X, Y + c)`. -/
private noncomputable def shiftIndex (G : K[X][X]) : Finset ((_ : ℕ) × (_ : ℕ) × ℕ) :=
  G.support.sigma fun i => (G.coeff i).support.sigma fun b => Finset.range (b + 1)

/-- The term `g_{ib} (b choose e) c^{b - e} X^i Y^e` of the binomial expansion. -/
private noncomputable def shiftTerm (G : K[X][X]) (c : K) (t : (_ : ℕ) × (_ : ℕ) × ℕ) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.monomial (Finsupp.single 0 t.1 + Finsupp.single 1 t.2.2)
    ((G.coeff t.1).coeff t.2.1 * (t.2.1.choose t.2.2 : K) * c ^ (t.2.1 - t.2.2))

private lemma shiftPoly_eq_sum (G : K[X][X]) (c : K) :
    shiftPoly G c = ∑ t ∈ shiftIndex G, shiftTerm G c t := by
  rw [shiftIndex, Finset.sum_sigma, shiftPoly, eval₂_eq_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_sigma]
  simp only [coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hm : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 e).prod
      (fun n k => (MvPolynomial.X n : MvPolynomial (Fin 2) K) ^ k) =
      MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ e := by
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  rw [shiftTerm, MvPolynomial.monomial_eq, hm]
  simp only [map_mul, map_pow, map_natCast]
  ring

/-- The degree bound `deg_X g + max_i deg_Y g_i`. -/
private noncomputable abbrev degBound (G : K[X][X]) : ℕ :=
  G.natDegree + G.support.sup fun i => (G.coeff i).natDegree

private lemma degBound_map {k K : Type*} [Field k] [Field K] (φ : k →+* K) (G : k[X][X]) :
    degBound (G.map (mapRingHom φ)) = degBound G := by
  have hinj : Function.Injective (mapRingHom φ) := Polynomial.map_injective _ φ.injective
  simp only [degBound, natDegree_map_eq_of_injective hinj, support_map_of_injective _ hinj,
    Polynomial.coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective φ.injective]

/-- An index `(i, b, e)` of the binomial expansion has `i + b ≤ degBound g` and `e ≤ b`. -/
private lemma add_le_degBound_of_mem_shiftIndex {G : K[X][X]} {t : (_ : ℕ) × (_ : ℕ) × ℕ}
    (ht : t ∈ shiftIndex G) : t.1 + t.2.1 ≤ degBound G ∧ t.2.2 ≤ t.2.1 := by
  simp only [shiftIndex, Finset.mem_sigma, Finset.mem_range] at ht
  obtain ⟨hi, hb, he⟩ := ht
  exact ⟨add_le_add (le_natDegree_of_mem_supp _ hi) ((le_natDegree_of_mem_supp _ hb).trans
    (Finset.le_sup (f := fun i => (G.coeff i).natDegree) hi)), Nat.lt_succ_iff.1 he⟩

private lemma totalDegree_shiftPoly_le (G : K[X][X]) (c : K) :
    (shiftPoly G c).totalDegree ≤ degBound G := by
  rw [shiftPoly_eq_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun t ht => ?_)
  obtain ⟨h1, h2⟩ := add_le_degBound_of_mem_shiftIndex ht
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  have h4 : ((Finsupp.single (0 : Fin 2) t.1 + Finsupp.single 1 t.2.2).sum fun _ => id) =
      t.1 + t.2.2 := by
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl,
      Finsupp.sum_single_index rfl]
    rfl
  rw [h4]
  omega

end Shift

section ShiftSize

open Polynomial Real

variable {K : Type*} [Field K] [NumberField K]

private lemma normalizedAbs_neg (v : InfinitePlace K ⊕ FinitePlace K) (x : K) :
    normalizedAbs v (-x) = normalizedAbs v x := by
  rcases v with w | w
  · rw [normalizedAbs_inl, normalizedAbs_inl]
    exact congrArg (· ^ _) (AbsoluteValue.map_neg w.1 x)
  · rw [normalizedAbs_inr, normalizedAbs_inr]
    exact congrArg (· ^ _) (AbsoluteValue.map_neg w.1 x)

private lemma normalizedAbs_natCast_le (v : InfinitePlace K ⊕ FinitePlace K) {n : ℕ} {B : ℝ}
    (hB : (n : ℝ) ≤ B) : normalizedAbs v (n : K) ≤ B ^ Faltings.NumberField.localWeight K v := by
  rcases v with w | w
  · simp only [normalizedAbs_inl, Faltings.NumberField.localWeight, InfinitePlace.map_natCast]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hB (by positivity)
  · simp only [normalizedAbs_inr, Faltings.NumberField.localWeight, Real.rpow_zero]
    have h1 : w (n : K) ≤ 1 :=
      IsNonarchimedean.apply_natCast_le_one (by simp) (map_one w) (fun x y => w.add_le x y)
    exact Real.rpow_le_one (apply_nonneg _ _) h1 (by positivity)

private lemma localWeight_nonneg (v : InfinitePlace K ⊕ FinitePlace K) :
    0 ≤ Faltings.NumberField.localWeight K v := by
  rcases v with w | w <;> simp only [Faltings.NumberField.localWeight] <;> positivity

/-- `|g|_v`, the largest `|g_{ib}|_v` over `i, b < N`. -/
private noncomputable abbrev polySize (v : InfinitePlace K ⊕ FinitePlace K) (G : K[X][X])
    (N : ℕ) : ℝ :=
  ⨆ t : Fin N × Fin N, normalizedAbs v ((G.coeff t.1).coeff t.2)

private lemma iSup_absV_monomial_le (v : InfinitePlace K ⊕ FinitePlace K)
    (m : Fin 2 →₀ ℕ) (a : K) :
    (⨆ c : (MvPolynomial.monomial m a).support,
      normalizedAbs v ((MvPolynomial.monomial m a).coeff c)) ≤ normalizedAbs v a := by
  refine Real.iSup_le (fun ⟨c, hc⟩ => ?_) (normalizedAbs_nonneg _ _)
  have h := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hc)
  simp only [MvPolynomial.coeff_monomial, h, ite_true, le_refl]

omit [NumberField K] in
private lemma coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 2) K) :
    AddMonoidAlgebra.coeff (∑ t ∈ s, f t) = ∑ t ∈ s, AddMonoidAlgebra.coeff (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddMonoidAlgebra.coeff_add, ih]

omit [NumberField K] in
private lemma card_shiftIndex_le (G : K[X][X]) {N : ℕ} (hN : degBound G < N) :
    (shiftIndex G).card ≤ N ^ 3 := by
  classical
  have hsub : shiftIndex G ⊆ (Finset.range N).sigma fun _ =>
      (Finset.range N).sigma fun _ => Finset.range N := by
    intro t ht
    obtain ⟨h1, h2⟩ := add_le_degBound_of_mem_shiftIndex ht
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  refine (Finset.card_le_card hsub).trans ?_
  simp [Finset.card_sigma, pow_succ, mul_assoc]

/-- **The size of the shifted relation at one place**:
`|p|_v ≤ (N³ 2^N)^{κ_v} |g|_v max(1, |c|_v)^N` for `N` above the degrees of `g`. -/
private lemma iSup_absV_shiftPoly_le (v : InfinitePlace K ⊕ FinitePlace K) (G : K[X][X])
    (c : K) {N : ℕ} (hN : degBound G < N) :
    (⨆ m : (shiftPoly G c).support, normalizedAbs v ((shiftPoly G c).coeff m)) ≤
      ((N ^ 3 * 2 ^ N : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v *
        polySize v G N * max 1 (normalizedAbs v c) ^ N := by
  have hκ := localWeight_nonneg v
  have hS0 : 0 ≤ polySize v G N := Real.iSup_nonneg fun _ => normalizedAbs_nonneg _ _
  rcases (shiftIndex G).eq_empty_or_nonempty with hs | hs
  · have : shiftPoly G c = 0 := by rw [shiftPoly_eq_sum, hs, Finset.sum_empty]
    have : IsEmpty (shiftPoly G c).support :=
      ⟨fun ⟨m, hm⟩ => by rw [this] at hm; simp at hm⟩
    rw [Real.iSup_of_isEmpty]
    positivity
  have hterm : ∀ t ∈ shiftIndex G,
      normalizedAbs v ((G.coeff t.1).coeff t.2.1 * (t.2.1.choose t.2.2 : K) * c ^ (t.2.1 - t.2.2)) ≤
        polySize v G N * ((2 ^ N : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v *
          max 1 (normalizedAbs v c) ^ N := by
    intro t ht
    obtain ⟨hdeg, he⟩ := add_le_degBound_of_mem_shiftIndex ht
    have hbN : t.2.1 < N := by omega
    have hiN : t.1 < N := by omega
    rw [map_mul, map_mul, map_pow]
    have h1 : normalizedAbs v ((G.coeff t.1).coeff t.2.1) ≤ polySize v G N :=
      le_ciSup (f := fun t : Fin N × Fin N => normalizedAbs v ((G.coeff t.1).coeff t.2))
        (Set.finite_range _).bddAbove (⟨t.1, hiN⟩, ⟨t.2.1, hbN⟩)
    have h2 : normalizedAbs v (t.2.1.choose t.2.2 : K) ≤
        ((2 ^ N : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v := by
      refine normalizedAbs_natCast_le v ?_
      exact_mod_cast (Nat.choose_le_two_pow _ _).trans
        (Nat.pow_le_pow_right (by norm_num) hbN.le)
    have h3 : normalizedAbs v c ^ (t.2.1 - t.2.2) ≤ max 1 (normalizedAbs v c) ^ N :=
      (pow_le_pow_left₀ (normalizedAbs_nonneg _ _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    have h4 : 0 ≤ normalizedAbs v (t.2.1.choose t.2.2 : K) := normalizedAbs_nonneg _ _
    calc _ ≤ polySize v G N * ((2 ^ N : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v *
          normalizedAbs v c ^ (t.2.1 - t.2.2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h4 hS0)
            (pow_nonneg (normalizedAbs_nonneg _ _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hcard := Faltings.NumberField.iSup_normalizedAbs_sum_le (K := K) v hs
    (fun t => AddMonoidAlgebra.coeff (shiftTerm G c t))
  simp only at hcard
  have hsum : AddMonoidAlgebra.coeff (shiftPoly G c) =
      ∑ t ∈ shiftIndex G, AddMonoidAlgebra.coeff (shiftTerm G c t) := by
    rw [shiftPoly_eq_sum, coeff_finset_sum]
  have hcardN : ((shiftIndex G).card : ℝ) ^ Faltings.NumberField.localWeight K v ≤
      ((N ^ 3 : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast card_shiftIndex_le G hN) hκ
  calc (⨆ m : (shiftPoly G c).support, normalizedAbs v ((shiftPoly G c).coeff m))
      ≤ ((shiftIndex G).card : ℝ) ^ Faltings.NumberField.localWeight K v *
          ⨆ t : shiftIndex G, ⨆ m : (shiftTerm G c t).support,
            normalizedAbs v ((shiftTerm G c t).coeff m) := by
        change (⨆ m : (AddMonoidAlgebra.coeff (shiftPoly G c)).support,
          normalizedAbs v (AddMonoidAlgebra.coeff (shiftPoly G c) m)) ≤ _
        rw [hsum]; exact hcard
    _ ≤ ((N ^ 3 : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v *
          (polySize v G N * ((2 ^ N : ℕ) : ℝ) ^ Faltings.NumberField.localWeight K v *
            max 1 (normalizedAbs v c) ^ N) := by
        refine mul_le_mul hcardN (Real.iSup_le (fun t => ?_) (by positivity))
          (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => normalizedAbs_nonneg _ _)
          (by positivity)
        exact (iSup_absV_monomial_le v _ _).trans (hterm t.1 t.2)
    _ = _ := by
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
        ring

end ShiftSize

/-! ### Sums over places and heights -/

section Heights

open Real

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
private lemma iSup_pos_of_ne_zero {ι : Type*} [Finite ι] (v : AbsoluteValue K ℝ) {x : ι → K}
    (hx : x ≠ 0) : 0 < ⨆ i, v (x i) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  exact (v.pos hi₀).trans_le (Finite.le_ciSup_of_le i₀ le_rfl)

/-- A finitely supported sum over a sum type with finite left summand. -/
private lemma finsum_sum_of_fintype_left {α β M : Type*} [AddCommMonoid M] [Fintype α]
    (f : α ⊕ β → M) (hf : (Function.support fun b => f (.inr b)).Finite) :
    ∑ᶠ x, f x = (∑ a, f (.inl a)) + ∑ᶠ b, f (.inr b) := by
  classical
  let t := hf.toFinset
  have hsub : Function.support f ⊆ (((Finset.univ : Finset α).disjSum t) : Finset _) := by
    rintro (a | b) h
    · simp
    · simpa [t] using h
  rw [finsum_eq_sum_of_support_subset f hsub, Finset.sum_disjSum,
    finsum_eq_sum_of_support_subset (s := t) _ (by simp [t])]

/-- **Heights as sums of normalised local terms**: for a nonzero tuple `x`,
`∑_v log max_i |x_i|_v = h(x) / [K : ℚ]`. -/
private lemma finsum_log_iSup_absV {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    ∑ᶠ v, Real.log (⨆ i, normalizedAbs v (x i)) = Height.logHeight x / finrank ℚ K := by
  have hN : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hinf : ∀ w : InfinitePlace K, Real.log (⨆ i, normalizedAbs (.inl w) (x i)) =
      (w.mult / finrank ℚ K) * Real.log (⨆ i, w (x i)) := fun w => by
    simp only [normalizedAbs_inl]
    rw [iSup_rpow_eq _ (fun _ => apply_nonneg _ _)
      (div_pos (by exact_mod_cast InfinitePlace.mult_pos) hN)]
    exact Real.log_rpow (iSup_pos_of_ne_zero w.1 hx) _
  have hfin : ∀ w : FinitePlace K, Real.log (⨆ i, normalizedAbs (.inr w) (x i)) =
      (1 / finrank ℚ K) * Real.log (⨆ i, w (x i)) := fun w => by
    simp only [normalizedAbs_inr]
    rw [iSup_rpow_eq _ (fun _ => apply_nonneg _ _) (by positivity)]
    exact Real.log_rpow (iSup_pos_of_ne_zero w.1 hx) _
  have hsupp := BombieriVojta.HeightLowerBound.hasFiniteSupport_log_iSup hx
  rw [finsum_sum_of_fintype_left _ (by
    refine hsupp.subset fun w hw => ?_
    simp only [Function.mem_support, hfin] at hw ⊢
    exact right_ne_zero_of_mul hw)]
  simp only [hinf, hfin]
  rw [← mul_finsum' _ _ hsupp, BombieriVojta.HeightLowerBound.logHeight_eq_sum_log_iSup hx,
    add_div, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · ring

omit [NumberField K] in
/-- `max_o |(1, y)_o|_v = max(1, max_i |y_i|_v)`. -/
private lemma iSup_elim_one {ι : Type*} [Finite ι] (v : K → ℝ)
    (hv1 : v 1 = 1) (y : ι → K) :
    (⨆ o : Option ι, v (o.elim 1 y)) = max 1 (⨆ i, v (y i)) := by
  refine le_antisymm (ciSup_le fun o => ?_) (max_le ?_ ?_)
  · rcases o with _ | i
    · simp [hv1]
    · change v (y i) ≤ _
      exact (Finite.le_ciSup_of_le (f := fun i => v (y i)) i le_rfl).trans (le_max_right _ _)
  · exact Finite.le_ciSup_of_le (f := fun o : Option ι => v (o.elim 1 y)) none (by simp [hv1])
  · rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]
      exact Finite.le_ciSup_of_le (f := fun o : Option ι => v (o.elim 1 y)) none (by simp [hv1])
    · exact ciSup_le fun i =>
        Finite.le_ciSup_of_le (f := fun o : Option ι => v (o.elim 1 y)) (some i) le_rfl

/-- **The height of a scalar as a sum of normalised local terms**:
`∑_v log⁺ |a|_v = h(a) / [K : ℚ]`. -/
private lemma finsum_posLog_absV (a : K) :
    ∑ᶠ v, log⁺ (normalizedAbs v a) = Height.logHeight₁ a / finrank ℚ K := by
  have h := finsum_log_iSup_absV (x := ![a, 1]) (by simp [funext_iff])
  rw [Height.logHeight₁_eq_logHeight, ← h]
  refine finsum_congr fun v => ?_
  have : (⨆ i, normalizedAbs v (![a, 1] i)) = max 1 (normalizedAbs v a) := by
    refine le_antisymm (ciSup_le fun i => ?_) (max_le ?_ (Finite.le_ciSup_of_le 0 le_rfl))
    · fin_cases i
      · exact le_max_right _ _
      · simp
    · exact Finite.le_ciSup_of_le 1 (by simp)
  rw [this, Real.posLog_eq_log_max_one (normalizedAbs_nonneg _ _)]

end Heights

section FieldIndependence

open Real

/-- Bombieri's sum of local heights, written with `normalizedAbs`. -/
private lemma sumLocalHeight_eq_finsum_absV {K : Type*} [Field K] [NumberField K] {ι : Type*}
    [Finite ι] (x : ι → K) :
    Faltings.sumLocalHeight x = ∑ᶠ v, Real.log (⨆ i, normalizedAbs v (x i)) := by
  unfold Faltings.sumLocalHeight
  rw [← finsum_comp_equiv (Equiv.sumComm (InfinitePlace K) (FinitePlace K))]
  refine finsum_congr fun v => ?_
  rcases v with w | w
  · simp only [Equiv.sumComm_apply, Sum.swap_inl, Faltings.NumberFieldPlace.localHeight,
      Faltings.NumberFieldPlace.vectorAbv, Faltings.NumberFieldPlace.normalizedAbv_inr,
      normalizedAbs_inl]
    congr 1
    refine iSup_congr fun i => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg _ _), div_eq_mul_inv]
  · simp only [Equiv.sumComm_apply, Sum.swap_inr, Faltings.NumberFieldPlace.localHeight,
      Faltings.NumberFieldPlace.vectorAbv, Faltings.NumberFieldPlace.normalizedAbv_inl,
      normalizedAbs_inr, one_div]

/-- **Field independence of the normalised height**: for number fields `k ⊆ K` and a nonzero
tuple `x` over `k`, `h_K(x) / [K : ℚ] = h_k(x) / [k : ℚ]`. -/
private lemma logHeight_algebraMap_div {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] {ι : Type*} [Finite ι] {x : ι → k} (hx : x ≠ 0) :
    Height.logHeight (algebraMap k K ∘ x) / finrank ℚ K =
      Height.logHeight x / finrank ℚ k := by
  have hxK : algebraMap k K ∘ x ≠ 0 := fun h =>
    hx (funext fun i => (algebraMap k K).injective (by simpa using congrFun h i))
  rw [← finsum_log_iSup_absV hxK, ← finsum_log_iSup_absV hx, ← sumLocalHeight_eq_finsum_absV,
    ← sumLocalHeight_eq_finsum_absV, Faltings.sumLocalHeight_algebraMap hx]

/-- The local term `log⁺ max_i |y_i|_v` summed over the places: the height of `(1, y)`. -/
private lemma finsum_posLog_iSup_absV {K : Type*} [Field K] [NumberField K] {ι : Type*}
    [Finite ι] (y : ι → K) :
    ∑ᶠ v, log⁺ (⨆ i, normalizedAbs v (y i)) =
      Height.logHeight (fun o : Option ι => o.elim 1 y) / finrank ℚ K := by
  have hne : (fun o : Option ι => o.elim 1 y) ≠ 0 := fun h => by
    simpa using congrFun h none
  rw [← finsum_log_iSup_absV hne]
  refine finsum_congr fun v => ?_
  rw [iSup_elim_one (normalizedAbs v) (map_one _),
    Real.posLog_eq_log_max_one (Real.iSup_nonneg fun _ => normalizedAbs_nonneg _ _)]

end FieldIndependence

section PolyHeights

open Polynomial Real

/-- The shifted relation commutes with extension of scalars. -/
private lemma shiftPoly_map {k K : Type*} [Field k] [Field K] (φ : k →+* K) (G : k[X][X])
    (c : k) :
    shiftPoly (G.map (mapRingHom φ)) (φ c) = MvPolynomial.map φ (shiftPoly G c) := by
  have : (MvPolynomial.map φ).comp (eval₂RingHom (shiftInner c) (MvPolynomial.X 0)) =
      (eval₂RingHom (shiftInner (φ c)) (MvPolynomial.X 0)).comp (mapRingHom (mapRingHom φ)) := by
    refine Polynomial.ringHom_ext (fun g => ?_) ?_
    · have h : (MvPolynomial.map φ).comp (shiftInner c) =
          (shiftInner (φ c)).comp (mapRingHom φ) := by
        refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp
      simpa using congrArg (fun f => f g) h
    · simp
  exact (congrArg (fun f => f G) this).symm

variable {K : Type*} [Field K] [NumberField K]

/-- The height of `(1, y)` as a sum of `log⁺` of local sizes. -/
private lemma logHeight_elim_one {ι : Type*} [Finite ι] (y : ι → K) :
    Height.logHeight (fun o : Option ι => o.elim 1 y) =
      (∑ w : InfinitePlace K, w.mult * log⁺ (⨆ i, w (y i))) +
        ∑ᶠ w : FinitePlace K, log⁺ (⨆ i, w (y i)) := by
  have hne : (fun o : Option ι => o.elim 1 y) ≠ 0 := fun h => by
    simpa using congrFun h none
  rw [BombieriVojta.HeightLowerBound.logHeight_eq_sum_log_iSup hne]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [iSup_elim_one (⇑w) (map_one w),
      Real.posLog_eq_log_max_one (Real.iSup_nonneg fun _ => apply_nonneg _ _)]
  · refine finsum_congr fun w => ?_
    rw [iSup_elim_one (⇑w) (map_one w),
      Real.posLog_eq_log_max_one (Real.iSup_nonneg fun _ => apply_nonneg _ _)]

/-- The affine height as a projective height: `h_aff(f) = h(1, f) / [K : ℚ]`. -/
private lemma affineLogHeight_eq_logHeight {α : Type*} (f : α →₀ K) :
    Faltings.affineLogHeight f =
      Height.logHeight (fun o : Option f.support => o.elim 1 fun c => f c) / finrank ℚ K := by
  rw [logHeight_elim_one, Faltings.affineLogHeight]

/-- **Field independence of the affine height** of a polynomial. -/
private lemma affineLogHeight_map {k : Type*} [Field k] [NumberField k] [Algebra k K]
    {σ : Type*} (Q : MvPolynomial σ k) :
    Faltings.affineLogHeight (AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap k K) Q)) =
      Faltings.affineLogHeight (AddMonoidAlgebra.coeff Q) := by
  have hsupp := MvPolynomial.support_map_of_injective Q (algebraMap k K).injective
  rw [affineLogHeight_eq_logHeight, affineLogHeight_eq_logHeight]
  have hne : (fun o : Option (AddMonoidAlgebra.coeff Q).support =>
      o.elim 1 fun c => (AddMonoidAlgebra.coeff Q) c) ≠ 0 := fun h => by
    simpa using congrFun h none
  rw [← logHeight_algebraMap_div (K := K) hne]
  congr 1
  have hcomp : (algebraMap k K ∘ fun o : Option (AddMonoidAlgebra.coeff Q).support =>
      o.elim 1 fun c => (AddMonoidAlgebra.coeff Q) c) =
      fun o => o.elim 1 fun c => algebraMap k K ((AddMonoidAlgebra.coeff Q) c) := by
    funext o; rcases o with _ | c <;> simp
  rw [hcomp, logHeight_elim_one, logHeight_elim_one]
  have key : ∀ g : K → ℝ, (⨆ c : (AddMonoidAlgebra.coeff
      (MvPolynomial.map (algebraMap k K) Q)).support,
        g ((AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap k K) Q)) c)) =
      ⨆ c : (AddMonoidAlgebra.coeff Q).support,
        g (algebraMap k K ((AddMonoidAlgebra.coeff Q) c)) := by
    intro g
    change (⨆ c : (MvPolynomial.map (algebraMap k K) Q).support,
        g ((MvPolynomial.map (algebraMap k K) Q).coeff c)) =
      ⨆ c : Q.support, g (algebraMap k K (Q.coeff c))
    simp only [MvPolynomial.coeff_map]
    rw [hsupp]
  simp only [key]

end PolyHeights

section PairBound

open Polynomial Real Function

variable {K : Type*} [Field K] [NumberField K]

/-- `log⁺ max_i |y_i|_v` vanishes at all but finitely many places. -/
private lemma hasFiniteSupport_posLog_iSup_absV {ι : Type*} [Finite ι] (y : ι → K) :
    HasFiniteSupport fun v => log⁺ (⨆ i, normalizedAbs v (y i)) := by
  classical
  have hfin : ∀ i : {i // y i ≠ 0}, (mulSupport fun w : FinitePlace K => w (y i)).Finite :=
    fun i => FinitePlace.hasFiniteMulSupport i.2
  let S : Set (FinitePlace K) := ⋃ i : {i // y i ≠ 0}, mulSupport fun w : FinitePlace K => w (y i)
  have hS : S.Finite := Set.finite_iUnion hfin
  refine ((Set.finite_univ (α := InfinitePlace K)).image Sum.inl |>.union
    (hS.image Sum.inr)).subset ?_
  rintro (w | w) hw
  · exact Or.inl ⟨w, trivial, rfl⟩
  · refine Or.inr ⟨w, ?_, rfl⟩
    by_contra hwS
    apply hw
    have h1 : ∀ i, normalizedAbs (.inr w) (y i) ≤ 1 := by
      intro i
      by_cases hi : y i = 0
      · rw [hi, map_zero]
        exact zero_le_one
      · have : w (y i) = 1 := by
          by_contra hne
          exact hwS (Set.mem_iUnion.2 ⟨⟨i, hi⟩, hne⟩)
        simp [this]
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => normalizedAbs_nonneg _ _)]
    exact Real.iSup_le h1 zero_le_one

private lemma hasFiniteSupport_posLog_absV (a : K) :
    HasFiniteSupport fun v => log⁺ (normalizedAbs v a) := by
  simpa using hasFiniteSupport_posLog_iSup_absV (fun _ : Unit => a)

private lemma hasFiniteSupport_localWeight :
    HasFiniteSupport fun v => Faltings.NumberField.localWeight K v := by
  refine ((Set.finite_univ (α := InfinitePlace K)).image Sum.inl).subset ?_
  rintro (w | w) hw
  · exact ⟨w, trivial, rfl⟩
  · simp [Faltings.NumberField.localWeight] at hw

private lemma hasFiniteSupport_mul_localWeight_mul (a b : ℝ) :
    HasFiniteSupport fun v => a * Faltings.NumberField.localWeight K v * b :=
  (hasFiniteSupport_localWeight.subset (support_mul_subset_right (fun _ => a) _)).subset
    (support_mul_subset_left _ fun _ => b)

/-- For `g = g₀` over `k` read over `K` and `c, u ∈ K`,
`∑_v (log⁺ |p|_v + log⁺ |g_X(u, c)⁻¹|_v) ≤ A + B (h(c) + h(u))` with `p(X, ς) = g(X, ς + c)`
and constants `A, B` depending only on `g₀` and `N`. -/
private lemma finsum_posLog_shiftPoly_add_le {k : Type*} [Field k] [NumberField k] [Algebra k K]
    (G₀ : k[X][X]) {N : ℕ} (hN : degBound G₀ < N) (c u : K) :
    let G := G₀.map (mapRingHom (algebraMap k K))
    let Q₀ := MvPolynomial.pderiv 0 (shiftPoly G₀ 0)
    ∑ᶠ v, (log⁺ (⨆ m : (shiftPoly G c).support, normalizedAbs v ((shiftPoly G c).coeff m)) +
        log⁺ (normalizedAbs v ((derivative G).evalEval c u)⁻¹)) ≤
      (Real.log ((N ^ 3 * 2 ^ N : ℕ) : ℝ) +
        Height.logHeight (fun o : Option (Fin N × Fin N) =>
          o.elim 1 fun t => (G₀.coeff t.1).coeff t.2) / finrank ℚ k +
        Faltings.affineLogHeight (AddMonoidAlgebra.coeff Q₀) +
        Real.log (Faltings.MvPolynomial.monomialCount Q₀)) +
      (N + Q₀.degreeOf 0 + Q₀.degreeOf 1) *
        (Height.logHeight₁ c / finrank ℚ K + Height.logHeight₁ u / finrank ℚ K) := by
  intro G Q₀
  have hNG : degBound G < N := (degBound_map (algebraMap k K) G₀).trans_lt hN
  set y₀ : Fin N × Fin N → k := fun t => (G₀.coeff t.1).coeff t.2
  have hpoly : ∀ v, polySize v G N = ⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t) := fun v => by
    simp [polySize, G, y₀]
  set M : ℝ := ((N ^ 3 * 2 ^ N : ℕ) : ℝ)
  have hM : 1 ≤ M := by
    have hN0 : N ≠ 0 := by omega
    have : 1 ≤ N ^ 3 * 2 ^ N := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hN0)
      (by positivity))
    change (1 : ℝ) ≤ ((N ^ 3 * 2 ^ N : ℕ) : ℝ)
    exact_mod_cast this
  have hpt : ∀ v, log⁺ (⨆ m : (shiftPoly G c).support, normalizedAbs v ((shiftPoly G c).coeff m)) ≤
      Faltings.NumberField.localWeight K v * Real.log M +
        log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) + N * log⁺ (normalizedAbs v c) := by
    intro v
    have h := iSup_absV_shiftPoly_le v G c hNG
    rw [hpoly] at h
    have hS0 : 0 ≤ ⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t) :=
      Real.iSup_nonneg fun _ => normalizedAbs_nonneg _ _
    have hMκ : 1 ≤ M ^ Faltings.NumberField.localWeight K v :=
      Real.one_le_rpow hM (localWeight_nonneg v)
    calc _ ≤ log⁺ (M ^ Faltings.NumberField.localWeight K v *
          (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) * max 1 (normalizedAbs v c) ^ N) :=
          Real.posLog_le_posLog (by linarith [Real.iSup_nonneg (fun m :
            (shiftPoly G c).support => normalizedAbs_nonneg v ((shiftPoly G c).coeff m))]) h
      _ ≤ log⁺ (M ^ Faltings.NumberField.localWeight K v) +
          log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) +
            log⁺ (max 1 (normalizedAbs v c) ^ N) := by
          refine Real.posLog_mul.trans ?_
          gcongr
          exact Real.posLog_mul
      _ = _ := by
          have e1 : log⁺ (M ^ Faltings.NumberField.localWeight K v) =
              Faltings.NumberField.localWeight K v * Real.log M := by
            rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact hMκ),
              Real.log_rpow (by linarith)]
          have e2 : log⁺ (max 1 (normalizedAbs v c) ^ N) = N * log⁺ (normalizedAbs v c) := by
            rw [Real.posLog_eq_log (x := max 1 (normalizedAbs v c) ^ N) (by
              rw [abs_of_nonneg (by positivity)]; exact one_le_pow₀ (le_max_left _ _)),
              Real.log_pow, ← Real.posLog_eq_log_max_one (normalizedAbs_nonneg _ _)]
          rw [e1, e2]
  set a := (derivative G).evalEval c u with ha
  have hQ : MvPolynomial.pderiv 0 (shiftPoly G 0) = MvPolynomial.map (algebraMap k K) Q₀ := by
    have := shiftPoly_map (algebraMap k K) G₀ 0
    rw [map_zero] at this
    rw [this, MvPolynomial.pderiv_map]
  have haeval : a = MvPolynomial.eval ![u, c] (MvPolynomial.map (algebraMap k K) Q₀) := by
    rw [← hQ, eval_pderiv_shiftPoly, add_zero]
  have hcard := Faltings.NumberField.logHeight₁_eval_le (MvPolynomial.map (algebraMap k K) Q₀)
    (fun t => (MvPolynomial.map (algebraMap k K) Q₀).degreeOf t) (fun _ => le_rfl) ![u, c]
  rw [← haeval, affineLogHeight_map, Fin.sum_univ_two] at hcard
  have hdeg' : ∀ t, (MvPolynomial.map (algebraMap k K) Q₀).degreeOf t = Q₀.degreeOf t := by
    intro t
    simp only [MvPolynomial.degreeOf,
      MvPolynomial.degrees_map_of_injective _ (algebraMap k K).injective]
  have hmc : Faltings.MvPolynomial.monomialCount (MvPolynomial.map (algebraMap k K) Q₀) =
      Faltings.MvPolynomial.monomialCount Q₀ := by
    simp only [Faltings.MvPolynomial.monomialCount,
      MvPolynomial.support_map_of_injective _ (algebraMap k K).injective]
  rw [hdeg', hdeg', hmc] at hcard
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcard
  have hfa := hasFiniteSupport_posLog_absV a⁻¹
  have hfc := hasFiniteSupport_posLog_absV c
  have hf0 := hasFiniteSupport_posLog_iSup_absV (algebraMap k K ∘ y₀)
  have hfp := hasFiniteSupport_posLog_iSup_absV
    (fun m : (shiftPoly G c).support => (shiftPoly G c).coeff m)
  have hfκ := (hasFiniteSupport_localWeight (K := K))
  have hfκM : HasFiniteSupport fun v => Faltings.NumberField.localWeight K v * Real.log M :=
    Set.Finite.subset hfκ (Function.support_mul_subset_left _ _)
  have hfNc : HasFiniteSupport fun v => (N : ℝ) * log⁺ (normalizedAbs v c) :=
    Set.Finite.subset hfc (Function.support_mul_subset_right _ _)
  have hle : ∑ᶠ v, (log⁺ (⨆ m : (shiftPoly G c).support,
          normalizedAbs v ((shiftPoly G c).coeff m)) +
        log⁺ (normalizedAbs v a⁻¹)) ≤
      ∑ᶠ v, (Faltings.NumberField.localWeight K v * Real.log M +
        log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) + N * log⁺ (normalizedAbs v c) +
          log⁺ (normalizedAbs v a⁻¹)) := by
    refine finsum_le_finsum' (hfp.add hfa) (((hfκM.add hf0).add hfNc).add hfa) fun v => ?_
    linarith [hpt v]
  have hR : ∑ᶠ v, (Faltings.NumberField.localWeight K v * Real.log M +
        log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) + N * log⁺ (normalizedAbs v c) +
          log⁺ (normalizedAbs v a⁻¹)) =
      Real.log M + Height.logHeight (fun o : Option (Fin N × Fin N) =>
          o.elim 1 (algebraMap k K ∘ y₀)) / finrank ℚ K +
        N * (Height.logHeight₁ c / finrank ℚ K) + Height.logHeight₁ a / finrank ℚ K := by
    have hs1 : HasFiniteSupport fun v => Faltings.NumberField.localWeight K v * Real.log M +
        log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) := hfκM.add hf0
    have hs2 : HasFiniteSupport fun v => Faltings.NumberField.localWeight K v * Real.log M +
        log⁺ (⨆ t, normalizedAbs v ((algebraMap k K ∘ y₀) t)) + N * log⁺ (normalizedAbs v c) :=
      hs1.add hfNc
    rw [finsum_add_distrib hs2 hfa, finsum_add_distrib hs1 hfNc, finsum_add_distrib hfκM hf0,
      ← finsum_mul,
      ← mul_finsum, Faltings.NumberField.finsum_localWeight, one_mul, finsum_posLog_iSup_absV,
      finsum_posLog_absV, finsum_posLog_absV, Height.logHeight₁_inv]
  rw [hR] at hle
  have hcomp : (fun o : Option (Fin N × Fin N) => o.elim 1 (algebraMap k K ∘ y₀)) =
      algebraMap k K ∘ fun o => o.elim 1 y₀ := by
    funext o; rcases o with _ | t <;> simp
  have hne : (fun o : Option (Fin N × Fin N) => o.elim 1 y₀) ≠ 0 := fun h => by
    simpa using congrFun h none
  rw [hcomp, logHeight_algebraMap_div hne] at hle
  have hN0 : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hhc : 0 ≤ Height.logHeight₁ c / finrank ℚ K := by positivity
  have hhu : 0 ≤ Height.logHeight₁ u / finrank ℚ K := by positivity
  have he0 : (0 : ℝ) ≤ Q₀.degreeOf 0 := Nat.cast_nonneg _
  have he1 : (0 : ℝ) ≤ Q₀.degreeOf 1 := Nat.cast_nonneg _
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine hle.trans ?_
  nlinarith [hcard, mul_nonneg he0 hhc, mul_nonneg he1 hhu, mul_nonneg hN' hhu]

end PairBound

section PlaneRelation

open Polynomial IntermediateField

variable {k : Type*} [Field k]

open scoped Classical in
/-- The primitive integral multiple `r μ ∈ k[Y][X]` of `μ ∈ k(Y)[X]`, `r` the monic least common
denominator of the coefficients: the construction behind
`Faltings.FunctionField.planeRelation`. -/
private noncomputable def clearDenoms (μ : (RatFunc k)[X]) : k[X][X] :=
  ∑ i ∈ μ.support, C ((μ.coeff i).num *
    ((μ.support.lcm fun i => (μ.coeff i).denom) / (μ.coeff i).denom)) * Polynomial.X ^ i

open scoped Classical in
private lemma map_clearDenoms (μ : (RatFunc k)[X]) :
    (clearDenoms μ).map (algebraMap k[X] (RatFunc k)) =
      C (algebraMap k[X] (RatFunc k) (μ.support.lcm fun i => (μ.coeff i).denom)) * μ := by
  ext i
  rw [coeff_map, coeff_C_mul, clearDenoms, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hji => ite_eq_right (Ne.symm hji)) (fun hi => by
    rw [ite_eq_left rfl, Polynomial.notMem_support_iff.1 hi]; simp)]
  rw [ite_eq_left rfl]
  by_cases hi : i ∈ μ.support
  · obtain ⟨q, hq⟩ : (μ.coeff i).denom ∣ μ.support.lcm fun i => (μ.coeff i).denom :=
      Finset.dvd_lcm hi
    rw [hq, mul_div_cancel_left₀ _ (RatFunc.denom_ne_zero _), map_mul, map_mul]
    have hden : algebraMap k[X] (RatFunc k) (μ.coeff i).denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (RatFunc.denom_ne_zero _)
    have h := RatFunc.num_div_denom (μ.coeff i)
    rw [div_eq_iff hden] at h
    rw [h]
    ring
  · rw [Polynomial.notMem_support_iff.1 hi]
    simp

open scoped Classical in
private lemma planeRelation_eq_clearDenoms {F : Type*} [Field F] [Algebra k F] (t z : F)
    (ht : Transcendental k t) :
    Faltings.FunctionField.planeRelation k t z ht =
      clearDenoms ((minpoly k⟮t⟯ z).map
        (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom) := rfl

/-- **The plane relation vanishes on `(z, t)`**: `g(z, t) = 0` in `F`. -/
private lemma eval₂_planeRelation {F : Type*} [Field F] [Algebra k F] (t z : F)
    (ht : Transcendental k t) :
    (Faltings.FunctionField.planeRelation k t z ht).eval₂ (Polynomial.aeval t).toRingHom z =
      0 := by
  classical
  set e := RatFunc.algEquivOfTranscendental t ht
  let ε : RatFunc k →+* F := (algebraMap k⟮t⟯ F).comp e.toRingEquiv.toRingHom
  have hev : (Polynomial.aeval t).toRingHom = ε.comp (algebraMap k[X] (RatFunc k)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [ε, e, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      change _ = algebraMap k⟮t⟯ F ((RatFunc.algEquivOfTranscendental t ht)
        (algebraMap k[X] (RatFunc k) (C a)))
      rw [RatFunc.algEquivOfTranscendental_algebraMap, aeval_C]
      rfl
    · simp [ε, e]
  rw [planeRelation_eq_clearDenoms, hev, ← eval₂_map, map_clearDenoms, eval₂_mul, eval₂_C,
    eval₂_map]
  refine mul_eq_zero_of_right _ ?_
  have : ε.comp e.symm.toRingEquiv.toRingHom = algebraMap k⟮t⟯ F := by
    ext x
    simp [ε]
  rw [this, ← Polynomial.aeval_def, minpoly.aeval]

/-- The plane relation has positive degree in `X` when `z` is algebraic over `k(t)`. -/
private lemma one_le_natDegree_planeRelation {F : Type*} [Field F] [Algebra k F] (t z : F)
    (ht : Transcendental k t) (hz : IsIntegral k⟮t⟯ z) :
    1 ≤ (Faltings.FunctionField.planeRelation k t z ht).natDegree := by
  classical
  set μ : (RatFunc k)[X] := (minpoly k⟮t⟯ z).map
    (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom
  have hμ : 1 ≤ μ.natDegree := by
    rw [natDegree_map]
    exact minpoly.natDegree_pos hz
  have hr : algebraMap k[X] (RatFunc k) (μ.support.lcm fun i => (μ.coeff i).denom) ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ?_
    rw [Ne, Finset.lcm_eq_zero_iff]
    push Not
    exact fun i _ => RatFunc.denom_ne_zero _
  have h := congrArg Polynomial.natDegree (map_clearDenoms μ)
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _), natDegree_C_mul hr] at h
  rw [planeRelation_eq_clearDenoms, h]
  exact hμ

end PlaneRelation

section BaseChangeRatFunc

open Polynomial

variable {k K : Type*} [Field k] [Field K]

private lemma num_denom_div_of_isCoprime {p q : K[X]} (hq : q.Monic) (hpq : IsCoprime p q) :
    (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q).num = p ∧
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q).denom = q := by
  set x := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have h := (RatFunc.num_mul_eq_mul_denom_iff hq.ne_zero (x := x) (p := p)).2 rfl
  have h1 : x.denom ∣ q := (RatFunc.isCoprime_num_denom x).symm.dvd_of_dvd_mul_left
    ⟨p, by rw [h, mul_comm]⟩
  have h2 : q ∣ x.denom := hpq.symm.dvd_of_dvd_mul_left ⟨x.num, by rw [← h, mul_comm]⟩
  have hd : x.denom = q := eq_of_monic_of_associated (RatFunc.monic_denom x) hq
    (associated_of_dvd_dvd h1 h2)
  refine ⟨?_, hd⟩
  rw [hd] at h
  exact mul_right_cancel₀ hq.ne_zero h

private lemma gcd_map_eq [DecidableEq k] [DecidableEq K] (φ : k →+* K) (p q : k[X]) :
    gcd (p.map φ) (q.map φ) = (gcd p q).map φ := by
  have h1 : (gcd p q).map φ ∣ gcd (p.map φ) (q.map φ) :=
    dvd_gcd (Polynomial.map_dvd φ (gcd_dvd_left p q)) (Polynomial.map_dvd φ (gcd_dvd_right p q))
  obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul p q
  have h2 : gcd (p.map φ) (q.map φ) ∣ (gcd p q).map φ := by
    rw [hxy, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul]
    exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_left (gcd_dvd_right _ _) _)
  have hn1 : normalize (gcd (p.map φ) (q.map φ)) = gcd (p.map φ) (q.map φ) := normalize_gcd _ _
  have hn2 : normalize ((gcd p q).map φ) = (gcd p q).map φ := by
    rw [← Polynomial.map_normalize, normalize_gcd]
  rw [← hn1, ← hn2]
  exact normalize_eq_normalize h2 h1

private lemma lcm_map_eq [DecidableEq k] [DecidableEq K] (φ : k →+* K) (p q : k[X]) :
    lcm (p.map φ) (q.map φ) = (lcm p q).map φ := by
  by_cases hg : gcd p q = 0
  · rw [gcd_eq_zero_iff] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simp
  have hg' : (gcd p q).map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).2 hg
  have h1 := gcd_mul_lcm (p.map φ) (q.map φ)
  have h2 := gcd_mul_lcm p q
  rw [gcd_map_eq] at h1
  have h3 : Associated ((gcd p q).map φ * (lcm p q).map φ) (p.map φ * q.map φ) := by
    rw [← Polynomial.map_mul, ← Polynomial.map_mul]
    obtain ⟨u, hu⟩ := h2
    refine ⟨(Units.map (Polynomial.mapRingHom φ).toMonoidHom u), ?_⟩
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_mapRingHom]
    rw [← Polynomial.map_mul, hu]
  have h4 := h1.trans h3.symm
  have h5 : Associated (lcm (p.map φ) (q.map φ)) ((lcm p q).map φ) :=
    (Associated.of_mul_left h4 (Associated.refl _) hg')
  have hn1 : normalize (lcm (p.map φ) (q.map φ)) = lcm (p.map φ) (q.map φ) := normalize_lcm _ _
  have hn2 : normalize ((lcm p q).map φ) = (lcm p q).map φ := by
    rw [← Polynomial.map_normalize, normalize_lcm]
  rw [← hn1, ← hn2]
  exact normalize_eq_normalize h5.dvd h5.symm.dvd

private lemma finset_lcm_map [DecidableEq k] [DecidableEq K] (φ : k →+* K) {ι : Type*}
    (s : Finset ι) (f : ι → k[X]) : (s.lcm f).map φ = s.lcm fun i => (f i).map φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.lcm_insert, Finset.lcm_insert, ← ih, lcm_map_eq]

/-- Extension of scalars `k(Y) → K(Y)` of rational functions. -/
private noncomputable def ratFuncMap (φ : k →+* K) : RatFunc k →+* RatFunc K :=
  RatFunc.liftRingHom ((algebraMap K[X] (RatFunc K)).comp (mapRingHom φ)) (by
    intro p hp
    refine mem_nonZeroDivisors_of_ne_zero ?_
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom]
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2
      ((Polynomial.map_ne_zero_iff φ.injective).2 (nonZeroDivisors.ne_zero hp)))

private lemma ratFuncMap_apply (φ : k →+* K) (f : RatFunc k) :
    ratFuncMap φ f = algebraMap K[X] (RatFunc K) (f.num.map φ) /
      algebraMap K[X] (RatFunc K) (f.denom.map φ) :=
  RatFunc.liftRingHom_apply _ _ f

private lemma ratFuncMap_algebraMap (φ : k →+* K) (p : k[X]) :
    ratFuncMap φ (algebraMap k[X] (RatFunc k) p) = algebraMap K[X] (RatFunc K) (p.map φ) := by
  rw [ratFuncMap_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.map_one,
    map_one, div_one]

private lemma num_ratFuncMap (φ : k →+* K) (f : RatFunc k) :
    (ratFuncMap φ f).num = f.num.map φ ∧ (ratFuncMap φ f).denom = f.denom.map φ := by
  rw [ratFuncMap_apply]
  exact num_denom_div_of_isCoprime ((RatFunc.monic_denom f).map φ)
    ((RatFunc.isCoprime_num_denom f).map (mapRingHom φ))

open scoped Classical in
/-- Clearing denominators commutes with extension of scalars. -/
private lemma clearDenoms_map (φ : k →+* K) (μ : (RatFunc k)[X]) :
    clearDenoms (μ.map (ratFuncMap φ)) = (clearDenoms μ).map (mapRingHom φ) := by
  have hsupp : (μ.map (ratFuncMap φ)).support = μ.support :=
    support_map_of_injective _ (ratFuncMap φ).injective
  have hlcm : ((μ.map (ratFuncMap φ)).support.lcm fun i =>
      ((μ.map (ratFuncMap φ)).coeff i).denom) =
      (μ.support.lcm fun i => (μ.coeff i).denom).map φ := by
    rw [finset_lcm_map, hsupp]
    refine Finset.lcm_congr rfl fun i _ => ?_
    rw [coeff_map, (num_ratFuncMap φ _).2]
  rw [clearDenoms, clearDenoms, hlcm, hsupp, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coeff_map, (num_ratFuncMap φ _).1,
    (num_ratFuncMap φ _).2, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_div]

end BaseChangeRatFunc

section MinpolyBaseChange

open Polynomial IntermediateField

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]

/-- The powers `1, z, …, z^{n-1}` are independent over `k[t]`, for `n = deg_{k(t)} z` and `t`
transcendental. -/
private lemma eq_zero_of_sum_aeval_mul_pow_eq_zero (t z : F) (ht : Transcendental k t)
    {m : ℕ} (hm : m < (minpoly k⟮t⟯ z).natDegree) (Q : ℕ → k[X])
    (h : ∑ i ∈ Finset.range (m + 1), Polynomial.aeval t (Q i) * z ^ i = 0) :
    ∀ i ≤ m, Q i = 0 := by
  set R : k⟮t⟯[X] := ∑ i ∈ Finset.range (m + 1),
    C (Polynomial.aeval (AdjoinSimple.gen k t) (Q i)) * Polynomial.X ^ i
  have hR : Polynomial.aeval z R = 0 := by
    simp only [R, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.algebraMap_apply, AdjoinSimple.coe_aeval_gen_apply]
  have hRdeg : R.natDegree ≤ m := by
    refine (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_)
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hR0 : R = 0 := by
    by_contra hne
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd k⟮t⟯ z hR) hne
    omega
  intro i hi
  have hc := congrArg (fun p => p.coeff i) hR0
  simp only [R, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun j _ hji => ite_eq_right (Ne.symm hji))
    (fun hi' => absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) hi'), ite_eq_left rfl] at hc
  have hc' : Polynomial.aeval t (Q i) = 0 := by
    rw [← AdjoinSimple.coe_aeval_gen_apply, hc]; rfl
  exact (transcendental_iff_injective.1 ht) (hc'.trans (map_zero _).symm)

variable {K : Type*} [Field K] [Algebra k K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra k F'] [IsScalarTower k K F']

/-- The decomposition of a polynomial over `K` along a `k`-basis of `K`. -/
private lemma eq_sum_basis_mul_map {ι : Type*} [Fintype ι] (b : Module.Basis ι k K) (P : K[X]) :
    P = ∑ r, C (b r) * (∑ j ∈ P.support, monomial j (b.repr (P.coeff j) r)).map
      (algebraMap k K) := by
  ext j
  simp only [finsetSum_coeff, coeff_C_mul, coeff_map, coeff_monomial]
  by_cases hj : j ∈ P.support
  · simp only [Finset.sum_ite_eq', ite_eq_left hj]
    conv_lhs => rw [← b.sum_repr (P.coeff j)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Algebra.smul_def, mul_comm]
  · rw [Polynomial.notMem_support_iff.1 hj]
    simp [Finset.sum_ite_eq', hj]

/-- **Independence over `K[t]`**, from the linear disjointness of `K` and `F` in `F'`. -/
public lemma eq_zero_of_sum_aeval_mul_pow_eq_zero_of_linearDisjoint {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k K) (β : F →ₐ[k] F')
    (hLD : ∀ f : ι → F, ∑ r, algebraMap K F' (b r) * β (f r) = 0 → ∀ r, f r = 0)
    (t z : F) (ht : Transcendental k t) {m : ℕ}
    (hm : m < (minpoly k⟮t⟯ z).natDegree) (P : ℕ → K[X])
    (h : ∑ i ∈ Finset.range (m + 1), Polynomial.aeval (β t) (P i) * β z ^ i = 0) :
    ∀ i ≤ m, P i = 0 := by
  set Q : ℕ → ι → k[X] := fun i r =>
    ∑ j ∈ (P i).support, monomial j (b.repr ((P i).coeff j) r)
  have hP : ∀ i, P i = ∑ r, C (b r) * (Q i r).map (algebraMap k K) :=
    fun i => eq_sum_basis_mul_map b (P i)
  have haeval : ∀ i, Polynomial.aeval (β t) (P i) =
      ∑ r, algebraMap K F' (b r) * β (Polynomial.aeval t (Q i r)) := by
    intro i
    conv_lhs => rw [hP i]
    simp only [map_sum, map_mul, aeval_C, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algHom_apply]
  have hsum : ∑ r, algebraMap K F' (b r) *
      β (∑ i ∈ Finset.range (m + 1), Polynomial.aeval t (Q i r) * z ^ i) = 0 := by
    rw [← h]
    simp only [haeval, map_sum, map_mul, map_pow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have hQ := hLD _ hsum
  intro i hi
  rw [hP i]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [eq_zero_of_sum_aeval_mul_pow_eq_zero t z ht hm (fun i => Q i r) (hQ r) i hi,
    Polynomial.map_zero, mul_zero]

end MinpolyBaseChange

section PlaneRelationBaseChange

open Polynomial IntermediateField

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
  {K : Type*} [Field K] [Algebra k K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra k F'] [IsScalarTower k K F']

/-- **The plane relation commutes with extension of scalars** `k → K`, when `K` and `F` are
linearly disjoint over `k` inside `F'`. -/
public lemma planeRelation_map_of_linearDisjoint {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k K) (β : F →ₐ[k] F')
    (hLD : ∀ f : ι → F, ∑ r, algebraMap K F' (b r) * β (f r) = 0 → ∀ r, f r = 0)
    (t z : F) (ht : Transcendental k t) (ht' : Transcendental K (β t))
    (hz : IsIntegral k⟮t⟯ z) :
    Faltings.FunctionField.planeRelation K (β t) (β z) ht' =
      (Faltings.FunctionField.planeRelation k t z ht).map (mapRingHom (algebraMap k K)) := by
  classical
  set e := RatFunc.algEquivOfTranscendental t ht
  set σ := RatFunc.algEquivOfTranscendental (β t) ht'
  set ρ := ratFuncMap (algebraMap k K)
  set θ : RatFunc k →+* K⟮β t⟯ := σ.toRingEquiv.toRingHom.comp ρ
  have he : ∀ p : k[X], (e (algebraMap k[X] (RatFunc k) p) : F) = Polynomial.aeval t p := by
    intro p
    rw [RatFunc.algEquivOfTranscendental_algebraMap, AdjoinSimple.coe_aeval_gen_apply]
  have hσ : ∀ p : K[X], (σ (algebraMap K[X] (RatFunc K) p) : F') = Polynomial.aeval (β t) p := by
    intro p
    rw [RatFunc.algEquivOfTranscendental_algebraMap, AdjoinSimple.coe_aeval_gen_apply]
  have hsq : (algebraMap K⟮β t⟯ F').comp θ =
      (β : F →+* F').comp ((algebraMap k⟮t⟯ F).comp e.toRingEquiv.toRingHom) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k[X]) (RingHom.ext fun p => ?_)
    simp only [RingHom.comp_apply, θ]
    change (σ (ρ (algebraMap k[X] (RatFunc k) p)) : F') = β (e (algebraMap k[X] (RatFunc k) p))
    rw [ratFuncMap_algebraMap, hσ, he, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algHom_apply]
  have hsq' : (algebraMap K⟮β t⟯ F').comp (θ.comp e.symm.toRingEquiv.toRingHom) =
      (β : F →+* F').comp (algebraMap k⟮t⟯ F) := by
    rw [← RingHom.comp_assoc, hsq]
    ext x
    simp
  set P : K⟮β t⟯[X] := (minpoly k⟮t⟯ z).map (θ.comp e.symm.toRingEquiv.toRingHom)
  have hPmon : P.Monic := (minpoly.monic hz).map _
  have hPz : Polynomial.aeval (β z) P = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hsq',
      show β z = (β : F →+* F') z from rfl, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hint : IsIntegral K⟮β t⟯ (β z) := ⟨P, hPmon, by rwa [← Polynomial.aeval_def]⟩
  have hPdeg : P.natDegree = (minpoly k⟮t⟯ z).natDegree := natDegree_map _
  have hdeg : (minpoly k⟮t⟯ z).natDegree ≤ (minpoly K⟮β t⟯ (β z)).natDegree := by
    by_contra hlt
    push Not at hlt
    set mK := minpoly K⟮β t⟯ (β z)
    set m := mK.natDegree
    set c : ℕ → RatFunc K := fun i => σ.symm (mK.coeff i)
    set Dn : K[X] := ∏ i ∈ Finset.range (m + 1), (c i).denom
    have hDn : Dn ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => RatFunc.denom_ne_zero _
    set P' : ℕ → K[X] := fun i => (c i).num * (Dn / (c i).denom)
    have hP' : ∀ i ∈ Finset.range (m + 1), algebraMap K[X] (RatFunc K) (P' i) =
        c i * algebraMap K[X] (RatFunc K) Dn := by
      intro i hi
      obtain ⟨q, hq⟩ : (c i).denom ∣ Dn := Finset.dvd_prod_of_mem _ hi
      have hden : algebraMap K[X] (RatFunc K) (c i).denom ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (RatFunc.denom_ne_zero _)
      simp only [P']
      rw [hq, mul_div_cancel_left₀ _ (RatFunc.denom_ne_zero _), map_mul, map_mul]
      have h := RatFunc.num_div_denom (c i)
      rw [div_eq_iff hden] at h
      rw [h]
      ring
    have hsum : ∑ i ∈ Finset.range (m + 1), Polynomial.aeval (β t) (P' i) * β z ^ i = 0 := by
      have h1 : ∀ i ∈ Finset.range (m + 1), Polynomial.aeval (β t) (P' i) * β z ^ i =
          Polynomial.aeval (β t) Dn * ((mK.coeff i : F') * β z ^ i) := by
        intro i hi
        rw [← hσ, hP' i hi, map_mul, ← hσ]
        simp only [c, AlgEquiv.apply_symm_apply]
        push_cast
        ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
      refine mul_eq_zero_of_right _ ?_
      have := minpoly.aeval K⟮β t⟯ (β z)
      rw [Polynomial.aeval_eq_sum_range] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def]
      rfl
    have h0 := eq_zero_of_sum_aeval_mul_pow_eq_zero_of_linearDisjoint b β hLD t z ht hlt P'
      hsum m le_rfl
    have hcm : c m = 1 := by
      simp only [c, mK, m]
      rw [(minpoly.monic hint).coeff_natDegree, map_one]
    simp only [P', hcm, RatFunc.num_one, RatFunc.denom_one, one_mul, EuclideanDomain.div_one]
      at h0
    exact hDn h0
  have hmin : minpoly K⟮β t⟯ (β z) = P :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPmon (minpoly.dvd _ _ hPz)
      (by rw [hPdeg]; exact hdeg)).symm
  rw [planeRelation_eq_clearDenoms, planeRelation_eq_clearDenoms, ← clearDenoms_map]
  congr 1
  rw [hmin, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply, θ]
  exact σ.symm_apply_apply _

end PlaneRelationBaseChange

section StepOne

open Polynomial Real _root_.PowerSeries

/-- The pairs `(ν, j)` with `ν ≠ j` and `(ν, j) ∉ {(1, 0), (0, 1)}`. -/
private noncomputable abbrev pairSet (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter fun P => P.1 ≠ P.2 ∧ P ≠ (1, 0) ∧ P ≠ (0, 1)

variable {k : Type*} [Field k] {K : Type*} [Field K] [NumberField K] [Algebra k K]

/-- The local bound `T_v` at a place `v`: the sum over the pairs of
`2 (log⁺ |p_{νj}|_v + log⁺ |a_{νj}⁻¹|_v)`, plus `7 κ_v log (2N)`. -/
private noncomputable def stepBound {n : ℕ} (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X]) (N : ℕ)
    (c₀ : K) (y : Fin (n + 1) → K) (v : InfinitePlace K ⊕ FinitePlace K) : ℝ :=
  (∑ P ∈ pairSet n, 2 *
    (log⁺ (⨆ m : (shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) c₀).support,
        normalizedAbs v ((shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) c₀).coeff m)) +
      log⁺ (normalizedAbs v
        ((derivative ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K)))).evalEval c₀
        (y P.1 / y P.2))⁻¹))) +
    7 * Faltings.NumberField.localWeight K v * Real.log (2 * N)

private lemma stepBound_nonneg {n : ℕ} (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X]) {N : ℕ}
    (hN : 1 ≤ N) (c₀ : K) (y : Fin (n + 1) → K) (v : InfinitePlace K ⊕ FinitePlace K) :
    0 ≤ stepBound G₀ N c₀ y v := by
  have h1 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have h2 := localWeight_nonneg (K := K) v
  refine add_nonneg (Finset.sum_nonneg fun P _ => ?_) (by positivity)
  exact mul_nonneg zero_le_two (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)

end StepOne

section StepOneLocal

open Polynomial Real _root_.PowerSeries

variable {k : Type*} [Field k] {K : Type*} [Field K] [NumberField K] [Algebra k K]

/-- The coefficients of `(c + X)⁻¹`. -/
private lemma coeff_eq_of_mul_eq_one {c : K} {e : K⟦X⟧}
    (h : (PowerSeries.C c + PowerSeries.X) * e = 1) (i : ℕ) :
    PowerSeries.coeff i e = (-c⁻¹) ^ i * c⁻¹ := by
  have h0 : c * PowerSeries.constantCoeff e = 1 := by
    simpa using congrArg PowerSeries.constantCoeff h
  have hc : c ≠ 0 := left_ne_zero_of_mul_eq_one h0
  have hrec : ∀ i, c * PowerSeries.coeff (i + 1) e + PowerSeries.coeff i e = 0 := by
    intro i
    have := congrArg (PowerSeries.coeff (i + 1)) h
    rwa [add_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero i)] at this
  induction i with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul]
    exact eq_inv_of_mul_eq_one_right h0
  | succ i ih =>
    have h3 : c * PowerSeries.coeff (i + 1) e = -((-c⁻¹) ^ i * c⁻¹) := by
      linear_combination hrec i - ih
    calc PowerSeries.coeff (i + 1) e = c⁻¹ * (c * PowerSeries.coeff (i + 1) e) := by
          field_simp
      _ = _ := by rw [h3, pow_succ]; ring

variable {R : Type*} [CommRing R] {F' : Type*} [Field F'] [Algebra R F'] [Algebra K F']

/-- The bound `log |∂_i ξ_{νj}(0)|_v ≤ i T_v` in the abstract setting: `R` is the local ring at
`z` inside `F' = K(C_K)`, `ev` is evaluation at `z`, `E` the expansion in `K⟦ς⟧`. -/
private lemma log_absV_coeff_le_stepBound (hinj : Function.Injective (algebraMap R F'))
    (cst : K →+* R) (hcst : ∀ a, algebraMap R F' (cst a) = algebraMap K F' a)
    (ev : R →+* K) (E : R →+* K⟦X⟧) (hE0 : ∀ r, PowerSeries.constantCoeff (E r) = ev r)
    (hEc : ∀ a, E (cst a) = PowerSeries.C a) (ς : R) (hEς : E ς = PowerSeries.X)
    (hEp : ∀ (ξ : R) (p : MvPolynomial (Fin 2) K),
      MvPolynomial.aeval ![algebraMap R F' ξ, algebraMap R F' ς] p = 0 →
        MvPolynomial.aeval ![E ξ, PowerSeries.X] p = 0)
    {n : ℕ} (x' : Fin (n + 1) → F') (ht : Transcendental K (x' 1 / x' 0))
    (s : R) (hs : algebraMap R F' s = x' 1 / x' 0) (hς : ς = s - cst (ev s))
    (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X])
    (hG : ∀ ν j, (ν, j) ∈ pairSet n → Faltings.FunctionField.planeRelation K (x' 1 / x' 0)
      (x' ν / x' j) ht = (G₀ ν j).map (mapRingHom (algebraMap k K)))
    (hdisc : ∀ ν j, (ν, j) ∈ pairSet n →
      ((Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).resultant
        (derivative (Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht))
        (Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).natDegree
        ((Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).natDegree -
          1)).eval (ev s) ≠ 0)
    (hdeg1 : ∀ ν j, (ν, j) ∈ pairSet n → 1 ≤ (G₀ ν j).natDegree)
    {N : ℕ} (hN : ∀ ν j, (ν, j) ∈ pairSet n → degBound (G₀ ν j) < N) (hN1 : 1 ≤ N)
    (y : Fin (n + 1) → K) (j : Fin (n + 1)) (ξ : Fin (n + 1) → R)
    (hξ : ∀ ν, algebraMap R F' (ξ ν) = x' ν / x' j) (hyξ : ∀ ν, ev (ξ ν) = y ν / y j)
    (v : InfinitePlace K ⊕ FinitePlace K) (hjv : ∀ ν, normalizedAbs v (ev (ξ ν)) ≤ 1)
    (ν : Fin (n + 1)) {i : ℕ} (hi : 1 ≤ i) :
    Real.log (normalizedAbs v (PowerSeries.constantCoeff
        (Faltings.PowerSeries.dividedDerivative K i (E (ξ ν))))) ≤
      i * stepBound G₀ N (ev s) y v := by
  have hT := stepBound_nonneg G₀ hN1 (ev s) y v
  have hiT : 0 ≤ (i : ℝ) * stepBound G₀ N (ev s) y v := mul_nonneg (Nat.cast_nonneg _) hT
  have hx0 : x' 0 ≠ 0 := fun h => ht.ne_zero (by rw [h, div_zero])
  have hx1 : x' 1 ≠ 0 := fun h => ht.ne_zero (by rw [h, zero_div])
  have hEs : E s = PowerSeries.X + PowerSeries.C (ev s) := by
    have : s = ς + cst (ev s) := by rw [hς]; ring
    conv_lhs => rw [this]
    rw [map_add, hEς, hEc]
  have hlog : ∀ a : K, normalizedAbs v a ≤ 1 →
      Real.log (normalizedAbs v a) ≤ i * stepBound G₀ N (ev s) y v :=
    fun a ha => (Real.log_nonpos (normalizedAbs_nonneg _ _) ha).trans hiT
  have habs0 := map_zero (normalizedAbs v)
  have habs1 := map_one (normalizedAbs v)
  by_cases hνj : ν = j
  · subst hνj
    rw [Faltings.PowerSeries.constantCoeff_dividedDerivative]
    have hc : PowerSeries.coeff i (E (ξ ν)) = 0 := by
      by_cases hxν : x' ν = 0
      · have h0 : ξ ν = 0 := hinj (by rw [hξ, hxν, div_zero, map_zero])
        rw [h0, map_zero, map_zero]
      · have h1 : ξ ν = 1 := hinj (by rw [hξ, div_self hxν, map_one])
        rw [h1, map_one, PowerSeries.coeff_one, ite_eq_right (by omega)]
    rw [hc]
    exact hlog 0 (by rw [habs0]; exact zero_le_one)
  by_cases h10 : (ν, j) = (1, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h10
    rw [Faltings.PowerSeries.constantCoeff_dividedDerivative]
    have h1 : ξ 1 = s := hinj (by rw [hξ, hs])
    rw [h1, hEs, map_add, PowerSeries.coeff_X, PowerSeries.coeff_C,
      ite_eq_right (show i ≠ 0 by omega), add_zero]
    refine hlog _ ?_
    split_ifs
    · exact habs1.le
    · rw [habs0]; exact zero_le_one
  by_cases h01 : (ν, j) = (0, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h01
    rw [Faltings.PowerSeries.constantCoeff_dividedDerivative]
    have h1 : ξ 0 * s = 1 := hinj (by
      rw [map_mul, hξ, hs, map_one, div_mul_div_comm, mul_comm (x' 0),
        div_self (mul_ne_zero hx1 hx0)])
    have h2 : (PowerSeries.C (ev s) + PowerSeries.X) * E (ξ 0) = 1 := by
      rw [add_comm, ← hEs, mul_comm, ← map_mul, h1, map_one]
    have h3 := coeff_eq_of_mul_eq_one h2
    have h4 : ev (ξ 0) = (ev s)⁻¹ := by
      rw [← hE0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, h3, pow_zero, one_mul]
    rw [h3 i]
    refine hlog _ ?_
    rw [map_mul, map_pow, normalizedAbs_neg, ← h4]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (normalizedAbs_nonneg _ _) (hjv 0))
      (normalizedAbs_nonneg _ _)).trans (by simpa using hjv 0)
  have hP : (ν, j) ∈ pairSet n := by
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hνj, h10, h01⟩
  have hGP : (G₀ ν j).map (mapRingHom (algebraMap k K)) =
      Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht := (hG ν j hP).symm
  set G₁ := (G₀ ν j).map (mapRingHom (algebraMap k K)) with hG₁
  set p := shiftPoly G₁ (ev s)
  have hp : MvPolynomial.aeval ![E (ξ ν), PowerSeries.X] p = 0 := by
    refine hEp _ _ ?_
    rw [aeval_shiftPoly]
    have ht' : algebraMap R F' ς + algebraMap K F' (ev s) = x' 1 / x' 0 := by
      rw [← hcst, ← map_add, hς, sub_add_cancel, hs]
    rw [ht', hξ, hGP]
    exact eval₂_planeRelation (x' 1 / x' 0) (x' ν / x' j) ht
  have hdeg : 1 ≤ p.degreeOf 0 := by
    rw [degreeOf_shiftPoly, hG₁, natDegree_map_eq_of_injective
      (Polynomial.map_injective _ (algebraMap k K).injective)]
    exact hdeg1 ν j hP
  have hD' : MvPolynomial.eval 0
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K 1 p)
        (Polynomial.derivative (MvPolynomial.finSuccEquiv K 1 p))
        (p.degreeOf 0) (p.degreeOf 0 - 1)) ≠ 0 := by
    rw [eval_resultant_shiftPoly, hGP]; exact hdisc ν j hP
  have hξv : normalizedAbs v (PowerSeries.constantCoeff (E (ξ ν))) ≤ 1 := by rw [hE0]; exact hjv ν
  have hb := log_absV_dividedDerivative_le p hdeg hD' (E (ξ ν)) hp v hξv hi
  rw [hE0, eval_pderiv_shiftPoly, zero_add, hyξ] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have htd : p.totalDegree < N := by
    have h1 := totalDegree_shiftPoly_le G₁ (ev s)
    rw [hG₁, degBound_map] at h1
    exact h1.trans_lt (hN ν j hP)
  have htd1 : 1 ≤ p.totalDegree := hdeg.trans (MvPolynomial.degreeOf_le_totalDegree p 0)
  have hlogN : Real.log (2 * p.totalDegree) ≤ Real.log (2 * N) := by
    refine Real.log_le_log (by positivity) ?_
    have : (p.totalDegree : ℝ) ≤ N := by exact_mod_cast htd.le
    linarith
  have hκ := localWeight_nonneg (K := K) v
  have hsingle := Finset.single_le_sum (f := fun P : Fin (n + 1) × Fin (n + 1) => 2 *
        (log⁺ (⨆ m : (shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) (ev s)).support,
            normalizedAbs v
              ((shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) (ev s)).coeff m)) +
          log⁺ (normalizedAbs v
            ((derivative ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K)))).evalEval
            (ev s) (y P.1 / y P.2))⁻¹))) (fun P _ => mul_nonneg zero_le_two
              (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)) hP
  unfold stepBound
  linarith [mul_le_mul_of_nonneg_left hlogN hκ, hsingle]

end StepOneLocal

section StepThree

open Polynomial Real _root_.PowerSeries Function

variable {k : Type*} [Field k] [NumberField k] {K : Type*} [Field K] [NumberField K]
  [Algebra k K]

/-- The constant `A` of the bound on `∑_v T_v` for one plane relation `g₀`. -/
private noncomputable def pairConstA (G₀ : k[X][X]) (N : ℕ) : ℝ :=
  Real.log ((N ^ 3 * 2 ^ N : ℕ) : ℝ) +
    Height.logHeight (fun o : Option (Fin N × Fin N) =>
      o.elim 1 fun t => (G₀.coeff t.1).coeff t.2) / finrank ℚ k +
    Faltings.affineLogHeight (AddMonoidAlgebra.coeff (MvPolynomial.pderiv 0 (shiftPoly G₀ 0))) +
    Real.log (Faltings.MvPolynomial.monomialCount (MvPolynomial.pderiv 0 (shiftPoly G₀ 0)))

/-- The constant `B` of the bound on `∑_v T_v` for one plane relation `g₀`. -/
private noncomputable def pairConstB (G₀ : k[X][X]) (N : ℕ) : ℝ :=
  N + (MvPolynomial.pderiv 0 (shiftPoly G₀ 0)).degreeOf 0 +
    (MvPolynomial.pderiv 0 (shiftPoly G₀ 0)).degreeOf 1

omit [NumberField k] in
private lemma pairConstB_nonneg (G₀ : k[X][X]) (N : ℕ) : 0 ≤ pairConstB G₀ N := by
  unfold pairConstB; positivity

private lemma hasFiniteSupport_finset_sum {α ι : Type*} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, HasFiniteSupport (f i)) : HasFiniteSupport fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Set.Finite.subset Set.finite_empty (by intro a ha; simp at ha)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have : HasFiniteSupport fun x => f a x + ∑ i ∈ s, f i x := h1.add h2
    simpa only [Finset.sum_insert ha] using this

/-- The sum over the places of `T_v` is at most `A₀ + A₁ h(y)`. -/
private lemma finsum_stepBound_le {n : ℕ} (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X]) {N : ℕ}
    (hN : ∀ ν j, (ν, j) ∈ pairSet n → degBound (G₀ ν j) < N)
    (y : Fin (n + 1) → K) (hy0 : y 0 = 1) :
    ∑ᶠ v, stepBound G₀ N (y 1) y v ≤
      (∑ P ∈ pairSet n, 2 * pairConstA (G₀ P.1 P.2) N + 7 * Real.log (2 * N)) +
        (∑ P ∈ pairSet n, 4 * pairConstB (G₀ P.1 P.2) N) *
          (Height.logHeight y / finrank ℚ K) := by
  have hdK : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  set H := Height.logHeight y / finrank ℚ K
  have hy1 : Height.logHeight₁ (y 1) / finrank ℚ K ≤ H := by
    have := Faltings.logHeight₁_div_le_logHeight y (j := 0) (by rw [hy0]; exact one_ne_zero) 1
    rw [hy0, div_one] at this
    exact div_le_div_of_nonneg_right this hdK.le
  have hyu : ∀ ν j : Fin (n + 1), Height.logHeight₁ (y ν / y j) / finrank ℚ K ≤ H := by
    intro ν j
    by_cases hj : y j = 0
    · rw [hj, div_zero, Height.logHeight₁_zero, zero_div]
      exact div_nonneg (Height.logHeight_nonneg _) hdK.le
    · exact div_le_div_of_nonneg_right (Faltings.logHeight₁_div_le_logHeight y hj ν) hdK.le
  set f : Fin (n + 1) × Fin (n + 1) → InfinitePlace K ⊕ FinitePlace K → ℝ := fun P v =>
    log⁺ (⨆ m : (shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) (y 1)).support,
        normalizedAbs v
          ((shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) (y 1)).coeff m)) +
      log⁺ (normalizedAbs v ((derivative ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K)))).evalEval
        (y 1) (y P.1 / y P.2))⁻¹)
  have hf : ∀ P, HasFiniteSupport (f P) := fun P =>
    (hasFiniteSupport_posLog_iSup_absV _).add (hasFiniteSupport_posLog_absV _)
  have hf2 : ∀ P ∈ pairSet n, HasFiniteSupport fun v => 2 * f P v := fun P _ =>
    Set.Finite.subset (hf P) (Function.support_mul_subset_right _ _)
  have hκ := hasFiniteSupport_mul_localWeight_mul (K := K) 7 (Real.log (2 * N))
  have hsum := hasFiniteSupport_finset_sum _ _ hf2
  have heq : ∑ᶠ v, stepBound G₀ N (y 1) y v =
      ∑ P ∈ pairSet n, 2 * ∑ᶠ v, f P v + 7 * Real.log (2 * N) := by
    unfold stepBound
    rw [finsum_add_distrib hsum hκ, finsum_sum_comm _ _ hf2]
    congr 1
    · refine Finset.sum_congr rfl fun P _ => ?_
      rw [mul_finsum]
    · have : (fun v => 7 * Faltings.NumberField.localWeight K v * Real.log (2 * N)) =
          fun v => Faltings.NumberField.localWeight K v * (7 * Real.log (2 * N)) := by
        funext v; ring
      rw [this, ← finsum_mul, Faltings.NumberField.finsum_localWeight, one_mul]
  rw [heq]
  have hP : ∀ P ∈ pairSet n, 2 * ∑ᶠ v, f P v ≤
      2 * pairConstA (G₀ P.1 P.2) N + 4 * pairConstB (G₀ P.1 P.2) N * H := by
    intro P hPm
    have h := finsum_posLog_shiftPoly_add_le (K := K) (G₀ P.1 P.2) (hN P.1 P.2 hPm) (y 1)
      (y P.1 / y P.2)
    simp only at h
    have h' : ∑ᶠ v, f P v ≤ _ := h
    have hB := pairConstB_nonneg (G₀ P.1 P.2) N
    have h2 : pairConstB (G₀ P.1 P.2) N * (Height.logHeight₁ (y 1) / finrank ℚ K +
        Height.logHeight₁ (y P.1 / y P.2) / finrank ℚ K) ≤ pairConstB (G₀ P.1 P.2) N * (2 * H) :=
      mul_le_mul_of_nonneg_left (by linarith [hy1, hyu P.1 P.2]) hB
    unfold pairConstA pairConstB
    unfold pairConstB at h2
    linarith [h', h2]
  have := Finset.sum_le_sum hP
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at this
  linarith

end StepThree

section PartOne

open Polynomial Real _root_.PowerSeries Function

variable {k : Type*} [Field k] [NumberField k] {K : Type*} [Field K] [NumberField K]
  [Algebra k K]

omit [NumberField k] in
private lemma hasFiniteSupport_stepBound {n : ℕ} (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X])
    (N : ℕ) (c₀ : K) (y : Fin (n + 1) → K) :
    HasFiniteSupport fun v => stepBound G₀ N c₀ y v := by
  have hf2 : ∀ P ∈ pairSet n, HasFiniteSupport fun v : InfinitePlace K ⊕ FinitePlace K => 2 *
      (log⁺ (⨆ m : (shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) c₀).support,
        normalizedAbs v ((shiftPoly ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K))) c₀).coeff m)) +
      log⁺ (normalizedAbs v
        ((derivative ((G₀ P.1 P.2).map (mapRingHom (algebraMap k K)))).evalEval c₀
        (y P.1 / y P.2))⁻¹)) := fun P _ =>
    Set.Finite.subset ((hasFiniteSupport_posLog_iSup_absV _).add (hasFiniteSupport_posLog_absV _))
      (Function.support_mul_subset_right _ _)
  have hκ := hasFiniteSupport_mul_localWeight_mul (K := K) 7 (Real.log (2 * N))
  exact (hasFiniteSupport_finset_sum _ _ hf2).add hκ

variable {R : Type*} [CommRing R] {F' : Type*} [Field F'] [Algebra R F'] [Algebra K F']

/-- **Part I**, in the abstract setting: the left side of the lemma is at most
`i* (A₀ + A₁ h(y))`, where `y` is the vector of values `ξ_{ν0}(z)`. -/
private lemma finsum_iSup_le_partOne (hinj : Function.Injective (algebraMap R F'))
    (cst : K →+* R) (hcst : ∀ a, algebraMap R F' (cst a) = algebraMap K F' a)
    (ev : R →+* K) (E : R →+* K⟦X⟧) (hE0 : ∀ r, PowerSeries.constantCoeff (E r) = ev r)
    (hEc : ∀ a, E (cst a) = PowerSeries.C a) (ς : R) (hEς : E ς = PowerSeries.X)
    (hEp : ∀ (ξ : R) (p : MvPolynomial (Fin 2) K),
      MvPolynomial.aeval ![algebraMap R F' ξ, algebraMap R F' ς] p = 0 →
        MvPolynomial.aeval ![E ξ, PowerSeries.X] p = 0)
    {n : ℕ} (x' : Fin (n + 1) → F') (ht : Transcendental K (x' 1 / x' 0))
    (s : R) (hs : algebraMap R F' s = x' 1 / x' 0) (hς : ς = s - cst (ev s))
    (G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X])
    (hG : ∀ ν j, (ν, j) ∈ pairSet n → Faltings.FunctionField.planeRelation K (x' 1 / x' 0)
      (x' ν / x' j) ht = (G₀ ν j).map (mapRingHom (algebraMap k K)))
    (hdisc : ∀ ν j, (ν, j) ∈ pairSet n →
      ((Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).resultant
        (derivative (Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht))
        (Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).natDegree
        ((Faltings.FunctionField.planeRelation K (x' 1 / x' 0) (x' ν / x' j) ht).natDegree -
          1)).eval (ev s) ≠ 0)
    (hdeg1 : ∀ ν j, (ν, j) ∈ pairSet n → 1 ≤ (G₀ ν j).natDegree)
    {N : ℕ} (hN : ∀ ν j, (ν, j) ∈ pairSet n → degBound (G₀ ν j) < N) (hN1 : 1 ≤ N)
    (y : Fin (n + 1) → K) (hy0 : y 0 = 1) (hy1 : ev s = y 1)
    (jv : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1))
    (ξ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1) → R)
    (hξ : ∀ v ν, algebraMap R F' (ξ v ν) = x' ν / x' (jv v))
    (hyξ : ∀ v ν, ev (ξ v ν) = y ν / y (jv v))
    (hjv : ∀ v ν, normalizedAbs v (ev (ξ v ν)) ≤ 1) (iStar : ℕ) :
    ∑ᶠ v, ⨆ p : iStar.Partition, (p.parts.map fun i => ⨆ ν, Real.log (normalizedAbs v
        (PowerSeries.constantCoeff (Faltings.PowerSeries.dividedDerivative K i
          (E (ξ v ν)))))).sum ≤
      iStar * ((∑ P ∈ pairSet n, 2 * pairConstA (G₀ P.1 P.2) N + 7 * Real.log (2 * N)) +
        (∑ P ∈ pairSet n, 4 * pairConstB (G₀ P.1 P.2) N) *
          (Height.logHeight y / finrank ℚ K)) := by
  set T := fun v => stepBound G₀ N (y 1) y v
  have hT0 : ∀ v, 0 ≤ T v := fun v => stepBound_nonneg G₀ hN1 _ y v
  have hloc : ∀ v, (⨆ p : iStar.Partition, (p.parts.map fun i => ⨆ ν, Real.log (normalizedAbs v
      (PowerSeries.constantCoeff (Faltings.PowerSeries.dividedDerivative K i
        (E (ξ v ν)))))).sum) ≤ iStar * T v := by
    intro v
    have : Nonempty iStar.Partition := ⟨Nat.Partition.indiscrete iStar⟩
    refine ciSup_le fun p => ?_
    have hle : ∀ i ∈ p.parts, (⨆ ν, Real.log (normalizedAbs v (PowerSeries.constantCoeff
        (Faltings.PowerSeries.dividedDerivative K i (E (ξ v ν)))))) ≤ (i : ℝ) * T v := by
      intro i hi
      refine ciSup_le fun ν => ?_
      have := log_absV_coeff_le_stepBound hinj cst hcst ev E hE0 hEc ς hEς hEp x' ht s hs hς
        G₀ hG hdisc hdeg1 hN hN1 y (jv v) (ξ v) (hξ v) (hyξ v) v (hjv v) ν (p.parts_pos hi)
      rwa [hy1] at this
    refine (Multiset.sum_map_le_sum_map _ _ hle).trans_eq ?_
    rw [Multiset.sum_map_mul_right, ← Nat.cast_multiset_sum]
    simp only [p.parts_sum]
  have hTfin : HasFiniteSupport fun v => (iStar : ℝ) * T v :=
    Set.Finite.subset (hasFiniteSupport_stepBound G₀ N (y 1) y)
      (Function.support_mul_subset_right _ _)
  have hsum : ∑ᶠ v, ⨆ p : iStar.Partition, (p.parts.map fun i => ⨆ ν, Real.log (normalizedAbs v
      (PowerSeries.constantCoeff (Faltings.PowerSeries.dividedDerivative K i
        (E (ξ v ν)))))).sum ≤ iStar * ∑ᶠ v, T v := by
    rw [mul_finsum]
    by_cases hfin : HasFiniteSupport fun v => ⨆ p : iStar.Partition, (p.parts.map fun i =>
        ⨆ ν, Real.log (normalizedAbs v (PowerSeries.constantCoeff
          (Faltings.PowerSeries.dividedDerivative K i (E (ξ v ν)))))).sum
    · exact finsum_le_finsum' hfin hTfin hloc
    · rw [finsum_of_infinite_support hfin]
      exact finsum_nonneg fun v => mul_nonneg (Nat.cast_nonneg _) (hT0 v)
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact finsum_stepBound_le G₀ hN y hy0

end PartOne

section SchemeLayer

universe w

/-- The `K`-algebra structure of `K(C)` factors through the constants of a stalk. -/
private lemma algebraMap_functionField_eq {K : Type w} [Field K] {C : Scheme.{w}}
    (fK : C ⟶ Spec (.of K)) [IsCurve K fK] (x : C) (a : K) :
    @algebraMap K C.functionField _ _ (functionFieldAlgebra K fK) a =
      algebraMap (C.presheaf.stalk x) C.functionField
        (((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫ C.presheaf.germ ⊤ x trivial).hom a) := by
  have h : C.presheaf.germ ⊤ x trivial ≫
      C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes (Set.mem_univ x)) =
      C.germToFunctionField ⊤ := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← h]
  rfl

/-- The pull-back of rational functions along a dominant morphism is compatible with germs of
sections over an open set. -/
private lemma functionFieldMap_germ {X Y : Scheme.{w}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y)
    [IsDominant π] (V : Y.Opens) (hV : genericPoint Y ∈ V) (hV' : genericPoint X ∈ π ⁻¹ᵁ V)
    (a : Γ(Y, V)) :
    functionFieldMap π ((Y.presheaf.germ V _ hV).hom a) =
      (X.presheaf.germ (π ⁻¹ᵁ V) _ hV').hom (π.app V a) := by
  have h : Y.presheaf.germ V (genericPoint Y) hV ≫
      (Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant π).symm)).hom ≫
        π.stalkMap (genericPoint X) = π.app V ≫ X.presheaf.germ (π ⁻¹ᵁ V) (genericPoint X) hV' := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  exact congrArg (fun f => f.hom a) h

/-- The pull-back of rational functions along a base change square `C_K → C` over
`Spec K → Spec k` is compatible with the constants. -/
public lemma functionFieldMap_algebraMap_of_comp_eq {k K : Type w} [Field k] [Field K]
    [Algebra k K] {C CK : Scheme.{w}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] (fK : CK ⟶ Spec (.of K)) [IsCurve K fK] (π : CK ⟶ C) [IsDominant π]
    (hsq : π ≫ f = fK ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (a : k) :
    functionFieldMap π (@algebraMap k C.functionField _ _ (functionFieldAlgebra k f) a) =
      @algebraMap K CK.functionField _ _ (functionFieldAlgebra K fK) (algebraMap k K a) := by
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ π.appTop =
      CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  simp only [RingHom.algebraMap_toAlgebra]
  exact (functionFieldMap_germ π ⊤ trivial trivial
    ((f.appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))).trans
    (congrArg (fun g => (CK.presheaf.germ ⊤ (genericPoint CK) trivial).hom (g.hom a)) key)

open scoped TensorProduct in
/-- **Linear disjointness from a domain tensor product**: if `F ⊗_k K` is a domain and
`K / k` is finite, then a `k`-basis of `K` stays independent over `F` inside any field `F'`
containing both. -/
public lemma eq_zero_of_sum_algebraMap_mul_eq_zero {k K F F' : Type*} [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [Field F] [Algebra k F] [Field F'] [Algebra K F']
    [Algebra k F'] [IsScalarTower k K F'] [IsDomain (F ⊗[k] K)] (β : F →ₐ[k] F')
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k K) (f : ι → F)
    (h : ∑ r, algebraMap K F' (b r) * β (f r) = 0) : ∀ r, f r = 0 := by
  let ψ : F ⊗[k] K →ₐ[k] F' :=
    Algebra.TensorProduct.lift β (IsScalarTower.toAlgHom k K F') fun _ _ => Commute.all _ _
  have hinj : Function.Injective ψ := by
    have hI : (RingHom.ker (ψ : F ⊗[k] K →+* F')).comap (algebraMap F (F ⊗[k] K)) = ⊥ := by
      rw [RingHom.comap_ker]
      refine (RingHom.injective_iff_ker_eq_bot _).1 ?_
      have : (ψ : F ⊗[k] K →+* F').comp (algebraMap F (F ⊗[k] K)) = (β : F →+* F') := by
        ext x
        simp [ψ, Algebra.TensorProduct.algebraMap_apply]
      rw [this]
      exact β.toRingHom.injective
    have : Algebra.IsIntegral F (F ⊗[k] K) := Algebra.IsIntegral.of_finite F _
    exact (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hI)
  have h0 : ∑ r, f r ⊗ₜ[k] b r = 0 := by
    apply hinj
    rw [map_sum, map_zero, ← h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [ψ, mul_comm]
  set B := Algebra.TensorProduct.basis F b
  have h1 : ∑ r, f r • B r = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact Fintype.linearIndependent_iff.1 B.linearIndependent f h1

open scoped TensorProduct in
/-- The function field of a geometrically integral curve over a field of characteristic zero
stays a domain after tensoring with any field extension. -/
public theorem isDomain_functionField_tensor (k : Type w) [Field k] [CharZero k]
    {C : Scheme.{w}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [GeometricallyIntegral f] (L : Type w) [Field L] [Algebra k L] :
    letI := functionFieldAlgebra k f
    IsDomain (C.functionField ⊗[k] L) := by
  let := functionFieldAlgebra k f
  let : Algebra k (C.residueField (genericPoint C)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.Γevaluation (genericPoint C)).hom.toAlgebra
  have hgi : Algebra.IsGeometricallyIrreducible k (C.residueField (genericPoint C)) :=
    ((geometricallyIrreducible_tfae_functionField k C f (genericPoint C)
      (genericPoint_spec C)).out 1 2).mp (inferInstance : GeometricallyIrreducible f)
  let e : C.functionField ≃ₐ[k] C.residueField (genericPoint C) :=
    { RingEquiv.ofBijective (IsLocalRing.residue C.functionField)
        ⟨(IsLocalRing.residue C.functionField).injective, IsLocalRing.residue_surjective⟩ with
      commutes' := fun r => rfl }
  rw [isDomain_iff_irreducibleSpace_and_isReduced]
  refine ⟨?_, ?_⟩
  · have := (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct
      k _).mp hgi L
    let e' := (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := k) (A₁ := L))).toRingEquiv
    let h := PrimeSpectrum.homeomorphOfRingEquiv e'
    exact h.symm.surjective.irreducibleSpace h.symm.continuous
  · have h := (Algebra.isGeometricallyReduced_tfae k 1 C.functionField k
      (AlgebraicClosure k)).out 3 5
    have h3 : IsReduced (k ⊗[k] C.functionField) :=
      isReduced_of_injective (Algebra.TensorProduct.lid k C.functionField).toRingEquiv.toRingHom
        (Algebra.TensorProduct.lid k C.functionField).injective
    have := h.mp h3 L
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm k C.functionField L).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm k _ _).injective

end SchemeLayer

/-! ### Part I on the base change -/

section PartOneScheme

open Polynomial

/-- Evaluation at a `K`-point kills exactly the maximal ideal of the stalk. -/
private lemma ker_stalkClosedPointTo {K : Type u} [Field K] {X : Scheme.{u}} (z : Spec (.of K) ⟶ X)
    (c : K →+* X.presheaf.stalk (z (IsLocalRing.closedPoint K)))
    (hc : ∀ a, (Scheme.stalkClosedPointTo z).hom (c a) = a)
    (g : X.presheaf.stalk (z (IsLocalRing.closedPoint K))) :
    (Scheme.stalkClosedPointTo z).hom g = 0 ↔ g ∈ IsLocalRing.maximalIdeal _ := by
  rw [← RingHom.mem_ker, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
    fun a => ⟨_, hc a⟩)]

/-- **Unpacking `z ∉ Z`**: outside the exceptional set, `ς = ξ₁₀ - ξ₁₀(z)` generates the maximal
ideal, and the discriminants of the plane relations do not vanish at `ξ₁₀(z)`. -/
private lemma of_notMem_exceptionalSet {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) [IsCurve K f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (x : Fin (n + 1) → C.functionField)
    (ht : letI := functionFieldAlgebra K f; Transcendental K (x 1 / x 0))
    (z : Spec (.of K) ⟶ C) (hzf : z ≫ f = 𝟙 _) (hz : z ∉ exceptionalSet K f D x ht)
    (hc : ∀ a, (Scheme.stalkClosedPointTo z).hom
      (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.presheaf.germ ⊤ (z (IsLocalRing.closedPoint K)) trivial).hom a) = a)
    (s : C.presheaf.stalk (z (IsLocalRing.closedPoint K)))
    (hs : algebraMap _ C.functionField s = x 1 / x 0) :
    letI := functionFieldAlgebra K f
    let c := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.presheaf.germ ⊤ (z (IsLocalRing.closedPoint K)) trivial).hom
    let ev := (Scheme.stalkClosedPointTo z).hom
    IsLocalRing.maximalIdeal _ = Ideal.span {s - c (ev s)} ∧
      ∀ ν j : Fin (n + 1), (ν, j) ∈ pairSet n →
        ((Faltings.FunctionField.planeRelation K (x 1 / x 0) (x ν / x j) ht).resultant
          (Polynomial.derivative (Faltings.FunctionField.planeRelation K (x 1 / x 0)
            (x ν / x j) ht))
          (Faltings.FunctionField.planeRelation K (x 1 / x 0) (x ν / x j) ht).natDegree
          ((Faltings.FunctionField.planeRelation K (x 1 / x 0) (x ν / x j) ht).natDegree -
            1)).eval (ev s) ≠ 0 := by
  intro c ev
  let := functionFieldAlgebra K f
  have hinj : Function.Injective (algebraMap (C.presheaf.stalk (z (IsLocalRing.closedPoint K)))
      C.functionField) := IsFractionRing.injective _ _
  have hmem : s - c (ev s) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← ker_stalkClosedPointTo z c hc, map_sub, hc, sub_self]
  have hz' := hz
  simp only [exceptionalSet, Set.mem_ofPred_eq, not_and, not_or] at hz'
  obtain ⟨h1, h2, h3, _⟩ := hz' hzf
  refine ⟨?_, ?_⟩
  · by_contra hne
    apply h2 h1
    intro g hg a ha
    have hgs : g = s := hinj (hg.trans hs.symm)
    subst hgs
    have ha' : a = ev g := by
      have : g - c a ∈ IsLocalRing.maximalIdeal _ := by
        rw [ha]; exact Ideal.mem_span_singleton_self _
      rw [← ker_stalkClosedPointTo z c hc, map_sub, hc, sub_eq_zero] at this
      exact this.symm
    subst ha'
    exact hne ha
  · intro ν j hP hdisc
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    exact h3 h1 ⟨ν, j, hP.1, hP.2.1, hP.2.2, s, hs, ev s, hmem, hdisc⟩

private lemma planeRelation_congr {K F : Type*} [Field K] [Field F] [Algebra K F] {t t' z z' : F}
    (h1 : t = t') (h2 : z = z') (ht : Transcendental K t) (ht' : Transcendental K t') :
    Faltings.FunctionField.planeRelation K t z ht =
      Faltings.FunctionField.planeRelation K t' z' ht' := by
  subst h1 h2; rfl

/-- **Part I on the curve**: the left side of the lemma is at most `i* (A₀ + A₁ h(y))` for the
vector `y` of the values `ξ_{a0}(z)`, with `A₀, A₁` independent of the number field `K`. -/
private lemma exists_partOne {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (N : ℕ)
    {n : ℕ} (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K]
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
        (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsIntegral CK] [IsLocallyNoetherian CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K fK; Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ)
        (zK : Spec (.of K) ⟶ CK) (_hzK : zK ≫ fK = 𝟙 _)
        (_hz : zK ∉ exceptionalSet K fK DK xK hξ₁₀),
      let ev : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)) →+* K :=
        (Scheme.stalkClosedPointTo zK).hom
      let c : K →+* CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
          CK.presheaf.germ ⊤ (zK (IsLocalRing.closedPoint K)) trivial).hom
      ∀ (s : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hs : algebraMap _ CK.functionField s = xK 1 / xK 0)
        (jv : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1))
        (ξ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1) →
          CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hξ : ∀ v ν, algebraMap _ CK.functionField (ξ v ν) = xK ν / xK (jv v))
        (_hjv : ∀ v ν, normalizedAbs v (ev (ξ v ν)) ≤ 1)
        (g : Fin (n + 1) → CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hg : ∀ a, algebraMap _ CK.functionField (g a) = xK a / xK 0),
      letI : CK.Over (Spec (.of K)) := ⟨fK⟩
      let ς := s - c (ev s)
      ∀ iStar : ℕ,
        ∑ᶠ v, ⨆ p : iStar.Partition,
            (p.parts.map fun i => ⨆ ν, Real.log (normalizedAbs v (_root_.PowerSeries.constantCoeff
              (Faltings.PowerSeries.dividedDerivative K i
                (_root_.PowerSeries.mk (BombieriVojta.taylorCoeff zK ς (ξ v ν))))))).sum ≤
          iStar * (A₀ + A₁ * (Height.logHeight (fun a => ev (g a)) / finrank ℚ K)) := by
  classical
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  let := functionFieldAlgebra k X.f
  have hβ : ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K]
      (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
      (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      [IsCurve K fK] [IsIntegral CK] [IsDominant π],
      letI : Algebra K CK.functionField := functionFieldAlgebra K fK
      letI : Algebra k CK.functionField :=
        ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
      ∃ β : X.C.functionField →ₐ[k] CK.functionField, ∀ a, β a = functionFieldMap π a := by
    intro K _ _ _ CK fK π hπ _ _ _
    let : Algebra K CK.functionField := functionFieldAlgebra K fK
    let : Algebra k CK.functionField :=
      ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
    exact ⟨{ functionFieldMap π with
      commutes' := fun a => functionFieldMap_algebraMap_of_comp_eq X.f fK π hπ.w a }, fun _ => rfl⟩
  by_cases htk : Transcendental k (x 1 / x 0)
  swap
  · refine ⟨0, 0, le_rfl, ?_⟩
    intro K _ _ _ CK fK π hπ _ _ _ _ xK hξ₁₀
    exfalso
    let : Algebra K CK.functionField := functionFieldAlgebra K fK
    let : Algebra k CK.functionField :=
      ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
    have : IsScalarTower k K CK.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨β, hβ'⟩ := hβ K CK fK π hπ
    apply hξ₁₀
    have h := ((not_not.1 htk).algHom β).tower_top K
    rwa [hβ', map_div₀] at h
  set G₀ : Fin (n + 1) → Fin (n + 1) → k[X][X] := fun ν j =>
    Faltings.FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) htk with hG₀
  set Nd : ℕ := ∑ P ∈ pairSet n, degBound (G₀ P.1 P.2) + 1
  have hNd : ∀ ν j, (ν, j) ∈ pairSet n → degBound (G₀ ν j) < Nd := fun ν j h => by
    have := Finset.single_le_sum (f := fun P : Fin (n + 1) × Fin (n + 1) =>
      degBound (G₀ P.1 P.2)) (fun _ _ => Nat.zero_le _) h
    simp only at this
    omega
  have hNd1 : 1 ≤ Nd := by omega
  have hint : ∀ w : X.C.functionField, IsIntegral (IntermediateField.adjoin k {x 1 / x 0}) w := by
    have hnot : x 1 / x 0 ∉ Set.range (algebraMap k X.C.functionField) := by
      rintro ⟨a, ha⟩; exact htk (ha ▸ isAlgebraic_algebraMap a)
    have hfin := (Faltings.FunctionField.finrank_adjoin_eq_finsum_ord k X.f (x 1 / x 0) hnot).1
    exact fun w => @IsIntegral.of_finite _ _ _ _ _ hfin w
  have hdeg1 : ∀ ν j, (ν, j) ∈ pairSet n → 1 ≤ (G₀ ν j).natDegree := fun ν j _ =>
    one_le_natDegree_planeRelation _ _ htk (hint _)
  refine ⟨∑ P ∈ pairSet n, 2 * pairConstA (G₀ P.1 P.2) Nd + 7 * Real.log (2 * Nd),
    ∑ P ∈ pairSet n, 4 * pairConstB (G₀ P.1 P.2) Nd,
    Finset.sum_nonneg fun P _ => mul_nonneg (by norm_num) (pairConstB_nonneg _ _), ?_⟩
  intro K _ _ _ CK fK π hπ _ _ _ _ xK hξ₁₀ DK zK hzK hz ev c s hs jv ξ hξ hjv g hg
  let : CK.Over (Spec (.of K)) := ⟨fK⟩
  intro ς iStar
  let : Algebra K CK.functionField := functionFieldAlgebra K fK
  let : Algebra k CK.functionField :=
    ((algebraMap K CK.functionField).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K CK.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨β, hβ'⟩ := hβ K CK fK π hπ
  have hβx : ∀ a b, β (x a / x b) = xK a / xK b := fun a b => by
    rw [map_div₀, hβ', hβ']
  have := isDomain_functionField_tensor k X.f K
  set b := Module.finBasis k K
  have hLD := fun f hf => eq_zero_of_sum_algebraMap_mul_eq_zero β b f hf
  have hG : ∀ ν j, (ν, j) ∈ pairSet n → Faltings.FunctionField.planeRelation K (xK 1 / xK 0)
      (xK ν / xK j) hξ₁₀ = (G₀ ν j).map (Polynomial.mapRingHom (algebraMap k K)) := by
    intro ν j _
    have h := planeRelation_map_of_linearDisjoint b β hLD (x 1 / x 0) (x ν / x j) htk
      (by rw [hβx]; exact hξ₁₀) (hint _)
    exact (planeRelation_congr (hβx 1 0).symm (hβx ν j).symm _ _).trans h
  have : IsCurve K (CK ↘ Spec (.of K)) := ‹IsCurve K fK›
  have : Smooth (CK ↘ Spec (.of K)) := MorphismProperty.of_isPullback hπ ‹Smooth X.f›
  have : zK.IsOver (Spec (.of K)) := ⟨by
    rw [show (Spec (.of K) ↘ Spec (.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K K))
      from rfl, Algebra.algebraMap_self]
    exact hzK.trans (Spec.map_id _).symm⟩
  have hc : ∀ a, ev (c a) = a := fun a => BombieriVojta.stalkClosedPointTo_constants zK a
  have hinj : Function.Injective (algebraMap (CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
      CK.functionField) := IsFractionRing.injective _ _
  obtain ⟨hς, hdisc⟩ := of_notMem_exceptionalSet fK DK xK hξ₁₀ zK hzK hz hc s hs
  set E := BombieriVojta.taylorCoeffHom zK hς
  have hEp : ∀ (w : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
      (p : MvPolynomial (Fin 2) K),
      MvPolynomial.aeval ![algebraMap _ CK.functionField w, algebraMap _ CK.functionField ς]
        p = 0 → MvPolynomial.aeval ![E w, (_root_.PowerSeries.X : _root_.PowerSeries K)] p = 0 := by
    intro w p hp
    have h := (BombieriVojta.aeval_mk_taylorCoeff_eq_zero zK ς w hς p hp).2
    rwa [BombieriVojta.mk_taylorCoeff zK hς] at h
  have hxK : ∀ a, xK a ≠ 0 := fun a h => (hx.linearIndependent.ne_zero a)
    ((functionFieldMap π).injective (h.trans (map_zero _).symm))
  have hg0 : g 0 = 1 := hinj (by rw [hg, div_self (hxK 0), map_one])
  have hgs : g 1 = s := hinj ((hg 1).trans hs.symm)
  have hξg : ∀ v ν, ξ v ν * g (jv v) = g ν := fun v ν => hinj (by
    rw [map_mul, hξ, hg, hg, div_mul_div_cancel₀ (hxK _)])
  have hyj : ∀ v, ev (g (jv v)) ≠ 0 := fun v h => by
    have := congrArg ev (hξg v 0)
    rw [map_mul, h, mul_zero, hg0, map_one] at this
    exact zero_ne_one this
  have hyξ : ∀ v ν, ev (ξ v ν) = ev (g ν) / ev (g (jv v)) := fun v ν => by
    rw [eq_div_iff (hyj v), ← map_mul, hξg]
  have hmain := finsum_iSup_le_partOne hinj c
    (fun a => (algebraMap_functionField_eq fK _ a).symm) ev E
    (BombieriVojta.constantCoeff_taylorCoeffHom zK hς)
    (BombieriVojta.taylorCoeffHom_constants zK hς) ς
    (BombieriVojta.taylorCoeffHom_uniformizer zK hς) hEp xK hξ₁₀ s hs rfl G₀ hG hdisc hdeg1
    hNd hNd1 (fun a => ev (g a)) (by simp only [hg0, map_one]) (by simp only [hgs]) jv ξ hξ hyξ
    hjv iStar
  have hmk : ∀ w, _root_.PowerSeries.mk (BombieriVojta.taylorCoeff zK ς w) = E w :=
    fun w => BombieriVojta.mk_taylorCoeff zK hς w
  simp only [hmk]
  exact hmain

end PartOneScheme

/-! ### Part II: the embedding `φ_{NP}` read on the basis `x` -/

section NPData

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

set_option backward.isDefEq.respectTransparency false in
/-- **The value of a section at a point of an open subscheme**: evaluating the germ of
`r ∈ Γ(X, U)` at a local-ring point `q = q' ≫ ι_U` is evaluating `r` on `U` along `q'`. -/
private lemma stalkClosedPointTo_germ_eq {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
    (U : X.Opens) (q' : Spec R ⟶ U.toScheme) (q : Spec R ⟶ X) (hq : q' ≫ U.ι = q)
    (r : Γ(X, U)) (hU : q (IsLocalRing.closedPoint R) ∈ U) :
    (Scheme.stalkClosedPointTo q).hom (X.presheaf.germ U _ hU r) =
      (Scheme.ΓSpecIso R).hom (q'.appTop (U.topIso.inv r)) := by
  subst hq
  rw [Scheme.stalkClosedPointTo_comp]
  have e1 : (X.presheaf.germ U _ hU).hom r = (X.presheaf.germ (U.ι ''ᵁ ⊤)
      (U.ι (q' (IsLocalRing.closedPoint R))) ⟨_, trivial, rfl⟩).hom (U.topIso.inv r) := by
    simp only [Scheme.Opens.topIso_inv]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [e1, ← Scheme.Opens.stalkIso_inv, CommRingCat.comp_apply]
  have e4 := congrArg (fun f => f.hom (U.topIso.inv r))
    (Scheme.Opens.germ_stalkIso_inv U ⊤ (q' (IsLocalRing.closedPoint R)) trivial)
  simp only [CommRingCat.comp_apply] at e4
  erw [e4]
  have e2 := Scheme.germ_stalkClosedPointTo q' ⊤ trivial
  have e3 := congrArg (fun f => f.hom (U.topIso.inv r)) e2
  simp only [CommRingCat.comp_apply] at e3
  erw [e3]
  simp [Scheme.Hom.appTop]

end NPData

/-! ### Part II: the height of `z` and the Néron norm -/

section PartTwo

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- **Part II**: the height of the vector `y` of values `ξ_{a0}(z)` is at most `B₀ + B₁ |z|²`,
with `B₀, B₁` independent of the number field `K`. -/
private lemma exists_partTwo {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (Kbar : Type u) [Field Kbar] [Algebra k Kbar] [IsAlgClosure k Kbar]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x) :
    ∃ B₀ B₁ : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] Kbar)
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
        (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsIntegral CK] [IsLocallyNoetherian CK] [IsDominant π]
        (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)
        (zK : Spec (.of K) ⟶ CK) (_hzK : zK ≫ fK = 𝟙 _) (_hzC : zK ≫ π = z.left)
        (zbar : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Kbar))) ⟶ Over.mk X.f)
        (_hzbar : zbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ z.left)
        (g : Fin (n + 1) → CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hg : ∀ a, algebraMap _ CK.functionField (g a) =
          functionFieldMap π (x a) / functionFieldMap π (x 0)),
      Height.logHeight (fun a => (Scheme.stalkClosedPointTo zK).hom (g a)) / finrank ℚ K ≤
        B₀ + B₁ * √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
          (.ofMul (zbar ≫ j)) (.ofMul (zbar ≫ j))) ^ 2 := by
  classical
  let : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  obtain ⟨L, hLinv, hL, s₀, hs₀, h, b, hh, hb⟩ := exists_basis_genericCoord_eq X N x hx
  obtain ⟨-, hgen, hci, α, hα, -⟩ := X.isClosedImmersion_toProjectiveSpaceOver N hN L hL b
  obtain ⟨cNP, hcNP⟩ := exists_abs_weilHeight_sub_neronPairing_le X A hg j hj D hrad hsupp N hN
    (Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen X.f)
    (Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst _ _ _)
    (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ L _ _).mpr
      ⟨(Scheme.Modules.pullbackComp
          (Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen X.f)
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).app
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≪≫
          @asIso _ _ _ _ α hα⟩).trans hL) Kbar
  refine ⟨2 * |cNP|, N / (2 * genus X.f) + |cNP|, ?_⟩
  intro K _ _ _ ι CK fK π hπ _ _ _ _ z zK hzK hzC zbar hzbar g hg'
  set ev := (Scheme.stalkClosedPointTo zK).hom
  set q := zK ≫ π with hqdef
  obtain ⟨i₀, hi₀⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks (⇑b)
    hgen (q (IsLocalRing.closedPoint K))
  set U := Stacks.ProjectiveFromSections.nvCover (⇑b) i₀
  have hrange : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]
  set q' := IsOpenImmersion.lift U.ι q hrange
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  set w : Fin (n + 1) → K := fun i => (Scheme.ΓSpecIso (.of K)).hom
    (q'.appTop (Stacks.ProjectiveFromSections.chartRatio (⇑b) i₀ i))
  have hw0 : w i₀ = 1 := by
    simp only [w, Stacks.ProjectiveFromSections.chartRatio_self, map_one]
  have hwspan : Ideal.span (Set.range w) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩) (by rw [hw0]; exact isUnit_one)
  have hgs : Ideal.span (Set.range fun i =>
      q'.appTop (Stacks.ProjectiveFromSections.chartRatio (⇑b) i₀ i)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩) (by
      simp only [Stacks.ProjectiveFromSections.chartRatio_self, map_one]; exact isUnit_one)
  have hpt : q ≫ Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse (⇑b) hgen =
      projectiveSpacePoint (R := .of K) w hwspan := by
    rw [← hq', Category.assoc, Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse,
      Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality q' _ _ hgs, projectiveSpacePoint]
    exact Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
      (funext fun i => by simp [w]) _ _
  have hιspan : Ideal.span (Set.range fun i => (CommRingCat.ofHom (ι : K →+* Kbar)) (w i)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i₀, rfl⟩) (by
      simp only [hw0, map_one]; exact isUnit_one)
  have hZ : zbar.left ≫ Stacks.ProjectiveFromSections.toProjectiveSpaceOver (⇑b) hgen X.f ≫
      projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      projectiveSpacePoint (R := .of Kbar) (fun i => (CommRingCat.ofHom (ι : K →+* Kbar)) (w i))
        hιspan := by
    rw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd, hzbar, ← hzC, Category.assoc,
      hpt]
    exact specMap_comp_projectiveSpacePoint (R := CommRingCat.of K) (S := CommRingCat.of Kbar)
      (CommRingCat.ofHom (ι : K →+* Kbar)) w hwspan hιspan
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.C.sheaf.obj
      X.C.ringCatSheaf.property L :=
    (show Stacks.SheafOfModules.IsInvertible X.C.presheaf X.C.ringCatSheaf.2 L
      from hLinv).toAlgebraicGeometry
  have hinj : Function.Injective (algebraMap (CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
      CK.functionField) := IsFractionRing.injective _ _
  have hη : genericPoint X.C ∈ U :=
    ((genericPoint_spec X.C).mem_open_set_iff U.isOpen).2 ⟨_, trivial, hi₀⟩
  have hη' : genericPoint CK ∈ π ⁻¹ᵁ U := by
    change π (genericPoint CK) ∈ U
    rw [map_genericPoint_of_isDominant]; exact hη
  have hzU : zK (IsLocalRing.closedPoint K) ∈ π ⁻¹ᵁ U := hi₀
  let := functionFieldAlgebra k X.f
  have hx0 : ∀ a, x a ≠ 0 := hx.linearIndependent.ne_zero
  have hxK : ∀ a, functionFieldMap π (x a) ≠ 0 := fun a hz =>
    hx0 a ((functionFieldMap π).injective (hz.trans (map_zero _).symm))
  have hgerm : ∀ i, (X.C.presheaf.germ U _ hη).hom (Stacks.ProjectiveFromSections.ratio (⇑b) i₀ i) =
      x i / x i₀ := by
    intro i
    have := germ_ratio_mul_genericCoord L s₀ hs₀ (⇑b) i₀ i hη
    rw [hb, hb] at this
    rw [eq_div_iff (hx0 i₀)]
    exact mul_left_cancel₀ hh (by rw [← this]; ring)
  have hval : ∀ i, w i * ev (g i₀) = ev (g i) := by
    intro i
    set r := Stacks.ProjectiveFromSections.ratio (⇑b) i₀ i
    set R := (CK.presheaf.germ (π ⁻¹ᵁ U) _ hzU).hom (π.app U r)
    have h1 : w i = ev R := by
      have e1 : w i = (Scheme.stalkClosedPointTo q).hom ((X.C.presheaf.germ U _ hi₀).hom r) :=
        (stalkClosedPointTo_germ_eq U q' q hq' r hi₀).symm
      refine e1.trans ?_
      have := congrArg (fun f => f.hom ((X.C.presheaf.germ U _ hi₀).hom r))
        (Scheme.stalkClosedPointTo_comp zK π)
      refine this.trans ?_
      have e3 := congrArg (fun f => f.hom r) (Scheme.Hom.germ_stalkMap π U _ hzU)
      simp only [CommRingCat.comp_apply] at e3
      exact congrArg ev e3
    have h2 : algebraMap _ CK.functionField R =
        functionFieldMap π (x i) / functionFieldMap π (x i₀) := by
      have e2 : algebraMap _ CK.functionField R =
          (CK.presheaf.germ (π ⁻¹ᵁ U) _ hη').hom (π.app U r) := by
        change (CK.presheaf.stalkSpecializes _).hom
          ((CK.presheaf.germ (π ⁻¹ᵁ U) _ hzU).hom (π.app U r)) = _
        rw [← CommRingCat.comp_apply]
        erw [TopCat.Presheaf.germ_stalkSpecializes]
      rw [e2, ← functionFieldMap_germ π U hη hη', hgerm, map_div₀]
    have h3 : R * g i₀ = g i := hinj (by
      rw [map_mul, h2, hg', hg', div_mul_div_cancel₀ (hxK i₀)])
    rw [h1, ← map_mul, h3]
  have hg0 : g 0 = 1 := hinj (by rw [hg', div_self (hxK 0), map_one])
  have hy0 : ev (g 0) = 1 := by rw [hg0, map_one]
  have hyi : ev (g i₀) ≠ 0 := fun h0 => by
    have := hval 0
    rw [h0, mul_zero, hy0] at this
    exact zero_ne_one this
  have hyw : (fun a => ev (g a)) = ev (g i₀) • w :=
    funext fun a => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hval]
  have hlog : Height.logHeight (fun a => ev (g a)) = Height.logHeight w := by
    rw [hyw, Height.logHeight_smul_eq_logHeight _ hyi]
  have hc0 : (fun i => (CommRingCat.ofHom (ι : K →+* Kbar)) (w i)) ≠ 0 := fun h0 => by
    have := congrFun h0 i₀
    simp only [hw0, map_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have hwne : w ≠ 0 := fun h0 => by
    have := congrFun h0 i₀
    rw [hw0, Pi.zero_apply] at this
    exact one_ne_zero this
  have hbd := hcNP zbar _ hc0 hZ
  have : CharZero Kbar := charZero_of_injective_algebraMap (algebraMap k Kbar).injective
  let : Algebra ℚ Kbar := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ Kbar := Algebra.IsAlgebraic.trans ℚ k Kbar
  let : Algebra K Kbar := (ι : K →+* Kbar).toAlgebra
  have hW := weilHeight_eq_sumLocalHeight (F := K) (y := w)
    (x := Projectivization.mk Kbar (fun i => (CommRingCat.ofHom (ι : K →+* Kbar)) (w i)) hc0)
    hc0 rfl
  rw [hW, sumLocalHeight_eq_finsum_absV, finsum_log_iSup_absV hwne] at hbd
  simp only at hbd
  rw [hlog]
  set nrm := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
    (.ofMul (zbar ≫ j)) (.ofMul (zbar ≫ j)))
  have hn : 0 ≤ nrm := Real.sqrt_nonneg _
  have h1 := (abs_le.1 hbd).2
  have h2 : cNP * (1 + nrm) ≤ |cNP| * (1 + nrm) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  nlinarith [abs_nonneg cNP, sq_nonneg (nrm - 1), mul_nonneg (abs_nonneg cNP) (sq_nonneg (nrm - 1))]

end PartTwo

/-- **Bound for the Taylor-coefficient term.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over
a number field `k` with a divisor `P` of degree one, `A` a Jacobian with Abel–Jacobi map `j`, `D`
the reduced theta divisor, `Kbar` an algebraic closure of `k`, `N ≥ 2g + 1` and `x` a generic basis
of `L(N P)`. There are constants `c₈, c₉` such that for every number field `K ⊇ k` with a
`k`-embedding `ι : K → Kbar`, every `K`-point `z` of `C` outside the exceptional set (read on the
base change `C_K`, through the `K`-point `z_K` over `z`) satisfies the following, with
`|z| = √⟨j zbar, j zbar⟩` the Néron norm of the point `zbar ∈ C(Kbar)` over `z`. Put
`ς = ξ₁₀ - ξ₁₀(z)`, and for each place `v` of `K` let `j_v` be an index with
`|ξ_{ν j_v}(z)|_v ≤ 1` for all `ν`.
Then for every `i* ≥ 0`, `∑_v` over the places of `K` of the maximum over the partitions
`{i_λ}` of `i*` of `∑_λ max_ν log |∂_{i_λ} ξ_{ν j_v}(0)|_v` is at most `c₈ i* |z|² + c₉ i*`,
where `∂_i ξ(0)` is the `i`-th divided derivative at `0` of the expansion of `ξ` in `K⟦ς⟧`. -/
@[faltings "lem_bvs_taylor_coefficient_bound"]
public theorem exists_finsum_iSup_log_dividedDerivative_le {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (Kbar : Type u) [Field Kbar] [Algebra k Kbar] [IsAlgClosure k Kbar]
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n : ℕ} (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x) :
    ∃ c₈ c₉ : ℝ, ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K] (ι : K →ₐ[k] Kbar)
        (CK : Scheme.{u}) (fK : CK ⟶ Spec (.of K)) (π : CK ⟶ X.C)
        (_hπ : IsPullback π fK X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        [IsCurve K fK] [IsIntegral CK] [IsLocallyNoetherian CK] [IsDominant π],
      let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
      ∀ (hξ₁₀ : letI := functionFieldAlgebra K fK; Transcendental K (xK 1 / xK 0))
        (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
        (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f)
        (zK : Spec (.of K) ⟶ CK) (_hzK : zK ≫ fK = 𝟙 _) (_hzC : zK ≫ π = z.left)
        (_hz : zK ∉ exceptionalSet K fK DK xK hξ₁₀)
        (zbar : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Kbar))) ⟶ Over.mk X.f)
        (_hzbar : zbar.left = Spec.map (CommRingCat.ofHom (ι : K →+* Kbar)) ≫ z.left),
      let ev : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)) →+* K :=
        (Scheme.stalkClosedPointTo zK).hom
      let c : K →+* CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appTop ≫
          CK.presheaf.germ ⊤ (zK (IsLocalRing.closedPoint K)) trivial).hom
      let absV : InfinitePlace K ⊕ FinitePlace K → K → ℝ := fun v y =>
        Sum.elim (fun w : InfinitePlace K => w y ^ ((w.mult : ℝ) / finrank ℚ K))
          (fun w : FinitePlace K => w y ^ ((1 : ℝ) / finrank ℚ K)) v
      ∀ (s : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hs : algebraMap _ CK.functionField s = xK 1 / xK 0)
        (jv : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1))
        (ξ : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1) →
          CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)))
        (_hξ : ∀ v ν, algebraMap _ CK.functionField (ξ v ν) = xK ν / xK (jv v))
        (_hjv : ∀ v ν, absV v (ev (ξ v ν)) ≤ 1),
      letI : CK.Over (Spec (.of K)) := ⟨fK⟩
      let ς := s - c (ev s)
      let coeff : InfinitePlace K ⊕ FinitePlace K → Fin (n + 1) → ℕ → K := fun v ν i =>
        _root_.PowerSeries.constantCoeff
          (Faltings.PowerSeries.dividedDerivative K i
            (_root_.PowerSeries.mk (BombieriVojta.taylorCoeff zK ς (ξ v ν))))
      let norm := √(neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp Kbar
        (.ofMul (zbar ≫ j)) (.ofMul (zbar ≫ j)))
      ∀ iStar : ℕ,
        ∑ᶠ v, ⨆ p : iStar.Partition,
            (p.parts.map fun i => ⨆ ν, Real.log (absV v (coeff v ν i))).sum ≤
          c₈ * iStar * norm ^ 2 + c₉ * iStar := by
  obtain ⟨A₀, A₁, hA₁, hI⟩ := exists_partOne X N x hx
  obtain ⟨B₀, B₁, hII⟩ := exists_partTwo X A hg j hj D hrad hsupp Kbar N hN x hx
  refine ⟨A₁ * B₁, A₀ + A₁ * B₀, ?_⟩
  intro K _ _ _ ι CK fK π hπ _ _ _ _ xK hξ₁₀ DK hDK z zK hzK hzC hz zbar hzbar ev c absV' s hs
    jv ξ hξ hjv
  let : CK.Over (Spec (.of K)) := ⟨fK⟩
  intro ς coeff norm iStar
  have hgerm : ∀ a, ∃ g : CK.presheaf.stalk (zK (IsLocalRing.closedPoint K)),
      algebraMap _ CK.functionField g = xK a / xK 0 := by
    intro a
    let := functionFieldAlgebra K fK
    by_cases ha : a = 0
    · subst ha
      have hx0 : xK 0 ≠ 0 := fun h => hξ₁₀.ne_zero (by rw [h, div_zero])
      exact ⟨1, by rw [map_one, div_self hx0]⟩
    · have hz' := hz
      simp only [exceptionalSet, Set.mem_ofPred_eq, not_and, not_or] at hz'
      obtain ⟨h1, -, -, h4⟩ := hz' hzK
      by_contra hne
      push Not at hne
      exact h4 h1 ⟨a, ha, fun g hg => absurd hg (hne g)⟩
  choose g hg using hgerm
  have h1 := hI K CK fK π hπ hξ₁₀ DK zK hzK hz s hs jv ξ hξ hjv g hg iStar
  have h2 := hII K ι CK fK π hπ z zK hzK hzC zbar hzbar g hg
  have hH : 0 ≤ (iStar : ℝ) := Nat.cast_nonneg _
  calc _ ≤ (iStar : ℝ) * (A₀ + A₁ * (Height.logHeight (fun a => ev (g a)) / finrank ℚ K)) := h1
    _ ≤ (iStar : ℝ) * (A₀ + A₁ * (B₀ + B₁ * norm ^ 2)) := by
        gcongr
    _ = _ := by ring

end Faltings.BombieriSiegel
