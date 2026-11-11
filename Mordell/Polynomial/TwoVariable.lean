module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Norm.FormNorm
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.Curve.Topology
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsTensorProduct
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne

/-!
# Two-variable polynomials: reversal, degree bounds and norms

Over algebraically independent `t, u`: the reversal `t^M H(t⁻¹, u)` is a polynomial with degree
bounds in each variable, integral elements of `k(s, u)` over `k[s, u]` are polynomials, norms of
such elements are polynomials with degree bounds, and bihomogeneous forms dehomogenise.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Faltings.BombieriRoth

open BombieriSiegel BombieriVojta

universe u

section Algebra

open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

/-- Reversal in the first variable: `t ^ M · H(t⁻¹, u)` is the value at `(t, u)` of a polynomial of
degree at most `M = deg_{X₀} H` in `X₀`. -/
public theorem exists_aeval_eq_pow_mul_aeval_inv {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t : L} (ht : t ≠ 0) (u : L) (H : MvPolynomial (Fin 2) k) :
    ∃ H' : MvPolynomial (Fin 2) k, H'.degreeOf 0 ≤ H.degreeOf 0 ∧
      aeval ![t, u] H' = t ^ H.degreeOf 0 * aeval ![t⁻¹, u] H := by
  set M := H.degreeOf 0
  refine ⟨∑ m ∈ H.support, monomial (Finsupp.single 0 (M - m 0) + Finsupp.single 1 (m 1))
    (H.coeff m), ?_, ?_⟩
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m _ => ?_)
    by_cases hc : H.coeff m = 0
    · simp [hc]
    rw [degreeOf_monomial_eq _ _ hc]
    simp
  · conv_rhs => rw [← support_sum_monomial_coeff H]
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m 0 ≤ M := monomial_le_degreeOf 0 hm
    rw [aeval_monomial, aeval_monomial]
    have hprod : ∀ (v : L) (n : Fin 2 →₀ ℕ),
        n.prod (fun i k => (![v, u] i) ^ k) = v ^ n 0 * u ^ n 1 := by
      intro v n
      rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      rfl
    rw [hprod, hprod]
    simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.isValue, ↓reduceIte, one_ne_zero,
      zero_ne_one, add_zero, zero_add, inv_pow]
    rw [show t ^ M = t ^ (M - m 0) * t ^ (m 0) by rw [← pow_add, Nat.sub_add_cancel hm0]]
    field_simp

/-- If `t, u` are algebraically independent and `G(t, u) = t ^ c · H(t⁻¹, u)`, then
`deg_{X₀} G ≤ c`. -/
public theorem degreeOf_zero_le_of_aeval_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t u : L} (ht : t ≠ 0)
    (hinj : Function.Injective (aeval ![t, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    {G H : MvPolynomial (Fin 2) k} {c : ℕ}
    (h : aeval ![t, u] G = t ^ c * aeval ![t⁻¹, u] H) : G.degreeOf 0 ≤ c := by
  obtain ⟨H', hH'deg, hH'⟩ := exists_aeval_eq_pow_mul_aeval_inv (k := k) ht u H
  set M := H.degreeOf 0
  have heq : X 0 ^ M * G = X 0 ^ c * H' := by
    apply hinj
    simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, h, hH']
    ring
  by_cases hG : G = 0
  · simp [hG]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image G.support (fun m => m 0)
    (support_nonempty.mpr hG)
  have hdeg : G.degreeOf 0 = m 0 := by
    rw [degreeOf_eq_sup]
    exact le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := fun m => m 0) hm)
  have hcoeff : (X 0 ^ M * G).coeff (Finsupp.single 0 M + m) ≠ 0 := by
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact mem_support_iff.mp hm
  have h1 := monomial_le_degreeOf 0 (mem_support_iff.mpr hcoeff)
  rw [heq] at h1
  have h2 := (degreeOf_mul_le 0 (X 0 ^ c : MvPolynomial (Fin 2) k) H').trans
    (add_le_add (show degreeOf 0 (X 0 ^ c : MvPolynomial (Fin 2) k) ≤ c by
      rw [X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]; simp) hH'deg)
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h1
  omega

/-- If `s, u` are algebraically independent over `k`, an element of `k(s, u)` integral over
`k[s, u]` is a polynomial in `s, u`. -/
public theorem exists_aeval_eq_of_isIntegral {k L : Type*} [Field k] [Field L] [Algebra k L]
    {s u : L} (hinj : Function.Injective (aeval ![s, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    {w : L} (hw : w ∈ IntermediateField.adjoin k {s, u})
    (hint : IsIntegral (Algebra.adjoin k {s, u}) w) :
    ∃ G : MvPolynomial (Fin 2) k, aeval ![s, u] G = w := by
  set A := Algebra.adjoin k ({s, u} : Set L)
  have hA : A = (aeval ![s, u] : MvPolynomial (Fin 2) k →ₐ[k] L).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty]
    rfl
  let e : MvPolynomial (Fin 2) k ≃ₐ[k] A :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hA.symm)
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : IsScalarTower A (IntermediateField.adjoin k {s, u}) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hintE : IsIntegral A (⟨w, hw⟩ : IntermediateField.adjoin k {s, u}) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (IntermediateField.adjoin k {s, u}) L)
      (algebraMap (IntermediateField.adjoin k {s, u}) L).injective).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintE
  refine ⟨e.symm a, ?_⟩
  have h1 : (e (e.symm a) : L) = a := by rw [e.apply_symm_apply]
  exact h1.trans (congrArg Subtype.val ha)

/-- The variant of `degreeOf_zero_le_of_aeval_eq` in the second variable. -/
public theorem degreeOf_one_le_of_aeval_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t u : L} (hu : u ≠ 0)
    (hinj : Function.Injective (aeval ![t, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    {G H : MvPolynomial (Fin 2) k} {c : ℕ}
    (h : aeval ![t, u] G = u ^ c * aeval ![t, u⁻¹] H) : G.degreeOf 1 ≤ c := by
  have hsw : ∀ (a b : L) (P : MvPolynomial (Fin 2) k),
      aeval ![b, a] (rename (Equiv.swap 0 1) P) = aeval ![a, b] P := by
    intro a b P
    have : (![b, a] ∘ Equiv.swap (0 : Fin 2) 1) = ![a, b] := by
      funext i
      fin_cases i <;> rfl
    rw [aeval_rename, this]
  have hinj' : Function.Injective (aeval ![u, t] : MvPolynomial (Fin 2) k →ₐ[k] L) := by
    intro P Q hPQ
    have : rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap 0 1) P) =
        rename (Equiv.swap (0 : Fin 2) 1) (rename (Equiv.swap 0 1) Q) := by
      congr 1
      apply hinj
      rw [hsw, hsw, hPQ]
    have hss : (Equiv.swap (0 : Fin 2) 1 ∘ Equiv.swap 0 1) = id := by
      funext i
      simp
    simpa [rename_rename, hss, rename_id] using this
  have h' : aeval ![u, t] (rename (Equiv.swap 0 1) G) =
      u ^ c * aeval ![u⁻¹, t] (rename (Equiv.swap 0 1) H) := by
    rw [hsw, hsw, h]
  have h0 := degreeOf_zero_le_of_aeval_eq hu hinj' h'
  have h1 := degreeOf_rename_of_injective (Equiv.injective (Equiv.swap (0 : Fin 2) 1)) 1 (p := G)
  rw [show Equiv.swap (0 : Fin 2) 1 1 = 0 from rfl] at h1
  omega

/-- The norm to `E = k(s, v)` of an element integral over `k[s, v]`, with `s, v` algebraically
independent, is a polynomial in `s, v`. -/
public theorem exists_aeval_eq_norm {k L : Type*} [Field k] [Field L] [Algebra k L]
    {E : IntermediateField k L} {s v : L}
    (hinj : Function.Injective (aeval ![s, v] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (hE : IntermediateField.adjoin k {s, v} = E) {y : L}
    (hy : IsIntegral (Algebra.adjoin k {s, v}) y) :
    ∃ H : MvPolynomial (Fin 2) k, aeval ![s, v] H = (Algebra.norm E y : L) := by
  subst hE
  have : IsScalarTower (Algebra.adjoin k {s, v}) (IntermediateField.adjoin k {s, v}) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := (Algebra.isIntegral_norm (IntermediateField.adjoin k {s, v}) hy).map
    (IsScalarTower.toAlgHom (Algebra.adjoin k {s, v}) (IntermediateField.adjoin k {s, v}) L)
  exact exists_aeval_eq_of_isIntegral hinj (Algebra.norm (IntermediateField.adjoin k {s, v}) y).2 h1

/-- Replacing `t` by `t⁻¹` does not change the field `k(t, u)`. -/
public theorem adjoin_inv_pair_eq {k L : Type*} [Field k] [Field L] [Algebra k L] (t u : L) :
    IntermediateField.adjoin k {t⁻¹, u} = IntermediateField.adjoin k {t, u} := by
  have ht : t ∈ IntermediateField.adjoin k {t, u} := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u ∈ IntermediateField.adjoin k {t, u} := IntermediateField.subset_adjoin _ _ (by simp)
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
    (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro _ (rfl | rfl)
    exacts [inv_mem ht, hu]
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, IntermediateField.subset_adjoin _ _ (by simp)⟩
    exact inv_inv t ▸ inv_mem (IntermediateField.subset_adjoin _ _ (by simp))

/-- The norm from `L` to an intermediate field `E` of `z · e⁻¹ ^ δ`, for `e ∈ E`, is
`N(z) · (e ^ ([L : E] δ))⁻¹`. -/
public theorem coe_norm_mul_inv_pow {k L : Type*} [Field k] [Field L] [Algebra k L]
    (E : IntermediateField k L) (z : L) (e : E) (δ : ℕ) :
    (Algebra.norm E (z * (e : L)⁻¹ ^ δ) : L) =
      (Algebra.norm E z : L) * ((e : L) ^ (Module.finrank E L * δ))⁻¹ := by
  have : (e : L)⁻¹ ^ δ = algebraMap E L (e⁻¹ ^ δ) := by simp
  rw [this, map_mul, Algebra.norm_algebraMap]
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv,
    ← pow_mul, inv_pow, mul_comm δ]

/-- **The norm of an element integral over `k[t, u]`, `k[t⁻¹, u]` and `k[t, u⁻¹]` after
division by `t ^ δ₁`, resp. `u ^ δ₂`.** If `t, u` are algebraically independent (and so are
`t⁻¹, u` and `t, u⁻¹`), the norm of `z` from `L` to `k(t, u)` is `G(t, u)` for a polynomial `G`
with `deg_{X₀} G ≤ D δ₁` and `deg_{X₁} G ≤ D δ₂`, where `D = [L : k(t, u)]`. -/
public theorem exists_degreeOf_le_aeval_eq_norm {k L : Type*} [Field k] [Field L]
    [Algebra k L] {t u : L} (ht : t ≠ 0) (hu : u ≠ 0)
    (h₁ : Function.Injective (aeval ![t, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (h₂ : Function.Injective (aeval ![t⁻¹, u] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (h₃ : Function.Injective (aeval ![t, u⁻¹] : MvPolynomial (Fin 2) k →ₐ[k] L))
    (δ₁ δ₂ : ℕ) {z : L} (hz : IsIntegral (Algebra.adjoin k {t, u}) z)
    (hz₁ : IsIntegral (Algebra.adjoin k {t⁻¹, u}) (z * t⁻¹ ^ δ₁))
    (hz₂ : IsIntegral (Algebra.adjoin k {t, u⁻¹}) (z * u⁻¹ ^ δ₂)) :
    ∃ G : MvPolynomial (Fin 2) k,
      G.degreeOf 0 ≤ Module.finrank (IntermediateField.adjoin k {t, u}) L * δ₁ ∧
      G.degreeOf 1 ≤ Module.finrank (IntermediateField.adjoin k {t, u}) L * δ₂ ∧
      aeval ![t, u] G = (Algebra.norm (IntermediateField.adjoin k {t, u}) z : L) := by
  have hE₁ := adjoin_inv_pair_eq (k := k) t u
  have hE₂ : IntermediateField.adjoin k {t, u⁻¹} = IntermediateField.adjoin k {t, u} := by
    rw [Set.pair_comm t u⁻¹, adjoin_inv_pair_eq, Set.pair_comm u t]
  set E := IntermediateField.adjoin k ({t, u} : Set L)
  have htE : t ∈ E := IntermediateField.subset_adjoin _ _ (by simp)
  have huE : u ∈ E := IntermediateField.subset_adjoin _ _ (by simp)
  obtain ⟨G, hG⟩ := exists_aeval_eq_norm h₁ rfl hz
  obtain ⟨H₁, hH₁⟩ := exists_aeval_eq_norm h₂ hE₁ hz₁
  obtain ⟨H₂, hH₂⟩ := exists_aeval_eq_norm h₃ hE₂ hz₂
  refine ⟨G, ?_, ?_, hG⟩
  · refine degreeOf_zero_le_of_aeval_eq ht h₁ (H := H₁) ?_
    rw [hH₁, show t = ((⟨t, htE⟩ : E) : L) from rfl, coe_norm_mul_inv_pow, hG]
    field_simp
    rfl
  · refine degreeOf_one_le_of_aeval_eq hu h₁ (H := H₂) ?_
    rw [hH₂, show u = ((⟨u, huE⟩ : E) : L) from rfl, coe_norm_mul_inv_pow, hG]
    field_simp
    rfl

end Algebra

section Evaluation

open MvPolynomial

/-- **Dehomogenisation.** For a bihomogeneous form `F` of bidegree `δ`, scaling the first set of
variables by `c` and the second by `d` multiplies the value by `c ^ δ.1 * d ^ δ.2`. -/
public theorem aeval_sumElim_mul_of_isWeightedHomogeneous {k L ι : Type*} [Field k] [Field L]
    [Algebra k L] {F : MvPolynomial (ι ⊕ ι) k} {δ : ℕ × ℕ}
    (hF : IsWeightedHomogeneous
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) F δ)
    (α β : ι → L) (c d : L) :
    aeval (Sum.elim (fun ν => c * α ν) (fun ν => d * β ν)) F =
      c ^ δ.1 * d ^ δ.2 * aeval (Sum.elim α β) F := by
  set w : ι ⊕ ι → ℕ × ℕ := Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))
  conv_lhs => rw [← support_sum_monomial_coeff F]
  conv_rhs => rw [← support_sum_monomial_coeff F]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight w m = δ := hF (mem_support_iff.mp hm)
  rw [aeval_monomial, aeval_monomial]
  have hg : ∀ i, Sum.elim (fun ν => c * α ν) (fun ν => d * β ν) i =
      (c ^ (w i).1 * d ^ (w i).2) * Sum.elim α β i := by
    rintro (i | i) <;> simp [w]
  have hpow : m.prod (fun i e => (c ^ (w i).1 * d ^ (w i).2) ^ e) =
      c ^ (Finsupp.weight w m).1 * d ^ (Finsupp.weight w m).2 := by
    simp only [mul_pow, Finsupp.prod_mul, ← pow_mul]
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.prod, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum, Finsupp.sum, Prod.fst_sum, Prod.snd_sum]
    simp [mul_comm]
  have hsplit : m.prod (fun i e => (Sum.elim (fun ν => c * α ν) (fun ν => d * β ν) i) ^ e) =
      m.prod (fun i e => (c ^ (w i).1 * d ^ (w i).2) ^ e) *
        m.prod (fun i e => (Sum.elim α β i) ^ e) := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext i e
    rw [hg, mul_pow]
  rw [hsplit, hpow, hw]
  ring

end Evaluation

end Faltings.BombieriRoth
