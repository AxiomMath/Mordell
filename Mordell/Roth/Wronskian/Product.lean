module
public import Mordell.Roth.Wronskian.Basic
public import Mordell.Roth.Wronskian.Roth

/-!
# The Wronskian of a sum of separated products factors: `W = U V`

Let `P = ∑_{j=0}^s φ_j(ς₁, …, ς_{m-1}) ψ_j(ς_m)` be a polynomial over a field of characteristic
zero whose terms separate the first `m - 1` variables from the last one, and let
`I'₀, …, I'_s ∈ ℕ^{m-1}`. Since `∂_{I'_μ}` involves only `ς₁, …, ς_{m-1}` and `∂_ν` only `ς_m`,
`∂_{I'_μ} ∂_ν P = ∑_j (∂_{I'_μ} φ_j)(∂_ν ψ_j)`; the matrix of `W_{I'}(P)` is thus the product of
the matrix of `Wr_{I'_0,…,I'_s}(φ₀, …, φ_s)` and the transpose of that of `Wr(ψ₀, …, ψ_s)`, and
taking determinants gives `W_{I'}(P) = Wr_{I'}(φ) · Wr(ψ)`.

## Main results

* `Faltings.rothWronskian_sum_mul_eq`: `W_{I'}(∑ⱼ φⱼ ψⱼ) = Wr_{I'}(φ) · Wr(ψ)`.

## Implementation notes

The `m = n + 2` variables are `Fin (n + 2)`, the last one being `ς_m`. A polynomial `φ` in
`ς₁, …, ς_{m-1}` is an element of `MvPolynomial (Fin (n + 1)) K`, embedded by renaming along
`Fin.castSucc`; a polynomial `ψ` in `ς_m` is an element of `MvPolynomial (Fin 1) K`, embedded by
renaming its variable to `Fin.last (n + 1)`. The one-variable Wronskian `Wr(ψ₀, …, ψ_s)` is
`Faltings.generalizedWronskian` at the multi-indices `I_ν = ν`. The base field is any field of
characteristic zero (the source takes `ℚ̄`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 635.
-/

namespace Faltings

open MvPolynomial

section SeparatedProducts

variable {K : Type*} [Field K] {n : ℕ}

/-- `ι₁`: the embedding of `K[ς₁, …, ς_{m-1}]`. -/
local notation "ι₁" => rename (R := K) (Fin.castSucc : Fin (n + 1) → Fin (n + 2))
/-- `ι₂`: the embedding of `K[ς_m]`. -/
local notation "ι₂" => rename (R := K) (fun _ : Fin 1 => Fin.last (n + 1))

private lemma pderiv_rename_eq_zero {σ τ : Type*} {f : σ → τ} (i : τ) (hi : ∀ x, f x ≠ i)
    (p : MvPolynomial σ K) : pderiv i (rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, hi j]

private lemma pderiv_castSucc_mul (i : Fin (n + 1)) (φ : MvPolynomial (Fin (n + 1)) K)
    (ψ : MvPolynomial (Fin 1) K) :
    pderiv i.castSucc (ι₁ φ * ι₂ ψ) = ι₁ (pderiv i φ) * ι₂ ψ := by
  rw [Derivation.leibniz, pderiv_rename_eq_zero _ (fun _ => (Fin.castSucc_lt_last i).ne'),
    pderiv_rename (Fin.castSucc_injective _)]
  simp [mul_comm]

private lemma pderiv_last_mul (φ : MvPolynomial (Fin (n + 1)) K)
    (ψ : MvPolynomial (Fin 1) K) :
    pderiv (Fin.last (n + 1)) (ι₁ φ * ι₂ ψ) = ι₁ φ * ι₂ (pderiv 0 ψ) := by
  rw [Derivation.leibniz, pderiv_rename_eq_zero _ (fun x => (Fin.castSucc_lt_last x).ne),
    pderiv_rename (f := fun _ : Fin 1 => Fin.last (n + 1)) (fun a b _ => Subsingleton.elim a b) 0]
  simp [mul_comm]

/-- An operator `e'` on `K[ς₁, …, ς_m]` acts on separated products through `e` on the first
factor. -/
private def ActsLeft (e' : Module.End K (MvPolynomial (Fin (n + 2)) K))
    (e : Module.End K (MvPolynomial (Fin (n + 1)) K)) : Prop :=
  ∀ φ ψ, e' (ι₁ φ * ι₂ ψ) = ι₁ (e φ) * ι₂ ψ

private lemma ActsLeft.mul {e₁' e₂' e₁ e₂} (h₁ : ActsLeft (K := K) (n := n) e₁' e₁)
    (h₂ : ActsLeft e₂' e₂) : ActsLeft (e₁' * e₂') (e₁ * e₂) := by
  intro φ ψ
  simp only [Module.End.mul_apply, h₂ φ ψ, h₁ _ ψ]

private lemma ActsLeft.one : ActsLeft (K := K) (n := n) 1 1 := fun _ _ => rfl

private lemma ActsLeft.pow {e' e} (h : ActsLeft (K := K) (n := n) e' e) (k : ℕ) :
    ActsLeft (e' ^ k) (e ^ k) := by
  induction k with
  | zero => simpa using ActsLeft.one
  | succ k ih => simpa [pow_succ] using ih.mul h

private lemma ActsLeft.prod_ofFn :
    ∀ {m : ℕ} (f' : Fin m → Module.End K (MvPolynomial (Fin (n + 2)) K))
      (f : Fin m → Module.End K (MvPolynomial (Fin (n + 1)) K)), (∀ i, ActsLeft (f' i) (f i)) →
      ActsLeft (List.ofFn f').prod (List.ofFn f).prod
  | 0, _, _, _ => by simpa using ActsLeft.one
  | m + 1, f', f, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ActsLeft.prod_ofFn _ _ fun i => h i.succ)

private lemma pderiv_last_pow_mul (φ : MvPolynomial (Fin (n + 1)) K)
    (ψ : MvPolynomial (Fin 1) K) (k : ℕ) :
    ((pderiv (Fin.last (n + 1))).toLinearMap ^ k) (ι₁ φ * ι₂ ψ) =
      ι₁ φ * ι₂ (((pderiv 0).toLinearMap ^ k) ψ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact pderiv_last_mul _ _

/-- The divided-derivative operator of `rothWronskian` on a separated product. -/
private lemma entry_mul [CharZero K] (I : Fin (n + 1) → ℕ) (ν : ℕ)
    (φ : MvPolynomial (Fin (n + 1)) K) (ψ : MvPolynomial (Fin 1) K) :
    (∏ k, ((Fin.snoc (α := fun _ => ℕ) I ν k).factorial : K))⁻¹ •
      (List.ofFn fun k => (pderiv k).toLinearMap ^ (Fin.snoc (α := fun _ => ℕ) I ν k)).prod
        (ι₁ φ * ι₂ ψ) =
      ι₁ ((∏ k, ((I k).factorial : K))⁻¹ •
          (List.ofFn fun k : Fin (n + 1) => (pderiv k).toLinearMap ^ I k).prod φ) *
        ι₂ ((∏ k : Fin 1, (((fun _ => ν) k : ℕ).factorial : K))⁻¹ •
          (List.ofFn fun k : Fin 1 => (pderiv k).toLinearMap ^ (fun _ => ν) k).prod ψ) := by
  rw [List.ofFn_succ_last, List.prod_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.prod_cons, List.prod_nil, mul_one]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Module.End.mul_apply, pderiv_last_pow_mul,
    ActsLeft.prod_ofFn _ _ (fun i => ActsLeft.pow (fun φ ψ => pderiv_castSucc_mul i φ ψ) _)]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Fin.prod_univ_one, map_smul, mul_inv, smul_mul_smul_comm]

end SeparatedProducts

/-- **`W = U V`.** For polynomials `φ j` in the first `m - 1` variables and `ψ j` in the last
variable `ς_m`, the Wronskian `Faltings.rothWronskian I'` of `P = ∑ⱼ φ j · ψ j` is the product of
the generalized Wronskian `Wr_{I'}(φ)` and the one-variable Wronskian `Wr(ψ)` (the generalized
Wronskian at `I_ν = ν`), both viewed in `K[ς₁, …, ς_m]`. -/
@[faltings "lem_bvr_roth_wronskian"]
public theorem rothWronskian_sum_mul_eq {K : Type*} [Field K] [CharZero K] {n s : ℕ}
    (I' : Fin (s + 1) → Fin (n + 1) → ℕ) (φ : Fin (s + 1) → MvPolynomial (Fin (n + 1)) K)
    (ψ : Fin (s + 1) → MvPolynomial (Fin 1) K) :
    rothWronskian I'
        (∑ j, rename Fin.castSucc (φ j) * rename (fun _ => Fin.last (n + 1)) (ψ j)) =
      rename Fin.castSucc (generalizedWronskian I' φ) *
        rename (fun _ => Fin.last (n + 1))
          (generalizedWronskian (fun ν _ => (ν : ℕ)) ψ) := by
  unfold rothWronskian generalizedWronskian
  rw [AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_transpose (AlgHom.mapMatrix (rename fun _ : Fin 1 => Fin.last (n + 1)) _),
    ← Matrix.det_mul]
  congr 1
  refine Matrix.ext fun μ ν => ?_
  simp only [Matrix.of_apply, map_sum, Finset.smul_sum, Matrix.mul_apply, Matrix.transpose_apply,
    AlgHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun j _ => entry_mul (I' μ) ν (φ j) (ψ j)

end Faltings
