module
public import Mathlib
public import Mordell.Attr

/-!
# A large affine co-ordinate

Let `K` be a field with a family of admissible absolute values (for instance a number field), and
let `x = (x₀ : x₁ : ⋯ : xₙ)` be a point of `ℙⁿ(K)` with `n ≥ 1` and `x₀ ≠ 0`. Write
`ξⱼ = xⱼ / x₀` for its affine co-ordinates. At every place `v`,
`max(1, |ξ₁|ᵥ, …, |ξₙ|ᵥ) ≤ ∏ⱼ max(1, |ξⱼ|ᵥ)`, so `h(x) ≤ ∑ⱼ h(ξⱼ)`. Hence one of the
`n` non-negative numbers `h(ξⱼ)` is at least `h(x) / n`.

Applied to `x = φ_{NP}(z)`, the image of a point `z` of the curve under the embedding given by
the basis `x₀, …, xₙ` of `H⁰(C, 𝒪(NP))`, this says that some affine co-ordinate `ξₐ(z)` has
height at least `h_{NP}(z) / n`.

## Main results

* `Faltings.exists_logHeight_div_le_logHeight₁_div`: if `x 0 ≠ 0`, then some `a : Fin n` has
  `Height.logHeight x / n ≤ Height.logHeight₁ (x a.succ / x 0)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632
-/

namespace Faltings

open Height

/-- The affine height bound: if `x 0 ≠ 0` then `h(x) ≤ ∑ₐ h(x (a+1) / x 0)`. The vector
`(x 0)⁻¹ • x` is a restriction of the multiplication table of the vectors `(x (a+1) / x 0, 1)`,
whose height is the sum of their heights. -/
private lemma logHeight_le_sum_logHeight₁_div {K : Type*} [Field K] [AdmissibleAbsValues K]
    {n : ℕ} (x : Fin (n + 1) → K) (hx : x 0 ≠ 0) :
    logHeight x ≤ ∑ a : Fin n, logHeight₁ (x a.succ / x 0) := by
  set t : Fin n → Fin 2 → K := fun a => ![x a.succ / x 0, 1]
  have htne (a : Fin n) : t a ≠ 0 := fun h => by simpa [t] using congrFun h 1
  let f : Fin (n + 1) → (Fin n → Fin 2) :=
    Fin.cases (fun _ => 1) (fun b a => if a = b then 0 else 1)
  have hcomp : (fun I : Fin n → Fin 2 => ∏ a, t a (I a)) ∘ f = (x 0)⁻¹ • x := by
    funext i
    induction i using Fin.cases with
    | zero => simp [f, t, hx]
    | succ b =>
      simp only [Function.comp_apply, f, Fin.cases_succ, Pi.smul_apply, smul_eq_mul]
      rw [Finset.prod_eq_single b]
      · simp [t, div_eq_inv_mul]
      · intro a _ hab; simp [t, hab]
      · simp
  calc logHeight x = logHeight ((x 0)⁻¹ • x) :=
        (logHeight_smul_eq_logHeight x (inv_ne_zero hx)).symm
    _ ≤ logHeight (fun I : Fin n → Fin 2 => ∏ a, t a (I a)) := by
        rw [← hcomp]; exact logHeight_comp_le _ _
    _ = ∑ a, logHeight (t a) := logHeight_fun_prod_eq htne
    _ = ∑ a : Fin n, logHeight₁ (x a.succ / x 0) := by
        simp [t, logHeight₁_eq_logHeight]

/-- If `x = (x₀ : ⋯ : xₙ)` has `x₀ ≠ 0` and `n ≥ 1`, then one of its affine co-ordinates
`xₐ / x₀` (`1 ≤ a ≤ n`) has logarithmic height at least `h(x) / n`. -/
@[faltings "lem_bvr_large_coordinate"]
public theorem exists_logHeight_div_le_logHeight₁_div {K : Type*} [Field K]
    [AdmissibleAbsValues K] {n : ℕ} [NeZero n] (x : Fin (n + 1) → K) (hx : x 0 ≠ 0) :
    ∃ a : Fin n, logHeight x / n ≤ logHeight₁ (x a.succ / x 0) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin n)))
    Finset.univ_nonempty (f := fun _ => logHeight x / n)
    (g := fun a => logHeight₁ (x a.succ / x 0)) (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ hn]
      exact logHeight_le_sum_logHeight₁_div x hx)
  exact ⟨a, ha⟩

end Faltings
