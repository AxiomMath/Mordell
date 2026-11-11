module

public import Mathlib
public import Mordell.Attr

/-!
# A bounded quadratic-plus-linear function has vanishing quadratic part

Let `M` be an abelian group, `b` a symmetric biadditive form on `M` with values in `ℝ`,
`q x = b x x / 2` the associated quadratic function and `ℓ : M →+ ℝ` additive. If `q + ℓ`
is bounded on `M`, then `q = 0`. Since `q` is even and `ℓ` is odd,
`2 q x = (q + ℓ) x + (q + ℓ) (-x)`, so `q` itself is bounded; and `q (n • x) = n ^ 2 * q x`
is then bounded in `n : ℕ`, which forces `q x = 0`.

## Main results

* `Faltings.eq_zero_of_isBounded_range_add`: the quadratic part of a bounded
  quadratic-plus-linear function vanishes.

## Implementation notes

The biadditive form is a bundled `M →+ M →+ ℝ`, the additive function an `M →+ ℝ`, and
boundedness of `q + ℓ` is `Bornology.IsBounded` of its range in `ℝ`.

## References

* [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 2.
-/

@[expose] public section

namespace Faltings

variable {M : Type*} [AddCommGroup M]

/-- A real function with `q (n • x) = n ^ 2 * q x` for all `n : ℕ` that is bounded on `M`
vanishes identically. -/
private lemma eq_zero_of_abs_le_of_nsmul {q : M → ℝ} {C : ℝ} (hC : ∀ x, |q x| ≤ C)
    (hsmul : ∀ (n : ℕ) x, q (n • x) = (n : ℝ) ^ 2 * q x) : q = 0 := by
  funext x
  by_contra hx
  have hpos : 0 < |q x| := abs_pos.2 hx
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |q x| + 1)
  have h := hC (n • x)
  rw [hsmul, abs_mul, abs_of_nonneg (by positivity)] at h
  have hCn : C < n * |q x| := by
    rw [← div_lt_iff₀ hpos]; linarith
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  have hn1 : (1 : ℝ) ≤ n := by linarith [div_nonneg hC0 hpos.le]
  nlinarith

/-- If `q` is even and `q + ℓ` is bounded by `C` with `ℓ` additive, then `q` is bounded
by `C`, since `2 q x = (q + ℓ) x + (q + ℓ) (-x)`. -/
private lemma abs_le_of_abs_add_le {q : M → ℝ} {C : ℝ} (ℓ : M →+ ℝ)
    (heven : ∀ x, q (-x) = q x) (hC : ∀ x, |q x + ℓ x| ≤ C) (x : M) : |q x| ≤ C := by
  have h1 := abs_le.1 (hC x)
  have h2 := hC (-x)
  rw [heven, map_neg] at h2
  rw [abs_le] at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- If `b` is a symmetric biadditive real form on an abelian group `M`, `q x = b x x / 2`
and `ℓ : M →+ ℝ` is additive with `q + ℓ` bounded on `M`, then `q = 0`. -/
@[faltings "lem_nt_bounded_quadratic_linear_zero"]
theorem eq_zero_of_isBounded_range_add {M : Type*} [AddCommGroup M] (b : M →+ M →+ ℝ)
    (hb : ∀ x y, b x y = b y x) (q : M → ℝ) (hq : ∀ x, q x = b x x / 2) (ℓ : M →+ ℝ)
    (hbdd : Bornology.IsBounded (Set.range (q + ⇑ℓ))) : q = 0 := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbdd
  refine eq_zero_of_abs_le_of_nsmul (C := C)
    (abs_le_of_abs_add_le ℓ (fun x => by simp [hq])
      (fun y => by simpa [Real.norm_eq_abs] using hC _ ⟨y, rfl⟩)) fun n x => ?_
  simp only [hq, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  ring

end Faltings


/-!
# A bounded quadratic-plus-linear function has vanishing linear part

Let `M` be an abelian group, `b` a symmetric biadditive form on `M` with values in `ℝ`,
`q x = b x x / 2` the associated quadratic function and `ℓ : M →+ ℝ` additive. If `q + ℓ` is
bounded on `M`, then `ℓ = 0`: the quadratic part vanishes since `q (n • x) = n ^ 2 * q x`, and then
`ℓ (n • x) = n * ℓ x` is bounded in `n`.

## Main results

* `Faltings.addMonoidHom_eq_zero_of_bounded_quadratic_add`: if `q + ℓ` is bounded then `ℓ = 0`.

## Implementation notes

The biadditive form is an `M →+ M →+ ℝ`, symmetry is the pointwise identity `b x y = b y x`, and
boundedness of `q + ℓ` is the existence of `C` with `|q x + ℓ x| ≤ C` for all `x`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 2.
-/

@[expose] public section

namespace Faltings

/-- An additive real function bounded on `M` vanishes: `|ℓ (n • x)| = n * |ℓ x|` is bounded
in `n : ℕ`. -/
private lemma addMonoidHom_eq_zero_of_abs_le {M : Type*} [AddCommGroup M] (ℓ : M →+ ℝ) {C : ℝ}
    (hC : ∀ x, |ℓ x| ≤ C) : ℓ = 0 := by
  ext x
  by_contra hx
  have hpos : 0 < |ℓ x| := abs_pos.2 hx
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |ℓ x|)
  have h := hC (n • x)
  rw [map_nsmul, nsmul_eq_mul, abs_mul, Nat.abs_cast] at h
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- If `b` is a symmetric biadditive real form on an abelian group `M`, `q x = b x x / 2`, and
`ℓ : M →+ ℝ` is additive with `q + ℓ` bounded on `M`, then `ℓ = 0`: the quadratic part vanishes
by `eq_zero_of_isBounded_range_add`, so `ℓ` itself is bounded. -/
@[faltings "lem_nt_bounded_linear_zero"]
theorem addMonoidHom_eq_zero_of_bounded_quadratic_add {M : Type*} [AddCommGroup M]
    (b : M →+ M →+ ℝ) (hb : ∀ x y, b x y = b y x) (q : M → ℝ) (hq : ∀ x, q x = b x x / 2)
    (ℓ : M →+ ℝ) (hbdd : ∃ C : ℝ, ∀ x, |q x + ℓ x| ≤ C) : ℓ = 0 := by
  obtain ⟨C, hC⟩ := hbdd
  have hq0 : q = 0 := eq_zero_of_isBounded_range_add b hb q hq ℓ
    (isBounded_iff_forall_norm_le.2 ⟨C, by
      rintro _ ⟨y, rfl⟩
      simpa [Real.norm_eq_abs] using hC y⟩)
  exact addMonoidHom_eq_zero_of_abs_le ℓ fun x => by simpa [hq0] using hC x

end Faltings
