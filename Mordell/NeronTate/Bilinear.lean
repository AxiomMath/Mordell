module

public import Mordell.NeronTate.Basic
public import Mordell.NeronTate.Existence
public import Mordell.AbelianVariety.EvenOddClass
public import Mordell.NeronTate.Functoriality

/-!
# The bilinear form of the Néron–Tate height

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ Pic(A) ⊗ ℚ`, with Néron–Tate height `ĥ_c : A(k) → ℝ`.
The *bilinear form* of `ĥ_c` is its polar form
`B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)` for `x, y ∈ A(k)`.

## Main definitions

* `Faltings.neronTateBilinear A c`: the polar form `B_c` of the Néron–Tate height of `c`.

## Implementation notes

The Néron–Tate height `ĥ_c` is the function characterised by `Faltings.IsNeronTateHeight A c`;
it exists and is unique, and it is taken here as `Classical.epsilon` of that property, so every
statement about `B_c` reads `ĥ_c` through `Faltings.IsNeronTateHeight`. The polar form is
Mathlib's `QuadraticMap.polar`. `ĥ_c` is a function on the sections `p : Spec k ⟶ A` of the
structure morphism, while the polar form needs the group `A(k)`, the morphisms
`Over.mk (𝟙 (Spec k)) ⟶ A` into the group object `A` written additively through `Additive`;
a point `z` of the group is the section `z.left`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- The **bilinear form of the Néron–Tate height**: for an abelian variety `A` over a field `k`
algebraic over `ℚ` and `c ∈ Pic(A) ⊗ ℚ`, `B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)` for
`x, y ∈ A(k)`, the polar form of the Néron–Tate height `ĥ_c` of `c`
(`Faltings.IsNeronTateHeight`). -/
@[faltings "def_nt_neron_tate_bilinear"]
noncomputable def neronTateBilinear {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x y : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) : ℝ :=
  letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  QuadraticMap.polar
    ((Classical.epsilon fun f ↦ IsNeronTateHeight A c f) ∘
      fun z : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) ↦
        (⟨z.toMul.left, by simpa using Over.w z.toMul⟩ :
          {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _}))
    x y

/-- `B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)`, by definition of the polar form. -/
theorem neronTateBilinear_apply {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x y : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    let ĥ : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) → ℝ :=
      (Classical.epsilon fun f ↦ IsNeronTateHeight A c f) ∘
        fun z : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) ↦
          (⟨z.toMul.left, by simpa using Over.w z.toMul⟩ :
            {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _})
    neronTateBilinear A c x y = ĥ (x + y) - ĥ x - ĥ y :=
  rfl

end Faltings

end


/-!
# The linear form of the Néron–Tate height

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ Pic(A) ⊗ ℚ`, with Néron–Tate height `ĥ_c : A(k) → ℝ`.
The *linear form* of `ĥ_c` is its odd part
`L_c(x) = (ĥ_c(x) - ĥ_c(-x)) / 2` for `x ∈ A(k)`.

## Main definitions

* `Faltings.neronTateLinear A c`: the linear form `L_c` of the Néron–Tate height of `c`.

## Implementation notes

The Néron–Tate height `ĥ_c` is the function characterised by `Faltings.IsNeronTateHeight A c`;
it exists and is unique, and it is taken here as `Classical.epsilon` of that property, so every
statement about `L_c` reads `ĥ_c` through `Faltings.IsNeronTateHeight`. `ĥ_c` is a function on
the sections `p : Spec k ⟶ A` of the structure morphism, while `-x` needs the group `A(k)`, the
morphisms `Over.mk (𝟙 (Spec k)) ⟶ A` into the group object `A` written additively through
`Additive`; a point `z` of the group is the section `z.left`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- The **linear form of the Néron–Tate height**: for an abelian variety `A` over a field `k`
algebraic over `ℚ` and `c ∈ Pic(A) ⊗ ℚ`, `L_c(x) = (ĥ_c(x) - ĥ_c(-x)) / 2` for `x ∈ A(k)`,
the odd part of the Néron–Tate height `ĥ_c` of `c` (`Faltings.IsNeronTateHeight`). -/
@[faltings "def_nt_neron_tate_linear"]
noncomputable def neronTateLinear {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) : ℝ :=
  letI hc : (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) → ℝ :=
    (Classical.epsilon fun f ↦ IsNeronTateHeight A c f) ∘
      fun z : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) ↦
        (⟨z.toMul.left, Over.w z.toMul⟩ :
          {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _})
  (hc x - hc (-x)) / 2

end Faltings

end


/-!
# The bilinear form of the Néron–Tate height is symmetric and biadditive

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` and `c ∈ Pic(A) ⊗ ℚ`. The polar
form `B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)` of the Néron–Tate height `ĥ_c` is a symmetric
biadditive form on the group `A(k)`: writing `ĥ_c(x) = ½ b(x, x) + ℓ(x)` with `b` symmetric
biadditive and `ℓ` additive, one finds `B_c = b`.

## Main results

* `Faltings.neronTateBilinear_symm_and_biadditive`: `B_c` is the underlying function of a
  symmetric biadditive map `A(k) →+ A(k) →+ ℝ`.

## Implementation notes

Biadditivity is expressed, as in `Faltings.IsNeronTateHeight`, by a bundled
`AddMonoidHom` into `AddMonoidHom`s whose values agree with `Faltings.neronTateBilinear A c`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

/-- The polar form of `z ↦ ½ b(z, z) + ℓ(z)`, for `b` symmetric biadditive and `ℓ` additive,
is `b`. -/
private lemma polar_half_diag_add {M : Type*} [AddCommGroup M] (b : M →+ M →+ ℝ)
    (hb : ∀ x y, b x y = b y x) (ℓ : M →+ ℝ) (x y : M) :
    QuadraticMap.polar (fun z ↦ b z z / 2 + ℓ z) x y = b x y := by
  simp only [QuadraticMap.polar, map_add, AddMonoidHom.add_apply, hb y x]
  ring

/-- The polar form `Faltings.neronTateBilinear A c` of the Néron–Tate height of `c` is a
symmetric biadditive form on `A(k)`: it is the underlying function of a symmetric
`b : A(k) →+ A(k) →+ ℝ`. -/
@[faltings "lem_nt_neron_tate_bilinear_form"]
theorem neronTateBilinear_symm_and_biadditive {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) :
    ∃ b : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →+
        Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →+ ℝ,
      (∀ x y, b x y = neronTateBilinear A c x y) ∧ ∀ x y, b x y = b y x := by
  letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨-, b, hsymm, ℓ, hf⟩ :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)
  refine ⟨b, fun x y ↦ ?_, hsymm⟩
  rw [← polar_half_diag_add b hsymm ℓ x y]
  refine congrArg (QuadraticMap.polar · x y) (funext fun z ↦ ?_)
  rw [Function.comp_apply, hf]
  congr <;> exact Additive.toMul.injective (Over.OverMorphism.ext rfl)

end Faltings


/-!
# Decomposition of the Néron–Tate height

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ ℚ ⊗ Pic(A)`, with Néron–Tate height `ĥ_c : A(k) → ℝ`.
Write `B_c(x, y) = ĥ_c(x + y) - ĥ_c(x) - ĥ_c(y)` for its bilinear form
(`Faltings.neronTateBilinear`) and `L_c(x) = ½ (ĥ_c(x) - ĥ_c(-x))` for its linear form
(`Faltings.neronTateLinear`). Then `ĥ_c(x) = ½ B_c(x, x) + L_c(x)` for
every `x ∈ A(k)`.

## Main results

* `Faltings.neronTateHeight_eq_neronTateBilinear_div_two_add`: `ĥ_c(x) = ½ B_c(x, x) + L_c(x)`.

## Implementation notes

As in `Faltings.neronTateBilinear` and `Faltings.neronTateLinear`, `ĥ_c` is
`Classical.epsilon (Faltings.IsNeronTateHeight A c)`, a function on the sections
`p : Spec k ⟶ A` of the structure morphism, and a point `z` of the group `A(k)` (written
additively through `Additive`) is read as the section `z.left`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

namespace Faltings

/-- A function of the form `z ↦ ½ b(z, z) + ℓ(z)`, with `b` biadditive and `ℓ`
additive, is half its polar form on the diagonal plus its odd part. -/
private lemma eq_polar_self_div_two_add_odd {M : Type*} [AddCommGroup M] {f : M → ℝ}
    (b : M →+ M →+ ℝ) (ℓ : M →+ ℝ)
    (hf : ∀ z, f z = b z z / 2 + ℓ z) (x : M) :
    f x = QuadraticMap.polar f x x / 2 + (f x - f (-x)) / 2 := by
  simp only [QuadraticMap.polar, hf, map_add, map_neg, AddMonoidHom.add_apply,
    AddMonoidHom.neg_apply]
  ring

/-- The **decomposition of the Néron–Tate height**: for an abelian variety `A` over a field `k`
algebraic over `ℚ`, `c ∈ ℚ ⊗ Pic(A)` and `x ∈ A(k)`,
`ĥ_c(x) = ½ B_c(x, x) + L_c(x)`, where `ĥ_c` is the Néron–Tate height of `c`
(`Faltings.IsNeronTateHeight`), `B_c = Faltings.neronTateBilinear A c` its bilinear form and
`L_c = Faltings.neronTateLinear A c` its linear form. -/
@[faltings "lem_nt_neron_tate_decomposition"]
theorem neronTateHeight_eq_neronTateBilinear_div_two_add {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) :
    letI hc : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) → ℝ :=
      Classical.epsilon (IsNeronTateHeight A c) ∘
        fun z : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A) ↦
          (⟨z.toMul.left, by simpa using Over.w z.toMul⟩ :
            {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _})
    hc x = neronTateBilinear A c x x / 2 + neronTateLinear A c x := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨-, b, -, ℓ, hf⟩ :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)
  refine eq_polar_self_div_two_add_odd b ℓ (fun z ↦ ?_) x
  rw [Function.comp_apply, hf]
  congr

end Faltings

end


/-!
# Even classes have no linear part

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ Pic(A) ⊗ ℚ` an even class, `c⁻ = [-1]^* c = c`. Then the
linear form `L_c` of the Néron–Tate height `ĥ_c` vanishes.

Indeed `ĥ_{c⁻}(x) = ĥ_c(-x)` (`Faltings.IsNeronTateHeight.epsilon_inv_apply`), so
`L_{c⁻}(x) = -L_c(x)`; since `c⁻ = c`, `L_c = -L_c`, i.e. `L_c = 0`.

## Main results

* `Faltings.IsEvenClass.neronTateLinear_eq_zero`: `L_c = 0` for an even class `c`.

## Implementation notes

`L_c` is `Faltings.neronTateLinear A c`, and evenness is `Faltings.IsEvenClass k A c`; both read
`[-1]` as the inversion `GrpObj.inv` of the group object `A`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

namespace Faltings

/-- **Even classes have no linear part.** For an abelian variety `A` and an even class
`c ∈ Pic(A) ⊗ ℚ` (`c⁻ = c`), the linear form `L_c` of the Néron–Tate height of `c` vanishes. -/
@[faltings "lem_nt_neron_tate_even"]
theorem IsEvenClass.neronTateLinear_eq_zero {k : Type u} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left} (hc : IsEvenClass k A c) :
    neronTateLinear A c = 0 := by
  funext x
  have e := IsNeronTateHeight.epsilon_inv_apply A c x
  have hc' : LinearMap.baseChange ℚ
      (Stacks.Picard.schemePullbackClassHom (GrpObj.inv (X := A)).left).toIntLinearMap c = c := hc
  rw [hc'] at e
  simp only [neronTateLinear, Function.comp_apply, Pi.zero_apply]
  rw [e, sub_self, zero_div]

end Faltings

end


/-!
# The linear form of the Néron–Tate height is additive

Let `A` be an abelian variety over a field `k` algebraic over `ℚ` (in the source, an algebraic
closure `k̄` of a number field) and `c ∈ Pic(A) ⊗ ℚ`, with Néron–Tate height `ĥ_c : A(k) → ℝ`.
Writing `ĥ_c(x) = ½ b(x, x) + ℓ(x)` with `b` symmetric biadditive and `ℓ` additive, the quadratic
part is even, so the odd part `L_c(x) = ½ (ĥ_c(x) - ĥ_c(-x))` of `ĥ_c` is `ℓ`; in particular
`L_c` is additive on `A(k)`.

## Main results

* `Faltings.neronTateLinear_add`: `L_c(x + y) = L_c(x) + L_c(y)`.

## Implementation notes

As in `Faltings.neronTateLinear`, `ĥ_c` is `Classical.epsilon (Faltings.IsNeronTateHeight A c)`;
that it is a Néron–Tate height is `Faltings.exists_isNeronTateHeight_of_isAlgebraic`. The
computation of the odd part of a quadratic-plus-linear function is done on an arbitrary abelian
group.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct MonObj

namespace Faltings

/-- The odd part of a quadratic-plus-linear function `x ↦ ½ b(x, x) + ℓ(x)` is `ℓ`. -/
private lemma odd_part_eq {M : Type*} [AddCommGroup M] {f : M → ℝ}
    (b : M →+ M →+ ℝ) (ℓ : M →+ ℝ) (hf : ∀ x, f x = b x x / 2 + ℓ x) (x : M) :
    (f x - f (-x)) / 2 = ℓ x := by
  simp only [hf, map_neg, AddMonoidHom.neg_apply, neg_neg]
  ring

/-- **`L_c` is additive.** For an abelian variety `A` over a field `k` algebraic over `ℚ` and
`c ∈ Pic(A) ⊗ ℚ`, the linear form `L_c = Faltings.neronTateLinear A c` of the Néron–Tate height
of `c` satisfies `L_c(x + y) = L_c(x) + L_c(y)` on `A(k)`. -/
@[faltings "lem_nt_neron_tate_linear_form"]
theorem neronTateLinear_add {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (x y : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) :
    neronTateLinear A c (x + y) = neronTateLinear A c x + neronTateLinear A c y := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨-, b, -, ℓ, hf⟩ :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic A c)
  have key (z : Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) : neronTateLinear A c z = ℓ z := by
    refine odd_part_eq b ℓ (fun w ↦ ?_) z
    rw [Function.comp_apply, hf]
    rfl
  rw [key, key, key, map_add]

end Faltings

end
