module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel

/-!
# Generic bases of the Riemann–Roch space

Let `C` be a curve over a field `k`, with function field `k(C)`, and let `D` be a divisor on `C`
(in the application `D = N P`). The space `H⁰(C, 𝒪(D))` is identified with the Riemann–Roch space
`L(D) = {f ∈ k(C) : f = 0 or ord_Q f + D(Q) ≥ 0 for all closed points Q}`, and the section `f`
vanishes at the closed point `Q` when `ord_Q f + D(Q) > 0`. For a `k`-basis `ℓ = (ℓ₀, …, ℓₙ)` of
`L(D)` write `ℓ_{νj} = ℓ_ν / ℓ_j ∈ k(C)`.
Following Bombieri, the basis `ℓ` is *generic* if

* (G1) for every `a ∈ {1, …, n}`, the sections `ℓ₀` and `ℓ_a` have no common zero on `C`;
* (G2) for all `a ≠ j` in `{1, …, n}`, `k(C) = k(ℓ_{a0}, ℓ_{j0})`;
* (G3) for all `ν ≠ j` in `{0, …, n}` with `(ν, j) ∉ {(1, 0), (0, 1)}`,
  `k(C) = k(ℓ_{νj}, ℓ_{10})`.

## Main definitions

* `Faltings.BombieriSiegel.SatisfiesG1`: the family `ℓ` satisfies (G1).
* `Faltings.BombieriSiegel.SatisfiesG2`: the family `ℓ` satisfies (G2).
* `Faltings.BombieriSiegel.SatisfiesG3`: the family `ℓ` satisfies (G3).
* `Faltings.BombieriSiegel.IsGenericBasis`: the family `ℓ` is a `k`-basis of `L(D)` satisfying
  (G1), (G2) and (G3).

## Implementation notes

Sections of `𝒪(D)` are rational functions: `H⁰(C, 𝒪(D))` is the Riemann–Roch space `L(D)` inside
`C.functionField`, with orders of vanishing `AlgebraicGeometry.Scheme.ord`, and the `k`-algebra
structure on `C.functionField` is `AlgebraicGeometry.functionFieldAlgebra k f`, induced by the
structure morphism `f`. A divisor is a finitely supported function `D : C →₀ ℤ` on the points of
`C`; Bombieri's `N P` is `N • P`. A divisor is supported on the closed points, so every condition
quantifies over closed points `Q` only (`IsClosed {Q}`) and the value of `D` at the generic point
plays no role. Since `Scheme.ord 0 = 0`, the zero function is put into `L(D)` explicitly, as
`g = 0 ∨ …`, so that `L(D)` is a subspace for every divisor, effective or not. Zeros are taken at
the closed points of `C` over `k`; as `ℓ₀` and `ℓ_a` are defined over `k`, they have a common zero
at a point of `C(k̄)` exactly when they have one at the closed point below it, so (G1) is the
source's condition.

The basis is a family `ℓ : Fin (n + 1) → k(C)`, linearly independent over `k` and spanning
`L(D)`. The indices `0` and `1` are the numerals of `Fin (n + 1)`; when `n = 0` all three
conditions are vacuous.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3; Section 7,
  pp. 627–628; Section 8, p. 629
-/

open AlgebraicGeometry IntermediateField

universe u

namespace Faltings.BombieriSiegel

/-- (G1) for the family `ℓ = (ℓ₀, …, ℓₙ)` of sections of `𝒪(D)` on `C`: for every `a ≠ 0`, the
sections `ℓ₀` and `ℓ_a` have no common zero at a closed point `Q`, a zero of `ℓ_ν` at `Q` being
`0 < ord_Q ℓ_ν + D Q`. -/
@[expose, faltings "def_bvs_generic_basis"]
public def SatisfiesG1 (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (ℓ : Fin (n + 1) → C.functionField) : Prop :=
  ∀ a : Fin (n + 1), a ≠ 0 → ∀ Q : C, IsClosed ({Q} : Set C) →
    ¬(0 < C.ord (ℓ 0) Q + D Q ∧ 0 < C.ord (ℓ a) Q + D Q)

/-- (G2) for the family `ℓ = (ℓ₀, …, ℓₙ)` in `k(C)`: for all `a ≠ j` both nonzero,
`k(C) = k(ℓ_{a0}, ℓ_{j0})`, where `ℓ_{νj} = ℓ_ν / ℓ_j`. -/
@[expose, faltings "def_bvs_generic_basis"]
public def SatisfiesG2 (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] {n : ℕ} (ℓ : Fin (n + 1) → C.functionField) : Prop :=
  letI := functionFieldAlgebra k f
  ∀ a j : Fin (n + 1), a ≠ 0 → j ≠ 0 → a ≠ j → k⟮ℓ a / ℓ 0, ℓ j / ℓ 0⟯ = ⊤

/-- (G3) for the family `ℓ = (ℓ₀, …, ℓₙ)` in `k(C)`: for all `ν ≠ j` with
`(ν, j) ∉ {(1, 0), (0, 1)}`, `k(C) = k(ℓ_{νj}, ℓ_{10})`, where `ℓ_{νj} = ℓ_ν / ℓ_j`. -/
@[expose, faltings "def_bvs_generic_basis"]
public def SatisfiesG3 (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve k f] {n : ℕ} (ℓ : Fin (n + 1) → C.functionField) : Prop :=
  letI := functionFieldAlgebra k f
  ∀ ν j : Fin (n + 1), ν ≠ j → (ν, j) ≠ (1, 0) → (ν, j) ≠ (0, 1) →
    k⟮ℓ ν / ℓ j, ℓ 1 / ℓ 0⟯ = ⊤

/-- The family `ℓ = (ℓ₀, …, ℓₙ)` of rational functions on the curve `C` over `k` is a **generic
basis** of the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))`: it is a `k`-basis of `L(D)` satisfying
(G1), (G2) and (G3). -/
@[faltings "def_bvs_generic_basis"]
public structure IsGenericBasis (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (ℓ : Fin (n + 1) → C.functionField) : Prop where
  /-- The family `ℓ` is linearly independent over `k`. -/
  linearIndependent : letI := functionFieldAlgebra k f; LinearIndependent k ℓ
  /-- The family `ℓ` spans the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))`. -/
  span_eq : letI := functionFieldAlgebra k f
    ((Submodule.span k (Set.range ℓ) : Submodule k C.functionField) : Set C.functionField) =
      {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q}
  /-- (G1): for `a ≠ 0`, the sections `ℓ₀` and `ℓ_a` of `𝒪(D)` have no common zero. -/
  satisfiesG1 : SatisfiesG1 k f D ℓ
  /-- (G2): for `a ≠ j` both nonzero, `k(C) = k(ℓ_{a0}, ℓ_{j0})`. -/
  satisfiesG2 : SatisfiesG2 k f ℓ
  /-- (G3): for `ν ≠ j` with `(ν, j) ∉ {(1, 0), (0, 1)}`, `k(C) = k(ℓ_{νj}, ℓ_{10})`. -/
  satisfiesG3 : SatisfiesG3 k f ℓ

end Faltings.BombieriSiegel
