module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mordell.Attr

/-!
# Coordinates of `φ_B` generic for the projections `π_{ab}`

Let `C` be a curve over a number field `k`, `φ_{NP} : C → ℙⁿ` the embedding given by a basis
`x₀, …, xₙ` of `H⁰(C, 𝒪(NP))`, and `φ_B : C × C → ℙᵐ` the embedding given by a basis
`y₀, …, y_m` of `H⁰(C × C, 𝒪(B))`, with `Dᵢ` the divisor of zeros of `yᵢ`. When `x₀` and `x_a`
have no common zero for every `1 ≤ a ≤ n`, the map
`π_{ab} = (x₀ : x_a ; x₀' : x_b') : C × C → ℙ¹ × ℙ¹` is defined everywhere. The coordinates
`y₀, …, y_m` are *generic for the projections* if for every `1 ≤ a, b ≤ n`, with `π = π_{ab}`:

* (G1) for `1 ≤ i ≤ m`, `π_* Dᵢ` and `π_* D₀` have no common component, and neither have
  `π_* D₁` and `π_* D₂`;
* (G2) for `1 ≤ i ≤ m`, no component of `π_* Dᵢ` lies in `(∞ × ℙ¹) ∪ (ℙ¹ × ∞)`;
* (G3) over every point `p` of `𝔸¹ × 𝔸¹` some `yᵢ`, `1 ≤ i ≤ m`, vanishes at no point of
  `π⁻¹(p)`.

## Main definitions

* `Faltings.IsGenericForProjections`: the coordinates of `φ_B` are generic for the projections
  `π_{ab}` built from the coordinates of `φ_{NP}`.

## Implementation notes

The condition only involves the geometric points of `C × C` and the vanishing of the
coordinates there, so it is stated on that data: a type `P` of points of `C` over a field `K`
(in the source `P = C(k̄)` and `K = k̄`), the map `φNP : P → ℙ(Kⁿ⁺¹)` and the map
`φB : P × P → ℙ(Kᵐ⁺¹)`. A coordinate vanishes at a point when it vanishes on a (any)
representative vector, so `Dᵢ` is supported on `{q | (φB q).rep i = 0}`. On `ℙ¹` with
coordinates `(X₀ : X₁)`, `∞` is `X₀ = 0` and `𝔸¹` is `X₀ ≠ 0`.

Since `π_{ab}` is finite, the support of `π_* Dᵢ` is the image `π(Supp Dᵢ)`, a curve in
`ℙ¹ × ℙ¹` whose components are the images of the components of `Dᵢ`. Over `k̄`, two curves in
`ℙ¹ × ℙ¹` have no common component exactly when they meet in finitely many points, and a curve
has no component in `(∞ × ℙ¹) ∪ (ℙ¹ × ∞)` exactly when it meets that union in finitely many
points (a component lying in the union is one of its two lines). So (G1) and (G2) are stated as
the finiteness of these intersections of images.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9
-/

namespace Faltings

open Projectivization
open scoped LinearAlgebra.Projectivization

/-- The coordinates of `φB : P × P → ℙᵐ` are *generic for the projections* `π_{ab}`
`= (x₀ : x_a ; x₀' : x_b')` built from the coordinates of `φNP : P → ℙⁿ` (where `hx` says that
`x₀` and `x_a`, `a ≠ 0`, have no common zero): for all `a, b ≠ 0`, writing `Zᵢ` for the zero set
of the coordinate `yᵢ` and `π = π_{ab}`,
(G1) `π(Zᵢ) ∩ π(Z₀)` is finite for `i ≠ 0`, and `π(Z₁) ∩ π(Z₂)` is finite;
(G2) `π(Zᵢ)` meets `(∞ × ℙ¹) ∪ (ℙ¹ × ∞)` in finitely many points for `i ≠ 0`;
(G3) over each point of `𝔸¹ × 𝔸¹` some `yᵢ`, `i ≠ 0`, vanishes at no point of the fibre of `π`. -/
@[expose, faltings "def_bvr_generic_b_coordinates"]
public def IsGenericForProjections {K P : Type*} [Field K] {n m : ℕ}
    (φNP : P → ℙ K (Fin (n + 1) → K))
    (hx : ∀ a : Fin (n + 1), a ≠ 0 → ∀ z, (φNP z).rep 0 ≠ 0 ∨ (φNP z).rep a ≠ 0)
    (φB : P × P → ℙ K (Fin (m + 1) → K)) : Prop :=
  ∀ (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0),
    let πa : P → ℙ K (Fin 2 → K) := fun z =>
      mk K ![(φNP z).rep 0, (φNP z).rep a] fun h =>
        (hx a ha z).elim (fun h0 => h0 (congrFun h 0)) (fun h1 => h1 (congrFun h 1))
    let πb : P → ℙ K (Fin 2 → K) := fun w =>
      mk K ![(φNP w).rep 0, (φNP w).rep b] fun h =>
        (hx b hb w).elim (fun h0 => h0 (congrFun h 0)) (fun h1 => h1 (congrFun h 1))
    let π : P × P → ℙ K (Fin 2 → K) × ℙ K (Fin 2 → K) := fun q => (πa q.1, πb q.2)
    let Z : Fin (m + 1) → Set (P × P) := fun i => {q | (φB q).rep i = 0}
    let atInfinity : Set (ℙ K (Fin 2 → K) × ℙ K (Fin 2 → K)) :=
      {p | p.1.rep 0 = 0 ∨ p.2.rep 0 = 0}
    -- (G1)
    ((∀ i : Fin (m + 1), i ≠ 0 → (π '' Z i ∩ π '' Z 0).Finite) ∧
      (∀ i j : Fin (m + 1), i.val = 1 → j.val = 2 → (π '' Z i ∩ π '' Z j).Finite)) ∧
    -- (G2)
    (∀ i : Fin (m + 1), i ≠ 0 → (π '' Z i ∩ atInfinity).Finite) ∧
    -- (G3)
    (∀ p, p ∉ atInfinity → ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ q, π q = p → (φB q).rep i ≠ 0)

end Faltings
