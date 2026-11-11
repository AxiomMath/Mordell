module
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mordell.Attr

/-!
# The Segre–Veronese embeddings `ψ_{δ₁,δ₂}`

For integers `δ₁, δ₂ ≥ 1` the Segre–Veronese map
`v_{δ₁,δ₂} : ℙ(K^ι) × ℙ(K^κ) → ℙ(K^{\{a // |a| = δ₁\} × \{b // |b| = δ₂\}})` sends a pair of
points with homogeneous coordinates `x = (x_i)_{i ∈ ι}` and `x' = (x'_j)_{j ∈ κ}` to the point
whose coordinates are all monomials `x^a x'^b = ∏ᵢ xᵢ ^ a i * ∏ⱼ x'ⱼ ^ b j` of bidegree
`(δ₁, δ₂)`. With `ι = κ = Fin (n + 1)` this is `v_{δ₁,δ₂} : ℙⁿ × ℙⁿ → ℙ^{M-1}` with
`M = binom (δ₁ + n) n * binom (δ₂ + n) n`, the number of such monomials.

Given a map `ψ : X → ℙ(K^ι) × ℙ(K^κ)`, its Segre–Veronese composite is
`ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ ψ`. In Bombieri's setting `X = (C × C)(k̄)` and
`ψ = φ_{NP} × φ_{NP}` is the product of the embedding `φ_{NP} : C → ℙⁿ` given by a basis of
`H⁰(C, 𝒪(NP))`; the map `v_{δ₁,δ₂}` itself is the case `ψ = id`.

The value does not depend on the representatives of the points: scaling `x` by `t ≠ 0` and
`x'` by `s ≠ 0` scales every coordinate `x^a x'^b` by `t ^ δ₁ * s ^ δ₂`. It is a point of
projective space because, if `xᵢ ≠ 0` and `x'ⱼ ≠ 0`, the coordinate `xᵢ ^ δ₁ * x'ⱼ ^ δ₂` is
nonzero.

## Main definitions

* `Faltings.segreVeroneseComposite`: the composite `ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ ψ` of a map
  `ψ : X → ℙ(K^ι) × ℙ(K^κ)` with the Segre–Veronese map of bidegree `(δ₁, δ₂)`.

## Implementation notes

The maps are given by their action on `K`-points, the projective spaces being
`Projectivization K (ι → K)`; this is the form in which `ψ_{δ₁,δ₂}` enters the heights
`h_{ψ_{δ₁,δ₂}}`. The homogeneous coordinates of the target are indexed by pairs of exponent
vectors `a : ι →₀ ℕ`, `b : κ →₀ ℕ` of total degrees `δ₁` and `δ₂`, and the coordinate at
`(a, b)` is computed from the chosen representatives `Projectivization.rep` of the two points.
The two factors are allowed different coordinate types `ι`, `κ`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 3, p. 619][bombieri1990]
-/

namespace Faltings

-- `h₁`, `h₂` are Bombieri's `δ₁, δ₂ ≥ 1`, kept in the statement though the formula
-- does not use them.
set_option linter.unusedVariables false in
open scoped LinearAlgebra.Projectivization in
/-- The **Segre–Veronese composite** `ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ ψ` of a map
`ψ : X → ℙ(K^ι) × ℙ(K^κ)`, for `δ₁, δ₂ ≥ 1`: it sends `p` with `ψ p = ([x], [x'])` to the point
`[(x^a x'^b)_{|a| = δ₁, |b| = δ₂}]` whose coordinates are all monomials of bidegree `(δ₁, δ₂)`.
For `ψ = id` this is the Segre–Veronese map `v_{δ₁,δ₂}` itself. -/
@[expose, faltings "def_bv_segre_veronese"]
public noncomputable def segreVeroneseComposite (K : Type*) [Field K] {X ι κ : Type*}
    (δ₁ δ₂ : ℕ) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (ψ : X → ℙ K (ι → K) × ℙ K (κ → K)) :
    X → ℙ K ({a : ι →₀ ℕ // a.degree = δ₁} × {b : κ →₀ ℕ // b.degree = δ₂} → K) :=
  fun p => Projectivization.mk K
    (fun ab => (ab.1.1.prod fun i k => (ψ p).1.rep i ^ k) *
      ab.2.1.prod fun j k => (ψ p).2.rep j ^ k) (by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (ψ p).1.rep_nonzero
      obtain ⟨j, hj⟩ := Function.ne_iff.mp (ψ p).2.rep_nonzero
      refine Function.ne_iff.mpr
        ⟨(⟨Finsupp.single i δ₁, by simp⟩, ⟨Finsupp.single j δ₂, by simp⟩), ?_⟩
      simpa using mul_ne_zero (pow_ne_zero δ₁ hi) (pow_ne_zero δ₂ hj))

end Faltings
