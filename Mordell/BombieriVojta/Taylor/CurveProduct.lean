module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Taylor.Curve

/-!
# Taylor coefficients in two local parameters

Let `X` be a scheme over a field `K` (in the source, `C × C` over a number field `K ⊇ k`),
`p ∈ X(K)` a `K`-rational point (in the source, `(z, w)`), and `ϖ, ϖ'` two elements of the
local ring `𝒪_{X,p}` forming a regular system of parameters (in the source, `ς ∘ pr₁` and
`ς' ∘ pr₂` for uniformizers `ς` at `z` and `ς'` at `w`). The completion `𝒪̂_{X,p}` is then
`K⟦ϖ, ϖ'⟧`, and every `f ∈ 𝒪_{X,p}` has a unique expansion `f = ∑ a_{i₁ i₂} ϖ^{i₁} ϖ'^{i₂}`
there. The Taylor coefficient `∂_{i₁} ∂'_{i₂} f(p)` is `a_{i₁ i₂}`; in characteristic zero it
is `(1/i₁!) (d/dϖ)^{i₁} (1/i₂!) (d/dϖ')^{i₂} f` at `ϖ = ϖ' = 0`. For a function `ξ` on `C`
the one-variable coefficients `∂ᵢ ξ(0)` are `Faltings.BombieriVojta.taylorCoeff`.

## Main definitions

* `Faltings.BombieriVojta.taylorCoeff₂`: the coefficient `∂_{i₁} ∂'_{i₂} f(p)` of
  `ϖ^{i₁} ϖ'^{i₂}` in the expansion of `f` at `p`.

## Implementation notes

The expansion is characterised without forming the completion: a power series
`F ∈ K⟦X₀, X₁⟧` is the expansion of `f` when, for every `n`, `f` minus the truncation
`∑_{j₁, j₂ < n} c(F_{j₁ j₂}) ϖ^{j₁} ϖ'^{j₂}` lies in `(ϖ, ϖ')ⁿ`, where `c : K → 𝒪_{X,p}` are the
constants (the structure morphism of `X` over `Spec K`). The terms with `j₁ + j₂ ≥ n` of the
truncation lie in `(ϖ, ϖ')ⁿ` already, so this is congruence modulo `(ϖ, ϖ')ⁿ` with the
total-degree truncation. Such an `F` exists and is unique when `(ϖ, ϖ')` is a regular system of
parameters at a `K`-point; the definition chooses one and is total, the hypotheses being carried
by the lemmas characterising `taylorCoeff₂`. The statement is made for any scheme over `K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Faltings.BombieriVojta

/-- The Taylor coefficient `∂_{i₁} ∂'_{i₂} f(p)`: the coefficient of `ϖ ^ i₁ * ϖ' ^ i₂` in the
expansion of `f ∈ 𝒪_{X,p}` as a power series in the local parameters `ϖ, ϖ'` at the
`K`-rational point `p` of the `K`-scheme `X`. The expansion is a power series `F` over `K` with
`f - ∑_{j₁, j₂ < n} F_{j₁ j₂} ϖ ^ j₁ * ϖ' ^ j₂ ∈ (ϖ, ϖ') ^ n` for every `n`. -/
@[expose, faltings "def_bv_taylor_coefficients"]
public noncomputable def taylorCoeff₂ {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))]
    (p : Spec (.of K) ⟶ X) (ϖ ϖ' f : X.presheaf.stalk (p (closedPoint K))) (i₁ i₂ : ℕ) : K :=
  let c : K →+* X.presheaf.stalk (p (closedPoint K)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
      X.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom
  let e : ℕ × ℕ → (Fin 2 →₀ ℕ) := fun j ↦ Finsupp.single 0 j.1 + Finsupp.single 1 j.2
  let F : MvPowerSeries (Fin 2) K := Classical.epsilon fun F : MvPowerSeries (Fin 2) K ↦
    ∀ n : ℕ, f - ∑ j ∈ Finset.range n ×ˢ Finset.range n,
        c (MvPowerSeries.coeff (e j) F) * ϖ ^ j.1 * ϖ' ^ j.2 ∈ Ideal.span {ϖ, ϖ'} ^ n
  MvPowerSeries.coeff (e (i₁, i₂)) F

end Faltings.BombieriVojta
