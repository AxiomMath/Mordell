module
public import Mathlib
public import Mordell.Attr

/-!
# Taylor coefficients at a rational point

Let `X` be a scheme over a field `K`, `p ∈ X(K)` a `K`-rational point and `ϖ` a local
uniformizing parameter at `p`, i.e. a generator of the maximal ideal of the local ring `𝒪_{X,p}`
(for a smooth curve, a rational function with a simple zero at `p`). Every `f ∈ 𝒪_{X,p}` has an
expansion `f = ∑ᵢ aᵢ ϖⁱ` in the completion `𝒪̂_{X,p} = K⟦ϖ⟧`, and the `i`-th Taylor coefficient
`∂ᵢ^ϖ f(p)` is `aᵢ ∈ K`. In characteristic zero it is `(1/i!) (d/dϖ)ⁱ f` at `ϖ = 0`.

## Main definitions

* `Faltings.BombieriVojta.taylorCoeff`: the coefficient `∂ᵢ^ϖ f(p)` of `ϖⁱ` in the expansion
  of `f` at `p`.

## Implementation notes

The coefficients are computed without forming the completion. Write `ev : 𝒪_{X,p} → K` for
evaluation at `p` (`AlgebraicGeometry.Scheme.stalkClosedPointTo`) and `c : K → 𝒪_{X,p}` for the
constants (the structure morphism of `X` over `Spec K`). For `g ∈ 𝒪_{X,p}` the element
`g - c (ev g)` vanishes at `p`, so it equals `ϖ * r` for an `r ∈ 𝒪_{X,p}`, unique when `ϖ` is a
nonzerodivisor; write `r = σ g`. Then `aᵢ = ev (σⁱ f)`, since `σ` sends `∑ aⱼ ϖʲ` to
`∑ aⱼ₊₁ ϖʲ`. The definition is total: off the hypotheses (`p` a `K`-point of `X`, `ϖ` a
uniformizer) `r` is an arbitrary choice and the value carries no meaning. Those hypotheses are
carried by the lemmas characterising `taylorCoeff`.

The statement is made for any scheme over `K`: the source's curve `C ×_k K` over a number field
`K ⊇ k` is the case in which it is used.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, pp. 624–625
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Faltings.BombieriVojta

/-- The Taylor coefficient `∂ᵢ^ϖ f(p)`: the coefficient of `ϖ ^ i` in the expansion of
`f ∈ 𝒪_{X,p}` as a power series in the local parameter `ϖ` at the `K`-rational point `p` of
the `K`-scheme `X`. It is `ev (σ^[i] f)`, where `ev` is evaluation at `p` and `σ g` is an
element with `g - ev g = ϖ * σ g`. -/
@[expose, faltings "def_bv_taylor_coefficients_curve"]
public noncomputable def taylorCoeff {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))]
    (p : Spec (.of K) ⟶ X) (ϖ f : X.presheaf.stalk (p (closedPoint K))) (i : ℕ) : K :=
  let ev : X.presheaf.stalk (p (closedPoint K)) →+* K := (Scheme.stalkClosedPointTo p).hom
  let c : K →+* X.presheaf.stalk (p (closedPoint K)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ Spec (.of K)).appTop ≫
      X.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom
  let σ : X.presheaf.stalk (p (closedPoint K)) → X.presheaf.stalk (p (closedPoint K)) :=
    fun g ↦ Classical.epsilon fun r ↦ g - c (ev g) = ϖ * r
  ev (σ^[i] f)

end Faltings.BombieriVojta
