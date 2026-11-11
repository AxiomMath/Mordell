module
public import Mordell.BombieriVojta.Taylor.CurveProduct

/-!
# Admissible pairs

Let `C` be a scheme over a field `K`, let `L` be a sheaf of modules on `C ×_K C`, let `s` be a
nonzero global section of `L` and let `p` be a `K`-rational point of `C ×_K C`, with projections
`z` and `w` in `C`. A pair `(i₁*, i₂*)` of natural numbers is *admissible for `s` at `p`* if
`s ≠ 0` and there are
local uniformizing parameters `ς` of `C` at `z` and `ς'` of `C` at `w` (generators of the maximal
ideals of the local rings), and a local generator `e` of `L` at `p`, such that, writing the
expansion of `σ = s / e` in `𝒪̂_{C×C,p} = K⟦ς, ς'⟧` as `∑ c_{ij} ς^i ς'^j`, so that `c_{ij}` is
the Taylor coefficient `Faltings.BombieriVojta.taylorCoeff₂` of `σ` in the local parameters
`ς ∘ pr₁`, `ς' ∘ pr₂`, we have `c_{i₁* i₂*} ≠ 0` and `c_{i₁ i₂} = 0` whenever
`(i₁, i₂) ≤ (i₁*, i₂*)` and `(i₁, i₂) ≠ (i₁*, i₂*)`. Equivalently, `(i₁*, i₂*)` is a minimal
element of the support of the expansion of `σ` for the product order on `ℕ × ℕ`.

## Main definitions

* `Faltings.BombieriRoth.IsAdmissiblePair L s p i`: the pair `i = (i₁*, i₂*)` is admissible for
  the section `s` of `L` at the `K`-point `p` of `C ×_K C`.

## Implementation notes

The coefficients are `Faltings.BombieriVojta.taylorCoeff₂`, the expansion of an element of the
local ring at `p` in two local parameters, applied to the parameters `ς ∘ pr₁` and `ς' ∘ pr₂`
(the images of `ς`, `ς'` under the stalk maps of the projections) and to the germ of `σ` at `p`.

A local generator of `L` at `p` is a section `e` of `L` over an open neighbourhood `U` of `p`
such that, for every open `V ⊆ U`, the map `a ↦ a • e|_V` from `𝒪(V)` to `L(V)` is bijective;
`σ = s / e` is then the unique function on `U` with `σ • e = s|_U`.

The source states the notion for the line bundle `𝒪(V)` (`Faltings.vojtaLineBundle`) on `C × C`
of a smooth projective curve `C` over a number field `k`, at a point of `(C × C)(k̄)`. The
condition depends only on `L` near `p`, and it makes sense for any scheme over any field, so it is
stated in that generality. Bombieri's notion is the case `K = k̄`, with `C` the base change of the
curve to `k̄` and `L` the pullback of `𝒪(V)`. The source's standing assumption `s ≠ 0` is part
of the condition. Outside the smooth-curve setting it is not implied by the rest: the expansion
`Faltings.BombieriVojta.taylorCoeff₂` is a choice, unique only when the parameters are regular
parameters, and for `C = Spec K[t]/(t²)`, `s = 0`, the pair `(2, 0)` satisfies the coefficient
conditions for a suitable choice.

## References

* [Bombieri, *The Mordell conjecture revisited*, §6, p. 625][bombieri1990]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

namespace Faltings.BombieriRoth

universe u

/-- A pair `i = (i₁*, i₂*)` of natural numbers is *admissible* for a global section `s` of a
sheaf of modules `L` on `C ×_K C` at a `K`-point `p` if `s ≠ 0` and there are local uniformizing
parameters `ς`, `ς'` of `C` at the two projections of `p` and a local generator `e` of `L` at `p`
such that the Taylor coefficients `c_j = ∂_{j₁} ∂'_{j₂} σ(p)`
(`Faltings.BombieriVojta.taylorCoeff₂`) of `σ = s / e` in the local parameters `ς ∘ pr₁`,
`ς' ∘ pr₂` satisfy `c_i ≠ 0` and `c_j = 0` for every `j ≤ i` with `j ≠ i`. -/
@[faltings "def_bvr_admissible_pair"]
def IsAdmissiblePair {K : Type u} [Field K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
    (L : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Modules) (s : Γ(L, ⊤))
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))] (i : ℕ × ℕ) : Prop :=
  let X := pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))
  let x : X := p (closedPoint K)
  s ≠ 0 ∧ ∃ (ς : C.presheaf.stalk (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) x))
    (ς' : C.presheaf.stalk (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) x)),
    maximalIdeal _ = Ideal.span {ς} ∧ maximalIdeal _ = Ideal.span {ς'} ∧
    ∃ (U : X.Opens) (hxU : x ∈ U) (e : Γ(L, U)),
      (∀ (V : X.Opens) (hVU : V ≤ U),
        Function.Bijective fun a : Γ(X, V) => a • L.presheaf.map (homOfLE hVU).op e) ∧
      ∃ σ : Γ(X, U), σ • e = L.presheaf.map (homOfLE le_top).op s ∧
        let c : ℕ × ℕ → K := fun j => BombieriVojta.taylorCoeff₂ p
          ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap x ς)
          ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap x ς')
          (X.presheaf.germ U x hxU σ) j.1 j.2
        c i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c j = 0

end Faltings.BombieriRoth

end
