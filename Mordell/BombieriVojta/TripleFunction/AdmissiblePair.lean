module
public import Mordell.BombieriVojta.Taylor.CurveProduct
public import Mordell.BombieriVojta.TripleFunction.Basic

/-!
# Admissible pairs

In Section 6 of Bombieri's proof of the Mordell conjecture, let `s` be a global section of the
line bundle `𝒪(V)` on `C × C` (`Faltings.vojtaLineBundle`), let `(z, w)` be a point of `C × C`
rational over a number field `K ⊇ k`, and let `ς, ς'` be local uniformizing parameters at `z`
and `w`. A pair `(i₁*, i₂*)` of natural numbers is *admissible* for `s` at `(z, w)` if for some
triple `(i, j, j')` that is non-vanishing at `(z, w)`, the rational function
`G_{ijj'} = s / e_{ijj'}` (`Faltings.BombieriVojta.tripleFunction`) is regular at `(z, w)`, its
Taylor coefficient `∂_{i₁*} ∂'_{i₂*} G_{ijj'}(z, w)` (`Faltings.BombieriVojta.taylorCoeff₂`) is
non-zero, and every coefficient `∂_{i₁} ∂'_{i₂} G_{ijj'}(z, w)` with `i₁ ≤ i₁*`, `i₂ ≤ i₂*`,
`(i₁, i₂) ≠ (i₁*, i₂*)` vanishes.

## Main definitions

* `Faltings.BombieriVojta.IsAdmissiblePair`: the pair `(i₁*, i₂*)` is admissible for `s` at the
  point `p` with respect to the local parameters `ς, ς'`.

## Implementation notes

* As for `Faltings.BombieriVojta.tripleFunction`, `C × C` is a scheme `X` over a base `S` with
  morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`. Since Taylor coefficients take values in
  the field of definition `K` of the point, `X` is moreover a scheme over `Spec K` (in the source,
  `C × C` after base change to `K`), and `(z, w)` is a morphism `p : Spec K ⟶ X`.
* The local parameters are the elements `ς ∘ pr₁` and `ς' ∘ pr₂` of the local ring of `X` at `p`,
  as in `Faltings.BombieriVojta.taylorCoeff₂`.
* The non-vanishing of the triple at `p` is the scheme-theoretic hypothesis of
  `Faltings.BombieriVojta.tripleFunction`: the point lies in the three inverse images of
  standard charts. "`G_{ijj'}` is regular at `p`" is the existence of `g` in the local ring at `p`
  whose image in the function field is `G_{ijj'}`; the Taylor coefficients are those of `g`.
  When `X` is integral, `g` is unique.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Faltings.BombieriVojta

universe u

/-- The pair `(i₁', i₂')` is *admissible* for the global section `s` of
`𝒪(V) = vojtaLineBundle ψ φ δ₁ δ₂ d` at the point `p : Spec K ⟶ X`, with respect to the local
parameters `ς, ς'` at `p`: for some triple `(i, j, j')` non-vanishing at `p`, the function
`G_{ijj'} = tripleFunction ψ φ δ₁ δ₂ d s _ i j j' _` is the image of an element `g` of the local
ring at `p` whose Taylor coefficient `∂_{i₁'} ∂'_{i₂'} g(p)` is non-zero while
`∂_{i₁} ∂'_{i₂} g(p) = 0` for all `i₁ ≤ i₁'`, `i₂ ≤ i₂'` with `(i₁, i₂) ≠ (i₁', i₂')`. -/
@[expose, faltings "def_bv_admissible_pair"]
public def IsAdmissiblePair {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) {K : Type u} [Field K] [X.Over (Spec (.of K))]
    (p : Spec (.of K) ⟶ X) (ς ς' : X.presheaf.stalk (p (closedPoint K))) (i₁' i₂' : ℕ) : Prop :=
  letI : ∀ r : ℕ,
      GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  ∃ (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (hx : p (closedPoint K) ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j')))
    (g : X.presheaf.stalk (p (closedPoint K))),
    algebraMap _ X.functionField g =
        tripleFunction ψ φ δ₁ δ₂ d s (p (closedPoint K)) i j j' hx ∧
      taylorCoeff₂ p ς ς' g i₁' i₂' ≠ 0 ∧
      ∀ i₁ ≤ i₁', ∀ i₂ ≤ i₂', (i₁, i₂) ≠ (i₁', i₂') → taylorCoeff₂ p ς ς' g i₁ i₂ = 0

end Faltings.BombieriVojta
