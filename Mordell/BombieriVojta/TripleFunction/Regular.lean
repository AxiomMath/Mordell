module
public import Mordell.BombieriVojta.TripleFunction.Basic

/-!
# The functions `G_{ijj'}` are regular at the base point

In Section 6 of Bombieri's proof of the Mordell conjecture, `G_{ijj'} = s / e_{ijj'}` is the
rational function on `C × C` obtained by dividing a global section `s` of `𝒪(V)` by the section
`e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d`, for a triple `(i, j, j')` that is non-vanishing at
`(z, w)` (`Faltings.BombieriVojta.tripleFunction`). Since `e_{ijj'}` is regular and non-vanishing
at `(z, w)`, it generates `𝒪(V)` near `(z, w)`, so `s = G_{ijj'} e_{ijj'}` there with `G_{ijj'}`
regular at `(z, w)`.

## Main results

* `Faltings.BombieriVojta.tripleFunction_mem_range_stalk`: `G_{ijj'}` lies in the image of the
  local ring `𝒪_{X,x}` in the function field.

## Implementation notes

A rational function on the irreducible scheme `X` is regular at a point `x` when it lies in the
image of the stalk `𝒪_{X,x}` in the function field `X.functionField`, under the specialisation
map `AlgebraicGeometry.stalkFunctionFieldAlgebra`. As for `Faltings.BombieriVojta.tripleFunction`,
`C × C` is an arbitrary irreducible scheme `X` over an arbitrary base `S`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Faltings.BombieriVojta

universe u

/-- The germ in the function field of a section on an open set `U` containing `x` comes from the
local ring at `x`. The instance `Nonempty U` is an implicit argument, so that it is found by
unification with whatever proof the germ was formed with. -/
private lemma germToFunctionField_mem_range {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    {_ : Nonempty U} {x : X} (hx : x ∈ U) (f : Γ(X, U)) :
    X.germToFunctionField U f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) :=
  ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField X hx f⟩

/-- For a global section `s` of `vojtaLineBundle ψ φ δ₁ δ₂ d` and a triple `(i, j, j')` that is
non-vanishing at the point `x`, the rational function `tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx`
is regular at `x`: it lies in the image of the local ring `𝒪_{X,x}` in the function field. -/
@[faltings "lem_bv_triple_function_regular"]
public theorem tripleFunction_mem_range_stalk {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) (x : X) (i : Fin (m + 1)) (j j' : Fin (n + 1))
    (hx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j'))) :
    tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx ∈
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  -- `G_{ijj'}` is the germ of a section on the open `U_{ijj'}`, which contains `x`.
  refine germToFunctionField_mem_range (x := x) ?_ _
  exact ⟨⟨hx.2.1, hx.2.2⟩, hx.1⟩

end Faltings.BombieriVojta
