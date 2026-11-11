module
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import Mordell.BombieriVojta.Taylor.Curve
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import Mordell.BombieriVojta.Taylor.MonomialBound

/-!
# The expansion of an algebraic function at a smooth rational point

Let `C` be a smooth curve over a field `K`, `z ∈ C(K)` a rational point and `ς` a uniformizer at
`z`, i.e. a generator of the maximal ideal of the discrete valuation ring `𝒪_{C,z}`. The
completion `𝒪̂_{C,z}` is `K⟦ς⟧`, and the image `ξ̂` of a function `ξ ∈ 𝒪_{C,z}` there is the power
series `∑ᵢ ∂ᵢ^ς ξ(z) ςⁱ` of its Taylor coefficients. Since `𝒪_{C,z} → K⟦ς⟧` is a homomorphism of
`K`-algebras sending `ς` to the variable and compatible with reduction modulo the maximal ideals,
`ξ̂` has constant term `ξ(z)`, and any polynomial relation `p(ξ, ς) = 0` with `p ∈ K[X, Y]`
holding in `K(C)` also holds for `ξ̂`: `p(ξ̂, ς) = 0` in `K⟦ς⟧`.

## Main definitions

* `Faltings.BombieriVojta.constants`: the constants `K →+* 𝒪_{C,z}`.
* `Faltings.BombieriVojta.taylorCoeffHom`: the expansion `𝒪_{C,z} →+* K⟦X⟧` at `z` in a
  uniformizer, `ξ ↦ ∑ᵢ ∂ᵢ^ς ξ(z) Xⁱ`.

## Main results

* `Faltings.BombieriVojta.coeff_taylorCoeffHom`: the coefficients of `taylorCoeffHom z hς ξ` are
  the Taylor coefficients `taylorCoeff z ς ξ`.
* `Faltings.BombieriVojta.aeval_comp_taylorCoeffHom`: `taylorCoeffHom` carries polynomial
  expressions over the constants to the same expressions over `K`.
* `Faltings.BombieriVojta.aeval_mk_taylorCoeff_eq_zero`: the series of Taylor coefficients of
  `ξ` has constant term `ξ(z)` and satisfies `p(ξ̂, X) = 0`.

## Implementation notes

The image of `ξ` in the completion is written as the power series
`PowerSeries.mk (Faltings.BombieriVojta.taylorCoeff z ς ξ)`, which is the image of `ξ` under the
canonical isomorphism `𝒪̂_{C,z} ≅ K⟦ς⟧`; the completion is not formed. A function regular at `z`
is an element of the stalk `𝒪_{C,z}`, which embeds into `K(C)`; the relation `p(ξ, ς) = 0` is
imposed in `K(C)`, with its `K`-algebra structure `AlgebraicGeometry.functionFieldAlgebra`. The
polynomial `p` is an `MvPolynomial (Fin 2) K` with `X = X 0`, `Y = X 1`.

The ring homomorphism `taylorCoeffHom` is `Faltings.BombieriVojta.curveExpansion`, the unique
expansion in powers of `ς`; it is `C` on the constants and sends `ς` to `X`, and its coefficients
are the Taylor coefficients, so it is `ξ ↦ PowerSeries.mk (taylorCoeff z ς ξ)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 5
-/

open AlgebraicGeometry CategoryTheory IsLocalRing PowerSeries

universe u

namespace Faltings.BombieriVojta

section Geometry

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (z : Spec (.of K) ⟶ X) [z.IsOver (Spec (.of K))]

/-- The `K`-algebra structure of `K(X)` factors through the constants of `𝒪_{X,z}`. -/
private lemma algebraMap_functionField [IsCurve K (X ↘ Spec (.of K))] :
    @algebraMap K X.functionField _ _ (functionFieldAlgebra K (X ↘ Spec (.of K))) =
      (algebraMap (X.presheaf.stalk (z (closedPoint K))) X.functionField).comp (constants z) := by
  simp only [functionFieldAlgebra, RingHom.algebraMap_toAlgebra, stalkFunctionFieldAlgebra]
  rw [← CommRingCat.hom_comp]
  simp only [constants, Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]

variable [IsCurve K (X ↘ Spec (.of K))] {ς : X.presheaf.stalk (z (closedPoint K))}
  (hς : maximalIdeal (X.presheaf.stalk (z (closedPoint K))) = Ideal.span {ς})

/-- The expansion `ξ ↦ ∑ᵢ ∂ᵢ^ς ξ(z) Xⁱ` of a function regular at a `K`-point `z` of a curve in a
uniformizer `ς` at `z`, as a ring homomorphism `𝒪_{X,z} →+* K⟦X⟧`: the canonical map to the
completion `𝒪̂_{X,z} ≅ K⟦ς⟧`. -/
public noncomputable def taylorCoeffHom : X.presheaf.stalk (z (closedPoint K)) →+* K⟦X⟧ :=
  curveExpansion z (comp_over_eq_id z) hς

/-- The `j`-th coefficient of the expansion `taylorCoeffHom z hς ξ` is the Taylor coefficient
`taylorCoeff z ς ξ j`. -/
@[simp]
public lemma coeff_taylorCoeffHom (ξ : X.presheaf.stalk (z (closedPoint K))) (j : ℕ) :
    coeff j (taylorCoeffHom z hς ξ) = taylorCoeff z ς ξ j :=
  coeff_curveExpansion z (comp_over_eq_id z) hς ξ j

/-- The power series with coefficients `taylorCoeff z ς ξ` is `taylorCoeffHom z hς ξ`. -/
public lemma mk_taylorCoeff (ξ : X.presheaf.stalk (z (closedPoint K))) :
    PowerSeries.mk (taylorCoeff z ς ξ) = taylorCoeffHom z hς ξ := by
  ext; simp

/-- The constant term of the expansion of `ξ` is its value `ξ(z)` at `z`. -/
@[simp]
public lemma constantCoeff_taylorCoeffHom (ξ : X.presheaf.stalk (z (closedPoint K))) :
    constantCoeff (taylorCoeffHom z hς ξ) = (Scheme.stalkClosedPointTo z).hom ξ :=
  constantCoeff_curveExpansion z (comp_over_eq_id z) hς ξ

/-- The expansion of the uniformizer `ς` is `X`. -/
@[simp]
public lemma taylorCoeffHom_uniformizer : taylorCoeffHom z hς ς = PowerSeries.X :=
  curveExpansion_self z (comp_over_eq_id z) hς

/-- On the constants `K → 𝒪_{X,z}`, the expansion is the inclusion `C` of constant series. -/
@[simp]
public lemma taylorCoeffHom_comp_constants : (taylorCoeffHom z hς).comp (constants z) = C :=
  curveExpansion_comp_const z (comp_over_eq_id z) hς

/-- The expansion of the constant `k` is the constant power series `C k`. -/
@[simp]
public lemma taylorCoeffHom_constants (k : K) : taylorCoeffHom z hς (constants z k) = C k :=
  congr($(taylorCoeffHom_comp_constants z hς) k)

/-- `taylorCoeffHom` carries a polynomial expression over the constants of `𝒪_{X,z}` to the same
polynomial expression over `K` in `K⟦X⟧`. -/
public lemma aeval_comp_taylorCoeffHom {ι : Type*} (v : ι → X.presheaf.stalk (z (closedPoint K)))
    (p : MvPolynomial ι K) :
    MvPolynomial.aeval (taylorCoeffHom z hς ∘ v) p =
      taylorCoeffHom z hς (MvPolynomial.eval₂ (constants z) v p) := by
  rw [MvPolynomial.aeval_def, algebraMap_eq, ← taylorCoeffHom_comp_constants z hς,
    ← MvPolynomial.eval₂_comp_left]

end Geometry

/-- Let `C` be a smooth curve over `K`, `z ∈ C(K)`, `ς` a uniformizer at `z`, `p ∈ K[X, Y]`, and
`ξ` a function regular at `z` with `p(ξ, ς) = 0` in `K(C)`. Then the expansion
`ξ̂ = ∑ᵢ ∂ᵢ^ς ξ(z) Xⁱ ∈ K⟦X⟧` of `ξ` at `z` has constant term `ξ(z)` and satisfies
`p(ξ̂, X) = 0`. -/
@[faltings "lem_bvs_power_series_branch"]
public theorem aeval_mk_taylorCoeff_eq_zero {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    (z : Spec (.of K) ⟶ C) [z.IsOver (Spec (.of K))]
    (ς ξ : C.presheaf.stalk (z (closedPoint K)))
    (hς : maximalIdeal (C.presheaf.stalk (z (closedPoint K))) = Ideal.span {ς})
    (p : MvPolynomial (Fin 2) K)
    (hp : letI := functionFieldAlgebra K (C ↘ Spec (.of K))
      MvPolynomial.aeval ![algebraMap _ C.functionField ξ, algebraMap _ C.functionField ς] p = 0) :
    constantCoeff (PowerSeries.mk (taylorCoeff z ς ξ)) = (Scheme.stalkClosedPointTo z).hom ξ ∧
      MvPolynomial.aeval ![PowerSeries.mk (taylorCoeff z ς ξ), (X : K⟦X⟧)] p = 0 := by
  rw [mk_taylorCoeff z hς, constantCoeff_taylorCoeffHom]
  refine ⟨rfl, ?_⟩
  have hp' : MvPolynomial.eval₂ (constants z) ![ξ, ς] p = 0 := by
    letI := functionFieldAlgebra K (C ↘ Spec (.of K))
    refine IsFractionRing.injective _ C.functionField ?_
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← algebraMap_functionField,
      ← MvPolynomial.aeval_def, ← hp]
    congr 2
    funext i
    fin_cases i <;> rfl
  have := aeval_comp_taylorCoeffHom z hς ![ξ, ς] p
  rwa [hp', map_zero, show taylorCoeffHom z hς ∘ ![ξ, ς] = ![taylorCoeffHom z hς ξ, X] by
    funext i
    fin_cases i
    · rfl
    · exact taylorCoeffHom_uniformizer z hς] at this

end Faltings.BombieriVojta
