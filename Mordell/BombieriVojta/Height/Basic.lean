module

public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.Surface

/-!
# The height associated to the divisor `V(d₁, d₂, d)`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, and let
`V = V(d₁, d₂, d) = d₁ P × C + d₂ C × P + d Δ'` be the divisor on `C × C` attached to arbitrary
integers `d₁, d₂, d`. Fix the auxiliary data of Bombieri's Section 3: an integer `s ≥ 1` with
`B = s P × C + s C × P - Δ'` very ample, a projective embedding `φ_B` of `C × C` by a basis of
`H⁰(C × C, 𝒪(B))`, an integer `N ≥ 2g + 1`, and the projective embedding `φ_{NP}` of `C` by a
basis of `H⁰(C, 𝒪(NP))`. With the heights `h_{NP} = h_{φ_{NP}}` and `h_B = h_{φ_B}` relative to
these embeddings and the rational numbers `δ₁ = (d₁ + s d) / N` and `δ₂ = (d₂ + s d) / N`, the
height associated to `V` is the function on `(C × C)(k)`
`h_V(z, w) = δ₁ h_{NP}(z) + δ₂ h_{NP}(w) - d h_B(z, w)`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.vojtaHeight`: the function `h_V` on pairs of `k`-points.

## Implementation notes

The heights are `Faltings.ProjectiveEmbedding.height`, which is defined for `k`-points of a
smooth projective variety over a field `k` algebraic over `ℚ`; the source's points of
`(C × C)(k̄)` over a number field are the case where `C` is the base change of the curve to
`k = k̄`. The pair `(z, w)` of `k`-points of `C` is the `k`-point `pullback.lift z w` of
`C ×_k C`, whose structure morphism is `pullback.fst f f ≫ f`; that this is a smooth projective
variety is `Faltings.IsSmoothProjectiveCurve.surface_pullback`.

The embeddings `φ_{NP}` and `φ_B` are arguments: the formula is the same for every pair of
projective embeddings, and the statements about `h_V` carry the hypotheses that identify them
with the embeddings by bases of `H⁰(C, 𝒪(NP))` and `H⁰(C × C, 𝒪(B))`
(`Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver` and
`Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver_vojtaClass`).
The integers `d₁, d₂, d` are arbitrary (positive, zero or negative), and `δ₁, δ₂` are rational,
read in `ℝ`; for `N = 0` the division is Lean's `x / 0 = 0`, a value no use of the definition
sees, since the source has `N ≥ 2g + 1`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 619
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Faltings

/-- The **height associated to `V(d₁, d₂, d)`**: for a curve `X = (C, P)` over a field `k`
algebraic over `ℚ`, projective embeddings `φNP` of `C` and `φB` of `C ×_k C`, and integers `s`,
`N`, `d₁`, `d₂`, `d`, the function on pairs `(z, w)` of `k`-points of `C`
`h_V(z, w) = δ₁ h_{φNP}(z) + δ₂ h_{φNP}(w) - d h_{φB}(z, w)` with `δ₁ = (d₁ + s d) / N` and
`δ₂ = (d₂ + s d) / N`. -/
@[faltings "def_bv_height_vojta"]
noncomputable def CurveWithDegreeOneDivisor.vojtaHeight {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k) {n m : ℕ}
    (φNP : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (s : ℤ) (N : ℕ) (d₁ d₂ d : ℤ)
    (z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _}) : ℝ :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
  haveI : Smooth (pullback.fst X.f X.f ≫ X.f) := SmoothOfRelativeDimension.smooth 2 _
  ((d₁ + s * d : ℤ) : ℝ) / N * φNP.height z + ((d₂ + s * d : ℤ) : ℝ) / N * φNP.height w -
    d * φB.height ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
      by rw [pullback.lift_fst_assoc, z.2]⟩

end Faltings

end
