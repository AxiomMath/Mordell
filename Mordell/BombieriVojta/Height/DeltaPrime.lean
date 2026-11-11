module

public import Mordell.Height.Machine.EmbeddingHeight
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.CurveProduct.Surface

/-!
# The height `h_{Δ'}` on `C × C`

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, with the auxiliary
data of Bombieri's Section 3: an integer `s ≥ 1` making `B = s P × C + s C × P - Δ'` very ample,
a projective embedding `φ_B` of `C × C` by a basis of `H⁰(C × C, 𝒪(B))`, an integer
`N ≥ 2g + 1`, and the projective embedding `φ_{NP}` of `C` by a basis of `H⁰(C, 𝒪(NP))`. With the
heights `h_{NP} = h_{φ_{NP}}` and `h_B = h_{φ_B}` relative to these embeddings, the height
attached to `Δ'` is the function on `(C × C)(k)`
`h_{Δ'}(z, w) = (s / N) h_{NP}(z) + (s / N) h_{NP}(w) - h_B(z, w)`.

## Main definitions

* `Faltings.BombieriVojta.heightDeltaPrime`: the function `h_{Δ'}` on pairs of `k`-points.

## Implementation notes

The heights are `Faltings.ProjectiveEmbedding.height`, defined for `k`-points of a smooth
projective variety over a field `k` algebraic over `ℚ`; the source's points of `(C × C)(k̄)`
over a number field are the case where `C` is the base change of the curve to `k = k̄`. The pair
`(z, w)` of `k`-points of `C` is the `k`-point `pullback.lift z w` of `C ×_k C`, whose structure
morphism is `pullback.fst f f ≫ f`; that this is a smooth projective variety is
`Faltings.IsSmoothProjectiveCurve.surface_pullback`.

The embeddings `φ_{NP}` and `φ_B` are arguments, exactly as for
`Faltings.CurveWithDegreeOneDivisor.vojtaHeight`: the formula is the same for every pair of
projective embeddings, and the statements about `h_{Δ'}` carry the hypotheses identifying them
with the embeddings by bases of `H⁰(C, 𝒪(NP))` and `H⁰(C × C, 𝒪(B))`. The quotient `s / N` is
read in `ℝ`; for `N = 0` it is Lean's `x / 0 = 0`, a value no use sees, since `N ≥ 2g + 1`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5, proof of Lemma 2
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

@[expose] public section

namespace Faltings.BombieriVojta

/-- The height `h_{Δ'}` of Bombieri's proof of Lemma 2: for a curve `X = (C, P)` over a field
`k` algebraic over `ℚ`, projective embeddings `φNP` of `C` and `φB` of `C ×_k C`, and integers
`s`, `N`, the function on pairs `(z, w)` of `k`-points of `C`
`h_{Δ'}(z, w) = (s / N) h_{φNP}(z) + (s / N) h_{φNP}(w) - h_{φB}(z, w)`. -/
@[faltings "def_bv_height_delta_prime"]
noncomputable def heightDeltaPrime {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k) {n m : ℕ}
    (φNP : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (s : ℤ) (N : ℕ)
    (z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _}) : ℝ :=
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
  haveI : Smooth (pullback.fst X.f X.f ≫ X.f) := SmoothOfRelativeDimension.smooth 2 _
  (s : ℝ) / N * φNP.height z + (s : ℝ) / N * φNP.height w -
    φB.height ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
      by rw [pullback.lift_fst_assoc, z.2]⟩

end Faltings.BombieriVojta

end
