module

public import Mordell.CurveProduct.Surface
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Embedding
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.RelativeLinearAction

/-!
# Non-vanishing triples

Let `(C, P)` be a curve over a field `k` with a divisor `P` of degree one, with the two auxiliary
projective embeddings of Bombieri's proof: `φ_B : C × C → ℙ^m`, given by a basis
`y = (y_0, …, y_m)` of `H⁰(C × C, 𝒪(B))`, and `φ_{NP} : C → ℙ^n`, given by a basis
`x = (x_0, …, x_n)` of `H⁰(C, 𝒪(NP))`. For a point `(z, w)` of `C × C`, a triple of indices
`(i, j, j')`, `0 ≤ i ≤ m`, `0 ≤ j, j' ≤ n`, is *non-vanishing at `(z, w)`* if `y_i(z, w) ≠ 0`,
`x_j(z) ≠ 0` and `x_{j'}(w) ≠ 0`. The `y_i` (resp. the `x_j`) are the homogeneous coordinates
of `φ_B` (resp. `φ_{NP}`), so these conditions say that the `i`-th homogeneous coordinate of
`φ_B(z, w)`, the `j`-th of `φ_{NP}(z)` and the `j'`-th of `φ_{NP}(w)` are non-zero. This does
not depend on the choice of homogeneous coordinate vectors. For such a triple,
`x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` is a local generator of `𝒪(V)` at `(z, w)`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.IsNonvanishingTriple`: the triple `(i, j, j')` is
  non-vanishing at `(z, w)` for the embeddings `φ_B` and `φ_{NP}`.

## Implementation notes

The embeddings, the points and the base are those of
`Faltings.CurveWithDegreeOneDivisor.vojtaHeight`. That is, `φNP` and `φB` are
`Faltings.ProjectiveEmbedding`s of `C` and of `C ×_k C`, and `z, w` are `k`-points of `C`. The
pair `(z, w)` is the `k`-point `pullback.lift z w` of `C ×_k C`. The image of a `k`-point `p`
under a projective embedding `φ` into `ℙⁿ_k` is read as a point of `ℙ k (Fin (n + 1) → k)`
through the dictionary of `Faltings.ProjectiveEmbedding.height`: the standard-basis coordinate
isomorphism `𝐏(kⁿ⁺¹) ≅ ℙⁿ_k`, the identification of `k`-points of `𝐏(V)` with lines of
functionals on `V`, and the dual basis. Its homogeneous coordinates are therefore the values at
`φ(p)` of the coordinate forms `T_0, …, T_n`. These are the `x_j`, resp. the `y_i`, when `φ` is
the embedding given by the basis `x`, resp. `y`. The non-vanishing of a coordinate is stated on
the representative `Projectivization.rep`. Rescaling does not change it.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization

universe u

namespace Faltings

/-- The triple of indices `(i, j, j')` is **non-vanishing at `(z, w)`** for the projective
embeddings `φB` of `C ×_k C` (coordinates `y_0, …, y_m`) and `φNP` of `C` (coordinates
`x_0, …, x_n`): `y_i(z, w) ≠ 0`, `x_j(z) ≠ 0` and `x_{j'}(w) ≠ 0`. In other words, the `i`-th
homogeneous coordinate of `φB(z, w)`, the `j`-th of `φNP(z)` and the `j'`-th of `φNP(w)` are
non-zero. Here the image of a `k`-point is read in `ℙ k (Fin (_ + 1) → k)` as in
`Faltings.ProjectiveEmbedding.height`. -/
@[faltings "def_bv_nonvanishing_triple"]
public def CurveWithDegreeOneDivisor.IsNonvanishingTriple {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k) {n m : ℕ}
    (φNP : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _})
    (i : Fin (m + 1)) (j j' : Fin (n + 1)) : Prop :=
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  -- the image `φ(p) ∈ ℙ k (Fin (r + 1) → k)` of a `k`-point `p`
  let image : ∀ {Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)} [IsProjectiveVariety k g] {r : ℕ},
      ProjectiveEmbedding g r → {p : Spec (.of k) ⟶ Y // p ≫ g = 𝟙 _} →
        ℙ k (Fin (r + 1) → k) := fun {Y g _ r} φ p =>
    let b := Pi.basisFun k (Fin (r + 1))
    let q : Spec (.of k) ⟶ projectiveSpaceOfModule k (Fin (r + 1) → k) :=
      p.1 ≫ φ.hom ≫ (projectiveSpaceOfModuleIso b).inv
    have hq : q ≫ projectiveSpaceOfModuleToSpec k (Fin (r + 1) → k) = 𝟙 _ := by
      simp only [q, Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec]
      rw [φ.hom_over, p.2]
    (ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual k _
        (ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient k _ ⟨q, hq⟩)).map
      b.toDualEquiv.symm.toLinearMap b.toDualEquiv.symm.injective
  (image φB ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm),
      by rw [pullback.lift_fst_assoc, z.2]⟩).rep i ≠ 0 ∧
    (image φNP z).rep j ≠ 0 ∧ (image φNP w).rep j' ≠ 0

end Faltings
