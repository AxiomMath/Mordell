module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.Composite
public import Mordell.BombieriVojta.Height.Basic
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.CompositeEmbedding
public import Mordell.Attr

/-!
# The Veronese embedding `φ_{dB}`

In Bombieri's proof, `(C, P)` is a curve over `k` with a divisor of degree one, `B` is a very
ample divisor on `C × C`, and `φ_B : C × C → ℙ^m` is the projective embedding given by a basis
`y = (y_0, …, y_m)` of `H⁰(C × C, 𝒪(B))`. Take an integer `d ≥ 1` and let
`v_d : ℙ^m → ℙ^{binom (d + m) m - 1}` be the Veronese map given by all monomials of degree `d`
in `y_0, …, y_m`. Then `φ_{dB} = v_d ∘ φ_B = φ_B^{(d)}` is again a projective embedding of
`C × C`.

## Main definitions

* `Faltings.CurveWithDegreeOneDivisor.veroneseDB`: the projective embedding
  `φ_{dB} = v_d ∘ φ_B : C ×_k C ⟶ ℙᴺ_k`, where `N + 1 = binom (d + m) m`.

## Implementation notes

The embedding `φ_B` is a `Faltings.ProjectiveEmbedding` of `C ×_k C` over `Spec k`, with
structure morphism `pullback.fst X.f X.f ≫ X.f`, as in
`Faltings.CurveWithDegreeOneDivisor.vojtaHeight`. The coordinates of the target are the monomials
`I : Fin (m + 1) →₀ ℕ` of total degree `d`, listed by an ordering
`σ : {I // I.degree = d} ≃ Fin (N + 1)`; such an ordering forces `N + 1 = binom (d + m) m`.
The value is the projective embedding of `Faltings.ProjectiveEmbedding.exists_veronese`: its
composite with the projection to the integral model of `ℙᴺ` is `φ_B` followed by the Veronese
morphism `v_d`, which is characterised on the standard charts. That condition determines the
embedding, since a morphism to `ℙᴺ_k` over `Spec k` is determined by its composite with that
projection. Its map on `k`-points is `Faltings.ProjectiveEmbedding.toPoint`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3, p. 619
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Faltings

/-- The **Veronese embedding** `φ_{dB} = φ_B^{(d)} = v_d ∘ φ_B : C ×_k C ⟶ ℙᴺ_k` for `d ≥ 1`,
where the homogeneous coordinates of `ℙᴺ` are the monomials of degree `d` in the coordinates of
`ℙ^m`, ordered by `σ` (so `N + 1 = binom (d + m) m`). It is the projective embedding of
`Faltings.ProjectiveEmbedding.exists_veronese`. -/
@[expose, faltings "def_bv_veronese_db"]
public noncomputable def CurveWithDegreeOneDivisor.veroneseDB {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) {m : ℕ}
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (d : ℕ) (hd : 1 ≤ d) (N : ℕ) (σ : {I : Fin (m + 1) →₀ ℕ // I.degree = d} ≃ Fin (N + 1)) :
    haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
    ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) N :=
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  (φB.exists_veronese d hd N σ).choose_spec.choose

end Faltings
