module
public import Mordell.BombieriVojta.DerivativeEstimate.PlaneRelation
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The exceptional set `Z`

Let `C` be a curve over a field `k` and `x₀, …, xₙ` sections of `𝒪(D)` for a divisor `D`
(in Bombieri's setting a basis of `H⁰(C, 𝒪(NP))`), with affine coordinates
`ξ_{νj} = x_ν / x_j` and `ξ_a = ξ_{a0}`. The exceptional set `Z` consists of the points `z` such
that

1. `x₀(z) = 0`; or
2. `x₀(z) ≠ 0` and `ξ₁₀ - ξ₁₀(z)` is not a uniformizer at `z`; or
3. `x₀(z) ≠ 0` and `D_{g_{νj}}(ξ₁₀(z)) = 0` for some `ν ≠ j` with `(ν, j) ∉ {(1, 0), (0, 1)}`,
   where `g_{νj}` is the plane relation of `ξ_{νj}` over `ξ₁₀` and
   `D_g = Res_X(g, ∂g/∂X)` its discriminant with respect to `X`; or
4. `x₀(z) ≠ 0` and `ξ_a - ξ_a(z)` is not a uniformizer at `z` for some `a ∈ {1, …, n}`.

Outside `Z` the function `ς = ξ₁₀ - ξ₁₀(z)` is a local parameter at `z`, the branches `ξ_{νj}`
are power series in `ς`, and the discriminants needed for Eisenstein's theorem do not vanish at
`ς = 0` (Bombieri's erratum to the proof of Lemma 6).

## Main definitions

* `Faltings.BombieriSiegel.exceptionalSet`: the set `Z` of `k`-points of `C`.

## Implementation notes

A point is a `k`-point, a section `z : Spec k ⟶ C` of the structure morphism `f`, with local ring
the stalk at `p = z (closedPoint k)`; the source's `C(k̄)` is the case of the base change of `C`
to `k̄`, as in `Faltings.FunctionField.finite_setOf_maximalIdeal_ne_span_sub`. Sections of
`𝒪(D)` are rational functions `x : Fin (n + 1) → k(C)` (the Riemann–Roch model of
`Faltings.BombieriSiegel.IsGenericBasis`), and `x₀(z) = 0` means `0 < ord_p x₀ + D(p)`.
The constants of the stalk are `c : k → 𝒪_{C,p}`, `(ΓSpecIso k).inv ≫ f.appTop ≫ germ`.
"`ξ - ξ(z)` is not a uniformizer" is written `∀ g ∈ 𝒪_{C,p}, g = ξ in k(C) → ∀ a : k,
𝔪_p ≠ (g - c a)`, and "`ξ(z) = a`" is `g - c a ∈ 𝔪_p` for the germ `g` of `ξ`; this avoids naming
an evaluation map. The discriminant is `Polynomial.resultant g (derivative g) e (e - 1)` with
`e = deg_X g`, and `g_{νj}` is `Faltings.FunctionField.planeRelation`, which needs `ξ₁₀`
transcendental over `k`; that is the hypothesis `ht`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, Lemma 6 and its
  proof, p. 628, with the Errata-Corrige (1991)
-/

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial

universe u

namespace Faltings.BombieriSiegel

/-- The **exceptional set** `Z` of Bombieri's Lemma 6: for sections `x₀, …, xₙ` of `𝒪(D)` on the
curve `C` over `k` (rational functions in `L(D)`), with `ξ_{νj} = x_ν / x_j`, the `k`-points `z`
of `C` such that `x₀(z) = 0`; or `x₀(z) ≠ 0` and `ξ₁₀ - ξ₁₀(z)` is not a uniformizer at `z`; or
`x₀(z) ≠ 0` and the discriminant `D_{g_{νj}} = Res_X(g_{νj}, ∂g_{νj}/∂X)` of the plane relation
`g_{νj}` vanishes at `ξ₁₀(z)` for some `ν ≠ j` with `(ν, j) ∉ {(1, 0), (0, 1)}`; or `x₀(z) ≠ 0`
and `ξ_{a0} - ξ_{a0}(z)` is not a uniformizer at `z` for some `a ≠ 0`. -/
@[expose, faltings "def_bvs_exceptional_set"]
public noncomputable def exceptionalSet (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsLocallyNoetherian C] (D : C →₀ ℤ) {n : ℕ}
    (x : Fin (n + 1) → C.functionField)
    (ht : letI := functionFieldAlgebra k f; Transcendental k (x 1 / x 0)) :
    Set (Spec (.of k) ⟶ C) :=
  letI := functionFieldAlgebra k f
  {z | z ≫ f = 𝟙 _ ∧
    let p := z (closedPoint k)
    let c : k → C.presheaf.stalk p :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.germ ⊤ p trivial).hom
    let NotUniformizer : C.functionField → Prop := fun ξ =>
      ∀ g : C.presheaf.stalk p, algebraMap _ C.functionField g = ξ →
        ∀ a : k, maximalIdeal (C.presheaf.stalk p) ≠ Ideal.span {g - c a}
    0 < C.ord (x 0) p + D p ∨
    (¬0 < C.ord (x 0) p + D p ∧ NotUniformizer (x 1 / x 0)) ∨
    (¬0 < C.ord (x 0) p + D p ∧ ∃ ν j : Fin (n + 1), ν ≠ j ∧ (ν, j) ≠ (1, 0) ∧ (ν, j) ≠ (0, 1) ∧
      ∃ g : C.presheaf.stalk p, algebraMap _ C.functionField g = x 1 / x 0 ∧
        ∃ a : k, g - c a ∈ maximalIdeal (C.presheaf.stalk p) ∧
          let G := FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) ht
          (G.resultant (derivative G) G.natDegree (G.natDegree - 1)).eval a = 0) ∨
    (¬0 < C.ord (x 0) p + D p ∧ ∃ a : Fin (n + 1), a ≠ 0 ∧ NotUniformizer (x a / x 0))}

end Faltings.BombieriSiegel
