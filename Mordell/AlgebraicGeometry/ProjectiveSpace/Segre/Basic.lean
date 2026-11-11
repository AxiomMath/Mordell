module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Segre.Morphism

/-!
# The Segre map

For `n m : ℕ` and a base scheme `S`, the Segre morphism
`s : ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{(n+1)(m+1)-1}_S` is the morphism given by the bihomogeneous forms
`z_{ij} = x_i y_j`, where `x` and `y` are the homogeneous coordinates of the two factors. It is
the morphism to projective space defined by the invertible module `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` and
its global sections `pr₁^* x_i ⊗ pr₂^* y_j`, whose nonvanishing loci
`pr₁⁻¹D₊(x_i) ∩ pr₂⁻¹D₊(y_j)` cover the product; on the chart `D₊(x_i) ×_S D₊(y_j)` it lands in
`D₊(z_{ij})` and pulls `z_{kl}/z_{ij}` back to `(x_k/x_i) ⊗ (y_l/y_j)`. On points over a field `K`
it is `(x, y) ↦ x ⊗ y = (x_i y_j)_{i,j}`.

## Main definitions

* `Faltings.segreMorphism`: the Segre morphism `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S`, a morphism over
  `S`.
* `Faltings.segreMap`: its action on `K`-points, `ℙ(K^ι) × ℙ(K^κ) → ℙ(K^{ι × κ})`,
  `(x, y) ↦ (x_i y_j)_{(i, j)}`.

## Implementation notes

Projective space over `S` is `AlgebraicGeometry.projectiveSpaceOver n S`, the base change of the
integral model `Proj ℤ[T₀, …, Tₙ]` along `S ⟶ Spec ℤ`. The Segre morphism over `S` is the base
change of the Segre morphism of the integral models, `AlgebraicGeometry.Segre.segreMorphism n m`,
which is the morphism defined by the sections `XᵢYⱼ` of `pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`
[Stacks, Tag 01NE]: the product `ℙⁿ_S ×_S ℙᵐ_S` maps to `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the two projections to
the integral models, and the result is lifted to `ℙ^{nm+n+m}_S` along the structure morphism to
`S`. Since the formation of the morphism defined by sections commutes with pullback, this is the
morphism given by the forms `x_i y_j` over `S`.

The homogeneous coordinates of the target are indexed by `Fin (n * m + n + m + 1)`, where
`n * m + n + m = (n + 1)(m + 1) - 1`; the coordinate `z_k` is `x_i y_j` for
`(i, j) = Stacks.ProductFamilyTwist.segreIndexEquiv n m k`, which is `finProdFinEquiv` after
`finCongr`.

The map on points is stated over a field `K` and arbitrary index types (the `K`-points of the
projective spaces, as `Projectivization`); its value is computed from the chosen representatives
`Projectivization.rep`, and does not depend on that choice since the forms `x_i y_j` are
bihomogeneous of bidegree `(1, 1)`.

## References

* [Hartshorne, *Algebraic Geometry*, I Ex. 2.14, II Ex. 5.11][hartshorne1977]
* [Gao, *An Introduction to Diophantine Geometry*, Prop. 1.2.14(i)][gao2022]
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

open scoped LinearAlgebra.Projectivization

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings

/-- The **Segre morphism** `ℙⁿ_S ×_S ℙᵐ_S ⟶ ℙ^{nm+n+m}_S` over a scheme `S`, given by the forms
`x_i y_j`: the base change to `S` of the Segre morphism `AlgebraicGeometry.Segre.segreMorphism`
of the integral models, lifted along the structure morphism to `S`. -/
@[expose, faltings "def_ht_segre_map"]
public noncomputable def segreMorphism (n m : ℕ) (S : Scheme.{u}) :
    pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver m S ↘ S) ⟶
      projectiveSpaceOver (n * m + n + m) S :=
  projectiveSpaceOver.liftAtUniverse (n * m + n + m)
    (pullback.fst _ _ ≫ projectiveSpaceOver n S ↘ S)
    (pullback.lift (pullback.fst _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse n S)
        (pullback.snd _ _ ≫ projectiveSpaceOver.toIntegralAtUniverse m S)
        (terminal.hom_ext _ _) ≫
      Segre.segreMorphism.{u} n m)

variable {K : Type*} [Field K] {ι κ : Type*}

/-- The **Segre map** on points, `ℙ(K^ι) × ℙ(K^κ) → ℙ(K^{ι × κ})`,
`(x, y) ↦ (x i * y j)_{(i, j)}`. -/
@[expose]
public noncomputable def segreMap (x : ℙ K (ι → K)) (y : ℙ K (κ → K)) : ℙ K (ι × κ → K) :=
  Projectivization.mk K (fun p => x.rep p.1 * y.rep p.2) (by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
    obtain ⟨j, hj⟩ := Function.ne_iff.mp y.rep_nonzero
    exact Function.ne_iff.mpr ⟨(i, j), mul_ne_zero hi hj⟩)

/-- The Segre product of the points with coordinates `u` and `w` is the point with coordinates
`(u i * w j)_{(i, j)}`. -/
public theorem segreMap_mk {u : ι → K} {w : κ → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    segreMap (Projectivization.mk K u hu) (Projectivization.mk K w hw) =
      Projectivization.mk K (fun p : ι × κ => u p.1 * w p.2) (by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
        exact Function.ne_iff.mpr ⟨(i, j), mul_ne_zero hi hj⟩) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (Projectivization.rep_nonzero _) hu).1
    (Projectivization.mk_rep _)
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' K _ _ (Projectivization.rep_nonzero _) hw).1
    (Projectivization.mk_rep _)
  refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).2 ⟨a * b, funext fun p => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← ha, ← hb]
  ring

end Faltings
