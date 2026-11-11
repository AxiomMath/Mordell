module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Embedding

/-!
# Very ample line bundles

Let `X` be a projective variety over a field `k`, with structure morphism `f : X ⟶ Spec k`.
A line bundle `L` on `X` is *very ample* if there is a projective embedding
`φ : X ⟶ ℙⁿ_k` of `X` with `L ≅ φ^* 𝒪(1)`.

## Main definitions

* `Faltings.IsVeryAmple`: `L` is isomorphic to the pullback of the hyperplane sheaf `𝒪(1)`
  along some projective embedding of `X`.

## Implementation notes

A line bundle is an invertible `𝒪_X`-module, i.e. an `L : X.Modules` with
`Stacks.Ample.IsInvertibleModule X L`. The hyperplane sheaf on `ℙⁿ_k` is
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec k)`, the pullback of the
degree-one twisting sheaf on `Proj ℤ[T₀, …, Tₙ]`, and pullback of modules is
`AlgebraicGeometry.Scheme.Modules.pullback`. The embedding ranges over all projective spaces,
so `n` is existentially quantified together with the embedding. This is the absolute notion of
[Hartshorne, II.7] for a projective variety over a field: the embedding is a closed immersion
into `ℙⁿ_k` over `k`, which for proper `X` agrees with Stacks' relative notion
(an immersion into `ℙ(ℰ)` over `Spec k`). The base field is an arbitrary field `k`; the case of
the source is `k = \bar{ℚ}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.7][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- A line bundle `L` on a projective variety `X` over a field `k` (structure morphism
`f : X ⟶ Spec k`) is **very ample** if `L ≅ φ^* 𝒪(1)` for some projective embedding
`φ : X ⟶ ℙⁿ_k`. -/
@[expose, faltings "def_ht_very_ample"]
public def IsVeryAmple {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  ∃ (n : ℕ) (φ : ProjectiveEmbedding f n),
    Nonempty (L ≅ (Scheme.Modules.pullback φ.hom).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))))

end Faltings


/-!
# Ample line bundles and ample classes

Let `X` be a projective variety over a field `k`, with structure morphism `f : X ⟶ Spec k`.
A line bundle `L` on `X` is *ample* if some positive tensor power `L^{⊗ e}`, `e ≥ 1`, is very
ample. A class `c ∈ Pic(X) ⊗ ℚ` is *ample* if `e • c = [L] ⊗ 1` for some integer `e ≥ 1` and
some ample line bundle `L`.

## Main definitions

* `Faltings.IsAmple`: `L^{⊗ e}` is very ample for some `e ≥ 1`.
* `Faltings.IsAmpleClass`: a class `c ∈ Pic(X) ⊗_ℤ ℚ` some positive multiple of which is the
  image `[L] ⊗ 1` of the class of an ample line bundle.

## Implementation notes

A line bundle is an `L : X.Modules` with `Stacks.Ample.IsInvertibleModule X L`; its tensor
powers are `Stacks.Ample.tensorPowModule X L e` (Stacks Tag 01CU), which are again invertible.
`Pic(X)` is `X.picardGroup` (Stacks Tag 01CX) and the class of `L` is `X.picardClass L _`;
`Pic(X) ⊗ ℚ` is the tensor product `X.picardGroup ⊗[ℤ] ℚ` of abelian groups. This is the
absolute notion of [Hartshorne, II.7] for a projective variety over a field (ample defined via a
very ample power), not Stacks' Tag 01PS; for projective varieties over a field the two agree.
The base field is an arbitrary field `k`; the case of the source is `k = \bar{ℚ}`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
* [Hartshorne, *Algebraic Geometry*, II.7][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory TensorProduct

namespace Faltings

/-- A line bundle `L` on a projective variety `X` over a field `k` (structure morphism
`f : X ⟶ Spec k`) is **ample** if `L^{⊗ e}` is very ample for some integer `e ≥ 1`. -/
@[expose, faltings "def_ht_ample"]
public def IsAmple {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  ∃ e : ℤ, 1 ≤ e ∧ IsVeryAmple f (Stacks.Ample.tensorPowModule X L e)

/-- A class `c ∈ Pic(X) ⊗ ℚ` on a projective variety `X` over a field `k` is **ample** if
`e • c = [L] ⊗ 1` for some integer `e ≥ 1` and some ample line bundle `L`. -/
@[expose, faltings "def_ht_ample"]
public def IsAmpleClass {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (c : X.picardGroup ⊗[ℤ] ℚ) : Prop :=
  ∃ (e : ℤ) (L : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X L),
    1 ≤ e ∧ IsAmple f L ∧ e • c = X.picardClass L ‹_› ⊗ₜ[ℤ] (1 : ℚ)

end Faltings
