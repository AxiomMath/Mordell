module

public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.KunnethRelativeForms
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant

/-!
# The canonical sheaf of `C × C`

Let `C` be a smooth projective geometrically integral curve over a field `k`, with structure
morphism `f : C ⟶ Spec k`, let `X = C ×_k C` and let `pr₁, pr₂ : X ⟶ C` be the projections.
The surface `X` is smooth of relative dimension `2` over `k`, and its canonical sheaf is
`K_X = ⋀² Ω_{X/k}`. Since `Ω_{X/k} ≅ pr₁^* Ω_{C/k} ⊕ pr₂^* Ω_{C/k}` with both summands
invertible, `K_X ≅ pr₁^* Ω_{C/k} ⊗ pr₂^* Ω_{C/k}`.

## Main results

* `Faltings.nonempty_exteriorPower_relativeDifferentials_pullback_iso_tensorObj`:
  `⋀² Ω_{C ×_k C / k} ≅ pr₁^* Ω_{C/k} ⊗ pr₂^* Ω_{C/k}`.

## Implementation notes

`X` is `pullback f f`, with structure morphism `pullback.fst f f ≫ f` and projections
`pullback.fst f f`, `pullback.snd f f`. The canonical sheaf is
`AlgebraicGeometry.Scheme.Modules.exteriorPower` of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` in degree `2`, the pull-backs are
`AlgebraicGeometry.Scheme.Modules.pullback`, and `⊗` is
`AlgebraicGeometry.Scheme.Modules.tensorObj`, the sheafified tensor product of `𝒪_X`-modules.

The proof goes through the Künneth decomposition of relative differential forms on `X ×_S X`
([Stacks, Tag 01V1] with the decomposition of `⋀ⁿ` of a biproduct): for `X/S` smooth of
relative dimension `N`, every summand `pr₁^* Ωᵖ ⊗ pr₂^* Ω^q` of `Ω^{2N}` with `(p, q) ≠ (N, N)`
has a factor of degree `> N` and vanishes. For a curve, `N = 1` and `Ω¹ = Ω`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 01V1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Faltings

open Stacks.WeilDeRham in
/-- For `X/S` smooth of relative dimension `N`, the Künneth projection onto the `(N, N)` summand
of `Ω^{2N}_{X ×_S X/S}` is an isomorphism: every other summand has a factor of degree `> N`. -/
@[expose] public noncomputable def topFormsIsoKunnethSummand {X S : Scheme.{u}} (f : X ⟶ S) (N : ℕ)
    [SmoothOfRelativeDimension N f] :
    Scheme.Hom.relativeDifferentialForms (pullback.fst f f ≫ f) ((N + N : ℕ) : ℤ) ≅
      kunnethSummand f (N + N) (Scheme.Hom.deRhamBoxIndexMk N N (N + N) rfl) where
  hom := kunnethProj f _ _
  inv := kunnethIncl f _ _
  hom_inv_id := by
    rw [← sum_kunnethProj_incl f (N + N), Fintype.sum_eq_single _ fun l hl => ?_]
    have hz : IsZero (kunnethSummand f _ l) := by
      refine isZero_kunnethSummand f N _ l ?_
      by_contra! hc
      have hs : l.1.1 + l.1.2 = N + N := l.2
      exact hl (Subtype.ext (Prod.ext (by simp; omega) (by simp; omega)))
    rw [hz.eq_of_tgt (kunnethProj f _ l) 0, zero_comp]
  inv_hom_id := kunnethIncl_proj_self f _ _

/-- For a smooth projective geometrically integral curve `f : C ⟶ Spec k`, the canonical sheaf
`K_X = ⋀² Ω_{X/k}` of the surface `X = C ×_k C` is isomorphic to
`pr₁^* Ω_{C/k} ⊗ pr₂^* Ω_{C/k}`. -/
@[faltings "lem_nt_canonical_c_times_c"]
theorem nonempty_exteriorPower_relativeDifferentials_pullback_iso_tensorObj
    (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f] :
    Nonempty (Scheme.Modules.exteriorPower (pullback.fst f f ≫ f).relativeDifferentials 2 ≅
      Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (pullback.fst f f)).obj f.relativeDifferentials)
        ((Scheme.Modules.pullback (pullback.snd f f)).obj f.relativeDifferentials)) := by
  let ω := Scheme.Modules.exteriorPowerOneIsoSelf f.relativeDifferentials
  exact ⟨topFormsIsoKunnethSummand f 1 ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      ((Scheme.Modules.pullback (pullback.fst f f)).mapIso ω)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
      ((Scheme.Modules.pullback (pullback.snd f f)).mapIso ω)⟩

end Faltings
