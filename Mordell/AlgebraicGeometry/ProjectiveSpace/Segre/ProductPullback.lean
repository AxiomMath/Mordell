module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Product
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Segre.Pullback

/-!
# Pullback of `𝒪(1)` under a Segre product

Let `S` be a scheme, `X` a scheme, and `f : X ⟶ ℙʳ_S`, `ψ : X ⟶ ℙᵐ_S` morphisms agreeing over
`S`. The pullback of the hyperplane sheaf along their Segre product
`f ⊗ ψ : X ⟶ ℙ^{(r+1)(m+1)-1}_S` is the tensor product of the two pullbacks,
`(f ⊗ ψ)^* 𝒪(1) ≅ f^* 𝒪(1) ⊗ ψ^* 𝒪(1)`. This follows from the Segre pullback
`s^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)` by pulling back along `(f, ψ)`, since
`pr₁ ∘ (f, ψ) = f` and `pr₂ ∘ (f, ψ) = ψ`.

## Main results

* `Faltings.nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso`:
  `(f ⊗ ψ)^* 𝒪(1) ≅ f^* 𝒪(1) ⊗ ψ^* 𝒪(1)` as modules on `X`.

## Implementation notes

The hyperplane sheaf on `ℙⁿ_S` is `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`,
and the tensor product of modules on `X` is `Stacks.SheafOfModules.Tensor.sheafTensor` for the
structure sheaf of `X`, the tensor product used by `AlgebraicGeometry.externalTensorProduct`.
The source works with a projective variety `X` over `Q̄`, that is `S = Spec Q̄`; the statement
holds for any base scheme `S` and any `S`-scheme `X`.

## References

* [Gao, *An Introduction to Diophantine Geometry*, proof of Prop. 5.1.3(iii)][gao2022]
* [Hartshorne, *Algebraic Geometry*, II Ex. 5.11][hartshorne1977]
-/

open AlgebraicGeometry CategoryTheory Limits Stacks.AmpleProjectiveImmersion

universe u

namespace Faltings

/-- For `g ≫ p = f`, the iterated pullback `g^* p^* M` is `f^* M`. -/
private noncomputable def pullbackPullbackIsoOfEq {X Y Z : Scheme.{u}} {g : X ⟶ Y}
    {p : Y ⟶ Z} {f : X ⟶ Z} (h : g ≫ p = f) (M : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullbackComp g p).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

/-- **Pullback of `𝒪(1)` under a Segre product**: for morphisms `f : X ⟶ ℙʳ_S` and
`ψ : X ⟶ ℙᵐ_S` agreeing over `S`, the Segre product `Faltings.segreProduct f ψ h` satisfies
`(f ⊗ ψ)^* 𝒪(1) ≅ f^* 𝒪(1) ⊗ ψ^* 𝒪(1)`. -/
@[faltings "lem_ht_product_embedding_pullback"]
public theorem nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso
    {S X : Scheme.{u}} {r m : ℕ}
    (f : X ⟶ projectiveSpaceOver r S) (ψ : X ⟶ projectiveSpaceOver m S)
    (h : f ≫ projectiveSpaceOver r S ↘ S = ψ ≫ projectiveSpaceOver m S ↘ S) :
    Nonempty ((Scheme.Modules.pullback (segreProduct f ψ h)).obj
        (projectiveSpaceTwistingSheaf (r * m + r + m) S) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback f).obj (projectiveSpaceTwistingSheaf r S))).obj
        ((Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf m S))) := by
  obtain ⟨α⟩ := nonempty_pullback_segreMorphism_projectiveSpaceTwistingSheaf_iso r m S
  exact ⟨(pullbackPullbackIsoOfEq (g := pullback.lift f ψ h) (p := segreMorphism r m S)
      rfl _).symm ≪≫
    (Scheme.Modules.pullback (pullback.lift f ψ h)).mapIso α ≪≫
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (pullback.lift f ψ h) _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      (pullbackPullbackIsoOfEq (pullback.lift_fst _ _ _) _)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
      (pullbackPullbackIsoOfEq (pullback.lift_snd _ _ _) _)⟩

end Faltings
