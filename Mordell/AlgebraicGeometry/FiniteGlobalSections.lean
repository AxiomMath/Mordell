module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible

/-!
# Finiteness of global sections of a line bundle

Let `k` be a field and `X` a scheme proper over `Spec k` via `p : X ⟶ Spec k`. For a line
bundle `L` on `X`, i.e. an `𝒪_X`-module locally isomorphic to `𝒪_X`, the space of global
sections `H⁰(X, L) = Γ(L, ⊤)` is a finite dimensional `k`-vector space. Here `k` acts on
`Γ(L, ⊤)` through the ring map `k ≅ Γ(Spec k, ⊤) ⟶ Γ(X, ⊤)` induced by `p`, followed by the
`Γ(X, ⊤)`-module structure of `Γ(L, ⊤)`. In particular this holds for a projective variety
over `\bar{ℚ}`, which is proper over `Spec \bar{ℚ}`.

## Main results

* `Faltings.finiteDimensional_sections_of_isProper`: global sections of a line bundle on a
  scheme proper over a field form a finite dimensional vector space.

## Implementation notes

The statement is made for a scheme proper over an arbitrary field `k`, rather than for a
projective variety over `\bar{ℚ}`: projective schemes are proper, and the finiteness holds
for proper schemes (it is the case `i = 0` of the finiteness of coherent cohomology).
A line bundle is encoded as an `𝒪_X`-module `L` such that every point of `X` has an open
neighbourhood `U` with `L|_U ≅ 𝒪_U`.

## References

* [Hartshorne, *Algebraic Geometry*, II.5.19][hartshorne1977]
* [Gao, *An Introduction to Diophantine Geometry*, Lemma 4.4.10][gao2022]
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- Restricting scalars of a finite module along a surjective ring map keeps it finite. -/
private theorem finite_compHom_of_surjective {k R M : Type*} [CommRing k] [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (φ : k →+* R)
    (hφ : Function.Surjective φ) :
    letI : Module k M := Module.compHom M φ
    Module.Finite k M := by
  letI : Algebra k R := φ.toAlgebra
  letI : Module k M := Module.compHom M φ
  haveI : IsScalarTower k R M := ⟨fun a b m => mul_smul (φ a) b m⟩
  haveI : Module.Finite k R := Module.Finite.of_surjective (Algebra.linearMap k R) hφ
  exact Module.Finite.trans R M

/-- An `𝒪_X`-module locally isomorphic to `𝒪_X` on a scheme proper over a field is
coherent. -/
private theorem isCoherent_of_locally_iso_unit (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules)
    (hL : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) :
    L.IsCoherent := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank L 1 :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mp fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hL x
      exact ⟨U, hx, ⟨e ≪≫ (Stacks.SheafOfModules.Invertible.freeUniqueIso _).symm⟩⟩
  exact Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
    k p L 1

/-- The global sections of a coherent module on a scheme proper over a Noetherian affine
scheme `S` form a finite `Γ(S, ⊤)`-module: they are the sections over `S` of the coherent
pushforward. -/
private theorem moduleFinite_sections_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f] (F : X.Modules) [F.IsCoherent] :
    letI : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom Γ(F, ⊤) f.appTop.hom
    Module.Finite Γ(S, ⊤) Γ(F, ⊤) := by
  have := ProperCoherenceWitness.isCoherent_pushforward f F
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward f).obj F)
  exact moduleFinite_sections_on_affine ((Scheme.Modules.pushforward f).obj F) ⊤
    (isAffineOpen_top S)

/-- The global sections of a line bundle on a scheme proper over a field `k` form a finite
dimensional `k`-vector space. -/
@[faltings "lem_ht_h0_finite_dimensional"]
public theorem finiteDimensional_sections_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : X.Modules)
    (hL : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    FiniteDimensional k Γ(L, ⊤) := by
  have := isCoherent_of_locally_iso_unit k p L hL
  letI : Module Γ(Spec (.of k), ⊤) Γ(L, ⊤) := Module.compHom Γ(L, ⊤) p.appTop.hom
  have := moduleFinite_sections_of_isProper p L
  exact finite_compHom_of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2

end Faltings
