module
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
import StacksFrontier.AlgebraicGeometry.GradedSectionsModule.IntGraded
import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import Mordell.BombieriVojta.Representative.Vanishing
import Mordell.BombieriVojta.Representative.Chart

/-!
# Non-zero sections of `𝒪(V)` in affine coordinates

In Section 8 of Bombieri's proof of the Mordell conjecture, `C` is a curve over a number field `k`,
`ψ = φ_{NP} × φ_{NP} : C × C → ℙⁿ × ℙⁿ` has coordinates `(x, x')`, `φ_B : C × C → ℙᵐ` has
coordinates `y`, and a global section `s` of `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` is given by a
representative: forms `F_0, …, F_m` of bidegree `(δ₁, δ₂)` over `k` with
`F_i|_{C × C} = s · y_i^d`. Then `s ≠ 0` if and only if
`F_i(ξ, ξ') = (F_i(x, x') / (x_0^{δ₁} x_0'^{δ₂}))|_{C × C} ≠ 0` in `k(C × C)` for some `i`.
Indeed `s = 0` if and only if every `F_i|_{C × C}` vanishes, since the sections `y_i^d` have no
common zero. On the open set `W` of `C × C` where `x_0 x_0'` does not vanish, which is non-empty
because `x_0` does not vanish identically on `C`, the restriction of `F_i` is
`c_i · x_0^{δ₁} x_0'^{δ₂}` with `x_0^{δ₁} x_0'^{δ₂}` a generator, and the germ of `c_i` at the
generic point is `F_i(ξ, ξ')`. On the integral scheme `C × C`, a section of an invertible sheaf
vanishing on `W` vanishes, and a function on `W` vanishes if and only if its germ does.

## Main results

* `Faltings.IsVojtaRepresentative.ne_zero_iff`: if `F` is a representative of `s`, then `s ≠ 0` if
  and only if `Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) F_i ≠ 0` for some `i`.

## Implementation notes

* The setting is that of `Faltings.exists_isVojtaRepresentative_iff`: `C × C` is the fibre
  product `pullback f f` over `Spec k`, `ψ` is `pullback.map _ _ _ _ φNP φNP (𝟙 _) _ _` and `φ_B`
  is a morphism `pullback f f ⟶ ℙᵐ_k`.
* `pr₁^*, pr₂^* : k(C) →ₐ[k] k(C × C)` are `AlgebraicGeometry.functionFieldMapAlgHom` of the two
  projections, with the `k`-algebra structures `AlgebraicGeometry.stalkAlgebraOver` at the
  generic points.
* The coordinates `x_ν ∈ k(C)` are trivialised by `x_0`: `x_ν` is the rational function
  `T_ν / T_0` on `ℙⁿ`, pulled back along `φ_{NP}`. Since
  `Faltings.BombieriVojta.affineEvaluation` is invariant under rescaling `x`, `F(ξ, ξ')` is
  `affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂) F`. The non-vanishing of `x_0` and `y_0` is the
  non-emptiness of the charts `φ_{NP}^{-1} D₊(T_0)` and `φ_B^{-1} D₊(T_0)`.
* The forms of the representative have coefficients in `Γ(Spec k, ⊤)`, read in `k` through
  `AlgebraicGeometry.Scheme.ΓSpecIso`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open Stacks.ProjectiveFromSections (resT resO resM)

namespace Faltings

universe u

/-- Let `C` be a smooth projective geometrically integral curve of genus `≥ 2` over a number
field `k`, with a divisor `P` of degree one, `φNP : C ⟶ ℙⁿ_k` (`N ≥ 2g + 1`, `n = N - g`) and
`φB : C ×_k C ⟶ ℙᵐ_k` closed immersions over `k`, and `ψ = φNP × φNP`. Let `d₁, d₂, d` be positive
integers with `dᵢ + s d = N δᵢ`. In `k(C × C)` let `ξ_ν = pr₁^* x_ν`, `ξ'_ν = pr₂^* x_ν`, where
`x_ν = T_ν / T_0` pulled back along `φNP`. If `F = (F_i)` is a representative
(`IsVojtaRepresentative`) of the global section `s` of `vojtaLineBundle ψ φB δ₁ δ₂ d`, then
`s ≠ 0` if and only if `F_i(ξ, ξ') ≠ 0` for some `i`, where `F(ξ, ξ')` is
`BombieriVojta.affineEvaluation`. -/
@[faltings "lem_bvs_basic_system_nonzero"]
public theorem IsVojtaRepresentative.ne_zero_iff (k : Type u) [Field k] [NumberField k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] (hg : 2 ≤ genus f)
    (P : C →₀ ℤ) (hPclosed : ∀ Q ∈ P.support, IsClosed ({Q} : Set C))
    (hP : ∑ᶠ Q : C, P Q * (f.residueDegree Q : ℤ) = 1)
    (sB : ℕ) (hsB : 1 ≤ sB) (N : ℕ) (hN : 2 * genus f + 1 ≤ N) {n m : ℕ} (hn : n = N - genus f)
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    [IsClosedImmersion φNP]
    (φB : pullback f f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) = pullback.fst f f ≫ f)
    [IsClosedImmersion φB]
    [IsIntegral (pullback f f)]
    (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 1 ≤ d)
    (hδd₁ : d₁ + sB * d = N * δ₁) (hδd₂ : d₂ + sB * d = N * δ₂)
    (hx₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set C).Nonempty)
    (hy₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set (pullback f f : Scheme.{u})).Nonempty)
    {s : Γ(vojtaLineBundle
      (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) φB δ₁ δ₂ d, ⊤)}
    {F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤)}
    (hF : IsVojtaRepresentative
      (pullback.map f f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) φB δ₁ δ₂ d s F) :
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    haveI : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0)) := hx₀.to_subtype
    -- the coordinates `x_ν = T_ν / T_0` pulled back along `φNP`, in `k(C)`
    let x : Fin (n + 1) → C.functionField := fun ν =>
      C.germToFunctionField _
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X ν)
              (by simpa using MvPolynomial.isHomogeneous_X _ ν))))
    -- the two projections `pr₁^*, pr₂^* : k(C) → k(C × C)`
    let pr₁ := functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
    let pr₂ := functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm
    (s ≠ 0 ↔ ∃ i, BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂)
      ⟨(F i).map (Scheme.ΓSpecIso (.of k)).hom.hom, fun _ hc =>
        hF.1 i fun h => hc (by rw [MvPolynomial.coeff_map, h, map_zero])⟩ ≠ 0) := by
  intro x pr₁ pr₂
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  have : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
      projChart.{u} n 0) := hx₀.to_subtype
  set π := projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)
  set ψ := pullback.map f f π π φNP φNP (𝟙 _) (by simp [π, hφNP]) (by simp [π, hφNP])
  have h₁ : ψ ≫ pullback.fst π π = pullback.fst f f ≫ φNP := pullback.lift_fst _ _ _
  have h₂ : ψ ≫ pullback.snd π π = pullback.snd f f ≫ φNP := pullback.lift_snd _ _ _
  have hσ : ψ ≫ pullback.fst π π ≫ π = pullback.fst f f ≫ f := by
    rw [← Category.assoc, h₁, Category.assoc, hφNP]
  have hc₀ : ∀ a, algebraMap k (pullback f f : Scheme.{u}).functionField
      ((Scheme.ΓSpecIso (.of k)).hom.hom a) =
        (pullback f f : Scheme.{u}).presheaf.germ ⊤ (genericPoint _) trivial
          ((ψ ≫ pullback.fst π π ≫ π).appTop a) := by
    intro a
    rw [hσ]
    change ((pullback f f : Scheme.{u}).presheaf.germ ⊤ (genericPoint _) trivial).hom
      ((pullback.fst f f ≫ f).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom a))) = _
    have e := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
      RingHom.id_apply] at e
    rw [e]
  have key : ∀ i, vojtaFormRestriction ψ δ₁ δ₂ (F i) = 0 ↔
      BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂)
        ⟨(F i).map (Scheme.ΓSpecIso (.of k)).hom.hom, fun _ hc =>
          hF.1 i fun h => hc (by rw [MvPolynomial.coeff_map, h, map_zero])⟩ = 0 := fun i =>
    vojtaFormRestriction_eq_zero_iff 0 φNP (pullback.fst f f) (pullback.snd f f) ψ h₁ h₂ pr₁ pr₂
      (fun _ => rfl) (fun _ => rfl) (Scheme.ΓSpecIso (.of k)).hom.hom hc₀ δ₁ δ₂ (F i) (hF.1 i) _
  rw [Ne, hF.eq_zero_iff_vojtaFormRestriction, not_forall]
  exact exists_congr fun i => not_congr (key i)

end Faltings
