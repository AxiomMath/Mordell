module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import Mordell.FunctionField.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelOverPerfectField

/-!
# Smooth projective models of a function field

Let `K` be a field and `F` a field which is a `K`-algebra (in the application, `F/K` is an
algebraic function field of one variable). A *smooth projective model* of `F/K` is a curve
`f : C ⟶ Spec K` which is smooth, projective and geometrically integral over `K`, together with
an isomorphism of `K`-algebras `φ : K(C) ≃ F` from its function field. The function field
`K(C) = 𝒪_{C,η}` is the stalk at the generic point, a `K`-algebra through
`K ≅ Γ(Spec K, ⊤) ⟶ Γ(C, ⊤) ⟶ K(C)`.

## Main definitions

* `Faltings.FunctionField.SmoothProjectiveModel K F`: the type of smooth projective models
  `(C, φ)` of `F/K`.

## Implementation notes

The curve is a scheme `C` with its structure morphism `f : C ⟶ Spec K`. Being a curve is
`AlgebraicGeometry.IsCurve K f`, projectivity is `AlgebraicGeometry.IsProjectiveVariety K f`
(H-projectivity of `f`, i.e. `C` is a closed subscheme of some `ℙⁿ_K`), smoothness is
`AlgebraicGeometry.Smooth f` and geometric integrality is
`AlgebraicGeometry.GeometricallyIntegral f`. The `K`-algebra structure on `C.functionField` is the
one induced by `f` on global sections followed by the germ at the generic point, so `φ` is
`K`-linear for the structure coming from the curve. The definition uses neither that `F/K` is a
function field nor any property of `F` beyond being a `K`-algebra which is a field, so it is
stated in that generality.

## References

* [Stacks, Tag 0BY1], [Stacks, Tag 0BYN]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Faltings.FunctionField

/-- A *smooth projective model* of `F/K`: a smooth projective geometrically integral curve
`f : C ⟶ Spec K` over `K` together with an isomorphism of `K`-algebras
`φ : C.functionField ≃ₐ[K] F`, where `C.functionField` is a `K`-algebra through `f`. -/
@[faltings "def_ff_smooth_model"]
structure SmoothProjectiveModel (K : Type u) [Field K] (F : Type v) [Field F]
    [Algebra K F] where
  /-- The underlying scheme of the curve. -/
  C : Scheme.{u}
  /-- The structure morphism of the curve. -/
  f : C ⟶ Spec (.of K)
  /-- `C` is a curve over `K`. -/
  [isCurve : IsCurve K f]
  /-- `C` is a projective curve over `K`. -/
  [isProjectiveVariety : IsProjectiveVariety K f]
  /-- `C` is smooth over `K`. -/
  [smooth : Smooth f]
  /-- `C` is geometrically integral over `K`. -/
  [geometricallyIntegral : GeometricallyIntegral f]
  /-- The isomorphism of `K`-algebras from the function field of `C` to `F`. -/
  φ : letI : Algebra K C.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.toAlgebra
    C.functionField ≃ₐ[K] F

end Faltings.FunctionField

end


/-!
# Existence of a smooth projective model

Let `K` be a perfect field and `F/K` an algebraic function field of one variable whose field of
constants is `K`, i.e. `K` is algebraically closed in `F`. Then `F/K` has a smooth projective
model: there is a smooth, projective, geometrically integral curve `C` over `K` together with an
isomorphism of `K`-algebras `K(C) ≃ F`. The curve is the normal projective curve with function
field `F`; perfectness of `K` makes it smooth, and `K` being algebraically closed in `F` makes it
geometrically integral.

## Main results

* `Faltings.FunctionField.nonempty_smoothProjectiveModel`: for `K` perfect and
  `algebraicClosure K F = ⊥`, the type `Faltings.FunctionField.SmoothProjectiveModel K F` is
  nonempty.

## Implementation notes

The function field structure is Mathlib's: `F` is an algebra over `RatFunc K` compatible with
`K → F` and finite dimensional over it (`FunctionField K F`). The field of constants is Mathlib's
`algebraicClosure K F`, and the condition that it equals `K` is `algebraicClosure K F = ⊥`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Section 1.1
* [The Stacks Project][stacks-project], Tags 0BY1, 0BYN
-/

namespace Faltings.FunctionField

open AlgebraicGeometry CategoryTheory

universe u v

/-- A finitely generated extension `L/K` of transcendence degree one is the function field of a
normal projective curve over `K`: `L` is the function field of a variety, which is a curve since
`L` has transcendence degree one, and that curve is birational to a normal projective one. -/
private theorem exists_normal_projective_curve (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] (htr : Algebra.trdeg K L = 1) :
    ∃ X : Variety K, IsCurve K X.structureMap ∧ IsProjectiveMorphism X.structureMap ∧
      IsNormal X.toScheme ∧ Nonempty (X.toScheme.functionField ≃ₐ[K] L) := by
  let L₀ : FinitelyGeneratedFieldExtension K :=
    ⟨CommAlgCat.of K L, ⟨Field.toIsField L, inferInstance⟩⟩
  let V := (functionFieldFunctor K).objPreimage (.op L₀)
  let e₁ : L ≃ₐ[K] V.toScheme.functionField := CommAlgCat.algEquivOfIso
    ((ObjectProperty.ι _).mapIso ((functionFieldFunctor K).objObjPreimageIso (.op L₀)).unop)
  have hV : IsCurve K V.structureMap := by
    rw [isCurve_iff_trdeg_functionField_eq_one]
    exact e₁.trdeg_eq ▸ htr
  let C : Curve K := ⟨V, hV⟩
  let N := (normalProjectiveCurveToCurve K).objPreimage C
  let e₂ : V.toScheme.functionField ≃ₐ[K]
      ((normalProjectiveCurveToCurve K).obj N).obj.toScheme.functionField :=
    CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso ((functionFieldFunctor K).mapIso
      ((ObjectProperty.ι _).mapIso ((normalProjectiveCurveToCurve K).objObjPreimageIso C))).unop)
  exact ⟨_, N.property.1, N.property.2.1, N.property.2.2, ⟨(e₁.trans e₂).symm⟩⟩

/-- A variety over `K` whose function field contains no element separable over `K` outside `K` is
geometrically irreducible. -/
private theorem geometricallyIrreducible_of_separableClosure_eq_bot {K : Type u} [Field K]
    (X : Variety K) (h : separableClosure K X.toScheme.functionField = ⊥) :
    GeometricallyIrreducible X.structureMap := by
  let : Algebra K (X.toScheme.residueField (genericPoint X.toScheme)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ X.structureMap.appTop ≫
      X.toScheme.Γevaluation (genericPoint X.toScheme)).hom.toAlgebra
  let ψ : X.toScheme.functionField ≃ₐ[K] X.toScheme.residueField (genericPoint X.toScheme) :=
    AlgEquiv.ofRingEquiv (f := genericResidueEquiv X.toScheme) fun c => by
      change genericResidueEquiv _ (functionFieldAlgebraMap X c) = _
      rw [DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField X) c]
      rfl
  refine ((geometricallyIrreducible_tfae_functionField K X.toScheme X.structureMap
    (genericPoint X.toScheme) (genericPoint_spec _)).out 1 3).mpr ?_
  rw [← separableClosure.map_eq_of_algEquiv ψ, h, IntermediateField.map_bot]

/-- A normal projective curve over a perfect field `K`, whose function field is identified with an
extension `L/K` in which `K` is algebraically closed, is a smooth projective model of `L/K`: it is
regular, hence smooth over the perfect field `K`, and geometrically integral since `K` is
separably closed in its function field. -/
private theorem nonempty_smoothProjectiveModel_of_isNormal {K : Type u} {L : Type v} [Field K]
    [PerfectField K] [Field L] [Algebra K L] (X : Variety K) [IsCurve K X.structureMap]
    [IsNormal X.toScheme] (hproj : IsProjectiveMorphism X.structureMap)
    (e : X.toScheme.functionField ≃ₐ[K] L) (h : algebraicClosure K L = ⊥) :
    Nonempty (SmoothProjectiveModel K L) := by
  have : IsProjectiveVariety K X.structureMap :=
    (isProjectiveVariety_iff_isProjectiveMorphism K X.structureMap).2 hproj
  have : Smooth X.structureMap := NonsingularProjectiveModel.smooth_structureMap
    { Y := X.toScheme, structureMap := X.structureMap, isCurve := inferInstance,
      isProjectiveVariety := inferInstance,
      isRegular := (isRegular_iff_isNormal_of_isCurve K X.structureMap).2 ‹_›,
      functionFieldEquiv := @AlgEquiv.refl K _ _ _ (functionFieldAlgebra K X.structureMap) }
  have : GeometricallyIrreducible X.structureMap :=
    geometricallyIrreducible_of_separableClosure_eq_bot X <| by
      have hs : separableClosure K L = ⊥ := le_bot_iff.mp (h ▸ le_algebraicClosure K L _)
      rw [← separableClosure.map_eq_of_algEquiv e.symm, hs, IntermediateField.map_bot]
  have : GeometricallyIntegral X.structureMap :=
    .of_geometricallyReduced_of_geometricallyIrreducible _
  let eR : X.toScheme.functionField ≃+* L := e.toRingEquiv
  have he (c : K) : eR (functionFieldAlgebraMap X c) = algebraMap K L c := e.commutes c
  let : Algebra K X.toScheme.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ X.structureMap.appTop ≫
      X.toScheme.germToFunctionField ⊤ (h := ⟨⟨genericPoint _, trivial⟩⟩)).hom.toAlgebra
  let φ : X.toScheme.functionField ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := eR) fun c => by
    rw [← he, DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField X) c]
    rfl
  exact ⟨{ C := X.toScheme, f := X.structureMap, φ := φ }⟩

/-- A function field `F/K` over a perfect field `K` which is algebraically closed in `F` has a
smooth projective model. -/
@[faltings "thm_ff_smooth_projective_model"]
public theorem nonempty_smoothProjectiveModel (K F : Type*) [Field K] [PerfectField K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F]
    (h : algebraicClosure K F = ⊥) :
    Nonempty (SmoothProjectiveModel K F) := by
  have := Module.Finite.small (R := RatFunc K) (M := F)
  let e : Shrink.{_} F ≃ₐ[K] F := Shrink.algEquiv K F
  obtain ⟨hfg, htr⟩ := fg_top_and_trdeg_eq_one K F
  have : Algebra.EssFiniteType K F := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType K (Shrink.{_} F) :=
    .of_surjective e.symm.toAlgHom e.symm.surjective
  obtain ⟨X, _, hproj, _, ⟨e'⟩⟩ := exists_normal_projective_curve K (Shrink.{_} F) <| by
    simpa [htr] using e.symm.lift_trdeg_eq.symm
  exact nonempty_smoothProjectiveModel_of_isNormal X hproj (e'.trans e) h

end Faltings.FunctionField
