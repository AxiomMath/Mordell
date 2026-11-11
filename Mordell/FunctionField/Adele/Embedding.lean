module

public import Mordell.FunctionField.Adele.Basic
public import Mordell.FunctionField.Place.Poles

/-!
# The diagonal embedding of a function field into its adeles

Let `F/K` be an algebraic function field of one variable. Every `x ∈ F` lies in the valuation
ring `𝒪_v` of all but finitely many places `v`, so the constant family `(x)_v` is an adele.
This gives a `K`-algebra homomorphism `ι : F → 𝒜_F`, `ι(x)_v = x`, whose image is exactly the
subspace `Faltings.Adele.principal K F` of principal adeles.

## Main results

* `Faltings.Adele.exists_algHom_range_eq_principal`: there is a `K`-algebra homomorphism
  `ι : F →ₐ[K] Faltings.Adele K F` with `ι x v = x` for all `x` and all places `v`, and its range,
  as a `K`-submodule, is `Faltings.Adele.principal K F`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Section 1.5
-/

public section

namespace Faltings

/-- A function field `F/K` embeds diagonally into its adele ring: there is a `K`-algebra
homomorphism `ι : F →ₐ[K] Adele K F` with `ι x v = x` for every `x ∈ F` and every place `v`, and
its range is the subspace `Adele.principal K F` of principal adeles. -/
@[faltings "lem_ff_principal_adele_embedding"]
theorem Adele.exists_algHom_range_eq_principal (K F : Type*) [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] :
    ∃ ι : F →ₐ[K] Adele K F, (∀ (x : F) (v : Place K F), ι x v = x) ∧
      Subalgebra.toSubmodule ι.range = Adele.principal K F := by
  let ι : F →ₐ[K] Adele K F :=
    { toFun x := ⟨fun _ ↦ x, Filter.eventually_cofinite.mpr (Place.finite_setOf_notMem x)⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  refine ⟨ι, fun _ _ ↦ rfl, le_antisymm ?_ fun α hα ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact Adele.mem_principal.mpr fun _ _ ↦ rfl
  · cases isEmpty_or_nonempty (Place K F) with
    | inl _ => exact ⟨0, RestrictedProduct.ext _ _ isEmptyElim⟩
    | inr h => exact ⟨α h.some, RestrictedProduct.ext _ _ (Adele.mem_principal.mp hα h.some)⟩

end Faltings

end

