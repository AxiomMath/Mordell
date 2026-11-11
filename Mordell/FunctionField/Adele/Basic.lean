module

public import Mordell.FunctionField.Place.Basic

/-!
# The adele ring of a function field

Let `F/K` be a field extension (in the application an algebraic function field of one variable)
and let `ℙ_F` be the set of places of `F/K`. The *adele ring* `𝒜_F` is the restricted product
`∏'_{v ∈ ℙ_F} (F, 𝒪_v)` with respect to the cofinite filter: the families `(α_v)_v` of elements of
`F` with `α_v ∈ 𝒪_v` for all but finitely many places `v`, with componentwise operations. Since
every place contains the image of `K`, the constant families `(c)_v` for `c ∈ K` are adeles, and
they make `𝒜_F` a commutative `K`-algebra.

## Main definitions

* `Faltings.Adele K F`: the adele ring `𝒜_F` of `F/K`, as a `RestrictedProduct`.
* `Faltings.Adele.instAlgebra`: the `K`-algebra structure on `𝒜_F`, with structure map
  `c ↦ (algebraMap K F c)_v`.

## Implementation notes

The commutative ring structure and the `K`-module structure are Mathlib's instances on a
restricted product of rings along subrings (`RestrictedProduct.instCommRingCoeOfSubringClass`,
`RestrictedProduct.instModuleCoeOfSMulMemClass`); only the algebra structure is supplied here.
The definition uses neither that `K` is a field nor that `F/K` is a function field, so it is
stated for a commutative ring `K` and an arbitrary `K`-algebra `F` which is a field.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.5.1
-/

namespace Faltings

@[expose] public section

variable (K F : Type*) [CommRing K] [Field F] [Algebra K F]

/-- The *adele ring* `𝒜_F` of `F/K`: the restricted product of copies of `F` over the places `v`
of `F/K`, with respect to the valuation rings `𝒪_v` and the cofinite filter. An element is a family
`(α_v)_v` with `α_v ∈ 𝒪_v` for all but finitely many `v`; operations are componentwise. -/
@[faltings "def_ff_adele"]
abbrev Adele : Type _ :=
  RestrictedProduct (fun _ : Place K F ↦ F) (fun v ↦ v.toSubalgebra) Filter.cofinite

/-- The `K`-algebra structure on the adele ring `𝒜_F`: `c ∈ K` maps to the constant family
`(c)_v`, which is an adele since every place contains the image of `K`. -/
@[faltings "def_ff_adele"]
instance Adele.instAlgebra : Algebra K (Adele K F) where
  __ := RestrictedProduct.instModuleCoeOfSMulMemClass ..
  algebraMap.toFun c :=
    ⟨fun _ ↦ algebraMap K F c, .of_forall fun v ↦ v.toSubalgebra.algebraMap_mem c⟩
  algebraMap.map_one' := by ext; exact (algebraMap K F).map_one
  algebraMap.map_mul' _ _ := by ext; exact (algebraMap K F).map_mul ..
  algebraMap.map_add' _ _ := by ext; exact (algebraMap K F).map_add ..
  algebraMap.map_zero' := by ext; exact (algebraMap K F).map_zero
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := by ext; apply Algebra.smul_def

end

end Faltings

/-!
# Integral adeles of a function field

Let `F/K` be a field extension with places `ℙ_F` and adele ring `𝒜_F`. The *integral adeles*
`𝒜_F(0)` are the adeles `α` with `α_v ∈ 𝒪_v` for *every* place `v`, not merely for all but
finitely many. Since each `𝒪_v` is a `K`-subalgebra of `F`, they form a `K`-subspace of `𝒜_F`.

## Main definitions

* `Faltings.Adele.integral K F`: the `K`-submodule `𝒜_F(0)` of `Faltings.Adele K F`.

## Main results

* `Faltings.Adele.mem_integral`: `α ∈ 𝒜_F(0)` if and only if `α_v ∈ 𝒪_v` for every place `v`.

## Implementation notes

`𝒜_F(0)` is in fact a `K`-subalgebra of `𝒜_F` (the product of the rings `𝒪_v`); it is stated as a
`Submodule`, the form in which it enters quotients such as `𝒜_F / (𝒜_F(0) + P_F)`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.5.3
-/

namespace Faltings

@[expose] public section

variable (K F : Type*) [CommRing K] [Field F] [Algebra K F]

/-- The *integral adeles* `𝒜_F(0)`: the `K`-subspace of the adele ring `𝒜_F` consisting of the
adeles `α` with `α_v ∈ 𝒪_v` for every place `v` of `F/K`. -/
@[faltings "def_ff_integral_adele"]
def Adele.integral : Submodule K (Adele K F) where
  carrier := {α | ∀ v, α v ∈ v.toSubalgebra}
  add_mem' h₁ h₂ v := add_mem (h₁ v) (h₂ v)
  zero_mem' v := zero_mem v.toSubalgebra
  smul_mem' c _ h v := v.toSubalgebra.smul_mem (h v) c

variable {K F} in
/-- An adele `α` is integral if and only if `α_v ∈ 𝒪_v` for every place `v`. -/
@[simp]
theorem Adele.mem_integral {α : Adele K F} : α ∈ Adele.integral K F ↔ ∀ v, α v ∈ v.toSubalgebra :=
  Iff.rfl

end

end Faltings

/-!
# The principal adeles of a function field

Let `F/K` be a field extension with set of places `ℙ_F` and adele ring `𝒜_F`. The *principal
adeles* are the constant families: the adeles `α` with `α_v = α_w` for all places `v, w`. They form
a `K`-subspace `P_F` of `𝒜_F`, closed under the componentwise operations.

## Main definitions

* `Faltings.Adele.principal K F`: the `K`-submodule `P_F` of constant families in
  `Faltings.Adele K F`.

## Main results

* `Faltings.Adele.mem_principal`: `α ∈ P_F` if and only if `α_v = α_w` for all places `v, w`.

## Implementation notes

The subspace is defined by the condition on components, as in the source, not as the range of the
diagonal map `F → 𝒜_F`; that the two agree is a separate result. Constant families are closed
under the operations for any commutative ring `K`, so `K` need not be a field.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.5.1
-/

@[expose] public section

namespace Faltings

variable (K F : Type*) [CommRing K] [Field F] [Algebra K F]

/-- The *principal adeles* `P_F`: the `K`-subspace of the adele ring `𝒜_F` consisting of the
constant families, i.e. the adeles `α` with `α_v = α_w` for all places `v, w` of `F/K`. -/
@[faltings "def_ff_principal_adeles"]
def Adele.principal : Submodule K (Adele K F) where
  carrier := {α | ∀ v w : Place K F, α v = α w}
  add_mem' ha hb v w := by simp [ha v w, hb v w]
  zero_mem' _ _ := rfl
  smul_mem' c α ha v w := by simp [ha v w]

variable {K F} in
/-- An adele `α` is principal if and only if `α_v = α_w` for all places `v, w`. -/
@[simp]
theorem Adele.mem_principal {α : Adele K F} :
    α ∈ Adele.principal K F ↔ ∀ v w : Place K F, α v = α w :=
  Iff.rfl

end Faltings
