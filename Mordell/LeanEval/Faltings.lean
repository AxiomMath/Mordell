module

public import Mathlib
public import Mordell.FunctionField.Adele.Basic
public import Mordell.FunctionField.Adele.Embedding
public import Mordell.FunctionField.Genus
public import Mordell.FunctionField.Place.Basic
public import Mordell.FunctionField.Place.Poles
public import Mordell.MordellConjecture.FunctionField

/-!
# Faltings' theorem in the form of the LeanEval problem `faltings`

The statement of the LeanEval benchmark problem `faltings`
(`LeanEval/AlgebraicGeometry/Faltings.lean` of `leanprover/lean-eval`), verbatim: its definitions of
places, adeles and the genus of a function field of one variable, following Stichtenoth, and its
two theorems, that an element of a function field has finitely many poles and that a function
field of genus at least two over a number field has finitely many places of degree one.

## Main results

* `LeanEval.AlgebraicGeometry.Faltings.finite_setOf_place_notMem`: finitely many poles.
* `LeanEval.AlgebraicGeometry.Faltings.faltings`: the Mordell conjecture.

## Implementation notes

The places, adeles, integral adeles and genus of the problem are its own definitions; the library
states the same objects as `Faltings.Place`, `Faltings.Adele`, `Faltings.Adele.integral`,
`Faltings.Adele.principal` and `Faltings.genus`. The two theorems are deduced from
`Faltings.Place.finite_setOf_notMem` and `Faltings.finite_setOf_place_isDegreeOne` through:

* `Faltings.LeanEval.placeEquiv`: the places of the problem are the places of the library (the
  same subring with the same two properties);
* `Faltings.LeanEval.residueFieldLinearEquiv`: corresponding places have `K`-isomorphic residue
  fields, so the places of degree one correspond;
* `Faltings.LeanEval.adeleLinearEquiv`: the two adele rings are `K`-isomorphic by reindexing along
  `placeEquiv`, carrying the integral adeles onto `Faltings.Adele.integral` and the image of the
  diagonal `F → 𝒜_F` onto `Faltings.Adele.principal`; hence `Faltings.LeanEval.genus_eq`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009]
* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
-/

@[expose] public section

namespace LeanEval.AlgebraicGeometry.Faltings

section ValuationSubalgebra

variable (R F : Type*) [CommSemiring R] [Field F] [Algebra R F]

@[ext] structure ValuationSubalgebra extends Subalgebra R F, ValuationSubring F

end ValuationSubalgebra

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

class BundledFunctionField extends
  Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F, FunctionField K F

/-- The type of places of a 1-dimensional function field. See [Stichtenoth,
Definition 1.1.4 and 1.1.8]. We omit the condition `toSubalgebra ≠ ⊥` since it is automatic. -/
@[ext] structure Place extends ValuationSubalgebra K F where
  ne_top : toSubalgebra ≠ ⊤

instance : SetLike (Place K F) F where
  coe v := v.carrier
  coe_injective _ _ := Place.ext

instance : SMulMemClass (Place K F) K F where
  smul_mem {v} r _ h := v.smul_mem h r

instance : SubringClass (Place K F) F where
  mul_mem {v} := v.mul_mem
  one_mem {v} := v.one_mem
  add_mem {v} := v.add_mem
  zero_mem {v} := v.zero_mem
  neg_mem {v} := v.toValuationSubring.neg_mem _

variable (v : Place K F)

instance : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

instance : Algebra v F := inferInstanceAs (Algebra v.toSubalgebra F)
instance : IsScalarTower K v F := inferInstanceAs (IsScalarTower K v.toSubalgebra F)
instance : IsFractionRing v F := inferInstanceAs (IsFractionRing v.toValuationSubring F)
instance : ValuationRing v := inferInstanceAs (ValuationRing v.toValuationSubring)

end LeanEval.AlgebraicGeometry.Faltings

/-! ### Places -/

namespace Faltings.LeanEval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The places of `F/K` in the sense of the problem are the places of the library: both are a
`K`-subalgebra of `F` which is a valuation subring and is proper. -/
def placeEquiv : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F ≃ Faltings.Place K F where
  toFun v := { v.toSubalgebra, v.toValuationSubring with ne_top := v.ne_top }
  invFun w :=
    { toValuationSubalgebra := { w.toSubalgebra, w.toValuationSubring with }
      ne_top := w.ne_top }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem mem_placeEquiv {v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F} {x : F} :
    x ∈ (placeEquiv v).toSubalgebra ↔ x ∈ v :=
  Iff.rfl

end Faltings.LeanEval

namespace LeanEval.AlgebraicGeometry.Faltings

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

variable {F}

/-- [Stichtenoth, Corollary 1.3.4] (finitely many poles). -/
theorem finite_setOf_place_notMem [BundledFunctionField K F] (x : F) :
    {v : Place K F | x ∉ v}.Finite :=
  (_root_.Faltings.Place.finite_setOf_notMem x).preimage
    _root_.Faltings.LeanEval.placeEquiv.injective.injOn

variable (F)

open scoped RestrictedProduct

/-- [Stichtenoth, Definition 1.5.2]. -/
abbrev Adele : Type _ := RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ v) Filter.cofinite

instance : CommRing (Adele K F) := RestrictedProduct.instCommRingCoeOfSubringClass ..

open RestrictedProduct

variable {F}

/-- The principal adele associated to an element in the function field. -/
def Adele.principal [BundledFunctionField K F] : F →+* Adele K F where
  toFun x := ⟨fun _ ↦ x, finite_setOf_place_notMem K x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (F)

instance [BundledFunctionField K F] : Algebra F (Adele K F) where
  smul x a := ⟨x • a, (Adele.principal K x * a).2⟩
  algebraMap := Adele.principal K
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := rfl

-- TODO: generalize this to RestrictedProduct
instance : Algebra K (Adele K F) where
  __ := RestrictedProduct.instModuleCoeOfSMulMemClass ..
  algebraMap.toFun x := ⟨fun _ ↦ algebraMap K F x, .of_forall fun _ ↦ algebraMap_mem ..⟩
  algebraMap.map_one' := by ext; exact (algebraMap K F).map_one
  algebraMap.map_mul' _ _ := by ext; exact (algebraMap K F).map_mul ..
  algebraMap.map_add' _ _ := by ext; exact (algebraMap K F).map_add ..
  algebraMap.map_zero' := by ext; exact (algebraMap K F).map_zero
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := by ext; apply Algebra.smul_def

instance [BundledFunctionField K F] : IsScalarTower K F (Adele K F) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The $K$-subspace $\mathcal{A}_F(0)$, see [Stichtenoth, Definition 1.5.3]. -/
def integralAdele : Submodule K (Adele K F) where
  carrier := {x | ∀ v, x v ∈ v}
  add_mem' h₁ h₂ v := add_mem (h₁ v) (h₂ v)
  zero_mem' _ := zero_mem _
  smul_mem' _ _ h v := v.smul_mem (h v) _

/-- The genus of a function field, [Stichtenoth, Corollary 1.5.5]. -/
noncomputable def genus [BundledFunctionField K F] : ℕ := Module.finrank K
  (Adele K F ⧸ integralAdele K F ⊔ (IsScalarTower.toAlgHom K F _).toLinearMap.range)

end LeanEval.AlgebraicGeometry.Faltings

/-! ### Residue fields, adeles and the genus -/

namespace Faltings.LeanEval

open _root_.LeanEval.AlgebraicGeometry.Faltings (BundledFunctionField integralAdele)

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The valuation ring of a place of the problem is the valuation ring of the corresponding
place. -/
def valuationRingEquiv (v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F) :
    v ≃+* (placeEquiv v).toValuationSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Corresponding places have `K`-isomorphic residue fields. -/
noncomputable def residueFieldLinearEquiv
    (v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F) :
    IsLocalRing.ResidueField v ≃ₗ[K] (placeEquiv v).ResidueField where
  __ := IsLocalRing.ResidueField.mapEquiv (valuationRingEquiv v)
  map_smul' c a := by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact map_mul (IsLocalRing.ResidueField.mapEquiv (valuationRingEquiv v)) _ _

/-- A place of the problem has residue field of rank one over `K` exactly when the corresponding
place has degree one. -/
theorem rank_residueField_eq_one_iff (v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F) :
    Module.rank K (IsLocalRing.ResidueField v) = 1 ↔ (placeEquiv v).IsDegreeOne := by
  rw [Faltings.Place.IsDegreeOne, (residueFieldLinearEquiv v).rank_eq]

variable (K F) in
/-- The adele ring of the problem is `K`-isomorphic to the adele ring of the library, by
reindexing along `placeEquiv`: `(Φ a)_w = a_{placeEquiv⁻¹ w}`. -/
noncomputable def adeleLinearEquiv :
    _root_.LeanEval.AlgebraicGeometry.Faltings.Adele K F ≃ₗ[K] Faltings.Adele K F where
  toFun a := ⟨fun w ↦ a (placeEquiv.symm w),
    placeEquiv.symm.injective.tendsto_cofinite.eventually a.2⟩
  invFun α := ⟨fun v ↦ α (placeEquiv v), placeEquiv.injective.tendsto_cofinite.eventually α.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem adeleLinearEquiv_apply (a : _root_.LeanEval.AlgebraicGeometry.Faltings.Adele K F)
    (w : Faltings.Place K F) : adeleLinearEquiv K F a w = a (placeEquiv.symm w) :=
  rfl

@[simp]
theorem adeleLinearEquiv_symm_apply (α : Faltings.Adele K F)
    (v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F) :
    (adeleLinearEquiv K F).symm α v = α (placeEquiv v) :=
  rfl

variable (K F) in
/-- The reindexing carries the integral adeles of the problem onto `Faltings.Adele.integral`. -/
theorem map_integralAdele :
    (integralAdele K F).map (adeleLinearEquiv K F : _ →ₗ[K] Faltings.Adele K F) =
      Faltings.Adele.integral K F := by
  ext α
  refine ⟨?_, fun hα ↦ ⟨(adeleLinearEquiv K F).symm α, fun v ↦ hα (placeEquiv v),
    (adeleLinearEquiv K F).apply_symm_apply α⟩⟩
  rintro ⟨a, ha, rfl⟩ w
  exact ha (placeEquiv.symm w)

variable (K F) in
/-- The reindexing carries the image of the diagonal `F → 𝒜_F` of the problem onto
`Faltings.Adele.principal`. -/
theorem map_range_toAlgHom [BundledFunctionField K F] :
    (LinearMap.range (IsScalarTower.toAlgHom K F
        (_root_.LeanEval.AlgebraicGeometry.Faltings.Adele K F)).toLinearMap).map
      (adeleLinearEquiv K F : _ →ₗ[K] Faltings.Adele K F) = Faltings.Adele.principal K F := by
  obtain ⟨ι, hι, hrange⟩ := Faltings.Adele.exists_algHom_range_eq_principal K F
  have hcomp : (adeleLinearEquiv K F : _ →ₗ[K] Faltings.Adele K F) ∘ₗ
      (IsScalarTower.toAlgHom K F
        (_root_.LeanEval.AlgebraicGeometry.Faltings.Adele K F)).toLinearMap =
      ι.toLinearMap :=
    LinearMap.ext fun x ↦ RestrictedProduct.ext _ _ fun w ↦ (hι x w).symm
  rw [← LinearMap.range_comp, hcomp, ← hrange]
  ext α
  simp

variable (K F) in
/-- The genus of the problem is the genus of the library. -/
theorem genus_eq [BundledFunctionField K F] :
    _root_.LeanEval.AlgebraicGeometry.Faltings.genus K F = Faltings.genus K F :=
  (Submodule.Quotient.equiv _ _ (adeleLinearEquiv K F) (by
    rw [Submodule.map_sup, map_integralAdele, map_range_toAlgHom])).finrank_eq

/-- If the places of degree one of `F/K` are finitely many, so are the places of the problem with
residue field of rank one over `K`. -/
theorem finite_setOf_rank_residueField_eq_one
    (h : {w : Faltings.Place K F | w.IsDegreeOne}.Finite) :
    {v : _root_.LeanEval.AlgebraicGeometry.Faltings.Place K F |
      Module.rank K (IsLocalRing.ResidueField v) = 1}.Finite := by
  refine (h.preimage placeEquiv.injective.injOn).subset fun v hv ↦ ?_
  exact (rank_residueField_eq_one_iff v).mp hv

end Faltings.LeanEval

namespace LeanEval.AlgebraicGeometry.Faltings

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Every function field of genus at least 2 (equivalently, every curve of geometric genus
at least 2) over a number field has only finitely many rational points.
Note: if K is not the full constant field of F/K then there are no rational points, because
every place contains the full constant field. -/
theorem faltings [NumberField K] [BundledFunctionField K F] (h : 2 ≤ genus K F) :
    {v : Place K F | Module.rank K (IsLocalRing.ResidueField v) = 1}.Finite :=
  _root_.Faltings.LeanEval.finite_setOf_rank_residueField_eq_one
    (_root_.Faltings.finite_setOf_place_isDegreeOne
      (_root_.Faltings.LeanEval.genus_eq K F ▸ h))

end LeanEval.AlgebraicGeometry.Faltings

end
