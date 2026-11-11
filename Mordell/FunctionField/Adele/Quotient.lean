module

public import Mordell.FunctionField.Adele.Basic
public import Mordell.FunctionField.Adele.Embedding

/-!
# Adeles modulo integral and principal adeles

Let `F/K` be an algebraic function field of one variable, with places `ℙ_F`, adele ring `𝒜_F`,
integral adeles `𝒜_F(0)` and principal adeles `P_F`. Every `x ∈ F` lies in `𝒪_v` for all but
finitely many places `v`, so `x ↦ (x mod 𝒪_v)_v` is a `K`-linear map
`δ : F → ⨁_{v ∈ ℙ_F} F/𝒪_v`. The map `ρ : 𝒜_F → ⨁_v F/𝒪_v`, `α ↦ (α_v mod 𝒪_v)_v`, is
surjective with kernel `𝒜_F(0)` and carries `P_F` onto `δ(F)`; hence it induces a `K`-linear
isomorphism `𝒜_F / (𝒜_F(0) + P_F) ≃ (⨁_v F/𝒪_v) / δ(F)`.

## Main results

* `Faltings.Adele.exists_linearEquiv_quotient_integral_sup_principal`: there is a `K`-linear map
  `δ : F →ₗ[K] ⨁ v, F ⧸ 𝒪_v` with `δ x v = x mod 𝒪_v`, and a `K`-linear equivalence
  `𝒜_F ⧸ (Adele.integral K F ⊔ Adele.principal K F) ≃ₗ[K] (⨁ v, F ⧸ 𝒪_v) ⧸ range δ` sending the
  class of an adele `α` to the class of `(α_v mod 𝒪_v)_v`.

## Implementation notes

The sum `𝒜_F(0) + P_F` is the supremum `Adele.integral K F ⊔ Adele.principal K F` of
`K`-submodules, and `𝒪_v` enters the quotient `F/𝒪_v` as the `K`-submodule
`Subalgebra.toSubmodule v.toSubalgebra`. The isomorphism is pinned by its value on classes:
`e [α] = [y]` for every finitely supported `y` with `y_v = α_v mod 𝒪_v` for all `v`.

## References

* [J.-P. Serre, *Groupes algébriques et corps de classes*][serre1959], Ch. II, no. 5
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Section 1.5
-/

public section

namespace Faltings

section Quotient

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- A surjective linear map `ρ : M → N` induces `M ⧸ (ker ρ ⊔ range f) ≃ N ⧸ range (ρ ∘ f)`,
sending the class of `m` to the class of `ρ m`. -/
private noncomputable def quotSupRangeEquiv (ρ : M →ₗ[R] N) (hρ : Function.Surjective ρ)
    (f : P →ₗ[R] M) :
    (M ⧸ (LinearMap.ker ρ ⊔ LinearMap.range f)) ≃ₗ[R] N ⧸ LinearMap.range (ρ ∘ₗ f) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp, Submodule.comap_map_eq,
        sup_comm])).trans
    (((LinearMap.range (ρ ∘ₗ f)).mkQ ∘ₗ ρ).quotKerEquivOfSurjective
      ((Submodule.mkQ_surjective _).comp hρ))

private theorem quotSupRangeEquiv_mk (ρ : M →ₗ[R] N) (hρ : Function.Surjective ρ)
    (f : P →ₗ[R] M) (m : M) :
    quotSupRangeEquiv ρ hρ f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ m) :=
  rfl

end Quotient

namespace Adele

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The family `(α_v mod 𝒪_v)_v` of an adele `α`, as an element of the direct sum. -/
private noncomputable def reductionFun (α : Adele K F) :
    DirectSum (Place K F) (fun v ↦ F ⧸ Subalgebra.toSubmodule v.toSubalgebra) := by
  classical
  exact DFinsupp.mk (Filter.eventually_cofinite.mp α.2).toFinset
    (fun v ↦ Submodule.Quotient.mk (α v.1))

private theorem reductionFun_apply (α : Adele K F) (v : Place K F) :
    reductionFun K F α v = Submodule.Quotient.mk (α v) := by
  classical
  rw [reductionFun, DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
    exact ((Submodule.Quotient.mk_eq_zero _).mpr h).symm

/-- The map `ρ : 𝒜_F → ⨁_v F/𝒪_v`, `α ↦ (α_v mod 𝒪_v)_v`. -/
private noncomputable def reduction :
    Adele K F →ₗ[K] DirectSum (Place K F) (fun v ↦ F ⧸ Subalgebra.toSubmodule v.toSubalgebra) where
  toFun := reductionFun K F
  map_add' α β := by
    ext v
    simp only [DirectSum.add_apply, reductionFun_apply]
    rfl
  map_smul' c α := by
    ext v
    simp only [DirectSum.smul_apply, reductionFun_apply, RingHom.id_apply]
    rfl

private theorem reduction_apply (α : Adele K F) (v : Place K F) :
    reduction K F α v = Submodule.Quotient.mk (α v) :=
  reductionFun_apply K F α v

private theorem reduction_surjective : Function.Surjective (reduction K F) := by
  classical
  intro y
  have hout (v : Place K F) : Submodule.Quotient.mk (y v).out = y v := Quotient.out_eq' _
  refine ⟨⟨fun v ↦ (y v).out, ?_⟩, DFinsupp.ext fun v ↦ (reduction_apply K F _ v).trans (hout v)⟩
  refine Filter.eventually_cofinite.mpr ((DFinsupp.support y).finite_toSet.subset fun v hv ↦ ?_)
  refine DFinsupp.mem_support_iff.mpr fun h ↦ hv ?_
  exact (Submodule.Quotient.mk_eq_zero _).mp ((hout v).trans h)

private theorem ker_reduction : LinearMap.ker (reduction K F) = Adele.integral K F := by
  ext α
  simp only [LinearMap.mem_ker, Adele.mem_integral, DirectSum.ext_iff, reduction_apply,
    DirectSum.zero_apply, Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule]

end Adele

/-- For a function field `F/K` there is a `K`-linear map `δ : F →ₗ[K] ⨁ v, F ⧸ 𝒪_v` with
`δ x v = x mod 𝒪_v`, and the map `α ↦ (α_v mod 𝒪_v)_v` induces a `K`-linear equivalence
`Adele K F ⧸ (Adele.integral K F ⊔ Adele.principal K F) ≃ₗ[K] (⨁ v, F ⧸ 𝒪_v) ⧸ range δ`. -/
@[faltings "lem_ff_adele_mod_integral"]
theorem Adele.exists_linearEquiv_quotient_integral_sup_principal (K F : Type*) [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] :
    ∃ δ : F →ₗ[K] DirectSum (Place K F) (fun v ↦ F ⧸ Subalgebra.toSubmodule v.toSubalgebra),
      (∀ (x : F) (v : Place K F), δ x v = Submodule.Quotient.mk x) ∧
      ∃ e : (Adele K F ⧸ (Adele.integral K F ⊔ Adele.principal K F)) ≃ₗ[K]
          (DirectSum (Place K F) (fun v ↦ F ⧸ Subalgebra.toSubmodule v.toSubalgebra) ⧸
            LinearMap.range δ),
        ∀ (α : Adele K F)
          (y : DirectSum (Place K F) (fun v ↦ F ⧸ Subalgebra.toSubmodule v.toSubalgebra)),
          (∀ v, y v = Submodule.Quotient.mk (α v)) →
            e (Submodule.Quotient.mk α) = Submodule.Quotient.mk y := by
  obtain ⟨ι, hι, hrange⟩ := Adele.exists_algHom_range_eq_principal K F
  refine ⟨Adele.reduction K F ∘ₗ ι.toLinearMap, fun x v ↦ by simp [Adele.reduction_apply, hι], ?_⟩
  have hP : LinearMap.range ι.toLinearMap = Adele.principal K F := by rw [← hrange]; rfl
  refine ⟨(Submodule.quotEquivOfEq _ _ (by rw [Adele.ker_reduction, hP])).trans
    (quotSupRangeEquiv _ (Adele.reduction_surjective K F) ι.toLinearMap), fun α y hy ↦ ?_⟩
  obtain rfl : y = Adele.reduction K F α := DFinsupp.ext fun v ↦ by rw [hy v, Adele.reduction_apply]
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, quotSupRangeEquiv_mk]

end Faltings

end

