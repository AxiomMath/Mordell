module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.SurfaceEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwiner

/-!
# The intersection number on a surface through inverse twists

Let `X` be a proper scheme of dimension `2` over a field `k` and let `𝓛, 𝓜` be invertible
`𝒪_X`-modules. The intersection number `(𝓛 · 𝓜)` is the coefficient of `n₁ n₂` in the numerical
polynomial `p(n₁, n₂) = χ(X, 𝓛^{⊗ n₁} ⊗ 𝓜^{⊗ n₂})` of total degree `≤ 2`. Evaluating the mixed
second difference of `p` at `(0, 0), (-1, 0), (0, -1), (-1, -1)` instead of at `{0, 1}²` gives

`(𝓛 · 𝓜) = χ(𝒪_X) - χ(𝓛⁻¹) - χ(𝓜⁻¹) + χ(𝓛⁻¹ ⊗ 𝓜⁻¹)`.

## Main results

* `Faltings.intersectionNumber_two_eq_eulerCharacteristic_inv`: the formula above.

## Implementation notes

The intersection number is `AlgebraicGeometry.intersectionNumber` with `Z = X` (the identity
closed immersion), `d = 2` and the family `![𝓛, 𝓜]`. The inverse `𝓛⁻¹` is the integral tensor
power `Stacks.SheafOfModules.Invertible.tensorPower _ _ 𝓛 (-1)`, the same tensor powers through
which the numerical polynomial is defined, and `⊗` is `AlgebraicGeometry.Scheme.Modules.tensorObj`.
The dimension hypothesis is `topologicalKrullDim X = 2`, as in the source.

## References

* [Stacks, Tag 0BEP, 0BEM]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.SheafOfModules.Invertible

universe u

namespace Faltings

/-- For a rational polynomial in two variables of total degree at most two, the mixed difference
at `(0,0), (-1,0), (0,-1), (-1,-1)` is the coefficient of `n₁ n₂`. -/
private theorem eval_mixed_sub_eq_coeff (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ 2) :
    MvPolynomial.eval (fun j => ((![0, 0] j : ℤ) : ℚ)) P -
        MvPolynomial.eval (fun j => ((![-1, 0] j : ℤ) : ℚ)) P -
        MvPolynomial.eval (fun j => ((![0, -1] j : ℤ) : ℚ)) P +
        MvPolynomial.eval (fun j => ((![-1, -1] j : ℤ) : ℚ)) P =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  simp only [MvPolynomial.eval_eq', Fin.prod_univ_two, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun _ => 1)]
  · simp
  · intro d hd hne
    have hle := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hle
    obtain h0 | h0 := Nat.eq_zero_or_pos (d 0)
    · simp [h0]
    obtain h1 | h1 := Nat.eq_zero_or_pos (d 1)
    · simp [h1]
    exact absurd (Finsupp.ext (Fin.forall_fin_two.2 ⟨by simp; omega, by simp; omega⟩)) hne
  · intro h
    simp [MvPolynomial.notMem_support_iff.mp h]

/-- Integer tensor powers depend only on the isomorphism class of the invertible module. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{u}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- **Stacks 0BEM on a surface, with the twists computed up to isomorphism.** On a scheme `X` of
dimension `2` proper over `k`, the Euler characteristics of the twists
`𝒪_X ⊗ 𝓛₀^{⊗ n₀} ⊗ 𝓛₁^{⊗ n₁}` are the values of a rational polynomial of total degree `≤ 2`, in
the form `AlgebraicGeometry.intersectionNumber_eq_coeff` consumes; and its value at `n` is
`χ(X, 𝒢)` for every coherent `𝒢` isomorphic to that twist. -/
private theorem exists_eulerPolynomial_of_dim_two (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : topologicalKrullDim X = 2) (F : Fin 2 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F j)] :
    ∃ P : MvPolynomial (Fin 2) ℚ, P.totalDegree ≤ 2 ∧
      (∀ n : Fin 2 → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        ((@eulerCharacteristic k _ X (𝟙 X ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
            (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (F j)) n)
          (isCoherent_twistedSheafUnitPullback k f (𝟙 X) F n) : ℤ) : ℚ)) ∧
      ∀ (n : Fin 2 → ℤ) (G : X.Modules) [G.IsCoherent],
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (F j)) n ≅ G) →
        MvPolynomial.eval (fun j => (n j : ℚ)) P = (eulerCharacteristic k f G : ℚ) := by
  obtain ⟨P, hPdeg, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (𝟙 X ≫ f)
    (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (F j)) (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (𝟙 X ≫ f))
  refine ⟨P, ?_, hP, fun n G _ e => ?_⟩
  · rcases hPdeg with rfl | h
    · simp
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le X _).trans hX.le)
  · rw [hP n, @eulerCharacteristic_eq_of_iso k _ X (𝟙 X ≫ f) _ _ G
      (isCoherent_twistedSheafUnitPullback k f (𝟙 X) F n) _ e]
    simp only [Category.id_comp]

/-- On a proper surface `X` over a field `k`, the intersection number of invertible modules
`L, M` is `(L · M) = χ(𝒪_X) - χ(L⁻¹) - χ(M⁻¹) + χ(L⁻¹ ⊗ M⁻¹)`, with `L⁻¹` the tensor power
`tensorPower _ _ L (-1)`. -/
@[faltings "lem_nt_intersection_euler_formula"]
theorem intersectionNumber_two_eq_eulerCharacteristic_inv (k : Type*) [Field k] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hX : topologicalKrullDim X = 2)
    (L M : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M] :
    @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![L, M]
        (Fin.forall_fin_two.2 ⟨hL, hM⟩) =
      @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf)
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f) -
        @eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.property L (-1))
          (SheafOfModules.isCoherent_of_isInvertible k f _) -
        @eulerCharacteristic k _ X f _ (tensorPower X.presheaf X.ringCatSheaf.property M (-1))
          (SheafOfModules.isCoherent_of_isInvertible k f _) +
        @eulerCharacteristic k _ X f _
          (Scheme.Modules.tensorObj (tensorPower X.presheaf X.ringCatSheaf.property L (-1))
            (tensorPower X.presheaf X.ringCatSheaf.property M (-1)))
          (@SheafOfModules.isCoherent_of_isInvertible X k _ f _ _
            (Stacks.SectionProduct.isInvertibleModule_tensorObj _ _)) := by
  haveI : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![L, M] j) :=
    Fin.forall_fin_two.2 ⟨hL, hM⟩
  obtain ⟨P, hdeg, hP, hval⟩ := exists_eulerPolynomial_of_dim_two k f hX ![L, M]
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  haveI := SheafOfModules.isCoherent_of_isInvertible k f
    (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
  haveI := SheafOfModules.isCoherent_of_isInvertible k f
    (tensorPower X.presheaf X.ringCatSheaf.2 M (-1))
  haveI := @SheafOfModules.isCoherent_of_isInvertible X k _ f _ _
    (Stacks.SectionProduct.isInvertibleModule_tensorObj
      (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
      (tensorPower X.presheaf X.ringCatSheaf.2 M (-1)))
  let eL := tensorPowerIsoOfIso _ L ((Scheme.Modules.pullbackId X).app L) (-1)
  let eM := tensorPowerIsoOfIso _ M ((Scheme.Modules.pullbackId X).app M) (-1)
  apply Int.cast_injective (α := ℚ)
  rw [intersectionNumber_eq_coeff k f (𝟙 X) 2 _ _ P hP hdeg, ← eval_mixed_sub_eq_coeff P hdeg,
    hval ![0, 0] (SheafOfModules.unit X.ringCatSheaf)
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _),
    hval ![-1, 0] (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (-1 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ eL),
    hval ![0, -1] (tensorPower X.presheaf X.ringCatSheaf.2 M (-1))
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (-1 : ℤ))) ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _) (Iso.refl _) ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ eM),
    hval ![-1, -1] (Scheme.Modules.tensorObj (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
        (tensorPower X.presheaf X.ringCatSheaf.2 M (-1)))
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (-1 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (-1 : ℤ))) ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ eL) eM)]
  push_cast
  ring

end Faltings
