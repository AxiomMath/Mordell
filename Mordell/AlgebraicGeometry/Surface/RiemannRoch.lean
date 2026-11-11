module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import Mordell.AlgebraicGeometry.Surface.IntersectionEulerCharacteristic
public import Mordell.AlgebraicGeometry.Surface.SerreDuality

/-!
# Riemann–Roch on a smooth projective surface

Let `X` be a smooth projective geometrically integral surface over a field `k`, with structure
morphism `f : X ⟶ Spec k` and canonical sheaf `K_X = ⋀² Ω_{X/k}`, and let `𝓛` be an invertible
`𝒪_X`-module. Writing `χ` for the Euler characteristic and `(𝓜 · 𝓝)` for the intersection pairing
of invertible modules on `X`,
`χ(X, 𝓛) = χ(𝒪_X) + ½ (𝓛 · 𝓛) - ½ (𝓛 · K_X)`.

## Main results

* `Faltings.eulerCharacteristic_eq_of_smoothOfRelativeDimension_two`: the Riemann–Roch formula
  above, as an equality of rational numbers.

## Implementation notes

The Euler characteristic is `AlgebraicGeometry.eulerCharacteristic`, which needs coherence of the
module: an invertible module on the locally Noetherian scheme `X` is coherent
(`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible`). The pairing `(𝓜 · 𝓝)` is
`AlgebraicGeometry.intersectionNumber` with `Z = X` (the closed immersion `𝟙 X`), `d = 2` and the
family `![𝓜, 𝓝]`; its dimension bound is
`AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field`. The canonical
sheaf `K_X` is the exterior square of the sheaf of relative differentials, which is invertible
because `Ω_{X/k}` is finite locally free of rank `2`
(`Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials`,
`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`).

The proof: Serre duality gives `χ(K_X ⊗ 𝓛⁻¹) = χ(𝓛)` and `χ(K_X) = χ(𝒪_X)`. The expression of the
intersection number through Euler characteristics of inverse twists, applied to the pair
`(𝓛⁻¹, (K_X ⊗ 𝓛⁻¹)⁻¹)`, gives `2 χ(𝒪_X) - 2 χ(𝓛)`, and bilinearity of the pairing
(`AlgebraicGeometry.intersectionNumber_tensor`) identifies the left side with
`(𝓛 · K_X) - (𝓛 · 𝓛)`.

## References

* [Beauville, *Complex algebraic surfaces*, Theorem I.12]
* [Bombieri, *The Mordell conjecture revisited*, §1]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.SheafOfModules.Invertible

universe u

namespace Faltings

section Tensor

variable {X : Scheme.{u}}

/-- Two modules that are both inverse to `B` under the tensor product are isomorphic. -/
private noncomputable def isoOfTensorIsoUnit {A B C : X.Modules}
    (eA : Scheme.Modules.tensorObj A B ≅ SheafOfModules.unit X.ringCatSheaf)
    (eC : Scheme.Modules.tensorObj C B ≅ SheafOfModules.unit X.ringCatSheaf) : A ≅ C :=
  (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 A).symm ≪≫
    tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl A)
      (tensorProductBraiding X.presheaf X.ringCatSheaf.2 B C ≪≫ eC).symm ≪≫
    (tensorProductAssociator X.presheaf X.ringCatSheaf.2 A B C).symm ≪≫
    tensorProductIso X.presheaf X.ringCatSheaf.2 eA (Iso.refl C) ≪≫
    tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 C

/-- `𝓛⁻¹ ⊗ 𝓛 ≅ 𝒪_X`. -/
private noncomputable def tensorPowerNegOneTensorIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Scheme.Modules.tensorObj (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) L ≅
      SheafOfModules.unit X.ringCatSheaf :=
  tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L (-1) ≪≫
    tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (by norm_num : (-1 : ℤ) + 1 = 0)

/-- `𝓛 ⊗ 𝓛⁻¹ ≅ 𝒪_X`. -/
private noncomputable def tensorTensorPowerNegOneIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Scheme.Modules.tensorObj L (tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  tensorProductBraiding X.presheaf X.ringCatSheaf.2 _ _ ≪≫ tensorPowerNegOneTensorIso L

/-- `(𝓛⁻¹)⁻¹ ≅ 𝓛`. -/
private noncomputable def tensorPowerNegOneNegOneIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    tensorPower X.presheaf X.ringCatSheaf.2 (tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
      (-1) ≅ L :=
  isoOfTensorIsoUnit (tensorPowerNegOneTensorIso _) (tensorTensorPowerNegOneIso L)

/-- The tensor product of two invertible modules is invertible. -/
private theorem isInvertible_tensorObj (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Scheme.Modules.tensorObj A B) := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property A :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property B :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.property
    A B).toAlgebraicGeometry

end Tensor

section EulerCharacteristic

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- On a proper scheme over `k` whose cohomology of `F` vanishes from degree `3` on, the Euler
characteristic of `F` is `h⁰ - h¹ + h²`. -/
private theorem eulerCharacteristic_eq_of_finrank_eq_zero [IsProper f] (F : X.Modules)
    [F.IsCoherent] (h : ∀ n, 3 ≤ n → Module.finrank k (cohomologyOverField k f F n) = 0) :
    eulerCharacteristic k f F =
      (Module.finrank k (cohomologyOverField k f F 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f F 1) +
        Module.finrank k (cohomologyOverField k f F 2) := by
  rw [eulerCharacteristic_eq_finsum, finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp [Finset.sum_range_succ]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hn'
    exact hn (by rw [h n (by omega)]; simp)

/-- **Serre duality, summed.** On a smooth projective geometrically integral surface,
`χ(K_X ⊗ 𝓛⁻¹) = χ(𝓛)` for every invertible module `𝓛`. -/
private theorem eulerCharacteristic_canonical_twist [IsProjectiveVariety k f]
    [GeometricallyIntegral f] [SmoothOfRelativeDimension 2 f] [IsProper f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [L.IsCoherent]
    [(twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
      (fun _ : Fin 1 => L) (fun _ => -1)).IsCoherent] :
    eulerCharacteristic k f (twistedSheaf (Scheme.Modules.exteriorPower f.relativeDifferentials 2)
      (fun _ : Fin 1 => L) (fun _ => -1)) = eulerCharacteristic k f L := by
  have S := Faltings.finrank_cohomologyOverField_eq_finrank_cohomologyOverField_canonical_twist
    k f L
  have S' : ∀ i : ℕ, i ≤ 2 → Module.finrank k (cohomologyOverField k f L i) =
      Module.finrank k (cohomologyOverField k f (twistedSheaf
        (Scheme.Modules.exteriorPower f.relativeDifferentials 2) (fun _ : Fin 1 => L)
        (fun _ => -1)) (2 - i)) := by
    intro i hi
    have h := S i
    rw [if_pos (by omega), if_pos (by omega), Int.toNat_natCast,
      show (2 - (i : ℤ)).toNat = 2 - i by omega] at h
    exact h
  rw [eulerCharacteristic_eq_of_finrank_eq_zero k f L,
    eulerCharacteristic_eq_of_finrank_eq_zero k f]
  · rw [S' 0 (by norm_num), S' 1 (by norm_num), S' 2 (by norm_num)]
    norm_num
    ring
  · intro n hn
    have h := S (2 - n)
    rw [if_neg (by omega), if_pos (by omega), show (2 - (2 - (n : ℤ))).toNat = n by omega] at h
    exact h.symm
  · intro n hn
    have h := S n
    rw [if_pos (by omega), if_neg (by omega), Int.toNat_natCast] at h
    exact h

end EulerCharacteristic

section Intersection

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hX : topologicalKrullDim X = 2)

/-- The intersection number `(𝓜 · 𝓝)` of two invertible modules on a proper surface. -/
private noncomputable abbrev pairing (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] : ℤ :=
  @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![M, N]
    (Fin.forall_fin_two.2 ⟨hM, hN⟩)

/-- Additivity of `(𝓜 · 𝓝)` in `𝓜`. -/
private theorem pairing_add_left (M M' M'' N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hM' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M']
    [hM'' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M'']
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (e : M ≅ Scheme.Modules.tensorObj M' M'') :
    pairing k f hX M N = pairing k f hX M' N + pairing k f hX M'' N := by
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M, N] q) :=
    Fin.forall_fin_two.2 ⟨hM, hN⟩
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M', N] q) :=
    Fin.forall_fin_two.2 ⟨hM', hN⟩
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M'', N] q) :=
    Fin.forall_fin_two.2 ⟨hM'', hN⟩
  exact intersectionNumber_tensor k f (𝟙 X) 2 (by simp [hX]) 0 ![M, N] ![M', N] ![M'', N]
    (Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => rfl⟩)
    (Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => rfl⟩) e

/-- Additivity of `(𝓜 · 𝓝)` in `𝓝`. -/
private theorem pairing_add_right (M N N' N'' : X.Modules)
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [hN' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N']
    [hN'' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N'']
    (e : N ≅ Scheme.Modules.tensorObj N' N'') :
    pairing k f hX M N = pairing k f hX M N' + pairing k f hX M N'' := by
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M, N] q) :=
    Fin.forall_fin_two.2 ⟨hM, hN⟩
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M, N'] q) :=
    Fin.forall_fin_two.2 ⟨hM, hN'⟩
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![M, N''] q) :=
    Fin.forall_fin_two.2 ⟨hM, hN''⟩
  exact intersectionNumber_tensor k f (𝟙 X) 2 (by simp [hX]) 1 ![M, N] ![M, N'] ![M, N'']
    (Fin.forall_fin_two.2 ⟨fun _ => rfl, fun h => absurd rfl h⟩)
    (Fin.forall_fin_two.2 ⟨fun _ => rfl, fun h => absurd rfl h⟩) e

/-- `(𝓜⁻¹ · 𝓝) = -(𝓜 · 𝓝)`. -/
private theorem pairing_tensorPower_neg_one_left (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    pairing k f hX (tensorPower X.presheaf X.ringCatSheaf.2 M (-1)) N =
      -pairing k f hX M N := by
  haveI := SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  have h0 : pairing k f hX (SheafOfModules.unit X.ringCatSheaf) N =
      pairing k f hX (SheafOfModules.unit X.ringCatSheaf) N +
        pairing k f hX (SheafOfModules.unit X.ringCatSheaf) N :=
    pairing_add_left k f hX _ _ _ N
      (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _).symm
  have h1 : pairing k f hX (SheafOfModules.unit X.ringCatSheaf) N =
      pairing k f hX (tensorPower X.presheaf X.ringCatSheaf.2 M (-1)) N +
        pairing k f hX M N :=
    pairing_add_left k f hX _ _ _ N (tensorPowerNegOneTensorIso M).symm
  omega

/-- `(𝓜 · 𝓝⁻¹) = -(𝓜 · 𝓝)`. -/
private theorem pairing_tensorPower_neg_one_right (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    pairing k f hX M (tensorPower X.presheaf X.ringCatSheaf.2 N (-1)) =
      -pairing k f hX M N := by
  haveI := SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  have h0 : pairing k f hX M (SheafOfModules.unit X.ringCatSheaf) =
      pairing k f hX M (SheafOfModules.unit X.ringCatSheaf) +
        pairing k f hX M (SheafOfModules.unit X.ringCatSheaf) :=
    pairing_add_right k f hX M _ _ _
      (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _).symm
  have h1 : pairing k f hX M (SheafOfModules.unit X.ringCatSheaf) =
      pairing k f hX M (tensorPower X.presheaf X.ringCatSheaf.2 N (-1)) +
        pairing k f hX M N :=
    pairing_add_right k f hX M _ _ _ (tensorPowerNegOneTensorIso N).symm
  omega

end Intersection

/-- **Riemann–Roch, doubled, in `ℤ`.** `2 χ(𝓛) = 2 χ(𝒪_X) + (𝓛 · 𝓛) - (𝓛 · K_X)`. The intersection
number of `𝓛⁻¹` and `(K_X ⊗ 𝓛⁻¹)⁻¹`, expressed through Euler characteristics, is
`2 χ(𝒪_X) - 2 χ(𝓛)` by Serre duality, and `(𝓛 · K_X) - (𝓛 · 𝓛)` by bilinearity. -/
private theorem eulerCharacteristic_mul_two (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [GeometricallyIntegral f]
    [SmoothOfRelativeDimension 2 f] (hX : topologicalKrullDim X = 2)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] [L.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower f.relativeDifferentials 2)] :
    eulerCharacteristic k f L * 2 =
      eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) * 2 + pairing k f hX L L -
        pairing k f hX L (Scheme.Modules.exteriorPower f.relativeDifferentials 2) := by
  haveI hO := SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  set K := Scheme.Modules.exteriorPower f.relativeDifferentials 2
  set O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set Li := tensorPower X.presheaf X.ringCatSheaf.2 L (-1)
  haveI hLi : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Li :=
    Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules L (-1)
  set T := Scheme.Modules.tensorObj K Li
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 T := isInvertible_tensorObj K Li
  set Ti := tensorPower X.presheaf X.ringCatSheaf.2 T (-1)
  haveI hTi : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Ti :=
    Scheme.Modules.algebraicGeometryIsInvertible_tensorPowerModules T (-1)
  have i1 : pairing k f hX Li Ti = -pairing k f hX L Ti :=
    pairing_tensorPower_neg_one_left k f hX L Ti
  have i2 : pairing k f hX L Ti = -pairing k f hX L T :=
    pairing_tensorPower_neg_one_right k f hX L T
  have i3 : pairing k f hX L T = pairing k f hX L K + pairing k f hX L Li :=
    pairing_add_right k f hX L T K Li (Iso.refl _)
  have i4 : pairing k f hX L Li = -pairing k f hX L L :=
    pairing_tensorPower_neg_one_right k f hX L L
  haveI : ∀ M : X.Modules, [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] →
      M.IsCoherent := fun M _ => SheafOfModules.isCoherent_of_isInvertible k f M
  haveI : (Scheme.Modules.tensorObj (tensorPower X.presheaf X.ringCatSheaf.2 Li (-1))
      (tensorPower X.presheaf X.ringCatSheaf.2 Ti (-1))).IsCoherent :=
    @SheafOfModules.isCoherent_of_isInvertible X k _ f _ _
      (@isInvertible_tensorObj X _ _
        (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ Li (-1))
        (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ Ti (-1)))
  haveI : (twistedSheaf K (fun _ : Fin 1 => O) (fun _ => -1)).IsCoherent :=
    @SheafOfModules.isCoherent_of_isInvertible X k _ f _ _ (isInvertible_tensorObj _ _)
  haveI := @SheafOfModules.isCoherent_of_isInvertible X k _ f _ _
    (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ Li (-1))
  have c1 : eulerCharacteristic k f (tensorPower X.presheaf X.ringCatSheaf.2 Li (-1)) =
      eulerCharacteristic k f L :=
    eulerCharacteristic_eq_of_iso k f (tensorPowerNegOneNegOneIso L)
  haveI := @SheafOfModules.isCoherent_of_isInvertible X k _ f _ _
    (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ Ti (-1))
  have c2 : eulerCharacteristic k f (tensorPower X.presheaf X.ringCatSheaf.2 Ti (-1)) =
      eulerCharacteristic k f T :=
    eulerCharacteristic_eq_of_iso k f (tensorPowerNegOneNegOneIso T)
  let e : Scheme.Modules.tensorObj L T ≅ K :=
    tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl L)
        (tensorProductBraiding X.presheaf X.ringCatSheaf.2 K Li) ≪≫
      (tensorProductAssociator X.presheaf X.ringCatSheaf.2 L Li K).symm ≪≫
      tensorProductIso X.presheaf X.ringCatSheaf.2 (tensorTensorPowerNegOneIso L) (Iso.refl K) ≪≫
      tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 K
  have c3 : eulerCharacteristic k f (Scheme.Modules.tensorObj
      (tensorPower X.presheaf X.ringCatSheaf.2 Li (-1))
      (tensorPower X.presheaf X.ringCatSheaf.2 Ti (-1))) = eulerCharacteristic k f K :=
    eulerCharacteristic_eq_of_iso k f
      (tensorProductIso X.presheaf X.ringCatSheaf.2 (tensorPowerNegOneNegOneIso L)
        (tensorPowerNegOneNegOneIso T) ≪≫ e)
  haveI : (twistedSheaf K (fun _ : Fin 1 => L) (fun _ => -1)).IsCoherent :=
    SheafOfModules.isCoherent_of_isInvertible k f T
  have c4 : eulerCharacteristic k f T = eulerCharacteristic k f L :=
    eulerCharacteristic_canonical_twist k f L
  let eO : twistedSheaf K (fun _ : Fin 1 => O) (fun _ => -1) ≅ K :=
    tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl K)
        (isoOfTensorIsoUnit (tensorPowerNegOneTensorIso O)
          (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 O)) ≪≫
      tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 K
  have c5 : eulerCharacteristic k f K = eulerCharacteristic k f O :=
    (eulerCharacteristic_eq_of_iso k f eO).symm.trans (eulerCharacteristic_canonical_twist k f O)
  have E' : pairing k f hX Li Ti = _ :=
    Faltings.intersectionNumber_two_eq_eulerCharacteristic_inv k f hX Li Ti
  rw [c1, c2, c3, c4, c5] at E'
  linarith

/-- **Riemann–Roch on a surface.** For a smooth projective geometrically integral surface
`f : X ⟶ Spec k` with canonical sheaf `K_X = ⋀² Ω_{X/k}` and an invertible `𝒪_X`-module `L`,
`χ(X, L) = χ(𝒪_X) + ½ (L · L) - ½ (L · K_X)`, where `(· · ·)` is the intersection number
`AlgebraicGeometry.intersectionNumber` on `X`. -/
@[faltings "thm_nt_riemann_roch_surface"]
theorem eulerCharacteristic_eq_of_smoothOfRelativeDimension_two
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 2 f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f 2
    haveI : L.IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
    haveI : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
    haveI hK : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Scheme.Modules.exteriorPower f.relativeDifferentials 2) :=
      (Scheme.Modules.isInvertible_exteriorPower_self
        f.relativeDifferentials 2).toAlgebraicGeometry
    let hd : topologicalKrullDim X ≤ (2 : ℕ) :=
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 f).le
    ((eulerCharacteristic k f L : ℤ) : ℚ) =
      (eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) : ℚ) +
        (1 / 2 : ℚ) * (@intersectionNumber k _ X X f _ (𝟙 X) _ 2 hd ![L, L]
          (Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩) : ℚ) -
        (1 / 2 : ℚ) * (@intersectionNumber k _ X X f _ (𝟙 X) _ 2 hd
          ![L, Scheme.Modules.exteriorPower f.relativeDifferentials 2]
          (Fin.forall_fin_two.2 ⟨‹_›, hK⟩) : ℚ) := by
  intro hd
  have hX : topologicalKrullDim X = 2 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f 2
  haveI := SheafOfModules.isCoherent_of_isInvertible k f L
  haveI := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X
    (SheafOfModules.unit X.ringCatSheaf)
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower f.relativeDifferentials 2) :=
    (Scheme.Modules.isInvertible_exteriorPower_self f.relativeDifferentials 2).toAlgebraicGeometry
  have key := congrArg (Int.cast : ℤ → ℚ) (eulerCharacteristic_mul_two k f hX L)
  push_cast at key
  show (eulerCharacteristic k f L : ℚ) =
    eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) +
      1 / 2 * (pairing k f hX L L : ℚ) -
      1 / 2 * (pairing k f hX L (Scheme.Modules.exteriorPower f.relativeDifferentials 2) : ℚ)
  linarith

end Faltings
