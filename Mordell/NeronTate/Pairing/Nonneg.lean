module

public import Mordell.NeronTate.Pairing.SelfHeight
public import Mordell.NeronTate.Nonneg
public import Mordell.Jacobian.Autoduality.Ample

/-!
# The Néron form is positive semidefinite

In the situation of `Faltings.neronPairing` — `k` a number field, `(C, P)` a curve over `k` with
a rational divisor of degree one, of genus `g ≥ 1`, `(J, ι)` a Jacobian, `θ = cl(Θ)` the class of
the theta divisor and `K` an algebraic closure of `k` — the Néron form satisfies
`⟨x, x⟩ ≥ 0` for every `x ∈ J(K)`.

The proof: `θ + θ⁻` is ample and even
(`Faltings.isEvenClass_thetaClass_add_inv_and_exists_isAmple`), so its Néron–Tate height is
non-negative (`Faltings.IsEvenClass.nonneg_of_isNeronTateHeight`), and
`⟨x, x⟩ = ĥ_θ (x) + ĥ_θ (-x) = ĥ_{θ + θ⁻} (x)` (`Faltings.neronPairing_self_eq_add_and_add_eq`).

## Main results

* `Faltings.neronPairing_self_nonneg`: `0 ≤ neronPairing … x x`.

## Implementation notes

Autoduality gives `θ + θ⁻` as the class of an invertible sheaf that is ample in the sense of
Stacks, Tag 01PS (`AlgebraicGeometry.Scheme.Modules.IsAmple`), while non-negativity is stated for
ample classes in the sense of `Faltings.IsAmpleClass`, through a very ample power. On a projective
variety over a field the first implies the second: by Stacks, Tag 01VS a positive power of an
ample sheaf is `𝒪(1)` pulled back along an immersion into `ℙⁿ_k` over `k`, and an immersion from
a proper `k`-scheme into the separated `ℙⁿ_k` is a closed immersion.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonObj TensorProduct

universe u

namespace Faltings

variable {k : Type u} [Field k]

/-- On a projective variety over a field, an ample invertible module in the sense of Stacks,
Tag 01PS, is ample in the sense of `Faltings.IsAmple`: some positive tensor power is `𝒪(1)`
pulled back along an immersion into `ℙⁿ_k` over `k` (Stacks, Tag 01VS), and that immersion is
closed because `X` is proper over `k`. -/
private theorem isAmple_of_isAmple {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Scheme.Modules.IsAmple X L) :
    Faltings.IsAmple f L := by
  obtain ⟨d, hd, h⟩ := Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform_iff.mp
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform X (Spec (.of k)) f L
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hL) inferInstance
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := h d le_rfl
  let g := pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse.{u} n))
  have : UniversallyClosed (i ≫ g) := by
    rw [hover]; infer_instance
  have : UniversallyClosed i := UniversallyClosed.of_comp_of_isSeparated i g
  exact ⟨d, by exact_mod_cast hd, n,
    ⟨i, IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range, hover⟩, ⟨e⟩⟩

/-- On a projective variety over a field, the class `[M] ⊗ 1` of an invertible module that is
ample in the sense of Stacks, Tag 01PS, is an ample class. -/
private theorem isAmpleClass_comm_one_tmul {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (hM : Scheme.Modules.IsAmple X M)
    {c : Stacks.Picard.ofScheme X}
    (hc : Stacks.SheafOfModules.picardClass X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) M
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M ‹_›) = c) :
    IsAmpleClass f (TensorProduct.comm ℤ ℚ _ ((1 : ℚ) ⊗ₜ c)) :=
  ⟨1, M, ‹_›, le_rfl, isAmple_of_isAmple f M hM, by
    rw [one_smul, TensorProduct.comm_tmul]
    exact congrArg (· ⊗ₜ[ℤ] (1 : ℚ)) hc.symm⟩

/-- A prime divisor is the unique radical ideal sheaf with its support. -/
private theorem idealSheaf_eq_of_support_eq {X : Scheme.{u}} (Z : Stacks.Divisors.PrimeDivisor X)
    {D : X.IdealSheafData} (hrad : D.radical = D) (h : Z.support = (D.support : Set X)) :
    Z.idealSheaf = D := by
  have := Z.integral
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (by ext1; exact h)

/-- **The Néron form is positive semidefinite.** In the situation of `Faltings.neronPairing`,
`⟨x, x⟩ ≥ 0` for every `x ∈ J(K)`. -/
@[faltings "lem_nt_neron_norm_nonneg"]
theorem neronPairing_self_nonneg [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) (hg : 1 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J)
    (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A hg j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (x : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)) :
    0 ≤ neronPairing X A hg j hj D hrad hsupp K x x := by
  have := A.isAbelianVariety
  let : IsCommMonObj A.J := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  let : IsProjectiveVariety k A.J.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.J.hom)
      (isProjective_of_isAbelianVariety k A.J)⟩
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Algebra ℚ K := DivisionRing.toRatAlgebra
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  obtain ⟨Z, hZ⟩ := exists_primeDivisor_support_eq_thetaDivisor X A hg j hj
  have hZD := idealSheaf_eq_of_support_eq Z hrad (hZ.trans hsupp.symm)
  have : Stacks.Divisors.IsEffectiveCartierDivisor Z.idealSheaf := hZD ▸ inferInstance
  obtain ⟨heven, M, hM, hMamp, hMcl⟩ :=
    isEvenClass_thetaClass_add_inv_and_exists_isAmple X A hg j hj Z hZ
  let θ := Stacks.Divisors.picardClass D
  let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
  have hθZ : Stacks.SheafOfModules.picardClass A.J.left.presheaf
      (Stacks.RingedSpace.structureIsSheaf A.J.left.toRingedSpace)
      (Stacks.Divisors.invertibleSheaf Z.idealSheaf)
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance) = θ :=
    Stacks.Divisors.picardClass_congr hZD
  rw [hθZ] at heven hMcl
  obtain ⟨f, hf⟩ := exists_isNeronTateHeight A.J K ((1 : ℚ) ⊗ₜ θ)
  obtain ⟨f', hf'⟩ := exists_isNeronTateHeight A.J K ((1 : ℚ) ⊗ₜ θm)
  obtain ⟨f'', hf''⟩ := exists_isNeronTateHeight A.J K ((1 : ℚ) ⊗ₜ (θ + θm))
  obtain ⟨h1, h2⟩ := neronPairing_self_eq_add_and_add_eq X A hg j hj D hrad hsupp K f f' f''
    hf hf' hf'' x
  rw [h1, h2]
  exact IsEvenClass.nonneg_of_isNeronTateHeight
    (isAmpleClass_comm_one_tmul _ M hMamp hMcl) heven K f'' hf'' _

end Faltings
