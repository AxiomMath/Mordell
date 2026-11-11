module

public import Mordell.MordellWeil.Kummer.Field
public import Mordell.AbelianVariety.GoodReduction
public import Mordell.MordellWeil.Kummer.PointDegree
public import Mordell.NumberField.HermiteMinkowski
public import Mordell.MordellWeil.Kummer.Unramified

/-!
# Finiteness of the Kummer field

Let `k` be a number field with algebraic closure `k̄`, `A` an abelian variety over `k` and
`m ≥ 1` with `A(k̄)[m] ⊆ A(k)`. Then the Kummer field `k(m⁻¹ A(k)) ⊆ k̄`, the compositum of the
fields of definition `k(Q)` of the points `Q ∈ A(k̄)` with `m Q ∈ A(k)`, is a finite extension
of `k`. The proof bounds each `[k(Q) : k]` by `m^{2g}`, shows `k(Q)/k` is unramified outside the
finite set of places dividing `m` or of bad reduction, and applies the Hermite–Minkowski theorem.

## Main results

* `Faltings.finiteDimensional_kummerField`: `Faltings.kummerField k k̄ A m` is
  finite-dimensional over `k`.

## Implementation notes

The finiteness of the extension is `FiniteDimensional k` of the `IntermediateField k k̄`.
The dimension `g` of `A` does not appear in the statement; it only enters the proof.

## References

* X. Wu, *Diophantine geometry*, weeks 9–10, Section 3
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VIII.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped MonObj

universe u

namespace Faltings

/-- An intermediate field contained in the compositum of a finite set of finite-dimensional
intermediate fields is finite-dimensional. -/
private lemma finiteDimensional_of_le_sSup {K L : Type*} [Field K] [Field L] [Algebra K L]
    {H : Set (IntermediateField K L)} (hH : H.Finite) (hfd : ∀ F ∈ H, FiniteDimensional K F)
    {E : IntermediateField K L} (hE : E ≤ sSup H) : FiniteDimensional K E := by
  have : Finite H := hH.to_subtype
  have : ∀ F : H, FiniteDimensional K F.1 := fun F => hfd F.1 F.2
  have := IntermediateField.finiteDimensional_iSup_of_finite (t := fun F : H => F.1)
  rw [sSup_eq_iSup'] at hE
  exact Module.Finite.of_injective (IntermediateField.inclusion hE).toLinearMap
    (IntermediateField.inclusion_injective hE)

/-- The field of definition `k(Q)` of a point `Q ∈ A(k̄)` with `m Q ∈ A(k)` is a finite
extension of `k` of degree at most `m ^ (2 g)`, unramified outside any finite set `S` of places
containing those dividing `m` and those of bad reduction. -/
private lemma fieldOfDefinition_mem_of_pow_mem
    (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (g : ℕ) (hdim : topologicalKrullDim A.left = g)
    (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hS : ∀ v ∉ S, (m : 𝓞 k) ∉ v.asIdeal ∧ HasGoodReduction k v A)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (hQ : ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    ∃ _ : FiniteDimensional k (fieldOfDefinition (k := k) Q.left (Over.w Q)),
      Module.finrank k (fieldOfDefinition (k := k) Q.left (Over.w Q)) ≤ m ^ (2 * g) ∧
        IsUnramifiedOutside k (fieldOfDefinition (k := k) Q.left (Over.w Q)) S :=
  ⟨(finiteDimensional_and_isGalois_fieldOfDefinition_of_pow_mem k kbar A m hm htors Q hQ).1,
    finrank_fieldOfDefinition_le_of_pow_mem k kbar A g hdim m hm htors Q hQ,
    fun v hv w _ => ramificationIdx_fieldOfDefinition_eq_one_of_pow_mem k kbar A m hm htors v
      (hS v hv).1 (hS v hv).2 Q hQ w.asIdeal⟩

/-- Let `A` be an abelian variety over a number field `k` and `m ≥ 1` with `A(k̄)[m] ⊆ A(k)`.
Then the Kummer field `k(m⁻¹ A(k)) = Faltings.kummerField k k̄ A m` is a finite extension
of `k`. -/
@[faltings "thm_mw_kummer_extension_finite"]
theorem finiteDimensional_kummerField
    (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T) :
    FiniteDimensional k (kummerField k kbar A m hm htors) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety k A.hom := .mk (toIsVariety := .mk)
  have : AlgebraicGeometry.IsAbelianVariety k A := ⟨⟩
  -- `S`: the places dividing `m` or of bad reduction
  have hSfin :=
    (finite_setOf_mem_asIdeal (Nat.cast_ne_zero.mpr (by omega) : (m : 𝓞 k) ≠ 0)).union
      (finite_setOf_not_hasGoodReduction k A)
  -- every `k(Q)` lies in the finite set of Hermite–Minkowski
  refine finiteDimensional_of_le_sSup (finite_setOf_finrank_le_isUnramifiedOutside k kbar
    hSfin.toFinset (m ^ (2 * Stacks.Groupoids.abelianVarietyDimension A))
    (Nat.one_le_pow _ _ (by omega))) (fun _ hL => hL.1)
    (iSup₂_le fun Q hQ => le_sSup ?_)
  exact fieldOfDefinition_mem_of_pow_mem k kbar A _
    (Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension A) m hm htors _
    (fun v hv => by simpa [not_or] using hv) Q hQ

end Faltings
