module

public import Mordell.AbelianVariety.EvenOddClass
public import Mordell.NeronTate.Basic
public import Mordell.NeronTate.Existence
public import Mordell.Height.Class.Basic
public import Mordell.AlgebraicGeometry.Ample
public import Mordell.Height.Machine.Northcott
public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.Height.Machine.IsomorphicPullbacks
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import Mordell.NeronTate.Nonneg
public import Mordell.Height.Class.Northcott
public import Mordell.Height.Class.Uniqueness
public import Mordell.Height.Machine.ClassZero
import Mordell.NeronTate.Uniqueness

/-!
# Northcott's theorem for the Néron–Tate height

Let `A` be an abelian variety over a number field `k` and `c ∈ Pic(A) ⊗ ℚ` an ample, even
class. For every number field `K` with `k ⊆ K ⊆ k̄` and every real `B`, the set of `x ∈ A(K)`
with `ĥ_c(x) ≤ B` is finite.

The Néron–Tate height `ĥ_c` lives on the `k̄`-points of the base change `A_{k̄}`: it is the
Néron–Tate height (`Faltings.IsNeronTateHeight`) of the pull-back of `c` to `A_{k̄}`, so `ĥ_c - h`
is bounded for a height `h` associated to that pull-back. On `A(K)` the degree of a point over
`k` is at most `[K : k]`, so Northcott's theorem for heights of ample classes gives the
finiteness.

## Main results

* `Faltings.IsEvenClass.finite_setOf_neronTateHeight_le`: if `c` is ample and even, then
  `{x ∈ A(K) | ĥ_c(x) ≤ B}` is finite for every number field `k ⊆ K ⊆ k̄` and every `B`.
* `Faltings.IsEvenClass.finite_setOf_neronTateHeight_le_of_numberField`: the same for a number
  field `K` given with an embedding `k ⊆ K ⊆ k̄`, for any Néron–Tate height of `c`.

## Implementation notes

`Pic(A) ⊗ ℚ` is `ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left`, as for `Faltings.IsEvenClass`; the
definitions `Faltings.IsAmpleClass` and `Faltings.IsHeightOfClass` use `X.picardGroup ⊗[ℤ] ℚ`,
which is the same group with the factors swapped, reached by `TensorProduct.comm`. The base
change `A_{k̄}` is `(Over.pullback (Spec k̄ ⟶ Spec k)).obj A`, the class on it is the base
change to `ℚ` of the pull-back `Stacks.Picard.schemePullbackClassHom` along the projection
`A_{k̄} ⟶ A`, and `ĥ_c` is `Classical.epsilon` of the Néron–Tate property, as in
`Faltings.exists_isNeronTateHeight`. A point `x` of the group `A_{k̄}(k̄)` lies in `A(K)`, for
`K` an intermediate field of `k̄ / k` finite over `k`, when its image in `A` factors through
`Spec k̄ ⟶ Spec K`. The finiteness is proved for any base change `X` of `A` presented by a
pull-back square, with the projectivity and smoothness of `X` as instance hypotheses; for
`A_{k̄}` they come from the abelian variety structure. The evenness of `c` is not used in the
proof: Northcott's theorem holds for the Néron–Tate height of any ample class.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [Wu] Theorem 2.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Faltings

section Northcott

variable {k K : Type u} [Field k] [NumberField k] [Field K] [Algebra k K]
  {A X : Scheme.{u}} {fA : A ⟶ Spec (.of k)} [IsProjectiveVariety k fA]
  {fX : X ⟶ Spec (.of K)} [IsProjectiveVariety K fX] {p : X ⟶ A}

/-- A pull-back square `X = A ×_k K` makes `k` a field of definition of `X`, with model `A`. -/
private noncomputable def fieldOfDefinitionOfIsPullback
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    FieldOfDefinition K fX k where
  model := A
  toSpec := fA
  isVariety := inferInstance
  iso := hX.isoPullback
  iso_hom_snd := hX.isoPullback_hom_snd

/-- A `K`-point of `X = A ×_k K` whose image in `A` is defined over `k ⊆ K' ⊆ K` has degree
at most `[K' : k]` over `k`. -/
private lemma pointDegree_le_finrank
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (K' : IntermediateField k K) [FiniteDimensional k K']
    (q : {q : Spec (.of K) ⟶ X // q ≫ fX = 𝟙 _}) (r : Spec (.of K') ⟶ A)
    (hr : q.1 ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K' K)) ≫ r) :
    (fieldOfDefinitionOfIsPullback hX).pointDegree q.1 q.2 ≤ Module.finrank k K' := by
  refine IntermediateField.finrank_le_of_le_right fun z hz ↦ ?_
  obtain ⟨y, rfl⟩ := fieldRange_descResidueField_le (algebraMap K' K) r
    (q := q.1 ≫ hX.isoPullback.hom ≫ pullback.fst _ _)
    (by rw [hX.isoPullback_hom_fst, hr]) hz
  exact y.2

/-- **Northcott's theorem for heights of ample classes.** If `c` is ample on `A` and `h` is a
height associated to `p^* c` on `X = A ×_k K`, then only finitely many `K`-points of `X` of
degree at most `δ` over `k` satisfy `h ≤ B`. -/
private theorem finite_setOf_pointDegree_le_height_le_of_isHeightOfClass [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] [Smooth fX]
    (hX : IsPullback p fX fA (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A} (hamp : IsAmpleClass fA (TensorProduct.comm ℤ ℚ _ c))
    {h : {q : Spec (.of K) ⟶ X // q ≫ fX = 𝟙 _} → ℝ}
    (hh : IsHeightOfClass fX (TensorProduct.comm ℤ ℚ _
      ((Stacks.Picard.schemePullbackClassHom p).toIntLinearMap.baseChange ℚ c)) h)
    {δ : ℕ} (hδ : 1 ≤ δ) (B : ℝ) :
    {q | (fieldOfDefinitionOfIsPullback hX).pointDegree q.1 q.2 ≤ δ ∧ h q ≤ B}.Finite := by
  obtain ⟨N, n, φ, hN, hcl⟩ := exists_embeddingClass_baseChange hX hamp
  obtain ⟨m, γ, hm, hγ, C₁, hC₁⟩ := hh
  obtain ⟨C₂, hC₂⟩ := exists_abs_inv_mul_height_sub_le hm hN hγ hcl
  refine (ProjectiveEmbedding.finite_setOf_pointDegree_le_height_le
    (fieldOfDefinitionOfIsPullback hX) (ProjectiveEmbedding.baseChange hX φ)
    ⟨φ.hom ≫ pullback.snd _ _, ?_⟩ hδ (N * (B + C₁ + C₂))).subset fun q hq ↦ ⟨hq.1, ?_⟩
  · exact (baseChangeHom_snd φ.hom).trans ((reassoc_of% hX.isoPullback_hom_fst) _).symm
  · have e1 := abs_le.1 (hC₁ q)
    have e2 := abs_le.1 (hC₂ q)
    simp only [EmbeddingGroup.height, FreeAbelianGroup.lift_apply_of] at e1 e2
    rw [← inv_mul_le_iff₀ (by exact_mod_cast hN)]
    linarith [hq.2]

end Northcott

/-- **Northcott for the Néron–Tate height.** Let `A` be an abelian variety over a number field
`k`, `Ω` an algebraic closure of `k` and `c ∈ Pic(A) ⊗ ℚ` ample and even, with Néron–Tate height
`ĥ_c` on `A(Ω)` (the Néron–Tate height `Faltings.IsNeronTateHeight` of the pull-back of `c` to
the base change `A_Ω`). For every number field `k ⊆ K ⊆ Ω` and every real `B`, the set
`{x ∈ A(K) | ĥ_c(x) ≤ B}` is finite. -/
@[faltings "prop_nt_ample_even_northcott"]
theorem IsEvenClass.finite_setOf_neronTateHeight_le {k : Type u} [Field k] [NumberField k]
    {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    (hamp : letI : IsProjectiveVariety k A.hom :=
        ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
          (isProjective_of_isAbelianVariety k A)⟩
      IsAmpleClass A.hom (TensorProduct.comm ℤ ℚ _ c))
    (hc : IsEvenClass k A c)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] (B : ℝ) :
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
    letI hhat : Additive (Over.mk (𝟙 (Spec (.of Ω))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj A) → ℝ :=
      Classical.epsilon (IsNeronTateHeight
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj A)
          ((Stacks.Picard.schemePullbackClassHom
            (pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).toIntLinearMap
              |>.baseChange ℚ c)) ∘
        fun z ↦ (⟨z.toMul.left, by simpa using Over.w z.toMul⟩ :
          {p : Spec (.of Ω) ⟶ _ // p ≫ _ = 𝟙 _})
    {x | (∃ q : Spec (.of K) ⟶ A.left,
        x.toMul.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ q) ∧ hhat x ≤ B}.Finite := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  letI : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  set AK := (Over.pullback φ).obj A
  letI : IsProjectiveVariety Ω AK.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := AK.hom)
      (isProjective_of_isAbelianVariety Ω AK)⟩
  letI : Smooth AK.hom := smooth_of_isAbelianVariety Ω AK
  obtain ⟨⟨h, hh, C, hC⟩, -⟩ :=
    Classical.epsilon_spec (exists_isNeronTateHeight_of_isAlgebraic AK
      ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φ)).toIntLinearMap.baseChange
        ℚ c))
  have hX : IsPullback (pullback.fst A.hom φ) AK.hom A.hom φ := IsPullback.of_hasPullback _ _
  let sec (x : Additive (Over.mk (𝟙 (Spec (.of Ω))) ⟶ AK)) :
      {q : Spec (.of Ω) ⟶ AK.left // q ≫ AK.hom = 𝟙 _} :=
    ⟨x.toMul.left, by simpa using Over.w x.toMul⟩
  have hinj : Function.Injective sec := fun x y hxy ↦
    Additive.toMul.injective (Over.OverMorphism.ext (congrArg Subtype.val hxy))
  refine ((finite_setOf_pointDegree_le_height_le_of_isHeightOfClass (p := pullback.fst A.hom φ)
    hX hamp hh (Module.finrank_pos (R := k) (M := K)) (B + C)).preimage hinj.injOn).subset ?_
  rintro x ⟨⟨q, hq⟩, hx⟩
  have hx' : Classical.epsilon (IsNeronTateHeight AK
      ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φ)).toIntLinearMap.baseChange
        ℚ c)) (sec x) ≤ B := hx
  exact ⟨pointDegree_le_finrank hX K (sec x) q hq,
    by linarith [(abs_le.1 (hC (sec x))).1]⟩

/-- **Northcott over a number field.** Let `A` be an abelian variety over a number field `k`,
`c ∈ Pic(A) ⊗ ℚ` an ample even class, `F` its Néron–Tate height on `A(k̄)` and `k ⊆ K ⊆ k̄` a
number field. For every `C`, only finitely many `x ∈ A(K)` have `F(x) ≤ C`, where `x` is seen
in `A(k̄)` through `Spec k̄ ⟶ Spec K`. -/
theorem IsEvenClass.finite_setOf_neronTateHeight_le_of_numberField {k : Type u} [Field k]
    [NumberField k] {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
    {c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left}
    (hamp : letI : IsProjectiveVariety k A.hom :=
        ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
          (isProjective_of_isAbelianVariety k A)⟩
      IsAmpleClass A.hom (TensorProduct.comm ℤ ℚ _ c))
    (hc : IsEvenClass k A c) (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (K : Type u) [Field K] [NumberField K] [Algebra k K] [Algebra K kbar]
    [IsScalarTower k K kbar] (C : ℝ) :
    haveI : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
    haveI : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
    let φΩ := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
    let AΩ : Over (Spec (.of kbar)) := (Over.pullback φΩ).obj A
    ∀ F : {p : Spec (.of kbar) ⟶ AΩ.left // p ≫ AΩ.hom = 𝟙 _} → ℝ,
      IsNeronTateHeight AΩ
        ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φΩ)).toIntLinearMap.baseChange
          ℚ c) F →
      {x : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) |
        F ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ x.toMul.left)
          (𝟙 _) (by simp [φΩ, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]), pullback.lift_snd _ _ _⟩ ≤ C}.Finite := by
  have : CharZero kbar := charZero_of_injective_algebraMap (algebraMap k kbar).injective
  have : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
  intro φΩ AΩ F hF
  obtain rfl := hF.unique (Classical.epsilon_spec (exists_isNeronTateHeight A kbar c))
  -- `K` is identified with its image `L` in `k̄`, where
  -- `IsEvenClass.finite_setOf_neronTateHeight_le` applies
  let τ := IsScalarTower.toAlgHom k K kbar
  let L : IntermediateField k kbar := τ.fieldRange
  let eK : K ≃ₐ[k] L := AlgEquiv.ofInjectiveField τ
  have : FiniteDimensional k K := Module.Finite.of_restrictScalars_finite ℚ k K
  have : FiniteDimensional k L := LinearEquiv.finiteDimensional eK.toLinearEquiv
  let sec : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) →
      Additive (Over.mk (𝟙 (Spec (.of kbar))) ⟶ AΩ) := fun x ↦ .ofMul <| Over.homMk
        (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ x.toMul.left) (𝟙 _)
          (by simp [φΩ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))
        (pullback.lift_snd _ _ _)
  have hsec : ∀ x, (sec x).toMul.left ≫ pullback.fst A.hom φΩ =
      Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ x.toMul.left := fun x ↦
    pullback.lift_fst _ _ _
  have hinj : Function.Injective sec := fun x y hxy ↦ by
    have h := hsec x
    rw [hxy, hsec y] at h
    exact Additive.toMul.injective (Over.OverMorphism.ext ((cancel_epi _).1 h).symm)
  refine ((hc.finite_setOf_neronTateHeight_le hamp kbar L C).preimage hinj.injOn).subset
    fun x hx ↦ ⟨⟨Spec.map (CommRingCat.ofHom eK.toRingEquiv.toRingHom) ≫ x.toMul.left, ?_⟩, hx⟩
  rw [hsec, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3

end Faltings
