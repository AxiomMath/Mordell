module
public import Mordell.CurveProduct.Diagonal
public import Mordell.CurveProduct.BoxEulerCharacteristic
public import Mordell.AlgebraicGeometry.Surface.IntersectionCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.SurfaceEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity

/-!
# Intersection numbers of pulled-back invertible sheaves on `C × C`

Let `C` be a smooth projective curve over a field `k`, `X = C ×_k C` with projections
`pr₁, pr₂ : X ⟶ C`, and `Δ ⊆ X` the diagonal. For invertible `𝓞_C`-modules `𝓐, 𝓐'` of degrees
`a, a'`, the intersection numbers on the surface `X` are

`(pr₁^* 𝓐 · pr₂^* 𝓐') = a a'`, `(pr_i^* 𝓐 · pr_i^* 𝓐') = 0`, `(pr_i^* 𝓐 · 𝓞_X(Δ)) = a`

for `i = 1, 2`.

## Main results

* `Faltings.intersectionNumber_pullback_curve_prod_self`: the three formulas above.
* `Faltings.picardIntersection_picardClass_pair`, `Faltings.intersectionNumber_pair_swap`,
  `Faltings.intersectionNumber_pair_eq_add_of_iso_tensorObj`: on a proper scheme of dimension
  at most `2`, the pairing on `Pic` of two classes is the intersection number of their
  representatives, which is symmetric and additive in the first slot.
* `Faltings.intersectionNumber_diagonal_eq_invertibleCurveDegree`: `(L · 𝓞_X(Δ)) = deg Δ^* L`.
* `Faltings.topologicalKrullDim_pullback_self`: `C ×_k C` has dimension `2`.
* `Faltings.invertibleCurveDegree_pullback_of_isIso`, `Faltings.invertibleCurveDegree_congr`: the
  degree is invariant under isomorphisms of curves and rewriting of the structure morphism.

## Implementation notes

The intersection number `(𝓛 · 𝓜)` on `X` is `AlgebraicGeometry.intersectionNumber` with
`Z = X` (the identity closed immersion), `d = 2` and structure morphism `pr₁ ≫ f`, applied to the
family `![𝓛, 𝓜]`; the bound `dim X ≤ 2` it needs is proved inside the statement, since `X` is
smooth of relative dimension `2` over `k`. The degree of an invertible module on `C` is
`AlgebraicGeometry.invertibleCurveDegree`. The two projections are indexed by `Fin 2`, as
`![pullback.fst f f, pullback.snd f f]`. The diagonal `Δ` is the ideal sheaf
`(pullback.diagonal f).ker`, an effective Cartier divisor by
`Faltings.isEffectiveCartierDivisor_ker_diagonal`, and `𝓞_X(Δ)` is
`Stacks.Divisors.invertibleSheaf`; since that module carries invertibility in the sense of
`Stacks.SheafOfModules.IsInvertible`, the statement takes an invertible `M` with an isomorphism
`M ≅ 𝓞_X(Δ)`, which is the same statement for `M = 𝓞_X(Δ)`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3 and Section 8
* [Stacks Project, Tag 0BEP], [Stacks Project, Tag 0AYR]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

namespace Faltings

section Pair

variable (k : Type u) [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [IsProper p]
  (hd : topologicalKrullDim Y ≤ ((2 : ℕ) : WithBot ℕ∞))

/-- On classes of two invertible modules, the form `picardIntersection` is their intersection
number. -/
public lemma picardIntersection_picardClass_pair (L N : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hN : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N] :
    picardIntersection k p (𝟙 Y) 2 hd
        ![Stacks.SheafOfModules.picardClass _ _ L hL,
          Stacks.SheafOfModules.picardClass _ _ N hN] =
      @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![L, N] (Fin.forall_fin_two.2 ⟨hL, hN⟩) := by
  have : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L, N] q) :=
    Fin.forall_fin_two.2 ⟨hL, hN⟩
  refine Eq.trans ?_ (picardIntersection_picardClass k p (𝟙 Y) 2 hd ![L, N])
  congr 1
  funext q
  fin_cases q <;> rfl

/-- The intersection number of two invertible modules is symmetric. -/
public lemma intersectionNumber_pair_swap (L N : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hN : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N] :
    @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![L, N] (Fin.forall_fin_two.2 ⟨hL, hN⟩) =
      @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![N, L] (Fin.forall_fin_two.2 ⟨hN, hL⟩) := by
  have : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![N, L] q) :=
    Fin.forall_fin_two.2 ⟨hN, hL⟩
  refine Eq.trans ?_ (intersectionNumber_comp_perm k p (𝟙 Y) 2 hd ![N, L] (Equiv.swap 0 1))
  congr 1
  funext q
  fin_cases q <;> rfl

/-- Additivity of the intersection number in the first slot: if `L ≅ L₁ ⊗ L₂` then
`(L · N) = (L₁ · N) + (L₂ · N)`. -/
public lemma intersectionNumber_pair_eq_add_of_iso_tensorObj (L L₁ L₂ N : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [hL₁ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₁]
    [hL₂ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L₂]
    [hN : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    (e : L ≅ Scheme.Modules.tensorObj L₁ L₂) :
    @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![L, N] (Fin.forall_fin_two.2 ⟨hL, hN⟩) =
      @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![L₁, N] (Fin.forall_fin_two.2 ⟨hL₁, hN⟩) +
        @intersectionNumber k _ _ _ p _ (𝟙 Y) _ 2 hd ![L₂, N]
          (Fin.forall_fin_two.2 ⟨hL₂, hN⟩) := by
  have : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L, N] q) :=
    Fin.forall_fin_two.2 ⟨hL, hN⟩
  have : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L₁, N] q) :=
    Fin.forall_fin_two.2 ⟨hL₁, hN⟩
  have : ∀ q, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (![L₂, N] q) :=
    Fin.forall_fin_two.2 ⟨hL₂, hN⟩
  refine intersectionNumber_tensor k p (𝟙 Y) 2 hd 0 _ _ _ (fun q hq => ?_) (fun q hq => ?_) e
  all_goals fin_cases q
  all_goals first | exact absurd rfl hq | rfl

end Pair

/-- The pullback of the structure sheaf is the structure sheaf. -/
private noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (q : X ⟶ Y) :
    (Scheme.Modules.pullback q).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  RingedSpaceModuleAdjunction.modulePullbackObjUnitIso q.toLRSHom.toShHom

/-- The degree of the structure sheaf of a curve is zero. -/
private lemma invertibleCurveDegree_unit (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (h : topologicalKrullDim X ≤ 1) :
    invertibleCurveDegree k f h (SheafOfModules.unit X.ringCatSheaf) = 0 := by
  simp [invertibleCurveDegree]

/-- The degree is unchanged by pulling back along an isomorphism of schemes. -/
public lemma invertibleCurveDegree_pullback_of_isIso (k : Type u) [Field k] {Y Z : Scheme.{u}}
    (φ : Y ⟶ Z) [IsIso φ] (g : Z ⟶ Spec (.of k)) [IsProper g] [IsProper (φ ≫ g)]
    (hY : topologicalKrullDim Y ≤ 1) (hZ : topologicalKrullDim Z ≤ 1) (E : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 E] :
    invertibleCurveDegree k (φ ≫ g) hY ((Scheme.Modules.pullback φ).obj E) =
      invertibleCurveDegree k g hZ E := by
  simp only [invertibleCurveDegree, finrank_cohomologyOverField_pullback,
    finrank_cohomologyOverField_unit_pushforward]

/-- The degree only depends on the structure morphism, not on how it is written. -/
public lemma invertibleCurveDegree_congr (k : Type u) [Field k] {X : Scheme.{u}}
    {g g' : X ⟶ Spec (.of k)} [IsProper g] [IsProper g'] (hg : g = g')
    (h : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E] :
    invertibleCurveDegree k g h E = invertibleCurveDegree k g' h E := by
  subst hg; rfl

/-- The Euler characteristic of any module isomorphic to a box product `pr₁^* A ⊗ pr₂^* B` on
`C ×_k C`. -/
private lemma eulerCharacteristic_eq_of_iso_tensorObj (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (A B : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 B]
    (M : (pullback f f).Modules)
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 M]
    (e : M ≅ Scheme.Modules.tensorObj ((Scheme.Modules.pullback (pullback.fst f f)).obj A)
      ((Scheme.Modules.pullback (pullback.snd f f)).obj B)) :
    @eulerCharacteristic k _ _ (pullback.fst f f ≫ f) _ M
        (SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) M) =
      (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A +
          1 - genus f) *
        (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) B +
          1 - genus f) := by
  have := SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) M
  have := SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f)
    (Scheme.Modules.tensorObj ((Scheme.Modules.pullback (pullback.fst f f)).obj A)
      ((Scheme.Modules.pullback (pullback.snd f f)).obj B))
  rw [eulerCharacteristic_eq_of_iso k (pullback.fst f f ≫ f) e]
  exact eulerCharacteristic_externalTensorProduct_of_isSmoothProjectiveCurve k f f A B

/-- `χ(𝒪_{C × C}) = (1 - g)²` for a smooth projective curve `C` of genus `g`. -/
public lemma eulerCharacteristic_unit_pullback (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] :
    @eulerCharacteristic k _ _ (pullback.fst f f ≫ f) _
        (SheafOfModules.unit (pullback f f).ringCatSheaf)
        (SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) _) =
      (1 - genus f) ^ 2 := by
  have := eulerCharacteristic_eq_of_iso_tensorObj k f (SheafOfModules.unit C.ringCatSheaf)
    (SheafOfModules.unit C.ringCatSheaf) (SheafOfModules.unit (pullback f f).ringCatSheaf)
    ((tensorProductRightUnitor _ _ _).symm ≪≫ tensorProductIso _ _
      (pullbackUnitIso (pullback.fst f f)).symm (pullbackUnitIso (pullback.snd f f)).symm)
  rwa [invertibleCurveDegree_unit, zero_add, ← sq] at this

/-- `χ(N) = (deg E + 1 - g)(1 - g)` for any `N ≅ pr₁^* E`. -/
private lemma eulerCharacteristic_pullback_fst (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (E : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 E] (N : (pullback f f).Modules)
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 N]
    (e : N ≅ (Scheme.Modules.pullback (pullback.fst f f)).obj E) :
    @eulerCharacteristic k _ _ (pullback.fst f f ≫ f) _ N
        (SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) _) =
      (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) E +
          1 - genus f) * (1 - genus f) := by
  have := eulerCharacteristic_eq_of_iso_tensorObj k f E (SheafOfModules.unit C.ringCatSheaf) _
    (e ≪≫ (tensorProductRightUnitor _ _ _).symm ≪≫
      tensorProductIso _ _ (Iso.refl _) (pullbackUnitIso (pullback.snd f f)).symm)
  rwa [invertibleCurveDegree_unit, zero_add] at this

/-- `χ(N) = (deg E + 1 - g)(1 - g)` for any `N ≅ pr₂^* E`. -/
private lemma eulerCharacteristic_pullback_snd (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (E : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 E] (N : (pullback f f).Modules)
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 N]
    (e : N ≅ (Scheme.Modules.pullback (pullback.snd f f)).obj E) :
    @eulerCharacteristic k _ _ (pullback.fst f f ≫ f) _ N
        (SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) _) =
      (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) E +
          1 - genus f) * (1 - genus f) := by
  have := eulerCharacteristic_eq_of_iso_tensorObj k f (SheafOfModules.unit C.ringCatSheaf) E _
    (e ≪≫ (tensorProductLeftUnitor _ _ _).symm ≪≫
      tensorProductIso _ _ (pullbackUnitIso (pullback.fst f f)).symm (Iso.refl _))
  rwa [invertibleCurveDegree_unit, zero_add, mul_comm] at this

/-- `(pr₁^* A · pr₂^* A') = deg A · deg A'`. -/
private lemma intersectionNumber_pullback_fst_snd (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (A A' : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A']
    (hX : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞)) (h) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hX
        ![(Scheme.Modules.pullback (pullback.fst f f)).obj A,
          (Scheme.Modules.pullback (pullback.snd f f)).obj A'] h =
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A *
        invertibleCurveDegree k f
          (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A' := by
  rw [intersectionNumber_two_eq_eulerCharacteristic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eulerCharacteristic_eq_of_iso_tensorObj k f A A' _ (Iso.refl _),
    eulerCharacteristic_pullback_fst k f A _ (Iso.refl _),
    eulerCharacteristic_pullback_snd k f A' _ (Iso.refl _), eulerCharacteristic_unit_pullback]
  ring

/-- Two pullbacks along the same projection `q` have intersection number zero, as soon as
`χ(N) = (deg E + 1 - g)(1 - g)` for every invertible `N ≅ q^* E`; this holds for
`q = pr₁, pr₂`. -/
private lemma intersectionNumber_pullback_pullback_eq_zero (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (q : pullback f f ⟶ C)
    (hq : ∀ (E : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 E]
      (N : (pullback f f).Modules)
      [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 N]
      (_ : N ≅ (Scheme.Modules.pullback q).obj E),
      @eulerCharacteristic k _ _ (pullback.fst f f ≫ f) _ N
          (SheafOfModules.isCoherent_of_isInvertible k (pullback.fst f f ≫ f) _) =
        (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) E +
          1 - genus f) * (1 - genus f))
    (A A' : C.Modules) [hA : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    [hA' : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A']
    (hX : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞)) (h) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hX
        ![(Scheme.Modules.pullback q).obj A, (Scheme.Modules.pullback q).obj A'] h = 0 := by
  rw [intersectionNumber_two_eq_eulerCharacteristic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hq (Scheme.Modules.tensorObj A A') (Scheme.Modules.tensorObj
      ((Scheme.Modules.pullback q).obj A) ((Scheme.Modules.pullback q).obj A'))
      (pullbackTensorObjIso q A A').symm,
    hq A _ (Iso.refl _), hq A' _ (Iso.refl _), eulerCharacteristic_unit_pullback]
  have hdeg : invertibleCurveDegree k f _ (Scheme.Modules.tensorObj A A') =
      invertibleCurveDegree k f _ A + invertibleCurveDegree k f _ A' :=
    invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A A' hA hA' inferInstance
  rw [hdeg]
  ring

/-- `C ×_k C` is a surface. -/
public lemma topologicalKrullDim_pullback_self (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] :
    topologicalKrullDim ↥(pullback f f) = 2 := by
  have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback f f).flip (inferInstanceAs (SmoothOfRelativeDimension 1 f))
  have : SmoothOfRelativeDimension 2 (pullback.fst f f ≫ f) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
  have : Nonempty ↥(pullback f f) :=
    ⟨(pullback.diagonal f).base (Nonempty.some (inferInstance : Nonempty C))⟩
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2 (pullback.fst f f ≫ f)

/-- Intersecting with `𝒪(Δ)` restricts to the diagonal `Δ ≅ C`: for invertible `L, M` on
`C ×_k C` with `M ≅ 𝒪(Δ)`, `(L · M) = deg Δ^* L`. -/
public lemma intersectionNumber_diagonal_eq_invertibleCurveDegree (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (L M : (pullback f f).Modules)
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 M]
    (eM : M ≅ Stacks.Divisors.invertibleSheaf (pullback.diagonal f).ker)
    (hX : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞)) (h) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hX ![L, M] h =
      @invertibleCurveDegree k _ _ f _ (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)
        ((Scheme.Modules.pullback (pullback.diagonal f)).obj L) (isInvertible_pullbackObj _ L) := by
  have := (isEffectiveCartierDivisor_ker_diagonal k f).1
  have hφι : (pullback.diagonal f).toImage ≫ (pullback.diagonal f).ker.subschemeι =
      pullback.diagonal f := (pullback.diagonal f).toImage_imageι
  have hcomp : (pullback.diagonal f).toImage ≫ (pullback.diagonal f).ker.subschemeι ≫
      pullback.fst f f ≫ f = f := by
    rw [reassoc_of% hφι, pullback.diagonal_fst_assoc]
  have : IsProper ((pullback.diagonal f).toImage ≫ (pullback.diagonal f).ker.subschemeι ≫
      pullback.fst f f ≫ f) := hcomp ▸ inferInstance
  rw [intersectionNumber_eq_invertibleCurveDegree_of_isEffectiveCartierDivisor k
    (pullback.fst f f ≫ f) (topologicalKrullDim_pullback_self k f) _ M
    (pullback.diagonal f).ker eM,
    ← invertibleCurveDegree_pullback_of_isIso k (pullback.diagonal f).toImage _
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f),
    invertibleCurveDegree_congr k hcomp]
  exact invertibleCurveDegree_eq_of_iso k f _
    ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hφι).app L)

/-- Intersecting with `𝒪(Δ)` restricts to `Δ ≅ C`: `(q^* A · 𝒪(Δ)) = deg A` for any retraction
`q` of the diagonal. -/
private lemma intersectionNumber_pullback_diagonal (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (q : pullback f f ⟶ C)
    (hq : pullback.diagonal f ≫ q = 𝟙 C) (A : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    (M : (pullback f f).Modules)
    [SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 M]
    (eM : M ≅ Stacks.Divisors.invertibleSheaf (pullback.diagonal f).ker)
    (hX : topologicalKrullDim ↥(pullback f f) ≤ ((2 : ℕ) : WithBot ℕ∞)) (h) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 hX
        ![(Scheme.Modules.pullback q).obj A, M] h =
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A := by
  have := isInvertible_pullbackObj q A
  rw [intersectionNumber_diagonal_eq_invertibleCurveDegree k f _ M eM]
  exact invertibleCurveDegree_eq_of_iso k f _
    ((Scheme.Modules.pullbackComp _ q).app A ≪≫ (Scheme.Modules.pullbackCongr hq).app A ≪≫
      (Scheme.Modules.pullbackId C).app A)

/-- On `X = C ×_k C` for a smooth projective curve `f : C ⟶ Spec k`, with projections
`pr₁ = pullback.fst f f`, `pr₂ = pullback.snd f f`, and invertible `𝓞_C`-modules `A, A'`:
`(pr₁^* A · pr₂^* A') = deg A · deg A'`, and for each `i`, `(pr_i^* A · pr_i^* A') = 0` and
`(pr_i^* A · M) = deg A` for any invertible `M ≅ 𝓞_X(Δ)`, `Δ` the diagonal. -/
@[faltings "lem_nt_intersection_pullbacks"]
public theorem intersectionNumber_pullback_curve_prod_self (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] (A A' : C.Modules)
    [hA : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    [hA' : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A']
    (M : (pullback f f).Modules)
    [hM : SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2 M]
    (eM : M ≅ Stacks.Divisors.invertibleSheaf (pullback.diagonal f).ker) :
    @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 (by
          have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
            (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
              (IsPullback.of_hasPullback f f).flip
              (inferInstanceAs (SmoothOfRelativeDimension 1 f))
          have : SmoothOfRelativeDimension 2 (pullback.fst f f ≫ f) :=
            smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
          rcases isEmpty_or_nonempty ↥(pullback f f) with h | h
          · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
          · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
              (pullback.fst f f ≫ f)).le)
        ![(Scheme.Modules.pullback (pullback.fst f f)).obj A,
          (Scheme.Modules.pullback (pullback.snd f f)).obj A']
        (Fin.forall_fin_two.2 ⟨isInvertible_pullbackObj _ A, isInvertible_pullbackObj _ A'⟩) =
      invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A *
        invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A' ∧
      ∀ i : Fin 2,
        @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 (by
          have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
            (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
              (IsPullback.of_hasPullback f f).flip
              (inferInstanceAs (SmoothOfRelativeDimension 1 f))
          have : SmoothOfRelativeDimension 2 (pullback.fst f f ≫ f) :=
            smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
          rcases isEmpty_or_nonempty ↥(pullback f f) with h | h
          · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
          · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
              (pullback.fst f f ≫ f)).le)
          ![(Scheme.Modules.pullback (![pullback.fst f f, pullback.snd f f] i)).obj A,
            (Scheme.Modules.pullback (![pullback.fst f f, pullback.snd f f] i)).obj A']
          (Fin.forall_fin_two.2 ⟨isInvertible_pullbackObj _ A, isInvertible_pullbackObj _ A'⟩) = 0 ∧
        @intersectionNumber k _ _ _ (pullback.fst f f ≫ f) _ (𝟙 _) _ 2 (by
          have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
            (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
              (IsPullback.of_hasPullback f f).flip
              (inferInstanceAs (SmoothOfRelativeDimension 1 f))
          have : SmoothOfRelativeDimension 2 (pullback.fst f f ≫ f) :=
            smoothOfRelativeDimension_comp (n := 1) (m := 1) _ _
          rcases isEmpty_or_nonempty ↥(pullback f f) with h | h
          · simp [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 h]
          · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 2
              (pullback.fst f f ≫ f)).le)
          ![(Scheme.Modules.pullback (![pullback.fst f f, pullback.snd f f] i)).obj A, M]
          (Fin.forall_fin_two.2 ⟨isInvertible_pullbackObj _ A, hM⟩) =
          invertibleCurveDegree k f
            (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A := by
  refine ⟨intersectionNumber_pullback_fst_snd k f A A' _ _, fun i => ?_⟩
  fin_cases i
  · exact ⟨intersectionNumber_pullback_pullback_eq_zero k f _
      (eulerCharacteristic_pullback_fst k f) A A' _ _,
      intersectionNumber_pullback_diagonal k f _ (pullback.diagonal_fst f) A M eM _ _⟩
  · exact ⟨intersectionNumber_pullback_pullback_eq_zero k f _
      (eulerCharacteristic_pullback_snd k f) A A' _ _,
      intersectionNumber_pullback_diagonal k f _ (pullback.diagonal_snd f) A M eM _ _⟩

end Faltings
