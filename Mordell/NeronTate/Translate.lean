module

public import Mordell.NeronTate.Existence
public import Mordell.NeronTate.Uniqueness

/-!
# The Néron–Tate height of a translated class

Let `A` be an abelian variety over a number field `k`, `c ∈ Pic(A) ⊗ ℚ` and `y ∈ A(k̄)`. Then
`ĥ_{τ_y^* c}(x) = ĥ_c(x + y) - ĥ_c(y)` for `x ∈ A(k̄)`, where `τ_y : x ↦ x + y` is the
translation by `y`.

Write `ĥ_c x = b x x / 2 + ℓ x`. Then `x ↦ ĥ_c(x + y) - ĥ_c(y) = b x x / 2 + (b x y + ℓ x)` is
again a quadratic form plus an additive function of `x`. It differs from `h_c ∘ τ_y` by a bounded
function, and by functoriality of heights `h_c ∘ τ_y` differs from a height `h_{τ_y^* c}` of
`τ_y^* c` by a bounded function. So it differs from `ĥ_{τ_y^* c}` by a bounded function, and two
quadratic-plus-additive functions at bounded distance are equal.

## Main results

* `Faltings.IsNeronTateHeight.apply_eq_apply_add_sub`: if `f` is a Néron–Tate height of `c_K` and
  `f'` one of `τ_y^* c_K` on `A_K`, then `f' x = f (x + y) - f y`.

## Implementation notes

As for `Faltings.neronPairing`, the points `A(k̄)` are those of the base change
`A_K = (Over.pullback (Spec K ⟶ Spec k)).obj A` to an algebraic closure `K` of `k`, an abelian
variety over `K`, and `c` enters `ℚ ⊗ Pic(A_K)` as its pull-back `c_K` along the projection
`A_K ⟶ A`, tensored with `ℚ`. A point of `A_K(K)` is a morphism `Over.mk (𝟙 (Spec K)) ⟶ A_K`,
with the group law of `A_K` written additively through `Additive`; it is read as a section of
`A_K ⟶ Spec K`, the argument of `Faltings.IsNeronTateHeight`, through its underlying morphism of
schemes. The translation `τ_y : A_K ⟶ A_K` is `lift (𝟙 _) (toUnit _ ≫ y) ≫ μ`, and `τ_y^*` on
`ℚ ⊗ Pic(A_K)` is the `ℚ`-base change of the pull-back of classes along it.

Néron–Tate heights `f` of `c_K` and `f'` of `τ_y^* c_K` are hypotheses rather than choices: a
Néron–Tate height of a class is unique, and its existence is a separate result.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 2.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  TensorProduct

universe u

namespace Faltings

/-- The translation formula on an abstract group: if `F` and `F'` are quadratic-plus-additive
and `F' - F ∘ τ_y` is bounded, then `F' x = F (x + y) - F y`. Indeed `x ↦ F (x + y) - F y` is
`b(x, x) / 2 + (ℓ + b(·, y))(x)`, at bounded distance from `F'`. -/
private lemma eq_apply_add_sub_of_abs_sub_le {M : Type*} [AddCommGroup M]
    {b b' : M →+ M →+ ℝ} (hb : ∀ x y, b x y = b y x) (hb' : ∀ x y, b' x y = b' y x)
    {ℓ ℓ' : M →+ ℝ} {F F' : M → ℝ} (hF : ∀ x, F x = b x x / 2 + ℓ x)
    (hF' : ∀ x, F' x = b' x x / 2 + ℓ' x) (y : M) {C : ℝ}
    (hC : ∀ x, |F' x - F (x + y)| ≤ C) (x : M) : F' x = F (x + y) - F y := by
  refine congrFun (eq_of_abs_sub_le_of_eq_half_add b' b hb' hb ℓ' (ℓ + b.flip y) hF'
    (f' := fun z => F (z + y) - F y) (fun z => ?_) (C := C + |F y|) fun z => ?_) x
  · simp only [hF, map_add, AddMonoidHom.add_apply, AddMonoidHom.flip_apply, hb y z]
    ring
  · rw [sub_sub_eq_add_sub, add_sub_right_comm]
    exact (abs_add_le _ _).trans (by gcongr; exact hC z)

/-- On points, the translation `τ_y = lift (𝟙 _) (toUnit _ ≫ y) ≫ μ` is `x ↦ x * y`. -/
lemma comp_translate {C : Type*} [Category C] [CartesianMonoidalCategory C] {A : C}
    [MonObj A] (x y : 𝟙_ C ⟶ A) : x ≫ lift (𝟙 A) (toUnit A ≫ y) ≫ μ = x * y := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (x ≫ toUnit A) (𝟙 _), Category.id_comp]

/-- The translation formula over a field `K` algebraic over `ℚ`: if `f` is a Néron–Tate height
of `c` and `f'` one of `τ_y^* c`, then `f' x = f (x + y) - f y`. -/
private theorem isNeronTateHeight_translate {K : Type u} [Field K] [Algebra ℚ K]
    [Algebra.IsAlgebraic ℚ K] (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety K A]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left) (y : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A))
    {f f' : {p : Spec (.of K) ⟶ A.left // p ≫ A.hom = 𝟙 _} → ℝ}
    (hf : IsNeronTateHeight A c f)
    (hf' : IsNeronTateHeight A ((Stacks.Picard.schemePullbackClassHom
      (lift (𝟙 _) (toUnit _ ≫ y.toMul) ≫ μ).left).toIntLinearMap.baseChange ℚ c) f')
    (x : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A)) :
    f' ⟨x.toMul.left, Over.w x.toMul⟩ =
      f ⟨(x + y).toMul.left, Over.w (x + y).toMul⟩ - f ⟨y.toMul.left, Over.w y.toMul⟩ := by
  generalize hτ : (lift (𝟙 _) (toUnit _ ≫ y.toMul) ≫ μ : A ⟶ A) = τ at hf'
  letI : IsProjectiveVariety K A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety K A)⟩
  letI : Smooth A.hom := smooth_of_isAbelianVariety K A
  letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨⟨h, hh, C, hC⟩, b, hb, ℓ, hfb⟩ := hf
  obtain ⟨⟨h', hh', C', hC'⟩, b', hb', ℓ', hfb'⟩ := hf'
  -- `h ∘ τ_y` is a height of `τ_y^* c`, so it is within `D` of `h'`
  have hτh := IsHeightOfClass.comp τ.left (Over.w τ) hh
  rw [← schemePullbackClassHom_eq_pullbackPicardHom, ← comm_baseChange] at hτh
  obtain ⟨D, hD⟩ := hh'.exists_abs_sub_le hτh
  refine eq_apply_add_sub_of_abs_sub_le (F := fun x => f ⟨x.toMul.left, Over.w x.toMul⟩)
    (F' := fun x => f' ⟨x.toMul.left, Over.w x.toMul⟩) hb hb' (fun _ => hfb _) (fun _ => hfb' _)
    y (C := C' + D + C) (fun z => ?_) x
  have e := hD ⟨z.toMul.left, Over.w z.toMul⟩
  have hτz : z.toMul.left ≫ τ.left = (z + y).toMul.left := by
    subst hτ; exact congrArg Over.Hom.left (comp_translate (C := Over (Spec (.of K))) _ _)
  rw [show h ⟨_, _⟩ = h ⟨_, Over.w (z + y).toMul⟩ from congrArg h (Subtype.ext hτz)] at e
  have := hC ⟨(z + y).toMul.left, Over.w (z + y).toMul⟩
  rw [abs_sub_comm] at this
  exact ((abs_sub_le _ _ _).trans <| add_le_add (hC' _) <|
    (abs_sub_le _ _ _).trans <| add_le_add e this).trans_eq (add_assoc ..).symm

/-- On an abelian variety `A` over a number field `k`, with `K` an algebraic closure of `k`:
for `c ∈ Pic(A) ⊗ ℚ` with base change `c_K` to `A_K`, and a point `y ∈ A_K(K)` with translation
`τ_y : A_K → A_K`, `x ↦ x + y`, if `f = ĥ_{c_K}` and `f' = ĥ_{τ_y^* c_K}` are Néron–Tate heights
then `f' x = f (x + y) - f y`. -/
@[faltings "lem_nt_neron_tate_translation"]
theorem IsNeronTateHeight.apply_eq_apply_add_sub {k : Type u} [Field k] [NumberField k]
    {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A]
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (c : ℚ ⊗[ℤ] Stacks.Picard.ofScheme A.left)
    (y : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A))
    {f f' : {p : Spec (.of K) ⟶ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A).left //
        p ≫ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A).hom =
          𝟙 _} → ℝ} :
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    IsNeronTateHeight ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)
        ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))).toIntLinearMap.baseChange ℚ c) f →
      IsNeronTateHeight ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)
        ((Stacks.Picard.schemePullbackClassHom
          (lift (𝟙 _) (toUnit _ ≫ y.toMul) ≫ μ).left).toIntLinearMap.baseChange ℚ
          ((Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))).toIntLinearMap.baseChange ℚ c))
        f' →
      ∀ x : Additive (Over.mk (𝟙 (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A),
        f' ⟨x.toMul.left, Over.w x.toMul⟩ =
          f ⟨(x + y).toMul.left, Over.w (x + y).toMul⟩ - f ⟨y.toMul.left, Over.w y.toMul⟩ := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  exact isNeronTateHeight_translate _ _ y

end Faltings
