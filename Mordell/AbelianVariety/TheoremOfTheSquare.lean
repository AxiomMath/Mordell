module
public import Mordell.AbelianVariety.PhiMap
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyOfAPoint
public import Mordell.AbelianVariety.PicZero
public import Mordell.AlgebraicGeometry.GroupScheme.BaseChangePoints
public import Mathlib

/-!
# The theorem of the square

Let `A` be an abelian variety over a field `k` and `c ∈ Pic(A)`. For every field extension
`K/k`, the map `φ_c : A(K) → Pic(A_K)`, `a ↦ τ_a^* c - c`, is a group homomorphism:
`φ_c(a + b) = φ_c(a) + φ_c(b)`, equivalently `τ_{a+b}^* c + c = τ_a^* c + τ_b^* c`.

## Main results

* `Faltings.AbelianVariety.phiMap_mul`: `φ_c(a * b) = φ_c(a) + φ_c(b)`.
* `Faltings.AbelianVariety.schemePullbackClass_cube`: the theorem of the cube on `Pic(B)` for
  three morphisms `f g h : B ⟶ A`.
* `Faltings.AbelianVariety.schemePullbackClass_comp_spec_field`: a class pulled back along a
  morphism factoring through `Spec K`, `K` a field, vanishes.

## Implementation notes

A `K`-point of `A` is a morphism `Spec K ⟶ A` in `Over (Spec k)`; these form a group under
the group object structure of `A` (the instance `CategoryTheory.Hom.group`, scoped in
`CategoryTheory.MonObj`),
which is written multiplicatively, while `Pic` is written additively. The statement is made
for an arbitrary field extension `K/k`; the case `K = k̄` is the classical one.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, v2.00 (2008), Ch. I, Theorem 5.5, Remark 5.6.
-/

namespace Faltings.AbelianVariety

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

/-- The pull-back of a class `x` along a morphism of schemes is the pull-back class of a chosen
representative of `x`. -/
public lemma schemePullbackClass_eq_pullbackPicardClass {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (x : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass φ x =
      Stacks.SheafOfModules.pullbackPicardClass φ
        (Stacks.Picard.picardRepresentative Y.toRingedSpace x).obj
        (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property := by
  conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x]
  exact Stacks.Picard.pullbackClass_classOf _ _ _

/-- The theorem of the cube for a triple `(f, g, h)` of morphisms `B ⟶ A`, on `Pic(B)`. -/
public lemma schemePullbackClass_cube {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (x : Stacks.Picard.ofScheme A.left) {B : Over (Spec (CommRingCat.of k))} (f g h : B ⟶ A) :
    Stacks.Picard.schemePullbackClass (f * g * h).left x +
        Stacks.Picard.schemePullbackClass f.left x +
        Stacks.Picard.schemePullbackClass g.left x +
        Stacks.Picard.schemePullbackClass h.left x =
      Stacks.Picard.schemePullbackClass (f * g).left x +
        Stacks.Picard.schemePullbackClass (f * h).left x +
        Stacks.Picard.schemePullbackClass (g * h).left x := by
  simp only [schemePullbackClass_eq_pullbackPicardClass]
  exact Stacks.Groupoids.pullbackPicardClass_cubeRelation A
    (Stacks.Groupoids.hasTheoremOfTheCube k A) _ _ f g h

/-- The pull-back of a class along a morphism factoring through the spectrum of a field
vanishes, since `Pic(Spec K) = 0`. -/
public lemma schemePullbackClass_comp_spec_field {K : Type u} [Field K] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Spec (CommRingCat.of K) ⟶ Y)
    (x : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass (p ≫ q) x = 0 := by
  have := AlgebraicGeometry.subsingleton_picardGroup_spec_field K
  rw [← Stacks.Picard.schemePullbackClass_comp,
    Subsingleton.elim (Stacks.Picard.schemePullbackClass q x) 0]
  exact map_zero (Stacks.Picard.schemePullbackClassHom p)

/-- The theorem of the square on `A ⊗ P`, for points `a b : P ⟶ A` such that `c` pulls back
trivially along every `snd A P ≫ x`: writing `τ_x = fst A P * (snd A P ≫ x)`, one has
`τ_{a * b}^* c - c = (τ_a^* c - c) + (τ_b^* c - c)` on `Pic(A ⊗ P)`. -/
private lemma schemePullbackClass_fst_mul_snd_comp_mul {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : Stacks.Picard.ofScheme A.left) {P : Over (Spec (CommRingCat.of k))}
    (h0 : ∀ x : P ⟶ A, Stacks.Picard.schemePullbackClass (snd A P ≫ x).left c = 0)
    (a b : P ⟶ A) :
    Stacks.Picard.schemePullbackClass (fst A P * (snd A P ≫ (a * b))).left c -
        Stacks.Picard.schemePullbackClass (fst A P).left c =
      (Stacks.Picard.schemePullbackClass (fst A P * (snd A P ≫ a)).left c -
          Stacks.Picard.schemePullbackClass (fst A P).left c) +
        (Stacks.Picard.schemePullbackClass (fst A P * (snd A P ≫ b)).left c -
          Stacks.Picard.schemePullbackClass (fst A P).left c) := by
  have h := schemePullbackClass_cube A c (fst A P) (snd A P ≫ a) (snd A P ≫ b)
  rw [h0, h0, ← comp_mul, h0, add_zero, add_zero, add_zero] at h
  rw [comp_mul, ← _root_.mul_assoc, sub_add_sub_comm, ← h]
  exact (add_sub_add_right_eq_sub _ _ _).symm

variable {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  [IsAbelianVariety k A] {K : Type u} [Field K] [Algebra k K]

/-- **Theorem of the square.** For an abelian variety `A` over `k` and `c ∈ Pic(A)`, the map
`a ↦ φ_c(a) = τ_a^* c - c` from `K`-points of `A` to `Pic(A_K)` is additive:
`φ_c(a * b) = φ_c(a) + φ_c(b)`, the product being the group law of `A(K)`. -/
@[faltings "lem_nt_theorem_of_square"]
public theorem phiMap_mul (c : Stacks.Picard.ofScheme A.left)
    (a b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A c (a * b) = phiMap A c a + phiMap A c b := by
  simp only [phiMap, ← Hom.mul_def]
  exact schemePullbackClass_fst_mul_snd_comp_mul A c
    (fun x => by rw [Over.comp_left]; exact schemePullbackClass_comp_spec_field _ _ c) a b

end Faltings.AbelianVariety


/-!
# `φ_c` takes values in `Pic⁰`

Let `A` be an abelian variety over a field `k`, `c ∈ Pic(A)`, and `K/k` a field extension.
For every point `a ∈ A(K)` the class `φ_c(a) = τ_a^* c - c ∈ Pic(A_K)` lies in the subgroup
`Pic⁰(A_K)` of the base change `A_K`, an abelian variety over `K`: that is,
`μ^* φ_c(a) = pr₁^* φ_c(a) + pr₂^* φ_c(a)` on `A_K × A_K`.

## Main results

* `Faltings.AbelianVariety.phiMap_mem_picZero`: `φ_c(a) ∈ Pic⁰(A_K)`.

## Implementation notes

The base change `A_K` is `(Over.pullback (Spec K → Spec k)).obj A`, a group scheme over
`Spec K` (`AlgebraicGeometry.grpObjPullbackObj`) and an abelian variety over `K`
(`AlgebraicGeometry.isAbelianVariety_pullbackObj`). Its underlying scheme is, by definition,
the underlying scheme of `A ⊗ Spec K` in `Over (Spec k)`, where `Faltings.AbelianVariety.phiMap`
takes its values, so the membership is stated with no transport. The statement is made for an
arbitrary field extension `K/k`; the classical case is `K = k̄`.

Since `Faltings.picZero` is defined by the identity `μ^* x = pr₁^* x + pr₂^* x` rather than by
translation invariance, the proof does not go through translation invariance (which would need
the seesaw principle). A `T`-point of `A_K` is turned into a `T`-point of `A` over `k` by the
adjunction `Over.map π ⊣ Over.pullback π`, which respects the group laws; the identity on
`A_K × A_K` is then the theorem of the cube for the three points `pr₁`, `pr₂` and the constant
point `a` of `A` with values in `A_K × A_K`, the term pulled back along `a` vanishing because
`Pic(Spec K) = 0`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, v2.00 (2008), Ch. I, Lemma 8.8, Remark 8.5.
-/

namespace Faltings.AbelianVariety

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

/-- Pull-back of classes commutes with subtraction. -/
public lemma schemePullbackClass_sub {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x y : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.schemePullbackClass f (x - y) =
      Stacks.Picard.schemePullbackClass f x - Stacks.Picard.schemePullbackClass f y :=
  map_sub (Stacks.Picard.schemePullbackClassHom f) x y

/-- The theorem of the square on `Pic(B)` for points `f g h : B ⟶ A` such that `c` pulls back
trivially along `h`: `(f g h)^* c - (f g)^* c = ((f h)^* c - f^* c) + ((g h)^* c - g^* c)`. -/
private lemma schemePullbackClass_mul_mul_sub {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (c : Stacks.Picard.ofScheme A.left) {B : Over (Spec (CommRingCat.of k))} (f g h : B ⟶ A)
    (h0 : Stacks.Picard.schemePullbackClass h.left c = 0) :
    Stacks.Picard.schemePullbackClass (f * g * h).left c -
        Stacks.Picard.schemePullbackClass (f * g).left c =
      (Stacks.Picard.schemePullbackClass (f * h).left c -
          Stacks.Picard.schemePullbackClass f.left c) +
        (Stacks.Picard.schemePullbackClass (g * h).left c -
          Stacks.Picard.schemePullbackClass g.left c) := by
  have hc := schemePullbackClass_cube A c f g h
  rw [h0, add_zero] at hc
  rw [sub_add_sub_comm, sub_eq_sub_iff_add_eq_add, ← add_assoc, hc]
  exact add_rotate _ _ _

section BaseChange

variable {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  {K : Type u} [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The pull-back of `φ_c(a)` along a `T`-point `u` of `A_K` is `(P u * a)^* c - (P u)^* c`. -/
private lemma schemePullbackClass_phiMap {T : Over (Spec (CommRingCat.of K))}
    (c : Stacks.Picard.ofScheme A.left) (a : Over.mk π ⟶ A)
    (u : T ⟶ (Over.pullback π).obj A) :
    Stacks.Picard.schemePullbackClass u.left (phiMap A c a) =
      Stacks.Picard.schemePullbackClass
          (P A u * ((Over.homMk T.hom : (Over.map π).obj T ⟶ Over.mk π) ≫ a)).left c -
        Stacks.Picard.schemePullbackClass (P A u).left c := by
  rw [phiMap, schemePullbackClass_sub,
    Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    ← lift_P_left A u, ← Over.comp_left, ← Over.comp_left, Hom.mul_def]
  congr 3
  · simp only [comp_lift_assoc, lift_fst, lift_snd_assoc]
  · simp

end BaseChange

variable {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  [IsAbelianVariety k A] {K : Type u} [Field K] [Algebra k K]

/-- For an abelian variety `A` over `k`, `c ∈ Pic(A)` and a point `a ∈ A(K)` over a field
extension `K/k`, the class `φ_c(a) = τ_a^* c - c` lies in `Pic⁰(A_K)`, the base change
`A_K` being an abelian variety over `K`. -/
@[faltings "lem_nt_phi_in_pic0"]
public theorem phiMap_mem_picZero (c : Stacks.Picard.ofScheme A.left)
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A c a ∈
      picZero K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) := by
  set AK := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A
  change Stacks.Picard.schemePullbackClass μ[AK].left (phiMap A c a) =
    Stacks.Picard.schemePullbackClass (fst AK AK).left (phiMap A c a) +
      Stacks.Picard.schemePullbackClass (snd AK AK).left (phiMap A c a)
  rw [schemePullbackClass_phiMap, schemePullbackClass_phiMap, schemePullbackClass_phiMap,
    MonObj.mul_eq_mul, P_mul]
  exact schemePullbackClass_mul_mul_sub A c _ _ _
    (by rw [Over.comp_left]; exact schemePullbackClass_comp_spec_field _ _ c)

end Faltings.AbelianVariety


/-!
# `φ_{c⁻} = φ_c`

Let `A` be an abelian variety over a field `k`, `c ∈ Pic(A)`, and let `c⁻ = [-1]^* c` be the
pull-back of `c` along the inversion `[-1] : A → A`. Then `c` and `c⁻` have the same map `φ`:
`φ_{c⁻}(a) = φ_c(a)` in `Pic(A_K)` for every field extension `K/k` and every `a ∈ A(K)`.

## Main results

* `Faltings.AbelianVariety.phiMap_schemePullbackClass_inv`: `φ_{[-1]^* c} = φ_c`.

## Implementation notes

The points are taken over an arbitrary field extension `K/k`; the source's statement on
`A(k̄)` is the case `K := k̄`. The inversion of the group object `A` is `ι[A] : A ⟶ A`, and
`c⁻` is `Stacks.Picard.schemePullbackClass ι[A].left c`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, v2.00 (2008), Ch. III, proof of Theorem 6.6.
* [MumAV] D. Mumford, *Abelian Varieties*, §8.
-/

@[expose] public section

namespace Faltings.AbelianVariety

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

variable {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  [IsAbelianVariety k A]

section Helpers

variable {K : Type u} [Field K] [Algebra k K]

local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The inversion of the base change `A_K` is, on underlying schemes, the map
`(x, t) ↦ (x⁻¹, t)` of `A ⊗ Spec K`. -/
private lemma inv_pullbackObj_left :
    (ι[(Over.pullback π).obj A]).left =
      (lift (fst A (Over.mk π) ≫ ι[A]) (snd A (Over.mk π))).left := by
  rw [show ι[(Over.pullback π).obj A] = (Over.pullback π).map ι[A] from Functor.obj.ι_def]
  apply pullback.hom_ext <;> simp

/-- `φ` is odd: `φ_c(a⁻¹) = -φ_c(a)`. -/
private lemma phiMap_inv (c : Stacks.Picard.ofScheme A.left) (a : Over.mk π ⟶ A) :
    phiMap A c a⁻¹ = -phiMap A c a := by
  have h₁ := phiMap_mul A c (1 : Over.mk π ⟶ A) 1
  have h₂ := phiMap_mul A c a⁻¹ a
  rw [_root_.mul_one, left_eq_add] at h₁
  rw [_root_.inv_mul_cancel, h₁] at h₂
  exact eq_neg_of_add_eq_zero_left h₂.symm

/-- Pulling `φ_c(a⁻¹)` back along the inversion of `A_K` gives `φ_{c⁻}(a)`, where
`c⁻ = [-1]^* c`: the translation `x ↦ x + a⁻¹` conjugated by `[-1]` is `x ↦ x + a`. -/
private lemma schemePullbackClass_inv_phiMap_inv (c : Stacks.Picard.ofScheme A.left)
    (a : Over.mk π ⟶ A) :
    Stacks.Picard.schemePullbackClass (ι[(Over.pullback π).obj A]).left (phiMap A c a⁻¹) =
      phiMap A (Stacks.Picard.schemePullbackClass ι[A].left c) a := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  rw [inv_pullbackObj_left]
  simp only [phiMap, schemePullbackClass_sub, Stacks.Picard.schemePullbackClass_comp,
    ← Over.comp_left]
  congr 3
  · rw [← Hom.mul_def, ← Hom.mul_def, ← Hom.inv_def, MonObj.comp_mul, lift_fst,
      lift_snd_assoc, ← Hom.inv_def, GrpObj.comp_inv, _root_.mul_inv]
  · rw [lift_fst]

end Helpers

/-- For an abelian variety `A` over `k` and `c ∈ Pic(A)`, the class `c⁻ = [-1]^* c` has the
same map `φ` as `c`: `φ_{c⁻}(a) = φ_c(a)` for every `a ∈ A(K)` over a field extension `K/k`. -/
@[faltings "lem_nt_phi_inverse_class"]
theorem phiMap_schemePullbackClass_inv (c : Stacks.Picard.ofScheme A.left)
    {K : Type u} [Field K] [Algebra k K]
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A (Stacks.Picard.schemePullbackClass ι[A].left c) a = phiMap A c a := by
  rw [← schemePullbackClass_inv_phiMap_inv]
  refine (schemePullbackClassHom_inv_of_mem_picZero K _ (phiMap_mem_picZero A c a⁻¹)).trans ?_
  rw [phiMap_inv, neg_neg]

end Faltings.AbelianVariety


/-!
# `φ_c` is unchanged by translating `c`

Let `A` be an abelian variety over a field `k`, `c ∈ Pic(A)` and `a ∈ A(k)`. Then the class
`τ_a^* c` obtained by pulling `c` back along translation by `a` has the same map `φ`:
`φ_{τ_a^* c}(b) = φ_c(b)` in `Pic(A_K)` for every field extension `K/k` and every `b ∈ A(K)`.

## Main results

* `Faltings.AbelianVariety.phiMap_schemePullbackClass_translate`: `φ_{τ_a^* c} = φ_c`.

## Implementation notes

The base field `k` is arbitrary; the source's statement over `k̄` (with `c ∈ Pic(A_{k̄})`
and `a ∈ A(k̄)`) is the case of the abelian variety `A_{k̄}` over the field `k̄`. A
`k`-point of `A` is a morphism `𝟙_ (Over (Spec k)) ⟶ A`, and translation by `a` is the
morphism `lift (𝟙 A) (toUnit A ≫ a) ≫ μ : A ⟶ A`, `x ↦ x + a`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, v2.00 (2008), Ch. III, proof of Theorem 6.6.
* [MumAV] D. Mumford, *Abelian Varieties*, §8.
-/

@[expose] public section

namespace Faltings.AbelianVariety

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

variable (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]

/-- The map `φ` of a translate: `φ_{τ_a^* c}(b) = φ_c(b + a) - φ_c(a)`, with the `k`-point `a`
read as a `K`-point. Only the associativity of the group law enters. -/
private lemma phiMap_translate_eq_sub (c : Stacks.Picard.ofScheme A.left)
    (a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ A) {K : Type u} [Field K] [Algebra k K]
    (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A (Stacks.Picard.schemePullbackClass (lift (𝟙 A) (toUnit A ≫ a) ≫ μ).left c) b =
      phiMap A c (b * (toUnit _ ≫ a)) - phiMap A c (toUnit _ ≫ a) := by
  simp only [phiMap, Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left,
    Category.comp_id, ← Hom.mul_def, comp_mul, _root_.mul_assoc,
    ← Category.assoc, comp_toUnit]
  exact (sub_sub_sub_cancel_right _ _ _).symm

/-- For an abelian variety `A` over `k`, a class `c ∈ Pic(A)` and a point `a ∈ A(k)`, the
translate `τ_a^* c` of `c` has the same map `φ` as `c`: `φ_{τ_a^* c}(b) = φ_c(b)` for every
`b ∈ A(K)` over a field extension `K/k`. By the theorem of the square,
`φ_{τ_a^* c}(b) = φ_c(b + a) - φ_c(a) = φ_c(b)`. -/
@[faltings "lem_nt_phi_translate_invariant"]
theorem phiMap_schemePullbackClass_translate (c : Stacks.Picard.ofScheme A.left)
    (a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ A) {K : Type u} [Field K] [Algebra k K]
    (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A (Stacks.Picard.schemePullbackClass (lift (𝟙 A) (toUnit A ≫ a) ≫ μ).left c) b =
      phiMap A c b := by
  rw [phiMap_translate_eq_sub, phiMap_mul, add_sub_cancel_right]

end Faltings.AbelianVariety
