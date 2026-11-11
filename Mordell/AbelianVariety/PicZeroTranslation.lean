module

public import Mordell.AbelianVariety.PhiMap
public import Mordell.AbelianVariety.PicZero
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankDisjointCover

/-!
# Classes in `Pic⁰` are translation invariant

Let `A` be an abelian variety over a field `k` and `M ∈ Pic⁰(A)`. For every field extension
`K/k` and every point `a ∈ A(K)`, the class `φ_M(a) = τ_a^* M - M` in `Pic(A_K)` vanishes,
i.e. `τ_a^* M = M` on `A_K`.

## Main results

* `Faltings.AbelianVariety.phiMap_eq_zero_of_mem_picZero`: `φ_M(a) = 0` for `M ∈ Pic⁰(A)`.

## Implementation notes

The source states the result for `M ∈ Pic⁰(A_{\bar k})` and `a ∈ A(\bar k)`. Here it is
stated for an abelian variety over an arbitrary field `k` and points with values in an
arbitrary field extension `K/k`; the source's form is the case where the base field is `\bar k`,
the abelian variety is `A_{\bar k}` and `K = \bar k`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Theorem 5.5, Remark 8.5.
-/

@[expose] public section

namespace Faltings.AbelianVariety

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

/-- For `M ∈ Pic⁰(A)` and any two morphisms `α, β : V → A` over `k`, with no hypothesis on `V`,
`(α + β)^* M = α^* M + β^* M`: the defining identity of `Pic⁰` pulled back along `(α, β)`. -/
private lemma pullback_lift_mul_of_mem_picZero {k : Type u} [Field k]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsAbelianVariety k A]
    {M : Stacks.Picard.ofScheme A.left} (hM : M ∈ picZero k A)
    {V : Over (Spec (CommRingCat.of k))} (α β : V ⟶ A) :
    Stacks.Picard.schemePullbackClassHom (lift α β ≫ μ[A]).left M =
      Stacks.Picard.schemePullbackClassHom α.left M +
        Stacks.Picard.schemePullbackClassHom β.left M := by
  have h := congrArg (Stacks.Picard.schemePullbackClassHom (lift α β).left) hM
  rwa [AddMonoidHom.add_apply, map_add, schemePullbackClassHom_comp_left,
    schemePullbackClassHom_comp_left, schemePullbackClassHom_comp_left, lift_fst, lift_snd] at h

/-- Every Picard class on the spectrum of a field is trivial. -/
private lemma eq_zero_of_spec_field {K : Type u} [Field K]
    (x : Stacks.Picard.ofScheme (Spec (CommRingCat.of K))) : x = 0 :=
  haveI : DiscreteTopology (Spec (CommRingCat.of K)) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum K))
  (Stacks.Picard.subsingleton_ofScheme_of_discreteTopology _).elim x 0

/-- A class `M ∈ Pic⁰(A)` of an abelian variety `A` over `k` is translation invariant: for every
field extension `K/k` and every point `a ∈ A(K)`, `φ_M(a) = τ_a^* M - M = 0` in `Pic(A_K)`. -/
@[faltings "lem_nt_pic0_translation_invariant"]
theorem phiMap_eq_zero_of_mem_picZero {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsAbelianVariety k A] {K : Type u} [Field K] [Algebra k K]
    {M : Stacks.Picard.ofScheme A.left} (hM : M ∈ picZero k A)
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    phiMap A M a = 0 := by
  have h := pullback_lift_mul_of_mem_picZero hM (fst A _) (snd A _ ≫ a)
  rw [← schemePullbackClassHom_comp_left (snd A _) a,
    eq_zero_of_spec_field (K := K) (Stacks.Picard.schemePullbackClassHom a.left M), map_zero,
    add_zero] at h
  exact sub_eq_zero.2 h

end Faltings.AbelianVariety
