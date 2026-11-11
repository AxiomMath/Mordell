module
public import Mathlib
public import Mordell.Attr

/-!
# The field norm as a determinant over a free order

Let `S` be an `R`-algebra which is free of finite rank as an `R`-module, and let `K` and `L` be
fraction fields of `R` and `S`, with `L` a `K`-algebra compatibly with `R → S`. Then a basis of
`S` over `R` is a basis of `L` over `K`, so for `f : S` the field norm
`Algebra.norm K (algebraMap S L f)` is the image in `K` of the determinant over `R` of the
`R`-linear map `S → S`, `u ↦ f * u`.

This is applied with `S = 𝒪(W)` the coordinate ring of the affine open `W = U × U` of `C × C`,
`R = k[ξ_a, ξ'_b]`, `K = k(ξ_a, ξ'_b)` and `L = k(C × C)`.

## Main results

* `Faltings.norm_algebraMap_eq_det_mulLeft`: `Norm_{L/K} f = det_R (u ↦ f u)`.

## Implementation notes

Since `S` is a domain finite over `R`, `L` is the localization of `S` at the image of `R⁰`, so
`Algebra.norm_localization` identifies `Norm_{L/K} f` with the image of `Norm_{S/R} f`, which is
the determinant of multiplication by `f`. Its side conditions are that `R → S` is injective,
because `R → K → L = R → S → L` is, and that `S` is a domain, because it embeds in `L`.

## References

* [Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9.
* [Bourbaki, *Algèbre*, Chapitre III, §9][bourbaki_algebra]
-/

@[expose] public section

namespace Faltings

open scoped nonZeroDivisors

/-- If `S` is a free `R`-algebra of finite rank with fraction field `L`, and `K` is a fraction
field of `R` with `L` a `K`-algebra compatibly, then the field norm from `L` to `K` of `f : S` is
the image of the determinant over `R` of multiplication by `f` on `S`. -/
@[faltings "lem_bvr_norm_facts"]
public theorem norm_algebraMap_eq_det_mulLeft {R S K L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Free R S] [Module.Finite R S] (f : S) :
    Algebra.norm K (algebraMap S L f) = algebraMap R K (LinearMap.det (LinearMap.mulLeft R f)) := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr <|
    .of_comp (f := algebraMap S L) <| by
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : NoZeroDivisors S :=
    (IsFractionRing.injective S L).noZeroDivisors _ (map_zero _) (map_mul _)
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  exact Algebra.norm_localization (Rₘ := K) (Sₘ := L) R R⁰ f

end Faltings

end
