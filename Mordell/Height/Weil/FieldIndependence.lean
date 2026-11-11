module

public import Mordell.Height.Weil.LocalHeight
public import Mordell.NumberField.NormalizedAbv.FieldExtension
public import Mordell.NumberField.Place.LiesOver

/-!
# Independence of the sum of local heights from the field

Let `K ⊆ L` be number fields and `x ∈ K^{n+1} \ {0}`. Because the absolute values
`Faltings.NumberFieldPlace.normalizedAbv` are normalized relative to `ℚ`, the sum of the local
heights of `x` does not depend on the number field in which its coordinates are viewed:
`S_L(x) = S_K(x)`.

## Main results

* `Faltings.sumLocalHeight_algebraMap`: `S_L(x) = S_K(x)` for `x ≠ 0`.

## Implementation notes

The inclusion `K ⊆ L` is an arbitrary `[Algebra K L]` (any field embedding of number fields),
and `x` viewed in `L^{n+1}` is `algebraMap K L ∘ x`. The index type is an arbitrary finite type
`ι` rather than `Fin (n + 1)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022], Sec. 1.2.
-/

@[expose] public section

namespace Faltings

open Function NumberField

/-- A finitely supported sum over `β` can be taken fibrewise along a relation `p` in which every
`b : β` is related to exactly one `a : α`. -/
private theorem finsum_finsum_subtype_of_existsUnique {α β M : Type*} [AddCommMonoid M]
    {p : β → α → Prop} (hp : ∀ b, ∃! a, p b a) {f : β → M} (hf : (support f).Finite) :
    ∑ᶠ a, ∑ᶠ b : {b // p b a}, f b = ∑ᶠ b, f b := by
  classical
  choose g hg huniq using hp
  have hpg (b : β) (a : α) : p b a ↔ g b = a := ⟨fun h => (huniq b a h).symm, (· ▸ hg b)⟩
  have inner (a : α) : ∑ᶠ b : {b // p b a}, f b = ∑ b ∈ hf.toFinset with g b = a, f b := by
    rw [finsum_subtype_eq_finsum_cond (p := (p · a)), Finset.sum_filter]
    simp_rw [finsum_eq_if, hpg]
    exact finsum_eq_sum_of_support_subset _ fun b hb => by by_cases h : g b = a <;> simp_all
  simp_rw [inner]
  rw [finsum_eq_sum_of_support_subset _ (s := hf.toFinset.image g) fun a ha => ?_,
    finsum_eq_sum_of_support_subset _ (s := hf.toFinset) (by simp),
    Finset.sum_fiberwise_of_maps_to fun b hb => Finset.mem_image_of_mem g hb]
  obtain ⟨b, hb, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  rw [Finset.mem_filter] at hb
  exact hb.2 ▸ Finset.mem_image_of_mem g hb.1

/-- The sum of the local heights `Faltings.sumLocalHeight` is independent of the number field:
for number fields `K ⊆ L` and a nonzero vector `x : ι → K`, `S_L(x) = S_K(x)`.

Each place `w` of `L` lies over exactly one place `v` of `K`, so `S_L(x)` regroups as a sum over
`v` of the sums over `w ∣ v`; each inner sum is the local height of `x` at `v`. -/
@[faltings "lem_ht_height_field_independent"]
theorem sumLocalHeight_algebraMap {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    sumLocalHeight (algebraMap K L ∘ x) = sumLocalHeight x := by
  have hxL : algebraMap K L ∘ x ≠ 0 := by simpa [funext_iff] using hx
  rw [sumLocalHeight, sumLocalHeight, ← finsum_finsum_subtype_of_existsUnique
    (NumberFieldPlace.existsUnique_liesOver (k := K)) (NumberFieldPlace.finite_support_localHeight hxL)]
  exact finsum_congr fun v => (NumberFieldPlace.log_iSup_normalizedAbv_eq_finsum_liesOver v x hx).symm

end Faltings
