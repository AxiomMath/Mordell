module

public import Mathlib
public import Mordell.Attr

/-!
# The image of a finitely generated abelian group in its real span is a lattice

Let `Γ` be a finitely generated abelian group and `f : Γ →ₗ[ℤ] V` a base change of `Γ` to `ℝ`
(so `V ≃ Γ ⊗[ℤ] ℝ` and `f x = x ⊗ 1`), where `V` carries a norm. Then the image of `f` is a
lattice in `V`: it is discrete and spans `V` over `ℝ`. Moreover the kernel of `f` is exactly the
torsion subgroup of `Γ`, so `f` induces an isomorphism `Γ ⧸ torsion ≃ range f`
(`LinearMap.quotKerEquivRange`).

## Main results

* `Faltings.discreteTopology_range_and_span_eq_top_and_ker_eq_torsion_of_isBaseChange`

## Implementation notes

Choose a `ℤ`-basis `b` of the free module `Γ ⧸ torsion ℤ Γ` and lifts `g i ∈ Γ` of `b i`. The
coordinate functionals of `b` extend along the base change, so `f ∘ g` is `ℝ`-linearly
independent; it spans `V` and its `ℤ`-span is the range of `f`. Hence `f ∘ g` is an `ℝ`-basis of
`V` whose `ℤ`-span is `range f`, which gives discreteness, and its independence gives
`ker f = torsion ℤ Γ`.

## References

* [Wu], Lemma 2.6; [B], Section 5.
-/

@[expose] public section

namespace Faltings

open Submodule

section

variable {Γ V : Type*} [AddCommGroup Γ] [AddCommGroup V] [Module ℝ V] {f : Γ →ₗ[ℤ] V}

/-- A `ℤ`-linear map into a real vector space kills torsion. -/
private lemma map_eq_zero_of_mem_torsion {x : Γ} (hx : x ∈ torsion ℤ Γ) : f x = 0 := by
  obtain ⟨a, ha⟩ := (mem_torsion_iff x).1 hx
  have : ((a : ℤ) : ℝ) • f x = 0 := by
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul, Submonoid.smul_def] at *
    simp [ha]
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast nonZeroDivisors.coe_ne_zero a)

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ (Γ ⧸ torsion ℤ Γ)) {g : ι → Γ}
  (hg : ∀ i, (torsion ℤ Γ).mkQ (g i) = b i)

include hg

/-- `f x` is the combination of the `f (g j)` with the coordinates of `x` modulo torsion. -/
private lemma map_eq_sum_repr (x : Γ) :
    f x = ∑ j, b.repr ((torsion ℤ Γ).mkQ x) j • f (g j) := by
  have hmem : x - ∑ j, b.repr ((torsion ℤ Γ).mkQ x) j • g j ∈ torsion ℤ Γ := by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply]
    simp only [map_sub, map_sum, map_zsmul, hg, b.sum_repr, sub_self]
  simpa [sub_eq_zero] using map_eq_zero_of_mem_torsion (f := f) hmem

/-- The heart of the argument: the images of the lifts are `ℝ`-linearly independent, as the
coordinate functionals of `b` extend along the base change. -/
private lemma linearIndependent_comp (hf : IsBaseChange ℝ f) : LinearIndependent ℝ (f ∘ g) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have := congrArg (hf.lift ((Algebra.linearMap ℤ ℝ) ∘ₗ b.coord i ∘ₗ (torsion ℤ Γ).mkQ)) ha
  simpa [map_sum, IsBaseChange.lift_eq, hg, Finsupp.single_apply] using this

/-- The images of the lifts span `V` over `ℝ`. -/
private lemma span_comp_eq_top (hf : IsBaseChange ℝ f) : span ℝ (Set.range (f ∘ g)) = ⊤ := by
  refine eq_top_iff.2 fun v _ =>
    hf.inductionOn v (motive := fun v => v ∈ span ℝ (Set.range (f ∘ g))) (fun x => ?_)
      (fun s _ hn => smul_mem _ s hn) (fun _ _ => add_mem)
  rw [map_eq_sum_repr b hg x]
  exact sum_mem fun j _ => by
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- The range of `f` is the `ℤ`-span of the images of the lifts. -/
private lemma range_eq_span_comp : LinearMap.range f = span ℤ (Set.range (f ∘ g)) := by
  refine le_antisymm ?_ (span_le.2 <| Set.range_comp_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  rw [map_eq_sum_repr b hg x]
  exact sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- An element of `ker f` has zero coordinates modulo torsion, so it is torsion. -/
private lemma ker_eq_torsion (hli : LinearIndependent ℝ (f ∘ g)) :
    LinearMap.ker f = torsion ℤ Γ := by
  refine le_antisymm (fun x hx => ?_) fun x => map_eq_zero_of_mem_torsion
  rw [← Quotient.mk_eq_zero, ← mkQ_apply, ← b.repr.map_eq_zero_iff]
  ext j
  rw [LinearMap.mem_ker, map_eq_sum_repr b hg x] at hx
  simp_rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  simpa using Fintype.linearIndependent_iff.1 hli _ hx j

end

/-- The image of a finitely generated abelian group `Γ` in its base change `V` to `ℝ` is discrete
and spans `V`, and the kernel of `Γ → V` is the torsion subgroup of `Γ`. -/
@[faltings "lem_nt_lattice_image"]
theorem discreteTopology_range_and_span_eq_top_and_ker_eq_torsion_of_isBaseChange
    {Γ V : Type*} [AddCommGroup Γ] [AddGroup.FG Γ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Γ →ₗ[ℤ] V} (hf : IsBaseChange ℝ f) :
    DiscreteTopology (LinearMap.range f) ∧
      Submodule.span ℝ (LinearMap.range f : Set V) = ⊤ ∧
      LinearMap.ker f = Submodule.torsion ℤ Γ := by
  let b := Module.Free.chooseBasis ℤ (Γ ⧸ torsion ℤ Γ)
  choose g hg using fun i => (torsion ℤ Γ).mkQ_surjective (b i)
  have hli := linearIndependent_comp b hg hf
  refine ⟨?_, eq_top_iff.2 ?_, ker_eq_torsion b hg hli⟩
  · rw [range_eq_span_comp b hg, ← Module.Basis.coe_mk hli (span_comp_eq_top b hg hf).ge]
    infer_instance
  · rw [← span_comp_eq_top b hg hf]
    exact span_mono (Set.range_comp_subset_range _ _)

end Faltings
