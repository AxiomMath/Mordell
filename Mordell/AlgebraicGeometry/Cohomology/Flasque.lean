module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived

/-!
# Flasque sheaves are acyclic

A sheaf of abelian groups `G` on a topological space `X` is flasque when every restriction map
`G(U) → G(V)`, `V ⊆ U`, is surjective (an epimorphism of abelian groups). Such a sheaf has no
higher cohomology: `H^n(X, G) = 0` for every `n > 0`.

## Main results

* `Faltings.subsingleton_H_of_isFlasque`: the sheaf cohomology `CategoryTheory.Sheaf.H G n` of a
  flasque abelian sheaf vanishes for `0 < n`.

## Implementation notes

The proof is by dimension shifting. An injective abelian sheaf is flasque
(`Stacks.Cohomology.isFlasque_of_injective`). Embedding a flasque `G` into an
injective `I`, the cokernel `Q` is flasque and `Γ(X, I) → Γ(X, Q)` is surjective; the long
exact `Ext`-sequence of `0 → G → I → Q → 0` then gives `H^{n+1}(X, G) = 0` from
`H^n(X, Q) = 0` for `n > 0`, and from the surjectivity on global sections for `n = 0`.

The cohomology of a module over a ringed space `(X, 𝒪_X)` agrees with the cohomology of its
underlying sheaf of abelian groups, and flasqueness only concerns the underlying sheaf; so the
statement is made for an arbitrary abelian sheaf on `X`, which covers every `𝒪_X`-module.
Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext` groups out of the constant sheaf `ℤ`
in the category of abelian sheaves.

## References

* [Stacks, Tag 09SY]
* [Stacks, Tag 01EA]
-/

public section

namespace Faltings

universe u w

open CategoryTheory Limits Opposite TopologicalSpace TopCat CategoryTheory.Abelian

section Vanishing

variable {X : TopCat.{u}} [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- A flasque abelian sheaf has vanishing cohomology in degree `n + 1`, by induction on `n`
along an embedding into an injective sheaf. -/
private theorem subsingleton_H_succ_of_isFlasque (n : ℕ) :
    ∀ (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Sheaf.IsFlasque (X := X) G → Subsingleton (G.H.{w} (n + 1)) := by
  induction n with
  | zero => ?_
  | succ k ih => ?_
  all_goals
    intro G hG
    let S := ShortComplex.cokernelSequence (Injective.ι G)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := inferInstanceAs (Mono (Injective.ι G)) }
    have hI : TopCat.Sheaf.IsFlasque (X := X) S.X₂ :=
      @Stacks.Cohomology.isFlasque_of_injective X (Injective.under G)
        (inferInstanceAs (Injective (Injective.under G)))
    have h₁ : TopCat.Sheaf.IsFlasque (X := X) S.X₁ := hG
    have hQ : TopCat.Sheaf.IsFlasque (X := X) S.X₃ :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (S := S) hS
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under G))
    have h₀ : x.comp (Ext.mk₀ S.f) (add_zero _) = 0 := Ext.eq_zero_of_injective _
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x h₀ rfl
  · -- degree zero of the quotient: global sections of `I` surject onto those of `Q`
    have hT : IsTerminal (⊤ : Opens X) := isTerminalTop
    have hepi : Epi (S.g.hom.app (op ⊤)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact (S := S) (U := ⊤) hS
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hepi
      (Sheaf.H.equiv₀ S.X₃ hT x₃)
    have hx : Sheaf.H.map S.g 0 ((Sheaf.H.equiv₀ S.X₂ hT).symm t) = x₃ := by
      rw [Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
    rw [← hx, Sheaf.H.map_apply]
    simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]
    rfl
  · have := ih S.X₃ hQ
    rw [Subsingleton.elim x₃ 0, Ext.zero_comp]
    rfl

end Vanishing

/-- A flasque sheaf of abelian groups on a topological space has vanishing cohomology in every
positive degree. -/
@[faltings "lem_ff_flasque_acyclic"]
theorem subsingleton_H_of_isFlasque {X : TopCat.{u}} (G : Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [Presheaf.IsFlasque G.obj] {n : ℕ} (hn : 0 < n) : Subsingleton (G.H n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact subsingleton_H_succ_of_isFlasque k G ‹_›

end Faltings

end
