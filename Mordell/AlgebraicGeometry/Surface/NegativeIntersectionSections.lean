module

public import Mordell.AlgebraicGeometry.Surface.AmplePositivity

/-!
# Invertible modules of negative degree have no global sections

Let `X` be an integral proper scheme of dimension `2` over a field `k`, let `𝓗` be an ample
invertible `𝓞_X`-module and let `𝓜` be an invertible `𝓞_X`-module with `(𝓗 · 𝓜) < 0`.
Then `H⁰(X, 𝓜) = Γ(X, 𝓜) = 0`: a nonzero global section would be regular, so `𝓜 ≅ 𝓞_X(E)`
for an effective Cartier divisor `E`, and then `(𝓗 · 𝓜) ≥ 0`.

## Main results

* `Faltings.subsingleton_sections_of_intersectionNumber_neg`: `Γ(X, 𝓜)` is trivial
  whenever `(𝓗 · 𝓜) < 0` for some ample invertible `𝓗`.

## Implementation notes

The intersection number `(𝓗 · 𝓜)` is `AlgebraicGeometry.intersectionNumber` with `Z = X`
(the identity closed immersion) and `d = 2`, applied to the family `![𝓗, 𝓜]`. Ampleness is
`AlgebraicGeometry.Scheme.Modules.IsAmple`. The vanishing `H⁰(X, 𝓜) = 0` is stated as the
triviality of the module of global sections `𝓜(X)`.

## References

* [Stacks] The Stacks project, Tags 01X0, 02OR.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace Faltings

/-- On a proper surface over a field, the intersection number of `𝓗` with `𝓞_X(E)` vanishes
when the effective Cartier divisor `E` is empty: it is computed on `E`, of dimension `⊥`. -/
private theorem intersectionNumber_eq_zero_of_isEmpty (k : Type*) [Field k] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hX : topologicalKrullDim X = 2)
    (H M : X.Modules) [hHinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property H]
    [hMinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (E : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    [IsEmpty E.subscheme] (hM : M ≅ Stacks.Divisors.invertibleSheaf E) :
    @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![H, M]
      (Fin.forall_fin_two.2 ⟨hHinv, hMinv⟩) = 0 := by
  have hd : topologicalKrullDim X ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) := by simp [hX]
  have : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (![M, H] j) :=
    Fin.forall_fin_two.2 ⟨hMinv, hHinv⟩
  have h := (intersectionNumber_comp_perm k f (𝟙 X) 2 hd ![M, H] (Equiv.swap 0 1)).trans
    (intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 1 hd ![M, H] E
      ((Scheme.Modules.pullbackId X).app M ≪≫ hM))
  rw [intersectionNumber_eq_zero_of_topologicalKrullDim_lt k f _ 1 _
    (by simp [(topologicalKrullDim_eq_bot_iff_isEmpty E.subscheme).2 ‹_›])] at h
  convert h using 2
  funext i; fin_cases i <;> rfl

/-- On a proper integral surface over a field, an ample `𝓗` meets `𝓞_X(E)` nonnegatively for
every effective Cartier divisor `E`. -/
private theorem zero_le_intersectionNumber_of_iso_invertibleSheaf (k : Type*) [Field k]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hX : topologicalKrullDim X = 2) (H M : X.Modules)
    [hHinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property H]
    [hMinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (hH : Scheme.Modules.IsAmple X H) (E : X.IdealSheafData)
    [hE : Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hM : M ≅ Stacks.Divisors.invertibleSheaf E) :
    0 ≤ @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![H, M]
      (Fin.forall_fin_two.2 ⟨hHinv, hMinv⟩) := by
  rcases isEmpty_or_nonempty E.subscheme with _ | hne
  · exact (intersectionNumber_eq_zero_of_isEmpty k f hX H M E hM).ge
  · have hdim := topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor (d := 1) k f E hE
      (by rw [hX]; rfl)
    exact (intersectionNumber_pos_of_isAmple_of_isEffectiveCartierDivisor k f hX H M hH
      E hne (by simpa using hdim) hM).le

/-- On an integral proper surface `X` over a field `k`, an invertible module `M` with
`(H · M) < 0` for some ample invertible `H` has no nonzero global sections. -/
@[faltings "lem_nt_h0_vanishing_negative_degree"]
theorem subsingleton_sections_of_intersectionNumber_neg
    (k : Type*) [Field k] {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] (hX : topologicalKrullDim X = 2) (H M : X.Modules)
    [hHinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property H]
    [hMinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (hH : Scheme.Modules.IsAmple X H)
    (hneg : @intersectionNumber k _ X X f _ (𝟙 X) _ 2 (by simp [hX]) ![H, M]
        (Fin.forall_fin_two.2 ⟨hHinv, hMinv⟩) < 0) :
    Subsingleton (M.val.obj (op ⊤)) := by
  refine subsingleton_of_forall_eq 0 fun s => by_contra fun hs => ?_
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := hMinv
  let t := Stacks.SheafOfModules.sectionsOfTopOfRingSheaf M s
  have hreg := isRegularSection_of_eval_top_ne_zero M t
    (by rwa [Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top M s])
  have := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X M t).2 hreg
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X M t hreg).exists
  exact hneg.not_ge (zero_le_intersectionNumber_of_iso_invertibleSheaf k f hX H M hH _ e.symm)

end Faltings
