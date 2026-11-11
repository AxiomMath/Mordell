module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.KPointCoordinates
public import Mordell.Height.Machine.IsomorphicPullbacks
public import Mordell.Height.Machine.PositiveCombination

/-!
# Weil's theorem: heights of classes of zero are bounded

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ`, with structure
morphism `f : X ⟶ Spec k`. If `γ` is a formal `ℤ`-combination of projective embeddings of `X`
whose class `cl(γ)` in `Pic(X)` vanishes, then the height `h_γ` is a bounded function on the
`k`-points of `X`.

Write `γ = γ₊ - γ₋` with `γ₊`, `γ₋` sums of projective embeddings, and add one embedding `φ₀`
to both. By `Faltings.EmbeddingGroup.exists_projectiveEmbedding_height_eq_and_embeddingClass_eq`
the combinations `γ₊ + φ₀` and `γ₋ + φ₀` are realized by single embeddings `Φ₊`, `Φ₋` with the
same heights and classes, so `Φ₊^*𝒪(1) ≅ Φ₋^*𝒪(1)` and `h_γ = h ∘ Φ₊ - h ∘ Φ₋`, which is
bounded by `Faltings.exists_abs_weilHeight_sub_le_of_pullback_iso`.

## Main results

* `Faltings.EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero`: if
  `Faltings.embeddingClass f γ = 0` then `|Faltings.EmbeddingGroup.height f γ p| ≤ C` for some
  constant `C` and every `k`-point `p` of `X`.

## Implementation notes

The base field is any field `k` algebraic over `ℚ`; the source's case is `k = ℚ̄`. A `k`-point
of `X` is a section of `f`. If `X` has no projective embedding at all, the group `Emb(X)` is
trivial and `γ = 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2, Weil's theorem (iii).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

/-- Every element of a free abelian group is a difference of two sums of generators. -/
public theorem exists_eq_sum_sub_sum {α : Type*} (γ : FreeAbelianGroup α) :
    ∃ l₁ l₂ : List α, γ = (l₁.map FreeAbelianGroup.of).sum - (l₂.map FreeAbelianGroup.of).sum := by
  induction γ using FreeAbelianGroup.induction_on with
  | zero => exact ⟨[], [], by simp⟩
  | of x => exact ⟨[x], [], by simp⟩
  | neg x => exact ⟨[], [x], by simp⟩
  | add a b ha hb =>
    obtain ⟨l₁, l₂, rfl⟩ := ha
    obtain ⟨m₁, m₂, rfl⟩ := hb
    exact ⟨l₁ ++ m₁, l₂ ++ m₂, by simp only [List.map_append, List.sum_append]; abel⟩

/-- Every element of a free abelian group is a difference of two sums of generators that both
begin with a prescribed generator `e`. -/
public theorem exists_eq_sum_cons_sub_sum_cons {α : Type*} (e : α) (γ : FreeAbelianGroup α) :
    ∃ l₁ l₂ : List α, γ = ((e :: l₁).map FreeAbelianGroup.of).sum -
      ((e :: l₂).map FreeAbelianGroup.of).sum := by
  obtain ⟨l₁, l₂, rfl⟩ := exists_eq_sum_sub_sum γ
  exact ⟨l₁, l₂, by simp only [List.map_cons, List.sum_cons]; abel⟩

/-- The comparison `φ^* L ≅ φ^* L` between the ringed-space pullback (in which Picard classes
are stated) and the pullback of sheaves of modules on schemes. -/
@[expose] public noncomputable def modulePullbackIsoPullback {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (L : Y.Modules) :
    (RingedSpaceModuleAdjunction.modulePullback φ.toLRSHom.toShHom).obj L ≅
      (Scheme.Modules.pullback φ).obj L :=
  ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    φ.toLRSHom.toShHom).leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction φ)).app L

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [IsProjectiveVariety k f] [Smooth f]

/-- A nonempty list of embeddings, all with coefficient `1`, is realized by one embedding. -/
public theorem exists_projectiveEmbedding_of_list [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    (e : Σ n : ℕ, ProjectiveEmbedding f n) (l : List (Σ n : ℕ, ProjectiveEmbedding f n)) :
    ∃ (N : ℕ) (Φ : ProjectiveEmbedding f N),
      Φ.height = EmbeddingGroup.height f (((e :: l).map FreeAbelianGroup.of).sum) ∧
      embeddingClass f (FreeAbelianGroup.of ⟨N, Φ⟩) =
        embeddingClass f (((e :: l).map FreeAbelianGroup.of).sum) := by
  have hsum : ∑ i : Fin (e :: l).length, 1 • FreeAbelianGroup.of ((e :: l).get i) =
      ((e :: l).map FreeAbelianGroup.of).sum := by
    simp only [one_smul, List.get_eq_getElem]
    exact Fin.sum_univ_fun_getElem _ _
  have : Nonempty (Fin (e :: l).length) := ⟨⟨0, by simp⟩⟩
  obtain ⟨N, Φ, h1, h2⟩ := EmbeddingGroup.exists_projectiveEmbedding_height_eq_and_embeddingClass_eq
    f (e :: l).get (fun _ => 1) (fun _ => Nat.one_pos)
  exact ⟨N, Φ, h1.trans (by rw [hsum]), h2.trans (by rw [hsum])⟩

/-- Two projective embeddings with the same class have isomorphic pullbacks of `𝒪(1)`. -/
public theorem nonempty_pullback_iso_of_embeddingClass_eq {N M : ℕ}
    (Φ : ProjectiveEmbedding f N) (Ψ : ProjectiveEmbedding f M)
    (h : embeddingClass f (FreeAbelianGroup.of ⟨N, Φ⟩) =
      embeddingClass f (FreeAbelianGroup.of ⟨M, Ψ⟩)) :
    Nonempty ((Scheme.Modules.pullback Φ.hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))) ≅
      (Scheme.Modules.pullback Ψ.hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M (Spec (.of k)))) := by
  simp only [embeddingClass, FreeAbelianGroup.lift_apply_of] at h
  obtain ⟨α⟩ := (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _ _ _).1 h
  exact ⟨(modulePullbackIsoPullback _ _).symm ≪≫ α ≪≫ modulePullbackIsoPullback _ _⟩

/-- **Weil's height machine, core case.** Two projective embeddings with the same class in
`Pic(X)` have heights differing by a bounded function on the `k`-points of `X`. -/
public theorem exists_abs_height_sub_height_le_of_embeddingClass_eq [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] {N M : ℕ}
    (Φ : ProjectiveEmbedding f N) (Ψ : ProjectiveEmbedding f M)
    (h : embeddingClass f (FreeAbelianGroup.of ⟨N, Φ⟩) =
      embeddingClass f (FreeAbelianGroup.of ⟨M, Ψ⟩)) :
    ∃ C : ℝ, ∀ p, |Φ.height p - Ψ.height p| ≤ C := by
  obtain ⟨α⟩ := nonempty_pullback_iso_of_embeddingClass_eq Φ Ψ h
  obtain ⟨C, hC⟩ :=
    exists_abs_weilHeight_sub_le_of_pullback_iso Φ.hom Φ.hom_over Ψ.hom Ψ.hom_over α
  refine ⟨C, fun p => hC p.1 p.2 ⟨_, ?_⟩ ⟨_, ?_⟩ rfl rfl⟩ <;>
    simp only [Category.assoc, projectiveSpaceOfModuleIso_inv_comp_toSpec] <;>
    rw [ProjectiveEmbedding.hom_over, p.2]

end

/-- **Weil's theorem** (classes of zero): if `γ ∈ Emb(X)` has class
`Faltings.embeddingClass f γ = 0` in `Pic(X)`, then the height `Faltings.EmbeddingGroup.height f γ`
is bounded on the `k`-points of `X`. -/
@[faltings "thm_ht_weil_height_machine"]
public theorem EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero {k : Type u}
    [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] {γ : EmbeddingGroup f}
    (hγ : embeddingClass f γ = 0) :
    ∃ C : ℝ, ∀ p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}, |EmbeddingGroup.height f γ p| ≤ C := by
  rcases isEmpty_or_nonempty (Σ n : ℕ, ProjectiveEmbedding f n) with _ | ⟨⟨e⟩⟩
  · exact ⟨0, fun p => by simp [Subsingleton.elim γ 0]⟩
  obtain ⟨l₁, l₂, rfl⟩ := exists_eq_sum_cons_sub_sum_cons e γ
  obtain ⟨N, Φ, hΦh, hΦc⟩ := exists_projectiveEmbedding_of_list e l₁
  obtain ⟨M, Ψ, hΨh, hΨc⟩ := exists_projectiveEmbedding_of_list e l₂
  obtain ⟨C, hC⟩ := exists_abs_height_sub_height_le_of_embeddingClass_eq Φ Ψ
    (by rw [hΦc, hΨc, ← sub_eq_zero, ← map_sub, hγ])
  exact ⟨C, fun p => by simpa [hΦh, hΨh] using hC p⟩

end Faltings
