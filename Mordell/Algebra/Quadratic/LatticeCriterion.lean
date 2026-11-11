module

public import Mathlib
public import Mordell.Attr

/-!
# The lattice criterion for positive definiteness

Let `Γ` be a finitely generated abelian group and `b` a symmetric biadditive real form on `Γ`
with `b x x ≥ 0` for all `x`, such that `{x | b x x ≤ C}` is finite for every real `C`. Then
the `ℝ`-bilinear extension of `b` to `V = ℝ ⊗[ℤ] Γ` is positive definite: its quadratic form
is positive on every nonzero vector.

The proof diagonalises `B` in an orthogonal basis. If some diagonal entry were `≤ 0`, the
projection `P` onto the coordinates with positive diagonal entry would bound `B w w` by a
multiple of `‖P w‖ ^ 2`. Then `P ∘ ι` has discrete image, and it kills only torsion, since
`b (N • x) (N • x) = N ^ 2 b x x ≤ 0` for every `N` would put infinitely many points in a finite
sublevel set. So `P ∘ ι` maps a basis of `V` taken from `ι(Γ)` to `ℤ`-independent vectors of a
discrete subgroup of a space of dimension `< finrank ℝ V`, which is impossible.

## Main results

* `Faltings.posDef_of_finite_setOf_le`: the lattice criterion.
* `Faltings.exists_bilinForm_posDef_of_finite_setOf_le`: the lattice criterion with the
  extension: `b` extends to a symmetric positive definite form on the real base change.

## Implementation notes

The real vector space `V` is not the concrete tensor product: it is any real vector space with
an additive map `ι : Γ →ₗ[ℤ] V` satisfying `IsBaseChange ℝ ι`, which characterises
`ℝ ⊗[ℤ] Γ` up to unique isomorphism. The extension of `b` is any `ℝ`-bilinear form `B` on `V`
with `B (ι x) (ι y) = b x y`; since `ι` is a base change, there is exactly one such `B`.
Positive definiteness is `QuadraticMap.PosDef` of `B.toQuadraticMap`.

The source's step through Minkowski's theorem, a non-zero lattice point in a thin convex body
around the null space of `B`, is replaced by its rank form: a discrete subgroup of a real vector
space has `ℤ`-rank at most the dimension (`Real.finrank_eq_int_finrank_of_discrete`).

## References

* [Wu] Lemma 2.6; [B] E. Bombieri, *The Mordell conjecture revisited*, Sec. 5.
-/

@[expose] public section

namespace Faltings

open Module Submodule

variable {Γ V : Type*} [AddCommGroup Γ] [AddCommGroup V] [Module ℝ V]

/-- If `b x x ≤ 0` and the sublevel set `{x | b x x ≤ 0}` is finite, then `x` is torsion: the
multiples `N • x` all lie in that set. -/
private lemma exists_zsmul_eq_zero (b : Γ →+ Γ →+ ℝ) (hfin : {x : Γ | b x x ≤ 0}.Finite)
    {x : Γ} (hx : b x x ≤ 0) : ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
  have hmaps : Set.MapsTo (fun N : ℤ => N • x) Set.univ {x : Γ | b x x ≤ 0} := fun N _ => by
    simpa [← mul_assoc] using mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg (N : ℝ)) hx
  obtain ⟨N₁, -, N₂, -, hne, heq⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hfin
  exact ⟨N₁ - N₂, sub_ne_zero.2 hne, by rw [sub_smul, heq, sub_self]⟩

/-- A `ℤ`-linear map into a real vector space kills elements of finite order. -/
private lemma map_eq_zero_of_zsmul_eq_zero (ι : Γ →ₗ[ℤ] V) {n : ℤ} (hn : n ≠ 0) {x : Γ}
    (hx : n • x = 0) : ι x = 0 := by
  have : (n : ℝ) • ι x = 0 := by rw [Int.cast_smul_eq_zsmul, ← map_zsmul, hx, map_zero]
  exact (smul_eq_zero.1 this).resolve_left (Int.cast_ne_zero.2 hn)

variable {E : Type*} [NormedAddCommGroup E]

/-- If `b x x ≤ D ‖Φ x‖ ^ 2` and `{x | b x x ≤ 1}` is finite, then `Φ` has discrete image: a
small ball around `0` meets it in a finite set. -/
private lemma discreteTopology_range (b : Γ →+ Γ →+ ℝ) (hfin : {x : Γ | b x x ≤ 1}.Finite)
    (Φ : Γ →ₗ[ℤ] E) {D : ℝ} (hD : 0 ≤ D) (hΦ : ∀ x, b x x ≤ D * ‖Φ x‖ ^ 2) :
    DiscreteTopology (LinearMap.range Φ) := by
  set δ : ℝ := 1 / (D + 1)
  have hδ : 0 < δ := by positivity
  have hsmall : ∀ x, ‖Φ x‖ < δ → b x x ≤ 1 := fun x hx => by
    refine (hΦ x).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx.le 2)
      hD).trans ?_)
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hF : (Φ '' {x | b x x ≤ 1} \ {0}).Finite := (hfin.image _).sdiff
  rw [discreteTopology_iff_isOpen_singleton_zero]
  refine ⟨Metric.ball 0 δ ∩ (Φ '' {x | b x x ≤ 1} \ {0})ᶜ,
    Metric.isOpen_ball.inter hF.isClosed.isOpen_compl, ?_⟩
  ext ⟨y, x, rfl⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_image, Set.mem_ofPred_eq,
    Subtype.ext_iff, ZeroMemClass.coe_zero]
  refine ⟨fun ⟨h1, h2⟩ => by_contra fun h0 => h2 ⟨⟨x, hsmall x h1, rfl⟩, h0⟩,
    fun h => ⟨by simp [h, hδ], fun h' => h'.2 h⟩⟩

/-- **Rank comparison.** Let `ι : Γ →ₗ[ℤ] V` have range spanning the finite-dimensional real
space `V`, and let `Φ : Γ →ₗ[ℤ] E` have discrete image in a finite-dimensional normed real space,
with `ι x = 0` whenever `Φ x = 0`. Then `finrank ℝ V ≤ finrank ℝ E`: the lifts to `Γ` of a basis
of `V` taken from `ι(Γ)` map to `ℤ`-independent vectors of the image of `Φ`, whose `ℤ`-rank is at
most `finrank ℝ E` by discreteness. -/
private lemma finrank_le_of_discreteTopology_range [Module.Finite ℤ Γ] [FiniteDimensional ℝ V]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Γ →ₗ[ℤ] V}
    (hspan : span ℝ (Set.range ι) = ⊤) (Φ : Γ →ₗ[ℤ] E)
    (hdisc : DiscreteTopology (LinearMap.range Φ)) (hker : ∀ x, Φ x = 0 → ι x = 0) :
    finrank ℝ V ≤ finrank ℝ E := by
  classical
  obtain ⟨t, hts, htspan, htli⟩ := exists_linearIndependent ℝ (Set.range ι)
  have := htli.setFinite.fintype
  have hcard : Fintype.card t = finrank ℝ V :=
    (finrank_eq_card_basis (Basis.mk htli (by rw [Subtype.range_coe, htspan, hspan]))).symm
  choose u hu using fun k : t => hts k.2
  have hli : LinearIndependent ℤ
      (fun k : t => (⟨Φ (u k), LinearMap.mem_range_self Φ _⟩ : LinearMap.range Φ)) := by
    refine LinearIndependent.of_comp (LinearMap.range Φ).subtype
      (Fintype.linearIndependent_iff.2 fun m hm k => ?_)
    have h1 := hker (∑ k, m k • u k) (by simpa [map_sum] using hm)
    simp only [map_sum, map_zsmul, hu, ← Int.cast_smul_eq_zsmul ℝ] at h1
    exact_mod_cast Fintype.linearIndependent_iff.1 htli _ h1 k
  calc finrank ℝ V = Fintype.card t := hcard.symm
    _ ≤ finrank ℤ (LinearMap.range Φ) := hli.fintype_card_le_finrank
    _ = Set.finrank ℝ (LinearMap.range Φ : Set E) := by
      rw [Real.finrank_eq_int_finrank_of_discrete (by rwa [span_eq]), Set.finrank, span_eq]
    _ ≤ finrank ℝ E := Submodule.finrank_le _

/-- In an orthogonal basis, `B w w` is the weighted sum of squares of the coordinates. -/
private lemma apply_self_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    {B : LinearMap.BilinForm ℝ V} (v : Basis n ℝ V) (hv : B.IsOrthoᵢ v) (w : V) :
    B w w = ∑ i, B (v i) (v i) * v.repr w i ^ 2 := by
  conv_lhs => rw [← v.sum_repr w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hv hji, mul_zero]) (by simp)]
  ring

/-- In an orthogonal basis, `B w w` is at most `D ‖P w‖ ^ 2`, where `P` projects onto the
coordinates with positive diagonal entry and `D` is the sum of the positive diagonal entries. -/
private lemma apply_self_le_mul_norm_sq {n : Type*} [Fintype n] [DecidableEq n]
    {B : LinearMap.BilinForm ℝ V} (v : Basis n ℝ V) (hv : B.IsOrthoᵢ v) (w : V) :
    B w w ≤ (∑ i, max (B (v i) (v i)) 0) *
      ‖(LinearMap.pi fun i : {i // 0 < B (v i) (v i)} => v.coord i.1) w‖ ^ 2 := by
  rw [apply_self_eq_sum v hv, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : 0 < B (v i) (v i)
  · rw [max_eq_left hi.le]
    refine mul_le_mul_of_nonneg_left ?_ hi.le
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_pi_norm ((LinearMap.pi fun i : {i // 0 < B (v i) (v i)} => v.coord i.1) w) ⟨i, hi⟩) 2
  · push Not at hi
    rw [max_eq_right hi, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hi (sq_nonneg _)

/-- **Lattice criterion.** Let `Γ` be a finitely generated abelian group and `b` a symmetric
biadditive real form on `Γ` with `0 ≤ b x x` and `{x | b x x ≤ C}` finite for every `C`. If
`ι : Γ →ₗ[ℤ] V` exhibits `V` as the real base change of `Γ` and `B` is the `ℝ`-bilinear form
on `V` extending `b`, then `B` is positive definite. -/
@[faltings "lem_nt_lattice_criterion"]
theorem posDef_of_finite_setOf_le {Γ V : Type*} [AddCommGroup Γ] [Module.Finite ℤ Γ]
    [AddCommGroup V] [Module ℝ V] (b : Γ →+ Γ →+ ℝ) (hb : ∀ x y, b x y = b y x)
    (hq : ∀ x, 0 ≤ b x x) (hfin : ∀ C : ℝ, {x : Γ | b x x ≤ C}.Finite)
    (ι : Γ →ₗ[ℤ] V) (hι : IsBaseChange ℝ ι) (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B (ι x) (ι y) = b x y) : B.toQuadraticMap.PosDef := by
  classical
  have := Module.finitePresentation_of_finite ℤ Γ
  have := FinitePresentation.of_isBaseChange ι hι
  have hspan : span ℝ (Set.range ι) = ⊤ :=
    eq_top_iff.2 fun w _ => hι.inductionOn w (motive := fun w => w ∈ span ℝ (Set.range ι))
      (fun x => subset_span ⟨x, rfl⟩) (fun s _ hn => smul_mem _ s hn) (fun _ _ => add_mem)
  have hsymm : B = B.flip := LinearMap.ext_on_range hspan fun x =>
    LinearMap.ext_on_range hspan fun y => by simp [hB, hb]
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1
    (LinearMap.BilinForm.isSymm_def.2 fun w w' => LinearMap.congr_fun₂ hsymm w w'))
  -- it suffices that every diagonal entry is positive
  suffices hpos : ∀ i, 0 < B (v i) (v i) by
    intro w hw
    rw [LinearMap.BilinMap.toQuadraticMap_apply, apply_self_eq_sum v hv]
    obtain ⟨i, hi⟩ : ∃ i, v.repr w i ≠ 0 := by
      by_contra! h
      exact hw (v.repr.injective (by ext i; simp [h]))
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hpos i) (pow_pos (abs_pos.2 hi) 2 |>.trans_eq (sq_abs _))⟩
  by_contra! ⟨j, hj⟩
  -- `Φ` is `ι` followed by the projection onto the coordinates where `B` is positive
  let Φ := (LinearMap.pi fun i : {i // 0 < B (v i) (v i)} => v.coord i.1).restrictScalars ℤ ∘ₗ ι
  have hΦ : ∀ x, b x x ≤ (∑ i, max (B (v i) (v i)) 0) * ‖Φ x‖ ^ 2 := fun x =>
    hB x x ▸ apply_self_le_mul_norm_sq v hv (ι x)
  have hker : ∀ x, Φ x = 0 → ι x = 0 := fun x hx => by
    obtain ⟨n, hn, hnx⟩ := exists_zsmul_eq_zero b (hfin 0) (by simpa [hx] using hΦ x)
    exact map_eq_zero_of_zsmul_eq_zero ι hn hnx
  have := finrank_le_of_discreteTopology_range hspan Φ (discreteTopology_range b (hfin 1) Φ
    (Finset.sum_nonneg fun i _ => le_max_right _ _) hΦ) hker
  have hlt := Fintype.card_subtype_lt (p := fun i => 0 < B (v i) (v i)) (x := j) (not_lt.2 hj)
  rw [Module.finrank_fintype_fun_eq_card] at this
  rw [Fintype.card_fin] at hlt
  omega

open scoped TensorProduct in
/-- **Lattice criterion, with the extension.** A symmetric biadditive real form `b` on a
finitely generated abelian group `Γ`, nonnegative on the diagonal and with finite sublevel sets
`{x | b x x ≤ C}`, extends to a symmetric positive definite `ℝ`-bilinear form on the real base
change `V` of `Γ`. -/
theorem exists_bilinForm_posDef_of_finite_setOf_le {Γ V : Type*} [AddCommGroup Γ]
    [Module.Finite ℤ Γ] [AddCommGroup V] [Module ℝ V] (b : Γ →+ Γ →+ ℝ)
    (hb : ∀ x y, b x y = b y x) (hq : ∀ x, 0 ≤ b x x)
    (hfin : ∀ C : ℝ, {x : Γ | b x x ≤ C}.Finite) (j : Γ →ₗ[ℤ] V) (hj : IsBaseChange ℝ j) :
    ∃ B : LinearMap.BilinForm ℝ V, (∀ x y, B (j x) (j y) = b x y) ∧ B.IsSymm ∧
      B.toQuadraticMap.PosDef := by
  let g : Γ →ₗ[ℤ] (ℝ ⊗[ℤ] Γ →ₗ[ℝ] ℝ) :=
    { toFun := fun x => LinearMap.liftBaseChange ℝ (b x).toIntLinearMap
      map_add' := fun x y => by ext; simp
      map_smul' := fun n x => by ext; simp }
  let e := hj.equiv
  let B : LinearMap.BilinForm ℝ V :=
    (LinearMap.liftBaseChange ℝ g).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have he : ∀ x, e.symm (j x) = 1 ⊗ₜ x := fun x => by
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  have hB : ∀ x y, B (j x) (j y) = b x y := fun x y => by
    simp [B, he, g]
  have hspan : Submodule.span ℝ (Set.range j) = ⊤ :=
    eq_top_iff.2 fun w _ =>
      hj.inductionOn w (motive := fun w => w ∈ Submodule.span ℝ (Set.range j))
      (fun x => Submodule.subset_span ⟨x, rfl⟩)
      (fun s _ hn => Submodule.smul_mem _ s hn) (fun _ _ => Submodule.add_mem _)
  have hsymm : B.IsSymm := by
    refine LinearMap.BilinForm.isSymm_def.2 fun v w => ?_
    have : B = B.flip := LinearMap.ext_on_range hspan fun x =>
      LinearMap.ext_on_range hspan fun y => by simp [hB, hb]
    exact LinearMap.congr_fun₂ this v w
  exact ⟨B, hB, hsymm, posDef_of_finite_setOf_le b hb hq hfin j hj B hB⟩

end Faltings
