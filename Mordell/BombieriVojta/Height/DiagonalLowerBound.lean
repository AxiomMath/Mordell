module
public import Mordell.BombieriVojta.Height.Basic
public import Mordell.CurveProduct.VojtaClass
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import Mordell.Height.Machine.Positivity
public import Mordell.Height.Machine.Functoriality
public import Mordell.Height.Machine.EmbeddingClassSurjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OverBase
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
import Mordell.NeronTate.Existence

/-!
# The height `h_Δ` is bounded below off the diagonal

Let `X = (C, P)` be a curve of genus `g ≥ 2` over a field `k` algebraic over `ℚ` with a divisor
`P` of degree one. Fix the auxiliary data of Bombieri's Section 3: an integer `N ≥ 2g + 1` with
the embedding `φ_{NP}` of `C` by a basis of `H⁰(C, 𝒪(NP))`, and an integer `s ≥ 1` with the
embedding `φ_B` of `C × C` by a basis of `H⁰(C × C, 𝒪(B))`, `B = s P × C + s C × P - Δ'`.
For `d₁ = d₂ = d = 1` the divisor `V(1, 1, 1) = P × C + C × P + Δ'` is the diagonal `Δ`, which
is effective, and its height `h_V = h_Δ` is bounded below off its support: there is `κ₄` with
`h_V(z, w) ≥ -κ₄` for all pairs `z ≠ w` of points of `C`.

## Main results

* `Faltings.CurveWithDegreeOneDivisor.exists_neg_le_vojtaHeight_one_one_one`: the lower bound.

## Implementation notes

The embeddings are pinned as the canonical morphisms
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of a `k`-basis of the global sections of
an invertible module whose class in the Picard group is that of `NP`, respectively of
`B = Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)`; that these are closed
immersions is `Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver` and
`Faltings.CurveWithDegreeOneDivisor.isClosedImmersion_toProjectiveSpaceOver_vojtaClass`. The
`k`-module structure on global sections is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule`, through the
structure morphism. The source's points of `(C × C)(k̄)` are the case `k = k̄`; a pair of
`k`-points off the diagonal is a pair `z ≠ w`.

For `d₁ = d₂ = d = 1` the height of Vojta's divisor is
`h_V(z, w) = (1 + s)/N · h_{NP}(z) + (1 + s)/N · h_{NP}(w) - h_B(z, w)`. The proof realises
`N h_V` up to a bounded function as the height of
`γ = (1 + s) γ₁ + (1 + s) γ₂ - N [φ_B] ∈ Emb(C × C)`, where `γᵢ` is any element of class
`prᵢ^* [φ_{NP}]`; `cl` is onto by `Faltings.exists_embeddingClass_sub_eq`, and
`h_{γᵢ} = h_{NP} ∘ prᵢ + O(1)` is Weil's functoriality
`Faltings.EmbeddingGroup.exists_abs_height_sub_height_comp_le`. The class of `γ` is
`(1 + s) N (P × C + C × P) - N (s P × C + s C × P - Δ') = N Δ`, and Weil's positivity theorem
`Faltings.EmbeddingGroup.exists_le_height_of_not_mem_baseLocus` applies: the base locus of
`|N Δ|` lies on `Δ`, because `N Δ` is itself a member of the system. The source uses the
Segre–Veronese embedding `ψ_{1+s,1+s}` and the Veronese composite `φ_{NB}` in place of the
`γᵢ`; the height and class of `γ` agree with those of `ψ_{1+s,1+s} - φ_{NB}` up to a bounded
function and exactly, respectively.

The diagonal `Δ ⊆ C ×_k C` is the prime divisor cut out by the kernel of `pullback.diagonal`, an
integral effective Cartier divisor (`Faltings.isEffectiveCartierDivisor_ker_diagonal`), of
codimension one by Krull's principal ideal theorem
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`); the `N`-th power
of its ideal is `AlgebraicGeometry.positiveWeilIdeal` of `N Δ`. A `k`-point of `C ×_k C` on `Δ`
is a pair `(z, z)`, since a `k`-point of a `k`-scheme is determined by its image point (the case
of an arbitrary field of Mathlib's `AlgebraicGeometry.ext_of_apply_closedPoint_eq`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 3; Section 4, p. 619;
  and Section 5, p. 623
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Faltings

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-! ### Rational points over a field -/

section Points

/-- Two left inverses `a`, `b` of a ring hom `ι : K →+* F` of fields agree: every `t` is
`ι (a t)`, since `a` is injective. -/
private theorem eq_of_comp_eq_id {F K : Type*} [Field F] [Field K] (ι : K →+* F) (a b : F →+* K)
    (ha : a.comp ι = RingHom.id K) (hb : b.comp ι = RingHom.id K) : a = b := by
  ext t
  have h : a (t - ι (a t)) = 0 := by
    rw [map_sub, ← RingHom.comp_apply, ha, RingHom.id_apply, sub_self]
  calc a t = b (ι (a t)) := (RingHom.congr_fun hb _).symm
    _ = b t := congrArg b (sub_eq_zero.1 ((map_eq_zero a).1 h)).symm

/-- If `Spec K ⟶ Spec κ(x) ⟶ X ⟶ Spec K` is the identity, then `a : κ(x) ⟶ K` is a left
inverse of the ring hom `K ⟶ κ(x)` that `X ⟶ Spec K` induces on global sections. -/
private theorem comp_eq_id_of_spec_map_comp_eq_id {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) (x : X)
    (a : X.residueField x ⟶ CommRingCat.of K)
    (ha : Spec.map a ≫ X.fromSpecResidueField x ≫ h = 𝟙 _) :
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (X.fromSpecResidueField x ≫ h).appTop ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom) ≫ a = 𝟙 _ := by
  have := congrArg Scheme.Hom.appTop ha
  rw [Scheme.Hom.comp_appTop] at this
  rw [Category.assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc
    (Scheme.Hom.appTop _), this, Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]

/-- Two `K`-points of a `K`-scheme with the same image point are equal, for an arbitrary field
`K`. -/
private theorem ext_of_apply_closedPoint_eq' {K : Type u} [Field K] {X : Scheme.{u}}
    {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K)) (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f.base (IsLocalRing.closedPoint K) = g.base (IsLocalRing.closedPoint K)) : f = g := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective f
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g
  obtain rfl : x = y := by
    simpa only [Equiv.apply_symm_apply] using (Scheme.SpecToEquivOfField_apply_fst _ _ _).trans
      (H.trans (Scheme.SpecToEquivOfField_apply_fst _ _ _).symm)
  rw [Scheme.SpecToEquivOfField_symm_apply] at hf hg ⊢
  rw [Category.assoc] at hf hg
  obtain rfl : a = b := by
    ext1
    exact eq_of_comp_eq_id _ _ _
      (congrArg CommRingCat.Hom.hom (comp_eq_id_of_spec_map_comp_eq_id h _ a hf))
      (congrArg CommRingCat.Hom.hom (comp_eq_id_of_spec_map_comp_eq_id h _ b hg))
  rfl

end Points

/-- The ideal of the `n`-th power of an ideal sheaf on an affine open is the `n`-th power of its
ideal there. -/
private theorem IdealSheafData.ideal_pow {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) : ∀ n : ℕ, (I ^ n).ideal U = I.ideal U ^ n
  | 0 => by rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top]; simp
  | n + 1 => by
    rw [pow_succ, pow_succ, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      IdealSheafData.ideal_pow I U n]

/-! ### The diagonal as a prime divisor -/

section Diagonal

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsSmoothProjectiveCurve k f]

/-- The diagonal `Δ ⊆ C ×_k C` of a smooth projective curve, as a prime divisor: the integral
closed subscheme cut out by the kernel of `pullback.diagonal f`. -/
private noncomputable def diagonalPrimeDivisor : PrimeDivisor (pullback f f) where
  idealSheaf := (pullback.diagonal f).ker
  integral := (isEffectiveCartierDivisor_ker_diagonal k f).2.1
  codimension_one := by
    have := (isEffectiveCartierDivisor_ker_diagonal k f).2.1
    have : IsLocallyNoetherian (pullback f f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
    rw [← ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one]
    refine ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor _
      (isEffectiveCartierDivisor_ker_diagonal k f).1 _ ?_
    exact ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, genericPoint_spec _⟩

open Classical in
/-- The Weil divisor `N Δ` on `C ×_k C`. -/
private noncomputable def nDiagonal (N : ℕ) : WeilDivisor (pullback f f) :=
  ⟨fun Z => if Z = diagonalPrimeDivisor f then (N : ℤ) else 0, by
    rw [mem_weilDivisor_iff]
    intro x
    refine ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton (diagonalPrimeDivisor f)).subset ?_⟩
    intro Z hZ
    by_contra hne
    simp [show Z ≠ diagonalPrimeDivisor f from hne] at hZ⟩

open Classical in
private theorem nDiagonal_apply (N : ℕ) (Z : PrimeDivisor (pullback f f)) :
    (nDiagonal f N).val Z = if Z = diagonalPrimeDivisor f then (N : ℤ) else 0 :=
  rfl

/-- The ideal sheaf of `N Δ` is the `N`-th power of the ideal of the diagonal. -/
private theorem positiveWeilIdeal_nDiagonal (N : ℕ) :
    positiveWeilIdeal (nDiagonal f N) = (pullback.diagonal f).ker ^ N := by
  classical
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [positiveWeilIdeal_ideal, IdealSheafData.ideal_pow]
  have hS : (finite_primeDivisors_meeting_affine (nDiagonal f N) U).toFinset ⊆
      {diagonalPrimeDivisor f} := by
    intro Z hZ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, nDiagonal_apply] at hZ
    simp only [Finset.mem_singleton]
    by_contra h
    simp [h] at hZ
  rw [Finset.prod_subset hS, Finset.prod_singleton, nDiagonal_apply, if_pos rfl,
    Int.toNat_natCast]
  · rfl
  intro Z hZ hZS
  rw [Finset.mem_singleton] at hZ
  subst hZ
  rw [nDiagonal_apply, if_pos rfl, Int.toNat_natCast]
  by_cases hN : N = 0
  · rw [hN, pow_zero]
  · refine ideal_pow_eq_one_of_supportSet_inter_not_nonempty _ U ?_ N
    intro hne
    apply hZS
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hne⟩
    rw [nDiagonal_apply, if_pos rfl]
    exact_mod_cast hN

/-- The negative part of `N Δ` is zero: its ideal sheaf is the unit ideal. -/
private theorem positiveWeilIdeal_neg_nDiagonal (N : ℕ) :
    positiveWeilIdeal (-nDiagonal f N) = ⊤ := by
  classical
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [positiveWeilIdeal_ideal]
  refine (Finset.prod_eq_one fun Z _ => ?_).trans (by simp)
  have : ((-nDiagonal f N).val Z).toNat = 0 := by
    change (-(nDiagonal f N).val Z).toNat = 0
    rw [nDiagonal_apply]
    split_ifs <;> simp
  rw [this, pow_zero]

variable [IsProjectiveVariety k (pullback.fst f f ≫ f)] [Smooth (pullback.fst f f ≫ f)]

/-- `cl(N Δ) = N [𝒪(Δ)]`, the class of the diagonal being that of the effective Cartier divisor
`ker (pullback.diagonal f)`. -/
private theorem picardClassOfWeilDivisor_nDiagonal (N : ℕ) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal f).ker :=
      (isEffectiveCartierDivisor_ker_diagonal k f).1
    picardClassOfWeilDivisor (pullback.fst f f ≫ f) (nDiagonal f N) =
      (N : ℤ) • Stacks.Divisors.picardClass (pullback.diagonal f).ker := by
  have hX := uniqueFactorizationMonoid_stalk_of_smooth (pullback.fst f f ≫ f)
  haveI : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k f).1
  haveI := positiveWeilIdeal_isEffectiveCartierDivisor hX (nDiagonal f N)
  haveI := positiveWeilIdeal_isEffectiveCartierDivisor hX (-nDiagonal f N)
  change Stacks.Divisors.picardClass (positiveWeilIdeal (nDiagonal f N)) -
    Stacks.Divisors.picardClass (positiveWeilIdeal (-nDiagonal f N)) = _
  rw [Stacks.Divisors.picardClass_congr (positiveWeilIdeal_nDiagonal f N),
    Stacks.Divisors.picardClass_congr (positiveWeilIdeal_neg_nDiagonal f N),
    Stacks.Divisors.picardClass_pow, Stacks.Divisors.picardClass_top, sub_zero]

/-- `N Δ` is effective. -/
private theorem nDiagonal_nonneg (N : ℕ) : 0 ≤ nDiagonal f N := fun Z => by
  change (0 : ℤ) ≤ (nDiagonal f N).val Z
  rw [nDiagonal_apply]
  split_ifs <;> simp

/-- `N Δ > 0` for `N ≥ 1`. -/
private theorem nDiagonal_pos (N : ℕ) (hN : 1 ≤ N) : 0 < nDiagonal f N := by
  refine lt_of_le_of_ne (nDiagonal_nonneg f N) fun h => ?_
  have := congrArg (fun D : WeilDivisor (pullback f f) => D.val (diagonalPrimeDivisor f)) h
  simp only [nDiagonal_apply] at this
  change (0 : ℤ) = N at this
  omega

/-- `N Δ ∈ |N Δ|`, as the divisor of the constant rational function `1`. -/
private theorem nDiagonal_mem_completeLinearSystem (N : ℕ) :
    nDiagonal f N ∈
      completeLinearSystemOfWeilDivisor (pullback.fst f f ≫ f) (nDiagonal f N) := by
  haveI : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ f)
  refine ⟨1, by rw [principalDivisor_one, zero_add], nDiagonal_nonneg f N⟩

/-- A pair `(z, w)` of distinct `k`-points of `C` is not in the base locus of `|N Δ|`: it is off
the support of `N Δ ∈ |N Δ|`. -/
private theorem lift_notMem_baseLocus (N : ℕ) (z w : Spec (.of k) ⟶ C) (hz : z ≫ f = 𝟙 _)
    (hw : w ≫ f = 𝟙 _) (hzw : z ≠ w) :
    pullback.lift z w (hz.trans hw.symm) ∉
      baseLocusOfWeilDivisor (pullback.fst f f ≫ f) (nDiagonal f N) := by
  rintro ⟨-, h⟩
  obtain ⟨Z, hZ, hmem⟩ := h _ (nDiagonal_mem_completeLinearSystem f N)
  have hZΔ : Z = diagonalPrimeDivisor f := by
    by_contra hne
    rw [nDiagonal_apply, if_neg hne] at hZ
    exact lt_irrefl _ hZ
  subst hZΔ
  have hsupp : (diagonalPrimeDivisor f).support = Set.range (pullback.diagonal f) :=
    (Scheme.Hom.support_ker (pullback.diagonal f)).trans
      (pullback.diagonal f).isClosedEmbedding.isClosed_range.closure_eq
  rw [hsupp] at hmem
  obtain ⟨q, hq⟩ := hmem
  apply hzw
  refine ext_of_apply_closedPoint_eq' f hz hw ?_
  have key : ∀ g : pullback f f ⟶ C, pullback.diagonal f ≫ g = 𝟙 _ →
      (pullback.lift z w (hz.trans hw.symm) ≫ g).base (IsLocalRing.closedPoint k) = q := by
    intro g hg
    have h0 := congrArg (fun φ : C ⟶ C => φ.base q) hg
    exact (congrArg (⇑g.base) hq).symm.trans h0
  have h1 := key _ (pullback.diagonal_fst f)
  have h2 := key _ (pullback.diagonal_snd f)
  simp only [pullback.lift_fst, pullback.lift_snd] at h1 h2
  exact h1.trans h2.symm

end Diagonal

/-! ### Classes of embeddings -/

section Classes

open Stacks.SheafOfModules

/-- The class of the embedding `toProjectiveSpaceOver s hs f` defined by generating global
sections `s` of an invertible module `L` is the class of `L`. -/
private theorem embeddingClass_eq_picardClass {k : Type u} [Field k] {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of k)} [IsProjectiveVariety k f] [Smooth f] {n : ℕ}
    (φ : ProjectiveEmbedding f n) (L : Y.Modules) [hL : Stacks.Ample.IsInvertibleModule Y L]
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : Stacks.ProjectiveFromSections.GeneratesStalks s)
    (hφ : φ.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f) :
    embeddingClass f (FreeAbelianGroup.of ⟨n, φ⟩) =
      Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL) := by
  obtain ⟨α, -⟩ := Stacks.ProjectiveSpaceModuli.exists_iso_pullback_toProjectiveSpaceOver s hs f
  rw [embeddingClass_apply_of]
  refine (Y.picardClass_eq_iff _ _ _ _).mpr ⟨?_⟩
  exact (((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
    φ.hom.toLRSHom.toShHom).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction φ.hom)).app _).symm ≪≫
    (Scheme.Modules.pullbackCongr hφ).app _ ≪≫ α

end Classes

/-! ### Heights -/

section Heights

variable {k : Type u} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]

/-- The height of the generator `[φ]` of `Emb(X)` is the height of `φ`. -/
private theorem height_of {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsProjectiveVariety k f]
    [Smooth f] {n : ℕ} (φ : ProjectiveEmbedding f n) :
    EmbeddingGroup.height f (FreeAbelianGroup.of ⟨n, φ⟩) = φ.height :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Every pull-back `g^* cl(γ)` is the class of some `γ' ∈ Emb(X)`, and then `h_{γ'}` is
`h_γ ∘ g` up to a bounded function. -/
private theorem exists_embeddingClass_eq_pullback_and_abs_height_sub_le {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    [IsProjectiveVariety k fX] [Smooth fX] [IsProjectiveVariety k fY] [Smooth fY]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (γ : EmbeddingGroup fY) :
    ∃ γ' : EmbeddingGroup fX,
      embeddingClass fX γ' = Stacks.SheafOfModules.pullbackPicardHom g (embeddingClass fY γ) ∧
      ∃ C : ℝ, ∀ (x : {p : Spec (.of k) ⟶ X // p ≫ fX = 𝟙 _})
        (y : {p : Spec (.of k) ⟶ Y // p ≫ fY = 𝟙 _}), x.1 ≫ g = y.1 →
          |EmbeddingGroup.height fX γ' x - EmbeddingGroup.height fY γ y| ≤ C := by
  obtain ⟨m, n, φ, ψ, h⟩ := exists_embeddingClass_sub_eq fX
    (Stacks.SheafOfModules.pullbackPicardHom g (embeddingClass fY γ))
  have hcl : embeddingClass fX (FreeAbelianGroup.of ⟨n, ψ⟩ - FreeAbelianGroup.of ⟨m, φ⟩) =
      _ := (map_sub _ _ _).trans h
  obtain ⟨C, hC⟩ := EmbeddingGroup.exists_abs_height_sub_height_comp_le g hg γ _ hcl
  exact ⟨_, hcl, C, by rintro x ⟨_, _⟩ rfl; exact hC x⟩

/-- The arithmetic of the endgame: from `κ ≤ c a₁ + c a₂ - N b` and `aᵢ = hᵢ + O(1)`, the
combination `c/N h₁ + c/N h₂ - b` is bounded below. -/
private theorem neg_div_le_of_le_of_abs_sub_le {N c κ C₁ C₂ a₁ a₂ h₁ h₂ b : ℝ} (hN : 0 < N)
    (hc : 0 ≤ c) (hκ : κ ≤ c * a₁ + c * a₂ - N * b) (ha₁ : |a₁ - h₁| ≤ C₁)
    (ha₂ : |a₂ - h₂| ≤ C₂) :
    -((c * (C₁ + C₂) - κ) / N) ≤ c / N * h₁ + c / N * h₂ - b := by
  rw [show c / N * h₁ + c / N * h₂ - b = (c * h₁ + c * h₂ - N * b) / N by field_simp,
    ← neg_div, div_le_div_iff_of_pos_right hN]
  nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 ha₁).2 hc,
    mul_le_mul_of_nonneg_left (abs_le.1 ha₂).2 hc]

end Heights

/-- **`h_Δ` is bounded below off the diagonal.** Let `X = (C, P)` be a curve of genus `g ≥ 2`
over a field `k` algebraic over `ℚ` with a divisor `P` of degree one, let `N ≥ 2g + 1` and
`s ≥ 1`, let `φNP` be the embedding of `C` by a `k`-basis `x` of the global sections of an
invertible module `L` of class `N • [P]`, and `φB` the embedding of `C ×_k C` by a `k`-basis `y`
of the global sections of an invertible module `M` of class `vojtaClass X s s (-1)`. Then there
is `κ₄` with `-κ₄ ≤ X.vojtaHeight φNP φB s N 1 1 1 z w` for all `k`-points `z ≠ w` of `C`. -/
@[faltings "lem_bv_height_diagonal_bounded_below"]
public theorem CurveWithDegreeOneDivisor.exists_neg_le_vojtaHeight_one_one_one {k : Type u}
    [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) (s : ℤ) (hs : 1 ≤ s) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    (L : X.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule X.C L]
    (hL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (M : (pullback X.f X.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      X.vojtaClass s s (-1))
    {n m : ℕ}
    (x : letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
      Module.Basis (Fin (n + 1)) k Γ(L, ⊤))
    (hx : letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
      Stacks.ProjectiveFromSections.GeneratesStalks ⇑x)
    (y : letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
      Module.Basis (Fin (m + 1)) k Γ(M, ⊤))
    (hy : letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
      Stacks.ProjectiveFromSections.GeneratesStalks ⇑y)
    (φNP : haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
      ProjectiveEmbedding X.f n)
    (hφNP : letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
      φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx X.f)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m)
    (hφB : letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
      haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
      φB.hom =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy (pullback.fst X.f X.f ≫ X.f)) :
    ∃ κ₄ : ℝ, ∀ z w : {p : Spec (.of k) ⟶ X.C // p ≫ X.f = 𝟙 _}, z ≠ w →
      -κ₄ ≤ X.vojtaHeight φNP φB s N 1 1 1 z w := by
  haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1
  haveI := (IsSmoothProjectiveCurve.surface_pullback k X.f X.f).2.2
  haveI : Smooth (pullback.fst X.f X.f ≫ X.f) := SmoothOfRelativeDimension.smooth 2 _
  letI : X.C.Over (Spec (.of k)) := ⟨X.f⟩
  letI : (pullback X.f X.f).Over (Spec (.of k)) := ⟨pullback.fst X.f X.f ≫ X.f⟩
  obtain ⟨γ₁, hγ₁, C₁, hC₁⟩ := exists_embeddingClass_eq_pullback_and_abs_height_sub_le
    (pullback.fst X.f X.f) rfl (FreeAbelianGroup.of ⟨n, φNP⟩)
  obtain ⟨γ₂, hγ₂, C₂, hC₂⟩ := exists_embeddingClass_eq_pullback_and_abs_height_sub_le
    (pullback.snd X.f X.f) pullback.condition.symm (FreeAbelianGroup.of ⟨n, φNP⟩)
  have hγ : embeddingClass _
      ((1 + s) • γ₁ + (1 + s) • γ₂ - (N : ℤ) • FreeAbelianGroup.of ⟨m, φB⟩) =
      picardClassOfWeilDivisor (pullback.fst X.f X.f ≫ X.f) (nDiagonal X.f N) := by
    rw [picardClassOfWeilDivisor_nDiagonal, map_sub, map_add, map_zsmul, map_zsmul, map_zsmul,
      hγ₁, hγ₂, (embeddingClass_eq_picardClass φB M y hy hφB).trans hM,
      (embeddingClass_eq_picardClass φNP L x hx hφNP).trans hL,
      ← schemePullbackClassHom_eq_pullbackPicardHom,
      ← schemePullbackClassHom_eq_pullbackPicardHom, CurveWithDegreeOneDivisor.vojtaClass,
      map_zsmul, map_zsmul]
    module
  have hN1 : 1 ≤ N := (Nat.le_add_left 1 _).trans hN
  obtain ⟨κ, hκ⟩ := EmbeddingGroup.exists_le_height_of_not_mem_baseLocus
    (nDiagonal_pos X.f N hN1) hγ
  refine ⟨((1 + s : ℤ) * (C₁ + C₂) - κ) / N, fun z w hzw => ?_⟩
  let p : {p : Spec (.of k) ⟶ pullback X.f X.f // p ≫ pullback.fst X.f X.f ≫ X.f = 𝟙 _} :=
    ⟨pullback.lift z.1 w.1 (z.2.trans w.2.symm), by rw [pullback.lift_fst_assoc, z.2]⟩
  have hκp := hκ p (lift_notMem_baseLocus X.f N z.1 w.1 z.2 w.2 fun h => hzw (Subtype.ext h))
  simp only [map_sub, map_add, map_zsmul, Pi.add_apply, Pi.sub_apply,
    zsmul_eq_mul, height_of, Int.cast_natCast] at hκp
  simp only [CurveWithDegreeOneDivisor.vojtaHeight, mul_one, Int.cast_one, one_mul]
  exact neg_div_le_of_le_of_abs_sub_le (by exact_mod_cast hN1) (by exact_mod_cast (by omega))
    hκp (height_of φNP ▸ hC₁ p z (pullback.lift_fst _ _ _))
    (height_of φNP ▸ hC₂ p w (pullback.lift_snd _ _ _))

end Faltings
