module

public import Mathlib
public import Mordell.AlgebraicGeometry.LinearSystem
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.CompositePullback
public import Mordell.Height.Machine.ClassZero
public import Mordell.Height.Machine.EmbeddingClassSurjective
public import Mordell.Height.Machine.PositivityOffZeros
public import Mordell.AlgebraicGeometry.VeryAmple.Twist
public import Mordell.AlgebraicGeometry.FiniteGlobalSections
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.CompositeEmbedding
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic

/-!
# Weil's theorem: positivity

Let `X` be a smooth projective variety over a field `k` algebraic over `ℚ` (in the source,
`k = ℚ̄`), `A > 0` an effective Weil divisor on `X`, and `α ∈ Emb(X)` a formal combination of
projective embeddings whose class `cl(α) ∈ Pic(X)` is the class `cl(A) = [𝒪_X(A)]`. Then the
height `h_α` is bounded below on the `k`-points of `X` outside the base locus of `|A|`.

## Main results

* `Faltings.EmbeddingGroup.exists_le_height_of_not_mem_baseLocus`: Weil's positivity theorem.

## Implementation notes

A `k`-point of `X` is a section `p` of the structure morphism `f : X ⟶ Spec k`. "Bounded
below off the base locus" is stated as the existence of `C : ℝ` with `C ≤ h_α(p)` for every
`k`-point `p` not in `Faltings.baseLocusOfWeilDivisor f A`.

The proof follows Bombieri. Write `L = 𝒪_X(A)`. Fix a projective embedding `φ₀` with
`L₀ = φ₀^* 𝒪(1)`, choose `a ≥ 1` with `L ⊗ L₀^{⊗ a} ≅ ψ^* 𝒪(1)` very ample, and let `φ` be the
Veronese composite of degree `a` of `φ₀`, so that `ψ^* 𝒪(1) ≅ L ⊗ φ^* 𝒪(1)`. For a basis
`s₀, …, s_r` of the finite-dimensional space `H⁰(X, L)`, `h_ψ - h_φ` is bounded below on the
nonvanishing locus of each `sᵢ`, and `h_α - (h_ψ - h_φ)` is bounded since `α - ψ + φ` has class
zero. A point outside the base locus lies off the support of some `D ∈ |A|`; the canonical section
of `𝒪_X(D) ≅ L` does not vanish there, so neither does some `sᵢ`.

`𝒪_X(D)` for an effective divisor `D` is `Stacks.Divisors.modulesInvertibleSheaf` of
`AlgebraicGeometry.positiveWeilIdeal D`. Its class in `Pic(X)` is identified with
`Faltings.picardClassOfWeilDivisor f D`, and linearly equivalent divisors get the same class,
through the injectivity of the first Chern class `Pic(X) → Cl(X)` on the normal scheme `X`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2, Weil's Theorem (iii)
* [M. Hindry, *Géométrie et hauteurs dans les groupes algébriques*][hindry1992], Sec. 2, H4
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Faltings

section Divisors

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProjectiveVariety k f] [Smooth f]

/-- The first Chern class sends `Faltings.picardClassOfWeilDivisor f D` to the class of `D`. -/
private lemma picardToWeil_picardClassOfWeilDivisor (D : WeilDivisor X) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    picardToWeilDivisorClassGroup X (picardClassOfWeilDivisor f D) =
      (D : weilDivisorClassGroup X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := uniqueFactorizationMonoid_stalk_of_smooth f
  have h : ∀ E : WeilDivisor X,
      haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal E) :=
        positiveWeilIdeal_isEffectiveCartierDivisor hX E
      picardToWeilDivisorClassGroup X (X.picardClass
        (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal E))
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf _)) =
        (positiveWeilDivisor E : weilDivisorClassGroup X) := by
    intro E
    have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal E) :=
      positiveWeilIdeal_isEffectiveCartierDivisor hX E
    exact (weilDivisorClassOfPicardClass_picardClass X _).trans
      (weilDivisorClassOfInvertibleSheaf_positiveWeilIdeal hX E)
  let F : X.picardGroup →+ weilDivisorClassGroup X := picardToWeilDivisorClassGroup X
  change F (_ - _) = _
  rw [map_sub]
  refine (congrArg₂ (· - ·) (h D) (h (-D))).trans ?_
  rw [← QuotientAddGroup.mk_sub, positiveWeilDivisor_sub_neg]

/-- The first Chern class of `X` is injective. -/
private lemma picardToWeil_injective :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Function.Injective (picardToWeilDivisorClassGroup X : X.picardGroup →+ _) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := uniqueFactorizationMonoid_stalk_of_smooth f
  have : IsNormal X :=
    { stalk_isDomain := fun _ => inferInstance
      stalk_normal := fun x => by
        have := hX x; exact UniqueFactorizationMonoid.instIsIntegrallyClosed }
  exact picardToWeilDivisorClassGroup_injective X

/-- For an effective divisor `D`, the class of `𝒪_X(D)` is `Faltings.picardClassOfWeilDivisor`. -/
private lemma picardClass_modulesInvertibleSheaf (D : WeilDivisor X) (hD : 0 ≤ D) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
      positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) D
    X.picardClass (Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal D))
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf _) =
      picardClassOfWeilDivisor f D := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := uniqueFactorizationMonoid_stalk_of_smooth f
  have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
    positiveWeilIdeal_isEffectiveCartierDivisor hX D
  apply picardToWeil_injective f
  have hpos : positiveWeilDivisor D = D := by
    refine Subtype.ext (funext fun Z => ?_)
    rw [positiveWeilDivisor_apply, Int.toNat_of_nonneg (hD Z)]
  refine ((weilDivisorClassOfPicardClass_picardClass X _).trans
      (weilDivisorClassOfInvertibleSheaf_positiveWeilIdeal hX D)).trans ?_
  rw [hpos]
  exact (picardToWeil_picardClassOfWeilDivisor f D).symm

/-- Members of the complete linear system `|A|` have the class of `A`. -/
private lemma picardClassOfWeilDivisor_eq_of_mem {A D : WeilDivisor X}
    (hD : D ∈ completeLinearSystemOfWeilDivisor f A) :
    picardClassOfWeilDivisor f D = picardClassOfWeilDivisor f A := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨g, rfl, -⟩ := hD
  apply picardToWeil_injective f
  rw [picardToWeil_picardClassOfWeilDivisor, picardToWeil_picardClassOfWeilDivisor,
    QuotientAddGroup.mk_add, (mk_eq_zero_iff X _).2 ⟨g, rfl⟩, zero_add]

end Divisors

/-- A point off the prime divisors with positive coefficient in `D` is off the support of the
ideal sheaf `positiveWeilIdeal D`. -/
private lemma notMem_supportSet_positiveWeilIdeal {X : Scheme.{u}} (D : WeilDivisor X) (x : X)
    (hx : ∀ Z : PrimeDivisor X, 0 < D.val Z → x ∉ Z.support) :
    x ∉ (positiveWeilIdeal D).supportSet := by
  classical
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    ← IdealSheafData.stalk_eq_top_iff_notMem_support]
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨W, hW⟩ hxW, positiveWeilIdeal_ideal,
    show Ideal.map (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 x hxW).hom
        (∏ V ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          V.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val V).toNat) =
        ∏ V ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          (V.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val V).toNat).map
            (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 x hxW).hom from
      map_prod (Ideal.mapHom _) _ _, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun V _ => ?_
  rw [Ideal.map_pow, ← IdealSheafData.stalk_eq_map_germ V.idealSheaf x ⟨W, hW⟩ hxW]
  rcases le_or_gt (D.val V) 0 with hV | hV
  · rw [Int.toNat_of_nonpos hV, pow_zero]
  · rw [IdealSheafData.stalk_eq_top_of_notMem_support V.idealSheaf (hx V hV), Ideal.top_pow,
      Ideal.one_eq_top]

/-- The canonical section of `𝒪_X(I)` does not vanish off the support of `I`. -/
private lemma mem_nonvanishingLocus_canonicalSections {X : Scheme.{u}} (I : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] {x : X} (hx : x ∉ I.supportSet) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Divisors.modulesInvertibleSheaf I)
      ((Stacks.Divisors.canonicalSections I).eval (Opposite.op ⊤)) := by
  rw [← Stacks.SchemeModulesSpelling.nonvanishingLocus_eq,
    Stacks.Divisors.nonvanishingLocus_canonicalSections]
  exact hx

/-- A finite linear combination of sections only fails to vanish where one of them does. -/
private lemma nonvanishingLocus_sum_subset {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    (s : Finset ι) (c : ι → Γ(X, ⊤)) (t : ι → Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus M (∑ i ∈ s, c i • t i) ⊆
      ⋃ i ∈ s, Stacks.Ample.nonvanishingLocus M (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    refine (Stacks.Ample.nonvanishingLocus_add_subset M _ _).trans ?_
    rw [Finset.set_biUnion_insert]
    exact Set.union_subset_union (Stacks.Ample.nonvanishingLocus_smul_subset M _ _) ih

/-- A section of `𝒪_X(A)` that does not vanish at `x`, for `x` off the support of some
`D ∈ |A|`: the canonical section of `𝒪_X(D) ≅ 𝒪_X(A)`. -/
private lemma exists_mem_nonvanishingLocus_of_mem_completeLinearSystem {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f]
    {A D : WeilDivisor X} (hA : 0 ≤ A) (hD : D ∈ completeLinearSystemOfWeilDivisor f A) {x : X}
    (hx : ∀ Z : PrimeDivisor X, 0 < D.val Z → x ∉ Z.support) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal A) :=
      positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) A
    ∃ t : Γ(Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal A), ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus _ t := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := uniqueFactorizationMonoid_stalk_of_smooth f
  have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal A) :=
    positiveWeilIdeal_isEffectiveCartierDivisor hX A
  have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal D) :=
    positiveWeilIdeal_isEffectiveCartierDivisor hX D
  obtain ⟨ι⟩ := (X.picardClass_eq_iff _ _ (Stacks.Divisors.isTensorInvertible_invertibleSheaf _)
    (Stacks.Divisors.isTensorInvertible_invertibleSheaf _)).1
    ((picardClass_modulesInvertibleSheaf f D (hD.choose_spec.2)).trans
      ((picardClassOfWeilDivisor_eq_of_mem f hD).trans
        (picardClass_modulesInvertibleSheaf f A hA).symm))
  exact ⟨_, (Set.ext_iff.mp (Stacks.Ample.nonvanishingLocus_congr ι _) _).2
    (mem_nonvanishingLocus_canonicalSections _ (notMem_supportSet_positiveWeilIdeal D x hx))⟩

/-- If some section of `M` does not vanish at `x`, neither does some member of a basis of
`Γ(M, ⊤)` over a ring `R` acting through `φ : R →+* Γ(X, ⊤)`. -/
private lemma exists_basis_mem_nonvanishingLocus {X : Scheme.{u}} (M : X.Modules) {R ι : Type*}
    [CommRing R] [Module R Γ(M, ⊤)] (φ : R →+* Γ(X, ⊤))
    (hφ : ∀ (c : R) (t : Γ(M, ⊤)), c • t = φ c • t)
    (b : Module.Basis ι R Γ(M, ⊤)) {x : X} {t : Γ(M, ⊤)}
    (hx : x ∈ Stacks.Ample.nonvanishingLocus M t) :
    ∃ j, x ∈ Stacks.Ample.nonvanishingLocus M (b j) := by
  have ht : ∑ j ∈ (b.repr t).support, φ (b.repr t j) • b j = t := by
    simp_rw [← hφ]
    exact (Finsupp.linearCombination_apply R _).symm.trans (b.linearCombination_repr t)
  obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1
    (nonvanishingLocus_sum_subset M _ (fun j => φ (b.repr t j)) b (ht ▸ hx))
  exact ⟨j, hj⟩

/-- The monomials of degree `e` in `n + 1` variables can be indexed by `Fin (N + 1)`. -/
private lemma exists_equiv_fin_degree_eq (n e : ℕ) :
    ∃ N : ℕ, Nonempty ({I : Fin (n + 1) →₀ ℕ // I.degree = e} ≃ Fin (N + 1)) := by
  have : Finite {I : Fin (n + 1) →₀ ℕ // I.degree = e} := by
    refine Set.Finite.to_subtype (s := {I : Fin (n + 1) →₀ ℕ | I.degree = e}) ?_
    convert ((Finset.univ : Finset (Fin (n + 1))).finsuppAntidiag e).finite_toSet
    ext I; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  obtain ⟨_ | N, ⟨τ⟩⟩ := Finite.exists_equiv_fin {I : Fin (n + 1) →₀ ℕ // I.degree = e}
  · exact (τ ⟨Finsupp.single 0 e, Finsupp.degree_single 0 e⟩).elim0
  · exact ⟨N, ⟨τ⟩⟩

/-- For an invertible sheaf `L` on `X`, there are projective embeddings `ψ` and `φ` of `X` with
`ψ^* 𝒪(1) ≅ L ⊗ φ^* 𝒪(1)`. -/
private lemma exists_projectiveEmbedding_pullback_iso_tensorModules {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    ∃ (m : ℕ) (ψ : ProjectiveEmbedding f m) (N : ℕ) (φ : ProjectiveEmbedding f N),
      Nonempty ((Scheme.Modules.pullback ψ.hom).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf m (Spec (.of k))) ≅
        Stacks.RelativeVeryAmple.tensorModules X L ((Scheme.Modules.pullback φ.hom).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))))) := by
  -- a projective embedding `φ₀` and `L₀ = φ₀^* 𝒪(1)`
  obtain ⟨n₀, i, hi, hif⟩ := (inferInstance : IsProjectiveVariety k f).isProjective
  let φ₀ : ProjectiveEmbedding f n₀ := ⟨i, hi, hif⟩
  let L₀ := (Scheme.Modules.pullback φ₀.hom).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n₀ (Spec (.of k)))
  have hL₀ : IsVeryAmple f L₀ := ⟨n₀, φ₀, ⟨Iso.refl _⟩⟩
  obtain ⟨a, ⟨m, ψ, ⟨e₁⟩⟩, ha⟩ :=
    ((eventually_isVeryAmple_tensorModules_tensorPowModule f L₀ hL₀ L).and
      (Filter.eventually_ge_atTop 1)).exists
  -- the Veronese composite `φ` of degree `e = a` of `φ₀`
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, (e : ℤ) = a := ⟨a.toNat, Int.toNat_of_nonneg (by omega)⟩
  have he : 1 ≤ e := by exact_mod_cast ha
  obtain ⟨N, ⟨σ⟩⟩ := exists_equiv_fin_degree_eq n₀ e
  obtain ⟨V, φ, hV, hφ⟩ := ProjectiveEmbedding.exists_veronese φ₀ e he N σ
  obtain ⟨e₂⟩ := nonempty_pullback_veronese_projectiveSpaceTwistingSheaf_iso e he N σ V hV
    φ₀.hom φ.hom hφ
  exact ⟨m, ψ, N, φ,
    ⟨e₁.symm ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl L) e₂.symm⟩⟩

/-- A `k`-point of `X` off the base locus of `|A|` maps into the nonvanishing locus of some
member of any `k`-basis of the global sections of `𝒪_X(A)`. -/
private lemma exists_basis_range_subset_nonvanishingLocus {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] [Smooth f]
    {A : WeilDivisor X} (hA : 0 ≤ A) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal A) :=
      positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) A
    ∀ {ι : Type} [Module k Γ(Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal A), ⊤)],
      (∀ (c : k) (t : Γ(Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal A), ⊤)),
        c • t = (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) c • t) →
      ∀ (b : Module.Basis ι k Γ(Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal A), ⊤))
        (p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _}), p.1 ∉ baseLocusOfWeilDivisor f A →
        ∃ j, Set.range p.1.base ⊆ Stacks.Ample.nonvanishingLocus _ (b j) := by
  intro ι _ hsmul b p hp
  obtain ⟨D, hD, hDx⟩ : ∃ D ∈ completeLinearSystemOfWeilDivisor f A, ∀ Z : PrimeDivisor X,
      0 < D.val Z → p.1.base (IsLocalRing.closedPoint k) ∉ Z.support := by
    by_contra h
    push Not at h
    exact hp ⟨p.2, h⟩
  obtain ⟨t, ht⟩ := exists_mem_nonvanishingLocus_of_mem_completeLinearSystem f hA hD hDx
  obtain ⟨j, hj⟩ := exists_basis_mem_nonvanishingLocus _ _ hsmul b ht
  refine ⟨j, ?_⟩
  rintro _ ⟨y, rfl⟩
  rwa [Subsingleton.elim y (IsLocalRing.closedPoint k)]

/-- **Weil's theorem** (positivity): if `A > 0` is an effective nonzero Weil divisor on `X` and
`α ∈ Emb(X)` has `Faltings.embeddingClass f α = Faltings.picardClassOfWeilDivisor f A`, then the
height `Faltings.EmbeddingGroup.height f α` is bounded below on the `k`-points of `X` outside
`Faltings.baseLocusOfWeilDivisor f A`. -/
@[faltings "thm_ht_weil_positivity"]
public theorem EmbeddingGroup.exists_le_height_of_not_mem_baseLocus {k : Type u} [Field k]
    [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    [IsProjectiveVariety k f] [Smooth f] {A : AlgebraicGeometry.WeilDivisor X}
    (hA : 0 < A) {α : EmbeddingGroup f}
    (hα : embeddingClass f α = picardClassOfWeilDivisor f A) :
    ∃ C : ℝ, ∀ p : {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _},
      p.1 ∉ baseLocusOfWeilDivisor f A → C ≤ EmbeddingGroup.height f α p := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Stacks.Divisors.IsEffectiveCartierDivisor (positiveWeilIdeal A) :=
    positiveWeilIdeal_isEffectiveCartierDivisor (uniqueFactorizationMonoid_stalk_of_smooth f) A
  set L := Stacks.Divisors.modulesInvertibleSheaf (positiveWeilIdeal A)
  have hL : Stacks.Ample.IsInvertibleModule X L :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  have hLc : X.picardClass L hL = picardClassOfWeilDivisor f A :=
    picardClass_modulesInvertibleSheaf f A hA.le
  obtain ⟨m, ψ, N, φ, ⟨e₃⟩⟩ := exists_projectiveEmbedding_pullback_iso_tensorModules f L
  -- `α - ψ + φ` has class zero, so its height is bounded
  obtain ⟨C', hC'⟩ := EmbeddingGroup.exists_abs_height_le_of_embeddingClass_eq_zero
    (γ := α - FreeAbelianGroup.of ⟨m, ψ⟩ + FreeAbelianGroup.of ⟨N, φ⟩) (by
      rw [map_add, map_sub, hα, embeddingClass_apply_of_eq_picardClass,
        embeddingClass_apply_of_eq_picardClass,
        (X.picardClass_eq_iff _ _ _ inferInstance).2 ⟨e₃⟩, picardClass_tensorModules, hLc]
      have key : ∀ {G : Type (u + 1)} [AddCommGroup G] (a p : G), a - (a + p) + p = 0 := by
        intros; abel
      exact key _ _)
  have hγ : ∀ p, EmbeddingGroup.height f (α - FreeAbelianGroup.of ⟨m, ψ⟩ +
      FreeAbelianGroup.of ⟨N, φ⟩) p = EmbeddingGroup.height f α p - ψ.height p + φ.height p := by
    intro p
    simp [EmbeddingGroup.height, FreeAbelianGroup.lift_apply_of]
  -- a basis of `H⁰(X, L)` and the constants of positivity off each basis section
  let ι : k →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Module k Γ(L, ⊤) := Module.compHom Γ(L, ⊤) ι
  have : FiniteDimensional k Γ(L, ⊤) := finiteDimensional_sections_of_isProper k f L
    ((isInvertible_iff_exists_restrict_iso_unit X L).mp hL)
  let b := Module.finBasis k Γ(L, ⊤)
  choose Cs hCs using fun j =>
    ProjectiveEmbedding.exists_height_sub_le_height_of_mem_nonvanishingLocus L (b j) φ ψ e₃
  refine ⟨-C' - ∑ j, |Cs j|, fun p hp => ?_⟩
  obtain ⟨j, hj⟩ :=
    exists_basis_range_subset_nonvanishingLocus f hA.le (fun _ _ => rfl) b p hp
  have hγp := (abs_le.1 (hC' p)).1
  rw [hγ] at hγp
  linarith [hCs j p hj, (le_abs_self (Cs j)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (Cs j)) (Finset.mem_univ j))]

end Faltings
