module
public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethQcqs

/-!
# The Euler characteristic of a box product on a product of curves

Let `k` be a field and `C`, `D` smooth projective curves over `k`, of genera `g` and `h`, with
projections `pr₁ : C ×_k D ⟶ C` and `pr₂ : C ×_k D ⟶ D`. For invertible modules `𝒜` on `C` and
`ℬ` on `D`, of degrees `a` and `b`, the Euler characteristic of the box product is

`χ(C ×_k D, pr₁^* 𝒜 ⊗ pr₂^* ℬ) = (a + 1 - g) (b + 1 - h)`.

It is the product of `χ(C, 𝒜) = a + 1 - g` and `χ(D, ℬ) = b + 1 - h` by the Künneth formula.
The case `D = C`, `𝒜 = ℬ = 𝒪_C` gives `χ(𝒪_{C × C}) = (1 - g)²`.

## Main results

* `Faltings.eulerCharacteristic_externalTensorProduct_of_isSmoothProjectiveCurve`: the formula
  above.

## Implementation notes

The box product is `AlgebraicGeometry.externalTensorProduct f g A B`, the tensor product over
`𝒪_{C ×_k D}` of the pullbacks of `A` and `B` along `pullback.fst f g` and `pullback.snd f g`.
The Euler characteristic is `AlgebraicGeometry.eulerCharacteristic` for the structure morphism
`pullback.fst f g ≫ f`; it requires the module to be coherent, which is supplied inside the
statement from the coherence of invertible modules on the locally Noetherian curves, of their
pullbacks, and of a tensor product of coherent modules. The degree is
`AlgebraicGeometry.invertibleCurveDegree` and the genus `AlgebraicGeometry.genus`. The
statement is for two curves; the product `C × C` is the case `g = f`.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 3
* [Stacks Project, Tag 0BEF], [Stacks Project, Tag 0BEJ], [Stacks Project, Tag 0AYR]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DirectSum Finset.HasAntidiagonal

universe u

namespace Faltings

/-- The dimension of `⨁_{p + q = n} Mₚ ⊗ N_q` is `∑_{p + q = n} dim Mₚ · dim N_q`. -/
private lemma finrank_directSum_antidiagonal_tensorProduct (k : Type u) [Field k]
    (M N : ℕ → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] [∀ i, FiniteDimensional k (M i)]
    [∀ i, FiniteDimensional k (N i)] (n : ℕ) :
    Module.finrank k (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        TensorProduct k (M pq.1.1) (N pq.1.2)) =
      ∑ pq ∈ antidiagonal n, Module.finrank k (M pq.1) * Module.finrank k (N pq.2) := by
  letI : Fintype {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
    Fintype.subtype (antidiagonal n) (by simp)
  rw [Module.finrank_directSum]
  simp only [Module.finrank_tensorProduct]
  exact (Finset.sum_subtype _ (by simp)
    (fun pq : ℕ × ℕ => Module.finrank k (M pq.1) * Module.finrank k (N pq.2))).symm

/-- The alternating sum of a Cauchy product of two sequences supported in degrees `0, 1`
is the product of their alternating sums. -/
private lemma finsum_alternating_antidiagonal (a b : ℕ → ℤ) (ha : ∀ n, 2 ≤ n → a n = 0)
    (hb : ∀ n, 2 ≤ n → b n = 0) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ∑ pq ∈ antidiagonal n, a pq.1 * b pq.2 =
      (a 0 - a 1) * (b 0 - b 1) := by
  have h3 : ∀ n, 3 ≤ n → ∑ pq ∈ antidiagonal n, a pq.1 * b pq.2 = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun pq hpq => ?_
    rw [mem_antidiagonal] at hpq
    rcases le_or_gt 2 pq.1 with h | h
    · rw [ha _ h, zero_mul]
    · rw [hb pq.2 (by omega), mul_zero]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, ha 2 le_rfl, hb 2 le_rfl]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra h
    exact hn (by rw [h3 n (by omega)]; simp)

/-- **The Künneth formula in dimensions.** For quasi-compact quasi-separated `X`, `Y` over `k`
and quasi-coherent `F`, `G` with finite-dimensional cohomology,
`hⁿ(X ×_k Y, F ⊠ G) = ∑_{p + q = n} hᵖ(X, F) hᑫ(Y, G)`. -/
private lemma finrank_cohomologyOverField_externalTensorProduct (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    [∀ p, FiniteDimensional k (cohomologyOverField k f F p)]
    [∀ q, FiniteDimensional k (cohomologyOverField k g G q)] (n : ℕ) :
    Module.finrank k
        (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorProduct f g F G) n) =
      ∑ pq ∈ antidiagonal n, Module.finrank k (cohomologyOverField k f F pq.1) *
        Module.finrank k (cohomologyOverField k g G pq.2) := by
  rw [(KunnethQcqs.kunnethIso f g F G n).toLinearEquiv.finrank_eq]
  exact finrank_directSum_antidiagonal_tensorProduct k (cohomologyOverField k f F ·)
    (cohomologyOverField k g G ·) n

/-- On a proper scheme of dimension at most one over `k`, `hⁿ = 0` for `n ≥ 2`. -/
private lemma finrank_cohomologyOverField_eq_zero_of_two_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) (n : ℕ) (hn : 2 ≤ n) :
    (Module.finrank k (cohomologyOverField k f F n) : ℤ) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_two_le k f hdim F n hn)
  simp [Module.finrank_zero_of_subsingleton]

/-- **Euler characteristic of a box product.** For smooth projective curves
`f : C ⟶ Spec k` and `g : D ⟶ Spec k` and invertible modules `A` on `C`, `B` on `D`,
`χ(C ×_k D, pr₁^* A ⊗ pr₂^* B) = (deg A + 1 - genus f) * (deg B + 1 - genus g)`, with
`deg = AlgebraicGeometry.invertibleCurveDegree`. -/
@[faltings "lem_nt_euler_box_product"]
public theorem eulerCharacteristic_externalTensorProduct_of_isSmoothProjectiveCurve
    (k : Type u) [Field k] {C D : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (g : D ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k g]
    (A : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 A]
    (B : D.Modules) [SheafOfModules.IsInvertible D.presheaf D.ringCatSheaf.2 B] :
    haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
    haveI : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian g
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f)
    haveI : A.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible C A
    haveI : B.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible D B
    haveI : (externalTensorProduct f g A B).IsCoherent :=
      @SheafOfModules.tensorSheaf_isCoherent (pullback f g).toRingedSpace
        ((Scheme.Modules.pullback (pullback.fst f g)).obj A)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj B)
        (isCoherent_pullback _ A) (isCoherent_pullback _ B)
    eulerCharacteristic k (pullback.fst f g ≫ f) (externalTensorProduct f g A B) =
      (invertibleCurveDegree k f (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f) A +
          1 - genus f) *
        (invertibleCurveDegree k g (topologicalKrullDim_le_one_of_smoothOfRelativeDimension g) B +
          1 - genus g) := by
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : A.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible C A
  haveI : B.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible D B
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k f
  haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) :=
    isIso_globalSections_of_geometricallyIntegral k g
  haveI := finiteDimensional_cohomologyOverField_of_isProper k f A
  haveI := finiteDimensional_cohomologyOverField_of_isProper k g B
  have hdf := topologicalKrullDim_le_one_of_smoothOfRelativeDimension f
  have hdg := topologicalKrullDim_le_one_of_smoothOfRelativeDimension g
  unfold eulerCharacteristic
  simp_rw [finrank_cohomologyOverField_externalTensorProduct k f g A B]
  push_cast
  rw [finsum_alternating_antidiagonal _ _
      (finrank_cohomologyOverField_eq_zero_of_two_le k f hdf A)
      (finrank_cohomologyOverField_eq_zero_of_two_le k g hdg B),
    finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdf A,
    finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k g hdg B]

end Faltings
