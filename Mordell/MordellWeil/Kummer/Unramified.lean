module

public import Mordell.AbelianVariety.GoodReduction
public import Mordell.AlgebraicGeometry.GeometricPoint.Galois
public import Mordell.MordellWeil.Kummer.PointField
public import Mordell.AbelianVariety.Reduction.Galois
public import Mordell.AbelianVariety.Reduction.Basic
public import Mordell.AbelianVariety.Reduction.Torsion

/-!
# Kummer extensions are unramified at good places prime to `m`

Let `k` be a number field, `k̄` an algebraic closure of `k`, `A` an abelian variety over `k` and
`m ≥ 1`, and assume that the `m`-torsion `A(k̄)[m]` is contained in `A(k)`. Let `𝔭` be a finite
place of `k` not dividing `m` at which `A` has good reduction. If `Q ∈ A(k̄)` has `m Q ∈ A(k)`,
then the field of definition `k(Q)` is unramified over `k` at `𝔭`: every prime `𝔓` of the ring
of integers of `k(Q)` lying over `𝔭` has ramification index `e(𝔓 | 𝔭) = 1`.

The proof shows the inertia group of `𝔓` is trivial: an inertia element `σ` fixes the reduction
of every point of `A(k(Q))` modulo `𝔓`, so `σ Q - Q` is an `m`-torsion point with trivial
reduction, hence zero since `m` is invertible at `𝔓`; thus `σ` fixes `Q` and so is trivial on
`k(Q)`.

## Main results

* `Faltings.ramificationIdx_fieldOfDefinition_eq_one_of_pow_mem`: `e(𝔓 | 𝔭) = 1` for every prime
  `𝔓` of `𝓞 k(Q)` over `𝔭`.

## Implementation notes

An abelian variety over `k` is an object `A` of `Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral. The points `A(k̄)` are
the morphisms `Over.mk (Spec (k → k̄)) ⟶ A`, a group written multiplicatively, so `m Q` is
`Q ^ m`; the `k`-points `A(k)` are the morphisms `Over.mk (𝟙 (Spec k)) ⟶ A`, and `A(k) → A(k̄)`
is precomposition with the morphism `Spec k̄ ⟶ Spec k` over `Spec k`. The field `k(Q)` is
`Faltings.fieldOfDefinition Q.left`. A finite place is a term of
`IsDedekindDomain.HeightOneSpectrum (𝓞 k)`, and `𝔭 ∤ m` is `(m : 𝓞 k) ∉ 𝔭`. The ramification
index is Mathlib's `Ideal.ramificationIdx` of `𝔓` over `𝓞 k`, which for `𝔓` lying over `𝔭` is
`e(𝔓 | 𝔭)`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VIII.1.5(b)
* J.-P. Serre, J. Tate, *Good reduction of abelian varieties*, §1, Theorem 1
* J. S. Milne, *Abelian varieties*, IV.3.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MonoidalCategory
open scoped MonObj

universe u

namespace Faltings

section Points

variable {X Y : Scheme.{u}}

/-- Points with two equal structure morphisms are the same group. -/
private noncomputable def overMkPointsMulEquiv {S : Scheme.{u}} {a b : S ⟶ Y} (h : a = b)
    (M : Over Y) [MonObj M] : (Over.mk a ⟶ M) ≃* (Over.mk b ⟶ M) where
  toFun P := Over.homMk (U := Over.mk b) (V := Over.mk a) (𝟙 S) (by simp [h]) ≫ P
  invFun P := Over.homMk (U := Over.mk a) (V := Over.mk b) (𝟙 S) (by simp [h]) ≫ P
  left_inv P := by ext; simp
  right_inv P := by ext; simp
  map_mul' P P' := MonObj.comp_mul _ _ _

private lemma overMkPointsMulEquiv_left {S : Scheme.{u}} {a b : S ⟶ Y} (h : a = b)
    (M : Over Y) [MonObj M] (P : Over.mk a ⟶ M) : (overMkPointsMulEquiv h M P).left = P.left := by
  simp [overMkPointsMulEquiv]

end Points

/-- Let `𝒜₀` be a group scheme over `R₀` whose base change to `k` is `A`, and `R₀ → R → L`,
`R₀ → k → L` a commutative square. Then `A(L)` embeds as a group into the `L`-points of the
generic fibre of `𝒜₀ ×_{R₀} R`, compatibly with the projections to `𝒜₀`. -/
private lemma exists_monoidHom_points_genericFibre {k L R₀ R : Type u} [Field k] [Field L]
    [CommRing R₀] [CommRing R] [Algebra k L] [Algebra R₀ k] [Algebra R₀ R] [Algebra R L]
    (h : (algebraMap R L).comp (algebraMap R₀ R) = (algebraMap k L).comp (algebraMap R₀ k))
    (𝒜₀ : Grp (Over (Spec (CommRingCat.of R₀)))) (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
    (e₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ k)))).mapGrp.obj 𝒜₀ ≅
      Grp.mk A) :
    ∃ α : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ A) →*
        (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
              𝒜₀)).X),
      Function.Injective α ∧ ∀ Q, (α Q).left ≫ Limits.pullback.fst _ _ ≫
        Limits.pullback.fst _ _ = Q.left ≫ e₀.inv.hom.hom.left ≫ Limits.pullback.fst _ _ := by
  have hs : (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R₀ k)) := by
    simp only [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  let β := ((mapPullbackAdjMulEquiv (Spec.map (CommRingCat.ofHom (algebraMap R L)))
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀)
    (𝟙_ _)).symm.trans
    (mapPullbackAdjMulEquiv (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) 𝒜₀ _).symm).trans
    (overMkPointsMulEquiv hs 𝒜₀.X)
  let ε := (mapPullbackAdjMulEquiv (Spec.map (CommRingCat.ofHom (algebraMap R₀ k))) 𝒜₀
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))).symm
  let α' := IsMonHom.monoidHom e₀.inv.hom.hom
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  have hβ (P : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀)).X) :
      (β P).left = P.left ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ := by
    simp only [β, MulEquiv.trans_apply]
    erw [overMkPointsMulEquiv_left, mapPullbackAdjMulEquiv_symm_left,
      mapPullbackAdjMulEquiv_symm_left, Category.assoc]
  have he : e₀.inv.hom.hom ≫ e₀.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) e₀.inv_hom_id
  refine ⟨β.symm.toMonoidHom.comp (ε.toMonoidHom.comp α'), ?_, fun Q => ?_⟩
  · refine β.symm.injective.comp (ε.injective.comp fun Q₁ Q₂ hQ => ?_)
    have := congrArg (· ≫ e₀.hom.hom.hom) hQ
    simpa [α', IsMonHom.monoidHom, he] using this
  · rw [← hβ]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply, ε, mapPullbackAdjMulEquiv_symm_left]
    simp only [α', IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk, Over.comp_left]
    exact Category.assoc _ _ _

/-- Let `R` be a discrete valuation ring with fraction field `L`, `𝒜₀` an abelian scheme over
`R₀`, `𝒜 = 𝒜₀ ×_{R₀} R` and `τ` an `R₀`-automorphism of `R` acting trivially on the residue
field. If two `L`-points `P, P'` of the generic fibre of `𝒜` satisfy `P' = P ∘ Spec τ_L` as
morphisms to `𝒜₀`, and `P' - P` is `n`-torsion with `n` invertible in `R`, then `P' = P`. -/
private lemma eq_of_comp_spec_map_of_pow_eq_one (R₀ R L : Type u) [CommRing R₀]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R₀ R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (𝒜₀ : Grp (Over (Spec (CommRingCat.of R₀))))
    [Flat 𝒜₀.X.hom] [IsProper 𝒜₀.X.hom] [LocallyOfFinitePresentation 𝒜₀.X.hom]
    (hfib₀ : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜₀.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜₀.X).hom)
    [Flat ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
      𝒜₀).X.hom]
    [IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
      𝒜₀).X.hom]
    [LocallyOfFinitePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀).X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
          𝒜₀).X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj
          𝒜₀).X).hom)
    (τ : R ≃ₐ[R₀] R) (hτ : ∀ x, IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv x = x)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (P P' : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀)).X)
    (hP : P'.left ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
          (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.toRingEquiv).toRingHom) ≫
        P.left ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
    (htors : (P' * P⁻¹) ^ n = 1) : P' = P := by
  have hc := reductionMap_comp_spec_map_residueFieldMapEquiv R₀ R L 𝒜₀ hfib₀ τ P P' hP
  have hid : CommRingCat.ofHom (IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv).toRingHom =
      𝟙 _ := by
    ext x
    exact hτ x
  rw [hid, Spec.map_id, Category.id_comp] at hc
  have hred : reductionMap R L _ hfib P' = reductionMap R L _ hfib P := by
    ext1
    exact Limits.pullback.hom_ext hc ((Over.w _).trans (Over.w _).symm)
  let red : (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀)).X) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ⟶
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))).mapGrp.obj 𝒜₀).X) :=
    MonoidHom.mk' (fun Q => reductionMap R L _ hfib Q) (reductionMap_mul R L _ hfib)
  have h1 : red (P' * P⁻¹) = red 1 := by
    rw [map_mul, map_inv, map_one]
    exact mul_inv_eq_one.mpr hred
  exact mul_inv_eq_one.mp
    (injOn_reductionMap_torsion R L _ hfib n hn hunit htors (one_pow n) h1)

section Localization

variable {k K : Type u} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : Ideal (𝓞 K)) [𝔓.IsPrime] [𝔓.LiesOver 𝔭.asIdeal]

omit [NumberField k] [NumberField K] in
private lemma primeCompl_le_comap_primeCompl :
    𝔭.asIdeal.primeCompl ≤ 𝔓.primeCompl.comap (algebraMap (𝓞 k) (𝓞 K)) :=
  fun x hx h => hx ((Ideal.mem_of_liesOver 𝔓 𝔭.asIdeal x).2 h)

/-- The restriction `𝓞_{k,(𝔭)} → 𝓞_{K,(𝔓)}` of `k → K`, for `𝔓` over `𝔭`. -/
private noncomputable def localizationMap :
    Localization.subalgebra k 𝔭.asIdeal.primeCompl 𝔭.asIdeal.primeCompl_le_nonZeroDivisors →+*
      Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors :=
  IsLocalization.map (M := 𝔭.asIdeal.primeCompl) (T := 𝔓.primeCompl) _
    (algebraMap (𝓞 k) (𝓞 K)) (primeCompl_le_comap_primeCompl 𝔭 𝔓)

private lemma algebraMap_comp_localizationMap :
    (algebraMap (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) K).comp
        (localizationMap 𝔭 𝔓) =
      (algebraMap k K).comp (algebraMap
        (Localization.subalgebra k 𝔭.asIdeal.primeCompl
          𝔭.asIdeal.primeCompl_le_nonZeroDivisors) k) := by
  refine IsLocalization.ringHom_ext 𝔭.asIdeal.primeCompl (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, localizationMap]
  rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

variable {𝔓} {σ : K ≃ₐ[k] K} (hσ : ∀ x : 𝓞 K, σ • x - x ∈ 𝔓)

include hσ

omit [NumberField k] [NumberField K] [𝔓.IsPrime] in
private lemma smul_mem_iff_of_mem_inertia (x : 𝓞 K) : σ • x ∈ 𝔓 ↔ x ∈ 𝔓 := by
  rw [← sub_add_cancel (σ • x) x]
  exact ⟨fun h => (Ideal.add_mem_iff_right _ (hσ x)).1 h,
    fun h => Ideal.add_mem _ (hσ x) h⟩

omit [NumberField k] [NumberField K] in
private lemma map_primeCompl_of_mem_inertia :
    Submonoid.map (MulSemiringAction.toRingEquiv _ (𝓞 K) σ).toMonoidHom 𝔓.primeCompl =
      𝔓.primeCompl := by
  have hσ' : ∀ x : 𝓞 K, σ⁻¹ • x - x ∈ 𝔓 := fun x => by
    have := 𝔓.neg_mem_iff.2 (hσ (σ⁻¹ • x))
    rwa [smul_inv_smul, neg_sub] at this
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact fun h => hs ((smul_mem_iff_of_mem_inertia hσ s).1 h)
  · intro hy
    exact ⟨σ⁻¹ • y, fun h => hy ((smul_mem_iff_of_mem_inertia hσ' y).1 h), smul_inv_smul σ y⟩

/-- An element `σ` of the inertia group of `𝔓` induces an automorphism of `𝓞_{K,(𝔓)}`. -/
private noncomputable def inertiaRingEquiv :
    Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors ≃+*
      Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors :=
  IsLocalization.ringEquivOfRingEquiv _ _ (MulSemiringAction.toRingEquiv _ (𝓞 K) σ)
    (map_primeCompl_of_mem_inertia hσ)

omit [NumberField k] in
private lemma algebraMap_inertiaRingEquiv
    (r : Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) :
    algebraMap _ K (inertiaRingEquiv hσ r) = σ (algebraMap _ K r) := by
  have : (algebraMap _ K).comp (inertiaRingEquiv hσ).toRingHom =
      (σ : K →+* K).comp (algebraMap _ K) := by
    refine IsLocalization.ringHom_ext 𝔓.primeCompl (RingHom.ext fun y => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      inertiaRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rfl
  exact RingHom.congr_fun this r

omit [NumberField k] in
private lemma residue_inertiaRingEquiv
    [IsLocalRing (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors)]
    (r : Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) :
    IsLocalRing.residue _ (inertiaRingEquiv hσ r) = IsLocalRing.residue _ r := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl r
  unfold inertiaRingEquiv
  rw [IsLocalization.ringEquivOfRingEquiv_mk', ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← IsLocalization.mk'_sub, IsLocalization.mk'_mem_iff,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔓]
  refine Ideal.mem_map_of_mem _ ?_
  change σ • a * s - a * σ • (s : 𝓞 K) ∈ 𝔓
  have : σ • a * s - a * σ • (s : 𝓞 K) = (σ • a - a) * s - a * (σ • (s : 𝓞 K) - s) := by ring
  rw [this]
  exact sub_mem (Ideal.mul_mem_right _ _ (hσ a)) (Ideal.mul_mem_left _ _ (hσ s))

private lemma inertiaRingEquiv_localizationMap
    (r : Localization.subalgebra k 𝔭.asIdeal.primeCompl
      𝔭.asIdeal.primeCompl_le_nonZeroDivisors) :
    inertiaRingEquiv hσ (localizationMap 𝔭 𝔓 r) = localizationMap 𝔭 𝔓 r := by
  apply IsFractionRing.injective _ K
  rw [algebraMap_inertiaRingEquiv, ← RingHom.comp_apply,
    algebraMap_comp_localizationMap, RingHom.comp_apply, AlgEquiv.commutes]

end Localization

section Inertia

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The automorphism `Spec σ` of `Spec K` over `Spec k`, for `σ ∈ Aut(K/k)`. -/
private noncomputable def specMapOver (σ : K ≃ₐ[k] K) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : K →+* K))) (by
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

private lemma specMapOver_left (σ : K ≃ₐ[k] K) :
    (specMapOver σ).left = Spec.map (CommRingCat.ofHom (σ : K →+* K)) := rfl

/-- Let `A` have good reduction at `𝔭`, `𝔓 | 𝔭` a prime of `K` and `σ` in the inertia group of
`𝔓`. If `P ∈ A(K)` and `σ P - P` is `m`-torsion with `m ∉ 𝔭`, then `σ P = P`. -/
private lemma specMapOver_comp_eq_of_mem_inertia [NumberField k] [NumberField K]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (𝔭 : HeightOneSpectrum (𝓞 k))
    (hgood : HasGoodReduction k 𝔭 A) {𝔓 : Ideal (𝓞 K)} [𝔓.IsPrime] [𝔓.LiesOver 𝔭.asIdeal]
    {σ : K ≃ₐ[k] K} (hσ : ∀ x : 𝓞 K, σ • x - x ∈ 𝔓) {m : ℕ} (hm : 0 < m)
    (h𝔭m : (m : 𝓞 k) ∉ 𝔭.asIdeal)
    (P : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A)
    (htors : ((specMapOver σ ≫ P) * P⁻¹) ^ m = 1) : specMapOver σ ≫ P = P := by
  -- the local rings `R₀ = 𝓞_{k,(𝔭)}` and `R = 𝓞_{K,(𝔓)}`
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot 𝔓
  let 𝔓' : HeightOneSpectrum (𝓞 K) := ⟨𝔓, inferInstance, h𝔓⟩
  have : 𝔓'.asIdeal.LiesOver 𝔭.asIdeal := ‹_›
  let : Algebra (Localization.subalgebra k 𝔭.asIdeal.primeCompl
      𝔭.asIdeal.primeCompl_le_nonZeroDivisors)
      (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) :=
    (localizationMap 𝔭 𝔓).toAlgebra
  have : IsDiscreteValuationRing
      (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) h𝔓 _
  -- the abelian scheme `𝒜₀` over `R₀` and its base change to `R`
  obtain ⟨𝒜₀, _, _, _, hfib₀, ⟨e₀⟩⟩ := hgood
  obtain ⟨_, _, _, hfib, -⟩ := isAbelianScheme_pullbackObj_of_liesOver k K 𝔭 𝔓'
    (localizationMap 𝔭 𝔓) (algebraMap_comp_localizationMap 𝔭 𝔓) A 𝒜₀ hfib₀ e₀
  -- `σ` induces an `R₀`-automorphism `τ` of `R`, trivial on the residue field
  let τ := AlgEquiv.ofRingEquiv (f := inertiaRingEquiv hσ)
    (inertiaRingEquiv_localizationMap 𝔭 hσ)
  have hτ : ∀ x, IsLocalRing.ResidueField.mapEquiv τ.toRingEquiv x = x := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact residue_inertiaRingEquiv hσ r
  have hτK : (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      τ.toRingEquiv).toRingHom = (σ : K →+* K) :=
    IsLocalization.ringHom_ext (nonZeroDivisors
      (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors))
      (RingHom.ext fun r => by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          IsFractionRing.ringEquivOfRingEquiv_algebraMap]
        exact algebraMap_inertiaRingEquiv hσ r)
  -- `m` is a unit in `R`
  have hunit : IsUnit
      (m : Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors) := by
    have hm𝔓 : (m : 𝓞 K) ∈ 𝔓.primeCompl := fun h =>
      h𝔭m ((Ideal.mem_of_liesOver 𝔓 𝔭.asIdeal (m : 𝓞 k)).2 (by simpa using h))
    simpa using IsLocalization.map_units
      (Localization.subalgebra K 𝔓.primeCompl 𝔓.primeCompl_le_nonZeroDivisors)
      (⟨_, hm𝔓⟩ : 𝔓.primeCompl)
  -- transport to the generic fibre of the base change and reduce
  obtain ⟨α, hαinj, hα⟩ := exists_monoidHom_points_genericFibre
    (algebraMap_comp_localizationMap 𝔭 𝔓) 𝒜₀ A e₀
  refine hαinj (eq_of_comp_spec_map_of_pow_eq_one _ _ K 𝒜₀ hfib₀ hfib τ hτ m hm hunit
    (α P) (α (specMapOver σ ≫ P)) ?_ (by simpa using congrArg α htors))
  rw [hα, hα, hτK]
  simp [specMapOver_left]

end Inertia

/-- Let `A` be an abelian variety over a number field `k` with `A(k̄)[m] ⊆ A(k)`, and `𝔭` a
finite place of `k` not dividing `m` at which `A` has good reduction. If `Q ∈ A(k̄)` satisfies
`m Q ∈ A(k)`, then every prime `𝔓` of the ring of integers of `k(Q)` lying over `𝔭` has
ramification index `e(𝔓 | 𝔭) = 1`. -/
@[faltings "thm_mw_kummer_unramified"]
theorem ramificationIdx_fieldOfDefinition_eq_one_of_pow_mem (k : Type u) [Field k]
    [NumberField k] (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (m : ℕ) (hm : 1 ≤ m)
    (htors : ∀ T : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A, T ^ m = 1 →
      ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
        Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
          (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = T)
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭m : (m : 𝓞 k) ∉ 𝔭.asIdeal)
    (hgood : HasGoodReduction k 𝔭 A)
    (Q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A)
    (hQ : ∃ P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A,
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P = Q ^ m) :
    letI : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
    haveI : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
      inferInstanceAs (LocallyOfFiniteType A.hom)
    ∀ (𝔓 : Ideal (𝓞 (fieldOfDefinition (k := k) Q.left (Over.w Q)))) [𝔓.IsPrime]
      [𝔓.LiesOver 𝔭.asIdeal], 𝔓.ramificationIdx (𝓞 k) = 1 := by
  let : A.left.Over (Spec (CommRingCat.of k)) := ⟨A.hom⟩
  have : LocallyOfFiniteType (A.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType A.hom)
  obtain ⟨P₀, hP₀⟩ := hQ
  set K := fieldOfDefinition (k := k) Q.left (Over.w Q)
  intro 𝔓 _ _
  obtain ⟨_, _⟩ := finiteDimensional_and_isGalois_fieldOfDefinition_of_pow_mem k kbar A m hm
    htors Q ⟨P₀, hP₀⟩
  have : NumberField K := NumberField.of_module_finite k K
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal 𝔓 (K ≃ₐ[k] K),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[k] K) 𝔭.asIdeal 𝔓,
    ((Subgroup.eq_bot_iff_forall (Ideal.inertia (K ≃ₐ[k] K) 𝔓)).2 ?_), Subgroup.card_bot]
  intro σ hσ
  rw [Ideal.mem_inertia] at hσ
  -- the point `Q` comes from a `K`-point `QK`
  obtain ⟨QK, hQK₁, hQK₂⟩ := (exists_spec_map_comp_eq_iff_fieldOfDefinition_le (k := k)
    Q.left (Over.w Q) K).2 le_rfl
  let QL : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A := Over.homMk QK hQK₁
  have := IsAlgClosure.normal k kbar
  let σbar : kbar ≃ₐ[k] kbar := σ.liftNormal kbar
  have hσbar (x : K) : σbar (algebraMap K kbar x) = algebraMap K kbar (σ x) :=
    σ.liftNormal_commutes kbar x
  -- restriction `A(K) → A(k̄)` is an injective group homomorphism
  let ιK : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) (by
      simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq])
  have hιQ : ιK ≫ QL = Q := Over.OverMorphism.ext hQK₂
  have hισQ : ιK ≫ specMapOver σ ≫ QL = galoisActionPoint k kbar A σbar Q := by
    ext1
    simp only [galoisActionPoint, Over.comp_left, Over.homMk_left, specMapOver_left, QL, ιK]
    rw [← hQK₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact (hσbar x).symm
  have hepi : Epi (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) :=
    Flat.epi_of_flat_of_surjective _
  let ιhom : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    { toFun := (ιK ≫ ·), map_one' := MonObj.comp_one _, map_mul' := MonObj.comp_mul _ }
  have hιinj : Function.Injective ιhom := fun X Y h =>
    Over.OverMorphism.ext ((cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))).1
      (congrArg CommaMorphism.left h))
  -- `σ QK - QK` is `m`-torsion, hence zero
  have hD : ((specMapOver σ ≫ QL) * QL⁻¹) ^ m = 1 := by
    apply hιinj
    rw [map_pow, map_mul, map_inv, map_one]
    change ((ιK ≫ specMapOver σ ≫ QL) * (ιK ≫ QL)⁻¹) ^ m = 1
    rw [hισQ, hιQ, ← kummerPairing_eq_of_pow_eq k kbar A m hm htors P₀ σbar Q hP₀.symm]
    exact kummerPairing_pow_eq_one k kbar A m hm htors P₀ σbar
  have hfix : galoisActionPoint k kbar A σbar Q = Q := by
    rw [← hισQ, ← hιQ, specMapOver_comp_eq_of_mem_inertia A 𝔭 hgood hσ hm h𝔭m QL hD]
  refine AlgEquiv.ext fun x => (algebraMap K kbar).injective ?_
  rw [AlgEquiv.one_apply, ← hσbar]
  exact (galoisActionPoint_eq_self_iff A σbar Q).1 hfix _ x.2

end Faltings
