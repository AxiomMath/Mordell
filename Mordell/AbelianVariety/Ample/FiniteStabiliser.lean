module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Canonical
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierSimultaneous
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableCurveOverAmple
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic

/-!
# Divisors with finite stabiliser are ample

Let `A` be an abelian variety over a field `k` and `D` an effective Cartier divisor on `A`.
For an algebraically closed field `K` containing `k`, a point `x ∈ A(K)` acts on the base change
`A_K = A ×_k Spec K` by the translation `τ_x : y ↦ y + x`, and `D` base-changes to a divisor
`D_K` on `A_K`. If only finitely many `x ∈ A(K)` satisfy `τ_x^* D_K = D_K`, then `D` is ample,
that is, the invertible sheaf `𝒪_A(D)` is ample.

The argument is that of Mumford. Ampleness descends from `A_K` to `A`, so we work on `A_K`, with
`L` the pullback of `𝒪_A(D)` and `s` the pullback of its canonical section. For `K`-points
`x, y` the theorem of the square gives `τ_x^* L ⊗ τ_y^* L ⊗ τ_{(xy)⁻¹}^* L ≅ L^{⊗ 3}`, so
`L^{⊗ 3}` has a section vanishing exactly on `τ_x^{-1} D ∪ τ_y^{-1} D ∪ τ_{(xy)⁻¹}^{-1} D`;
these sections have no common zero. A base-point-free invertible module on a proper scheme over
an algebraically closed field is ample as soon as its sections separate the closed points of
every irreducible closed subset with infinitely many closed points: the morphism to projective
space defined by a basis of the sections is then quasi-finite, hence finite, and `L^{⊗ 3}` is the
pullback of `𝒪(1)` along it. If a curve `C` were contracted, every section above would vanish
either at all closed points of `C` or at none; choosing `y` generically this forces `C x ⊆ D` as
soon as `C x` meets `D`, so the translations by `c c₀⁻¹` (`c, c₀ ∈ C`) preserve the support of
`D`. Infinitely many of them fix each generic point of each component of that support, and on
the normal scheme `A_K` such an automorphism fixes the divisor itself, contradicting finiteness
of the stabiliser.

## Main results

* `Faltings.isAmple_of_finite_setOf_comap_translation_eq`: an effective Cartier divisor on an
  abelian variety whose stabiliser under translation by geometric points is finite is ample.

## Implementation notes

An abelian variety is a group object `A` of `Over (Spec k)` satisfying
`AlgebraicGeometry.IsAbelianVariety k A`, and a `K`-point is a morphism `Spec K ⟶ A` over
`Spec k`. The base change `A_K` is the cartesian product `A ⊗ Spec K` in `Over (Spec k)`; the
translation by `x` is `lift (lift (fst _ _) (snd _ _ ≫ x) ≫ μ) (snd _ _) : A_K ⟶ A_K`.
Divisors are closed subschemes `D : A.IdealSheafData` with
`Stacks.Divisors.IsEffectiveCartierDivisor D`, and pull-back of divisors is the scheme-theoretic
inverse image `AlgebraicGeometry.Scheme.IdealSheafData.comap`; so `D_K` is `D.comap` along the
projection `A_K → A`, and `τ_x^* D_K = D_K` is an equality of closed subschemes of `A_K`.
Ampleness is `AlgebraicGeometry.Scheme.Modules.IsAmple`; since the library records no
invertibility instance on `Stacks.Divisors.invertibleSheaf D` at that spelling, `𝒪_A(D)` enters as
an invertible module `M` with `M ≅ Stacks.Divisors.invertibleSheaf D`, which is the same
statement for `M = 𝒪_A(D)`. The field `K` is any algebraically closed extension of `k`, in
particular an algebraic closure.

Mumford uses the linear system `|2D|` and the sections `τ_x^* D + τ_{-x}^* D`; here `|3D|` and
the sections `τ_x^* D + τ_y^* D + τ_{(xy)⁻¹}^* D` are used, which makes the step "`C x` meets `D`
implies `C x ⊆ D`" immediate. The passage from the support of `D` to `D` itself, which Mumford
reads off the multiplicities of a Weil divisor, is done through the local rings at the points of
codimension one, which are discrete valuation rings, and algebraic Hartogs on affine opens.

## References

* [MumAV] D. Mumford, *Abelian Varieties*, Sec. 6, Application 1, (i) ⟹ (iii).
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Proposition 6.6(a).
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open Topology TopologicalSpace Order Opposite RingedSpaceModuleAdjunction

universe u

namespace Faltings

/-! ### Topology of schemes of finite type over an algebraically closed field -/

/-- In a Noetherian quasi-sober space, a closed point `x` of a closed set `F` that is not
isolated in `F` is a specialization of another point of `F`. -/
private theorem exists_ne_specializes_of_not_isOpen {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {F : Set X} (hF : IsClosed F) {x : X} (hxF : x ∈ F)
    (hx : IsClosed {x}) (h : ¬ IsOpen ({⟨x, hxF⟩} : Set F)) : ∃ z ∈ F, z ≠ x ∧ z ⤳ x := by
  set T : Set X := F \ {x} with hT
  have hxT : x ∈ closure T := by
    by_contra hxT
    refine h ?_
    have : ({⟨x, hxF⟩} : Set F) = Subtype.val ⁻¹' (closure T)ᶜ := by
      ext ⟨y, hy⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_compl_iff, Subtype.mk.injEq]
      refine ⟨fun h ↦ ?_, fun hy' ↦ ?_⟩
      · subst h
        exact hxT
      · by_contra hne
        exact hy' (subset_closure ⟨hy, hne⟩)
    rw [this]
    exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := T))
  set S' : Set (Set X) := S \ {{x}} with hS'
  have hTS' : closure T ⊆ ⋃₀ S' := by
    refine closure_minimal ?_ ?_
    · intro y hy
      have hyS : y ∈ ⋃₀ S := hS ▸ subset_closure hy
      obtain ⟨t, htS, hyt⟩ := hyS
      refine ⟨t, ⟨htS, ?_⟩, hyt⟩
      rintro rfl
      exact hy.2 hyt
    · exact (hSf.subset Set.sdiff_subset).isClosed_sUnion fun t ht => hSc t ht.1
  obtain ⟨t, ⟨htS, htx⟩, hxt⟩ := hTS' hxT
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hSi t htS) (hSc t htS)
  have htF : t ⊆ F := fun y hy ↦
    closure_minimal Set.sdiff_subset hF (show y ∈ closure T from hS ▸ ⟨t, htS, hy⟩)
  refine ⟨ξ, htF hξ.mem, ?_, ?_⟩
  · rintro rfl
    apply htx
    rw [Set.mem_singleton_iff, ← hξ.def, hx.closure_eq]
  · rwa [specializes_iff_mem_closure, hξ.def]

/-- In a Jacobson space the closure of a point with a proper specialization has infinitely many
closed points. -/
private theorem infinite_closure_inter_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {z x : X} (hzx : z ≠ x) (hspec : z ⤳ x) :
    (closure {z} ∩ closedPoints X).Infinite := by
  intro hfin
  have hcl : IsClosed (closure {z} ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closure {z} ∩ closedPoints X)]
    exact hfin.isClosed_biUnion fun y hy => hy.2
  have hdense := JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({z} : Set X)))
  rw [hcl.closure_eq] at hdense
  have hz : z ∈ closedPoints X := by
    have : z ∈ closure ({z} : Set X) := subset_closure rfl
    rw [← hdense] at this
    exact this.2
  have hx : x ∈ closure ({z} : Set X) := specializes_iff_mem_closure.mp hspec
  rw [(show IsClosed ({z} : Set X) from hz).closure_eq] at hx
  exact hzx (hx.symm)

/-- In a Noetherian quasi-sober space the maximal points (for specialization) of a closed set
are finitely many: they are generic points of its irreducible components. -/
private theorem finite_setOf_maximal {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] {Z : Set X} (hZ : IsClosed Z) :
    {ζ | ζ ∈ Z ∧ ∀ ξ ∈ Z, ξ ⤳ ζ → ξ = ζ}.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have : Finite S := hSf.to_subtype
  refine (Set.finite_range fun t : S => (hSi t.1 t.2).genericPoint).subset ?_
  rintro ξ ⟨hξZ, hmax⟩
  have : ξ ∈ ⋃₀ S := hS ▸ hξZ
  obtain ⟨t, htS, hξt⟩ := this
  refine ⟨⟨t, htS⟩, ?_⟩
  have hg : IsGenericPoint (hSi t htS).genericPoint t := by
    have := (hSi t htS).isGenericPoint_genericPoint_closure
    rwa [(hSc t htS).closure_eq] at this
  have hgZ : (hSi t htS).genericPoint ∈ Z := hS ▸ ⟨t, htS, hg.mem⟩
  exact hmax _ hgZ (hg.specializes hξt)

/-- In a Jacobson space two closed sets with the same closed points are equal. -/
private theorem eq_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {Z₁ Z₂ : Set X} (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : ∀ x, IsClosed ({x} : Set X) → (x ∈ Z₁ ↔ x ∈ Z₂)) : Z₁ = Z₂ := by
  rw [← JacobsonSpace.closure_inter_closedPoints h₁,
    ← JacobsonSpace.closure_inter_closedPoints h₂]
  congr 1
  ext x
  exact ⟨fun hx => ⟨(h x hx.2).mp hx.1, hx.2⟩, fun hx => ⟨(h x hx.2).mpr hx.1, hx.2⟩⟩

/-- A nonempty open subset of a Jacobson space contains a closed point. -/
private theorem exists_isClosed_singleton_mem_of_isOpen {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, IsClosed ({x} : Set X) := by
  by_contra hno
  push Not at hno
  have hsub : closedPoints X ⊆ Uᶜ := fun x hx hxU => hno x hxU hx
  have := closure_minimal hsub hU.isClosed_compl
  rw [closure_closedPoints] at this
  obtain ⟨x, hx⟩ := hne
  exact this (Set.mem_univ x) hx

/-- A global section of a module that is nonvanishing at `x` does not vanish along the
residue-field point of `x`. -/
private theorem not_vanishesAlong_of_mem_nonvanishingLocus {X : Scheme} (L : X.Modules) (x : X)
    (s : Γ(L, ⊤)) (hx : x ∈ Stacks.Ample.nonvanishingLocus L s) :
    ¬ VanishesAlong (X.fromSpecResidueField x) s := by
  intro hv
  have hpt : (X.fromSpecResidueField x) (IsLocalRing.closedPoint (X.residueField x)) = x :=
    X.fromSpecResidueField_apply x _
  have h := (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff
    (X.fromSpecResidueField x) L s (IsLocalRing.closedPoint (X.residueField x))).mpr
    (hpt.symm ▸ hx)
  have h0 : Stacks.NonvanishingPullback.pullbackGlobalSection (X.fromSpecResidueField x) L s = 0 :=
    hv
  have h' := (Stacks.Ample.mem_nonvanishingLocus_iff _ _ _).mp (h0 ▸ h)
  exact h' (by rw [map_zero]; exact Submodule.zero_mem _)

/-- A global section is nonvanishing at `x` exactly when it does not vanish along the
residue-field point of `x`. -/
private theorem mem_nonvanishingLocus_iff_not_vanishesAlong {X : Scheme} (L : X.Modules) (x : X)
    (s : Γ(L, ⊤)) :
    x ∈ Stacks.Ample.nonvanishingLocus L s ↔ ¬ VanishesAlong (X.fromSpecResidueField x) s :=
  ⟨not_vanishesAlong_of_mem_nonvanishingLocus L x s,
    mem_nonvanishingLocus_of_not_vanishesAlong L x s⟩

open Stacks.ProjectiveFromSections in
/-- **An ampleness criterion over an algebraically closed field.** Let `X` be proper over an
algebraically closed field `K` and `L` an invertible module with a section nonvanishing at each
closed point. If for every irreducible closed `C ⊆ X` with infinitely many closed points some
global section of `L` vanishes at one closed point of `C` and not at another, then `L` is ample:
the morphism `φ : X ⟶ ℙⁿ_K` of a basis of `Γ(X, L)` contracts no such `C`, so it is
quasi-finite at the closed points, hence quasi-finite, hence finite, and `L ≅ φ^* 𝒪(1)`. -/
private theorem isAmple_of_forall_isIrreducible {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hgen : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ s : Γ(L, ⊤), x ∈ Stacks.Ample.nonvanishingLocus L s)
    (hsep : ∀ C : Set X, IsClosed C → IsIrreducible C → (C ∩ closedPoints X).Infinite →
      ∃ s : Γ(L, ⊤), ∃ c ∈ C, ∃ c' ∈ C, IsClosed ({c} : Set X) ∧ IsClosed ({c'} : Set X) ∧
        c ∈ Stacks.Ample.nonvanishingLocus L s ∧ c' ∉ Stacks.Ample.nonvanishingLocus L s) :
    Stacks.Ample.IsAmple X L := by
  classical
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have hid : GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)) :=
    generatesStalks_of_forall_isClosed_exists_mem_nonvanishingLocus p L id hgen
  let : Module K Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  obtain ⟨n, s, hs, hspan⟩ := exists_fin_basis_generatesStalks_of_generatesStalks_id p L hid
  set φ := toProjectiveSpaceOver s hs p with hφ
  set q := Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of K)) with hq
  have hφq : φ ≫ q = p := toProjectiveSpaceOver_fst s hs p
  have : IsProper q := projectiveSpaceOver_isProper n _
  have : IsProper (φ ≫ q) := hφq ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ q
  obtain ⟨θ, hθ⟩ := exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver s hs p
  have hreal : ∀ σ : Γ(L, ⊤), ∃ u, θ.hom.app ⊤ (pullbackSectionTop φ _ u) = σ := fun σ =>
    exists_eq_pullbackSectionTop_of_mem_span p q φ hφq _ θ _ s hθ σ (hspan σ)
  have hpt : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      (pointOfClosedPoint p x hx ≫ φ) (IsLocalRing.closedPoint K) = φ x := fun x hx =>
    congrArg φ (pointOfClosedPoint_apply p x hx _)
  have hfib : ∀ (x y : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)),
      φ x = φ y → ∀ σ : Γ(L, ⊤), (x ∈ Stacks.Ample.nonvanishingLocus L σ ↔
        y ∈ Stacks.Ample.nonvanishingLocus L σ) := by
    intro x y hx hy hxy σ
    obtain ⟨u, hu⟩ := hreal σ
    have hab : pointOfClosedPoint p x hx ≫ φ = pointOfClosedPoint p y hy ≫ φ := by
      refine ext_of_apply_closedPoint_eq q ?_ ?_ ?_
      · rw [Category.assoc, hφq, pointOfClosedPoint_comp]
      · rw [Category.assoc, hφq, pointOfClosedPoint_comp]
      · rw [hpt, hpt, hxy]
    have key := (vanishesAlong_comp_iff_of_pullbackIso φ θ hu
      (pointOfClosedPoint p x hx)).symm.trans ((vanishesAlong_congr_iff hab _ _).trans
        (vanishesAlong_comp_iff_of_pullbackIso φ θ hu (pointOfClosedPoint p y hy)))
    have key' := (vanishesAlong_pointOfClosedPoint_iff p x hx σ).symm.trans
      (key.trans (vanishesAlong_pointOfClosedPoint_iff p y hy σ))
    rw [mem_nonvanishingLocus_iff_not_vanishesAlong, mem_nonvanishingLocus_iff_not_vanishesAlong,
      key']
  have hφclosed : ∀ x : X, IsClosed ({x} : Set X) → IsClosed ({φ x} : Set _) := by
    intro x hx
    have h : IsClosed {(pointOfClosedPoint p x hx ≫ φ) (IsLocalRing.closedPoint K)} :=
      ((pointEquivClosedPoint q) ⟨pointOfClosedPoint p x hx ≫ φ,
        by rw [Category.assoc, hφq, pointOfClosedPoint_comp]⟩).2
    rwa [hpt] at h
  have hqf_closed : ∀ x : X, IsClosed ({x} : Set X) → φ.QuasiFiniteAt x := by
    intro x hx
    by_contra hnot
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber] at hnot
    have hF : IsClosed (φ ⁻¹' {φ x}) := (hφclosed x hx).preimage φ.continuous
    have hxF : x ∈ φ ⁻¹' {φ x} := rfl
    have hopen : ¬ IsOpen ({⟨x, hxF⟩} : Set (φ ⁻¹' {φ x})) := by
      intro h
      apply hnot
      rw [← (φ.fiberHomeo (φ x)).isOpen_image, Set.image_singleton]
      convert h
      exact congrArg Subtype.val ((φ.fiberHomeo (φ x)).apply_symm_apply _)
    obtain ⟨z, hzF, hzx, hzsp⟩ := exists_ne_specializes_of_not_isOpen hF hxF hx hopen
    have hCF : closure {z} ⊆ φ ⁻¹' {φ x} :=
      closure_minimal (Set.singleton_subset_iff.mpr hzF) hF
    obtain ⟨σ, c, hc, c', hc', hcc, hcc', hcσ, hcσ'⟩ := hsep (closure {z}) isClosed_closure
      isIrreducible_singleton.closure (infinite_closure_inter_closedPoints hzx hzsp)
    have h1 : φ c = φ x := hCF hc
    have h2 : φ c' = φ x := hCF hc'
    exact hcσ' ((hfib c c' hcc hcc' (h1.trans h2.symm) σ).mp hcσ)
  have hqf : LocallyQuasiFinite φ := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine top_unique fun x _ => ?_
    by_contra hx
    have hZ : IsClosed ((φ.quasiFiniteLocus : Set X)ᶜ) :=
      φ.quasiFiniteLocus.isOpen.isClosed_compl
    have hempty : (φ.quasiFiniteLocus : Set X)ᶜ ∩ closedPoints X = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => hw.1 ?_
      exact hqf_closed w hw.2
    have := JacobsonSpace.closure_inter_closedPoints hZ
    rw [hempty, closure_empty] at this
    exact (this ▸ hx : x ∈ (∅ : Set X))
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have := Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf n (Spec (.of K))
  have hO := (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
    (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n (Spec (.of K)))
  have hpull := Scheme.Modules.isAmple_pullback_of_isAffineHom φ _ hO
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr (Scheme.Modules.isAmple_of_iso θ hpull)

/-! ### Rigidity of effective Cartier divisors on a normal scheme -/

/-- A ring automorphism of a discrete valuation ring fixes every ideal. -/
private theorem map_ringEquiv_eq_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (e : R ≃+* R) (I : Ideal R) : I.map e = I := by
  by_cases hI : I = ⊥
  · subst hI; exact Ideal.map_bot
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton]
  have he : Irreducible (e ϖ) := (MulEquiv.irreducible_iff (e : R ≃* R)).mpr hϖ
  exact (IsDiscreteValuationRing.associated_of_irreducible R he hϖ).pow_pow

/-- An isomorphism of local rings `𝒪_{X, y} ≅ 𝒪_{X, v}` with `y = v`, where `𝒪_{X, v}` is a
discrete valuation ring, carries the stalk of an ideal sheaf at `y` onto its stalk at `v`. -/
private theorem stalk_map_eq_of_eq {X : Scheme.{u}} (I : X.IdealSheafData) {y v : X}
    (hy : y = v) (g : X.presheaf.stalk y ⟶ X.presheaf.stalk v) [IsIso g]
    [IsDomain (X.presheaf.stalk v)] [IsDiscreteValuationRing (X.presheaf.stalk v)] :
    (IdealSheafData.stalk I y).map g.hom = IdealSheafData.stalk I v := by
  subst hy
  exact map_ringEquiv_eq_of_isDiscreteValuationRing (asIso g).commRingCatIsoToRingEquiv _

/-- On a normal integral locally Noetherian scheme, let `f` be an automorphism preserving the
support of an effective Cartier divisor `I` and fixing the maximal points of that support. Then
`f^* I` and `I` have the same stalk at every point of codimension one. -/
private theorem stalk_comap_eq_of_coheight_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {I : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (f : X ⟶ X) [IsIso f]
    (hsupp : ∀ x, f x ∈ I.supportSet ↔ x ∈ I.supportSet)
    (hfix : ∀ ζ ∈ I.supportSet, (∀ ξ ∈ I.supportSet, ξ ⤳ ζ → ξ = ζ) → f ζ = ζ)
    {v : X} (hv : coheight v = 1) :
    IdealSheafData.stalk (I.comap f) v = IdealSheafData.stalk I v := by
  rw [idealStalk_comap_eq_map]
  by_cases hvs : v ∈ I.supportSet
  · have hmax : ∀ ξ ∈ I.supportSet, ξ ⤳ v → ξ = v := by
      intro ξ hξ hξv
      by_contra hne
      have hlt : v < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hξv)
        (fun h2 => hne (hξv.antisymm (Scheme.le_iff_specializes.mp h2)).eq)
      have hfin : coheight ξ < ⊤ := (coheight_anti hlt.le).trans_lt (by rw [hv]; decide)
      have h0 : coheight ξ < 1 := hv ▸ coheight_strictAnti hlt hfin
      have hmaxξ : IsMax ξ := coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
      have hgen : ξ = genericPoint X :=
        ((genericPoint_specializes ξ).antisymm
          (Scheme.le_iff_specializes.mp
            (hmaxξ (Scheme.le_iff_specializes.mpr (genericPoint_specializes ξ))))).eq.symm
      exact genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hI (hgen ▸ hξ)
    have hfv := hfix v hvs hmax
    have : IsDiscreteValuationRing (X.presheaf.stalk v) :=
      Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hv
    exact stalk_map_eq_of_eq I hfv (f.stalkMap v)
  · have hfvs : f v ∉ I.supportSet := fun h => hvs ((hsupp v).mp h)
    rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support I (f v)).mpr hfvs, Ideal.map_top,
      (Stacks.Divisors.stalk_eq_top_iff_notMem_support I v).mpr hvs]

/-- On a normal integral locally Noetherian scheme, two effective Cartier divisors with the same
stalks at the points of codimension one satisfy `J ≤ I` (hence are equal): on an affine open on
which both are principal, the quotient of the generators is regular at every height-one prime,
hence regular. -/
private theorem le_of_stalk_eq_of_coheight_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {I J : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (h : ∀ v : X, coheight v = 1 → IdealSheafData.stalk I v = IdealSheafData.stalk J v) :
    J ≤ I := by
  classical
  refine IdealSheafData.le_of_stalk_le J I fun w => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hwW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  obtain ⟨U, hwU, -, f, hf⟩ := Stacks.Divisors.exists_affineOpen_le_forall_ideal_eq_span
    (Finset.univ : Finset (Fin 2)) ![I, J] (fun i _ => by fin_cases i <;> assumption)
    ⟨W, hW⟩ w hwW
  obtain ⟨ha, hIa⟩ := hf 0 (Finset.mem_univ _)
  obtain ⟨hb, hJb⟩ := hf 1 (Finset.mem_univ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hIa hJb
  set a := f 0
  set b := f 1
  have hU : IsAffineOpen U.1 := U.2
  have : Nonempty U.1 := ⟨⟨w, hwU⟩⟩
  have : IsDomain Γ(X, U.1) := AlgebraicGeometry.IsIntegral.component_integral U.1
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsIntegrallyClosed Γ(X, U.1) :=
    (AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal X).mp inferInstance U inferInstance
  have : IsFractionRing Γ(X, U.1) X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U.1 hU
  have ha0 : a ≠ 0 := isRegular_iff_ne_zero.mp ha
  have ha0' : algebraMap Γ(X, U.1) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have key : b ∈ Ideal.span {a} := by
    obtain ⟨r, hr⟩ :=
      Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
      X.functionField (z := algebraMap Γ(X, U.1) X.functionField b /
        algebraMap Γ(X, U.1) X.functionField a) fun q hq => by
      let q' : ↥(Spec Γ(X, U.1)) := q
      have hround : hU.isoSpec.hom.base (hU.isoSpec.inv.base q') = q := by
        rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
        rfl
      obtain ⟨v, hpq⟩ : ∃ v : U.1, hU.primeIdealOf v = q := ⟨hU.isoSpec.inv.base q', hround⟩
      have hch : coheight (v : X) = 1 := by
        rw [show (v : X) = U.1.ι.base v from rfl,
          AlgebraicGeometry.coheight_eq_of_isOpenImmersion U.1.ι (x := v),
          ← AlgebraicGeometry.coheight_eq_of_isOpenImmersion hU.isoSpec.hom (x := v),
          ← AlgebraicGeometry.idealHeight_eq_coheight, show hU.isoSpec.hom.base v = q from hpq]
        exact hq
      have hloc : IsLocalization.AtPrime (X.presheaf.stalk (v : X)) q.asIdeal := by
        rw [← hpq]; exact hU.isLocalization_stalk v
      have hst := h v hch
      rw [IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := U) v.2 hIa,
        IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := U) v.2 hJb] at hst
      have hbmem : (X.presheaf.germ U.1 v v.2).hom b ∈
          Ideal.span {(X.presheaf.germ U.1 v v.2).hom a} := hst ▸ Ideal.mem_span_singleton_self _
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hbmem
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl c
      have hrs' : IsLocalization.mk' (X.presheaf.stalk (v : X)) r s = c := hrs
      have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (v : X)) r s
      rw [hrs'] at hspec
      refine ⟨r, s.1, s.2, ?_⟩
      have hcg : algebraMap Γ(X, U.1) (X.presheaf.stalk (v : X)) b *
          algebraMap Γ(X, U.1) (X.presheaf.stalk (v : X)) s.1 =
          algebraMap Γ(X, U.1) (X.presheaf.stalk (v : X)) r *
          algebraMap Γ(X, U.1) (X.presheaf.stalk (v : X)) a := by
        rw [← hspec]
        change (X.presheaf.germ U.1 v v.2).hom b * _ = _ * (X.presheaf.germ U.1 v v.2).hom a
        rw [← hc]; ring
      have hK := congrArg (algebraMap (X.presheaf.stalk (v : X)) X.functionField) hcg
      simp only [map_mul, ← IsScalarTower.algebraMap_apply] at hK
      rw [div_mul_eq_mul_div, div_eq_iff ha0', hK]
    have hbr : b = r * a := IsFractionRing.injective Γ(X, U.1) X.functionField (by
      rw [map_mul, hr, div_mul_cancel₀ _ ha0'])
    exact Ideal.mem_span_singleton'.mpr ⟨r, hbr.symm⟩
  rw [IdealSheafData.stalk_eq_map_germ J w U hwU, IdealSheafData.stalk_eq_map_germ I w U hwU,
    hJb, hIa]
  exact Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr key)

/-- **Rigidity of an effective Cartier divisor under an automorphism.** On a normal integral
locally Noetherian scheme, an automorphism `f` preserving the support of an effective Cartier
divisor `I` and fixing each maximal point of that support (the generic points of its irreducible
components) satisfies `f^* I = I`. -/
private theorem comap_eq_self_of_isIso {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {I : X.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (f : X ⟶ X) [IsIso f] (hsupp : ∀ x, f x ∈ I.supportSet ↔ x ∈ I.supportSet)
    (hfix : ∀ ζ ∈ I.supportSet, (∀ ξ ∈ I.supportSet, ξ ⤳ ζ → ξ = ζ) → f ζ = ζ) :
    I.comap f = I := by
  have hJ : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) :=
    Stacks.Divisors.isPullbackDefined_of_flat f I hI
  have hst := fun v (hv : coheight v = 1) => stalk_comap_eq_of_coheight_eq_one hI f hsupp hfix hv
  exact le_antisymm (le_of_stalk_eq_of_coheight_eq_one hI hJ fun v hv => (hst v hv).symm)
    (le_of_stalk_eq_of_coheight_eq_one hJ hI hst)

/-! ### Tensor products and pullbacks of global sections -/

/-- The tensor product of two global sections of modules on a scheme, as a global section of the
tensor product module. -/
private noncomputable def tensorTop {X : Scheme.{u}} (F G : X.Modules) (s : Γ(F, ⊤))
    (t : Γ(G, ⊤)) : Γ((Stacks.SheafOfModules.schemeTensor X F G : X.Modules), ⊤) :=
  (Stacks.SheafOfModules.tensorSections (X := X.toRingedSpace) F G
    (Stacks.SheafOfModules.sectionsOfTop F s) (Stacks.SheafOfModules.sectionsOfTop G t)).eval
    (op ⊤)

/-- The nonvanishing locus of a tensor product of global sections is the intersection of the
nonvanishing loci. -/
private theorem nonvanishingLocus_tensorTop {X : Scheme.{u}} (F G : X.Modules) (s : Γ(F, ⊤))
    (t : Γ(G, ⊤)) :
    Stacks.Ample.nonvanishingLocus (Stacks.SheafOfModules.schemeTensor X F G : X.Modules)
        (tensorTop F G s t) =
      Stacks.Ample.nonvanishingLocus F s ∩ Stacks.Ample.nonvanishingLocus G t := by
  have h1 := nonvanishingLocus_sectionsOfTop_eq
    (Stacks.SheafOfModules.schemeTensor X F G : X.Modules) (tensorTop F G s t)
  have h2 : Stacks.SheafOfModules.sectionsOfTop
      (Stacks.SheafOfModules.schemeTensor X F G : X.Modules) (tensorTop F G s t) =
      Stacks.SheafOfModules.tensorSections (X := X.toRingedSpace) F G
        (Stacks.SheafOfModules.sectionsOfTop F s) (Stacks.SheafOfModules.sectionsOfTop G t) :=
    Stacks.SheafOfModules.sections_ext_of_eval_top _
      (Stacks.SheafOfModules.sectionsOfTop_eval_top _ _)
  rw [← h1, h2]
  refine (Stacks.SheafOfModules.nonvanishingLocus_tensorSections (X := X.toRingedSpace) F G _
    _).trans ?_
  rw [nonvanishingLocus_sectionsOfTop_eq, nonvanishingLocus_sectionsOfTop_eq]

/-- The nonvanishing locus of a pulled-back global section is the preimage of the nonvanishing
locus. -/
private theorem nonvanishingLocus_pullbackGlobalSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus _ (Stacks.NonvanishingPullback.pullbackGlobalSection f M s) =
      f ⁻¹' Stacks.Ample.nonvanishingLocus M s :=
  Set.ext fun x => Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f M s x

/-! ### The base change of an abelian variety to an algebraically closed field -/

section BaseChange

variable {k : Type u} [Field k] {A : Over (Spec (CommRingCat.of k))} [GrpObj A] {K : Type u}
  [Field K] [Algebra k K]

/-- `Spec K` as an object over `Spec k`. -/
noncomputable abbrev geomBase (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))

variable (A K) in
/-- `A_K` is the fibre product `A ×_k Spec K`. -/
private theorem isPullback_fst_snd : IsPullback (fst A (geomBase k K)).left
    (snd A (geomBase k K)).left A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  IsPullback.of_hasPullback _ _

variable (A K) in
/-- The projection `A_K ⟶ A` is flat. -/
private theorem flat_fst : Flat (fst A (geomBase k K)).left := by
  change Flat (Limits.pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

variable (A K) in
/-- The projection `A_K ⟶ A` is surjective. -/
private theorem surjective_fst : Surjective (fst A (geomBase k K)).left := by
  change Surjective (Limits.pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

section AbelianVariety

variable [IsAbelianVariety k A]

variable (A K) in
/-- `A_K` is proper over `K`. -/
private theorem isProper_snd : IsProper (snd A (geomBase k K)).left := by
  change IsProper (Limits.pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

variable (A K) in
/-- `A_K` is a Jacobson space, being of finite type over a field. -/
private theorem jacobsonSpace_tensor : JacobsonSpace (A ⊗ geomBase k K).left :=
  have := isProper_snd A K
  have : JacobsonSpace (geomBase k K).left :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of K)))
  LocallyOfFiniteType.jacobsonSpace (snd A (geomBase k K)).left

variable (A K) in
/-- `A_K` is integral. -/
private theorem isIntegral_tensor : IsIntegral (A ⊗ geomBase k K).left :=
  GeometricallyIntegral.geometrically_isIntegral (f := A.hom) _ _ _ (isPullback_fst_snd A K)

variable (A K) in
/-- `A_K` is normal, being smooth over `K`. -/
private theorem isNormal_tensor : IsNormal (A ⊗ geomBase k K).left :=
  have := smooth_of_isAbelianVariety k A
  have : Smooth (snd A (geomBase k K)).left := by
    change Smooth (Limits.pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  isNormal_of_smooth_over_field (snd A (geomBase k K)).left

end AbelianVariety

/-- The `K`-point of `A_K = A ⊗ Spec K` attached to a `K`-point `g` of `A`. -/
private noncomputable abbrev pointHom (g : geomBase k K ⟶ A) : geomBase k K ⟶ A ⊗ geomBase k K :=
  lift g (𝟙 _)

/-- The closed point of `A_K` attached to a `K`-point `g` of `A`. -/
private noncomputable abbrev ptOf (g : geomBase k K ⟶ A) : (A ⊗ geomBase k K).left :=
  (pointHom g).left (IsLocalRing.closedPoint K)

/-- The point `pointHom g` is a section of `A_K ⟶ Spec K`. -/
private theorem pointHom_left_snd (g : geomBase k K ⟶ A) :
    (pointHom g).left ≫ (snd A (geomBase k K)).left = 𝟙 _ := by
  rw [← Over.comp_left, lift_snd]; rfl

/-- The translation `y ↦ y · x` of `A_K` by a `K`-point `x` of `A`. -/
private noncomputable abbrev transl (x : geomBase k K ⟶ A) :
    A ⊗ geomBase k K ⟶ A ⊗ geomBase k K :=
  lift (lift (fst _ _) (snd _ _ ≫ x) ≫ μ) (snd _ _)

/-- The first coordinate of the translation by `x` is `y ↦ y · x`. -/
private theorem transl_fst (x : geomBase k K ⟶ A) :
    transl x ≫ fst A _ = fst A _ * (snd A _ ≫ x) := by
  simp only [transl, lift_fst]; rfl

/-- The translation by `x` is a morphism over `Spec K`. -/
private theorem transl_snd (x : geomBase k K ⟶ A) : transl x ≫ snd A _ = snd A _ := by
  simp only [transl, lift_snd]

/-- The translation by `x` sends the point `g` to the point `g · x`. -/
private theorem pointHom_transl (g x : geomBase k K ⟶ A) :
    pointHom g ≫ transl x = pointHom (g * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, transl_fst, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_fst,
      lift_snd, Category.id_comp]
  · rw [Category.assoc, transl_snd, lift_snd, lift_snd]

/-- Translations compose: `τ_x ≫ τ_y = τ_{x y}`. -/
private theorem transl_comp (x y : geomBase k K ⟶ A) : transl x ≫ transl y = transl (x * y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, transl_fst, MonObj.comp_mul, ← Category.assoc, transl_fst, transl_fst,
      transl_snd, _root_.mul_assoc, ← MonObj.comp_mul]
  · rw [Category.assoc, transl_snd, transl_snd, transl_snd]

/-- The translation by the unit is the identity. -/
private theorem transl_one : transl (1 : geomBase k K ⟶ A) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [transl_fst, Category.id_comp]; simp
  · rw [transl_snd, Category.id_comp]

/-- Translations are isomorphisms. -/
private theorem isIso_transl (x : geomBase k K ⟶ A) : IsIso (transl x) :=
  ⟨⟨transl x⁻¹, by rw [transl_comp, _root_.mul_inv_cancel, transl_one],
    by rw [transl_comp, _root_.inv_mul_cancel, transl_one]⟩⟩

/-- The translation by `x` sends the closed point of `g` to that of `g · x`. -/
private theorem transl_ptOf (g x : geomBase k K ⟶ A) :
    (transl x).left (ptOf g) = ptOf (g * x) := by
  change ((pointHom g).left ≫ (transl x).left) _ = _
  rw [← Over.comp_left, pointHom_transl]

section Points

variable [IsAlgClosed K] [LocallyOfFiniteType (snd A (geomBase k K)).left]

/-- The point of a `K`-point is closed. -/
private theorem isClosed_ptOf (g : geomBase k K ⟶ A) : IsClosed {ptOf g} :=
  ((pointEquivClosedPoint (snd A (geomBase k K)).left) ⟨_, pointHom_left_snd g⟩).2

/-- Every closed point of `A_K` is the point of a `K`-point of `A`. -/
private theorem exists_ptOf_eq (y : (A ⊗ geomBase k K).left) (hy : IsClosed {y}) :
    ∃ g : geomBase k K ⟶ A, ptOf g = y := by
  set a := pointOfClosedPoint (snd A (geomBase k K)).left y hy
  have ha : a ≫ (snd A (geomBase k K)).left = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let b : geomBase k K ⟶ A ⊗ geomBase k K := Over.homMk a (by
    rw [← Over.w (snd A (geomBase k K)), ← Category.assoc, ha]; exact Category.id_comp _)
  have hb : pointHom (b ≫ fst A _) = b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
    · rw [lift_snd]
      exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha.symm)
  refine ⟨b ≫ fst A _, ?_⟩
  rw [ptOf, hb]
  exact pointOfClosedPoint_apply _ _ _ _

end Points

/-! ### The theorem of the square on `A_K` -/

/-- The pullback of an invertible module on `A` along a morphism factoring through `Spec K` is
trivial. -/
private theorem pullbackPicardClass_comp_eq_zero
    (M : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)
    {B : Over (Spec (CommRingCat.of k))} (x : geomBase k K ⟶ A) (b : B ⟶ geomBase k K) :
    Stacks.SheafOfModules.pullbackPicardClass (b ≫ x).left M hM = 0 := by
  have hx := Stacks.Groupoids.isInvertible_pullbackOver x M hM
  have htriv : Stacks.SheafOfModules.IsTrivial (Spec (CommRingCat.of K)).presheaf
      (Spec (CommRingCat.of K)).ringCatIsSheaf (Stacks.Groupoids.pullbackOver x M) :=
    have := hx
    Stacks.PicardUFD.isTrivial_of_isInvertible_spec K _
  refine (Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff _ _ _).mpr ?_
  exact ⟨(modulePullbackComp b.left.toLRSHom.toShHom x.left.toLRSHom.toShHom).app M ≪≫
    (modulePullback b.left.toLRSHom.toShHom).mapIso htriv.some ≪≫
    modulePullbackObjUnitIso b.left.toLRSHom.toShHom⟩

section AbelianVariety

variable [IsAbelianVariety k A]
  (M : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)

/-- **The theorem of the square** on `A_K`, for translations by `K`-points:
`τ_{xy}^* L + L = τ_x^* L + τ_y^* L` in `Pic(A_K)`, for `L` pulled back from `A`. -/
private theorem pullbackPicardClass_square (x y : geomBase k K ⟶ A) :
    Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ (x * y))).left M hM +
        Stacks.SheafOfModules.pullbackPicardClass (fst A (geomBase k K)).left M hM =
      Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ x)).left M hM +
        Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ y)).left M hM := by
  have h := Stacks.Groupoids.pullbackPicardClass_cubeRelation A
    (Stacks.Groupoids.hasTheoremOfTheCube k A) M hM (fst A (geomBase k K))
    (snd A _ ≫ x) (snd A _ ≫ y)
  rw [pullbackPicardClass_comp_eq_zero M hM x, pullbackPicardClass_comp_eq_zero M hM y,
    ← MonObj.comp_mul, pullbackPicardClass_comp_eq_zero M hM (x * y), _root_.mul_assoc,
    ← MonObj.comp_mul, add_zero, add_zero, add_zero] at h
  exact h

/-- `τ_x^* L + τ_y^* L + τ_{(xy)⁻¹}^* L = 3 L` in `Pic(A_K)`. -/
private theorem pullbackPicardClass_triple (x y : geomBase k K ⟶ A) :
    Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ x)).left M hM +
        Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ y)).left M hM +
        Stacks.SheafOfModules.pullbackPicardClass (fst A _ * (snd A _ ≫ (x * y)⁻¹)).left M hM =
      3 • Stacks.SheafOfModules.pullbackPicardClass (fst A (geomBase k K)).left M hM := by
  have h1 := pullbackPicardClass_square M hM x y
  have h2 := pullbackPicardClass_square M hM (x * y) (x * y)⁻¹
  rw [_root_.mul_inv_cancel, MonObj.comp_one, _root_.mul_one] at h2
  rw [← h1, add_assoc, add_comm (Stacks.SheafOfModules.pullbackPicardClass (fst A _).left M hM),
    ← add_assoc, ← h2, three_nsmul, add_assoc]

end AbelianVariety

/-- For a global section `s` of `M` on `A` and `K`-points `x`, `y`, the cube `L^{⊗ 3}` of the
pullback `L` of `M` to `A_K` has a global section whose nonvanishing locus is
`τ_x^{-1}(A_s) ∩ τ_y^{-1}(A_s) ∩ τ_{(xy)⁻¹}^{-1}(A_s)`. -/
private theorem exists_tensorPower_section [IsAbelianVariety k A] (M : A.left.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (A ⊗ geomBase k K).left.toRingedSpace.presheaf
      (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
      (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M)]
    (s : Γ(M, ⊤)) (x y : geomBase k K ⟶ A) :
    ∃ t : Γ((Stacks.SheafOfModules.Invertible.tensorPower
        (A ⊗ geomBase k K).left.toRingedSpace.presheaf
        (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
        (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ) :
          (A ⊗ geomBase k K).left.Modules), ⊤),
      Stacks.Ample.nonvanishingLocus _ t =
        (fst A _ * (snd A _ ≫ x)).left ⁻¹' Stacks.Ample.nonvanishingLocus M s ∩
        (fst A _ * (snd A _ ≫ y)).left ⁻¹' Stacks.Ample.nonvanishingLocus M s ∩
        (fst A _ * (snd A _ ≫ (x * y)⁻¹)).left ⁻¹' Stacks.Ample.nonvanishingLocus M s := by
  set X := (A ⊗ geomBase k K).left
  set mx := fst A (geomBase k K) * (snd A _ ≫ x)
  set my := fst A (geomBase k K) * (snd A _ ≫ y)
  set mw := fst A (geomBase k K) * (snd A _ ≫ (x * y)⁻¹)
  have hx := Stacks.Groupoids.isInvertible_pullbackOver mx M hM
  have hy := Stacks.Groupoids.isInvertible_pullbackOver my M hM
  have hw := Stacks.Groupoids.isInvertible_pullbackOver mw M hM
  have hN := Stacks.Groupoids.isInvertible_pullbackOver (fst A (geomBase k K)) M hM
  have hxy := Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ hx hy
  have hF := Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ hxy hw
  have hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (Stacks.SheafOfModules.Invertible.tensorPowerModule'
        (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ)) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ _ _
  have hcl : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf _ hF =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf _ hP := by
    rw [Stacks.SheafOfModules.Invertible.picardClass_tensorPowerModule' _ hN 3 hP,
      Stacks.SheafOfModules.picardClass_schemeTensor X _ _ hxy hw,
      Stacks.SheafOfModules.picardClass_schemeTensor X _ _ hx hy]
    exact pullbackPicardClass_triple M hM x y
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ hF hP).mp hcl
  let e' : @Iso X.Modules _ (Stacks.SheafOfModules.schemeTensor X
    (Stacks.SheafOfModules.schemeTensor X (Stacks.Groupoids.pullbackOver mx M)
      (Stacks.Groupoids.pullbackOver my M)) (Stacks.Groupoids.pullbackOver mw M))
      (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ)) := e
  refine ⟨e'.hom.app ⊤ (tensorTop _ _ (tensorTop _ _
    (Stacks.NonvanishingPullback.pullbackGlobalSection mx.left M s)
    (Stacks.NonvanishingPullback.pullbackGlobalSection my.left M s))
    (Stacks.NonvanishingPullback.pullbackGlobalSection mw.left M s)), ?_⟩
  refine ((Stacks.Ample.nonvanishingLocus_congr e' _).trans
    (nonvanishingLocus_tensorTop _ _ _ _)).trans ?_
  exact congrArg₂ (· ∩ ·) ((nonvanishingLocus_tensorTop _ _ _ _).trans
    (congrArg₂ (· ∩ ·) (nonvanishingLocus_pullbackGlobalSection _ _ _)
      (nonvanishingLocus_pullbackGlobalSection _ _ _)))
    (nonvanishingLocus_pullbackGlobalSection _ _ _)

/-- Translations are isomorphisms of schemes. -/
private theorem isIso_transl_left (x : geomBase k K ⟶ A) : IsIso (transl x).left :=
  have := isIso_transl x
  (Over.forget _).map_isIso (transl x)

/-- `τ_{x⁻¹} ∘ τ_x = id` on points. -/
private theorem transl_left_inv_apply (x : geomBase k K ⟶ A) (w : (A ⊗ geomBase k K).left) :
    (transl x⁻¹).left ((transl x).left w) = w := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp, _root_.mul_inv_cancel, transl_one]
  rfl

/-- `τ_y ∘ τ_x = τ_{x y}` on points. -/
private theorem transl_left_comp_apply (x y : geomBase k K ⟶ A) (w : (A ⊗ geomBase k K).left) :
    (transl y).left ((transl x).left w) = (transl (x * y)).left w := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp]

/-! ### Points of `A_K` in the support of `D_K` -/

/-- A `K`-point `g` of `A` lies on the divisor `D`. -/
private abbrev InSupp (D : A.left.IdealSheafData) (g : geomBase k K ⟶ A) : Prop :=
  g.left (IsLocalRing.closedPoint K) ∈ D.supportSet

/-- A morphism `h : A_K ⟶ A` sends the point of `g` into `D` exactly when `g ≫ h` lies on `D`. -/
private theorem apply_ptOf_mem_iff (D : A.left.IdealSheafData) (h : A ⊗ geomBase k K ⟶ A)
    (g : geomBase k K ⟶ A) : h.left (ptOf g) ∈ D.supportSet ↔ InSupp D (pointHom g ≫ h) := by
  rw [InSupp, Over.comp_left]; rfl

/-- `(y ↦ y · x)` evaluated at the point `g` is `g · x`. -/
private theorem pointHom_comp_mul (g x : geomBase k K ⟶ A) :
    pointHom g ≫ (fst A _ * (snd A _ ≫ x)) = g * x := by
  rw [MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd, Category.id_comp]

/-- The point of `g` lies on `D_K` exactly when `g` lies on `D`. -/
private theorem ptOf_mem_comap_iff (D : A.left.IdealSheafData) (g : geomBase k K ⟶ A) :
    ptOf g ∈ (D.comap (fst A (geomBase k K)).left).supportSet ↔ InSupp D g := by
  change ptOf g ∈ ((D.comap (fst A (geomBase k K)).left).support : Set _) ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  change (fst A _).left (ptOf g) ∈ D.supportSet ↔ _
  rw [apply_ptOf_mem_iff, lift_fst]

variable [IsAlgClosed K]

section Avoid

variable [IsAbelianVariety k A] (D : A.left.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- Some `K`-point of `A` lies off `D`. -/
private theorem exists_not_inSupp : ∃ d : geomBase k K ⟶ A, ¬ InSupp D d := by
  have := isProper_snd A K
  have := jacobsonSpace_tensor A K
  have := surjective_fst A K
  have hgen := genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor
    (inferInstance : Stacks.Divisors.IsEffectiveCartierDivisor D)
  obtain ⟨w, hw⟩ := (fst A (geomBase k K)).left.surjective (genericPoint A.left)
  obtain ⟨y, hy, hycl⟩ := exists_isClosed_singleton_mem_of_isOpen
    (((D.support.isClosed).preimage (fst A (geomBase k K)).left.continuous).isOpen_compl)
    ⟨w, by rw [Set.mem_compl_iff, Set.mem_preimage, hw]; exact hgen⟩
  obtain ⟨d, rfl⟩ := exists_ptOf_eq y hycl
  refine ⟨d, fun hd => hy ?_⟩
  change (fst A _).left (ptOf d) ∈ D.supportSet
  rwa [apply_ptOf_mem_iff, lift_fst]

/-- For `K`-points `g`, `x` of `A` there is a `K`-point `y` with `g y ∉ D` and
`g (x y)⁻¹ ∉ D`. -/
private theorem exists_avoid (g x : geomBase k K ⟶ A) :
    ∃ y : geomBase k K ⟶ A, ¬ InSupp D (g * y) ∧ ¬ InSupp D (g * (x * y)⁻¹) := by
  have := isProper_snd A K
  have := jacobsonSpace_tensor A K
  have := isIntegral_tensor A K
  obtain ⟨d, hd⟩ := exists_not_inSupp (K := K) D
  set h₁ : A ⊗ geomBase k K ⟶ A := (snd A _ ≫ g) * fst A _
  set h₂ : A ⊗ geomBase k K ⟶ A := (snd A _ ≫ g) * ((snd A _ ≫ x) * fst A _)⁻¹
  have e₁ : ∀ y, pointHom y ≫ h₁ = g * y := fun y => by
    rw [MonObj.comp_mul, ← Category.assoc, lift_snd, Category.id_comp, lift_fst]
  have e₂ : ∀ y, pointHom y ≫ h₂ = g * (x * y)⁻¹ := fun y => by
    rw [MonObj.comp_mul, ← Category.assoc, lift_snd, Category.id_comp, GrpObj.comp_inv,
      MonObj.comp_mul, ← Category.assoc, lift_snd, Category.id_comp, lift_fst]
  set Z₁ := h₁.left ⁻¹' D.supportSet
  set Z₂ := h₂.left ⁻¹' D.supportSet
  have hZ₁ : IsClosed Z₁ := D.support.isClosed.preimage h₁.left.continuous
  have hZ₂ : IsClosed Z₂ := D.support.isClosed.preimage h₂.left.continuous
  have hw₁ : ptOf (g⁻¹ * d) ∉ Z₁ := by
    change ¬ h₁.left (ptOf _) ∈ D.supportSet
    rwa [apply_ptOf_mem_iff, e₁, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hw₂ : ptOf (x⁻¹ * (g⁻¹ * d)⁻¹) ∉ Z₂ := by
    change ¬ h₂.left (ptOf _) ∈ D.supportSet
    rwa [apply_ptOf_mem_iff, e₂, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul,
      inv_inv, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  obtain ⟨w, -, hw⟩ := (IrreducibleSpace.isIrreducible_univ (A ⊗ geomBase k K).left).2 _ _
    hZ₁.isOpen_compl hZ₂.isOpen_compl ⟨_, trivial, hw₁⟩ ⟨_, trivial, hw₂⟩
  obtain ⟨y', hy', hycl⟩ := exists_isClosed_singleton_mem_of_isOpen
    (hZ₁.isOpen_compl.inter hZ₂.isOpen_compl) ⟨w, hw⟩
  obtain ⟨y, rfl⟩ := exists_ptOf_eq y' hycl
  refine ⟨y, ?_, ?_⟩
  · have := hy'.1
    change ¬ h₁.left (ptOf _) ∈ D.supportSet at this
    rwa [apply_ptOf_mem_iff, e₁] at this
  · have := hy'.2
    change ¬ h₂.left (ptOf _) ∈ D.supportSet at this
    rwa [apply_ptOf_mem_iff, e₂] at this

/-- The section of `L^{⊗ 3}` of `exists_tensorPower_section`, built from a section of `M` with
nonvanishing locus the complement of `D`, is nonvanishing at the point of `g` exactly when none
of `g x`, `g y`, `g (x y)⁻¹` lies on `D`. -/
private theorem exists_tensorPower_section_ptOf (M : A.left.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (A ⊗ geomBase k K).left.toRingedSpace.presheaf
      (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
      (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M)]
    (sM : Γ(M, ⊤)) (hsM : Stacks.Ample.nonvanishingLocus M sM = D.supportSetᶜ)
    (x y : geomBase k K ⟶ A) :
    ∃ t : Γ((Stacks.SheafOfModules.Invertible.tensorPower
        (A ⊗ geomBase k K).left.toRingedSpace.presheaf
        (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
        (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ) :
          (A ⊗ geomBase k K).left.Modules), ⊤), ∀ g : geomBase k K ⟶ A,
      ptOf g ∈ Stacks.Ample.nonvanishingLocus _ t ↔
        (¬ InSupp D (g * x) ∧ ¬ InSupp D (g * y)) ∧ ¬ InSupp D (g * (x * y)⁻¹) := by
  obtain ⟨t, ht⟩ := exists_tensorPower_section M hM sM x y
  refine ⟨t, fun g => ?_⟩
  simp only [ht, Set.mem_inter_iff, Set.mem_preimage, hsM, Set.mem_compl_iff, apply_ptOf_mem_iff,
    pointHom_comp_mul]

/-- A `K`-point `z` of `A` stabilizing `D` on `K`-points stabilizes the support of `D_K` under
translation. -/
private theorem transl_mem_comap_iff (z : geomBase k K ⟶ A)
    (hz : ∀ d, InSupp D (d * z) ↔ InSupp D d) (w : (A ⊗ geomBase k K).left) :
    (transl z).left w ∈ (D.comap (fst A (geomBase k K)).left).supportSet ↔
      w ∈ (D.comap (fst A (geomBase k K)).left).supportSet := by
  have := isProper_snd A K
  have := jacobsonSpace_tensor A K
  have hS : IsClosed (D.comap (fst A (geomBase k K)).left).supportSet :=
    (D.comap (fst A (geomBase k K)).left).support.isClosed
  have heq := eq_of_forall_isClosed_singleton (hS.preimage (transl z).left.continuous) hS
    fun y hy => by
      obtain ⟨g, rfl⟩ := exists_ptOf_eq y hy
      rw [Set.mem_preimage, transl_ptOf, ptOf_mem_comap_iff, ptOf_mem_comap_iff, hz]
  exact Set.ext_iff.mp heq w

/-- **The contracted-curve step.** Let `C ⊆ A_K` be such that every global section of
`L^{⊗ 3}` (with `L` the pullback of `𝒪_A(D)`) which is nonvanishing at one closed point of `C`
is nonvanishing at every closed point of `C`. If `c`, `c₀` are `K`-points with closed points on
`C`, then `c c₀⁻¹ d ∈ D` for every `K`-point `d ∈ D`. -/
private theorem inSupp_mul_of_forall_mem_nonvanishingLocus (M : A.left.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (A ⊗ geomBase k K).left.toRingedSpace.presheaf
      (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
      (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M)]
    (sM : Γ(M, ⊤)) (hsM : Stacks.Ample.nonvanishingLocus M sM = D.supportSetᶜ)
    (C : Set (A ⊗ geomBase k K).left)
    (hfib : ∀ σ : Γ((Stacks.SheafOfModules.Invertible.tensorPower
        (A ⊗ geomBase k K).left.toRingedSpace.presheaf
        (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
        (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ) :
          (A ⊗ geomBase k K).left.Modules), ⊤), ∀ c ∈ C, ∀ c' ∈ C,
        IsClosed ({c} : Set _) → IsClosed ({c'} : Set _) →
        c ∈ Stacks.Ample.nonvanishingLocus _ σ → c' ∈ Stacks.Ample.nonvanishingLocus _ σ)
    {c c₀ : geomBase k K ⟶ A} (hc : ptOf c ∈ C) (hc₀ : ptOf c₀ ∈ C) {d : geomBase k K ⟶ A}
    (hd : InSupp D d) : InSupp D (c * c₀⁻¹ * d) := by
  have := isProper_snd A K
  by_contra hcx
  rw [_root_.mul_assoc] at hcx
  obtain ⟨y, hy₁, hy₂⟩ := exists_avoid D c (c₀⁻¹ * d)
  obtain ⟨t, hmem⟩ := exists_tensorPower_section_ptOf D M hM sM hsM (c₀⁻¹ * d) y
  have h₁ := (hmem c).mpr ⟨⟨hcx, hy₁⟩, hy₂⟩
  have h₂ := (hmem c₀).mp (hfib t _ hc _ hc₀ (isClosed_ptOf c) (isClosed_ptOf c₀) h₁)
  apply h₂.1.1
  rwa [← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]

/-- **Pigeonhole and rigidity.** If infinitely many `K`-points of `A` stabilize the `K`-points of
`D` under translation, then infinitely many translations of `A_K` fix the divisor `D_K`. -/
private theorem infinite_setOf_comap_transl_eq (Zs : Set (geomBase k K ⟶ A))
    (hZs : Zs.Infinite) (hstab : ∀ z ∈ Zs, ∀ d, InSupp D (d * z) ↔ InSupp D d) :
    {u : geomBase k K ⟶ A | (D.comap (fst A (geomBase k K)).left).comap (transl u).left =
      D.comap (fst A (geomBase k K)).left}.Infinite := by
  classical
  have := isProper_snd A K
  have := isIntegral_tensor A K
  have := isNormal_tensor A K
  have : IsLocallyNoetherian (geomBase k K).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  have : CompactSpace (geomBase k K).left :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of K)))
  have : IsLocallyNoetherian (A ⊗ geomBase k K).left :=
    LocallyOfFiniteType.isLocallyNoetherian (snd A (geomBase k K)).left
  have : CompactSpace (A ⊗ geomBase k K).left :=
    QuasiCompact.compactSpace_of_compactSpace (snd A (geomBase k K)).left
  have : IsNoetherian (A ⊗ geomBase k K).left := {}
  set I := D.comap (fst A (geomBase k K)).left with hIdef
  have hI : Stacks.Divisors.IsEffectiveCartierDivisor I := by
    have := flat_fst A K
    exact Stacks.Divisors.isPullbackDefined_of_flat _ D inferInstance
  set G := {ζ | ζ ∈ I.supportSet ∧ ∀ ξ ∈ I.supportSet, ξ ⤳ ζ → ξ = ζ} with hGdef
  have hG : G.Finite := finite_setOf_maximal I.support.isClosed
  have stab_inv : ∀ z : geomBase k K ⟶ A, (∀ d, InSupp D (d * z) ↔ InSupp D d) →
      ∀ d, InSupp D (d * z⁻¹) ↔ InSupp D d := fun z hz d => by
    rw [← hz (d * z⁻¹), inv_mul_cancel_right]
  have stab_mul : ∀ a b : geomBase k K ⟶ A, (∀ d, InSupp D (d * a) ↔ InSupp D d) →
      (∀ d, InSupp D (d * b) ↔ InSupp D d) → ∀ d, InSupp D (d * (a⁻¹ * b)) ↔ InSupp D d :=
    fun a b ha hb d => by rw [← _root_.mul_assoc, hb, stab_inv a ha]
  have hmaps : ∀ z, (∀ d, InSupp D (d * z) ↔ InSupp D d) → ∀ ζ ∈ G, (transl z).left ζ ∈ G := by
    intro z hz ζ ⟨hζS, hζmax⟩
    refine ⟨(transl_mem_comap_iff D z hz ζ).mpr hζS, fun ξ hξ hξζ => ?_⟩
    have h₁ : (transl z⁻¹).left ξ ⤳ ζ := by
      have := hξζ.map (transl z⁻¹).left.continuous
      rwa [transl_left_inv_apply] at this
    have h₂ : (transl z⁻¹).left ξ ∈ I.supportSet :=
      (transl_mem_comap_iff D z⁻¹ (stab_inv z hz) ξ).mpr hξ
    have h₃ := hζmax _ h₂ h₁
    calc ξ = (transl z).left ((transl z⁻¹).left ξ) := by
          rw [transl_left_comp_apply, _root_.inv_mul_cancel, transl_one]; rfl
      _ = (transl z).left ζ := by rw [h₃]
  have : Finite G := hG.to_subtype
  have : Infinite Zs := hZs.to_subtype
  let F : Zs → (G → G) := fun z ζ => ⟨(transl z.1).left ζ.1, hmaps z.1 (hstab z.1 z.2) ζ.1 ζ.2⟩
  obtain ⟨φ, hφ⟩ := Finite.exists_infinite_fiber F
  obtain ⟨z₁⟩ : Nonempty (F ⁻¹' {φ}) := inferInstance
  refine Set.infinite_of_injective_forall_mem (f := fun z : F ⁻¹' {φ} => (z₁.1.1)⁻¹ * z.1.1)
    (fun a b hab => Subtype.ext (Subtype.ext (mul_left_cancel hab))) fun z => ?_
  have hu := stab_mul _ _ (hstab z₁.1.1 z₁.1.2) (hstab z.1.1 z.1.2)
  have := isIso_transl_left ((z₁.1.1)⁻¹ * z.1.1)
  refine comap_eq_self_of_isIso hI _ (transl_mem_comap_iff D _ hu) fun ζ hζS hζmax => ?_
  have hinj : Function.Injective (F z₁.1) := fun a b hab => Subtype.ext (by
    have := congrArg (fun p : G => (transl (z₁.1.1)⁻¹).left p.1) hab
    simpa only [F, transl_left_inv_apply] using this)
  obtain ⟨ν, hν⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨ζ, hζS, hζmax⟩
  have hFz : F z.1 = F z₁.1 := (Set.mem_singleton_iff.mp z.2).trans
    (Set.mem_singleton_iff.mp z₁.2).symm
  have hzη : (transl z.1.1).left ν.1 = (transl z₁.1.1).left ν.1 :=
    congrArg (fun f : G → G => (f ν).1) hFz
  have hζ : (transl z₁.1.1).left ν.1 = ζ := congrArg Subtype.val hν
  rw [← hζ, transl_left_comp_apply, mul_inv_cancel_left, hzη]

end Avoid

end BaseChange

/-- Let `A` be an abelian variety over `k`, `K` an algebraically closed extension of `k`, and `D`
an effective Cartier divisor on `A`. If only finitely many points `x ∈ A(K)` satisfy
`τ_x^* D_K = D_K`, where `D_K` is the base change of `D` to `A_K = A ⊗ Spec K` and `τ_x` is
translation by `x` on `A_K`, then `D` is ample: every invertible module `M ≅ 𝒪_A(D)` is
ample. -/
@[faltings "lem_nt_ample_translation_finite"]
theorem isAmple_of_finite_setOf_comap_translation_eq {k : Type u} [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsAbelianVariety k A]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
    (D : A.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hfin : {x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A |
      (D.comap (fst A _).left).comap
          (lift (lift (fst _ _) (snd _ _ ≫ x) ≫ μ) (snd _ _)).left =
        D.comap (fst A _).left}.Finite)
    (M : A.left.Modules)
    [SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.property M]
    (hM : M ≅ Stacks.Divisors.invertibleSheaf D) :
    Scheme.Modules.IsAmple A.left M := by
  classical
  have := isProper_snd A K
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have hM' : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance
  have hN := Stacks.Groupoids.isInvertible_pullbackOver (fst A (geomBase k K)) M hM'
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (A ⊗ geomBase k K).left.toRingedSpace.presheaf
      (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
      (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hN
  have hL' : Stacks.Ample.IsInvertibleModule (A ⊗ geomBase k K).left
      (Stacks.SheafOfModules.Invertible.tensorPower
        (A ⊗ geomBase k K).left.toRingedSpace.presheaf
        (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
        (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M) ((3 : ℕ) : ℤ)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Scheme.Modules.isInvertible_tensorPower _ _ _)
  -- the canonical section of `𝒪_A(D)`, carried to `M`
  have hc₀ : Stacks.Ample.nonvanishingLocus (Stacks.Divisors.invertibleSheaf D)
      (Stacks.Divisors.canonicalSection D) = D.supportSetᶜ :=
    (nonvanishingLocus_sectionsOfTop_eq _ _).symm.trans
      (Stacks.Divisors.nonvanishingLocus_canonicalSections D)
  set sM : Γ(M, ⊤) := hM.inv.app ⊤ (Stacks.Divisors.canonicalSection D)
  have hsM : Stacks.Ample.nonvanishingLocus M sM = D.supportSetᶜ :=
    (Stacks.Ample.nonvanishingLocus_congr hM.symm _).trans hc₀
  have hamp := isAmple_of_forall_isIrreducible (snd A (geomBase k K)).left _ (fun y hy => by
      obtain ⟨g, rfl⟩ := exists_ptOf_eq y hy
      obtain ⟨d, hd⟩ := exists_not_inSupp (K := K) D
      obtain ⟨y', hy₁, hy₂⟩ := exists_avoid D g (g⁻¹ * d)
      obtain ⟨t, ht⟩ := exists_tensorPower_section_ptOf D M hM' sM hsM (g⁻¹ * d) y'
      refine ⟨t, (ht g).mpr ⟨⟨?_, hy₁⟩, hy₂⟩⟩
      rwa [mul_inv_cancel_left])
    (fun C hC hCirr hCinf => by
      by_contra hno
      push Not at hno
      set CP : Set (geomBase k K ⟶ A) := {g | ptOf g ∈ C}
      have hCP : CP.Infinite := by
        refine fun hfin' => hCinf ((hfin'.image ptOf).subset ?_)
        rintro y ⟨hyC, hy⟩
        obtain ⟨g, rfl⟩ := exists_ptOf_eq y hy
        exact ⟨g, hyC, rfl⟩
      obtain ⟨c₀, hc₀C⟩ := hCP.nonempty
      have hZs : ((fun c => c * c₀⁻¹) '' CP).Infinite :=
        hCP.image fun a _ b _ hab => mul_right_cancel hab
      refine infinite_setOf_comap_transl_eq D _ hZs ?_ hfin
      rintro _ ⟨c, hcC, rfl⟩ d
      constructor
      · intro h
        have := inSupp_mul_of_forall_mem_nonvanishingLocus D M hM' sM hsM C hno hc₀C hcC h
        rwa [mul_comm d, ← _root_.mul_assoc, _root_.mul_assoc c₀, _root_.mul_assoc c₀,
          inv_mul_cancel_left, mul_inv_cancel_left] at this
      · intro h
        have := inSupp_mul_of_forall_mem_nonvanishingLocus D M hM' sM hsM C hno hcC hc₀C h
        rwa [mul_comm] at this)
  have h₁ := (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp hamp
  have h₂ := (isAmple_iff_tensorPower_isAmple _ _ 3 (by norm_num)).mpr h₁
  have e : (Stacks.Groupoids.pullbackOver (fst A (geomBase k K)) M :
      (A ⊗ geomBase k K).left.Modules) ≅
        (Scheme.Modules.pullback (fst A (geomBase k K)).left).obj M :=
    ((Stacks.ProjectiveBundleQuotients.pullbackIso (fst A (geomBase k K)).left).app M).symm
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (A ⊗ geomBase k K).left.toRingedSpace.presheaf
      (structureSheafRing (A ⊗ geomBase k K).left.toRingedSpace).property
      ((Scheme.Modules.pullback (fst A (geomBase k K)).left).obj M) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  have h₃ := Scheme.Modules.isAmple_of_iso e h₂
  exact (C1590Private.isAmple_iff_isAmple_pullback_of_isPullback A.hom
    (fst A (geomBase k K)).left (snd A (geomBase k K)).left (isPullback_fst_snd A K) M).mpr h₃

end Faltings
