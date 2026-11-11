module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Norm.FormNorm
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.Curve.Topology
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsTensorProduct
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne

/-!
# The function field of `C ×_k C`

Every point of `C` is the image of a point of `C ×_k C` under both projections; tensor charts
`Γ(U) ⊗_k Γ(U) ↪ k(C ×_k C)`; pull-backs of transcendental functions along the two projections
are algebraically independent; and `k(C ×_k C)` is spanned by, and of bounded degree over, a
compositum of the two pulled-back subfields.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Faltings.BombieriRoth

open BombieriSiegel BombieriVojta

universe u

section Product

open TensorProduct

/-- Every point `c` of `C` is the image of a point of `C ×_k C` under both projections. -/
public theorem exists_fst_eq_and_snd_eq {k : Type u} [Field k] {C X : Scheme.{u}}
    {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) (c : C) :
    ∃ z : X, pr₁ z = c ∧ pr₂ z = c := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) c c rfl
  refine ⟨hX.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, hX.isoPullback_inv_snd, hz₂]

/-- **A chart of `C ×_k C`.** For a nonempty affine open `U` of `C`, the sections over
`W = pr₁⁻¹ U ∩ pr₂⁻¹ U` are `Γ(U) ⊗_k Γ(U)`; so the map `a ⊗ b ↦ pr₂^* a · pr₁^* b` from
`Γ(U) ⊗_k Γ(U)` to `k(C ×_k C)` is injective, and every rational function on `C ×_k C` is a
quotient of two of its values. -/
public theorem exists_tensor_chart {k : Type u} [Field k] {C X : Scheme.{u}} [IsIntegral C]
    [IsIntegral X] (f : C ⟶ Spec (.of k)) {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f)
    (ι₁ ι₂ : C.functionField →+* X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra k Γ(C, U) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom.toAlgebra
    ∃ Θ : Γ(C, U) ⊗[k] Γ(C, U) →+* X.functionField, Function.Injective Θ ∧
      (∀ a b, Θ (a ⊗ₜ b) = ι₂ (C.germToFunctionField U a) * ι₁ (C.germToFunctionField U b)) ∧
      ∀ l : X.functionField, ∃ p q, Θ q ≠ 0 ∧ l = Θ p / Θ q := by
  let : Algebra k Γ(C, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom.toAlgebra
  set W : X.Opens := pr₁ ⁻¹ᵁ U ⊓ pr₂ ⁻¹ᵁ U with hWdef
  have hUtop : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := fun _ _ => trivial
  have hW : IsAffineOpen W :=
    isAffineOpen_of_isPullback hX (isAffineOpen_top (Spec (.of k))) hU hU hUtop hUtop hWdef
  have hWne : Nonempty W := by
    obtain ⟨⟨c, hc⟩⟩ := ‹Nonempty U›
    obtain ⟨z, hz₁, hz₂⟩ := exists_fst_eq_and_snd_eq hX c
    exact ⟨⟨z, show pr₁ z ∈ U from hz₁ ▸ hc, show pr₂ z ∈ U from hz₂ ▸ hc⟩⟩
  have : Nonempty (pr₁ ⁻¹ᵁ U) := ⟨⟨hWne.some.1, hWne.some.2.1⟩⟩
  have : Nonempty (pr₂ ⁻¹ᵁ U) := ⟨⟨hWne.some.1, hWne.some.2.2⟩⟩
  let eC : Γ(Spec (.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have hD : ∀ y : Γ(Spec (.of k), ⊤), (RingEquiv.refl Γ(C, U)) ((f.appLE ⊤ U hUtop).hom y) =
      algebraMap k Γ(C, U) (eC y) := fun y => by
    change _ = (f.appLE ⊤ U hUtop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom
      ((Scheme.ΓSpecIso (.of k)).hom.hom y))
    simp
  let e : Γ(X, W) ≃+* Γ(C, U) ⊗[k] Γ(C, U) :=
    sectionsTensorEquiv hX hUtop hUtop hWdef (isAffineOpen_top (Spec (.of k))) hU hU eC
      (RingEquiv.refl _) (RingEquiv.refl _) hD hD
  have he₂ : ∀ a : Γ(C, U), e.symm (a ⊗ₜ 1) = (pr₂.appLE U W (chart_le_preimage_right hWdef)) a :=
    fun a => e.symm_apply_eq.mpr
      (sectionsTensorEquiv_appLE_right hX hUtop hUtop hWdef _ hU hU eC _ _ hD hD a).symm
  have he₁ : ∀ b : Γ(C, U), e.symm (1 ⊗ₜ b) = (pr₁.appLE U W (chart_le_preimage_left hWdef)) b :=
    fun b => e.symm_apply_eq.mpr
      (sectionsTensorEquiv_appLE_left hX hUtop hUtop hWdef _ hU hU eC _ _ hD hD b).symm
  have hgermLE : ∀ {V : X.Opens} [Nonempty V] (h : W ≤ V) (t : Γ(X, V)),
      X.germToFunctionField W (X.presheaf.map (homOfLE h).op t) = X.germToFunctionField V t :=
    fun h t => X.presheaf.germ_res_apply (homOfLE h) _ _ t
  let Θ : Γ(C, U) ⊗[k] Γ(C, U) →+* X.functionField :=
    (X.germToFunctionField W).hom.comp (e.symm : Γ(C, U) ⊗[k] Γ(C, U) →+* Γ(X, W))
  have hΘinj : Function.Injective Θ :=
    (X.germToFunctionField_injective W).comp e.symm.injective
  refine ⟨Θ, hΘinj, fun a b => ?_, fun l => ?_⟩
  · have hab : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : Γ(C, U))) * ((1 : Γ(C, U)) ⊗ₜ[k] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change X.germToFunctionField W (e.symm (a ⊗ₜ b)) = _
    rw [hab, map_mul, map_mul, he₂, he₁, hι₁, hι₂]
    exact congrArg₂ (· * ·) (hgermLE inf_le_right _) (hgermLE inf_le_left _)
  · have := functionField_isFractionRing_of_isAffineOpen X W hW
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) l
    refine ⟨e p, e q, ?_, ?_⟩
    · change X.germToFunctionField W (e.symm (e q)) ≠ 0
      rw [e.symm_apply_apply]
      exact fun h => nonZeroDivisors.ne_zero hq
        (X.germToFunctionField_injective W (h.trans (map_zero _).symm))
    · change _ = X.germToFunctionField W (e.symm (e p)) / X.germToFunctionField W (e.symm (e q))
      rw [e.symm_apply_apply, e.symm_apply_apply]
      rfl

/-- The powers of an element transcendental over `k` are linearly independent over `k`. -/
public theorem linearIndependent_pow_of_transcendental {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] {z : A} (hz : Transcendental k z) : LinearIndependent k (fun i : ℕ => z ^ i) := by
  have h := (Polynomial.basisMonomials k).linearIndependent.map' (Polynomial.aeval z).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hz))
  have he : (fun i : ℕ => z ^ i) =
      (Polynomial.aeval z).toLinearMap ∘ Polynomial.basisMonomials k := by
    funext i
    simp [Polynomial.coe_basisMonomials]
  rwa [he]

/-- A rational function `ξ` on `C` over which `k(C)` is finite is transcendental over `k`, since
`k(C)` has transcendence degree one. -/
public theorem transcendental_of_finiteDimensional {k K : Type*} [Field k] [Field K]
    [Algebra k K] (htr : Algebra.trdeg k K ≠ 0) {ξ : K}
    [FiniteDimensional (IntermediateField.adjoin k {ξ}) K] : Transcendental k ξ := by
  intro halg
  have : FiniteDimensional k (IntermediateField.adjoin k {ξ}) :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  have : FiniteDimensional k K := Module.Finite.trans (IntermediateField.adjoin k {ξ}) K
  exact htr trdeg_eq_zero

/-- **Algebraic independence on `C ×_k C`.** If `ζ₁, ζ₂ ∈ k(C)` are transcendental over `k`, then
`pr₁^* ζ₁` and `pr₂^* ζ₂` are algebraically independent over `k` in `k(C ×_k C)`. -/
public theorem injective_aeval_of_transcendental {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ Spec (.of k)) {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) [Algebra k C.functionField]
    (hkC : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    [Algebra k X.functionField] (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    {ζ₁ ζ₂ : C.functionField} (h₁ : Transcendental k ζ₁) (h₂ : Transcendental k ζ₂) :
    Function.Injective
      (MvPolynomial.aeval ![ι₁ ζ₁, ι₂ ζ₂] : MvPolynomial (Fin 2) k →ₐ[k] X.functionField) := by
  -- an affine open `U` on which `ζ₁` and `ζ₂` are regular
  obtain ⟨V₁, hV₁, s₁, hs₁⟩ := TopCat.Presheaf.exists_germ_eq C.presheaf (x := genericPoint C) ζ₁
  obtain ⟨V₂, hV₂, s₂, hs₂⟩ := TopCat.Presheaf.exists_germ_eq C.presheaf (x := genericPoint C) ζ₂
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUV⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint C ∈ ((V₁ ⊓ V₂ : C.Opens) : Set C) from ⟨hV₁, hV₂⟩) (V₁ ⊓ V₂).isOpen
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hU₁ : U ≤ V₁ := fun x hx => (hUV hx).1
  have hU₂ : U ≤ V₂ := fun x hx => (hUV hx).2
  set z₁ : Γ(C, U) := C.presheaf.map (homOfLE hU₁).op s₁
  set z₂ : Γ(C, U) := C.presheaf.map (homOfLE hU₂).op s₂
  have hz₁ : C.germToFunctionField U z₁ = ζ₁ :=
    (C.presheaf.germ_res_apply (homOfLE hU₁) _ hηU s₁).trans hs₁
  have hz₂ : C.germToFunctionField U z₂ = ζ₂ :=
    (C.presheaf.germ_res_apply (homOfLE hU₂) _ hηU s₂).trans hs₂
  let : Algebra k Γ(C, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom.toAlgebra
  obtain ⟨Θ, hΘinj, hΘ, -⟩ :=
    exists_tensor_chart f hX ι₁.toRingHom ι₂.toRingHom hι₁ hι₂ U hU
  have hgermk : ∀ c : k, C.germToFunctionField U (algebraMap k Γ(C, U) c) =
      algebraMap k C.functionField c := by
    intro c
    rw [hkC]
    change C.presheaf.germ U _ hηU (C.presheaf.map (homOfLE (fun _ _ => trivial :
      U ≤ f ⁻¹ᵁ ⊤)).op ((f.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) = _
    rw [C.presheaf.germ_res_apply]
    rfl
  let g : Γ(C, U) →ₐ[k] C.functionField :=
    { toRingHom := (C.germToFunctionField U).hom, commutes' := hgermk }
  have ht₁ : Transcendental k z₁ := fun h => h₁ (hz₁ ▸ h.algHom g)
  have ht₂ : Transcendental k z₂ := fun h => h₂ (hz₂ ▸ h.algHom g)
  set ψ : MvPolynomial (Fin 2) k →ₐ[k] Γ(C, U) ⊗[k] Γ(C, U) :=
    MvPolynomial.aeval ![1 ⊗ₜ z₁, z₂ ⊗ₜ 1]
  have hcomp : ∀ p, MvPolynomial.aeval ![ι₁ ζ₁, ι₂ ζ₂] p = Θ (ψ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply,
        hΘ, hgermk, map_one]
      change _ = ι₂ (algebraMap k C.functionField a) * ι₁ 1
      rw [AlgHom.commutes, map_one, mul_one]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      congr 1
      fin_cases i
      · change ι₁ ζ₁ = Θ (1 ⊗ₜ z₁)
        rw [hΘ, map_one, hz₁]
        change ι₁ ζ₁ = ι₂ 1 * ι₁ ζ₁
        rw [map_one, one_mul]
      · change ι₂ ζ₂ = Θ (z₂ ⊗ₜ 1)
        rw [hΘ, map_one, hz₂]
        change ι₂ ζ₂ = ι₂ ζ₂ * ι₁ 1
        rw [map_one, mul_one]
  -- the monomials `z₂ ^ i ⊗ z₁ ^ j` are linearly independent
  have hT := (linearIndependent_pow_of_transcendental ht₂).tmul_of_flat_left
    (linearIndependent_pow_of_transcendental ht₁)
  set σ : (Fin 2 →₀ ℕ) → ℕ × ℕ := fun m => (m 1, m 0)
  have hσ : Function.Injective σ := by
    intro m n h
    simp only [σ, Prod.mk.injEq] at h
    ext i
    fin_cases i
    · exact h.2
    · exact h.1
  have hT' := hT.comp σ hσ
  have hψm : ∀ m : Fin 2 →₀ ℕ, ∀ c : k, ψ (MvPolynomial.monomial m c) =
      c • ((z₂ ^ (m 1)) ⊗ₜ[k] (z₁ ^ (m 0))) := by
    intro m c
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.TensorProduct.tmul_pow,
      one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.smul_def]
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [hcomp, ← map_zero Θ] at hp
  have hp' := hΘinj hp
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum] at hp'
  simp only [hψm] at hp'
  have hc := linearIndependent_iff'.mp hT' p.support (fun m => p.coeff m) hp'
  ext m
  by_cases hm : m ∈ p.support
  · simpa using hc m hm
  · simpa using MvPolynomial.notMem_support_iff.mp hm

/-- **Spanning set of `k(C ×_k C)` over a compositum.** If `k(C)` is finite over subfields `K₁`
and `K₂`, and `E ⊆ k(C ×_k C)` contains `pr₁^* K₁` and `pr₂^* K₂`, the products
`pr₁^* b_i · pr₂^* b'_j` of basis vectors of `k(C)` over `K₁` and `K₂` span `k(C ×_k C)` over
`E`: they span an `E`-subalgebra, finite over `E` and hence a field, which contains the values of
a tensor chart and so their quotients. -/
public theorem span_eq_top_of_isPullback {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ Spec (.of k)) {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) [Algebra k C.functionField] [Algebra k X.functionField]
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (K₁ K₂ : IntermediateField k C.functionField) [FiniteDimensional K₁ C.functionField]
    [FiniteDimensional K₂ C.functionField] (E : IntermediateField k X.functionField)
    (hE₁ : ∀ c ∈ K₁, ι₁ c ∈ E) (hE₂ : ∀ c ∈ K₂, ι₂ c ∈ E) :
    Submodule.span E (Set.range fun p : Fin (Module.finrank K₁ C.functionField) ×
        Fin (Module.finrank K₂ C.functionField) =>
      ι₁ (Module.finBasis K₁ C.functionField p.1) * ι₂ (Module.finBasis K₂ C.functionField p.2)) =
      ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint C)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  let : Algebra k Γ(C, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom.toAlgebra
  obtain ⟨Θ, -, hΘ, hfrac⟩ := exists_tensor_chart f hX ι₁.toRingHom ι₂.toRingHom hι₁ hι₂ U hU
  set b₁ := Module.finBasis K₁ C.functionField
  set b₂ := Module.finBasis K₂ C.functionField
  set gen : Fin (Module.finrank K₁ C.functionField) × Fin (Module.finrank K₂ C.functionField) →
    X.functionField := fun p => ι₁ (b₁ p.1) * ι₂ (b₂ p.2)
  set S : Submodule E X.functionField := Submodule.span E (Set.range gen)
  have hprod : ∀ c c' : C.functionField, ι₁ c * ι₂ c' ∈ S := by
    intro c c'
    rw [← b₁.sum_repr c, ← b₂.sum_repr c', map_sum, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
    have he : ι₁ (algebraMap K₁ C.functionField (b₁.repr c i)) *
        ι₂ (algebraMap K₂ C.functionField (b₂.repr c' j)) ∈ E :=
      E.mul_mem (hE₁ _ (b₁.repr c i).2) (hE₂ _ (b₂.repr c' j).2)
    have : ι₁ (algebraMap K₁ C.functionField (b₁.repr c i)) * ι₁ (b₁ i) *
        (ι₂ (algebraMap K₂ C.functionField (b₂.repr c' j)) * ι₂ (b₂ j)) =
        (⟨_, he⟩ : E) • gen (i, j) := by
      rw [Algebra.smul_def]
      change _ = (ι₁ (algebraMap K₁ C.functionField (b₁.repr c i)) *
        ι₂ (algebraMap K₂ C.functionField (b₂.repr c' j))) * (ι₁ (b₁ i) * ι₂ (b₂ j))
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hone : (1 : X.functionField) ∈ S := by simpa using hprod 1 1
  have hmul : ∀ x y : X.functionField, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hle : S * S ≤ S := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, rfl⟩
      change ι₁ (b₁ p.1) * ι₂ (b₂ p.2) * (ι₁ (b₁ q.1) * ι₂ (b₂ q.2)) ∈ S
      have := hprod (b₁ p.1 * b₁ q.1) (b₂ p.2 * b₂ q.2)
      rw [map_mul, map_mul] at this
      convert this using 1
      ring
    exact hle (Submodule.mul_mem_mul hx hy)
  set A : Subalgebra E X.functionField := S.toSubalgebra hone hmul
  have hfg : (Subalgebra.toSubmodule A).FG := Submodule.fg_span (Set.finite_range gen)
  have hΘS : ∀ p, Θ p ∈ S := by
    intro p
    induction p using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul a b =>
      rw [hΘ, mul_comm]
      exact hprod _ _
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  refine eq_top_iff.mpr fun l _ => ?_
  obtain ⟨p, q, hq, rfl⟩ := hfrac l
  have hinv : (Θ q)⁻¹ ∈ A :=
    IsIntegral.inv_mem (IsIntegral.of_mem_of_fg A hfg _ (hΘS q)) (hΘS q)
  rw [div_eq_mul_inv]
  exact hmul _ _ (hΘS p) hinv

/-- **Finiteness of `k(C ×_k C)` over a compositum.** If `k(C)` is finite over subfields `K₁`
and `K₂`, and `E ⊆ k(C ×_k C)` contains `pr₁^* K₁` and `pr₂^* K₂`, then `k(C ×_k C)` is finite
over `E`. -/
public theorem finite_of_isPullback {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ Spec (.of k)) {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) [Algebra k C.functionField] [Algebra k X.functionField]
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (K₁ K₂ : IntermediateField k C.functionField) [FiniteDimensional K₁ C.functionField]
    [FiniteDimensional K₂ C.functionField] (E : IntermediateField k X.functionField)
    (hE₁ : ∀ c ∈ K₁, ι₁ c ∈ E) (hE₂ : ∀ c ∈ K₂, ι₂ c ∈ E) :
    Module.Finite E X.functionField :=
  ⟨span_eq_top_of_isPullback f hX ι₁ ι₂ hι₁ hι₂ K₁ K₂ E hE₁ hE₂ ▸
    Submodule.fg_span (Set.finite_range _)⟩

/-- **The degree of `k(C ×_k C)` over a compositum.** If `k(C)` is finite over subfields `K₁`
and `K₂`, and `E ⊆ k(C ×_k C)` contains `pr₁^* K₁` and `pr₂^* K₂`, then
`[k(C ×_k C) : E] ≤ [k(C) : K₁] · [k(C) : K₂]`. -/
public theorem finrank_le_mul_of_isPullback {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ Spec (.of k)) {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) [Algebra k C.functionField] [Algebra k X.functionField]
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (K₁ K₂ : IntermediateField k C.functionField) [FiniteDimensional K₁ C.functionField]
    [FiniteDimensional K₂ C.functionField] (E : IntermediateField k X.functionField)
    (hE₁ : ∀ c ∈ K₁, ι₁ c ∈ E) (hE₂ : ∀ c ∈ K₂, ι₂ c ∈ E) :
    Module.finrank E X.functionField ≤
      Module.finrank K₁ C.functionField * Module.finrank K₂ C.functionField := by
  have h := finrank_range_le_card (R := E) fun p : Fin (Module.finrank K₁ C.functionField) ×
      Fin (Module.finrank K₂ C.functionField) =>
    ι₁ (Module.finBasis K₁ C.functionField p.1) * ι₂ (Module.finBasis K₂ C.functionField p.2)
  rw [Set.finrank, span_eq_top_of_isPullback f hX ι₁ ι₂ hι₁ hι₂ K₁ K₂ E hE₁ hE₂,
    finrank_top] at h
  simpa [Fintype.card_prod] using h

end Product

end Faltings.BombieriRoth
