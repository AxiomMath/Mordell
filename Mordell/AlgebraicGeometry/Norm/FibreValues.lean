module
public import Mordell.AlgebraicGeometry.Norm.FibreMultiplicity

/-!
# Values of a norm along the fibres of a finite free morphism

Let `S` be an `R`-algebra which is free of finite rank as an `R`-module, and let `f : S`. The
norm `Algebra.norm R f` is the determinant of multiplication by `f`. Its value at a point `p` of
`Spec R` is computed from the fibre of `Spec S → Spec R` over `p`: the fibre algebra
`S ⊗_R κ(p)` is a finite product of local Artinian `κ(p)`-algebras, one for each prime `q` of
`S` over `p`, of length `e_q = Faltings.fibreMultiplicity`, and on the factor at `q` the
determinant of multiplication by `f` is `N_{κ(q)/κ(p)}(f(q)) ^ e_q`. Hence
`(Norm f)(p) = ∏_{q ↦ p} N_{κ(q)/κ(p)}(f(q)) ^ e_q`. When `κ(q) = κ(p)`, as for a geometric
point `p` over an algebraically closed field, the factor is `f(q) ^ e_q`.

This is applied with `S = 𝒪(W_{ab})` the coordinate ring of the affine open `W_{ab} = U × U` of
`C × C`, free over `R = k[ξ_a, ξ'_b]`, and `p` a `k̄`-point of `𝔸¹ × 𝔸¹`.

## Main results

* `Faltings.algebraMap_norm_eq_finprod_norm_pow_fibreMultiplicity`: the value of
  `Algebra.norm R f` at `p` is `∏ᶠ q ↦ p, Algebra.norm κ(p) f(q) ^ e_q`.

## Implementation notes

The source fixes a geometric point `p`, so that all residue fields `κ(q)` equal `κ(p) = k̄`;
the statement is made for an arbitrary prime `p` of `R`, with the residue-field norm
`κ(q) → κ(p)` in each factor. The multiplicity `fibreMultiplicity` is `ℕ∞`-valued and finite
here, since the fibre is finite over `κ(p)`; it enters as an exponent through `ENat.toNat`.
`R` and `S` lie in one universe, as `Spec.map` requires.

## References

* [Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9.
-/

open IsLocalRing AlgebraicGeometry CategoryTheory Limits

universe u

namespace Faltings

private theorem det_lsmul_eq_norm_residue_pow {κ B : Type*} [Field κ] [CommRing B]
    [IsLocalRing B] [Algebra κ B] (b : B) (n : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module B M] [Module κ M] [IsScalarTower κ B M]
      [FiniteDimensional κ M], Module.finrank κ M = n →
    LinearMap.det ((LinearMap.lsmul B M b).restrictScalars κ) =
      Algebra.norm κ (residue B b) ^ (Module.length B M).toNat := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [Module.length_eq_zero, LinearMap.det_eq_one_of_subsingleton]
    simp
  have : IsArtinian B M := isArtinian_of_tower κ inferInstance
  have : IsNoetherian B M := isNoetherian_of_tower κ inferInstance
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule B M)).resolve_left
    top_ne_bot
  have hNs : IsSimpleModule B N := isSimpleModule_iff_isAtom.mpr hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hNs
  rw [eq_maximalIdeal hm] at e
  let W := N.restrictScalars κ
  let f := (LinearMap.lsmul B M b).restrictScalars κ
  have hf : W ≤ W.comap f := fun x hx => N.smul_mem b hx
  rw [LinearMap.det_eq_det_mul_det W f hf]
  -- the simple submodule `N ≅ κ(B)`
  let eW : W ≃ₗ[κ] ResidueField B :=
    ((Submodule.restrictScalarsEquiv κ B M N).restrictScalars κ).trans (e.restrictScalars κ)
  have : FiniteDimensional κ (ResidueField B) := eW.finiteDimensional
  have h1 : LinearMap.det (f.restrict hf) = Algebra.norm κ (residue B b) := by
    rw [← LinearMap.det_conj (f.restrict hf) eW, Algebra.norm_apply]
    congr 1
    ext y
    obtain ⟨x, rfl⟩ := eW.surjective y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    change e ⟨b • x.1, N.smul_mem b x.2⟩ = _
    rw [show (⟨b • x.1, N.smul_mem b x.2⟩ : N) = b • ⟨x.1, x.2⟩ from rfl, e.map_smul,
      Algebra.smul_def]
    rfl
  -- the quotient `M ⧸ N`
  let eQ : (M ⧸ W) ≃ₗ[κ] M ⧸ N := Submodule.Quotient.restrictScalarsEquiv κ N
  have : FiniteDimensional κ (M ⧸ N) := Module.Finite.equiv eQ
  have : IsArtinian B (M ⧸ N) := isArtinian_of_tower κ inferInstance
  have : IsNoetherian B (M ⧸ N) := isNoetherian_of_tower κ inferInstance
  have hfin : Module.finrank κ (M ⧸ N) < n := by
    rw [← eQ.finrank_eq, ← hn, ← Submodule.finrank_quotient_add_finrank W]
    have : 0 < Module.finrank κ W := by
      rw [eW.finrank_eq]; exact Module.finrank_pos
    omega
  have h2 : LinearMap.det (W.mapQ W f hf) =
      Algebra.norm κ (residue B b) ^ (Module.length B (M ⧸ N)).toNat := by
    rw [← ih _ hfin (M ⧸ N) rfl, ← LinearMap.det_conj (W.mapQ W f hf) eQ]
    congr 1
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change eQ (W.mapQ W f hf (eQ.symm (Submodule.Quotient.mk x))) = _
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply,
      Submodule.Quotient.restrictScalarsEquiv_mk]
    rfl
  have hlen : Module.length B M = 1 + Module.length B (M ⧸ N) := by
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), Module.length_eq_one]
  have hne : Module.length B (M ⧸ N) ≠ ⊤ := Module.length_ne_top
  rw [h1, h2, hlen, ENat.toNat_add ENat.one_ne_top hne, ENat.toNat_one, pow_add, pow_one]

private theorem norm_eq_norm_residue_pow {κ B : Type*} [Field κ] [CommRing B]
    [IsLocalRing B] [Algebra κ B] [FiniteDimensional κ B] (b : B) :
    Algebra.norm κ b = Algebra.norm κ (residue B b) ^ (Module.length B B).toNat := by
  rw [← det_lsmul_eq_norm_residue_pow b _ B rfl, Algebra.norm_apply]
  rfl

private theorem norm_mulSingle {κ ι : Type*} [Field κ] [DecidableEq ι] [Finite ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra κ (B i)]
    [∀ i, FiniteDimensional κ (B i)] (i : ι) (a : B i) :
    Algebra.norm κ (Pi.mulSingle i a : Π j, B j) = Algebra.norm κ a := by
  let π : (Π j, B j) →ₗ[κ] B i := LinearMap.proj i
  have hπ : Function.Surjective π := fun z => ⟨Pi.single i z, Pi.single_eq_same i z⟩
  let W := LinearMap.ker π
  let f := Algebra.lmul κ (Π j, B j) (Pi.mulSingle i a)
  have hf : W ≤ W.comap f := fun y (hy : y i = 0) => by
    change (Pi.mulSingle i a * y) i = 0
    simp [hy]
  rw [Algebra.norm_apply, LinearMap.det_eq_det_mul_det W _ hf]
  have h1 : f.restrict hf = LinearMap.id := by
    refine LinearMap.ext fun ⟨y, hy⟩ => Subtype.ext (funext fun j => ?_)
    change (Pi.mulSingle i a * y) j = y j
    by_cases hj : j = i
    · subst hj
      have hy : y j = 0 := hy
      simp [hy]
    · simp [Pi.mulSingle_eq_of_ne hj]
  let eq := π.quotKerEquivOfSurjective hπ
  rw [h1, LinearMap.det_id, one_mul, ← LinearMap.det_conj _ eq, Algebra.norm_apply]
  congr 1
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := eq.surjective z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, Submodule.mapQ_apply]
  change (Pi.mulSingle i a * y) i = a * y i
  simp

private theorem norm_pi {κ ι : Type*} [Field κ] [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra κ (B i)]
    [∀ i, FiniteDimensional κ (B i)] (x : Π i, B i) :
    Algebra.norm κ x = ∏ i, Algebra.norm κ (x i) := by
  classical
  conv_lhs => rw [← Finset.univ_prod_mulSingle x]
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => norm_mulSingle i (x i)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fiberIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫ pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫
    asIso (pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) _).inv)
      (𝟙 _) (𝟙 _) (by simp) (by simp)) ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S

set_option backward.isDefEq.respectTransparency false in
private theorem fiberIso_hom_includeRight (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    (fiberIso R S p).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField) (B := S)).toRingHom) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p := by
  simp [fiberIso, Scheme.Hom.fiberι]

private theorem length_self_eq_of_ringEquiv {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') :
    Module.length A A = Module.length A' A' := by
  have : RingHomSurjective (e : A →+* A') := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* A')] A' :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

private theorem comap_includeRight_injective (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    Function.Injective (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField) (B := S)).toRingHom) := fun _ _ h =>
  (PrimeSpectrum.preimageEquivFiber R S p).symm.injective (Subtype.ext h)

private theorem algebraMap_norm_eq_norm_tmul {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Module.Free R S] [Module.Finite R S] (f : S) :
    algebraMap R A (Algebra.norm R f) = Algebra.norm A ((1 : A) ⊗ₜ[R] f) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext s
  simp

/-- The fibre multiplicity of `Spec S → Spec R` at a prime `q` of `S` over `p` is the length of
the localization of the fibre algebra `κ(p) ⊗[R] S` at the prime `P` corresponding to `q`. -/
private theorem fibreMultiplicity_eq_length (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) (P : PrimeSpectrum (p.asIdeal.Fiber S))
    (q : PrimeSpectrum S) (hq : q.comap (algebraMap R S) = p)
    (hP : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField) (B := S)).toRingHom P = q) :
    fibreMultiplicity (Spec.map (CommRingCat.ofHom (algebraMap R S))) q =
      Module.length (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal) := by
  subst hq
  set φ := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let E := fiberIso R S (φ q)
  have hx : E.hom (φ.asFiber q) = P := by
    refine comap_includeRight_injective R S (φ q) (Eq.trans ?_ hP.symm)
    conv_rhs => rw [← φ.fiberι_asFiber q, ← fiberIso_hom_includeRight R S (φ q)]
    rfl
  subst hx
  exact length_self_eq_of_ringEquiv
    ((asIso (E.hom.stalkMap (φ.asFiber q))).symm ≪≫ Spec.stalkIso _ _).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
private theorem norm_residue_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (P : PrimeSpectrum (p.asIdeal.Fiber S)) (f : S)
    (h : (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := R)
        (A := p.asIdeal.ResidueField) (B := S)).toRingHom P).comap (algebraMap R S) = p) :
    letI := (Ideal.ResidueField.map p.asIdeal (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := S)).toRingHom P).asIdeal (algebraMap R S)
          (congrArg PrimeSpectrum.asIdeal h).symm).toAlgebra
    Algebra.norm p.asIdeal.ResidueField (algebraMap S (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := S)).toRingHom P).asIdeal.ResidueField f) =
      @Algebra.norm p.asIdeal.ResidueField (ResidueField (Localization.AtPrime P.asIdeal)) _ _
        (ResidueField.algebra _) (residue (Localization.AtPrime P.asIdeal)
          (algebraMap (p.asIdeal.Fiber S) (Localization.AtPrime P.asIdeal)
            ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] f))) := by
  let g := (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := S)).toRingHom
  let q := PrimeSpectrum.comap g P
  let _ := (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S)
    (congrArg PrimeSpectrum.asIdeal h).symm).toAlgebra
  let _ : Algebra p.asIdeal.ResidueField P.asIdeal.ResidueField := ResidueField.algebra _
  let σ := Ideal.ResidueField.map q.asIdeal P.asIdeal g rfl
  have hσ : Function.Bijective σ :=
    (RingHom.SurjectiveOnStalks.baseChange'
      (Ideal.surjectiveOnStalks_residueField p.asIdeal)).residueFieldMap_bijective _ _ rfl
  have hc : σ.comp (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField) =
      algebraMap p.asIdeal.ResidueField P.asIdeal.ResidueField := by
    ext r
    simp [σ, RingHom.algebraMap_toAlgebra, g]
    rfl
  let e : q.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] P.asIdeal.ResidueField :=
    AlgEquiv.ofBijective { σ with commutes' := fun c => congrArg (fun φ => φ c) hc } hσ
  rw [← Algebra.norm_eq_of_algEquiv e]
  congr 1
  change σ (algebraMap S _ f) = _
  rw [Ideal.ResidueField.map_algebraMap]
  rfl

/-- Let `S` be a free `R`-algebra of finite rank, `f : S` and `p` a prime of `R`. The value at
`p` of `Algebra.norm R f` is the product, over the primes `q` of `S` lying over `p`, of the norm
from `κ(q)` to `κ(p)` of the value of `f` at `q`, raised to the fibre multiplicity
`fibreMultiplicity` of `Spec S → Spec R` at `q`. -/
@[faltings "lem_bvr_norm_fibre_product"]
public theorem algebraMap_norm_eq_finprod_norm_pow_fibreMultiplicity {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] (f : S)
    (p : PrimeSpectrum R) :
    algebraMap R p.asIdeal.ResidueField (Algebra.norm R f) =
      ∏ᶠ (q : PrimeSpectrum S) (h : q.comap (algebraMap R S) = p),
        letI := (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S)
          (congrArg PrimeSpectrum.asIdeal h).symm).toAlgebra
        Algebra.norm p.asIdeal.ResidueField (algebraMap S q.asIdeal.ResidueField f) ^
          (fibreMultiplicity (Spec.map (CommRingCat.ofHom (algebraMap R S))) q).toNat := by
  classical
  let κ := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let g : S →+* F := (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := S)).toRingHom
  let ψ : PrimeSpectrum F → PrimeSpectrum S := PrimeSpectrum.comap g
  have hψ : Function.Injective ψ := comap_includeRight_injective R S p
  have hψp : ∀ P, (ψ P).comap (algebraMap R S) = p := fun P =>
    ((PrimeSpectrum.preimageEquivFiber R S p).symm P).2
  have hψs : ∀ q : PrimeSpectrum S, q.comap (algebraMap R S) = p → q ∈ Set.range ψ :=
    fun q hq => ⟨PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩,
      congrArg Subtype.val ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)⟩
  have : IsArtinianRing F := IsArtinianRing.of_finite κ F
  let _ : Fintype (PrimeSpectrum F) := Fintype.ofFinite _
  let e := (PrimeSpectrum.toPiLocalizationEquiv F).restrictScalars κ
  have hfin : ∀ P : PrimeSpectrum F, FiniteDimensional κ (Localization.AtPrime P.asIdeal) :=
    fun P => Module.Finite.of_surjective ((LinearMap.proj P).comp e.toLinearMap)
      ((Function.surjective_eval P).comp e.surjective)
  rw [algebraMap_norm_eq_norm_tmul, ← Algebra.norm_eq_of_algEquiv e, norm_pi,
    finprod_eq_prod_of_mulSupport_subset (s := Finset.univ.image ψ) _ ?_]
  · rw [Finset.prod_image fun _ _ _ _ h => hψ h]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [@finprod_unique _ _ _ (uniqueProp (hψp P)),
      show e ((1 : κ) ⊗ₜ[R] f) P = algebraMap F (Localization.AtPrime P.asIdeal)
        ((1 : κ) ⊗ₜ[R] f) from rfl, norm_eq_norm_residue_pow]
    exact congrArg₂ (· ^ ·) (norm_residue_eq p P f (hψp P)).symm
      (congrArg ENat.toNat (fibreMultiplicity_eq_length R S p P (ψ P) (hψp P) rfl).symm)
  · intro q hq
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hψs q (by_contra fun hne => hq (@finprod_of_isEmpty _ _ _ ⟨hne⟩ _))

end Faltings
