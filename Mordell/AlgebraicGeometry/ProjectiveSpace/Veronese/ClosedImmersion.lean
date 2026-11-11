module

public import Mathlib
public import Mordell.Attr
public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-!
# The Veronese map is a closed immersion

Let `R` be a commutative ring, `e ≥ 1`, and let `ℙ(σ)_R = Proj R[X_s : s ∈ σ]` be the projective
space over `R` with homogeneous coordinates indexed by `σ`, a scheme over `Spec R` through its
degree `0` part. The Veronese morphism of degree `e` is
`Φ_e : ℙ(ι)_R ⟶ ℙ({I : ι →₀ ℕ // |I| = e})_R`, whose coordinates are the monomials
`y_I = x^I` of degree `e`: over the affine chart `D₊(x_i)` it lands in the chart
`D₊(y_{e • eᵢ})` (as `y_{e • eᵢ} = x_i ^ e`) and pulls back the coordinate `y_J / y_{e • eᵢ}`
to `x^J / x_i ^ e`. This morphism is a closed immersion. On `K`-points it is
`Faltings.veroneseMap`.

## Main results

* `Faltings.exists_isClosedImmersion_veronese`: for `e ≥ 1` the morphism
  `ℙ(ι)_R ⟶ ℙ({I // |I| = e})_R` over `Spec R`, given on the charts by
  `y_J / y_{e • eᵢ} ↦ x^J / x_i ^ e`, exists and is a closed immersion.

## Implementation notes

Projective space is `AlgebraicGeometry.Proj` of `MvPolynomial σ R` with the grading by total
degree (`MvPolynomial.gradedAlgebra`); its structure morphism is `Proj.toSpecZero` followed by
`Spec` of `algebraMap R` into the degree `0` part. The charts are `Proj.awayι` at the
coordinate `X s`, whose rings are the degree `0` localizations
`HomogeneousLocalization.Away`; the element `x^J / x_i ^ e` is
`HomogeneousLocalization.Away.mk` of the monomial `x^J ∈ R[X]_e` over the `e`-th power of
`x_i`. The morphism is required to be over `Spec R`, and is pinned by its restrictions to the
charts `D₊(x_i)`, which cover `ℙ(ι)_R`: each maps into `D₊(y_{e • eᵢ})` and the induced ring
map sends `y_J / y_{e • eᵢ}` to `x^J / x_i ^ e`. Since the `y_J / y_{e • eᵢ}` generate the
ring of `D₊(y_{e • eᵢ})`, these conditions determine the morphism, so the existential
statement is the statement about the Veronese morphism. The base ring and the index type are
arbitrary; for `R = K` a field and `ι = Fin (n + 1)` this is
`Φ_e : ℙⁿ → ℙ^{binom (n + e) n - 1}`, there being `binom (n + e) n` monomials of degree `e`.

## References

* [Hartshorne, *Algebraic Geometry*, I Ex. 2.12, II Ex. 5.13][hartshorne1977]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Faltings

/-- `a / 1 = a / f ^ 0` in a degree-zero localization. -/
private theorem fromZeroRingHom_eq_away_mk {A σ' : Type*} [CommRing A] [SetLike σ' A]
    [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (a : 𝒜 0) :
    fromZeroRingHom 𝒜 (Submonoid.powers f) a = Away.mk 𝒜 hf 0 a (by simp) := by
  ext
  simp only [fromZeroRingHom, Away.val_mk, pow_zero]
  rfl

/-- `Away.mk` only depends on the exponent and the numerator, not on their spelling. -/
theorem away_mk_congr {A σ' : Type*} [CommRing A] [SetLike σ' A]
    [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    {n n' : ℕ} (hn : n = n') {a a' : A} (ha : a = a') (h : a ∈ 𝒜 (n • d))
    (h' : a' ∈ 𝒜 (n' • d)) :
    Away.mk 𝒜 hf n a h = Away.mk 𝒜 hf n' a' h' := by
  subst hn ha
  rfl

section VeroneseRing

/-- The coordinate `x_s` is homogeneous of degree one. -/
theorem X_mem (R : Type u) [CommRing R] {σ : Type*} (s : σ) :
    X (R := R) s ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R s)

variable {R : Type u} [CommRing R] {ι κ : Type*} {e : ℕ}
  (σ : {I : ι →₀ ℕ // I.degree = e} ≃ κ)

/-- The multi-index `e • eᵢ`. -/
noncomputable abbrev singleIdx (i : ι) : {I : ι →₀ ℕ // I.degree = e} :=
  ⟨Finsupp.single i e, Finsupp.degree_single i e⟩

/-- `y_{σ J} ↦ x^J`. -/
noncomputable def veroneseAlgHom : MvPolynomial κ R →ₐ[R] MvPolynomial ι R :=
  aeval fun k => monomial (σ.symm k).1 1

theorem veroneseAlgHom_X (J : {I : ι →₀ ℕ // I.degree = e}) :
    veroneseAlgHom σ (X (σ J) : MvPolynomial κ R) = monomial J.1 1 := by
  simp [veroneseAlgHom]

theorem veroneseAlgHom_mem ⦃m : ℕ⦄ ⦃p : MvPolynomial κ R⦄
    (hp : p ∈ homogeneousSubmodule κ R m) :
    veroneseAlgHom σ p ∈ homogeneousSubmodule ι R (m * e) := by
  rw [mem_homogeneousSubmodule] at hp ⊢
  rw [mul_comm]
  exact hp.aeval _ fun k => isHomogeneous_monomial _ (σ.symm k).2

/-- A monomial `x^K` of degree `m e` is the image of a homogeneous polynomial of degree `m`. -/
theorem exists_mem_eq_monomial (m : ℕ) :
    ∀ K : ι →₀ ℕ, K.degree = m * e → ∃ p ∈ homogeneousSubmodule κ R m,
      veroneseAlgHom σ p = monomial K (1 : R) := by
  induction m with
  | zero =>
    intro K hK
    rw [zero_mul, Finsupp.degree_eq_zero_iff] at hK
    subst hK
    exact ⟨1, (mem_homogeneousSubmodule 0 _).2 (isHomogeneous_one _ _), by simp⟩
  | succ m ih =>
    intro K hK
    obtain ⟨J, hJK, hJ⟩ := K.exists_le_degree_eq e (by rw [hK]; nlinarith)
    obtain ⟨p, hp, hpK⟩ := ih (K - J) (by
      rw [← add_tsub_cancel_of_le hJK, map_add, hJ] at hK; rw [add_mul, one_mul] at hK; omega)
    refine ⟨X (σ ⟨J, hJ⟩) * p, ?_, ?_⟩
    · rw [add_comm]
      exact SetLike.mul_mem_graded ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R _)) hp
    · rw [map_mul, hpK, veroneseAlgHom_X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hJK]

/-- Every polynomial homogeneous of degree `m e` is the image of one homogeneous of degree
`m`. -/
theorem exists_mem_eq (m : ℕ) {b : MvPolynomial ι R}
    (hb : b ∈ homogeneousSubmodule ι R (m * e)) :
    ∃ p ∈ homogeneousSubmodule κ R m, veroneseAlgHom σ p = b := by
  have hb' : b.IsHomogeneous (m * e) := (mem_homogeneousSubmodule _ _).1 hb
  rw [b.as_sum]
  refine Finset.sum_induction _ (fun b => ∃ p ∈ homogeneousSubmodule κ R m,
      veroneseAlgHom (R := R) σ p = b) (fun _ _ ⟨p, hp, hpb⟩ ⟨q, hq, hqb⟩ =>
      ⟨p + q, add_mem hp hq, by rw [map_add, hpb, hqb]⟩) ⟨0, zero_mem _, map_zero _⟩
    fun K hK => ?_
  obtain ⟨p, hp, hpK⟩ := exists_mem_eq_monomial (R := R) σ m K (by
    rw [Finsupp.degree_eq_weight_one]; exact hb' (mem_support_iff.1 hK))
  refine ⟨b.coeff K • p, Submodule.smul_mem _ _ hp, ?_⟩
  rw [map_smul, hpK, smul_monomial, smul_eq_mul, mul_one]

end VeroneseRing

section ScaledMap

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ] (φ : A →+* B) {e : ℕ}
  (hφ : ∀ ⦃n : ℕ⦄ ⦃a : A⦄, a ∈ 𝒜 n → φ a ∈ ℬ (n * e))
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap φ)

private noncomputable def scaledFun :
    HomogeneousLocalization 𝒜 P → HomogeneousLocalization ℬ Q :=
  Quotient.map' (fun x ↦ ⟨x.1 * e, ⟨_, hφ x.2.2⟩, ⟨_, hφ x.3.2⟩, hPQ x.4⟩)
    fun x y (h : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (S := Localization P) (Localization Q) φ hPQ at h
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at h
      exact h

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
private theorem val_scaledFun (x : HomogeneousLocalization 𝒜 P) :
    (scaledFun φ hφ hPQ x).val =
      IsLocalization.map (S := Localization P) (Localization Q) φ hPQ x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  change (mk ⟨c.1 * e, ⟨_, hφ c.2.2⟩, ⟨_, hφ c.3.2⟩, hPQ c.4⟩ : HomogeneousLocalization ℬ Q).val = _
  simp only [val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']

/-- `a / s ↦ φ a / φ s` on degree-zero localizations, for a ring map `φ` multiplying degrees
by `e`. -/
private noncomputable def scaledMap :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := scaledFun φ hφ hPQ
  map_one' := val_injective _ (by simp [val_scaledFun])
  map_mul' x y := val_injective _ (by simp [val_scaledFun])
  map_zero' := val_injective _ (by simp [val_scaledFun])
  map_add' x y := val_injective _ (by simp [val_scaledFun])

private theorem val_scaledMap (x : HomogeneousLocalization 𝒜 P) :
    (scaledMap φ hφ hPQ x).val =
      IsLocalization.map (S := Localization P) (Localization Q) φ hPQ x.val :=
  val_scaledFun φ hφ hPQ x

variable {φ} in
/-- The degree-scaling map `A₍t₎ → B₍s₎`, `a / tⁿ ↦ φ a / sⁿ`, for `φ t = s`. -/
private noncomputable def awayScaled {t : A} {s : B} (h : φ t = s) :
    Away 𝒜 t →+* Away ℬ s :=
  scaledMap φ hφ (P := Submonoid.powers t) (Q := Submonoid.powers s) <| by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [h]⟩

variable {φ}

private theorem awayScaled_mk {t : A} {s : B} (h : φ t = s) {d : ℕ} (ht : t ∈ 𝒜 d)
    (hs : s ∈ ℬ (d * e)) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) (ha' : φ a ∈ ℬ (n • (d * e))) :
    awayScaled hφ h (Away.mk 𝒜 ht n a ha) = Away.mk ℬ hs n (φ a) ha' := by
  apply val_injective
  rw [awayScaled, val_scaledMap, Away.val_mk, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', Localization.mk_eq_mk']
  congr 2
  simp [h]

private theorem awayMap_comp_awayScaled {t t' x : A} {s s' y : B} (h : φ t = s) (h' : φ t' = s')
    (hxy : φ x = y) {d d' : ℕ} (ht : t ∈ 𝒜 d) (ht' : t' ∈ 𝒜 d') (hs' : s' ∈ ℬ (d' * e))
    (hx : x = t * t') (hy : y = s * s') :
    (awayMap ℬ hs' hy).comp (awayScaled hφ h) = (awayScaled hφ hxy).comp (awayMap 𝒜 ht' hx) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht z
  have hs : s ∈ ℬ (d * e) := h ▸ hφ ht
  have hy' : y ∈ ℬ ((d + d') * e) := hxy ▸ hφ (hx ▸ SetLike.mul_mem_graded ht ht')
  simp only [RingHom.comp_apply, awayScaled_mk hφ h ht hs n a ha (by simpa [mul_assoc] using hφ ha),
    awayMap_mk, awayScaled_mk hφ hxy (hx ▸ SetLike.mul_mem_graded ht ht') hy' n _ _
      (by
        have := hφ (SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n ht'))
        rwa [show (n • d + n • d') * e = n • ((d + d') * e) by simp; ring] at this)]
  rw [Away.val_mk, Away.val_mk]
  congr 1
  simp [h']

private theorem away_mk_pow {f : B} {d : ℕ} (hf : f ∈ ℬ d) (n : ℕ) (a : B) (ha : a ∈ ℬ (n • d))
    (p : ℕ) (ha' : a ^ p ∈ ℬ ((n * p) • d)) :
    Away.mk ℬ hf n a ha ^ p = Away.mk ℬ hf (n * p) (a ^ p) ha' := by
  apply val_injective
  rw [HomogeneousLocalization.val_pow, Away.val_mk, Away.val_mk, Localization.mk_pow]
  congr 2
  ext; simp [pow_mul]

end ScaledMap

section Glue

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- The affine open cover of `Proj 𝒜` by the `D₊(f j)`, given that they cover. -/
private noncomputable def affineOpenCoverOfISupEqTop (𝒜 : ℕ → σ) [GradedRing 𝒜] {I : Type*}
    (f : I → A) {m : I → ℕ} (f_deg : ∀ j, f j ∈ 𝒜 (m j)) (hm : ∀ j, 0 < m j)
    (hf : ⨆ j, Proj.basicOpen 𝒜 (f j) = ⊤) : (Proj 𝒜).AffineOpenCover where
  I₀ := I
  X j := .of (Away 𝒜 (f j))
  f j := Proj.awayι 𝒜 (f j) (f_deg j) (hm j)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp (hf.ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι 𝒜 _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp (hf.ge (Set.mem_univ x))).choose_spec

private theorem awayι_congr (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m m' : ℕ} (h : m = m')
    (hf : f ∈ 𝒜 m) (hf' : f ∈ 𝒜 m') (hm : 0 < m) (hm' : 0 < m') :
    Proj.awayι 𝒜 f hf hm = Proj.awayι 𝒜 f hf' hm' := by
  subst h; rfl

/-- Opens of `Proj 𝒜` agreeing on each member of a cover by standard opens are equal. -/
private theorem opens_ext_of_iSup {I : Type*} (f : I → A) (hf : ⨆ j, Proj.basicOpen 𝒜 (f j) = ⊤)
    {U V : (Proj 𝒜).Opens} (h : ∀ j, U ⊓ Proj.basicOpen 𝒜 (f j) = V ⊓ Proj.basicOpen 𝒜 (f j)) :
    U = V := by
  rw [← inf_top_eq U, ← inf_top_eq V, ← hf, inf_iSup_eq, inf_iSup_eq]
  exact iSup_congr h

/-- `A₍f₎ → A₍f · fᵏ₎` is an isomorphism. -/
private theorem awayMap_pow_bijective (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℕ) {x : A} (hx : x = f * f ^ k) :
    Function.Bijective (awayMap 𝒜 (SetLike.pow_mem_graded k hf) hx) := by
  let := (awayMap 𝒜 (SetLike.pow_mem_graded k hf) hx).toAlgebra
  have := Away.isLocalization_mul hf (SetLike.pow_mem_graded k hf) hx hd.ne'
  have hu : IsUnit (Away.isLocalizationElem hf (SetLike.pow_mem_graded k hf)) := by
    convert isUnit_one
    apply val_injective
    rw [Away.val_mk, val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp [← pow_mul, mul_comm]⟩
  let eq := IsLocalization.atUnit (Away 𝒜 f) (Away 𝒜 x) _ hu
  convert eq.bijective
  funext z
  exact (eq.commutes z).symm

variable (φ : A →+* B) {e : ℕ} (hφ : ∀ ⦃n : ℕ⦄ ⦃a : A⦄, a ∈ 𝒜 n → φ a ∈ ℬ (n * e))
  (he : 0 < e) {I : Type*} (t : I → A) {m : I → ℕ} (ht : ∀ j, t j ∈ 𝒜 (m j))
  (hm : ∀ j, 0 < m j) (hcov : ⨆ j, Proj.basicOpen ℬ (φ (t j)) = ⊤)

/-- The chart `D₊(φ (t j)) ⟶ D₊(t j) ⊆ Proj 𝒜`. -/
private noncomputable def glueChart (j : I) : Spec (.of (Away ℬ (φ (t j)))) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (awayScaled hφ (rfl : φ (t j) = _))) ≫
    Proj.awayι 𝒜 (t j) (ht j) (hm j)

private theorem SpecMap_awayMap_glueChart (j k : I) {x : A} {y : B} (hx : x = t j * t k)
    (hy : y = φ (t j) * φ (t k)) (hxy : φ x = y) :
    Spec.map (CommRingCat.ofHom (awayMap ℬ (hφ (ht k)) hy)) ≫ glueChart φ hφ t ht hm j =
      Spec.map (CommRingCat.ofHom (awayScaled hφ hxy)) ≫
        Proj.awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded (ht j) (ht k))
          ((hm j).trans_le (Nat.le_add_right _ _)) := by
  rw [glueChart, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp_awayScaled hφ rfl rfl hxy (ht j) (ht k) (hφ (ht k)) hx hy,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι 𝒜 (ht j) (hm j) (ht k) hx]

/-- The cover of `Proj ℬ` by the `D₊(φ (t j))`. -/
private noncomputable abbrev glueCover : (Proj ℬ).OpenCover :=
  (affineOpenCoverOfISupEqTop ℬ (fun j => φ (t j)) (fun j => hφ (ht j))
      (fun j => Nat.mul_pos (hm j) he) hcov).openCover

private theorem glueChart_compat' (j k : I) :
    Limits.pullback.fst (Proj.awayι ℬ (φ (t j)) (hφ (ht j)) (Nat.mul_pos (hm j) he))
        (Proj.awayι ℬ (φ (t k)) (hφ (ht k)) (Nat.mul_pos (hm k) he)) ≫
        glueChart φ hφ t ht hm j =
      Limits.pullback.snd (Proj.awayι ℬ (φ (t j)) (hφ (ht j)) (Nat.mul_pos (hm j) he))
        (Proj.awayι ℬ (φ (t k)) (hφ (ht k)) (Nat.mul_pos (hm k) he)) ≫
        glueChart φ hφ t ht hm k := by
  rw [← cancel_epi (Proj.pullbackAwayιIso ℬ (hφ (ht j)) (Nat.mul_pos (hm j) he) (hφ (ht k))
    (Nat.mul_pos (hm k) he) (rfl : φ (t j) * φ (t k) = _)).inv]
  rw [Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc]
  rw [SpecMap_awayMap_glueChart φ hφ t ht hm j k rfl rfl (map_mul φ _ _),
    SpecMap_awayMap_glueChart φ hφ t ht hm k j (mul_comm _ _) (mul_comm _ _) (map_mul φ _ _)]
  congr 1

private theorem glueChart_compat (j k : I) :
    Limits.pullback.fst ((glueCover φ hφ he t ht hm hcov).f j)
        ((glueCover φ hφ he t ht hm hcov).f k) ≫ glueChart φ hφ t ht hm j =
      Limits.pullback.snd ((glueCover φ hφ he t ht hm hcov).f j)
        ((glueCover φ hφ he t ht hm hcov).f k) ≫ glueChart φ hφ t ht hm k :=
  glueChart_compat' φ hφ he t ht hm j k

/-- The morphism `Proj ℬ ⟶ Proj 𝒜` glued from the charts `glueChart`. -/
private noncomputable def glued : Proj ℬ ⟶ Proj 𝒜 :=
  (glueCover φ hφ he t ht hm hcov).glueMorphisms (glueChart φ hφ t ht hm)
    (glueChart_compat φ hφ he t ht hm hcov)

private theorem awayι_comp_glued (j : I) :
    Proj.awayι ℬ (φ (t j)) (hφ (ht j)) (Nat.mul_pos (hm j) he) ≫ glued φ hφ he t ht hm hcov =
      glueChart φ hφ t ht hm j :=
  (glueCover φ hφ he t ht hm hcov).ι_glueMorphisms (glueChart φ hφ t ht hm)
    (glueChart_compat φ hφ he t ht hm hcov) j

private theorem glued_preimage_basicOpen (j : I) :
    glued φ hφ he t ht hm hcov ⁻¹ᵁ Proj.basicOpen 𝒜 (t j) = Proj.basicOpen ℬ (φ (t j)) := by
  refine opens_ext_of_iSup (fun k => φ (t k)) hcov fun k => ?_
  rw [inf_comm, inf_comm _ (Proj.basicOpen ℬ (φ (t k))),
    ← Proj.opensRange_awayι ℬ _ (hφ (ht k)) (Nat.mul_pos (hm k) he),
    ← Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_preimage_eq_opensRange_inf]
  congr 1
  rw [← Scheme.Hom.comp_preimage, awayι_comp_glued, glueChart, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 (ht k) (hm k) (ht j) (hm j),
    Proj.awayι_preimage_basicOpen ℬ (hφ (ht k)) (Nat.mul_pos (hm k) he) (hφ (ht j))
      (Nat.mul_pos (hm j) he), SpecMap_preimage_basicOpen]
  have h1 : φ (t j ^ m k) ∈ ℬ (m j • (m k * e)) := by
    have := hφ (SetLike.pow_mem_graded (m k) (ht j))
    rwa [show (m k • m j) * e = m j • (m k * e) by simp only [smul_eq_mul]; ring] at this
  have h2 : φ (t j ^ m k) ^ e ∈ ℬ ((m j * e) • (m k * e)) := by
    have := SetLike.pow_mem_graded e h1
    rwa [show e • m j • (m k * e) = (m j * e) • (m k * e) by simp only [smul_eq_mul]; ring]
      at this
  simp only [CommRingCat.hom_ofHom, Away.isLocalizationElem]
  rw [awayScaled_mk hφ rfl (ht k) (hφ (ht k)) _ _ _ h1, ← PrimeSpectrum.basicOpen_pow _ e he,
    away_mk_pow _ _ _ _ e h2]
  congr 1
  exact away_mk_congr _ _ rfl (by rw [map_pow, ← pow_mul]) _ _

private theorem isClosedImmersion_glued (hcov' : ⨆ j, Proj.basicOpen 𝒜 (t j) = ⊤)
    (hsurj : ∀ j, Function.Surjective (awayScaled hφ (rfl : φ (t j) = _))) :
    IsClosedImmersion (glued φ hφ he t ht hm hcov) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (affineOpenCoverOfISupEqTop 𝒜 t ht hm hcov').openCover fun j => ?_
  exact pullback_snd_of_isPullback
    (IsOpenImmersion.isPullback (Spec.map (CommRingCat.ofHom (awayScaled hφ rfl)))
      (Proj.awayι ℬ (φ (t j)) (hφ (ht j)) (Nat.mul_pos (hm j) he))
      (Proj.awayι 𝒜 (t j) (ht j) (hm j)) (glued φ hφ he t ht hm hcov)
      (awayι_comp_glued φ hφ he t ht hm hcov j) (by
        rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
        exact glued_preimage_basicOpen φ hφ he t ht hm hcov j)).flip
    (IsClosedImmersion.spec_of_surjective _ (hsurj j))

end Glue

section Veronese

variable (R : Type u) [CommRing R] (ι : Type u) (e : ℕ)

/-- `y_J ↦ x^J`, as a map of polynomial rings: `Faltings.veroneseAlgHom` for the tautological
indexing of the monomials of degree `e`. -/
private noncomputable abbrev veroneseAlgHomRefl :
    MvPolynomial {I : ι →₀ ℕ // I.degree = e} R →ₐ[R] MvPolynomial ι R :=
  veroneseAlgHom (Equiv.refl {I : ι →₀ ℕ // I.degree = e})

/-- `y_J ↦ x^J` multiplies degrees by `e`. -/
private theorem veroneseAlgHomRefl_mem ⦃n : ℕ⦄
    ⦃p : MvPolynomial {I : ι →₀ ℕ // I.degree = e} R⦄
    (hp : p ∈ homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R n) :
    (veroneseAlgHomRefl R ι e).toRingHom p ∈ homogeneousSubmodule ι R (n * e) :=
  veroneseAlgHom_mem (Equiv.refl {I : ι →₀ ℕ // I.degree = e}) hp

/-- The coordinates `x_i` generate the irrelevant ideal of `R[x]`. -/
private theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal ≤
      Ideal.span (Set.range (X (R := R))) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hp' : p.IsHomogeneous n := (mem_homogeneousSubmodule _ _).1 hp
  change p ∈ Ideal.span (Set.range X)
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra h
  push Not at h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  have := hp' (mem_support_iff.1 hm)
  rw [hm0, map_zero] at this
  omega

private theorem veroneseAlgHomRefl_X (J : {I : ι →₀ ℕ // I.degree = e}) :
    veroneseAlgHomRefl R ι e (X J) = monomial J.1 1 :=
  veroneseAlgHom_X (Equiv.refl {I : ι →₀ ℕ // I.degree = e}) J

private theorem veroneseAlgHom_X_single (i : ι) :
    veroneseAlgHomRefl R ι e (X (singleIdx (e := e) i)) = X i ^ e := by
  simp [veroneseAlgHomRefl_X, X_pow_eq_monomial]

private theorem iSup_basicOpen_veroneseAlgHom :
    ⨆ J, Proj.basicOpen (homogeneousSubmodule ι R) ((veroneseAlgHomRefl R ι e).toRingHom (X J)) =
      ⊤ := by
  refine top_le_iff.1 ?_
  rw [← Proj.iSup_basicOpen_eq_top (homogeneousSubmodule ι R) X (irrelevant_le_span_X R ι)]
  refine iSup_le fun i => le_iSup_of_le (singleIdx (e := e) i) fun x hx => ?_
  rw [Proj.mem_basicOpen] at hx ⊢
  change veroneseAlgHomRefl R ι e (X _) ∉ _
  rw [veroneseAlgHom_X_single]
  exact fun h => hx (x.isPrime.mem_of_pow_mem _ h)

private theorem awayScaled_veronese_surjective (J : {I : ι →₀ ℕ // I.degree = e}) :
    Function.Surjective (awayScaled (veroneseAlgHomRefl_mem R ι e)
      (rfl : (veroneseAlgHomRefl R ι e).toRingHom (X J) = _)) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective _ (veroneseAlgHomRefl_mem R ι e (X_mem R J)) z
  obtain ⟨p, hp, rfl⟩ := exists_mem_eq (Equiv.refl {I : ι →₀ ℕ // I.degree = e}) n (b := b)
    (by simpa using hb)
  exact ⟨Away.mk _ (X_mem R J) n p (by simpa using hp), awayScaled_mk _ rfl _ _ _ _ _ _⟩

variable {e} in
/-- The Veronese morphism `ℙ(ι)_R ⟶ ℙ({I // |I| = e})_R`. -/
private noncomputable def veroneseMorphism (he : 0 < e) :
    Proj (homogeneousSubmodule ι R) ⟶
      Proj (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R) :=
  glued (veroneseAlgHomRefl R ι e).toRingHom (veroneseAlgHomRefl_mem R ι e) he X (X_mem R)
    (fun _ => one_pos) (iSup_basicOpen_veroneseAlgHom R ι e)

variable {e} in
private theorem awayι_comp_veroneseMorphism (he : 0 < e) (J : {I : ι →₀ ℕ // I.degree = e}) :
    Proj.awayι (homogeneousSubmodule ι R) ((veroneseAlgHomRefl R ι e).toRingHom (X J))
        (veroneseAlgHomRefl_mem R ι e (X_mem R J)) (Nat.mul_pos one_pos he) ≫
        veroneseMorphism R ι he =
      Spec.map (CommRingCat.ofHom (awayScaled (veroneseAlgHomRefl_mem R ι e)
          (rfl : (veroneseAlgHomRefl R ι e).toRingHom (X J) = _))) ≫
        Proj.awayι (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R) (X J) (X_mem R J)
          one_pos :=
  awayι_comp_glued _ _ he X (X_mem R) (fun _ => one_pos) _ J

variable {e} in
private theorem veroneseMorphism_comp_toSpec (he : 0 < e) :
    veroneseMorphism R ι he ≫
        Proj.toSpecZero (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap R (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R 0))) =
      Proj.toSpecZero (homogeneousSubmodule ι R) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule ι R 0))) := by
  refine (glueCover _ (veroneseAlgHomRefl_mem R ι e) he X (X_mem R) (fun _ => one_pos)
    (iSup_basicOpen_veroneseAlgHom R ι e)).hom_ext _ _
    fun (J : {I : ι →₀ ℕ // I.degree = e}) => ?_
  change Proj.awayι (homogeneousSubmodule ι R) ((veroneseAlgHomRefl R ι e).toRingHom (X J))
      (veroneseAlgHomRefl_mem R ι e (X_mem R J)) (Nat.mul_pos one_pos he) ≫ _ =
    Proj.awayι (homogeneousSubmodule ι R) ((veroneseAlgHomRefl R ι e).toRingHom (X J))
      (veroneseAlgHomRefl_mem R ι e (X_mem R J)) (Nat.mul_pos one_pos he) ≫ _
  rw [reassoc_of% awayι_comp_veroneseMorphism, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [fromZeroRingHom_eq_away_mk _ (X_mem R J),
    fromZeroRingHom_eq_away_mk _ (veroneseAlgHomRefl_mem R ι e (X_mem R J)),
    awayScaled_mk _ rfl (X_mem R J) _ 0 _ _ (by simp)]
  refine away_mk_congr _ _ rfl ?_ _ _
  simp [veroneseAlgHomRefl, veroneseAlgHom, MvPolynomial.algebraMap_eq]

variable {e} in
private theorem veroneseAlgHom_X_single_eq_mul (he : 0 < e) (i : ι) :
    (veroneseAlgHomRefl R ι e).toRingHom (X (singleIdx (e := e) i)) = X i * X i ^ (e - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel he]; exact veroneseAlgHom_X_single R ι e i

variable {e} in
/-- The Veronese morphism is a closed immersion: over `D₊(y_J)` it is `Spec` of the surjection
`T₍y_J₎ → S₍ₓᴶ₎`. -/
private theorem isClosedImmersion_veroneseMorphism (he : 0 < e) :
    IsClosedImmersion (veroneseMorphism R ι he) :=
  isClosedImmersion_glued _ _ he X (X_mem R) (fun _ => one_pos) _
    (Proj.iSup_basicOpen_eq_top _ X (irrelevant_le_span_X R _))
    (awayScaled_veronese_surjective R ι e)

variable {e} in
/-- On `D₊(x_i) = D₊(x_i ^ e)` the Veronese morphism lands in `D₊(y_{e • eᵢ})` and pulls
`y_J / y_{e • eᵢ}` back to `x^J / x_i ^ e`. -/
private theorem exists_chart_veroneseMorphism (he : 0 < e) (i : ι) :
    ∃ g : Spec (.of (Away (homogeneousSubmodule ι R) (X i))) ⟶
        Spec (.of (Away (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R)
          (X (R := R) (singleIdx (e := e) i)))),
      g ≫ Proj.awayι (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R)
          (X (R := R) (singleIdx (e := e) i)) (X_mem R _) one_pos =
        Proj.awayι (homogeneousSubmodule ι R) (X i) (X_mem R i) one_pos ≫
          veroneseMorphism R ι he ∧
      ∀ J : {I : ι →₀ ℕ // I.degree = e},
        g.appTop ((Scheme.ΓSpecIso _).inv
            (Away.mk _ (X_mem R _) 1 (X J) (by simpa using X_mem R J))) =
          (Scheme.ΓSpecIso _).inv (Away.mk _ (X_mem R i) e (monomial J.1 1)
            ((mem_homogeneousSubmodule _ _).2
              (isHomogeneous_monomial _ (by rw [smul_eq_mul, mul_one]; exact J.2)))) := by
  have hx := veroneseAlgHom_X_single_eq_mul R ι he i
  let α := awayMap (homogeneousSubmodule ι R) (SetLike.pow_mem_graded (e - 1) (X_mem R i)) hx
  let αe := RingEquiv.ofBijective α (awayMap_pow_bijective _ (X_mem R i) one_pos (e - 1) hx)
  let ψ := awayScaled (veroneseAlgHomRefl_mem R ι e)
    (rfl : (veroneseAlgHomRefl R ι e).toRingHom (X (singleIdx (e := e) i)) = _)
  refine ⟨Spec.map (CommRingCat.ofHom ((αe.symm : _ →+* _).comp ψ)), ?_, fun J => ?_⟩
  · have h1 : Spec.map (CommRingCat.ofHom α) ≫
          Proj.awayι (homogeneousSubmodule ι R) (X i) (X_mem R i) one_pos =
        Proj.awayι _ ((veroneseAlgHomRefl R ι e).toRingHom (X (singleIdx (e := e) i)))
          (veroneseAlgHomRefl_mem R ι e (X_mem R _)) (Nat.mul_pos one_pos he) :=
      (Proj.SpecMap_awayMap_awayι _ (X_mem R i) one_pos _ hx).trans
        (awayι_congr _ _ (by simp; omega) _ _ _ _)
    have h2 : Proj.awayι (homogeneousSubmodule ι R) (X i) (X_mem R i) one_pos =
        Spec.map (CommRingCat.ofHom (αe.symm : _ →+* _)) ≫ Spec.map (CommRingCat.ofHom α) ≫
          Proj.awayι _ (X i) (X_mem R i) one_pos := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (αe.symm : _ →+* _).comp α = RingHom.id _ :=
        RingHom.ext αe.symm_apply_apply
      rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [h2, h1, Category.assoc, awayι_comp_veroneseMorphism, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    change αe.symm (ψ _) = _
    rw [RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply,
      awayScaled_mk _ rfl (X_mem R _) (veroneseAlgHomRefl_mem R ι e (X_mem R _)) 1 _ _
      (by simpa using veroneseAlgHomRefl_mem R ι e (X_mem R J)), awayMap_mk]
    apply val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [RingHom.coe_coe, AlgHom.toRingHom_eq_coe, veroneseAlgHomRefl_X, pow_one]
    rw [← X_pow_eq_monomial]
    generalize (monomial J.1 (1 : R)) = q
    obtain ⟨k, hk⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [show e - 1 = k by omega, hk]
    ring

end Veronese

/-- For `e ≥ 1`, the **Veronese morphism** `ℙ(ι)_R ⟶ ℙ({I : ι →₀ ℕ // |I| = e})_R` over
`Spec R`, given on the chart `D₊(x_i)` by `y_J / y_{e • eᵢ} ↦ x^J / x_i ^ e`, exists and is a
closed immersion. -/
@[faltings "lem_ht_veronese_closed_immersion"]
theorem exists_isClosedImmersion_veronese (R : Type u) [CommRing R] (ι : Type u) (e : ℕ)
    (he : 1 ≤ e) :
    ∃ v : Proj (homogeneousSubmodule ι R) ⟶
        Proj (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R),
      IsClosedImmersion v ∧
      v ≫ Proj.toSpecZero (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap R (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R 0))) =
        Proj.toSpecZero (homogeneousSubmodule ι R) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule ι R 0))) ∧
      ∀ i : ι, ∃ g : Spec (.of (HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X i))) ⟶
          Spec (.of (HomogeneousLocalization.Away
            (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R)
            (X (R := R) (⟨Finsupp.single i e, Finsupp.degree_single i e⟩ :
              {I : ι →₀ ℕ // I.degree = e})))),
        g ≫ Proj.awayι (homogeneousSubmodule {I : ι →₀ ℕ // I.degree = e} R)
            (X (R := R) (⟨Finsupp.single i e, Finsupp.degree_single i e⟩ :
              {I : ι →₀ ℕ // I.degree = e}))
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R _)) one_pos =
          Proj.awayι (homogeneousSubmodule ι R) (X i)
            ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R i)) one_pos ≫ v ∧
        ∀ J : {I : ι →₀ ℕ // I.degree = e},
          g.appTop ((Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R _)) 1 (X J)
                ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R J)))) =
            (Scheme.ΓSpecIso _).inv
              (HomogeneousLocalization.Away.mk _
                ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R i)) e (monomial J.1 1)
                ((mem_homogeneousSubmodule _ _).2
                  (isHomogeneous_monomial _ (by
                    rw [smul_eq_mul, mul_one]; exact J.2)))) :=
  ⟨veroneseMorphism R ι he, isClosedImmersion_veroneseMorphism R ι he,
    veroneseMorphism_comp_toSpec R ι he, exists_chart_veroneseMorphism R ι he⟩

end Faltings
