module

public import Mathlib
public import Mordell.Attr

/-!
# Hensel's bound for the different

Let `L` be a number field and `𝔓` a prime of `𝓞 L` lying over the rational prime `p`, with
ramification index `e = e(𝔓 | p)`. Hensel's bound on the exponent of `𝔓` in the absolute
different `𝔇_L = differentIdeal ℤ (𝓞 L)` is
`ord_𝔓 (𝔇_L) ≤ ord_𝔓 (e) + e - 1 = e · v_p(e) + e - 1`.

## Main results

* `Faltings.count_normalizedFactors_differentIdeal_le`: Hensel's bound
  `ord_𝔓 (𝔇_L) ≤ e · v_p(e) + e - 1`.

## Implementation notes

The exponent `ord_𝔓 (𝔇_L)` is the multiplicity of `𝔓` in the factorisation of `𝔇_L`, written
`Multiset.count 𝔓 (normalizedFactors (differentIdeal ℤ (𝓞 L)))`, the same form in which Mathlib
expresses ramification indices of Dedekind domains. Since `e ≥ 1`, the natural subtraction
`e - 1` is the integer one.

The proof follows Conrad. Put `k = v_p(e) + 1` and `N = e k`, and write `p 𝓞 = 𝔓 ^ e J` with
`J` prime to `𝔓`, so that `q 𝓞 = 𝔓 ^ N J ^ k` for `q = p ^ k`. By the Chinese remainder theorem
`𝓞 / q = 𝓞 / 𝔓 ^ N × 𝓞 / J ^ k` over `ZMod q`. The local factor `𝓞 / 𝔓 ^ N` is free over
`ZMod q`, being free over an unramified extension `W` of `ZMod q` (a Hensel lift of the residue
field) with basis `1, π, …, π ^ (e - 1)`; its trace is `e` times the trace of `W`, which does not
vanish modulo `p ^ k` because `p ^ k ∤ e`. Lifting an element of nonzero trace to `x ∈ J ^ k`
gives `Tr(x) ∉ q ℤ`, hence `𝔓 ^ N ∤ 𝔇_L` by `not_dvd_differentIdeal_of_intTrace_not_mem`.

## References

* [B. Conrad, *The different ideal*, (4.12)][conrad-different]
* [J.-P. Serre, *Local Fields*, Ch. III, §6][serre-local-fields]
-/

@[expose] public section

open NumberField UniqueFactorizationMonoid Polynomial

namespace Faltings

/-- The trace is compatible with a ring map carrying a basis to a basis. -/
private lemma trace_map_of_basis {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R' S'] {ι : Type*} [Finite ι]
    (f : R →+* R') (ψ : S →+* S') (hψ : ψ.comp (algebraMap R S) = (algebraMap R' S').comp f)
    (b : Module.Basis ι R S) (b' : Module.Basis ι R' S') (hb : ∀ i, b' i = ψ (b i)) (x : S) :
    Algebra.trace R' S' (ψ x) = f (Algebra.trace R S x) := by
  classical
  have := Fintype.ofFinite ι
  have hrepr : ∀ s i, b'.repr (ψ s) i = f (b.repr s i) := by
    intro s i
    have : ψ s = ∑ j, f (b.repr s j) • b' j := by
      conv_lhs => rw [← b.sum_repr s]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hb, ← RingHom.comp_apply, hψ,
        RingHom.comp_apply]
    rw [this, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b', Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul, hrepr]

/-- Units of `R` detected through a map to a field with nilpotent kernel. -/
private lemma isUnit_of_res_ne_zero {R F : Type*} [CommRing R] [Field F] (res : R →+* F)
    (hres : Function.Surjective res) (hnil : ∀ r, res r = 0 → IsNilpotent r) {r : R}
    (hr : res r ≠ 0) : IsUnit r := by
  obtain ⟨y, hy⟩ := hres (res r)⁻¹
  have h1 : res (1 - r * y) = 0 := by
    rw [map_sub, map_one, map_mul, hy, mul_inv_cancel₀ hr, sub_self]
  have := (hnil _ h1).isUnit_one_sub
  rw [sub_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left this

/-- The local computation behind Hensel's bound: a finite `ZMod (p ^ k)`-algebra `R` that looks
like `𝓞 / 𝔓 ^ (e k)` (residue field `F`, uniformizer `π` with `π ^ e ∈ p R`, `π ^ (e k) = 0`,
and the right cardinality) is free over `ZMod (p ^ k)` with a trace that does not vanish, as
long as `k = v_p(e) + 1`. -/
private lemma free_and_exists_trace_ne_zero {p : ℕ} [hp : Fact p.Prime] {k e : ℕ}
    (hk : k = padicValNat p e + 1) (he : e ≠ 0)
    {R : Type*} [CommRing R] [Finite R] [Algebra (ZMod (p ^ k)) R]
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]
    (res : R →+* F) (hres : Function.Surjective res)
    (π : R) (hm : ∀ r, res r = 0 ↔ ∃ s, r = π * s)
    (hπe : ∃ v, π ^ e = (p : R) * v) (hπN : π ^ (e * k) = 0)
    (hcard : Nat.card R = Nat.card F ^ (e * k)) :
    Module.Free (ZMod (p ^ k)) R ∧ Module.Finite (ZMod (p ^ k)) R ∧
      ∃ r : R, Algebra.trace (ZMod (p ^ k)) R r ≠ 0 := by
  set A := ZMod (p ^ k)
  have hk0 : k ≠ 0 := by omega
  have hdvd : p ∣ p ^ k := dvd_pow_self p hk0
  let c : A →+* ZMod p := ZMod.castHom hdvd (ZMod p)
  have hc : Function.Surjective c := ZMod.castHom_surjective hdvd
  have hcomp : res.comp (algebraMap A R) = (algebraMap (ZMod p) F).comp c := RingHom.ext_zmod _ _
  have hnil : ∀ r, res r = 0 → IsNilpotent r := by
    intro r hr
    obtain ⟨s, rfl⟩ := (hm r).1 hr
    exact ⟨e * k, by rw [mul_pow, hπN, zero_mul]⟩
  have hpk : (p : R) ^ k = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (algebraMap A R), ZMod.natCast_self, map_zero]
  -- a power basis of the residue field and a monic lift of the minimal polynomial
  have : FiniteDimensional (ZMod p) F := Module.Finite.of_finite
  let pbF := Field.powerBasisOfFiniteOfSeparable (ZMod p) F
  set g := minpoly (ZMod p) pbF.gen with hg_def
  have hg_monic : g.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hg_sep : g.Separable := Algebra.IsSeparable.isSeparable (ZMod p) pbF.gen
  obtain ⟨G, hGmap, hGdeg, hGmonic⟩ := lifts_and_degree_eq_and_monic
    ((mem_lifts g).2 (map_surjective c hc g)) hg_monic
  have hGnat : G.natDegree = g.natDegree := natDegree_eq_of_degree_eq hGdeg
  have key : ∀ (y : R) (P : A[X]), res (aeval y P) = aeval (res y) (P.map c) := by
    intro y P
    rw [aeval_def, aeval_def, hom_eval₂, hcomp, eval₂_map]
  -- Hensel lifting of the generator
  obtain ⟨x0, hx0⟩ := hres pbF.gen
  have h1 : IsNilpotent (aeval x0 G) := hnil _ (by rw [key, hx0, hGmap, minpoly.aeval])
  have h2 : IsUnit (aeval x0 (derivative G)) := by
    refine isUnit_of_res_ne_zero res hres hnil ?_
    rw [key, hx0, ← derivative_map, hGmap]
    exact hg_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨θ, ⟨hθnil, hθ⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero h1 h2
  have hresθ : res θ = pbF.gen := by
    have : res (x0 - θ) = 0 := (hθnil.map res).eq_zero
    rw [map_sub, sub_eq_zero] at this
    rw [← this, hx0]
  -- the unramified subring
  let W := AdjoinRoot G
  let φ : W →ₐ[A] R := AdjoinRoot.liftAlgHom G (Algebra.ofId A R) θ (by
    rw [← hθ, aeval_def]; rfl)
  have hφroot : φ (AdjoinRoot.root G) = θ := AdjoinRoot.liftAlgHom_root _ _ _ _
  let : Algebra W R := φ.toRingHom.toAlgebra
  have hφ : ∀ w, algebraMap W R w = φ w := fun _ => rfl
  have : IsScalarTower A W R := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let pbW := AdjoinRoot.powerBasis' hGmonic
  -- `W` maps onto the residue field
  have hS : ∀ y : F, ∃ w : W, res (φ w) = y := by
    intro y
    let cl : ZMod p → A := Function.surjInv hc
    refine ⟨∑ i, algebraMap A W (cl (pbF.basis.repr y i)) * AdjoinRoot.root G ^ (i : ℕ), ?_⟩
    conv_rhs => rw [← pbF.basis.sum_repr y]
    simp only [map_sum, map_mul, map_pow, hφroot, AlgHom.commutes, PowerBasis.coe_basis]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hresθ, Algebra.smul_def, ← RingHom.comp_apply res, hcomp, RingHom.comp_apply,
      Function.surjInv_eq hc]
  -- the `W`-linear map `(w_i) ↦ ∑ w_i π^i`
  let Φ : (Fin e → W) →ₗ[W] R := Fintype.linearCombination W (fun i : Fin e => π ^ (i : ℕ))
  have hΦsingle : ∀ (i : Fin e) (w : W), Φ (Pi.single i w) = φ w * π ^ (i : ℕ) := by
    intro i w
    rw [Fintype.linearCombination_apply_single, Algebra.smul_def, hφ]
  have step1 : ∀ j ≤ e, ∀ r : R, ∃ (c' : Fin e → W) (s : R), r = Φ c' + π ^ j * s := by
    intro j
    induction j with
    | zero => exact fun _ r => ⟨0, r, by simp⟩
    | succ j ih =>
      intro hj r
      obtain ⟨c', s, hrs⟩ := ih (by omega) r
      obtain ⟨w, hw⟩ := hS (res s)
      obtain ⟨t, ht⟩ := (hm (s - φ w)).1 (by rw [map_sub, hw, sub_self])
      refine ⟨c' + Pi.single ⟨j, by omega⟩ w, t, ?_⟩
      rw [map_add, hΦsingle, hrs, show s = φ w + π * t by rw [← ht]; ring]
      simp only
      ring
  have step2 : ∀ i : ℕ, ∀ r : R, ∃ (c' : Fin e → W) (s : R), r = Φ c' + (p : R) ^ i * s := by
    intro i
    induction i with
    | zero => exact fun r => ⟨0, r, by simp⟩
    | succ i ih =>
      intro r
      obtain ⟨c', s, hrs⟩ := ih r
      obtain ⟨c'', s', hs⟩ := step1 e le_rfl s
      obtain ⟨v, hv⟩ := hπe
      refine ⟨c' + ((p : W) ^ i) • c'', v * s', ?_⟩
      rw [map_add, map_smul, hrs, hs, hv, Algebra.smul_def, hφ, map_pow, map_natCast]
      ring
  have hΦsurj : Function.Surjective Φ := by
    intro r
    obtain ⟨c', s, hrs⟩ := step2 k r
    exact ⟨c', by rw [hrs, hpk, zero_mul, add_zero]⟩
  -- counting: `Φ` is a bijection
  have hdim : pbW.dim = pbF.dim := by
    rw [AdjoinRoot.powerBasis'_dim, hGnat, hg_def, PowerBasis.natDegree_minpoly]
  have hcardW : Nat.card W = (p ^ k) ^ pbF.dim := by
    rw [Nat.card_congr pbW.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      hdim]
  have hcardF : Nat.card F = p ^ pbF.dim := by
    rw [Nat.card_congr pbF.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have : Module.Finite A W := pbW.finite
  have : Finite W := Module.finite_of_finite A
  have hΦbij : Function.Bijective Φ := by
    refine hΦsurj.bijective_of_nat_card_le (le_of_eq ?_)
    rw [Nat.card_fun, Nat.card_fin, hcardW, hcard, hcardF, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  let bR : Module.Basis (Fin e) W R :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective Φ hΦbij).symm
  let bAR := pbW.basis.smulTower bR
  refine ⟨Module.Free.of_basis bAR, Module.Finite.of_basis bAR, ?_⟩
  -- the trace of `φ w` is `e` times the trace of `w`
  have htr : ∀ w : W, Algebra.trace A R (φ w) = e • Algebra.trace A W w := by
    intro w
    rw [← Algebra.trace_trace_of_basis pbW.basis bR, ← hφ, Algebra.trace_algebraMap_of_basis bR,
      Fintype.card_fin, map_nsmul]
  -- reduction modulo `p`: `W / p = (ZMod p)[X] / (g)` is a separable field extension
  have : Fact (Irreducible g) := ⟨minpoly.irreducible (Algebra.IsIntegral.isIntegral _)⟩
  let W' := AdjoinRoot g
  let ψ : W →+* W' := AdjoinRoot.map c G g (by rw [hGmap])
  let pbW' := AdjoinRoot.powerBasis' hg_monic
  have : Module.Finite (ZMod p) W' := pbW'.finite
  have : Finite W' := Module.finite_of_finite (ZMod p)
  have hψmk : ∀ P : A[X], ψ (AdjoinRoot.mk G P) = AdjoinRoot.mk g (P.map c) := by
    intro P
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk G P) = _
    rw [AdjoinRoot.lift_mk, ← eval₂_map, ← AdjoinRoot.aeval_eq, aeval_def]
    rfl
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    obtain ⟨P, rfl⟩ := map_surjective c hc q
    exact ⟨_, hψmk P⟩
  let b' : Module.Basis (Fin G.natDegree) (ZMod p) W' :=
    (pbW'.basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hg_monic))).reindex
      (finCongr hGnat.symm)
  let bW : Module.Basis (Fin G.natDegree) A W :=
    pbW.basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hGmonic))
  have hb : ∀ i, b' i = ψ (bW i) := by
    intro i
    simp only [b', bW, pbW, pbW', Module.Basis.reindex_apply, PowerBasis.coe_basis,
      AdjoinRoot.powerBasis'_gen, map_pow, ψ]
    rw [AdjoinRoot.map_root]
    simp
  have hψc : ψ.comp (algebraMap A W) = (algebraMap (ZMod p) W').comp c := RingHom.ext_zmod _ _
  have htrψ : ∀ w, Algebra.trace (ZMod p) W' (ψ w) = c (Algebra.trace A W w) :=
    trace_map_of_basis c ψ hψc bW b' hb
  obtain ⟨y, hy⟩ : ∃ y : W', Algebra.trace (ZMod p) W' y ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero (ZMod p) W' (LinearMap.ext h)
  obtain ⟨w, rfl⟩ := hψsurj y
  rw [htrψ] at hy
  refine ⟨φ w, ?_⟩
  rw [htr]
  set t := Algebra.trace A W w
  intro h0
  have ht : t = ((t.val : ℕ) : A) := (ZMod.natCast_zmod_val t).symm
  rw [ht, map_natCast, Ne, ZMod.natCast_eq_zero_iff] at hy
  rw [ht, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  have hcop : Nat.Coprime (p ^ k) t.val :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hy)
  have := hcop.dvd_of_dvd_mul_right h0
  rw [hk] at this
  exact pow_succ_padicValNat_not_dvd he this

/-- `ZMod (p ^ k)` is a local ring. -/
private lemma isLocalRing_zmod_prime_pow {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    IsLocalRing (ZMod (p ^ k)) := by
  have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk hp.out.one_lt⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases h : p ∣ a.val
  · right
    refine IsNilpotent.isUnit_one_sub ⟨k, ?_⟩
    rw [← ZMod.natCast_zmod_val a, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd h k
  · left
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm

/-- An ideal squeezed between `P ^ N` and `P ^ a`, but not contained in `P ^ (a + 1)`,
is `P ^ a`. -/
private lemma eq_pow_of_pow_le {D : Type*} [CommRing D] [IsDedekindDomain D] {P I : Ideal D}
    [P.IsMaximal] (hP : P ≠ ⊥) {a N : ℕ} (hN : P ^ N ≤ I) (ha : I ≤ P ^ a)
    (ha' : ¬ I ≤ P ^ (a + 1)) : I = P ^ a := by
  have hprime : Prime P := Ideal.prime_of_isPrime hP inferInstance
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hprime N).1 (Ideal.dvd_iff_le.2 hN)
  rw [associated_iff_eq] at hj
  subst hj
  have hanti := Ideal.pow_right_strictAnti P hP (Ideal.IsMaximal.ne_top inferInstance)
  have h1 : a ≤ j := by
    by_contra h
    exact (hanti (show j < a by omega)).not_ge ha
  have h2 : j ≤ a := by
    by_contra h
    exact ha' (Ideal.pow_le_pow_right (by omega))
  rw [le_antisymm h2 h1]

/-- In a Dedekind domain, `P ^ n ∣ I` iff `n` is at most the multiplicity of `P` in `I`. -/
private lemma pow_dvd_iff_le_count {D : Type*} [CommRing D] [IsDedekindDomain D] {P I : Ideal D}
    [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥) (n : ℕ) :
    P ^ n ∣ I ↔ n ≤ Multiset.count P (normalizedFactors I) := by
  have hPirr := (Ideal.prime_of_isPrime hP inferInstance).irreducible
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP) hI,
    normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]

/-- The quotient `𝓞 L ⧸ (q)` is free over `ZMod q`, with basis the image of a `ℤ`-basis. -/
private lemma exists_basis_quotient_span_natCast (L : Type*) [Field L] [NumberField L] (q : ℕ)
    [NeZero q] (M : Ideal (𝓞 L)) (hM : M = Ideal.span {(q : 𝓞 L)})
    [Algebra (ZMod q) (𝓞 L ⧸ M)] :
    ∃ b' : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) (ZMod q) (𝓞 L ⧸ M),
      ∀ i, b' i = Ideal.Quotient.mk M (Module.Free.chooseBasis ℤ (𝓞 L) i) := by
  set b := Module.Free.chooseBasis ℤ (𝓞 L)
  let Λ : (Module.Free.ChooseBasisIndex ℤ (𝓞 L) → ZMod q) →ₗ[ZMod q] 𝓞 L ⧸ M :=
    Fintype.linearCombination (ZMod q) (fun i => Ideal.Quotient.mk M (b i))
  have hsurj : Function.Surjective Λ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨fun i => (b.repr x i : ZMod q), ?_⟩
    conv_rhs => rw [← b.sum_repr x]
    simp only [Λ, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_intCast, zsmul_eq_mul, map_mul, map_intCast]
  have hM0 : M ≠ ⊥ := by simp [hM, NeZero.ne q]
  have : Finite (𝓞 L ⧸ M) := Ideal.finiteQuotientOfFreeOfNeBot M hM0
  have hcard : Nat.card (𝓞 L ⧸ M) = q ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hM, Ideal.absNorm_span_singleton,
      show (q : 𝓞 L) = algebraMap ℤ (𝓞 L) (q : ℤ) by simp, Algebra.norm_algebraMap,
      Module.finrank_eq_card_chooseBasisIndex]
    simp
  have hbij : Function.Bijective Λ := by
    refine hsurj.bijective_of_nat_card_le (le_of_eq ?_)
    rw [Nat.card_fun, Nat.card_zmod, hcard, Nat.card_eq_fintype_card]
  refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective Λ hbij).symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  change Λ (Pi.single i 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

/-- A prime `P` of a Dedekind domain does not contain the extension of `p` to its
`(e + 1)`-st power, `e` being the ramification index. -/
private lemma not_map_le_pow_ramificationIdx'_succ {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] {p : Ideal R} {P : Ideal S} [P.IsPrime]
    (hp : Ideal.map (algebraMap R S) p ≠ ⊥) (hP : P ≠ ⊥) :
    ¬ Ideal.map (algebraMap R S) p ≤ P ^ (p.ramificationIdx' P + 1) := by
  intro h
  have := Ideal.dvd_iff_le.2 h
  rw [pow_dvd_iff_le_count hP hp,
    ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp inferInstance hP]
    at this
  omega

/-- A direct factor of a finite free module over a local ring is finite and free. -/
private lemma free_and_finite_of_linearEquiv_prod {A S M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup S] [AddCommGroup M] [AddCommGroup N] [Module A S] [Module A M] [Module A N]
    [Module.Free A S] [Module.Finite A S] (f : S ≃ₗ[A] M × N) :
    Module.Free A N ∧ Module.Finite A N := by
  have : Module.Projective A N :=
    Module.Projective.of_split (f.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _)
      (LinearMap.snd _ _ _ ∘ₗ f.toLinearMap) (LinearMap.ext fun t => by simp)
  have : Module.Finite A N :=
    Module.Finite.of_surjective (LinearMap.snd _ _ _ ∘ₗ f.toLinearMap)
      fun t => ⟨f.symm (0, t), by simp⟩
  exact ⟨Module.free_of_flat_of_isLocalRing, this⟩

/-- The local factor: for `𝔓` over `p` with ramification index `e` and `k = v_p(e) + 1`, the
ring `𝓞 L ⧸ 𝔓 ^ (e k)` is free over `ZMod (p ^ k)` with a trace that does not vanish. -/
private lemma free_and_exists_trace_ne_zero_quotient_pow (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [Fact p.Prime] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(p : ℤ)})] {e k : ℕ}
    (he : e = (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔓) (hk : k = padicValNat p e + 1)
    [Algebra (ZMod (p ^ k)) (𝓞 L ⧸ 𝔓 ^ (e * k))] :
    Module.Free (ZMod (p ^ k)) (𝓞 L ⧸ 𝔓 ^ (e * k)) ∧
      Module.Finite (ZMod (p ^ k)) (𝓞 L ⧸ 𝔓 ^ (e * k)) ∧
      ∃ r : 𝓞 L ⧸ 𝔓 ^ (e * k), Algebra.trace (ZMod (p ^ k)) (𝓞 L ⧸ 𝔓 ^ (e * k)) r ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hspan0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have he0 : e ≠ 0 := he ▸ Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver 𝔓 hspan0
  have h𝔓0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan0 𝔓
  have h𝔓max : 𝔓.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔓0
  have hNle : 𝔓 ^ (e * k) ≤ 𝔓 := Ideal.pow_le_self (Nat.mul_ne_zero he0 (by omega))
  let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓0
  have : Finite (𝓞 L ⧸ 𝔓 ^ (e * k)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ h𝔓0)
  have hpO : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hpO0 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan0
  have hp𝔓 : (p : 𝓞 L) ∈ 𝔓 :=
    Ideal.map_le_iff_le_comap.2 (Ideal.over_def 𝔓 (Ideal.span {(p : ℤ)})).le
      (hpO ▸ Ideal.mem_span_singleton_self _)
  have hpF : ∀ a ∈ Ideal.span {((p : ℕ) : ℤ)}, Int.castRingHom (𝓞 L ⧸ 𝔓) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk 𝔓),
      Ideal.Quotient.eq_zero_iff_mem.2 hp𝔓, zero_mul]
  let : Algebra (ZMod p) (𝓞 L ⧸ 𝔓) :=
    ((Ideal.Quotient.lift _ _ hpF).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom).toAlgebra
  -- a uniformizer
  obtain ⟨ϖ, hϖ, hϖ2⟩ := SetLike.exists_of_lt (by
    simpa using Ideal.pow_right_strictAnti 𝔓 h𝔓0 h𝔓max.ne_top (show 1 < 2 by norm_num) :
      𝔓 ^ 2 < 𝔓)
  have hsupϖ : Ideal.span {ϖ} ⊔ 𝔓 ^ (e * k) = 𝔓 := by
    simpa using eq_pow_of_pow_le (a := 1) h𝔓0 le_sup_right
      (by rw [pow_one]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hϖ) hNle)
      (fun h => hϖ2 (h (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))))
  have hsupp : Ideal.span {(p : 𝓞 L)} ⊔ 𝔓 ^ (e * k) = 𝔓 ^ e :=
    eq_pow_of_pow_le h𝔓0 le_sup_right
      (sup_le (hpO ▸ he ▸ Ideal.le_pow_ramificationIdx')
        (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right e (by omega)))) fun h =>
      not_map_le_pow_ramificationIdx'_succ hpO0 h𝔓0 (he ▸ hpO ▸ le_sup_left.trans h)
  let res : 𝓞 L ⧸ 𝔓 ^ (e * k) →+* 𝓞 L ⧸ 𝔓 := Ideal.Quotient.factor hNle
  have hm : ∀ r, res r = 0 ↔ ∃ s, r = Ideal.Quotient.mk (𝔓 ^ (e * k)) ϖ * s := by
    intro r
    constructor
    · intro hr
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, ← hsupϖ] at hr
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      refine ⟨Ideal.Quotient.mk _ s, ?_⟩
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hb, add_zero, map_mul]
      exact mul_comm _ _
    · rintro ⟨s, rfl⟩
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hϖ, zero_mul]
  have hπe : ∃ v, Ideal.Quotient.mk (𝔓 ^ (e * k)) ϖ ^ e = (p : 𝓞 L ⧸ 𝔓 ^ (e * k)) * v := by
    have h := Ideal.pow_mem_pow hϖ e
    rw [← hsupp] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine ⟨Ideal.Quotient.mk _ v, ?_⟩
    rw [← map_pow, ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hb, add_zero, map_mul,
      map_natCast]
    exact mul_comm _ _
  have hπN : Ideal.Quotient.mk (𝔓 ^ (e * k)) ϖ ^ (e * k) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hϖ _
  have hcard : Nat.card (𝓞 L ⧸ 𝔓 ^ (e * k)) = Nat.card (𝓞 L ⧸ 𝔓) ^ (e * k) := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, map_pow]
  exact free_and_exists_trace_ne_zero hk he0 res (Ideal.Quotient.factor_surjective hNle) _
    hm hπe hπN hcard

/-- **Hensel's bound for the different.** For a prime `𝔓` of the ring of integers of a number
field `L` lying over the rational prime `p`, with ramification index `e = e(𝔓 | p)`, the exponent
of `𝔓` in the different `differentIdeal ℤ (𝓞 L)` is at most `e · v_p(e) + e - 1`. -/
@[faltings "lem_mw_different_exponent_bound"]
theorem count_normalizedFactors_differentIdeal_le (L : Type*) [Field L] [NumberField L]
    (p : ℕ) [Fact p.Prime] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver (Ideal.span {(p : ℤ)})] :
    Multiset.count 𝔓 (normalizedFactors (differentIdeal ℤ (𝓞 L))) ≤
      (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔓 *
          padicValNat p ((Ideal.span {(p : ℤ)}).ramificationIdx' 𝔓) +
        (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔓 - 1 := by
  classical
  have hp : p.Prime := Fact.out
  set e := (Ideal.span {(p : ℤ)}).ramificationIdx' 𝔓 with he_def
  set k := padicValNat p e + 1 with hk_def
  have hspan0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have h𝔓0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan0 𝔓
  have h𝔓max : 𝔓.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔓0
  suffices hnd : ¬ 𝔓 ^ (e * k) ∣ differentIdeal ℤ (𝓞 L) by
    rw [pow_dvd_iff_le_count h𝔓0 differentIdeal_ne_bot] at hnd
    have : e * k = e * padicValNat p e + e := by rw [hk_def, mul_add, mul_one]
    omega
  -- `p 𝓞 = 𝔓 ^ e * J` with `J` prime to `𝔓`
  obtain ⟨J, hJ⟩ : 𝔓 ^ e ∣ Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) :=
    Ideal.dvd_iff_le.2 Ideal.le_pow_ramificationIdx'
  have hJ𝔓 : ¬ J ≤ 𝔓 := fun h =>
    not_map_le_pow_ramificationIdx'_succ (Ideal.map_ne_bot_of_ne_bot hspan0) h𝔓0
      (Ideal.le_of_dvd (by rw [hJ, pow_succ]; exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 h)))
  have hcop : IsCoprime 𝔓 J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact h𝔓max.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJ𝔓 (h ▸ le_sup_right))
  have hP : 𝔓 ^ (e * k) * J ^ k =
      Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)} ^ k) := by
    rw [Ideal.map_pow, hJ, mul_pow, ← pow_mul]
  suffices ∃ x ∈ J ^ k, Algebra.intTrace ℤ (𝓞 L) x ∉ Ideal.span {(p : ℤ)} ^ k by
    obtain ⟨x, hxQ, hx⟩ := this
    exact not_dvd_differentIdeal_of_intTrace_not_mem ℤ (𝔓 ^ (e * k)) (J ^ k) hP x hxQ hx
  -- reduction modulo `q = p ^ k`
  set q := p ^ k with hq_def
  have : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  set M := Ideal.span {(q : 𝓞 L)} with hM_def
  have hM : 𝔓 ^ (e * k) * J ^ k = M := by
    rw [hP, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, hM_def]
    simp [hq_def]
  have hqI : ∀ I : Ideal (𝓞 L), M ≤ I →
      ∀ a ∈ Ideal.span {((q : ℕ) : ℤ)}, Int.castRingHom (𝓞 L ⧸ I) a = 0 := by
    intro I hI a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem.2
      (hI (Ideal.mem_span_singleton_self _)), zero_mul]
  let : Algebra (ZMod q) (𝓞 L ⧸ M) :=
    ((Ideal.Quotient.lift _ _ (hqI M le_rfl)).comp
      (Int.quotientSpanNatEquivZMod q).symm.toRingHom).toAlgebra
  let : Algebra (ZMod q) (𝓞 L ⧸ 𝔓 ^ (e * k)) :=
    ((Ideal.Quotient.lift _ _ (hqI _ (hM ▸ Ideal.mul_le_left))).comp
      (Int.quotientSpanNatEquivZMod q).symm.toRingHom).toAlgebra
  let : Algebra (ZMod q) (𝓞 L ⧸ J ^ k) :=
    ((Ideal.Quotient.lift _ _ (hqI _ (hM ▸ Ideal.mul_le_right))).comp
      (Int.quotientSpanNatEquivZMod q).symm.toRingHom).toAlgebra
  obtain ⟨b', hb'⟩ := exists_basis_quotient_span_natCast L q M rfl
  -- the Chinese remainder theorem `𝓞 / q = 𝓞 / 𝔓 ^ (e k) × 𝓞 / J ^ k`
  let e₀ : (𝓞 L ⧸ M) ≃+* (𝓞 L ⧸ 𝔓 ^ (e * k)) × (𝓞 L ⧸ J ^ k) :=
    (Ideal.quotEquivOfEq hM.symm).trans (Ideal.quotientMulEquivQuotientProd _ _ hcop.pow)
  let e₁ : (𝓞 L ⧸ M) ≃ₐ[ZMod q] (𝓞 L ⧸ 𝔓 ^ (e * k)) × (𝓞 L ⧸ J ^ k) :=
    AlgEquiv.ofRingEquiv (f := e₀) fun x => by
      have := RingHom.ext_zmod (e₀.toRingHom.comp (algebraMap (ZMod q) (𝓞 L ⧸ M)))
        (algebraMap (ZMod q) ((𝓞 L ⧸ 𝔓 ^ (e * k)) × (𝓞 L ⧸ J ^ k)))
      exact congr($this x)
  obtain ⟨hfreeR, hfinR, r, hr⟩ := free_and_exists_trace_ne_zero_quotient_pow L p 𝔓 he_def hk_def
  have : Module.Free (ZMod q) (𝓞 L ⧸ M) := Module.Free.of_basis b'
  have : Module.Finite (ZMod q) (𝓞 L ⧸ M) := Module.Finite.of_basis b'
  have : IsLocalRing (ZMod q) := isLocalRing_zmod_prime_pow (by omega)
  obtain ⟨hfreeJ, hfinJ⟩ := free_and_finite_of_linearEquiv_prod e₁.toLinearEquiv
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e₁.symm (r, 0))
  refine ⟨x, ?_, ?_⟩
  · have := congr((e₁ $hx).2)
    simp only [AlgEquiv.apply_symm_apply] at this
    simpa [e₁, e₀, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [Algebra.intTrace_eq_trace, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have h1 := trace_map_of_basis (Int.castRingHom (ZMod q)) (Ideal.Quotient.mk M)
      (RingHom.ext_int _ _) (Module.Free.chooseBasis ℤ (𝓞 L)) b' hb' x
    rw [hx, ← Algebra.trace_eq_of_algEquiv e₁, AlgEquiv.apply_symm_apply,
      Algebra.trace_prod_apply, map_zero, add_zero] at h1
    apply hr
    rw [h1, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd

end Faltings
