module

public import Mathlib
public import Mordell.Attr

/-!
# Biprojective normality in high bidegree

Let `k` be a field and let `S = k[xᵢ, x'ⱼ]` be the polynomial ring in two finite families of
variables, bigraded by `ℕ × ℕ` with `deg xᵢ = (1, 0)` and `deg x'ⱼ = (0, 1)`, so that
`Proj S = ℙ(V) ×ₖ ℙ(W)`. A closed subscheme `X ⊆ ℙ(V) × ℙ(W)` is cut out by a bihomogeneous
ideal `I ⊆ S`; put `A = S ⧸ I`. The opens `D₊(xᵢ x'ⱼ)` cover `ℙ(V) × ℙ(W)`, they intersect in
`D₊(xᵢ x'ⱼ · xₖ x'ₗ)`, and the sections of `𝒪_X(δ₁, δ₂)` over `X ∩ D₊(u)` are the elements of
bidegree `(δ₁, δ₂)` of `A_u`, i.e. the fractions `a / uᵐ` with `a` bihomogeneous of bidegree
`(δ₁ + m, δ₂ + m)`. A global section of `𝒪_X(δ₁, δ₂)` is thus a family of such fractions that
agree on the overlaps.

The theorem: there is `δ₀` such that for `δ₁, δ₂ ≥ δ₀` every such compatible family is the
image of a single bihomogeneous polynomial `F ∈ S` of bidegree `(δ₁, δ₂)`, i.e. the restriction
map `S_{(δ₁, δ₂)} → H⁰(X, 𝒪_X(δ₁, δ₂))` is surjective.

## Main results

* `Faltings.exists_isWeightedHomogeneous_restrict_eq_of_compatible`: biprojective normality in
  high bidegree.

## Implementation notes

The section `H⁰(X, 𝒪_X(δ₁, δ₂))` is written through its Čech description on the affine cover
`{X ∩ D₊(xᵢ x'ⱼ)}`: a family `s i j` in `Localization.Away (xᵢ x'ⱼ)` over `A`, each of bidegree
`(δ₁, δ₂)`, compatible under the canonical maps `IsLocalization.Away.awayToAwayRight` and
`IsLocalization.Away.awayToAwayLeft` into `Localization.Away (xᵢ x'ⱼ · xₖ x'ₗ)`. The restriction of
`F` is its image `F / 1` in every chart. The bigrading is
`MvPolynomial.IsWeightedHomogeneous` for the weight `Sum.elim (fun _ ↦ (1, 0)) (fun _ ↦ (0, 1))`,
and bihomogeneity of `I` is closure under taking weighted homogeneous components. The two factors
are `ℙ(V)` and `ℙ(W)` for arbitrary finite index types `ι`, `κ`; the source's `ℙⁿ × ℙⁿ` is
`ι = κ = Fin (n + 1)`.

The source argues with the sheaf cohomology of coherent sheaves on `ℙⁿ × ℙⁿ`. Here the same
descending induction on `q` (Serre vanishing) runs on the Čech complex of graded `S`-modules for
the cover `{D₊(xᵢ x'ⱼ)}`. Every localization `S_u` at a monomial `u` embeds in the Laurent
polynomial ring `k[ℤ^{ι ⊕ κ}]`, so Čech cochains of a graded subquotient `M / N` of a shifted
free module `S^r` are functions on sets of charts with values there. For a free module the
complex is exact in high bidegree, since on each Laurent monomial it is the cochain complex of a
cone; in general a choice of finitely many homogeneous generators of `M` and the connecting map
reduce `Ȟ^q(M / N)` to `Ȟ^{q+1}` of the kernel. Degree `q = 0` is the theorem.

## References

* [Stacks, Tag 01WD, 01XT, 0BED, 01QB]
* [Bombieri, *The Mordell conjecture revisited*]
-/

@[expose] public section

open MvPolynomial

namespace Faltings

section Laurent

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def castE : ((ι ⊕ κ) →₀ ℕ) →+ (ι ⊕ κ → ℤ) where
  toFun m z := (m z : ℤ)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

private lemma castE_apply (m : (ι ⊕ κ) →₀ ℕ) (z : ι ⊕ κ) : castE m z = (m z : ℤ) := rfl

private lemma castE_injective : Function.Injective (castE (ι := ι) (κ := κ)) := fun a b h => by
  ext z
  simpa [castE] using congrFun h z

private noncomputable def emb : MvPolynomial (ι ⊕ κ) k →+* AddMonoidAlgebra k (ι ⊕ κ → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom k castE

private lemma emb_coeff_castE (f : MvPolynomial (ι ⊕ κ) k) (m) :
    (emb f).coeff (castE m) = f.coeff m := by
  simp [emb]
  rw [Finsupp.mapDomain_apply_of_injective castE_injective]

private lemma emb_coeff_of_notMem (f : MvPolynomial (ι ⊕ κ) k) (e : ι ⊕ κ → ℤ)
    (he : e ∉ Set.range castE) : (emb f).coeff e = 0 := by
  simp [emb]
  exact Finsupp.mapDomain_of_notMem_range _ _ he

private lemma emb_injective : Function.Injective (emb (k := k) (ι := ι) (κ := κ)) := by
  intro f g h
  ext m
  rw [← emb_coeff_castE, ← emb_coeff_castE, h]

/-- The monomial `t^g` of the Laurent polynomial ring. -/
private noncomputable def mon (g : ι ⊕ κ → ℤ) : AddMonoidAlgebra k (ι ⊕ κ → ℤ) :=
  AddMonoidAlgebra.single g 1

private lemma mon_add (g h : ι ⊕ κ → ℤ) : (mon (g + h) : AddMonoidAlgebra k _) = mon g * mon h := by
  simp [mon, AddMonoidAlgebra.single_mul_single]

private lemma mon_zero : (mon 0 : AddMonoidAlgebra k (ι ⊕ κ → ℤ)) = 1 := rfl

private lemma mon_neg_mul_mon (g : ι ⊕ κ → ℤ) : (mon (-g) : AddMonoidAlgebra k _) * mon g = 1 := by
  rw [← mon_add, neg_add_cancel, mon_zero]

private lemma mon_mul_mon_neg (g : ι ⊕ κ → ℤ) : (mon g : AddMonoidAlgebra k _) * mon (-g) = 1 := by
  rw [← mon_add, add_neg_cancel, mon_zero]

private lemma coeff_mon_mul (g : ι ⊕ κ → ℤ) (x : AddMonoidAlgebra k (ι ⊕ κ → ℤ)) (e) :
    (mon g * x).coeff e = x.coeff (-g + e) := by
  simp [mon]

private lemma mon_nsmul (n : ℕ) (g : ι ⊕ κ → ℤ) :
    (mon (n • g) : AddMonoidAlgebra k _) = mon g ^ n := by
  induction n with
  | zero => simp [mon_zero]
  | succ n ih => rw [succ_nsmul, mon_add, ih, pow_succ]

private lemma emb_monomial (m : (ι ⊕ κ) →₀ ℕ) : emb (monomial m (1 : k)) = mon (castE m) := by
  simp [emb, mon, ← single_eq_monomial]

private lemma emb_X (z : ι ⊕ κ) : emb (X z : MvPolynomial (ι ⊕ κ) k) = mon (Pi.single z 1) := by
  rw [X, emb_monomial]
  congr 1
  ext y
  simp [castE_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

private lemma mem_range_emb_iff (y : AddMonoidAlgebra k (ι ⊕ κ → ℤ)) :
    y ∈ Set.range (emb (k := k)) ↔ ∀ e, y.coeff e ≠ 0 → ∀ z, 0 ≤ e z := by
  constructor
  · rintro ⟨f, rfl⟩ e he z
    by_cases h : e ∈ Set.range castE
    · obtain ⟨m, rfl⟩ := h
      simp [castE_apply]
    · exact absurd (emb_coeff_of_notMem f e h) he
  · intro hy
    let toN : (ι ⊕ κ → ℤ) → ((ι ⊕ κ) →₀ ℕ) := fun e => Finsupp.equivFunOnFinite.symm
      (fun z => (e z).toNat)
    have hcast : ∀ e, (∀ z, 0 ≤ e z) → castE (toN e) = e := by
      intro e he; ext z; simp [toN, castE_apply, he z]
    refine ⟨∑ e ∈ y.coeff.support, monomial (toN e) (y.coeff e), ?_⟩
    rw [map_sum]
    have : ∀ e ∈ y.coeff.support, emb (monomial (toN e) (y.coeff e)) =
        AddMonoidAlgebra.single e (y.coeff e) := by
      intro e he
      rw [Finsupp.mem_support_iff] at he
      simp [emb, ← single_eq_monomial, hcast e (hy e he)]
    rw [Finset.sum_congr rfl this]
    ext e
    simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single e]
    · simp
    · exact fun b _ hb => by simp [hb]
    · intro he; simp only [Finsupp.mem_support_iff, ne_eq, not_not] at he; simp [he]

/-- The bigrading weight: `deg xᵢ = (1, 0)`, `deg x'ⱼ = (0, 1)`, with values in `ℤ × ℤ`. -/
private def wt : ι ⊕ κ → ℤ × ℤ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

/-- The bidegree of a Laurent monomial. -/
private def degG : (ι ⊕ κ → ℤ) →+ ℤ × ℤ where
  toFun e := ∑ z, e z • wt z
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]

private lemma degG_apply (e : ι ⊕ κ → ℤ) : degG e = ∑ z, e z • wt z := rfl

private lemma degG_fst (e : ι ⊕ κ → ℤ) : (degG e).1 = ∑ i, e (Sum.inl i) := by
  simp [degG_apply, Prod.fst_sum, Fintype.sum_sum_type, wt]

private lemma degG_snd (e : ι ⊕ κ → ℤ) : (degG e).2 = ∑ j, e (Sum.inr j) := by
  simp [degG_apply, Prod.snd_sum, Fintype.sum_sum_type, wt]

private lemma degG_castE (m : (ι ⊕ κ) →₀ ℕ) : degG (castE m) = Finsupp.weight wt m := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), degG_apply]
  simp [castE_apply]

/-- Laurent polynomials homogeneous of bidegree `d`. -/
private def homL (d : ℤ × ℤ) : AddSubgroup (AddMonoidAlgebra k (ι ⊕ κ → ℤ)) where
  carrier := {x | ∀ e, x.coeff e ≠ 0 → degG e = d}
  zero_mem' := by simp
  add_mem' {x y} hx hy e he := by
    simp only [Set.mem_ofPred_eq, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply] at *
    by_cases h : x.coeff e = 0
    · exact hy e (by simpa [h] using he)
    · exact hx e h
  neg_mem' {x} hx e he := by
    simp only [Set.mem_ofPred_eq] at *
    exact hx e (by simpa using he)

private lemma mul_mem_homL {a b : ℤ × ℤ} {x y : AddMonoidAlgebra k (ι ⊕ κ → ℤ)} (hx : x ∈ homL a)
    (hy : y ∈ homL b) : x * y ∈ homL (a + b) := by
  classical
  intro e he
  rw [AddMonoidAlgebra.coeff_mul] at he
  obtain ⟨e₁, he₁, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  obtain ⟨e₂, he₂, h₂⟩ := Finset.exists_ne_zero_of_sum_ne_zero h₁
  have hsum : e₁ + e₂ = e := by by_contra h; simp [h] at h₂
  rw [← hsum, map_add, hx e₁ (Finsupp.mem_support_iff.mp he₁),
    hy e₂ (Finsupp.mem_support_iff.mp he₂)]

private lemma mon_mem_homL (g : ι ⊕ κ → ℤ) : (mon g : AddMonoidAlgebra k _) ∈ homL (degG g) := by
  intro e he
  simp only [mon, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at he
  by_contra h
  exact he (if_neg (fun h' => h (by rw [h'])))

private lemma emb_mem_homL_iff {d : ℤ × ℤ} {f : MvPolynomial (ι ⊕ κ) k} :
    emb f ∈ homL d ↔ IsWeightedHomogeneous wt f d := by
  constructor
  · intro h m hm
    rw [← degG_castE]
    exact h _ (by rwa [emb_coeff_castE])
  · intro h e he
    by_cases hr : e ∈ Set.range castE
    · obtain ⟨m, rfl⟩ := hr
      rw [degG_castE]
      exact h (by rwa [emb_coeff_castE] at he)
    · exact absurd (emb_coeff_of_notMem f e hr) he

end Laurent

section Cech

variable {V : Type*} [LinearOrder V] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private def sgn (a : V) (σ : Finset V) : ℤ := (-1) ^ (σ.filter (· < a)).card

private def dif (c : Finset V → A) (σ : Finset V) : A := ∑ a ∈ σ, sgn a σ • c (σ.erase a)

private def cone (a₀ : V) (c : Finset V → A) (τ : Finset V) : A :=
  if a₀ ∈ τ then 0 else sgn a₀ (insert a₀ τ) • c (insert a₀ τ)

private lemma sgn_mul_self (a : V) (σ : Finset V) : sgn a σ * sgn a σ = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp

private lemma card_filter_erase {a b : V} {σ : Finset V} (ha : a ∈ σ) :
    ((σ.erase a).filter (· < b)).card + (if a < b then 1 else 0) = (σ.filter (· < b)).card := by
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨ha, h⟩)]
    have : 0 < (σ.filter (· < b)).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩⟩
    omega
  · rw [Finset.erase_eq_of_notMem (s := σ.filter (· < b)) (a := a) (by simp [h])]; simp

private lemma card_filter_insert {a b : V} {σ : Finset V} (ha : a ∉ σ) :
    ((insert a σ).filter (· < b)).card = (σ.filter (· < b)).card + (if a < b then 1 else 0) := by
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.mp h').1)]
  · simp

private lemma sgn_insert_self {a : V} {σ : Finset V} (ha : a ∉ σ) :
    sgn a (insert a σ) = sgn a σ := by
  rw [sgn, sgn, card_filter_insert ha, if_neg (lt_irrefl a), add_zero]

private lemma sgn_erase_swap {a b : V} {σ : Finset V} (ha : a ∈ σ) (hb : b ∈ σ) (hab : a ≠ b) :
    sgn a σ * sgn b (σ.erase a) = - (sgn b σ * sgn a (σ.erase b)) := by
  have h1 := card_filter_erase (b := b) ha
  have h2 := card_filter_erase (b := a) hb
  simp only [sgn]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [if_pos h] at h1
    rw [if_neg (not_lt.mpr h.le)] at h2
    rw [← h1, ← h2]; ring
  · rw [if_neg (not_lt.mpr h.le)] at h1
    rw [if_pos h] at h2
    rw [← h1, ← h2]; ring

private lemma dif_dif (c : Finset V → A) (σ : Finset V) : dif (dif c) σ = 0 := by
  simp only [dif, Finset.smul_sum, smul_smul]
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    simp only
    rw [Finset.erase_right_comm, ← add_smul, sgn_erase_swap hx.1 hx.2.2 (Ne.symm hx.2.1),
      neg_add_cancel, zero_smul]
  · rintro ⟨a, b⟩ hx _ h
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx
    simp only [Sigma.mk.inj_iff] at h
    exact hx.2.1 h.1
  · rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_erase] at hx ⊢
    exact ⟨hx.2.2, Ne.symm hx.2.1, hx.1⟩
  · intros; rfl

private lemma sgn_cone_identity {a a₀ : V} {σ : Finset V} (ha : a ∈ σ) (h₀ : a₀ ∉ σ) :
    sgn a σ * sgn a₀ (insert a₀ (σ.erase a)) + sgn a₀ (insert a₀ σ) * sgn a (insert a₀ σ) = 0 := by
  have hne : a ≠ a₀ := fun h => h₀ (h ▸ ha)
  rw [sgn_insert_self h₀, sgn_insert_self (fun h => h₀ (Finset.mem_of_mem_erase h))]
  have h1 := card_filter_erase (b := a₀) ha
  have h2 := card_filter_insert (b := a) h₀
  simp only [sgn]
  rw [h2]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h] at h1
    rw [if_neg (not_lt.mpr h.le)]
    rw [← h1]; ring
  · rw [if_neg (not_lt.mpr h.le)] at h1
    rw [if_pos h]
    rw [← h1]; ring

private lemma dif_cone (a₀ : V) (c : Finset V → A) (σ : Finset V) :
    dif (cone a₀ c) σ + cone a₀ (dif c) σ = c σ := by
  by_cases h : a₀ ∈ σ
  · simp only [cone, if_pos h, add_zero, dif]
    rw [Finset.sum_eq_single a₀]
    · rw [if_neg (Finset.notMem_erase a₀ σ), Finset.insert_erase h, smul_smul, sgn_mul_self,
        one_smul]
    · intro b _ hb
      rw [if_pos (Finset.mem_erase.mpr ⟨Ne.symm hb, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · simp only [cone, if_neg h, dif]
    rw [Finset.sum_insert h, Finset.erase_insert h, smul_add, smul_smul, sgn_mul_self, one_smul,
      Finset.smul_sum]
    have : ∀ a ∈ σ, sgn a σ • (if a₀ ∈ σ.erase a then 0 else
        sgn a₀ (insert a₀ (σ.erase a)) • c (insert a₀ (σ.erase a))) +
        sgn a₀ (insert a₀ σ) • (sgn a (insert a₀ σ) • c ((insert a₀ σ).erase a)) = 0 := by
      intro a ha
      have hne : a₀ ≠ a := fun h' => h (h' ▸ ha)
      rw [if_neg (fun h' => h (Finset.mem_of_mem_erase h')), Finset.erase_insert_of_ne hne,
        smul_smul, smul_smul, ← add_smul, sgn_cone_identity ha h, zero_smul]
    rw [add_comm (c σ), ← add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero this, zero_add]

private lemma dif_map (f : A →+ B) (c : Finset V → A) (σ : Finset V) :
    dif (fun τ => f (c τ)) σ = f (dif c σ) := by
  simp [dif, map_sum, map_zsmul]

private lemma dif_sub (c c' : Finset V → A) (σ : Finset V) :
    dif (fun τ => c τ - c' τ) σ = dif c σ - dif c' σ := by
  simp [dif, smul_sub, Finset.sum_sub_distrib]

private lemma dif_congr {n : ℕ} {c c' : Finset V → A} (h : ∀ τ : Finset V, τ.card = n → c τ = c' τ)
    {σ : Finset V} (hσ : σ.card = n + 1) : dif c σ = dif c' σ := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [h _ (by rw [Finset.card_erase_of_mem ha, hσ]; rfl)]

private lemma dif_mem {n : ℕ} (S : Finset V → AddSubgroup A) (hS : ∀ τ σ, τ ⊆ σ → S τ ≤ S σ)
    {c : Finset V → A} (hc : ∀ τ : Finset V, τ.card = n → c τ ∈ S τ)
    {σ : Finset V} (hσ : σ.card = n + 1) : dif c σ ∈ S σ := by
  apply AddSubgroup.sum_mem
  intro a ha
  apply AddSubgroup.zsmul_mem
  exact hS _ _ (Finset.erase_subset a σ)
    (hc _ (by rw [Finset.card_erase_of_mem ha, hσ]; rfl))

end Cech

section Loc

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [LinearOrder V] (π : V → ι × κ) {r : ℕ}

/-- The exponent vector of the monomial `∏_{v ∈ σ} x_{(π v).1} x'_{(π v).2}`. -/
private def expo (σ : Finset V) : ι ⊕ κ → ℤ :=
  ∑ v ∈ σ, (Pi.single (Sum.inl (π v).1) 1 + Pi.single (Sum.inr (π v).2) 1)

/-- The monomial `u_σ = ∏_{v ∈ σ} x_{(π v).1} x'_{(π v).2}` of the polynomial ring. -/
private noncomputable def uR (σ : Finset V) : MvPolynomial (ι ⊕ κ) k :=
  ∏ v ∈ σ, X (Sum.inl (π v).1) * X (Sum.inr (π v).2)

omit [Fintype ι] [Fintype κ] in
private lemma expo_nonneg (σ : Finset V) (z : ι ⊕ κ) : 0 ≤ expo π σ z := by
  simp only [expo, Finset.sum_apply]
  apply Finset.sum_nonneg
  intro v _
  simp only [Pi.add_apply]
  have h1 : (0 : ℤ) ≤ (Pi.single (Sum.inl (π v).1) 1 : ι ⊕ κ → ℤ) z := by
    by_cases h : z = Sum.inl (π v).1 <;> simp [Pi.single_apply, h]
  have h2 : (0 : ℤ) ≤ (Pi.single (Sum.inr (π v).2) 1 : ι ⊕ κ → ℤ) z := by
    by_cases h : z = Sum.inr (π v).2 <;> simp [Pi.single_apply, h]
  omega

omit [Fintype ι] [Fintype κ] in
private lemma expo_insert {a : V} {σ : Finset V} (h : a ∉ σ) :
    expo π (insert a σ) =
      (Pi.single (Sum.inl (π a).1) 1 + Pi.single (Sum.inr (π a).2) 1) + expo π σ := by
  rw [expo, Finset.sum_insert h, expo]

omit [Fintype ι] [Fintype κ] in
private lemma expo_empty : expo π (∅ : Finset V) = 0 := by simp [expo]

omit [Fintype ι] [Fintype κ] in
private lemma expo_sdiff {τ σ : Finset V} (h : τ ⊆ σ) :
    expo π σ = expo π (σ \ τ) + expo π τ := by
  rw [expo, expo, expo, Finset.sum_sdiff h]

private lemma emb_uR (σ : Finset V) : emb (uR (k := k) π σ) = mon (expo π σ) := by
  induction σ using Finset.induction_on with
  | empty => simp [uR, expo, mon_zero]
  | insert a σ ha ih =>
    rw [uR, Finset.prod_insert ha, map_mul, ← uR, ih, expo_insert π ha, mon_add, map_mul,
      emb_X, emb_X, ← mon_add]

/-- The localization `M_{u_σ}` of a submodule `M ⊆ R^r`, as a subgroup of `L^r`, where `L` is
the Laurent polynomial ring: the vectors `x` with `u_σ^m x ∈ M` for some `m`. -/
private noncomputable def loc
    (M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k))
    (σ : Finset V) : AddSubgroup (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) where
  carrier := {x | ∃ m : ℕ, ∃ p ∈ M, ∀ j, mon (m • expo π σ) * x j = emb (p j)}
  zero_mem' := ⟨0, 0, M.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨m, p, hp, hx⟩ ⟨m', p', hp', hy⟩
    refine ⟨m + m', uR π σ ^ m' • p + uR π σ ^ m • p', M.add_mem (M.smul_mem _ hp)
      (M.smul_mem _ hp'), fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, emb_uR,
      ← hx j, ← hy j, ← mon_nsmul, add_smul, mon_add]
    ring
  neg_mem' := by
    rintro x ⟨m, p, hp, hx⟩
    exact ⟨m, -p, M.neg_mem hp, fun j => by rw [Pi.neg_apply, mul_neg, hx j, Pi.neg_apply, map_neg]⟩

private lemma loc_mono {M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)}
    {τ σ : Finset V} (h : τ ⊆ σ) : loc π M τ ≤ loc π M σ := by
  rintro x ⟨m, p, hp, hx⟩
  refine ⟨m, uR π (σ \ τ) ^ m • p, M.smul_mem _ hp, fun j => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, emb_uR, ← hx j, expo_sdiff π h,
    smul_add, mon_add, ← mon_nsmul]
  ring

private lemma loc_mono_left {M M' : Submodule (MvPolynomial (ι ⊕ κ) k)
    (Fin r → MvPolynomial (ι ⊕ κ) k)} (h : M ≤ M') (σ : Finset V) :
    loc π M σ ≤ loc π M' σ := by
  rintro x ⟨m, p, hp, hx⟩
  exact ⟨m, p, h hp, hx⟩

private lemma mem_loc_bot {σ : Finset V} {x : Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} :
    x ∈ loc π ⊥ σ ↔ x = 0 := by
  constructor
  · rintro ⟨m, p, hp, hx⟩
    rw [Submodule.mem_bot] at hp
    subst hp
    ext1 j
    have := congrArg (mon (-(m • expo π σ)) * ·) (hx j)
    simpa [← mul_assoc, mon_neg_mul_mon] using this
  · rintro rfl; exact zero_mem _

private lemma mem_loc_top_iff {σ : Finset V} {x : Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} :
    x ∈ loc π ⊤ σ ↔ ∀ j e, (x j).coeff e ≠ 0 → ∀ z, expo π σ z = 0 → 0 ≤ e z := by
  constructor
  · rintro ⟨m, p, -, hx⟩ j e he z hz
    have hmem : mon (m • expo π σ) * x j ∈ Set.range (emb (k := k)) := ⟨p j, (hx j).symm⟩
    rw [mem_range_emb_iff] at hmem
    have := hmem (m • expo π σ + e) (by rwa [coeff_mon_mul, neg_add_cancel_left]) z
    simpa [hz] using this
  · intro h
    let N : ℕ := ∑ j, ∑ e ∈ (x j).coeff.support, ∑ z, (-e z).toNat
    have hN : ∀ j e, (x j).coeff e ≠ 0 → ∀ z, (-e z).toNat ≤ N := by
      intro j e he z
      calc (-e z).toNat ≤ ∑ z, (-e z).toNat :=
            Finset.single_le_sum (f := fun z => (-e z).toNat) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ z)
        _ ≤ ∑ e ∈ (x j).coeff.support, ∑ z, (-e z).toNat :=
            Finset.single_le_sum (f := fun e => ∑ z, (-e z).toNat) (fun _ _ => Nat.zero_le _)
              (Finsupp.mem_support_iff.mpr he)
        _ ≤ N := Finset.single_le_sum
              (f := fun j => ∑ e ∈ (x j).coeff.support, ∑ z, (-e z).toNat)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hr : ∀ j, mon (N • expo π σ) * x j ∈ Set.range (emb (k := k)) := by
      intro j
      rw [mem_range_emb_iff]
      intro e' he' z
      rw [coeff_mon_mul] at he'
      set e := -(N • expo π σ) + e' with he_def
      have he'eq : e' = N • expo π σ + e := by rw [he_def, add_neg_cancel_left]
      rw [he'eq]
      change 0 ≤ (N • expo π σ) z + e z
      rw [Pi.smul_apply, nsmul_eq_mul]
      by_cases hz : expo π σ z = 0
      · rw [hz]; simpa using h j e he' z hz
      · have h1 : 1 ≤ expo π σ z := by have := expo_nonneg π σ z; omega
        have h2 := hN j e he' z
        have h3 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
        have h4 : -e z ≤ ((-e z).toNat : ℤ) := Int.self_le_toNat _
        have h5 : (N : ℤ) ≤ N * expo π σ z := le_mul_of_one_le_right h3 h1
        have h6 : (((-e z).toNat : ℕ) : ℤ) ≤ N := by exact_mod_cast h2
        linarith
    choose p hp using hr
    exact ⟨N, p, Submodule.mem_top, fun j => (hp j).symm⟩

/-- Vectors in `L^r` whose `j`-th coordinate is homogeneous of bidegree `δ - s j`. -/
private def degS (s : Fin r → ℤ × ℤ) (δ : ℤ × ℤ) :
    AddSubgroup (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) where
  carrier := {x | ∀ j, x j ∈ homL (δ - s j)}
  zero_mem' _ := zero_mem _
  add_mem' hx hy j := add_mem (hx j) (hy j)
  neg_mem' hx j := neg_mem (hx j)

end Loc

section Base

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [Fintype V] [LinearOrder V] (π : V → ι × κ) {r : ℕ}

/-- A Laurent monomial of bidegree `≥ (0, 0)` has a nonnegative exponent at some `xᵢ` and at some
`x'ⱼ`, hence at both variables of some chart `u_v`. -/
private lemma exists_nonneg_chart (hπ : Function.Surjective π) [Nonempty V] {e : ι ⊕ κ → ℤ}
    (h1 : 0 ≤ (degG e).1) (h2 : 0 ≤ (degG e).2) :
    ∃ v, 0 ≤ e (Sum.inl (π v).1) ∧ 0 ≤ e (Sum.inr (π v).2) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hi : ∃ i, 0 ≤ e (Sum.inl i) := by
    by_contra h
    push Not at h
    have : ∑ i, e (Sum.inl i) < ∑ _i : ι, (0 : ℤ) :=
      Finset.sum_lt_sum_of_nonempty ⟨(π v₀).1, Finset.mem_univ _⟩ (fun i _ => h i)
    rw [degG_fst] at h1
    simp at this; omega
  have hj : ∃ j, 0 ≤ e (Sum.inr j) := by
    by_contra h
    push Not at h
    have : ∑ j, e (Sum.inr j) < ∑ _j : κ, (0 : ℤ) :=
      Finset.sum_lt_sum_of_nonempty ⟨(π v₀).2, Finset.mem_univ _⟩ (fun j _ => h j)
    rw [degG_snd] at h2
    simp at this; omega
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  obtain ⟨v, hv⟩ := hπ (i, j)
  exact ⟨v, by rw [hv]; exact hi, by rw [hv]; exact hj⟩

/-- Evaluation of the coefficient of `t^e` in the `l`-th coordinate. -/
private noncomputable def evC (l : Fin r) (e : ι ⊕ κ → ℤ) :
    (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) →+ k :=
  (Finsupp.applyAddHom e).comp
    ((AddMonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ l))

private lemma evC_apply (l : Fin r) (e : ι ⊕ κ → ℤ) (x : Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) :
    evC l e x = (x l).coeff e := rfl

private lemma dif_zero' (σ : Finset V) : dif (fun _ : Finset V => (0 : k)) σ = 0 := by
  simp [dif]

/-- **The Čech complex of a free module is exact in nonnegative bidegrees.** For the free module
`R^r` with generators in bidegrees `s l ≤ δ`, every Čech cocycle of bidegree `δ` (in the extended
complex) is a coboundary. On each Laurent monomial the cochains form the cochain complex of a cone
whose apex is a chart `u_v` both of whose variables have nonnegative exponent. -/
private lemma free_exact (hπ : Function.Surjective π) (s : Fin r → ℤ × ℤ) (δ : ℤ × ℤ)
    (hδ : ∀ l, (s l).1 ≤ δ.1 ∧ (s l).2 ≤ δ.2) (q : ℕ)
    (c : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)))
    (hc : ∀ σ : Finset V, σ.card = q + 1 → c σ ∈ loc (k := k) π ⊤ σ ∧ c σ ∈ degS s δ)
    (hdc : ∀ σ : Finset V, σ.card = q + 2 → dif c σ = 0) :
    ∃ b : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)),
      (∀ σ : Finset V, σ.card = q → b σ ∈ loc (k := k) π ⊤ σ ∧ b σ ∈ degS s δ) ∧
      ∀ σ : Finset V, σ.card = q + 1 → dif b σ = c σ := by
  classical
  set c₀ : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) :=
    fun σ => if σ.card = q + 1 then c σ else 0 with hc₀
  have hc₀c : ∀ τ : Finset V, τ.card = q + 1 → c₀ τ = c τ := fun τ hτ => by simp [hc₀, hτ]
  let good : (ι ⊕ κ → ℤ) → V → Prop := fun e v => 0 ≤ e (Sum.inl (π v).1) ∧ 0 ≤ e (Sum.inr (π v).2)
  let γ : Fin r → (ι ⊕ κ → ℤ) → Finset V → k := fun l e τ => (c₀ τ l).coeff e
  let f : Finset V → Fin r → (ι ⊕ κ → ℤ) → k := fun σ l e =>
    if h : ∃ v, good e v then cone h.choose (γ l e) σ else 0
  have hf : ∀ σ l e, f σ l e ≠ 0 →
      ∃ v, good e v ∧ v ∉ σ ∧ (c₀ (insert v σ) l).coeff e ≠ 0 := by
    intro σ l e hne
    simp only [f] at hne
    split_ifs at hne with h
    · refine ⟨h.choose, h.choose_spec, ?_⟩
      simp only [cone] at hne
      split_ifs at hne with h'
      · exact absurd rfl hne
      · refine ⟨h', fun h0 => hne ?_⟩
        simp only [γ, h0, smul_zero]
    · exact absurd rfl hne
  let S : Fin r → Finset (ι ⊕ κ → ℤ) := fun l =>
    Finset.univ.biUnion (fun τ => (c₀ τ l).coeff.support)
  have hS : ∀ σ l e, f σ l e ≠ 0 → e ∈ S l := by
    intro σ l e hne
    obtain ⟨v, -, -, h⟩ := hf σ l e hne
    exact Finset.mem_biUnion.mpr ⟨insert v σ, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩
  let b : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) := fun σ l =>
    AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (S l) (f σ l) (fun e he => hS σ l e he))
  have hb : ∀ σ l e, (b σ l).coeff e = f σ l e := by
    intro σ l e
    simp [b]
  refine ⟨b, fun σ hσ => ⟨?_, ?_⟩, fun σ hσ => ?_⟩
  · rw [mem_loc_top_iff]
    intro l e he z hz
    rw [hb] at he
    obtain ⟨v, hgood, hv, h⟩ := hf σ l e he
    have hcard : (insert v σ).card = q + 1 := by rw [Finset.card_insert_of_notMem hv, hσ]
    rw [hc₀c _ hcard] at h
    have hloc := (mem_loc_top_iff π).mp (hc _ hcard).1 l e h z
    rw [expo_insert π hv] at hloc
    by_cases h1 : z = Sum.inl (π v).1
    · rw [h1]; exact hgood.1
    by_cases h2 : z = Sum.inr (π v).2
    · rw [h2]; exact hgood.2
    apply hloc
    simp [h1, h2, hz]
  · intro l e he
    rw [hb] at he
    obtain ⟨v, -, hv, h⟩ := hf σ l e he
    have hcard : (insert v σ).card = q + 1 := by rw [Finset.card_insert_of_notMem hv, hσ]
    rw [hc₀c _ hcard] at h
    exact (hc _ hcard).2 l e h
  · funext l
    ext e
    have key : (dif b σ l).coeff e = dif (fun τ => f τ l e) σ := by
      rw [← evC_apply, ← dif_map]
      simp only [evC_apply, hb]
    rw [key]
    by_cases h : ∃ v, good e v
    · have hfe : (fun τ => f τ l e) = cone h.choose (γ l e) := by
        funext τ; simp only [f, dif_pos h]
      rw [hfe]
      have hcone := dif_cone h.choose (γ l e) σ
      have hzero : cone h.choose (dif (γ l e)) σ = 0 := by
        simp only [cone]
        split_ifs with hv
        · rfl
        · have hcard : (insert h.choose σ).card = q + 2 := by
            rw [Finset.card_insert_of_notMem hv, hσ]
          have : dif (γ l e) (insert h.choose σ) = 0 := by
            have h1 : dif (γ l e) (insert h.choose σ) = evC l e (dif c₀ (insert h.choose σ)) := by
              rw [← dif_map]; rfl
            rw [h1, dif_congr hc₀c hcard, hdc _ hcard, map_zero]
          rw [this, smul_zero]
      rw [hzero, add_zero] at hcone
      rw [hcone]
      simp only [γ, hc₀c σ hσ]
    · have hfe : (fun τ => f τ l e) = fun _ => 0 := by
        funext τ; simp only [f, dif_neg h]
      rw [hfe, dif_zero']
      by_contra hne
      have hdeg := (hc σ hσ).2 l e (Ne.symm hne)
      have : Nonempty V := by
        obtain ⟨v, -⟩ := Finset.card_pos.mp (by rw [hσ]; omega : 0 < σ.card)
        exact ⟨v⟩
      apply h
      apply exists_nonneg_chart π hπ
      · rw [hdeg]; simp only [Prod.fst_sub]; linarith [(hδ l).1]
      · rw [hdeg]; simp only [Prod.snd_sub]; linarith [(hδ l).2]

end Base

section Graded

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {r : ℕ}

/-- The bidegree-`D` component of a vector of `R^r` whose `j`-th basis vector has bidegree
`s j`. -/
private noncomputable def comp (s : Fin r → ℤ × ℤ) (D : ℤ × ℤ)
    (p : Fin r → MvPolynomial (ι ⊕ κ) k) :
    Fin r → MvPolynomial (ι ⊕ κ) k :=
  fun j => weightedHomogeneousComponent wt (D - s j) (p j)

/-- A vector of `R^r` is homogeneous of bidegree `D` (for the shifts `s`). -/
private def IsHomV (s : Fin r → ℤ × ℤ) (D : ℤ × ℤ) (p : Fin r → MvPolynomial (ι ⊕ κ) k) : Prop :=
  ∀ j, IsWeightedHomogeneous wt (p j) (D - s j)

/-- A submodule of `R^r` is graded (for the shifts `s`). -/
private def Homog (s : Fin r → ℤ × ℤ)
    (M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)) : Prop :=
  ∀ p ∈ M, ∀ D, comp s D p ∈ M

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma weightedHomogeneousComponent_mul_of_isWeightedHomogeneous {m n : ℤ × ℤ}
    {f : MvPolynomial (ι ⊕ κ) k} (hf : IsWeightedHomogeneous wt f n)
    (a : MvPolynomial (ι ⊕ κ) k) :
    weightedHomogeneousComponent wt m (a * f) = weightedHomogeneousComponent wt (m - n) a * f := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  by_cases hx : Finsupp.weight wt x = m
  · rw [if_pos hx]
    apply Finset.sum_congr rfl
    rintro ⟨y, z⟩ hyz
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hyz
    simp only
    rw [coeff_weightedHomogeneousComponent]
    by_cases hz : f.coeff z = 0
    · simp [hz]
    · have hwz := hf hz
      have hy : Finsupp.weight wt y = m - n := by
        rw [← hx, ← hyz, map_add, hwz]; abel
      rw [if_pos hy]
  · rw [if_neg hx]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨y, z⟩ hyz
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hyz
    simp only
    rw [coeff_weightedHomogeneousComponent]
    by_cases hz : f.coeff z = 0
    · simp [hz]
    · have hwz := hf hz
      have hy : Finsupp.weight wt y ≠ m - n := by
        intro hy
        apply hx
        rw [← hyz, map_add, hwz, hy]; abel
      rw [if_neg hy, zero_mul]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma comp_smul {s : Fin r → ℤ × ℤ} {e : ℤ × ℤ} {p : Fin r → MvPolynomial (ι ⊕ κ) k}
    (hp : IsHomV s e p) (D : ℤ × ℤ) (a : MvPolynomial (ι ⊕ κ) k) :
    comp s D (a • p) = weightedHomogeneousComponent wt (D - e) a • p := by
  funext j
  simp only [comp, Pi.smul_apply, smul_eq_mul]
  rw [weightedHomogeneousComponent_mul_of_isWeightedHomogeneous (hp j),
    show D - s j - (e - s j) = D - e by abel]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma comp_sum {s : Fin r → ℤ × ℤ} (D : ℤ × ℤ) {β : Type*} (t : Finset β)
    (g : β → Fin r → MvPolynomial (ι ⊕ κ) k) :
    comp s D (∑ l ∈ t, g l) = ∑ l ∈ t, comp s D (g l) := by
  funext j
  simp [comp, Finset.sum_apply, map_sum]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma comp_of_isHomV {s : Fin r → ℤ × ℤ} {D : ℤ × ℤ} {p : Fin r → MvPolynomial (ι ⊕ κ) k}
    (hp : IsHomV s D p) : comp s D p = p := by
  funext j
  exact weightedHomogeneousComponent_eq_self (hp j)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma isHomV_comp (s : Fin r → ℤ × ℤ) (D : ℤ × ℤ) (p : Fin r → MvPolynomial (ι ⊕ κ) k) :
    IsHomV s D (comp s D p) :=
  fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma sum_weightedHomogeneousComponent_sub (φ : MvPolynomial (ι ⊕ κ) k) (c : ℤ × ℤ)
    (T : Finset (ℤ × ℤ)) (hT : ∀ m ∈ φ.support, Finsupp.weight wt m + c ∈ T) :
    ∑ D ∈ T, weightedHomogeneousComponent wt (D - c) φ = φ := by
  classical
  ext x
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hx : φ.coeff x = 0
  · simp [hx]
  · rw [Finset.sum_eq_single (Finsupp.weight wt x + c)]
    · rw [if_pos (by abel)]
    · intro D _ hD
      rw [if_neg (fun h => hD (by rw [h]; abel))]
    · intro h
      exact absurd (hT x (mem_support_iff.mpr hx)) h

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma exists_sum_comp (s : Fin r → ℤ × ℤ) (p : Fin r → MvPolynomial (ι ⊕ κ) k) :
    ∃ T : Finset (ℤ × ℤ), ∑ D ∈ T, comp s D p = p := by
  classical
  refine ⟨Finset.univ.biUnion (fun j => (p j).support.image (fun m => Finsupp.weight wt m + s j)),
    ?_⟩
  funext j
  simp only [Finset.sum_apply, comp]
  apply sum_weightedHomogeneousComponent_sub
  intro m hm
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- A graded submodule of `R^r` is generated by finitely many homogeneous elements. -/
private lemma exists_homogeneous_generators [Finite ι] [Finite κ] (s : Fin r → ℤ × ℤ)
    (M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)) (hM : Homog s M) :
    ∃ (r' : ℕ) (p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k) (s' : Fin r' → ℤ × ℤ),
      (∀ l, p l ∈ M) ∧ (∀ l, IsHomV s (s' l) (p l)) ∧
      ∀ x ∈ M, ∃ a : Fin r' → MvPolynomial (ι ⊕ κ) k, ∑ l, a l • p l = x := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian M : M.FG)
  choose T hT using exists_sum_comp (k := k) s
  let U : Finset ((Fin r → MvPolynomial (ι ⊕ κ) k) × (ℤ × ℤ)) :=
    S.biUnion (fun g => (T g).image (fun D => (comp s D g, D)))
  have hU : ∀ x ∈ U, x.1 ∈ M ∧ IsHomV s x.2 x.1 := by
    intro x hx
    obtain ⟨g, hg, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hM g (hS ▸ Submodule.subset_span hg) D, isHomV_comp s D g⟩
  let eU := U.equivFin
  refine ⟨U.card, fun l => (eU.symm l).1.1, fun l => (eU.symm l).1.2,
    fun l => (hU _ (eU.symm l).2).1, fun l => (hU _ (eU.symm l).2).2, ?_⟩
  intro x hx
  rw [← Submodule.mem_span_range_iff_exists_fun]
  have hle : M ≤ Submodule.span (MvPolynomial (ι ⊕ κ) k)
      (Set.range (fun l => (eU.symm l).1.1)) := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [← hT g]
    refine Submodule.sum_mem _ (fun D hD => Submodule.subset_span ?_)
    have hmem : (comp s D g, D) ∈ U :=
      Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩
    exact ⟨eU ⟨_, hmem⟩, by simp⟩
  exact hle hx

end Graded

section Phi

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [LinearOrder V] (π : V → ι × κ) {r r' : ℕ}

/-- The map `L^{r'} → L^r` extending `R^{r'} → R^r`, `eₗ ↦ p l`, to Laurent polynomials. -/
private noncomputable def phiL (p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k) :
    (Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) →+ (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) where
  toFun x j := ∑ l, x l * emb (p l j)
  map_zero' := by funext j; simp
  map_add' x y := by funext j; simp [add_mul, Finset.sum_add_distrib]

private lemma phiL_apply (p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k)
    (x : Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) (j : Fin r) :
    phiL p x j = ∑ l, x l * emb (p l j) := rfl

private lemma phiL_emb (p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k)
    (e : Fin r' → MvPolynomial (ι ⊕ κ) k) :
    phiL p (fun l => emb (e l)) = fun j => emb (Fintype.linearCombination _ p e j) := by
  funext j
  simp [phiL_apply, Fintype.linearCombination_apply, Finset.sum_apply, map_sum, map_mul]

private lemma phiL_mon_mul (p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k) (g : ι ⊕ κ → ℤ)
    (x : Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) :
    phiL p (fun l => mon g * x l) = fun j => mon g * phiL p x j := by
  funext j
  simp [phiL_apply, Finset.mul_sum, mul_assoc]

private lemma phiL_mem_degS {p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k} {s : Fin r → ℤ × ℤ}
    {s' : Fin r' → ℤ × ℤ} (hp : ∀ l, IsHomV s (s' l) (p l)) {δ : ℤ × ℤ}
    {x : Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} (hx : x ∈ degS s' δ) :
    phiL p x ∈ degS s δ := by
  intro j
  rw [phiL_apply]
  refine AddSubgroup.sum_mem _ (fun l _ => ?_)
  have := mul_mem_homL (hx l) (emb_mem_homL_iff.mpr (hp l j))
  rwa [show δ - s' l + (s' l - s j) = δ - s j by abel] at this

private lemma phiL_mem_loc {p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k}
    {M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r' → MvPolynomial (ι ⊕ κ) k)}
    {N : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)}
    (hMN : ∀ e ∈ M, Fintype.linearCombination _ p e ∈ N) {σ : Finset V}
    {x : Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} (hx : x ∈ loc π M σ) :
    phiL p x ∈ loc π N σ := by
  obtain ⟨m, e, he, hx⟩ := hx
  refine ⟨m, _, hMN e he, fun j => ?_⟩
  have h1 := congrFun (phiL_mon_mul p (m • expo π σ) x) j
  simp only [hx] at h1
  rw [← h1, phiL_emb]

private lemma phiL_reflect {p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k}
    {N : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)} {σ : Finset V}
    {x : Fin r' → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} (hx : x ∈ loc π ⊤ σ)
    (hpx : phiL p x ∈ loc π N σ) :
    x ∈ loc π (N.comap (Fintype.linearCombination _ p)) σ := by
  obtain ⟨m, e, -, hx⟩ := hx
  obtain ⟨m', n, hn, hy⟩ := hpx
  refine ⟨m + m', uR (k := k) π σ ^ m' • e, ?_, fun l => ?_⟩
  · rw [Submodule.mem_comap, map_smul]
    have key : uR (k := k) π σ ^ m' • Fintype.linearCombination _ p e =
        uR (k := k) π σ ^ m • n := by
      funext j
      apply emb_injective
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, emb_uR]
      have h1 := congrFun (phiL_emb p e) j
      have h2 := congrFun (phiL_mon_mul p (m • expo π σ) x) j
      simp only [hx] at h2
      rw [← h1, h2, ← hy j, ← mon_nsmul, ← mon_nsmul]
      ring
    rw [key]
    exact N.smul_mem _ hn
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, emb_uR, ← hx l, add_smul, mon_add,
      ← mon_nsmul]
    ring

private lemma phiL_lift {p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k} {s : Fin r → ℤ × ℤ}
    {s' : Fin r' → ℤ × ℤ} (hp : ∀ l, IsHomV s (s' l) (p l))
    {M : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)}
    (hgen : ∀ x ∈ M, ∃ a : Fin r' → MvPolynomial (ι ⊕ κ) k, ∑ l, a l • p l = x)
    {σ : Finset V} {δ : ℤ × ℤ} {x : Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)}
    (hx : x ∈ loc π M σ) (hxd : x ∈ degS s δ) :
    ∃ y, y ∈ loc π ⊤ σ ∧ y ∈ degS s' δ ∧ phiL p y = x := by
  obtain ⟨m, q, hq, hx⟩ := hx
  set g := m • expo π σ
  obtain ⟨D, hD⟩ : ∃ D, D = degG g + δ := ⟨_, rfl⟩
  have hqD : IsHomV s D q := by
    intro j
    rw [← emb_mem_homL_iff, ← hx j, show D - s j = degG g + (δ - s j) by rw [hD]; abel]
    exact mul_mem_homL (mon_mem_homL g) (hxd j)
  obtain ⟨a, ha⟩ := hgen q hq
  set a' : Fin r' → MvPolynomial (ι ⊕ κ) k := fun l =>
    weightedHomogeneousComponent wt (D - s' l) (a l)
  have ha' : ∑ l, a' l • p l = q := by
    conv_rhs => rw [← comp_of_isHomV hqD, ← ha, comp_sum]
    exact Finset.sum_congr rfl (fun l _ => (comp_smul (hp l) D (a l)).symm)
  refine ⟨fun l => mon (-g) * emb (a' l), ⟨m, a', Submodule.mem_top, fun l => ?_⟩, fun l => ?_, ?_⟩
  · rw [← mul_assoc, mon_mul_mon_neg, one_mul]
  · have h1 := mul_mem_homL (mon_mem_homL (k := k) (-g))
      (emb_mem_homL_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - s' l) (a l)))
    rwa [show degG (-g) + (D - s' l) = δ - s' l by rw [map_neg, hD]; abel] at h1
  · rw [phiL_mon_mul, phiL_emb]
    funext j
    rw [Fintype.linearCombination_apply, ha']
    dsimp only
    rw [← hx j, ← mul_assoc, mon_neg_mul_mon, one_mul]

private lemma homog_comap {p : Fin r' → Fin r → MvPolynomial (ι ⊕ κ) k} {s : Fin r → ℤ × ℤ}
    {s' : Fin r' → ℤ × ℤ} (hp : ∀ l, IsHomV s (s' l) (p l))
    {N : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)} (hN : Homog s N) :
    Homog s' (N.comap (Fintype.linearCombination _ p)) := by
  intro e he D
  rw [Submodule.mem_comap] at he ⊢
  rw [Fintype.linearCombination_apply] at he ⊢
  have : ∑ l, comp s' D e l • p l = comp s D (∑ l, e l • p l) := by
    rw [comp_sum]
    exact Finset.sum_congr rfl (fun l _ => (comp_smul (hp l) D (e l)).symm)
  rw [this]
  exact hN _ he D

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma homog_bot (s : Fin r → ℤ × ℤ) :
    Homog s (⊥ : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)) := by
  intro p hp D
  rw [Submodule.mem_bot] at hp ⊢
  subst hp
  funext j
  simp [comp]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private lemma homog_top (s : Fin r → ℤ × ℤ) :
    Homog s (⊤ : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)) :=
  fun _ _ _ => Submodule.mem_top

end Phi

section Vanishing

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [Fintype V] [LinearOrder V] (π : V → ι × κ)

/-- `Ȟ^q(M / N)` vanishes in bidegree `δ`, for the extended Čech complex of the charts `u_v`
(degree `q` cochains live on sets of `q + 1` charts; `q = 0` is the cokernel of
`M / N → Ȟ⁰`). -/
private def Van {r : ℕ} (s : Fin r → ℤ × ℤ)
    (M N : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k))
    (δ : ℤ × ℤ) (q : ℕ) : Prop :=
  ∀ c : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)),
    (∀ σ : Finset V, σ.card = q + 1 → c σ ∈ loc π M σ ∧ c σ ∈ degS s δ) →
    (∀ σ : Finset V, σ.card = q + 1 + 1 → dif c σ ∈ loc π N σ) →
    ∃ b : Finset V → (Fin r → AddMonoidAlgebra k (ι ⊕ κ → ℤ)),
      (∀ σ : Finset V, σ.card = q → b σ ∈ loc π M σ ∧ b σ ∈ degS s δ) ∧
      ∀ σ : Finset V, σ.card = q + 1 → c σ - dif b σ ∈ loc π N σ

/-- Serre vanishing in degree `q`: for every graded subquotient `M / N` of a shifted free module,
`Ȟ^q(M / N)` vanishes in all bidegrees `≥ (t, t)` for some `t`. -/
private def VanishesHigh (q : ℕ) : Prop :=
  ∀ (r : ℕ) (s : Fin r → ℤ × ℤ)
    (M N : Submodule (MvPolynomial (ι ⊕ κ) k) (Fin r → MvPolynomial (ι ⊕ κ) k)),
    Homog s M → Homog s N → ∃ t : ℤ, ∀ δ : ℤ × ℤ, t ≤ δ.1 → t ≤ δ.2 → Van π s M N δ q

private lemma vanishesHigh_of_card_le {q : ℕ} (hq : Fintype.card V ≤ q) :
    VanishesHigh (k := k) π q := by
  intro r s M N _ _
  refine ⟨0, fun δ _ _ c _ _ => ⟨0, fun σ _ => ⟨zero_mem _, zero_mem _⟩, fun σ hσ => ?_⟩⟩
  have := Finset.card_le_univ σ
  omega

private lemma vanishesHigh_of_succ (hπ : Function.Surjective π) (q : ℕ)
    (IH : VanishesHigh (k := k) π (q + 1)) : VanishesHigh (k := k) π q := by
  intro r s M N hM hN
  obtain ⟨r', p, s', hpM, hp, hgen⟩ := exists_homogeneous_generators s M hM
  set K := N.comap (Fintype.linearCombination (MvPolynomial (ι ⊕ κ) k) p)
  obtain ⟨tK, htK⟩ := IH r' s' K ⊥ (homog_comap hp hN) (homog_bot s')
  refine ⟨max tK 0 + ∑ l, (|(s' l).1| + |(s' l).2|), fun δ h1 h2 => ?_⟩
  have hsum : ∀ l, |(s' l).1| + |(s' l).2| ≤ ∑ l, (|(s' l).1| + |(s' l).2|) := fun l =>
    Finset.single_le_sum (f := fun l => |(s' l).1| + |(s' l).2|)
      (fun l _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ l)
  have hnn : 0 ≤ ∑ l, (|(s' l).1| + |(s' l).2|) :=
    Finset.sum_nonneg (fun l _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hK1 : tK ≤ δ.1 := by linarith [le_max_left tK 0]
  have hK2 : tK ≤ δ.2 := by linarith [le_max_left tK 0]
  have hs' : ∀ l, (s' l).1 ≤ δ.1 ∧ (s' l).2 ≤ δ.2 := by
    intro l
    have := hsum l
    have := le_abs_self (s' l).1
    have := le_abs_self (s' l).2
    have := abs_nonneg (s' l).1
    have := abs_nonneg (s' l).2
    have := le_max_right tK 0
    constructor <;> linarith
  intro c hc hdc
  have hlift : ∀ σ : Finset V, ∃ y, σ.card = q + 1 →
      y ∈ loc π ⊤ σ ∧ y ∈ degS s' δ ∧ phiL p y = c σ := by
    intro σ
    by_cases hσ : σ.card = q + 1
    · obtain ⟨y, hy1, hy2, hy3⟩ := phiL_lift π hp hgen (hc σ hσ).1 (hc σ hσ).2
      exact ⟨y, fun _ => ⟨hy1, hy2, hy3⟩⟩
    · exact ⟨0, fun h => absurd h hσ⟩
  choose ct hct using hlift
  have hdct : ∀ σ : Finset V, σ.card = q + 1 + 1 → dif ct σ ∈ loc π K σ ∧ dif ct σ ∈ degS s' δ := by
    intro σ hσ
    have h1 : dif ct σ ∈ loc π ⊤ σ :=
      dif_mem (loc π ⊤) (fun τ σ h => loc_mono π h) (fun τ hτ => (hct τ hτ).1) hσ
    have h2 : dif ct σ ∈ degS s' δ :=
      dif_mem (fun _ => degS s' δ) (fun _ _ _ => le_rfl) (fun τ hτ => (hct τ hτ).2.1) hσ
    refine ⟨phiL_reflect π h1 ?_, h2⟩
    have : phiL p (dif ct σ) = dif c σ := by
      rw [← dif_map]; exact dif_congr (fun τ hτ => (hct τ hτ).2.2) hσ
    rw [this]; exact hdc σ hσ
  have hddct : ∀ σ : Finset V, σ.card = q + 1 + 1 + 1 → dif (dif ct) σ ∈ loc π ⊥ σ :=
    fun σ _ => by rw [dif_dif]; exact zero_mem _
  obtain ⟨b, hb, hb'⟩ := htK δ hK1 hK2 (dif ct) hdct hddct
  obtain ⟨e, he, he'⟩ := free_exact π hπ s' δ hs' q (fun σ => ct σ - b σ)
    (fun σ hσ => ⟨sub_mem (hct σ hσ).1 (loc_mono_left π le_top σ (hb σ hσ).1),
      sub_mem (hct σ hσ).2.1 (hb σ hσ).2⟩)
    (fun σ hσ => by
      rw [dif_sub]
      exact (mem_loc_bot π).mp (hb' σ hσ))
  refine ⟨fun σ => phiL p (e σ), fun σ hσ => ⟨?_, phiL_mem_degS hp (he σ hσ).2⟩, fun σ hσ => ?_⟩
  · refine phiL_mem_loc π (fun x _ => ?_) (he σ hσ).1
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ (fun l _ => M.smul_mem _ (hpM l))
  · have : c σ - dif (fun τ => phiL p (e τ)) σ = phiL p (b σ) := by
      rw [dif_map, he' σ hσ, map_sub, (hct σ hσ).2.2]; abel
    rw [this]
    exact phiL_mem_loc π (fun x hx => hx) (hb σ hσ).1

private lemma vanishesHigh (hπ : Function.Surjective π) (q : ℕ) : VanishesHigh (k := k) π q := by
  have : ∀ n q, Fintype.card V ≤ q + n → VanishesHigh (k := k) π q := by
    intro n
    induction n with
    | zero => intro q hq; exact vanishesHigh_of_card_le π hq
    | succ n ih => intro q hq; exact vanishesHigh_of_succ π hπ q (ih (q + 1) (by omega))
  exact this (Fintype.card V) q (by omega)

end Vanishing

section Weights

variable {k : Type*} [Field k] {ι κ : Type*}

/-- The inclusion `ℕ × ℕ → ℤ × ℤ` of bidegrees. -/
private def castNZ : ℕ × ℕ →+ ℤ × ℤ :=
  (Nat.castAddMonoidHom ℤ).prodMap (Nat.castAddMonoidHom ℤ)

private lemma castNZ_apply (d : ℕ × ℕ) : castNZ d = ((d.1 : ℤ), (d.2 : ℤ)) := rfl

private lemma castNZ_injective : Function.Injective castNZ := by
  intro a b h
  simp only [castNZ_apply, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext h.1 h.2

private lemma weight_wt (m : (ι ⊕ κ) →₀ ℕ) :
    Finsupp.weight wt m =
      castNZ (Finsupp.weight (Sum.elim (fun _ ↦ ((1 : ℕ), (0 : ℕ))) (fun _ ↦ (0, 1))) m) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  cases z <;> rfl

private lemma isWeightedHomogeneous_wt_iff {f : MvPolynomial (ι ⊕ κ) k} {d : ℕ × ℕ} :
    IsWeightedHomogeneous wt f (castNZ d) ↔
      IsWeightedHomogeneous (Sum.elim (fun _ ↦ ((1 : ℕ), (0 : ℕ))) (fun _ ↦ (0, 1))) f d := by
  constructor
  · intro h m hm
    exact castNZ_injective (by rw [← weight_wt]; exact h hm)
  · intro h m hm
    rw [weight_wt, h hm]

private lemma weightedHomogeneousComponent_wt_mem {I : Ideal (MvPolynomial (ι ⊕ κ) k)}
    (hI : ∀ (m : ℕ × ℕ), ∀ p ∈ I,
      weightedHomogeneousComponent (Sum.elim (fun _ ↦ ((1 : ℕ), (0 : ℕ))) (fun _ ↦ (0, 1))) m p ∈ I)
    (D : ℤ × ℤ) {p : MvPolynomial (ι ⊕ κ) k} (hp : p ∈ I) :
    weightedHomogeneousComponent wt D p ∈ I := by
  classical
  by_cases h : ∃ d, castNZ d = D
  · obtain ⟨d, rfl⟩ := h
    have : weightedHomogeneousComponent wt (castNZ d) p =
        weightedHomogeneousComponent
          (Sum.elim (fun _ ↦ ((1 : ℕ), (0 : ℕ))) (fun _ ↦ (0, 1))) d p := by
      ext x
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_wt]
      simp only [castNZ_injective.eq_iff]
    rw [this]
    exact hI d p hp
  · have : weightedHomogeneousComponent wt D p = 0 := by
      ext x
      rw [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply, if_neg]
      intro hx
      exact h ⟨_, by rw [← weight_wt, hx]⟩
    rw [this]
    exact I.zero_mem

end Weights

section Localization

private lemma exists_pow_mul_sub_eq_zero_of_awayToAway {A : Type*} [CommRing A] (x y a b : A)
    (m n : ℕ)
    (h : IsLocalization.Away.awayToAwayRight (P := Localization.Away (x * y)) x y
        (Localization.mk a ⟨x ^ m, m, rfl⟩ : Localization.Away x) =
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away (x * y)) y x
        (Localization.mk b ⟨y ^ n, n, rfl⟩ : Localization.Away y)) :
    ∃ K : ℕ, (x * y) ^ K * (a * y ^ n - b * x ^ m) = 0 := by
  have e1 : (Localization.mk a ⟨x ^ m, m, rfl⟩ : Localization.Away x) *
      algebraMap A _ (x ^ m) = algebraMap A _ a := by
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have e2 : (Localization.mk b ⟨y ^ n, n, rfl⟩ : Localization.Away y) *
      algebraMap A _ (y ^ n) = algebraMap A _ b := by
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have f1 := congrArg (IsLocalization.Away.awayToAwayRight (P := Localization.Away (x * y)) x y) e1
  have f2 := congrArg (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (x * y)) y x) e2
  rw [map_mul, IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayRight_eq] at f1
  rw [map_mul, IsLocalization.Away.awayToAwayLeft_eq, IsLocalization.Away.awayToAwayLeft_eq] at f2
  rw [h] at f1
  have key : algebraMap A (Localization.Away (x * y)) (a * y ^ n) =
      algebraMap A (Localization.Away (x * y)) (b * x ^ m) := by
    rw [map_mul, map_mul, ← f1, ← f2]; ring
  obtain ⟨⟨_, K, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (x * y)) key
  exact ⟨K, by rw [mul_sub, hc, sub_self]⟩

private lemma algebraMap_eq_mk_of_pow_mul_eq_zero {A : Type*} [CommRing A] (u a f : A) (m n : ℕ)
    (h : u ^ n * (a - u ^ m * f) = 0) :
    algebraMap A (Localization.Away u) f =
      Localization.mk a (⟨u ^ m, m, rfl⟩ : Submonoid.powers u) := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨u ^ n, n, rfl⟩, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  linear_combination (-1 : A) * h

end Localization

section Charts

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [LinearOrder V] (π : V → ι × κ)

private lemma degG_single (z : ι ⊕ κ) : degG (Pi.single z 1 : ι ⊕ κ → ℤ) = wt z := by
  rw [degG_apply]
  simp [Pi.single_apply]

private lemma degG_expo_singleton (v : V) : degG (expo π {v}) = (1, 1) := by
  simp only [expo, Finset.sum_singleton, map_add, degG_single]
  rfl

omit [Fintype ι] [Fintype κ] in
private lemma expo_pair {v w : V} (h : v ≠ w) : expo π {v, w} = expo π {v} + expo π {w} := by
  simp [expo, Finset.sum_pair h]

private lemma emb_uR_singleton (v : V) :
    emb (X (Sum.inl (π v).1) * X (Sum.inr (π v).2) : MvPolynomial (ι ⊕ κ) k) =
      mon (expo π {v}) := by
  rw [← emb_uR]; simp [uR]

private lemma mon_neg_nsmul (n : ℕ) (g : ι ⊕ κ → ℤ) :
    (mon (-(n • g)) : AddMonoidAlgebra k (ι ⊕ κ → ℤ)) = mon (-g) ^ n := by
  rw [← smul_neg, mon_nsmul]

private lemma dif_singleton {A : Type*} [AddCommGroup A] (b : Finset V → A) (v : V) :
    dif b {v} = b ∅ := by
  simp [dif, sgn, Finset.filter_singleton]

private lemma dif_pair {A : Type*} [AddCommGroup A] (c : Finset V → A) {v w : V} (h : v < w) :
    dif c {v, w} = c {w} - c {v} := by
  have hvw : v ≠ w := h.ne
  rw [dif, Finset.sum_pair hvw, Finset.erase_insert (by simpa using hvw),
    Finset.erase_insert_of_ne hvw, Finset.erase_singleton, insert_empty_eq]
  have h1 : sgn v {v, w} = 1 := by
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, not_lt.mpr h.le]
  have h2 : sgn w {v, w} = -1 := by
    simp [sgn, Finset.filter_insert, Finset.filter_singleton, h]
  rw [h1, h2, one_smul, neg_one_smul, sub_eq_add_neg]

end Charts

private lemma glue_identity {R : Type*} [CommRing R] (X X' Y Y' A B : R) (K mv mw : ℕ)
    (hX : X * X' = 1) (hY : Y * Y' = 1) :
    X ^ (K + mv + mw) * Y ^ (K + mv + mw) * (Y' ^ mw * B - X' ^ mv * A) =
      -(X ^ mw * Y ^ mv) * ((X * Y) ^ K * (A * Y ^ mw - B * X ^ mv)) := by
  have e1 : (Y * Y') ^ mw = 1 := by rw [hY, one_pow]
  have e2 : (X * X') ^ mv = 1 := by rw [hX, one_pow]
  linear_combination (X ^ (K + mv + mw) * Y ^ (K + mv) * B) * e1 -
    (X ^ (K + mw) * Y ^ (K + mv + mw) * A) * e2

private lemma restrict_identity {R : Type*} [CommRing R] (X X' A F : R) (n mv : ℕ)
    (hX : X * X' = 1) :
    X ^ n * (A - X ^ mv * F) = X ^ mv * (X ^ n * (X' ^ mv * A - F)) := by
  have e2 : (X * X') ^ mv = 1 := by rw [hX, one_pow]
  linear_combination (-(X ^ n * A)) * e2

section Sections

variable {k : Type*} [Field k] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {V : Type*} [LinearOrder V] (π : V → ι × κ)

/-- The ideal `I`, as a submodule of the free module of rank one. -/
private noncomputable abbrev idealVec (I : Ideal (MvPolynomial (ι ⊕ κ) k)) :
    Submodule (MvPolynomial (ι ⊕ κ) k) (Fin 1 → MvPolynomial (ι ⊕ κ) k) :=
  Submodule.comap (LinearMap.proj (R := MvPolynomial (ι ⊕ κ) k)
    (φ := fun _ : Fin 1 => MvPolynomial (ι ⊕ κ) k) 0) I

/-- **Gluing on an overlap.** Two local sections `a_v / u_v ^ m_v` and `a_w / u_w ^ m_w` of `S / I`
that agree on `D₊(u_v u_w)` differ, as Laurent polynomials, by an element of `I_{u_v u_w}`. -/
private lemma sub_mem_loc_pair (I : Ideal (MvPolynomial (ι ⊕ κ) k)) {v w : V} (hvw : v ≠ w)
    (av aw : MvPolynomial (ι ⊕ κ) k) (mv mw : ℕ)
    (h : IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)) *
          Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2))))
        (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)))
        (Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2)))
        (Localization.mk (Ideal.Quotient.mk I av) ⟨_, mv, rfl⟩ :
          Localization.Away (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)))) =
      IsLocalization.Away.awayToAwayLeft
        (P := Localization.Away (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)) *
          Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2))))
        (Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2)))
        (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)))
        (Localization.mk (Ideal.Quotient.mk I aw) ⟨_, mw, rfl⟩ :
          Localization.Away (Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2))))) :
    (fun _ => mon (-(mw • expo π {w})) * emb aw - mon (-(mv • expo π {v})) * emb av :
      Fin 1 → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) ∈ loc π (idealVec I) {v, w} := by
  obtain ⟨K, hK⟩ := exists_pow_mul_sub_eq_zero_of_awayToAway
    (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)))
    (Ideal.Quotient.mk I (X (Sum.inl (π w).1) * X (Sum.inr (π w).2)))
    (Ideal.Quotient.mk I av) (Ideal.Quotient.mk I aw) mv mw h
  set uv : MvPolynomial (ι ⊕ κ) k := X (Sum.inl (π v).1) * X (Sum.inr (π v).2)
  set uw : MvPolynomial (ι ⊕ κ) k := X (Sum.inl (π w).1) * X (Sum.inr (π w).2)
  have hQ : (uv * uw) ^ K * (av * uw ^ mw - aw * uv ^ mv) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [map_mul, map_sub, map_pow] using hK
  refine ⟨K + mv + mw,
    fun _ => -(uv ^ mw * uw ^ mv) * ((uv * uw) ^ K * (av * uw ^ mw - aw * uv ^ mv)),
    I.mul_mem_left _ hQ, fun _ => ?_⟩
  rw [expo_pair π hvw, smul_add, mon_add, mon_nsmul, mon_nsmul, mon_neg_nsmul, mon_neg_nsmul]
  have huv : emb uv = mon (expo π {v}) := emb_uR_singleton π v
  have huw : emb uw = mon (expo π {w}) := emb_uR_singleton π w
  simp only [map_mul, map_neg, map_sub, map_pow, huv, huw]
  exact glue_identity _ _ _ _ _ _ K mv mw (mon_mul_mon_neg _) (mon_mul_mon_neg _)

/-- **Restriction to a chart.** If `a / u_v ^ m - F` lies in `I_{u_v}` as a Laurent polynomial,
then `F` restricts to `a / u_v ^ m` on `D₊(u_v)`. -/
private lemma algebraMap_eq_mk_of_mem_loc (I : Ideal (MvPolynomial (ι ⊕ κ) k)) {v : V}
    (a F : MvPolynomial (ι ⊕ κ) k) (m : ℕ)
    {x : Fin 1 → AddMonoidAlgebra k (ι ⊕ κ → ℤ)} (hx : x ∈ loc π (idealVec I) {v})
    (hx0 : x 0 = mon (-(m • expo π {v})) * emb a - emb F) :
    algebraMap _
        (Localization.Away (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2))))
      (Ideal.Quotient.mk I F) = Localization.mk (Ideal.Quotient.mk I a)
        (⟨_, m, rfl⟩ : Submonoid.powers
          (Ideal.Quotient.mk I (X (Sum.inl (π v).1) * X (Sum.inr (π v).2)))) := by
  obtain ⟨n, p, hp, hpe⟩ := hx
  obtain ⟨u, hu⟩ : ∃ u : MvPolynomial (ι ⊕ κ) k, u = X (Sum.inl (π v).1) * X (Sum.inr (π v).2) :=
    ⟨_, rfl⟩
  have hR : u ^ n * (a - u ^ m * F) = u ^ m * p 0 := by
    apply emb_injective
    rw [map_mul, map_mul, ← hpe 0, hx0]
    simp only [map_sub, map_mul, map_pow]
    rw [hu, emb_uR_singleton, mon_nsmul, mon_neg_nsmul]
    exact restrict_identity _ _ _ _ n _ (mon_mul_mon_neg _)
  have hp0 : Ideal.Quotient.mk I (p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hA := congrArg (Ideal.Quotient.mk I) hR
  simp only [map_mul, map_sub, map_pow, hp0, mul_zero] at hA
  subst hu
  exact algebraMap_eq_mk_of_pow_mul_eq_zero _ _ _ _ n hA

end Sections

/-- **Biprojective normality in high bidegree.** Let `I` be a bihomogeneous ideal of
`k[xᵢ, x'ⱼ]` (bigraded by `deg xᵢ = (1, 0)`, `deg x'ⱼ = (0, 1)`), defining a closed subscheme
`X` of `ℙ(V) × ℙ(W)`. There is `δ₀` such that for `δ₁, δ₂ ≥ δ₀`, every section of
`𝒪_X(δ₁, δ₂)` — a family `s i j` of elements of bidegree `(δ₁, δ₂)` of the localizations of
`S ⧸ I` away from `xᵢ x'ⱼ`, agreeing in the localizations away from `xᵢ x'ⱼ xₖ x'ₗ` — is the
restriction of a bihomogeneous polynomial `F` of bidegree `(δ₁, δ₂)`. -/
@[faltings "thm_nt_projective_normality_biprojective"]
theorem exists_isWeightedHomogeneous_restrict_eq_of_compatible
    (k : Type*) [Field k] (ι κ : Type*) [Finite ι] [Finite κ]
    (I : Ideal (MvPolynomial (ι ⊕ κ) k))
    (hI : ∀ (m : ℕ × ℕ), ∀ p ∈ I,
      weightedHomogeneousComponent (Sum.elim (fun _ ↦ (1, 0)) (fun _ ↦ (0, 1))) m p ∈ I) :
    ∃ δ₀ : ℕ, ∀ δ₁ δ₂ : ℕ, δ₀ ≤ δ₁ → δ₀ ≤ δ₂ →
      ∀ s : (i : ι) → (j : κ) →
          Localization.Away (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j))),
        (∀ i j, ∃ (a : MvPolynomial (ι ⊕ κ) k) (m : ℕ),
          IsWeightedHomogeneous (Sum.elim (fun _ ↦ (1, 0)) (fun _ ↦ (0, 1))) a
            (δ₁ + m, δ₂ + m) ∧
          s i j = Localization.mk (Ideal.Quotient.mk I a)
            (⟨_, m, rfl⟩ : Submonoid.powers
              (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j))))) →
        (∀ i j i' j',
          IsLocalization.Away.awayToAwayRight
              (P := Localization.Away (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j)) *
                Ideal.Quotient.mk I (X (Sum.inl i') * X (Sum.inr j'))))
              (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j)))
              (Ideal.Quotient.mk I (X (Sum.inl i') * X (Sum.inr j'))) (s i j) =
            IsLocalization.Away.awayToAwayLeft
              (P := Localization.Away (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j)) *
                Ideal.Quotient.mk I (X (Sum.inl i') * X (Sum.inr j'))))
              (Ideal.Quotient.mk I (X (Sum.inl i') * X (Sum.inr j')))
              (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j))) (s i' j')) →
        ∃ F : MvPolynomial (ι ⊕ κ) k,
          IsWeightedHomogeneous (Sum.elim (fun _ ↦ (1, 0)) (fun _ ↦ (0, 1))) F (δ₁, δ₂) ∧
          ∀ i j, algebraMap _ (Localization.Away
              (Ideal.Quotient.mk I (X (Sum.inl i) * X (Sum.inr j))))
            (Ideal.Quotient.mk I F) = s i j := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let π : Fin (Fintype.card (ι × κ)) → ι × κ := (Fintype.equivFin (ι × κ)).symm
  have hπ : Function.Surjective π := (Fintype.equivFin (ι × κ)).symm.surjective
  have hIhom : Homog (0 : Fin 1 → ℤ × ℤ) (idealVec I) := fun p hp D => by
    have : weightedHomogeneousComponent wt D (p 0) ∈ I :=
      weightedHomogeneousComponent_wt_mem hI D hp
    simpa only [idealVec, Submodule.mem_comap, LinearMap.proj_apply, comp, Pi.zero_apply,
      sub_zero] using this
  obtain ⟨t, ht⟩ := vanishesHigh (k := k) π hπ 0 1 0 ⊤ (idealVec I) (homog_top 0) hIhom
  refine ⟨t.toNat, fun δ₁ δ₂ h1 h2 s hs hcompat => ?_⟩
  choose a m ha hsa using hs
  let cv : Fin (Fintype.card (ι × κ)) → AddMonoidAlgebra k (ι ⊕ κ → ℤ) := fun v =>
    mon (-(m (π v).1 (π v).2 • expo π {v})) * emb (a (π v).1 (π v).2)
  let c : Finset (Fin (Fintype.card (ι × κ))) → (Fin 1 → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) :=
    fun σ _ => ∑ v ∈ σ, cv v
  have hc1 : ∀ v, c {v} = fun _ => cv v := fun v => by funext; simp [c]
  have hmem : ∀ v w, v ≠ w → (fun _ => cv w - cv v : Fin 1 → AddMonoidAlgebra k (ι ⊕ κ → ℤ)) ∈
      loc π (idealVec I) {v, w} := fun v w hvw =>
    sub_mem_loc_pair π I hvw _ _ _ _ (by rw [← hsa, ← hsa]; exact hcompat _ _ _ _)
  have hc : ∀ σ : Finset (Fin (Fintype.card (ι × κ))), σ.card = 0 + 1 →
      c σ ∈ loc π ⊤ σ ∧ c σ ∈ degS (0 : Fin 1 → ℤ × ℤ) ((δ₁ : ℤ), (δ₂ : ℤ)) := by
    intro σ hσ
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hσ
    rw [hc1]
    refine ⟨⟨m (π v).1 (π v).2, fun _ => a (π v).1 (π v).2, Submodule.mem_top, fun _ => ?_⟩,
      fun _ => ?_⟩
    · rw [← mul_assoc, mon_mul_mon_neg, one_mul]
    · convert mul_mem_homL (mon_mem_homL (k := k) (-(m (π v).1 (π v).2 • expo π {v})))
        (emb_mem_homL_iff.mpr (isWeightedHomogeneous_wt_iff.mpr (ha (π v).1 (π v).2)))
        using 2
      rw [map_neg, map_nsmul, degG_expo_singleton, castNZ_apply]
      ext <;> simp
  have hdc : ∀ σ : Finset (Fin (Fintype.card (ι × κ))), σ.card = 0 + 1 + 1 →
      dif c σ ∈ loc π (idealVec I) σ := by
    intro σ hσ
    obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hσ
    rcases lt_or_gt_of_ne hvw with h | h
    · rw [dif_pair c h, hc1, hc1]
      exact hmem v w hvw
    · rw [Finset.pair_comm, dif_pair c h, hc1, hc1, Finset.pair_comm]
      convert neg_mem (hmem v w hvw) using 1
      funext; simp
  obtain ⟨b, hb, hb'⟩ := ht ((δ₁ : ℤ), (δ₂ : ℤ)) (by dsimp only; omega) (by dsimp only; omega)
    c hc hdc
  obtain ⟨n0, p0, -, hp0⟩ := (hb ∅ Finset.card_empty).1
  have hb0 : b ∅ 0 = emb (p0 0) := by
    simpa [expo_empty, mon_zero] using hp0 0
  refine ⟨p0 0, ?_, fun i j => ?_⟩
  · have := (hb ∅ Finset.card_empty).2 0
    rwa [hb0, Pi.zero_apply, sub_zero, show ((δ₁ : ℤ), (δ₂ : ℤ)) = castNZ (δ₁, δ₂) from rfl,
      emb_mem_homL_iff, isWeightedHomogeneous_wt_iff] at this
  · obtain ⟨v, hv⟩ := hπ (i, j)
    obtain rfl : i = (π v).1 := by rw [hv]
    obtain rfl : j = (π v).2 := by rw [hv]
    have h := hb' {v} (Finset.card_singleton v)
    rw [dif_singleton, hc1] at h
    rw [hsa]
    exact algebraMap_eq_mk_of_mem_loc π I _ _ _ h (by simp [cv, hb0])

end Faltings
