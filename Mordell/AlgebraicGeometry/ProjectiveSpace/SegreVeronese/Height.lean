module
public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The height of the Segre–Veronese composite

Let `ψ : X → ℙ(K^ι) × ℙ(K^κ)` be a map to a product of projective spaces and, for
`δ₁, δ₂ ≥ 1`, let `ψ_{δ₁,δ₂} = v_{δ₁,δ₂} ∘ ψ` be its composite with the Segre–Veronese map
of bidegree `(δ₁, δ₂)`. Then for every `p ∈ X`
`h(ψ_{δ₁,δ₂}(p)) = δ₁ h((ψ p).1) + δ₂ h((ψ p).2)`, an exact equality. Indeed, if
`ψ p = ([x], [x'])`, the point `ψ_{δ₁,δ₂}(p)` has coordinates `(x^a x'^b)_{|a| = δ₁, |b| = δ₂}`,
the Segre product of the Veronese images `Φ_{δ₁}(x)` and `Φ_{δ₂}(x')`; the height of a Segre
product is the sum of the heights, and the height of `Φ_δ(x)` is `δ h(x)`.

In Bombieri's setting `X = (C × C)(k̄)` and `ψ = φ_{NP} × φ_{NP}`, so that
`h_{ψ_{δ₁,δ₂}}(z, w) = δ₁ h_{NP}(z) + δ₂ h_{NP}(w)`.

## Main results

* `Faltings.logHeight_segreVeroneseComposite`: the height of `ψ_{δ₁,δ₂}(p)` is
  `δ₁ h((ψ p).1) + δ₂ h((ψ p).2)`.

## Implementation notes

Heights are `Projectivization.logHeight` over a field `K` with admissible absolute values, for
instance a number field. For a number field this is `[K : ℚ]` times the absolute height; since the
identity is homogeneous in the heights, it is equivalent to the identity for absolute heights, and
a point over `k̄` is a point over a number field `K`, where all its coordinates lie. The coordinate
types `ι`, `κ` of the two factors are arbitrary finite types; the monomials of a fixed degree in
finitely many variables form a finite type by `Finsupp.finite_of_degree_eq`.

## References

* [Bombieri, *The Mordell conjecture revisited*, Sec. 3, p. 619][bombieri1990]
-/

open scoped LinearAlgebra.Projectivization

namespace Faltings

private lemma finite_degree_eq {ι : Type*} [Finite ι] (δ : ℕ) :
    Finite {a : ι →₀ ℕ // a.degree = δ} :=
  (Finsupp.finite_of_degree_eq δ).to_subtype

attribute [local instance] finite_degree_eq

section Veronese

variable {K : Type*} [Field K] {ι : Type*}

/-- The Veronese image `(x^a)_{|a| = δ}` of a tuple `x`. -/
private noncomputable def veronese (x : ι → K) (δ : ℕ) : {a : ι →₀ ℕ // a.degree = δ} → K :=
  fun a => a.1.prod fun i k => x i ^ k

private lemma veronese_single (x : ι → K) (δ : ℕ) (i : ι) :
    veronese x δ ⟨Finsupp.single i δ, by simp⟩ = x i ^ δ := by
  simp [veronese]

private lemma veronese_ne_zero {x : ι → K} (hx : x ≠ 0) (δ : ℕ) : veronese x δ ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Function.ne_iff.mpr ⟨⟨Finsupp.single i δ, by simp⟩, by
    simpa [veronese_single] using pow_ne_zero δ hi⟩

/-- `Φ_{δ+1}(x)` is a subfamily of the Segre product `Φ_δ(x) ⊗ x`, along `a ↦ (a - eᵢ, i)` for
some `i` in the support of `a`. -/
private lemma exists_eq_add_single {δ : ℕ} {a : ι →₀ ℕ} (ha : a.degree = δ + 1) :
    ∃ i, ∃ b : ι →₀ ℕ, b.degree = δ ∧ a = b + Finsupp.single i 1 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr (by rintro rfl; simp at ha : a ≠ 0)
  have hle : Finsupp.single i 1 ≤ a := by
    simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hi
  refine ⟨i, a - Finsupp.single i 1, ?_, (tsub_add_cancel_of_le hle).symm⟩
  have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  simp only [map_add, Finsupp.degree_single] at this
  omega

variable [Height.AdmissibleAbsValues K]

private lemma logHeight_veronese_le [Finite ι] {x : ι → K} (hx : x ≠ 0) (δ : ℕ) :
    Height.logHeight (veronese x δ) ≤ δ * Height.logHeight x := by
  induction δ with
  | zero =>
    have : Subsingleton {a : ι →₀ ℕ // a.degree = 0} :=
      ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ => Subtype.ext <|
        ((Finsupp.degree_eq_zero_iff _).mp ha).trans
          ((Finsupp.degree_eq_zero_iff _).mp hb).symm⟩
    simp [Height.logHeight_eq_zero_of_subsingleton]
  | succ δ ih =>
    choose i b hb hab using fun a : {a : ι →₀ ℕ // a.degree = δ + 1} => exists_eq_add_single a.2
    have : veronese x (δ + 1) =
        (fun q : {b : ι →₀ ℕ // b.degree = δ} × ι => veronese x δ q.1 * x q.2) ∘
          fun a => (⟨b a, hb a⟩, i a) := by
      ext a
      simp only [Function.comp_apply, veronese]
      rw [hab a, Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (by simp), pow_one]
    rw [this]
    refine (Height.logHeight_comp_le _ _).trans ?_
    rw [Height.logHeight_fun_mul_eq (veronese_ne_zero hx δ) hx]
    push_cast
    linarith

/-- The Veronese image of a nonzero tuple `x` has height `δ h(x)`. -/
private lemma logHeight_veronese [Finite ι] {x : ι → K} (hx : x ≠ 0) (δ : ℕ) :
    Height.logHeight (veronese x δ) = δ * Height.logHeight x := by
  refine le_antisymm (logHeight_veronese_le hx δ) ?_
  rw [← Height.logHeight_pow]
  have : x ^ δ = veronese x δ ∘ fun i => ⟨Finsupp.single i δ, by simp⟩ := by
    ext i; simp [veronese_single]
  exact this ▸ Height.logHeight_comp_le _ _

end Veronese

/-- **Height of the Segre–Veronese composite.** For a map `ψ : X → ℙ(K^ι) × ℙ(K^κ)` and
`δ₁, δ₂ ≥ 1`, the height of `ψ_{δ₁,δ₂}(p) = segreVeroneseComposite K δ₁ δ₂ h₁ h₂ ψ p` is exactly
`δ₁ h((ψ p).1) + δ₂ h((ψ p).2)`. -/
@[faltings "lem_bv_height_segre_veronese"]
public theorem logHeight_segreVeroneseComposite (K : Type*) [Field K]
    [Height.AdmissibleAbsValues K] {X ι κ : Type*} [Finite ι] [Finite κ]
    (δ₁ δ₂ : ℕ) (h₁ : 1 ≤ δ₁) (h₂ : 1 ≤ δ₂) (ψ : X → ℙ K (ι → K) × ℙ K (κ → K)) (p : X) :
    haveI : Finite {a : ι →₀ ℕ // a.degree = δ₁} := (Finsupp.finite_of_degree_eq δ₁).to_subtype
    haveI : Finite {b : κ →₀ ℕ // b.degree = δ₂} := (Finsupp.finite_of_degree_eq δ₂).to_subtype
    (segreVeroneseComposite K δ₁ δ₂ h₁ h₂ ψ p).logHeight =
      δ₁ * (ψ p).1.logHeight + δ₂ * (ψ p).2.logHeight := by
  conv_rhs => rw [← (ψ p).1.mk_rep, ← (ψ p).2.mk_rep]
  rw [segreVeroneseComposite, Projectivization.logHeight_mk,
    Projectivization.logHeight_mk, Projectivization.logHeight_mk,
    ← logHeight_veronese (ψ p).1.rep_nonzero, ← logHeight_veronese (ψ p).2.rep_nonzero,
    ← Height.logHeight_fun_mul_eq (veronese_ne_zero (ψ p).1.rep_nonzero δ₁)
      (veronese_ne_zero (ψ p).2.rep_nonzero δ₂)]
  rfl

end Faltings
