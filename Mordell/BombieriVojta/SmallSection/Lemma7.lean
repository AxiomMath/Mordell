module

public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.LineBundle.VojtaDivisor
public import Mordell.BombieriVojta.SmallSection.AffineEvaluation
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.BombieriVojta.SmallSection.U1
public import Mordell.BombieriVojta.SmallSection.U2
public import Mordell.BombieriVojta.Representative.BasicSystem
public import Mordell.BombieriVojta.Representative.NeZero
public import Mordell.BombieriVojta.SmallSection.DimU0
public import Mordell.BombieriVojta.SmallSection.DimU1
public import Mordell.BombieriVojta.SmallSection.DimU2InterU1
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma5
public import Mordell.BombieriVojta.SmallSection.Lemma7Estimate
public import Mordell.BombieriVojta.SmallSection.LinearSystem
public import Mordell.BombieriVojta.Projection.MonomialBasis
public import Mordell.BombieriVojta.Projection.MonomialIndependence
public import Mordell.Height.Siegel.Dimension
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.SmallSection.BasisB
public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import Mordell.CurveProduct.FormRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatAtPullbackMap
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.FunctionField.ProductFunctionField
public import Mordell.BombieriVojta.Projection.FunctionFieldDegree

/-!
# Bombieri's Lemma 7: existence of a small section of `𝒪(V)`

Let `X = (C, P)` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a
number field `k`, with a divisor `P` of degree one. Let `N ≥ 2g + 1`, `n = N - g`, and let
`φ_{NP} : C → ℙⁿ` be the embedding given by a `k`-basis `x = (x₀, …, xₙ)` of `H⁰(C, 𝒪(NP))`,
`s ≥ 1` the auxiliary integer, `φ_B : C × C → ℙᵐ` the second auxiliary embedding, given by the
divisor `B = s (P × C) + s (C × P) - Δ'` with `Δ' = Δ - P × C - C × P`, and
`ψ = φ_{NP} × φ_{NP}`. Assume the basis `x` is generic. Then there is a constant `c₁₀`, depending
only on these data, such that for all `γ > 0` and `ε > 0` there is `D₀` with the following
property: whenever `d₁, d₂, d` are positive integers with `min(d₁, d₂) ≥ D₀`, such that
`δᵢ = (dᵢ + s d) / N` are integers, `V(d₁, d₂, d)` is a Vojta divisor and
`d₁ d₂ - g d² > γ d₁ d₂`, there is a nonzero global section of
`𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹` with a representative `F = (F_i)` with coefficients in `k`
whose height satisfies `h(F) ≤ c₁₀ (d₁ + d₂) / γ + ε (d₁ + d₂)`.

## Main results

* `Faltings.BombieriSiegel.exists_ne_zero_isVojtaRepresentative_logHeight_le`: Bombieri's
  Lemma 7.

## Implementation notes

* The curve and its divisor are `X : Faltings.CurveWithDegreeOneDivisor k`. The divisor `NP`
  on the points of `C` is `N • X.P.mapDomain Subtype.val`.
* The basis `x` is a family `ℓ : Fin (n + 1) → k(C)` with
  `Faltings.BombieriSiegel.IsGenericBasis k X.f (N • P) ℓ`, and `φ_{NP}` is the morphism it
  defines: for all `ν, j` the generic point of `C` lies in `φ_{NP}^{-1} D₊(T_j)` and the pull-back
  of the regular function `T_ν / T_j` of the integral model of `ℙⁿ` (`Proj.awayToSection` of the
  degree-zero fraction) has germ `ℓ_ν / ℓ_j` in `k(C)`. Since `C` is reduced and `ℙⁿ` separated,
  this determines `φ_{NP}`.
* The embedding `φ_B` is a closed immersion over `k` with `φ_B^*𝒪(1) ≅ 𝒪(B)`, stated in
  `Pic(C ×_k C)`: since `B = s (P × C) + s (C × P) - Δ'`, its class is
  `Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1)`. Of the source's requirement that
  `φ_B` be given by a basis `y₀, …, y_m` of `H⁰(C × C, 𝒪(B))`, the statement keeps that `y₀` is a
  nonzero section: `φ_B^{-1} D₊(y₀)` is nonempty.
* Sections and forms over `k` are those over the base `S = Spec k`, with `C ×_k C`,
  `ψ = pullback.map _ _ _ _ φ_{NP} φ_{NP} (𝟙 _) _ _`, and coefficients in `Γ(Spec k, ⊤) ≅ k`.
  `h(F)` is the absolute height `Height.logHeight / [k : ℚ]` of the vector of all coefficients
  of all `F_i`, read in `k` through `Scheme.ΓSpecIso`.
* The integers `d₁, d₂` are in `ℤ` and `d`, `δ₁`, `δ₂` in `ℕ`, with `dᵢ + s d = N δᵢ`; the
  positivity of `d₁, d₂, d` is part of `Faltings.CurveWithDegreeOneDivisor.IsVojtaDivisor`.
* The quantifiers are those of the source with the `o(d₁ + d₂)` made explicit: `c₁₀` is chosen
  before `γ` and `ε`, and `D₀` depends only on `γ` and `ε`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, Lemma 7, pp.
  629–631
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped TensorProduct

namespace Faltings.BombieriSiegel

universe u

/-! ### The basic system on `U₁` as a linear system of small height -/

/-- The Vojta conditions on integer coefficients, read for the natural numbers `d₁.toNat`,
`d₂.toNat`: these are positive and satisfy `g d² < d₁ d₂ < g² d²` in `ℕ`. -/
private theorem isVojtaDivisor_toNat {k : Type u} [Field k] {X : CurveWithDegreeOneDivisor k}
    {d₁ d₂ : ℤ} {d : ℕ} (hV : X.IsVojtaDivisor d₁ d₂ d) :
    0 < d₁.toNat ∧ 0 < d₂.toNat ∧ 0 < d ∧
      genus X.f * d ^ 2 < d₁.toNat * d₂.toNat ∧
      d₁.toNat * d₂.toNat < genus X.f ^ 2 * d ^ 2 ∧
      ((d₁.toNat : ℝ) = d₁) ∧ ((d₂.toNat : ℝ) = d₂) := by
  have h₁ := hV.pos_d₁
  have h₂ := hV.pos_d₂
  have e₁ : ((d₁.toNat : ℤ)) = d₁ := Int.toNat_of_nonneg h₁.le
  have e₂ : ((d₂.toNat : ℤ)) = d₂ := Int.toNat_of_nonneg h₂.le
  refine ⟨by omega, by omega, by exact_mod_cast hV.pos_d, ?_, ?_,
    by exact_mod_cast congrArg (Int.cast (R := ℝ)) e₁,
    by exact_mod_cast congrArg (Int.cast (R := ℝ)) e₂⟩
  · have : ((genus X.f * d ^ 2 : ℕ) : ℤ) < ((d₁.toNat * d₂.toNat : ℕ) : ℤ) := by
      push_cast; rw [e₁, e₂]; exact hV.genus_mul_sq_lt
    exact_mod_cast this
  · have : ((d₁.toNat * d₂.toNat : ℕ) : ℤ) < ((genus X.f ^ 2 * d ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [e₁, e₂]; exact hV.lt_genus_sq_mul_sq
    exact_mod_cast this

/-- The support of `P.mapDomain Subtype.val` consists of closed points. -/
private theorem isClosed_of_mem_support_mapDomain {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) :
    ∀ Q ∈ (X.P.mapDomain Subtype.val).support, IsClosed ({Q} : Set X.C) := by
  intro Q hQ
  classical
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hQ)
  exact x.2

/-- The class of `B = sB (P × C) + sB (C × P) - Δ'` is `(sB + 1)(P × C + C × P) - Δ`, written
with the point classes of the support of `P`. -/
private theorem vojtaClass_eq_sum {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k)
    (sB : ℕ)
    (hPclosed : ∀ Q ∈ (X.P.mapDomain Subtype.val).support, IsClosed ({Q} : Set X.C)) :
    haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
    haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
      (isEffectiveCartierDivisor_ker_diagonal k X.f).1
    X.vojtaClass sB sB (-1) =
      ((sB : ℤ) + 1) • ∑ Q ∈ (X.P.mapDomain Subtype.val).support.attach,
        X.P.mapDomain Subtype.val Q •
          (Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f)
              (Stacks.Zeta.pointClass X.f ⟨Q, hPclosed Q Q.2⟩) +
            Stacks.Picard.schemePullbackClass (pullback.snd X.f X.f)
              (Stacks.Zeta.pointClass X.f ⟨Q, hPclosed Q Q.2⟩)) -
        Stacks.Divisors.picardClass (pullback.diagonal X.f).ker := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  classical
  set P' := X.P.mapDomain Subtype.val
  let G : X.C → Stacks.Picard.ofScheme X.C := fun Q =>
    if h : IsClosed ({Q} : Set X.C) then Stacks.Zeta.pointClass X.f ⟨Q, h⟩ else 0
  let H : Stacks.Picard.ofScheme X.C →+ Stacks.Picard.ofScheme (pullback X.f X.f) :=
    Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f) +
      Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f)
  have hsum : ∑ Q ∈ P'.support.attach, P' Q •
        (Stacks.Picard.schemePullbackClass (pullback.fst X.f X.f)
            (Stacks.Zeta.pointClass X.f ⟨Q, hPclosed Q Q.2⟩) +
          Stacks.Picard.schemePullbackClass (pullback.snd X.f X.f)
            (Stacks.Zeta.pointClass X.f ⟨Q, hPclosed Q Q.2⟩)) =
      H (X.P.sum fun x n => n • Stacks.Zeta.pointClass X.f x) := by
    calc _ = ∑ Q ∈ P'.support.attach, P' Q.1 • H (G Q.1) := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            simp only [G, dite_eq_left (hPclosed Q Q.2)]
            rfl
      _ = ∑ Q ∈ P'.support, P' Q • H (G Q) :=
            Finset.sum_attach P'.support (fun Q => P' Q • H (G Q))
      _ = P'.sum (fun Q n => n • H (G Q)) := rfl
      _ = X.P.sum (fun x n => n • H (G x.1)) :=
            Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
      _ = _ := by
            rw [map_finsuppSum]
            refine Finsupp.sum_congr fun x _ => ?_
            rw [map_zsmul]
            simp only [G, dite_eq_left x.2]
  rw [hsum]
  unfold CurveWithDegreeOneDivisor.vojtaClass
  rw [AddMonoidHom.add_apply]
  dsimp only
  have hc : (X.P.sum fun x n =>
      haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
      n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) =
      X.P.sum fun x n ↦ n • Stacks.Zeta.pointClass X.f x := rfl
  rw [hc]
  generalize (Stacks.Picard.schemePullbackClassHom (pullback.fst X.f X.f))
    (X.P.sum fun x n ↦ n • Stacks.Zeta.pointClass X.f x) = a
  generalize (Stacks.Picard.schemePullbackClassHom (pullback.snd X.f X.f))
    (X.P.sum fun x n ↦ n • Stacks.Zeta.pointClass X.f x) = b
  have : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  generalize Stacks.Divisors.picardClass (Scheme.Hom.ker (pullback.diagonal X.f)) = c
  have key : ∀ {A : Type _} [AddCommGroup A] (a b c : A),
      (sB : ℤ) • a + (sB : ℤ) • b + (-1 : ℤ) • (c - a - b) = ((sB : ℤ) + 1) • (a + b) - c := by
    intros; simp only [add_smul, one_smul, smul_add, smul_sub, neg_one_smul]; abel
  exact key a b c

/-- For `N ≥ 3` and `δ ≥ N - 1`, the pairs `(l, μ)` with `μ < N` and `l + μ ≤ δ` number
`N (δ + 1) - N (N - 1) / 2 ≤ N δ`. -/
private theorem card_pairs_le (N δ : ℕ) (hN : 3 ≤ N) (hδ : N - 1 ≤ δ) :
    Fintype.card {p : Fin (δ + 1) × Fin N // (p.1 : ℕ) + p.2 ≤ δ} ≤ N * δ := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have hcol : ∀ μ : Fin N, (∑ l : Fin (δ + 1), if (l : ℕ) + μ ≤ δ then 1 else 0) = δ + 1 - μ := by
    intro μ
    rw [Fin.sum_univ_eq_sum_range (fun l => if l + (μ : ℕ) ≤ δ then 1 else 0) (δ + 1),
      ← Finset.card_filter]
    have : (Finset.range (δ + 1)).filter (fun l => l + (μ : ℕ) ≤ δ) = Finset.range (δ + 1 - μ) := by
      ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  simp only [hcol]
  rw [Fin.sum_univ_eq_sum_range (fun μ => δ + 1 - μ) N]
  have hsum : ∀ M, M ≤ δ + 1 → (∑ μ ∈ Finset.range M, (δ + 1 - μ)) + ∑ μ ∈ Finset.range M, μ =
      M * (δ + 1) := by
    intro M hM
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => δ + 1)
      (fun μ hμ => by rw [Finset.mem_range] at hμ; omega)]
    simp
  have h1 := hsum N (by omega)
  have h2 := Finset.sum_range_id_mul_two N
  have h3 : N ≤ N * (N - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 ≤ N - 1 := by omega
    exact Nat.mul_le_mul_left N this
  have h4 : N ≤ ∑ μ ∈ Finset.range N, μ := by
    rw [Finset.sum_range_id]; exact h3
  have h5 : N * (δ + 1) = N * δ + N := by ring
  omega

/-- The triples `(l, l', μ)` with `l + μ₁ ≤ δ₁` and `l' + μ₂ ≤ δ₂`, `μ ∈ [0, N)²`: they index
the functions `ξ_a^l ξ'_a^{l'} b_μ` spanning `U₁`. -/
private abbrev Triples (N δ₁ δ₂ : ℕ) : Type :=
  {τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N) //
    (τ.1 : ℕ) + τ.2.2.1 ≤ δ₁ ∧ (τ.2.1 : ℕ) + τ.2.2.2 ≤ δ₂}

/-- The triples `(l, l', μ)` indexing the coordinates of `U₁` split as two families of pairs. -/
private def triplesEquiv (N δ₁ δ₂ : ℕ) :
    Triples N δ₁ δ₂ ≃
      {p : Fin (δ₁ + 1) × Fin N // (p.1 : ℕ) + p.2 ≤ δ₁} ×
        {p : Fin (δ₂ + 1) × Fin N // (p.1 : ℕ) + p.2 ≤ δ₂} where
  toFun τ := (⟨(τ.1.1, τ.1.2.2.1), τ.2.1⟩, ⟨(τ.1.2.1, τ.1.2.2.2), τ.2.2⟩)
  invFun p := ⟨(p.1.1.1, p.2.1.1, p.1.1.2, p.2.1.2), p.1.2, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For `N ≥ 3` and `δᵢ ≥ N - 1` there are at most `N² δ₁ δ₂` triples `(l, l', μ)`. -/
private theorem card_triples_le (N δ₁ δ₂ : ℕ) (hN : 3 ≤ N) (hδ₁ : N - 1 ≤ δ₁)
    (hδ₂ : N - 1 ≤ δ₂) :
    Fintype.card (Triples N δ₁ δ₂) ≤ N ^ 2 * δ₁ * δ₂ := by
  rw [Fintype.card_congr (triplesEquiv N δ₁ δ₂), Fintype.card_prod]
  calc _ ≤ (N * δ₁) * (N * δ₂) :=
        Nat.mul_le_mul (card_pairs_le N δ₁ hN hδ₁) (card_pairs_le N δ₂ hN hδ₂)
    _ = N ^ 2 * δ₁ * δ₂ := by ring

/-- The triple `(0, 0, (0, 0))` is admissible, so there is at least one triple. -/
private theorem card_triples_pos (N δ₁ δ₂ : ℕ) (hN : 0 < N) :
    0 < Fintype.card (Triples N δ₁ δ₂) :=
  Fintype.card_pos_iff.2 ⟨⟨(0, 0, ⟨0, hN⟩, ⟨0, hN⟩), by simp, by simp⟩⟩

/-- A triple is determined by `(l, l', μ)` read in `ℕ × ℕ × (Fin N × Fin N)`. -/
private theorem triples_toNat_injective (N δ₁ δ₂ : ℕ) :
    Function.Injective fun τ : Triples N δ₁ δ₂ => ((τ.1.1 : ℕ), (τ.1.2.1 : ℕ), τ.1.2.2) := by
  rintro ⟨⟨⟨l, hl⟩, ⟨l', hl'⟩, ν⟩, _⟩ ⟨⟨⟨m, hm⟩, ⟨m', hm'⟩, μ⟩, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- `C ×_k C` is integral: `C` is geometrically integral over `k`. -/
private theorem isIntegral_pullback {k : Type u} [Field k] (X : CurveWithDegreeOneDivisor k) :
    IsIntegral (pullback X.f X.f) := by
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst X.f X.f)

/-- If `e` is injective, `e c ∈ V ↔ A c = 0`, and `V` lies in the range of `e`, then the
solution space of `A` has the dimension of `V`. -/
private theorem finrank_ker_mulVecLin_eq {k W ι κ : Type*} [Field k] [AddCommGroup W]
    [Module k W] [Fintype ι] (A : Matrix κ ι k) (e : (ι → k) →ₗ[k] W)
    (he : Function.Injective e) (V : Submodule k W) (hV : ∀ c, e c ∈ V ↔ A.mulVec c = 0)
    (hrange : V ≤ LinearMap.range e) :
    finrank k (LinearMap.ker A.mulVecLin) = finrank k V := by
  have hmap : (LinearMap.ker A.mulVecLin).map e = V := by
    ext w
    refine ⟨fun ⟨c, hc, hw⟩ => hw ▸ (hV c).2 hc, fun hw => ?_⟩
    obtain ⟨c, rfl⟩ := hrange hw
    exact ⟨c, (hV c).1 hw, rfl⟩
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e he _))

/-- The arithmetic of Lemma 7. Suppose that for admissible `(d₁, d₂, d)` there is a linear system
`A` over `k` with `N_u` unknowns, `1 ≤ N_u ≤ (m + 1) N² δ₁ δ₂`, a solution space of dimension at
least `γ d₁ d₂ - c₁₄ (δ₁ + δ₂) - (m + 1)(g - 1)²`, rows of height at most `c₁₃ d + ε₁₃(d) d`,
and every nonzero solution `x` giving a good object of height `h(x)`. Then, by Siegel's lemma
and the final estimate, there is a good object of height at most
`c₁₃ (m + 1)(s + 1)² (d₁ + d₂) / γ + ε (d₁ + d₂)` once `min(d₁, d₂)` is large. -/
private theorem exists_good_of_linearSystem {k : Type u} [Field k] [NumberField k]
    {g m N s : ℕ} (hg : 2 ≤ g) (hs : 1 ≤ s) (hN : 2 * g + 1 ≤ N) {c₁₃ c₁₄ : ℝ}
    (hc₁₃ : 0 ≤ c₁₃) (hc₁₄ : 0 ≤ c₁₄) {ε₁₃ : ℕ → ℝ} (hε₁₃ : ∀ d, 0 ≤ ε₁₃ d)
    (hε₁₃_tendsto : Filter.Tendsto ε₁₃ Filter.atTop (nhds 0))
    (Adm : ℕ → ℕ → ℕ → Prop) (Good : ℕ → ℕ → ℕ → ℝ → Prop)
    (hmono : ∀ d₁ d₂ d B B', B ≤ B' → Good d₁ d₂ d B → Good d₁ d₂ d B')
    {γ : ℝ} (hγ : 0 < γ)
    (hpkg : ∀ d₁ d₂ d : ℕ, Adm d₁ d₂ d → ∃ (ι : Type) (κ : Type) (_ : Fintype ι)
      (_ : Fintype κ) (A : Matrix κ ι k),
      (1 : ℝ) ≤ Fintype.card ι ∧
      (Fintype.card ι : ℝ) ≤
        (m + 1) * N ^ 2 * (((d₁ : ℝ) + s * d) / N) * (((d₂ : ℝ) + s * d) / N) ∧
      γ * d₁ * d₂ - c₁₄ * (((d₁ : ℝ) + s * d) / N + ((d₂ : ℝ) + s * d) / N)
          - (m + 1) * ((g : ℝ) - 1) ^ 2 ≤ finrank k (LinearMap.ker A.mulVecLin) ∧
      (∀ r, Height.logHeight (A r) / finrank ℚ k ≤ c₁₃ * d + ε₁₃ d * d) ∧
      ∀ x : ι → k, x ≠ 0 → A.mulVec x = 0 → Good d₁ d₂ d (Height.logHeight x / finrank ℚ k))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℕ, ∀ d₁ d₂ d : ℕ, 0 < d₁ → 0 < d₂ → 0 < d → D₁ ≤ min d₁ d₂ →
      g * d ^ 2 < d₁ * d₂ → d₁ * d₂ < g ^ 2 * d ^ 2 → Adm d₁ d₂ d →
      Good d₁ d₂ d (c₁₃ * (m + 1) * (s + 1) ^ 2 * ((d₁ : ℝ) + d₂) / γ + ε * ((d₁ : ℝ) + d₂)) := by
  obtain ⟨c_k, hc_k, hSieg⟩ := Faltings.exists_ne_zero_mulVec_eq_zero_logHeight_le k
  obtain ⟨D₁, hD₁⟩ := Faltings.BombieriVojta.exists_pos_and_div_mul_add_log_le (m := m) hg hs hN
    hγ hc₁₃ hc_k hc₁₄ (fun d _ => hε₁₃ d) hε₁₃_tendsto hε
  refine ⟨D₁, fun d₁ d₂ d hd₁ hd₂ hd hD hlo hhi hadm => ?_⟩
  obtain ⟨ι, κ, _, _, A, hN₁, hN₂, hS, hrows, hgood⟩ := hpkg d₁ d₂ d hadm
  have hH : 0 ≤ c₁₃ * d + ε₁₃ d * d :=
    add_nonneg (mul_nonneg hc₁₃ d.cast_nonneg) (mul_nonneg (hε₁₃ d) d.cast_nonneg)
  obtain ⟨hSpos, hbound⟩ := hD₁ d₁ d₂ d hd₁ hd₂ hd hD hlo hhi _ _ _ hN₁ hN₂ le_rfl hH le_rfl
  obtain ⟨x, hx, hAx, hhx⟩ := hSieg A _ _ hSpos hS hH fun r _ => hrows r
  exact hmono _ _ _ _ _ (hhx.trans hbound) (hgood x hx hAx)

/-- Deleting coordinates that vanish does not change the height: if `x` vanishes off the range of
an injective `j`, then `h(x ∘ j) = h(x)`. -/
private theorem logHeight_comp_eq_of_eq_zero {K α β : Type*} [Field K]
    [Height.AdmissibleAbsValues K] [Finite α] (x : α → K) (j : β → α) (hj : Function.Injective j)
    (hx : ∀ a, a ∉ Set.range j → x a = 0) :
    Height.logHeight (x ∘ j) = Height.logHeight x := by
  classical
  have : Finite β := Finite.of_injective j hj
  let e : β ⊕ {a // a ∉ Set.range j} ≃ α :=
    (Equiv.sumCongr (Equiv.ofInjective j hj) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun a => a ∈ Set.range j))
  have he : x ∘ e = Sum.elim (x ∘ j) (0 : {a // a ∉ Set.range j} → K) := by
    ext (b | ⟨a, ha⟩)
    · rfl
    · exact hx a ha
  rw [← Height.logHeight_comp_equiv e x, he, Height.logHeight_sumElim_zero_eq]

/-- The coefficient of `x^{m τ}` in `∑_τ' c_τ' x^{m τ'}` is `c_τ`, for `m` injective. -/
private theorem coeff_sum_monomial {R σ M : Type*} [CommSemiring R] [Fintype M]
    (m : M → σ →₀ ℕ) (hm : Function.Injective m) (c : M → R) (τ : M) :
    (∑ τ', MvPolynomial.monomial (m τ') (c τ')).coeff (m τ) = c τ := by
  classical
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single τ]
  · simp
  · intro τ' _ h; rw [MvPolynomial.coeff_monomial, ite_eq_right (fun e => h (hm e))]
  · simp

/-- The forms `F_t = ∑_τ x_{t,τ} X^{m τ}`, `m` injective, have the height of `x`: the height
of the family of all their coefficients is `h(x)`. -/
private theorem logHeight_coeff_sum_monomial {K R σ T M : Type*} [Field K]
    [Height.AdmissibleAbsValues K] [CommRing R] [Finite T] [Fintype M] (e : R ≃+* K)
    (m : M → σ →₀ ℕ) (hm : Function.Injective m) (x : T × M → K) (F : T → MvPolynomial σ R)
    (hF : ∀ t, F t = ∑ τ, MvPolynomial.monomial (m τ) (e.symm (x (t, τ)))) :
    Height.logHeight (fun c : Σ t, (F t).support => e ((F c.1).coeff c.2)) =
      Height.logHeight x := by
  classical
  have hcoeff : ∀ t τ, (F t).coeff (m τ) = e.symm (x (t, τ)) := fun t τ => by
    rw [hF]; exact coeff_sum_monomial m hm _ τ
  have hsupp : ∀ t α, α ∈ (F t).support → ∃ τ, m τ = α := by
    intro t α hα
    by_contra h
    simp only [not_exists] at h
    refine (MvPolynomial.mem_support_iff.1 hα) ?_
    rw [hF, MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero fun τ _ => by rw [MvPolynomial.coeff_monomial, ite_eq_right (h τ)]
  let j : (Σ t, (F t).support) → T × M := fun c => (c.1, (hsupp c.1 c.2 c.2.2).choose)
  have hj_spec : ∀ c : Σ t, (F t).support, m (j c).2 = c.2 :=
    fun c => (hsupp c.1 c.2 c.2.2).choose_spec
  have hfam : (fun c : Σ t, (F t).support => e ((F c.1).coeff c.2)) = x ∘ j := by
    funext c
    simp only [Function.comp_apply]
    rw [← hj_spec c, hcoeff, RingEquiv.apply_symm_apply]
  have hjinj : Function.Injective j := by
    rintro ⟨t, α, hα⟩ ⟨t', α', hα'⟩ h
    have ht : t = t' := congrArg Prod.fst h
    subst ht
    have : α = α' := (hj_spec ⟨t, α, hα⟩).symm.trans
      ((congrArg (fun p => m p.2) h).trans (hj_spec ⟨t, α', hα'⟩))
    subst this
    rfl
  rw [hfam]
  refine logHeight_comp_eq_of_eq_zero x j hjinj fun ⟨t, τ⟩ hτ => ?_
  by_contra hne
  have hmem : m τ ∈ (F t).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]; simpa using hne
  exact hτ ⟨⟨t, m τ, hmem⟩, Prod.ext rfl (hm (hj_spec ⟨t, m τ, hmem⟩))⟩

/-- The exponent of the monomial `x₀^{δ₁-l-i} x_a^l x_b^i · x'₀^{δ₂-l'-i'} x'_a^{l'} x'_b^{i'}`
attached to the triple `(l, l', (i, i'))`; its affine evaluation is
`ξ_a^l ξ'_a^{l'} b_{(i,i')}`. -/
private noncomputable def tripleExponent {n N : ℕ} (a b : Fin (n + 1)) (δ₁ δ₂ : ℕ)
    (τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N)) : (Fin (n + 1) ⊕ Fin (n + 1)) →₀ ℕ :=
  Finsupp.single (Sum.inl 0) (δ₁ - (τ.1 : ℕ) - (τ.2.2.1 : ℕ)) +
    Finsupp.single (Sum.inl a) (τ.1 : ℕ) + Finsupp.single (Sum.inl b) (τ.2.2.1 : ℕ) +
    Finsupp.single (Sum.inr 0) (δ₂ - (τ.2.1 : ℕ) - (τ.2.2.2 : ℕ)) +
    Finsupp.single (Sum.inr a) (τ.2.1 : ℕ) + Finsupp.single (Sum.inr b) (τ.2.2.2 : ℕ)

/-- Distinct triples give distinct monomials when `0, a, b` are distinct. -/
private theorem tripleExponent_injective {n N : ℕ} {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (δ₁ δ₂ : ℕ) : Function.Injective (tripleExponent (N := N) a b δ₁ δ₂) := by
  intro τ τ' h
  have ev : ∀ v, tripleExponent (N := N) a b δ₁ δ₂ τ v =
      tripleExponent (N := N) a b δ₁ δ₂ τ' v := fun v => by rw [h]
  have h1 := ev (Sum.inl a)
  have h2 := ev (Sum.inl b)
  have h3 := ev (Sum.inr a)
  have h4 := ev (Sum.inr b)
  simp only [tripleExponent, Finsupp.single_tsub, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
    Pi.sub_apply, ne_eq, Sum.inl.injEq, ha.symm, not_false_eq_true, Finsupp.single_eq_of_ne',
    tsub_self, Finsupp.single_eq_same, zero_add, hab, add_zero, reduceCtorEq, hb.symm, hab.symm,
    Sum.inr.injEq] at h1 h2 h3 h4
  obtain ⟨l, l', i, i'⟩ := τ
  obtain ⟨m, m', j, j'⟩ := τ'
  simp only at h1 h2 h3 h4
  simp only [Prod.mk.injEq, Fin.ext_iff]
  exact ⟨h1, h3, h2, h4⟩

/-- For an admissible triple the monomial has bidegree `(δ₁, δ₂)`. -/
private theorem weight_tripleExponent {n N : ℕ} (a b : Fin (n + 1)) (δ₁ δ₂ : ℕ)
    (τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N))
    (h₁ : (τ.1 : ℕ) + τ.2.2.1 ≤ δ₁) (h₂ : (τ.2.1 : ℕ) + τ.2.2.2 ≤ δ₂) :
    Finsupp.weight (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
      Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (tripleExponent a b δ₁ δ₂ τ) = (δ₁, δ₂) := by
  simp only [tripleExponent, map_add, Finsupp.weight_single, Sum.elim_inl, Sum.elim_inr]
  ext <;> simp <;> omega

/-- The affine evaluation of the monomial of a triple `(l, l', (i, i'))` is
`ξ_a^l ξ'_a^{l'} b_{(i, i')}`, the function attached to the triple in the definition of `U₁`. -/
private theorem aeval_monomial_tripleExponent {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) {n N : ℕ} (x : Fin (n + 1) → K)
    (hx₀ : x 0 ≠ 0) (a b : Fin (n + 1)) (δ₁ δ₂ : ℕ)
    (τ : Fin (δ₁ + 1) × Fin (δ₂ + 1) × (Fin N × Fin N))
    (h₁ : (τ.1 : ℕ) + τ.2.2.1 ≤ δ₁) (h₂ : (τ.2.1 : ℕ) + τ.2.2.2 ≤ δ₂) :
    MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)))
        (MvPolynomial.monomial (tripleExponent a b δ₁ δ₂ τ) (1 : k)) /
        (pr₁ (x 0) ^ δ₁ * pr₂ (x 0) ^ δ₂) =
      pr₁ (x a / x 0) ^ (τ.1 : ℕ) * pr₂ (x a / x 0) ^ (τ.2.1 : ℕ) *
        basisB pr₁ pr₂ (x b / x 0) τ.2.2 := by
  have h01 : pr₁ (x 0) ≠ 0 := by simpa using hx₀
  have h02 : pr₂ (x 0) ≠ 0 := by simpa using hx₀
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  simp only [tripleExponent]
  repeat rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod_single_index, pow_zero, Sum.elim_inl, Sum.elim_inr,
    basisB, map_div₀, div_pow]
  obtain ⟨⟨l, hl⟩, ⟨l', hl'⟩, ⟨i, hi⟩, ⟨i', hi'⟩⟩ := τ
  simp only at h₁ h₂ ⊢
  obtain ⟨u, rfl⟩ : ∃ u, δ₁ = l + i + u := ⟨δ₁ - l - i, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, δ₂ = l' + i' + v := ⟨δ₂ - l' - i', by omega⟩
  rw [show l + i + u - l - i = u by omega, show l' + i' + v - l' - i' = v by omega]
  field_simp
  ring

/-- A ring map `ψ : k(C) ⊗[k] k(C) → k(C ×_k C)` with `ψ (a ⊗ b) = pr₁^* a · pr₂^* b` is `k`-linear
for the `k`-structure of `C ×_k C`. -/
private theorem isScalarTower_tensor_functionField {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)]
    (ψ : letI := stalkAlgebraOver k f (genericPoint C)
      C.functionField ⊗[k] C.functionField →+* (pullback f f).functionField)
    (hψ : letI := stalkAlgebraOver k f (genericPoint C)
      ∀ a b, ψ (a ⊗ₜ b) =
        functionFieldMap (pullback.fst f f) a * functionFieldMap (pullback.snd f f) b) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    letI := ψ.toAlgebra
    IsScalarTower k (C.functionField ⊗[k] C.functionField) (pullback f f).functionField := by
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  let := ψ.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  change _ = ψ (algebraMap k (C.functionField ⊗[k] C.functionField) c)
  rw [Algebra.TensorProduct.algebraMap_apply, hψ, map_one, mul_one]
  exact ((functionFieldMapAlgHom k f (pullback.fst f f) _ rfl).commutes c).symm

/-- The two projections `k(C) → k(C ×_k C)` obtained from `ψ` through `includeLeft` and
`includeRight` are the pull-backs `pr₁^*`, `pr₂^*` along the projections. -/
private theorem toAlgHom_comp_include_eq {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsIntegral C] [IsIntegral (pullback f f)]
    (ψ : letI := stalkAlgebraOver k f (genericPoint C)
      C.functionField ⊗[k] C.functionField →+* (pullback f f).functionField)
    (hψ : letI := stalkAlgebraOver k f (genericPoint C)
      ∀ a b, ψ (a ⊗ₜ b) =
        functionFieldMap (pullback.fst f f) a * functionFieldMap (pullback.snd f f) b) :
    letI := stalkAlgebraOver k f (genericPoint C)
    letI := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
    letI := ψ.toAlgebra
    haveI := isScalarTower_tensor_functionField f ψ hψ
    (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) _).comp
        Algebra.TensorProduct.includeLeft =
      functionFieldMapAlgHom k f (pullback.fst f f) (pullback.fst f f ≫ f) rfl ∧
    (IsScalarTower.toAlgHom k (C.functionField ⊗[k] C.functionField) _).comp
        Algebra.TensorProduct.includeRight =
      functionFieldMapAlgHom k f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm := by
  let := stalkAlgebraOver k f (genericPoint C)
  let := stalkAlgebraOver k (pullback.fst f f ≫ f) (genericPoint (pullback f f : Scheme.{u}))
  let := ψ.toAlgebra
  have := isScalarTower_tensor_functionField f ψ hψ
  refine ⟨AlgHom.ext fun a => ?_, AlgHom.ext fun b => ?_⟩
  · change ψ (a ⊗ₜ 1) = _
    rw [hψ, map_one, mul_one]; rfl
  · change ψ (1 ⊗ₜ b) = _
    rw [hψ, map_one, one_mul]; rfl

/-- If `L` is spanned by a family `v` over a subfield `F ≤ k(y)` and `v` lies in `k(y)`, then every
element of `L` is a quotient `P(y) / Q(y)` of polynomials over `k` with `Q(y) ≠ 0`. -/
private theorem exists_eq_aeval_div_aeval_of_span {k L ι κ : Type*} [Field k] [Field L]
    [Algebra k L] (y : ι → L) (F : IntermediateField k L)
    (hF : F ≤ IntermediateField.adjoin k (Set.range y)) (v : κ → L)
    (hv : ∀ ν, v ν ∈ IntermediateField.adjoin k (Set.range y))
    (hspan : Submodule.span F (Set.range v) = ⊤) (z : L) :
    ∃ P Q : MvPolynomial ι k, MvPolynomial.aeval y Q ≠ 0 ∧
      z = MvPolynomial.aeval y P / MvPolynomial.aeval y Q := by
  set K := IntermediateField.adjoin k (Set.range y)
  have hz : z ∈ K := by
    have : z ∈ Submodule.span F (Set.range v) := by rw [hspan]; trivial
    induction this using Submodule.span_induction with
    | mem w hw => obtain ⟨ν, rfl⟩ := hw; exact hv ν
    | zero => exact K.zero_mem
    | add a b _ _ ha hb => exact K.add_mem ha hb
    | smul c w _ hw => exact K.mul_mem (hF c.2) hw
  obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_range_iff k y z).1 hz
  by_cases hQ : MvPolynomial.aeval y Q = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hPQ, hQ, div_zero]; simp
  · exact ⟨P, Q, hQ, hPQ⟩

/-- A tuple whose coordinates lie in the `k`-span of a finite family `w` is
`t ↦ ∑_τ c_{t,τ} w_τ` for some coefficients `c`. -/
private theorem exists_eq_sum_of_mem_pi_span_range {k L σ M : Type*} [Field k] [Field L]
    [Algebra k L] [Fintype M] (w : M → L) (u : σ → L)
    (hu : u ∈ Submodule.pi Set.univ fun _ : σ => Submodule.span k (Set.range w)) :
    ∃ c : σ × M → k, u = fun t => ∑ τ, algebraMap k L (c (t, τ)) * w τ := by
  have h : ∀ t, ∃ c : M → k, ∑ τ, c τ • w τ = u t := fun t =>
    (Submodule.mem_span_range_iff_exists_fun k).1 (hu t (Set.mem_univ _))
  choose c hc using h
  refine ⟨fun p => c p.1 p.2, funext fun t => ?_⟩
  rw [← hc t]
  simp only [Algebra.smul_def]

/-- The spanning set of `U₁` is the range of the functions `ξ_a^l ξ'_a^{l'} b_ν` indexed by the
admissible triples. -/
private theorem setOf_monomial_eq_range {L : Type*} [CommRing L] (α β : L) {N : ℕ}
    (e : Fin N × Fin N → L) (δ₁ δ₂ : ℕ) :
    {f | ∃ (l l' : ℕ) (ν : Fin N × Fin N), l + ν.1 ≤ δ₁ ∧ l' + ν.2 ≤ δ₂ ∧
        f = α ^ l * β ^ l' * e ν} =
      Set.range fun τ : Triples N δ₁ δ₂ =>
        α ^ (τ.1.1 : ℕ) * β ^ (τ.1.2.1 : ℕ) * e τ.1.2.2 := by
  ext f
  constructor
  · rintro ⟨l, l', ν, h₁, h₂, rfl⟩
    exact ⟨⟨(⟨l, by omega⟩, ⟨l', by omega⟩, ν), h₁, h₂⟩, rfl⟩
  · rintro ⟨⟨⟨l, l', ν⟩, h₁, h₂⟩, rfl⟩
    exact ⟨l, l', ν, h₁, h₂, rfl⟩

/-- If the family `W` is linearly independent and `j` is injective, then a coefficient vector `c`
is determined by the tuple `t ↦ ∑_τ c_{t,τ} W_{j τ}`. -/
private theorem injective_sum_of_linearIndependent {k L σ M T : Type*} [Field k] [Field L]
    [Algebra k L] [Fintype M] (W : T → L) (hW : LinearIndependent k W) (j : M → T)
    (hj : Function.Injective j) :
    Function.Injective fun c : σ × M → k => fun t => ∑ τ, algebraMap k L (c (t, τ)) * W (j τ) := by
  intro c c' h
  have hli := (hW.comp j hj)
  funext ⟨t, τ⟩
  have ht := congrFun h t
  simp only at ht
  have h0 : ∑ τ, (c (t, τ) - c' (t, τ)) • (W ∘ j) τ = 0 := by
    simp only [Function.comp_apply, Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [ht, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 τ)

/-- The form `F_t = ∑_τ c_τ X^{m τ}` has bidegree `(δ₁, δ₂)`. -/
private theorem sum_monomial_tripleExponent_mem {k : Type*} [Field k] {n N : ℕ}
    (a b : Fin (n + 1)) (δ₁ δ₂ : ℕ)
    (c : Triples N δ₁ δ₂ → k) :
    (∑ τ, MvPolynomial.monomial (tripleExponent a b δ₁ δ₂ τ.1) (c τ)) ∈
      MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) :=
  Submodule.sum_mem _ fun τ _ => MvPolynomial.isWeightedHomogeneous_monomial _ _ _
    (weight_tripleExponent a b δ₁ δ₂ τ.1 τ.2.1 τ.2.2)

/-- The affine evaluation of `F_t = ∑_τ c_τ X^{m τ}` is `∑_τ c_τ ξ_a^l ξ'_a^{l'} b_ν`. -/
private theorem affineEvaluation_sum_monomial_tripleExponent {k K L : Type*} [Field k] [Field K]
    [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) {n N : ℕ} (x : Fin (n + 1) → K)
    (hx₀ : x 0 ≠ 0) (a b : Fin (n + 1)) (δ₁ δ₂ : ℕ)
    (c : Triples N δ₁ δ₂ → k) :
    Faltings.BombieriVojta.affineEvaluation pr₁ pr₂ x 0 (δ₁, δ₂)
        ⟨_, sum_monomial_tripleExponent_mem a b δ₁ δ₂ c⟩ =
      ∑ τ, algebraMap k L (c τ) * (pr₁ (x a / x 0) ^ (τ.1.1 : ℕ) *
        pr₂ (x a / x 0) ^ (τ.1.2.1 : ℕ) *
          basisB pr₁ pr₂ (x b / x 0) τ.1.2.2) := by
  simp only [Faltings.BombieriVojta.affineEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← aeval_monomial_tripleExponent pr₁ pr₂ x hx₀ a b δ₁ δ₂ τ.1 τ.2.1 τ.2.2,
    show MvPolynomial.monomial (tripleExponent a b δ₁ δ₂ τ.1) (c τ) =
      MvPolynomial.C (c τ) * MvPolynomial.monomial (tripleExponent a b δ₁ δ₂ τ.1) 1 by
        rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.aeval_C, mul_div_assoc]

/-- The tuple `t ↦ ∑_τ c_{t,τ} ξ_a^l ξ'_a^{l'} b_ν` lies in `U₁`: each coordinate is the affine
evaluation of `F_t = ∑_τ c_{t,τ} X^{m τ}` and lies in the span of the `ξ_a^l ξ'_a^{l'} b_ν`. -/
private theorem sum_mem_affineEvaluationTuplesMonomial {k K L : Type*} [Field k] [Field K]
    [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) {n : ℕ} (x : Fin (n + 1) → K)
    (hx₀ : x 0 ≠ 0) (a b : Fin (n + 1)) (N δ₁ δ₂ : ℕ) (σ : Type*)
    (c : σ × Triples N δ₁ δ₂ → k) :
    (fun t => ∑ τ, algebraMap k L (c (t, τ)) * (pr₁ (x a / x 0) ^ (τ.1.1 : ℕ) *
        pr₂ (x a / x 0) ^ (τ.1.2.1 : ℕ) *
          basisB pr₁ pr₂ (x b / x 0) τ.1.2.2)) ∈
      Faltings.BombieriVojta.affineEvaluationTuplesMonomial pr₁ pr₂ x 0 a b N (δ₁, δ₂) σ := by
  refine Submodule.mem_inf.2 ⟨fun t _ => ⟨⟨_, sum_monomial_tripleExponent_mem a b δ₁ δ₂
    fun τ => c (t, τ)⟩, affineEvaluation_sum_monomial_tripleExponent pr₁ pr₂ x hx₀ a b δ₁ δ₂ _⟩,
    fun t _ => Submodule.sum_mem _ fun τ _ => ?_⟩
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨τ.1.1, τ.1.2.1, τ.1.2.2, τ.2.1, τ.2.2, rfl⟩)

/-- **The solution space of the linear system is `U₂ ∩ U₁`.** If `A` cuts out, among the tuples
`t ↦ ∑_τ c_{t,τ} ξ_a^l ξ'_a^{l'} b_ν`, those in `U₂`, and the `ξ_a^l ξ'_a^{l'} b_ν` are linearly
independent, then the solution space of `A` has the dimension of `U₂ ∩ U₁`. -/
private theorem finrank_ker_eq_finrank_basicSystem_inf_monomial {k K L : Type*} [Field k]
    [Field K] [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) {n : ℕ}
    (x : Fin (n + 1) → K) (hx₀ : x 0 ≠ 0) (a b : Fin (n + 1)) (N δ₁ δ₂ : ℕ) (σ : Type*)
    [Fintype σ] (P Q : σ → L) (d : ℕ)
    (hind : LinearIndependent k fun t : ℕ × ℕ × (Fin N × Fin N) =>
      pr₁ (x a / x 0) ^ t.1 * pr₂ (x a / x 0) ^ t.2.1 *
        basisB pr₁ pr₂ (x b / x 0) t.2.2)
    {κ : Type*} (A : Matrix κ (σ × Triples N δ₁ δ₂) k)
    (hA : ∀ c : σ × Triples N δ₁ δ₂ → k,
      (fun t => ∑ τ : Triples N δ₁ δ₂, algebraMap k L (c (t, τ)) *
        (pr₁ (x a / x 0) ^ (τ.1.1 : ℕ) * pr₂ (x a / x 0) ^ (τ.1.2.1 : ℕ) *
            basisB pr₁ pr₂ (x b / x 0) τ.1.2.2)) ∈
        Faltings.BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0 (δ₁, δ₂) σ P Q d ↔
      A.mulVec c = 0) :
    Module.finrank k (LinearMap.ker A.mulVecLin) =
      Module.finrank k ↥(Faltings.BombieriVojta.affineEvaluationTuplesBasicSystem pr₁ pr₂ x 0
          (δ₁, δ₂) σ P Q d ⊓
        Faltings.BombieriVojta.affineEvaluationTuplesMonomial pr₁ pr₂ x 0 a b N (δ₁, δ₂) σ) := by
  classical
  set w : Triples N δ₁ δ₂ → L := fun τ => pr₁ (x a / x 0) ^ (τ.1.1 : ℕ) *
    pr₂ (x a / x 0) ^ (τ.1.2.1 : ℕ) * basisB pr₁ pr₂ (x b / x 0) τ.1.2.2
  let e : (σ × Triples N δ₁ δ₂ → k) →ₗ[k] (σ → L) :=
    LinearMap.pi fun t => ∑ τ, (LinearMap.proj (t, τ)).smulRight (w τ)
  have he : ∀ c, e c = fun t => ∑ τ, algebraMap k L (c (t, τ)) * w τ := by
    intro c; funext t
    simp [e, LinearMap.sum_apply, Algebra.smul_def]
  have hinj : Function.Injective e := by
    intro c c' h
    rw [he, he] at h
    exact injective_sum_of_linearIndependent _ hind _ (triples_toNat_injective N δ₁ δ₂) h
  refine finrank_ker_mulVecLin_eq A e hinj _ (fun c => ?_) (fun u hu => ?_)
  · rw [he, Submodule.mem_inf, hA]
    exact ⟨fun h => h.1, fun h => ⟨h, sum_mem_affineEvaluationTuplesMonomial pr₁ pr₂ x hx₀ a b N
      δ₁ δ₂ σ c⟩⟩
  · have hu₁ := (Submodule.mem_inf.1 hu).2
    have hspan := (Submodule.mem_inf.1 hu₁).2
    rw [setOf_monomial_eq_range] at hspan
    obtain ⟨c, rfl⟩ := exists_eq_sum_of_mem_pi_span_range w u hspan
    exact ⟨c, he c⟩

/-- The forms `F_t = ∑_τ x_{t,τ} X^{m τ}`, with coefficients moved into `Γ(Spec k, ⊤)`, have the
height of `x` when their coefficients are read back in `k`. -/
private theorem logHeight_map_sum_monomial {k : Type u} [Field k] [NumberField k] {σ T M : Type*}
    [Finite T] [Fintype M] (m : M → σ →₀ ℕ) (hm : Function.Injective m) (x : T × M → k) :
    Height.logHeight (fun c : Σ t, ((∑ τ, MvPolynomial.monomial (m τ) (x (t, τ))).map
          (Scheme.ΓSpecIso (.of k)).inv.hom).support =>
        (Scheme.ΓSpecIso (.of k)).hom
          (((∑ τ, MvPolynomial.monomial (m τ) (x (c.1, τ))).map
            (Scheme.ΓSpecIso (.of k)).inv.hom).coeff c.2)) =
      Height.logHeight x :=
  logHeight_coeff_sum_monomial (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv m hm x _
    fun t => by simp only [map_sum, MvPolynomial.map_monomial]; rfl

/-- The degree-one condition on `P` in the form `∑ᶠ Q, P Q · [κ(Q) : k] = 1` for the divisor
`P.mapDomain Subtype.val` on the points of `C`. -/
private theorem finsum_mapDomain_mul_residueDegree {k : Type u} [Field k]
    (X : CurveWithDegreeOneDivisor k) :
    ∑ᶠ Q : X.C, (X.P.mapDomain Subtype.val) Q * (X.f.residueDegree Q : ℤ) = 1 := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := (X.P.mapDomain Subtype.val).support) fun Q hQ => by
    simp only [Function.mem_support] at hQ
    exact Finsupp.mem_support_iff.2 fun h => hQ (by rw [h, zero_mul])]
  change (X.P.mapDomain Subtype.val).sum (fun Q n => n * (X.f.residueDegree Q : ℤ)) = 1
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact X.degree_P

/-- **The basic system on `U₁` as a linear system** in the setting of Bombieri's Lemma 7, for
`δᵢ ≥ max(δ₀, N - 1)`: a linear system `A` over `k` in the coordinates of `U₁`, whose solution
space has the dimension of `U₂ ∩ U₁`, whose rows have small height, and each of whose nonzero
solutions gives a nonzero section of `𝒪(V)` with a representative of the same height. -/
private theorem exists_linearSystem_package {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) (sB : ℕ) (hsB : 1 ≤ sB) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n m : ℕ} (hn : n = N - genus X.f)
    (ℓ : Fin (n + 1) → X.C.functionField)
    (hℓ : haveI : IsCurve k X.f :=
        Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) ℓ)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint X.C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          X.C.presheaf.germ _ (genericPoint X.C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1)) 
    (hy₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set (pullback X.f X.f : Scheme.{u})).Nonempty)
    (δ₀ : ℕ) (hδ₀ : ∀ δ₁ δ₂ : ℕ, δ₀ ≤ δ₁ → δ₀ ≤ δ₂ →
      Function.Surjective fun G : MvPolynomial.weightedHomogeneousSubmodule k
          (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
            Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂) =>
        vojtaFormRestriction
          (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by simp [hφNP]) (by simp [hφNP])) δ₁ δ₂
          (G.1.map (Scheme.ΓSpecIso (.of k)).inv.hom)) :
    ∃ c₁₃ : ℝ, 0 ≤ c₁₃ ∧ ∃ ε₁₃ : ℕ → ℝ, (∀ d, 0 ≤ ε₁₃ d) ∧
      Filter.Tendsto ε₁₃ Filter.atTop (nhds 0) ∧
      ∀ γ : ℝ, 0 < γ → ∀ d₁ d₂ d δ₁ δ₂ : ℕ, X.IsVojtaDivisor d₁ d₂ d →
        γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - genus X.f * (d : ℝ) ^ 2 →
        δ₀ ≤ δ₁ → δ₀ ≤ δ₂ → N - 1 ≤ δ₁ → N - 1 ≤ δ₂ →
        2 * (genus X.f : ℤ) - 2 < N * δ₁ → 2 * (genus X.f : ℤ) - 2 < N * δ₂ →
        4 * (genus X.f : ℤ) - 4 < d₁ + d₂ →
        (d₁ : ℤ) + sB * d = N * δ₁ → (d₂ : ℤ) + sB * d = N * δ₂ →
        ∃ (κ : Type) (_ : Fintype κ) (A : Matrix κ (Fin (m + 1) × Triples N δ₁ δ₂) k),
          γ * (d₁ * d₂ : ℝ) - (((genus X.f : ℝ) - 1) * N + (m + 1) * (N : ℝ) ^ 3 / 2) *
              (δ₁ + δ₂) - (m + 1) * ((genus X.f : ℝ) - 1) ^ 2 ≤
            Module.finrank k (LinearMap.ker A.mulVecLin) ∧
          (∀ r, Height.logHeight (A r) / Module.finrank ℚ k ≤ c₁₃ * d + ε₁₃ d * d) ∧
          ∀ x, x ≠ 0 → A.mulVec x = 0 →
            ∃ s : Γ(vojtaLineBundle
                (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
                  (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤),
              s ≠ 0 ∧
              ∃ F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤),
                IsVojtaRepresentative
                  (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
                    (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s F ∧
                Height.logHeight (fun c : Σ i, (F i).support =>
                    (Scheme.ΓSpecIso (.of k)).hom ((F c.1).coeff c.2)) =
                  Height.logHeight x := by
  classical
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
  have : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
  have := isIntegral_pullback X
  have : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  have hPclosed := isClosed_of_mem_support_mapDomain X
  have hP := finsum_mapDomain_mul_residueDegree X
  have hli := hℓ.linearIndependent
  have hspan := hℓ.span_eq
  have hG1 := hℓ.satisfiesG1
  have hG2 := hℓ.satisfiesG2
  have hn3 : 3 ≤ n := by omega
  set a : Fin (n + 1) := ⟨1, by omega⟩ with ha_def
  set b : Fin (n + 1) := ⟨2, by omega⟩ with hb_def
  have ha : a ≠ 0 := by simp [a, Fin.ext_iff]
  have hb : b ≠ 0 := by simp [b, Fin.ext_iff]
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let := stalkAlgebraOver k X.f (genericPoint X.C)
  have := isDomain_functionField_tensor k X.f X.C.functionField
  obtain ⟨ψ, hψ, hfrac⟩ := exists_isFractionRing_tensor_functionField k X.f X.f rfl rfl
  let := stalkAlgebraOver k (pullback.fst X.f X.f ≫ X.f)
    (genericPoint (pullback X.f X.f : Scheme.{u}))
  let := ψ.toAlgebra
  have := isScalarTower_tensor_functionField X.f ψ hψ
  have := hfrac
  obtain ⟨hpr₁, hpr₂⟩ := toAlgHom_comp_include_eq X.f ψ hψ
  set q₁ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField :=
    (IsScalarTower.toAlgHom k (X.C.functionField ⊗[k] X.C.functionField) _).comp
      Algebra.TensorProduct.includeLeft with hq₁
  set q₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField :=
    (IsScalarTower.toAlgHom k (X.C.functionField ⊗[k] X.C.functionField) _).comp
      Algebra.TensorProduct.includeRight with hq₂
  set y : Fin 4 → (pullback X.f X.f).functionField :=
    ![q₁ (ℓ a / ℓ 0), q₁ (ℓ b / ℓ 0), q₂ (ℓ a / ℓ 0), q₂ (ℓ b / ℓ 0)] with hy
  have hpres : ∀ z : (pullback X.f X.f).functionField, ∃ Pz Qz : MvPolynomial (Fin 4) k,
      MvPolynomial.aeval y Qz ≠ 0 ∧ z = MvPolynomial.aeval y Pz / MvPolynomial.aeval y Qz := by
    obtain ⟨-, hsp⟩ := linearIndependent_and_span_monomial_eq_top
      k X.f hg _ hPclosed hP N hN ℓ hli hspan hG1 hG2 (pullback X.f X.f).functionField a b b a
      ha hb hb ha hab.symm hab
    intro z
    refine exists_eq_aeval_div_aeval_of_span y _ ?_ _ (fun ν => ?_) hsp z
    · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩,
        IntermediateField.subset_adjoin _ _ ⟨3, rfl⟩⟩
    · have h1 : y 1 ∈ IntermediateField.adjoin k (Set.range y) :=
        IntermediateField.subset_adjoin _ _ ⟨1, rfl⟩
      have h2 : y 2 ∈ IntermediateField.adjoin k (Set.range y) :=
        IntermediateField.subset_adjoin _ _ ⟨2, rfl⟩
      exact IntermediateField.mul_mem _ (pow_mem h1 _) (pow_mem h2 _)
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  have : Nonempty ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X 0)) := hy₀.to_subtype
  -- `η_i = T_i / T_0` pulled back along `φB`, in `k(C × C)`
  set η : Fin (m + 1) → (pullback X.f X.f).functionField := fun i =>
    (pullback X.f X.f : Scheme.{u}).germToFunctionField _
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))).app _
        (Proj.awayToSection _ (MvPolynomial.X 0)
          (HomogeneousLocalization.Away.mk
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ))
            (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X i)
            (by simpa using MvPolynomial.isHomogeneous_X _ i)))) with hη
  choose Pη Qη hQη hPη using fun i => hpres (η i)
  obtain ⟨c₁₃, hc₁₃, ε₁₃, hε₁₃, hε₁₃t, hLS⟩ :=
    Faltings.BombieriVojta.exists_mulVec_eq_zero_iff_mem_basicSystem_logHeight_le
      k X.f hg _ hPclosed hP N hN ℓ hli hspan hG1 hG2 (pullback X.f X.f).functionField a b ha hb
      hab.symm (Fin (m + 1)) Pη Qη hQη
  refine ⟨c₁₃, hc₁₃, ε₁₃, hε₁₃, hε₁₃t, fun γ hγ d₁ d₂ d δ₁ δ₂ hV hγd h0₁ h0₂ hN₁ hN₂ hg₁ hg₂
    hg₁₂ e₁ e₂ => ?_⟩
  have hd : 0 < d := by exact_mod_cast hV.pos_d
  obtain ⟨κ, _, A, hA, hrows⟩ := hLS δ₁ δ₂ d hd
  simp only [← hq₁, ← hq₂] at hA
  have hind := Faltings.BombieriSiegel.linearIndependent_pow_mul_pow_mul_basisB
    k X.f hg _ hPclosed hP N hN ℓ hli hspan hG1 hG2 (pullback X.f X.f).functionField a b ha hb
    hab.symm
  simp only [← hq₁, ← hq₂] at hind
  have hℓ0 : ℓ 0 ≠ 0 := hli.ne_zero 0
  refine ⟨κ, inferInstance, A, ?_, hrows, ?_⟩
  · rw [finrank_ker_eq_finrank_basicSystem_inf_monomial q₁ q₂ ℓ hℓ0 a b N δ₁ δ₂ (Fin (m + 1)) _ _
      d hind A hA]
    have hdim := Faltings.BombieriVojta.le_finrank_affineEvaluationTuplesBasicSystem_inf_monomial
      k X.f hg _ hPclosed hP sB hsB N hN hn ℓ hli hspan hG1 hG2 φNP hφNP hφℓ φB hφB
      (hφBB.trans (vojtaClass_eq_sum X sB hPclosed)) hy₀ (fun i => MvPolynomial.aeval y (Pη i))
      (fun i => MvPolynomial.aeval y (Qη i)) hQη hPη d₁ d₂ δ₁ δ₂ d
      (by exact_mod_cast hV.pos_d₁) (by exact_mod_cast hV.pos_d₂) hd e₁ e₂ (hδ₀ δ₁ δ₂ h0₁ h0₂)
      hN₁ hN₂ hg₁ hg₂ hg₁₂ γ hγ (by push_cast; exact hγd) a b ha hb hab
    push_cast at hdim
    rw [← hpr₁, ← hpr₂] at hdim
    exact hdim
  · intro c hc hAc
    set F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) k := fun t =>
      ∑ τ, MvPolynomial.monomial (tripleExponent a b δ₁ δ₂ τ.1) (c (t, τ)) with hF_def
    have hF : ∀ t, F t ∈ MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ)))) (δ₁, δ₂) :=
      fun t => sum_monomial_tripleExponent_mem a b δ₁ δ₂ _
    have hU₂ := (hA c).2 hAc
    -- the affine coordinates `x_ν = T_ν / T_0` of `φNP` are `ℓ_ν / ℓ_0`
    have hx₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) := MvPolynomial.gradedAlgebra
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X 0) : Set X.C).Nonempty := ⟨_, (hφℓ 0 0).1⟩
    have hbs := Faltings.exists_isVojtaRepresentative_iff k X.f hg _ hPclosed hP sB hsB N hN hn
      φNP hφNP φB hφB (d₁ : ℤ) d₂ δ₁ δ₂ d (by exact_mod_cast hV.pos_d₁)
      (by exact_mod_cast hV.pos_d₂) hd e₁ e₂ (hδ₀ δ₁ δ₂ h0₁ h0₂) hx₀ hy₀
      (fun i => MvPolynomial.aeval y (Pη i)) (fun i => MvPolynomial.aeval y (Qη i)) hQη hPη F hF
    let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
      MvPolynomial.gradedAlgebra
    have : Nonempty ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X 0)) := hx₀.to_subtype
    have hxb : (fun ν : Fin (n + 1) => X.C.germToFunctionField _
        ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
          (Proj.awayToSection _ (MvPolynomial.X 0)
            (HomogeneousLocalization.Away.mk
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X ν)
              (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) = fun ν => ℓ ν / ℓ 0 :=
      funext fun ν => (hφℓ ν 0).choose_spec
    have haff : ∀ G : MvPolynomial.weightedHomogeneousSubmodule k
        (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
          Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂),
        Faltings.BombieriVojta.affineEvaluation
          (functionFieldMapAlgHom k X.f (pullback.fst X.f X.f) (pullback.fst X.f X.f ≫ X.f) rfl)
          (functionFieldMapAlgHom k X.f (pullback.snd X.f X.f) (pullback.fst X.f X.f ≫ X.f)
            pullback.condition.symm) (fun ν : Fin (n + 1) => X.C.germToFunctionField _
              ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
                (Proj.awayToSection _ (MvPolynomial.X 0)
                  (HomogeneousLocalization.Away.mk
                    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                    (MvPolynomial.isHomogeneous_X _ 0) 1 (MvPolynomial.X ν)
                    (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) 0 (δ₁, δ₂) G =
          Faltings.BombieriVojta.affineEvaluation q₁ q₂ ℓ 0 (δ₁, δ₂) G := by
      intro G
      rw [hxb, Faltings.BombieriVojta.affineEvaluation_div _ _ _ _ hℓ0, ← hpr₁, ← hpr₂]
    have hev : ∀ t, Faltings.BombieriVojta.affineEvaluation q₁ q₂ ℓ 0 (δ₁, δ₂) ⟨F t, hF t⟩ =
        ∑ τ, algebraMap k _ (c (t, τ)) * (q₁ (ℓ a / ℓ 0) ^ (τ.1.1 : ℕ) *
          q₂ (ℓ a / ℓ 0) ^ (τ.1.2.1 : ℕ) *
            basisB q₁ q₂ (ℓ b / ℓ 0) τ.1.2.2) := fun t =>
      affineEvaluation_sum_monomial_tripleExponent q₁ q₂ ℓ hℓ0 a b δ₁ δ₂ _
    obtain ⟨s, hs⟩ := hbs.2 fun i j => by
      rw [haff, haff, hev, hev]
      exact (Submodule.mem_inf.1 hU₂).2 i j
    refine ⟨s, ?_, _, hs, logHeight_map_sum_monomial
      (fun τ : Triples N δ₁ δ₂ => tripleExponent a b δ₁ δ₂ τ.1)
      ((tripleExponent_injective ha hb hab δ₁ δ₂).comp Subtype.val_injective) c⟩
    refine (Faltings.IsVojtaRepresentative.ne_zero_iff k X.f hg _ hPclosed hP sB hsB N hN hn φNP
      hφNP φB hφB (d₁ : ℤ) d₂ δ₁ δ₂ d (by exact_mod_cast hV.pos_d₁)
      (by exact_mod_cast hV.pos_d₂) hd e₁ e₂ hx₀ hy₀ hs).2 ?_
    obtain ⟨i, hi⟩ : ∃ i, ∑ τ, algebraMap k (pullback X.f X.f).functionField (c (i, τ)) *
        (q₁ (ℓ a / ℓ 0) ^ (τ.1.1 : ℕ) * q₂ (ℓ a / ℓ 0) ^ (τ.1.2.1 : ℕ) *
          basisB q₁ q₂ (ℓ b / ℓ 0) τ.1.2.2) ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      refine hc (injective_sum_of_linearIndependent (σ := Fin (m + 1)) _ hind _
        (triples_toNat_injective N δ₁ δ₂) ?_)
      funext t
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact h t
    have hmm : ((F i).map (Scheme.ΓSpecIso (.of k)).inv.hom).map
        (Scheme.ΓSpecIso (.of k)).hom.hom = F i := by
      have hid : (Scheme.ΓSpecIso (.of k)).hom.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom =
          RingHom.id k := by
        rw [← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
      rw [MvPolynomial.map_map, hid, MvPolynomial.map_id]
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hev, ← haff]
    exact (congrArg _ (Subtype.ext hmm.symm)).trans h0

/-! ### Lemma 7 -/

/-- **Bombieri's Lemma 7** (existence of a small section). Let `X = (C, P)` be a smooth
projective geometrically integral curve of genus `g ≥ 2` over a number field `k` with a divisor
`P` of degree one, `N ≥ 2g + 1`, `n = N - g`, `ℓ` a generic `k`-basis (`IsGenericBasis`) of
`H⁰(C, 𝒪(NP))`, and `φNP : C ⟶ ℙⁿ_k` the closed immersion it defines; let `sB ≥ 1` and let
`φB : C ×_k C ⟶ ℙᵐ_k` be a closed immersion over `k` with `[φB^*𝒪(1)] = X.vojtaClass sB sB (-1)`,
the class of `B = sB (P × C) + sB (C × P) - Δ'`, whose coordinate `y₀` does not vanish
identically on `C ×_k C`. There is `c₁₀` such that for all `γ > 0` and
`ε > 0` there is `D₀` such that, for `d₁, d₂ ≥ D₀` and `d` with `dᵢ + sB d = N δᵢ`,
`X.IsVojtaDivisor d₁ d₂ d` and `d₁ d₂ - g d² > γ d₁ d₂`, some nonzero global section of
`vojtaLineBundle ψ φB δ₁ δ₂ d` (`ψ = φNP × φNP`) has a representative `F`
(`IsVojtaRepresentative`) with coefficients in `k` whose absolute height is at most
`c₁₀ (d₁ + d₂) / γ + ε (d₁ + d₂)`. -/
@[faltings "thm_bvs_auxiliary_section"]
public theorem exists_ne_zero_isVojtaRepresentative_logHeight_le {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k)
    (hg : 2 ≤ genus X.f) (sB : ℕ) (hsB : 1 ≤ sB) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N)
    {n m : ℕ} (hn : n = N - genus X.f)
    (ℓ : Fin (n + 1) → X.C.functionField)
    (hℓ : haveI : IsCurve k X.f :=
        Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      haveI : IsLocallyNoetherian X.C := LocallyOfFiniteType.isLocallyNoetherian X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) ℓ)
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    (hφℓ :
      letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ∀ ν j : Fin (n + 1),
        ∃ h : genericPoint X.C ∈ (φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _) ⁻¹ᵁ
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (MvPolynomial.X j),
          X.C.presheaf.germ _ (genericPoint X.C) h
            ((φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n _).app _
              (Proj.awayToSection
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.X j)
                (HomogeneousLocalization.Away.mk _
                  (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) 1 (MvPolynomial.X ν)
                  (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) ν)))) =
            ℓ ν / ℓ j)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hy₀ : letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
        MvPolynomial.gradedAlgebra
      ((φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k))) ⁻¹ᵁ
        Proj.basicOpen _ (MvPolynomial.X 0) : Set (pullback X.f X.f : Scheme.{u})).Nonempty) :
    ∃ c₁₀ : ℝ, ∀ γ : ℝ, 0 < γ → ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ,
      ∀ (d₁ d₂ : ℤ) (δ₁ δ₂ d : ℕ), (D₀ : ℤ) ≤ d₁ → (D₀ : ℤ) ≤ d₂ →
        d₁ + sB * d = N * δ₁ → d₂ + sB * d = N * δ₂ →
        X.IsVojtaDivisor d₁ d₂ d →
        γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - genus X.f * (d : ℝ) ^ 2 →
        ∃ s : Γ(vojtaLineBundle
            (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
              (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤),
          s ≠ 0 ∧
          ∃ F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤),
            IsVojtaRepresentative
              (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
                (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s F ∧
            Height.logHeight (fun c : Σ i, (F i).support =>
                (Scheme.ΓSpecIso (.of k)).hom ((F c.1).coeff c.2)) / finrank ℚ k ≤
              c₁₀ * (d₁ + d₂ : ℝ) / γ + ε * (d₁ + d₂ : ℝ) := by
  classical
  -- `Good d₁ d₂ d B`: `𝒪(V(d₁, d₂, d))` has a nonzero section with a representative of
  -- height `≤ B`
  let Good : ℕ → ℕ → ℕ → ℝ → Prop := fun d₁ d₂ d B => ∀ δ₁ δ₂ : ℕ,
    (d₁ : ℤ) + sB * d = N * δ₁ → (d₂ : ℤ) + sB * d = N * δ₂ →
    ∃ s : Γ(vojtaLineBundle
        (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
          (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d, ⊤),
      s ≠ 0 ∧
      ∃ F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(Spec (.of k), ⊤),
        IsVojtaRepresentative
          (pullback.map X.f X.f _ _ φNP φNP (𝟙 _) (by rw [Category.comp_id, hφNP])
            (by rw [Category.comp_id, hφNP])) φB δ₁ δ₂ d s F ∧
        Height.logHeight (fun c : Σ i, (F i).support =>
            (Scheme.ΓSpecIso (.of k)).hom ((F c.1).coeff c.2)) / finrank ℚ k ≤ B
  have hmono : ∀ d₁ d₂ d B B', B ≤ B' → Good d₁ d₂ d B → Good d₁ d₂ d B' :=
    fun _ _ _ _ _ hB h δ₁ δ₂ e₁ e₂ => by
      obtain ⟨s, hs, F, hF, hh⟩ := h δ₁ δ₂ e₁ e₂
      exact ⟨s, hs, F, hF, hh.trans hB⟩
  let Adm : ℝ → ℕ → ℕ → ℕ → ℕ → Prop := fun γ D d₁ d₂ d =>
    D ≤ min d₁ d₂ ∧ X.IsVojtaDivisor d₁ d₂ d ∧
      γ * (d₁ * d₂ : ℝ) < (d₁ * d₂ : ℝ) - genus X.f * (d : ℝ) ^ 2 ∧
      ∃ δ₁ δ₂ : ℕ, (d₁ : ℤ) + sB * d = N * δ₁ ∧ (d₂ : ℤ) + sB * d = N * δ₂
  set c₁₄ : ℝ := ((genus X.f : ℝ) - 1) * N + (m + 1) * (N : ℝ) ^ 3 / 2 with hc₁₄_def
  have hc₁₄ : 0 ≤ c₁₄ := by
    have hg' : (1 : ℝ) ≤ genus X.f := by exact_mod_cast (by omega : 1 ≤ genus X.f)
    have : 0 ≤ ((genus X.f : ℝ) - 1) * N := mul_nonneg (by linarith) N.cast_nonneg
    positivity
  obtain ⟨c₁₃, hc₁₃, ε₁₃, hε₁₃, hε₁₃t, hpkg⟩ : ∃ c₁₃ : ℝ, 0 ≤ c₁₃ ∧ ∃ ε₁₃ : ℕ → ℝ,
      (∀ d, 0 ≤ ε₁₃ d) ∧ Filter.Tendsto ε₁₃ Filter.atTop (nhds 0) ∧
      ∀ γ : ℝ, 0 < γ → ∃ D : ℕ, ∀ d₁ d₂ d : ℕ, Adm γ D d₁ d₂ d →
        ∃ (ι : Type) (κ : Type) (_ : Fintype ι) (_ : Fintype κ) (A : Matrix κ ι k),
          (1 : ℝ) ≤ Fintype.card ι ∧
          (Fintype.card ι : ℝ) ≤
            (m + 1) * N ^ 2 * (((d₁ : ℝ) + sB * d) / N) * (((d₂ : ℝ) + sB * d) / N) ∧
          γ * d₁ * d₂ - c₁₄ * (((d₁ : ℝ) + sB * d) / N + ((d₂ : ℝ) + sB * d) / N)
              - (m + 1) * ((genus X.f : ℝ) - 1) ^ 2 ≤ finrank k (LinearMap.ker A.mulVecLin) ∧
          (∀ r, Height.logHeight (A r) / finrank ℚ k ≤ c₁₃ * d + ε₁₃ d * d) ∧
          ∀ x : ι → k, x ≠ 0 → A.mulVec x = 0 →
            Good d₁ d₂ d (Height.logHeight x / finrank ℚ k) := by
    obtain ⟨δ₀, hδ₀⟩ := exists_surjective_vojtaFormRestriction_map X.f φNP hφNP
    obtain ⟨c₁₃, hc₁₃, ε₁₃, hε₁₃, hε₁₃t, hpk⟩ := exists_linearSystem_package X hg sB hsB N hN hn
      ℓ hℓ φNP hφNP hφℓ φB hφB hφBB hy₀ δ₀ hδ₀
    refine ⟨c₁₃, hc₁₃, ε₁₃, hε₁₃, hε₁₃t, fun γ hγ => ⟨N * (δ₀ + N + 4 * genus X.f),
      fun d₁ d₂ d ⟨hD, hV, hγd, δ₁, δ₂, e₁, e₂⟩ => ?_⟩⟩
    have hN0 : N ≠ 0 := by omega
    have hd₁ := hD.trans (min_le_left _ _)
    have hd₂ := hD.trans (min_le_right _ _)
    have e₁' : d₁ + sB * d = N * δ₁ := by exact_mod_cast e₁
    have e₂' : d₂ + sB * d = N * δ₂ := by exact_mod_cast e₂
    have hδ₁ : δ₀ + N + 4 * genus X.f ≤ δ₁ :=
      Nat.le_of_mul_le_mul_left (by rw [← e₁']; omega) (Nat.pos_of_ne_zero hN0)
    have hδ₂ : δ₀ + N + 4 * genus X.f ≤ δ₂ :=
      Nat.le_of_mul_le_mul_left (by rw [← e₂']; omega) (Nat.pos_of_ne_zero hN0)
    have hNδ₁ : N ≤ N * δ₁ := Nat.le_mul_of_pos_right N (by omega)
    have hNδ₂ : N ≤ N * δ₂ := Nat.le_mul_of_pos_right N (by omega)
    have hgN : 4 * genus X.f ≤ N * (δ₀ + N + 4 * genus X.f) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN0))
    obtain ⟨κ, _, A, hS, hrows, hgood⟩ := hpk γ hγ d₁ d₂ d δ₁ δ₂ hV hγd (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) e₁ e₂
    have hδr₁ : ((d₁ : ℝ) + sB * d) / N = δ₁ := by
      rw [div_eq_iff (by exact_mod_cast hN0)]; exact_mod_cast e₁'.trans (mul_comm _ _)
    have hδr₂ : ((d₂ : ℝ) + sB * d) / N = δ₂ := by
      rw [div_eq_iff (by exact_mod_cast hN0)]; exact_mod_cast e₂'.trans (mul_comm _ _)
    refine ⟨_, κ, inferInstance, inferInstance, A, ?_, ?_, ?_, hrows,
      fun x hx hAx δ₁' δ₂' e₁'' e₂'' => ?_⟩
    · rw [Fintype.card_prod, Fintype.card_fin]
      have := card_triples_pos N δ₁ δ₂ (by omega)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    · rw [Fintype.card_prod, Fintype.card_fin, hδr₁, hδr₂]
      refine (Nat.cast_le (α := ℝ)).2 (Nat.mul_le_mul_left (m + 1)
        (card_triples_le N δ₁ δ₂ (by omega) (by omega) (by omega))) |>.trans (le_of_eq ?_)
      push_cast; ring
    · rw [hδr₁, hδr₂, hc₁₄_def]
      convert hS using 2
      ring
    · obtain rfl : δ₁' = δ₁ := by
        exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hN0 : (N : ℤ) ≠ 0) (e₁''.symm.trans e₁)
      obtain rfl : δ₂' = δ₂ := by
        exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hN0 : (N : ℤ) ≠ 0) (e₂''.symm.trans e₂)
      obtain ⟨s, hs, F, hF, hh⟩ := hgood x hx hAx
      exact ⟨s, hs, F, hF, by rw [hh]⟩
  refine ⟨c₁₃ * (m + 1) * (sB + 1) ^ 2, fun γ hγ ε hε => ?_⟩
  obtain ⟨Dp, hDp⟩ := hpkg γ hγ
  obtain ⟨D₁, hD₁⟩ := exists_good_of_linearSystem (g := genus X.f) (m := m) (N := N) (s := sB)
    hg hsB hN hc₁₃ hc₁₄ hε₁₃ hε₁₃t (Adm γ Dp) Good hmono hγ hDp hε
  refine ⟨max D₁ Dp, fun d₁ d₂ δ₁ δ₂ d hD₁' hD₂' hδ₁ hδ₂ hV hγd => ?_⟩
  obtain ⟨p₁, p₂, pd, hlo, hhi, e₁, e₂⟩ := isVojtaDivisor_toNat hV
  have i₁ : ((d₁.toNat : ℕ) : ℤ) = d₁ := Int.toNat_of_nonneg hV.pos_d₁.le
  have i₂ : ((d₂.toNat : ℕ) : ℤ) = d₂ := Int.toNat_of_nonneg hV.pos_d₂.le
  have hmin : max D₁ Dp ≤ min d₁.toNat d₂.toNat := by omega
  have hadm : Adm γ Dp d₁.toNat d₂.toNat d := by
    refine ⟨by omega, by rw [i₁, i₂]; exact hV, by rw [e₁, e₂]; exact hγd, δ₁, δ₂,
      by rw [i₁]; exact hδ₁, by rw [i₂]; exact hδ₂⟩
  have := hD₁ d₁.toNat d₂.toNat d (by omega) (by omega) pd (by omega) hlo hhi hadm δ₁ δ₂
    (by rw [i₁]; exact hδ₁) (by rw [i₂]; exact hδ₂)
  rw [e₁, e₂] at this
  obtain ⟨s, hs, F, hF, hh⟩ := this
  refine ⟨s, hs, F, hF, hh.trans (le_of_eq ?_)⟩
  ring

end Faltings.BombieriSiegel
