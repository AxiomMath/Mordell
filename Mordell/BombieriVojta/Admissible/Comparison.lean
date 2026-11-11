module
public import Mordell.Attr
public import Mordell.BombieriVojta.Admissible.Basic
public import Mordell.BombieriVojta.TripleFunction.AdmissiblePair
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
import Mordell.BombieriVojta.Admissible.Intrinsic
import Mordell.BombieriVojta.TripleFunction.Formula
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic

/-!
# Comparison of the two notions of admissible pair

Let `C` be a smooth curve over a field `K`, let `X = C ×_K C`, and let `𝒪(V)` be the line
bundle `ψ^*𝒪(δ₁, δ₂) ⊗ φ^*𝒪(d)⁻¹` on `X` (`Faltings.vojtaLineBundle`). For a global section
`s ≠ 0` of `𝒪(V)` and a `K`-point `p = (z, w)` of `X` there are two notions of an admissible
pair `(i₁*, i₂*)`:

* the intrinsic one, `Faltings.BombieriRoth.IsAdmissiblePair`: for some uniformizers `ς, ς'`
  at `z, w` and some local generator `e` of `𝒪(V)` at `p`, the pair is a minimal element of the
  support of the expansion of `s / e` in `ς, ς'`;
* the one of Section 6, `BombieriVojta.IsAdmissiblePair`: for given local parameters
  `ς, ς'`, there is a non-vanishing triple `(i, j, j')` at `p` such that the function
  `G_{ijj'} = s / e_{ijj'}` (`BombieriVojta.tripleFunction`) is regular at `p` and
  `(i₁*, i₂*)` is a minimal element of the support of its Taylor coefficients
  `∂_{i₁} ∂'_{i₂} G_{ijj'}(p)` (`BombieriVojta.taylorCoeff₂`).

This file states that the first implies the second, for every choice of uniformizers `ς, ς'`.
The proof takes a non-vanishing triple, which exists since the coordinate charts `D₊(Tₖ)`
cover projective space. The section `e_{ijj'} = x_j^{δ₁} x'_{j'}^{δ₂} / y_i^d` generates `𝒪(V)`
on the open where it is defined (`Faltings.BombieriVojta.TripleGenerator.isGen_genU`): the chart
sections `Tₖ ^ a` generate the twisting sheaves on `D₊(Tₖ)`, and generators are preserved by
pullback, restriction and tensor product. Hence
`s / e_{ijj'} = G_{ijj'}`, and `Faltings.BombieriRoth.IsAdmissiblePair.taylorCoeff₂` (admissibility
does not depend on the uniformizers and the local generator) gives the Taylor coefficients.

## Main results

* `Faltings.exists_bijective_smul_vojtaLineBundle`: `𝒪(V)` has a local generator at every point.
* `Faltings.BombieriRoth.IsAdmissiblePair.bombieriVojta`: a pair admissible for `s` at `p` is
  admissible in the sense of Section 6 with respect to any uniformizers `ς, ς'` at the two
  projections of `p`.

## Implementation notes

The source works with a curve `C` over a number field `k` and a point of `(C × C)(K)` for a
number field `K ⊇ k`; here `C` is a smooth curve over the field `K` of the point (the base
change of the source's curve), and `K` is any field. The morphisms `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S`,
`φ : X ⟶ ℙᵐ_S` and the integers `δ₁, δ₂, d` are arbitrary, as in `Faltings.vojtaLineBundle`.
The uniformizers of Section 6 are elements of the local ring of `X` at `p`; they are the images
`ς ∘ pr₁`, `ς' ∘ pr₂` of the uniformizers `ς, ς'` of `C` at `z, w` under the stalk maps of the
projections.

## References

* [Bombieri, *The Mordell conjecture revisited*, §6, p. 625][bombieri1990]
-/

open AlgebraicGeometry CategoryTheory Limits IsLocalRing Opposite MonoidalCategory
open Faltings.BombieriVojta.TripleGenerator

namespace Faltings.BombieriRoth

universe u

section Triple

/-- Every point of a scheme mapping to `ℙʳ_S` lies over a standard chart `D₊(Tₖ)`. -/
private lemma exists_mem_chart {S Y : Scheme.{u}} (r : ℕ) (f : Y ⟶ projectiveSpaceOver r S)
    (y : Y) : ∃ k : Fin (r + 1), y ∈ f ⁻¹ᵁ chart S r k := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  have hy : projectiveSpaceOver.toIntegralAtUniverse r S (f y) ∈
      (⨆ k : Fin (r + 1), Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) (MvPolynomial.X k)) := by
    rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) r]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨k, hk⟩

variable {S X : Scheme.{u}} {n m : ℕ}
  (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
  (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℤ)

/-- Every point `x` of `X` has an open neighbourhood `U` on which `𝒪(V)` has a generator `e`:
multiplication by the restriction of `e` is bijective over every open `V ⊆ U`. One may take
`e = e_{ijj'}` on `U = U_{ijj'}` for a triple `(i, j, j')` with `x ∈ U_{ijj'}`. -/
public theorem _root_.Faltings.exists_bijective_smul_vojtaLineBundle (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (e : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, U)),
      ∀ V (hVU : V ≤ U), Function.Bijective fun a : Γ(X, V) =>
        a • (vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE hVU).op e := by
  obtain ⟨i, hi⟩ := exists_mem_chart m φ x
  obtain ⟨j, hj⟩ := exists_mem_chart n (ψ ≫ pullback.fst _ _) x
  obtain ⟨j', hj'⟩ := exists_mem_chart n (ψ ≫ pullback.snd _ _) x
  exact ⟨chartU ψ φ i j j', ⟨⟨hj, hj'⟩, hi⟩, genU ψ φ δ₁ δ₂ (-d) i j j',
    isGen_genU ψ φ δ₁ δ₂ (-d) i j j'⟩

end Triple

/-- The comparison, with the conclusion of `Faltings.BombieriRoth.IsAdmissiblePair.taylorCoeff₂`
for the chosen data taken as the hypothesis `H`. -/
private lemma bombieriVojta_of_forall {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))]
    [IrreducibleSpace ↥(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))]
    {S : Scheme.{u}} {n m : ℕ}
    (ψ : pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ⟶
      pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ⟶ projectiveSpaceOver m S)
    (δ₁ δ₂ d : ℤ) (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))
    [p.IsOver (Spec (.of K))] (i : ℕ × ℕ)
    (ς ς' : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.stalk (p (closedPoint K)))
    (H : ∀ (U : (pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).Opens)
      (hxU : p (closedPoint K) ∈ U) (e : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, U))
      (_ : IsGen (vojtaLineBundle ψ φ δ₁ δ₂ d) U e)
      (σ : Γ(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)), U))
      (_ : σ • e = (vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE le_top).op s),
      let c : ℕ × ℕ → K := fun j => BombieriVojta.taylorCoeff₂ p ς ς'
        ((pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).presheaf.germ U _ hxU σ) j.1 j.2
      c i ≠ 0 ∧ ∀ j ≤ i, j ≠ i → c j = 0) :
    BombieriVojta.IsAdmissiblePair ψ φ δ₁ δ₂ d s p ς ς' i.1 i.2 := by
  let : ∀ r : ℕ, GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
    fun _ => MvPolynomial.gradedAlgebra
  obtain ⟨i₀, hi₀⟩ := exists_mem_chart m φ (p (closedPoint K))
  obtain ⟨j, hj⟩ := exists_mem_chart n (ψ ≫ pullback.fst _ _) (p (closedPoint K))
  obtain ⟨j', hj'⟩ := exists_mem_chart n (ψ ≫ pullback.snd _ _) (p (closedPoint K))
  have hxU : p (closedPoint K) ∈ chartU ψ φ i₀ j j' := ⟨⟨hj, hj'⟩, hi₀⟩
  have he := isGen_genU ψ φ δ₁ δ₂ (-d) i₀ j j'
  set e := genU ψ φ δ₁ δ₂ (-d) i₀ j j'
  set σ := Function.invFun
    (fun g : Γ(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)), chartU ψ φ i₀ j j') => g • e)
    ((vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE le_top).op s)
  have hσ : σ • e = (vojtaLineBundle ψ φ δ₁ δ₂ d).presheaf.map (homOfLE le_top).op s :=
    Function.invFun_eq (he.bijective.2 _)
  obtain ⟨h₁, h₂⟩ := H _ hxU e he σ hσ
  refine ⟨i₀, j, j', ⟨hi₀, hj, hj'⟩, _, ?_, h₁, fun i₁ hi₁ i₂ hi₂ hne =>
    h₂ (i₁, i₂) (Prod.mk_le_mk.2 ⟨hi₁, hi₂⟩) hne⟩
  have : Nonempty (chartU ψ φ i₀ j j') := ⟨⟨_, hxU⟩⟩
  exact (Scheme.algebraMap_germ_eq_germToFunctionField _ hxU σ).trans
    (tripleFunction_eq ψ φ δ₁ δ₂ d s (p (closedPoint K)) i₀ j j' ⟨hi₀, hj, hj'⟩).symm

/-- Let `C` be a smooth curve over `K`, `s ≠ 0` a global section of
`𝒪(V) = vojtaLineBundle ψ φ δ₁ δ₂ d` on `C ×_K C`, and `p` a `K`-point of `C ×_K C`.
If `i = (i₁*, i₂*)` is admissible for `s` at `p`, then for all local uniformizing parameters
`ς, ς'` of `C` at the two projections of `p`, the pair is admissible in the sense of
`BombieriVojta.IsAdmissiblePair` with respect to the parameters `ς ∘ pr₁`, `ς' ∘ pr₂`
of `C ×_K C` at `p`. -/
@[faltings "lem_bvr_admissible_pair_compare"]
public theorem IsAdmissiblePair.bombieriVojta {K : Type u} [Field K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve K (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))]
    [IrreducibleSpace ↥(pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)))]
    {S : Scheme.{u}} {n m : ℕ}
    (ψ : pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ⟶
      pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) ⟶ projectiveSpaceOver m S)
    (δ₁ δ₂ d : ℤ) {s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)} (hs : s ≠ 0)
    {p : Spec (.of K) ⟶ pullback (C ↘ Spec (.of K)) (C ↘ Spec (.of K))}
    [p.IsOver (Spec (.of K))] {i : ℕ × ℕ}
    (h : IsAdmissiblePair (vojtaLineBundle ψ φ δ₁ δ₂ d) s p i)
    (ς : C.presheaf.stalk
      (pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (ς' : C.presheaf.stalk
      (pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K)) (p (closedPoint K))))
    (hς : maximalIdeal _ = Ideal.span {ς}) (hς' : maximalIdeal _ = Ideal.span {ς'}) :
    BombieriVojta.IsAdmissiblePair ψ φ δ₁ δ₂ d s p
      ((pullback.fst (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς)
      ((pullback.snd (C ↘ Spec (.of K)) (C ↘ Spec (.of K))).stalkMap _ ς') i.1 i.2 :=
  bombieriVojta_of_forall ψ φ δ₁ δ₂ d s p i _ _ fun U hxU e he σ hσ =>
    h.taylorCoeff₂ ς ς' hς hς' U hxU e he σ hσ

end Faltings.BombieriRoth
