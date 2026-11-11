module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.TripleFunction.AdmissiblePair
public import Mordell.BombieriVojta.TripleFunction.AffineFunctions
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Taylor.Leibniz
public import Mordell.BombieriVojta.TripleFunction.Formula
public import Mordell.BombieriVojta.TripleFunction.Generator
public import Mordell.BombieriVojta.TripleFunction.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.AssociatedGradedPolynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkSections
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# The value of the first non-vanishing Taylor coefficient of `G_{ijj'}`

In Section 6 of Bombieri's proof of the Mordell conjecture, `s` is a global section of `𝒪(V)` on
`C × C` with a representative `F = (F_i)`, `(z, w)` is a `K`-rational point and `ς, ς'` are local
parameters at `z, w`. For two triples `(i°, j°, j'°)` and `(i, j, j')` that are non-vanishing at
`(z, w)`, the functions `G° = G_{i°j°j'°}` and `G = G_{ijj'} = F_i(ξ_j, ξ'_{j'})` differ by the
unit `u = (x_j / x_{j°})^{δ₁} (x'_{j'} / x'_{j'°})^{δ₂} (y_{i°} / y_i)^d`. If the Taylor
coefficients `∂_{i₁} ∂'_{i₂} G°(z, w)` vanish for all `(i₁, i₂) ≤ (i₁*, i₂*)` other than
`(i₁*, i₂*)`, Leibniz's rule shows that
`∂_{i₁*} ∂'_{i₂*} G°(z, w) = u(z, w) · ∂_{i₁*} ∂'_{i₂*} F_i(ξ_j, ξ'_{j'})(0, 0)`, where
`u(z, w)` is computed from any representatives `x, x', y` of `φ_{NP}(z), φ_{NP}(w), φ_B(z, w)`.

## Main results

* `Faltings.BombieriVojta.taylorCoeff₂_eq_mul_taylorCoeff₂_eval₂`: the formula above.

## Implementation notes

* As for `Faltings.BombieriVojta.IsAdmissiblePair`, `C × C` is a scheme `X` over a base `S`,
  with `ψ : X ⟶ ℙⁿ_S ×_S ℙⁿ_S` and `φ : X ⟶ ℙᵐ_S`, which is moreover a scheme over `Spec K`, and
  `(z, w)` is a `K`-point `p : Spec K ⟶ X` over `Spec K`. That `ς, ς'` are local uniformizing
  parameters at `z, w` is the hypothesis that the local ring at `p` is regular of dimension `2`
  with maximal ideal `(ς, ς')`, as in `Faltings.BombieriVojta.taylorCoeff₂_prod`.
* `∂_{i₁} ∂'_{i₂} G°(z, w)` is the Taylor coefficient `Faltings.BombieriVojta.taylorCoeff₂` of an
  element `g°` of the local ring at `p` whose image in the function field is `G°`, as in
  `Faltings.BombieriVojta.IsAdmissiblePair`.
* `ξ_{νj}` is the germ at `p` of the function `T_ν / T_j` on the standard chart `D₊(T_j)` of the
  integral model (`AlgebraicGeometry.Proj.awayToSection`), pulled back along `ψ ≫ pr₁`; `ξ'_{νj'}`
  is the same along `ψ ≫ pr₂`, and `η_{νi}` along `φ`. The form `F_i(ξ_j, ξ'_{j'})` is
  `MvPolynomial.eval₂` of `F_i` along the structure map `Γ(S, 𝒪_S) → 𝒪_{X,p}`, as in
  `Faltings.BombieriVojta.tripleFunction_eq_eval₂`.
* A representative of the `K`-point `q` of `ℙʳ` is a nonzero vector `v ∈ Kʳ⁺¹` with
  `v_ν = v_k · (T_ν / T_k)(q)` for every chart `D₊(T_k)` containing `q`; the value at `p` of an
  element of the local ring is its image under `𝒪_{X,p} → 𝒪_{Spec K} = K`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 6, p. 625
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace Faltings.BombieriVojta

universe u

open TripleGenerator

/-- An element `l` of the antidiagonal of `a` in `Fin 2 →₀ ℕ` satisfies `l 0 + l 1 = a`. -/
public theorem antidiag_add {a : ℕ} {l : Fin 2 →₀ ℕ}
    (hl : l ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag a) : l 0 + l 1 = a := by
  rw [Finset.mem_finsuppAntidiag, Fin.sum_univ_two] at hl
  exact hl.1

section Taylor

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
  [IsRegularLocalRing (X.presheaf.stalk (p (closedPoint K)))]
  (hdim : ringKrullDim (X.presheaf.stalk (p (closedPoint K))) = 2)
  {ϖ ϖ' : X.presheaf.stalk (p (closedPoint K))}
  (hϖ : maximalIdeal (X.presheaf.stalk (p (closedPoint K))) = Ideal.span {ϖ, ϖ'})

include hdim hϖ

omit [IsRegularLocalRing (X.presheaf.stalk (p (closedPoint K)))] hdim in
/-- The constant Taylor coefficient `∂₀ ∂'₀ f(p)` is the value `f(p)`. -/
public theorem taylorCoeff₂_zero_zero (f : X.presheaf.stalk (p (closedPoint K))) :
    taylorCoeff₂ p ϖ ϖ' f 0 0 = (Scheme.stalkClosedPointTo p).hom f := by
  let c : K →+* X.presheaf.stalk (p (closedPoint K)) := const _
  let ev : X.presheaf.stalk (p (closedPoint K)) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hev : ∀ k, ev (c k) = k := ev_const p (comp_over_eq_id p)
  have key : taylorCoeff₂ p ϖ ϖ' f 0 0 =
      MvPowerSeries.coeff (bidegree (0, 0)) (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F f) :=
    rfl
  have hspec : IsExpansion₂ c ϖ ϖ' (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F f) f :=
    Classical.epsilon_spec (exists_isExpansion₂ hϖ c ev hev f)
  have h1 := hspec 1
  simp only [Finset.range_one, Finset.singleton_product_singleton, Finset.sum_singleton,
    pow_zero, mul_one, pow_one] at h1
  rw [← hϖ] at h1
  have h0 : ev (f - c (MvPowerSeries.coeff (bidegree (0, 0))
      (Classical.epsilon fun F ↦ IsExpansion₂ c ϖ ϖ' F f))) = 0 := by
    by_contra h
    exact (mem_maximalIdeal _).1 h1 (isUnit_of_map_unit ev _ (isUnit_iff_ne_zero.2 h))
  rw [map_sub, hev, sub_eq_zero] at h0
  exact key.trans h0.symm

/-- Leibniz's rule for two factors, in the form given by `taylorCoeff₂_prod`. -/
public theorem taylorCoeff₂_mul (f g : X.presheaf.stalk (p (closedPoint K))) (a b : ℕ) :
    taylorCoeff₂ p ϖ ϖ' (f * g) a b =
      ∑ l ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag a,
        ∑ m ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag b,
          taylorCoeff₂ p ϖ ϖ' f (l 0) (m 0) * taylorCoeff₂ p ϖ ϖ' g (l 1) (m 1) := by
  have h := taylorCoeff₂_prod p hdim hϖ Finset.univ ![f, g] a b
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- If all Taylor coefficients of `u * G` below `(a, b)` vanish and `u` is a unit, the coefficient
of `u * G` at `(a, b)` is `u(p)` times that of `G`. -/
public theorem taylorCoeff₂_mul_of_vanish {u G : X.presheaf.stalk (p (closedPoint K))}
    (hu : IsUnit u) (a b : ℕ)
    (hvanish : ∀ i₁ ≤ a, ∀ i₂ ≤ b, (i₁, i₂) ≠ (a, b) →
      taylorCoeff₂ p ϖ ϖ' (u * G) i₁ i₂ = 0) :
    taylorCoeff₂ p ϖ ϖ' (u * G) a b =
      (Scheme.stalkClosedPointTo p).hom u * taylorCoeff₂ p ϖ ϖ' G a b := by
  classical
  have hG : ∀ a' ≤ a, ∀ b' ≤ b, (a', b') ≠ (a, b) → taylorCoeff₂ p ϖ ϖ' G a' b' = 0 := by
    intro a' ha' b' hb' hne
    obtain ⟨v, hv⟩ := hu
    have hGu : G = ↑v⁻¹ * (u * G) := by
      rw [← mul_assoc, ← hv, Units.inv_mul, one_mul]
    rw [hGu, taylorCoeff₂_mul p hdim hϖ]
    refine Finset.sum_eq_zero fun l hl => Finset.sum_eq_zero fun m hm => ?_
    have h1 := antidiag_add hl
    have h2 := antidiag_add hm
    rw [hvanish (l 1) (by omega) (m 1) (by omega) (fun h => hne (by
      simp only [Prod.mk.injEq] at h ⊢; omega)), mul_zero]
  have hsa : Finsupp.single 1 a ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag a := by
    simp [Finset.mem_finsuppAntidiag]
  have hsb : Finsupp.single 1 b ∈ (Finset.univ : Finset (Fin 2)).finsuppAntidiag b := by
    simp [Finset.mem_finsuppAntidiag]
  have hext : ∀ {c : ℕ} {l : Fin 2 →₀ ℕ}, l 0 + l 1 = c → l ≠ Finsupp.single 1 c → l 1 < c := by
    intro c l hl hne
    by_contra hlt
    apply hne
    ext i
    fin_cases i <;> simp <;> omega
  rw [taylorCoeff₂_mul p hdim hϖ, Finset.sum_eq_single_of_mem _ hsa,
    Finset.sum_eq_single_of_mem _ hsb]
  · simp [taylorCoeff₂_zero_zero p hϖ]
  · intro m hm hne
    have := hext (antidiag_add hm) hne
    rw [hG _ (by simp) _ (by omega) (by simp; omega), mul_zero]
  · intro l hl hne
    have := hext (antidiag_add hl) hne
    refine Finset.sum_eq_zero fun m hm => ?_
    have := antidiag_add hm
    rw [hG _ (by omega) _ (by omega) (by simp only [ne_eq, Prod.mk.injEq]; omega), mul_zero]

end Taylor

section Injective

/-- At a point of an irreducible scheme whose local ring is a domain, the map from the local ring
to the function field is injective. -/
public theorem algebraMap_stalk_functionField_injective {X : Scheme.{u}} [IrreducibleSpace X]
    (x : X) [IsDomain (X.presheaf.stalk x)] :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨U, hxU, t, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxU
  have hV' : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  set t' := X.presheaf.map (homOfLE hVU).op t with ht'
  have hgerm : X.presheaf.germ U x hxU t = X.presheaf.germ V x hxV t' := by
    rw [ht', X.presheaf.germ_res_apply]
  rw [hgerm] at hr ⊢
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at hr
  have hη : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using ⟨x, hxV⟩)
  have hr' :
      X.presheaf.germ V (genericPoint X) hη t' = X.presheaf.germ V (genericPoint X) hη 0 := by
    rwa [map_zero]
  obtain ⟨W, hηW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hη hη t' 0 hr'
  rw [map_zero] at hW
  obtain ⟨f, hfW, hηf⟩ := hV'.exists_basicOpen_le (V := W) ⟨genericPoint X, hηW⟩ hη
  have hres : X.presheaf.map (homOfLE (X.basicOpen_le f)).op t' = 0 := by
    have : homOfLE (X.basicOpen_le f) = homOfLE hfW ≫ iU := rfl
    rw [this, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hW, map_zero]
  obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X hV' t' f hres
  have hk' := congrArg (X.presheaf.germ V x hxV) hk
  rw [map_mul, map_pow, map_zero] at hk'
  rcases mul_eq_zero.1 hk' with h | h
  · exfalso
    have hf0 : X.presheaf.germ V x hxV f = 0 := pow_eq_zero_iff'.1 h |>.1
    have hu : IsUnit (X.presheaf.germ V (genericPoint X) hη f) := (X.mem_basicOpen f _ hη).1 hηf
    have : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV f) =
        X.presheaf.germ V (genericPoint X) hη f :=
      Scheme.algebraMap_germ_eq_germToFunctionField X hxV f
    rw [hf0, map_zero] at this
    rw [← this] at hu
    exact not_isUnit_zero hu
  · exact h

end Injective

section Representatives

variable {K ι : Type*} [Field K] {v : ι → K} {k : ι} {f : ι → K}

/-- If `v = v_k · f` for a nonzero vector `v`, then `v_k ≠ 0`. -/
public lemma ne_zero_of_eq_mul (hv : v ≠ 0) (h : ∀ ν, v ν = v k * f ν) : v k ≠ 0 := by
  intro h0
  exact hv (funext fun ν => by rw [h ν, h0, zero_mul]; rfl)

/-- If `v = v_k · f` for a nonzero vector `v`, then `f_ν = v_ν / v_k`. -/
public lemma eq_div_of_eq_mul (hv : v ≠ 0) (h : ∀ ν, v ν = v k * f ν) (ν : ι) :
    f ν = v ν / v k := by
  rw [h ν, mul_div_cancel_left₀ _ (ne_zero_of_eq_mul hv h)]

end Representatives

section Charts

open MonoidalCategory Opposite

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory MvPolynomial.gradedAlgebra

/-- On an open `W ⊆ D₊(T_k) ∩ D₊(T_l)`, the generator `T_k ^ a` of `𝒪(a)` is `(T_k / T_l) ^ a`
times the generator `T_l ^ a`. -/
private lemma genI_res_eq_smul (r a : ℕ) (k l : Fin (r + 1))
    {W : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens} (hk : W ≤ projChart r k)
    (hl : W ≤ projChart r l) :
    (projTwist.{u} r a).presheaf.map (homOfLE hk).op (genI r a k) =
      ((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hl).op
        (projRatio r l k)) ^ a •
        (projTwist.{u} r a).presheaf.map (homOfLE hl).op (genI r a l) := by
  apply Subtype.ext
  funext x
  change Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r) (a : ℤ)
      (le_refl (projChart.{u} r k)) ⟨x.1, hk x.2⟩ =
    ((((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hl).op
      (projRatio r l k)) ^ a).1 x).val •
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r) (a : ℤ)
      (le_refl (projChart.{u} r l)) ⟨x.1, hl x.2⟩
  have hev : ((((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hl).op
      (projRatio r l k)) ^ a).1 x).val =
      (Localization.mk (MvPolynomial.X k) ⟨MvPolynomial.X l, hl x.2⟩ :
        Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) ^ a := by
    change (((projRatio r l k).1 ⟨x.1, hl x.2⟩) ^ a).val = _
    rw [HomogeneousLocalization.val_pow]
    exact congrArg (· ^ a) (val_projRatio r l k ⟨x.1, hl x.2⟩)
  rw [hev]
  simp only [Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun, Int.toNat_natCast,
    Int.toNat_neg_natCast, pow_zero]
  rw [smul_eq_mul, Localization.mk_pow, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp; ring))

/-- On an open `W ⊆ D₊(T_k) ∩ D₊(T_l)`, the generator `T_k ^ (-a)` of `𝒪(-a)` is `(T_l / T_k) ^ a`
times the generator `T_l ^ (-a)`. -/
private lemma genI_neg_res_eq_smul (r a : ℕ) (k l : Fin (r + 1))
    {W : (AlgebraicGeometry.Proj (projGrading.{u} r)).Opens} (hk : W ≤ projChart r k)
    (hl : W ≤ projChart r l) :
    (projTwist.{u} r (-(a : ℤ))).presheaf.map (homOfLE hk).op (genI r (-(a : ℤ)) k) =
      ((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hk).op
        (projRatio r k l)) ^ a •
        (projTwist.{u} r (-(a : ℤ))).presheaf.map (homOfLE hl).op (genI r (-(a : ℤ)) l) := by
  apply Subtype.ext
  funext x
  change Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r) (-(a : ℤ))
      (le_refl (projChart.{u} r k)) ⟨x.1, hk x.2⟩ =
    ((((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hk).op
      (projRatio r k l)) ^ a).1 x).val •
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (projGrading.{u} r) (-(a : ℤ))
      (le_refl (projChart.{u} r l)) ⟨x.1, hl x.2⟩
  have hev : ((((AlgebraicGeometry.Proj (projGrading.{u} r)).presheaf.map (homOfLE hk).op
      (projRatio r k l)) ^ a).1 x).val =
      (Localization.mk (MvPolynomial.X l) ⟨MvPolynomial.X k, hk x.2⟩ :
        Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) ^ a := by
    change (((projRatio r k l).1 ⟨x.1, hk x.2⟩) ^ a).val = _
    rw [HomogeneousLocalization.val_pow]
    exact congrArg (· ^ a) (val_projRatio r k l ⟨x.1, hk x.2⟩)
  rw [hev]
  simp only [Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun, Int.toNat_natCast,
    Int.toNat_neg_natCast, neg_neg, pow_zero]
  rw [smul_eq_mul, Localization.mk_pow, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

section Setting

variable {S X : Scheme.{u}} {n m : ℕ}
  (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
  (φ : X ⟶ projectiveSpaceOver m S)

/-- Restricting a section of `𝒪_Y` from `T` to `T'` and then to `T''` is restricting it from `T`
to `T''`. -/
public lemma sres_sres {Y : Scheme.{u}} {T T' T'' : Y.Opens} (h : T' ≤ T) (h' : T'' ≤ T')
    (t : Γ(Y, T)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op t) =
      Y.presheaf.map (homOfLE (h'.trans h)).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A relation `t_A = c • t_B` on `A ⊓ B` between sections of `M` pulls back along `g`. -/
private lemma res_pb_eq_smul {Z Y : Scheme.{u}} (g : Z ⟶ Y) {M : Y.Modules} {A B C : Y.Opens}
    (tA : Γ(M, A)) (tB : Γ(M, B)) (c : Γ(Y, C)) (hC : A ⊓ B ≤ C)
    (h : M.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op tA =
      Y.presheaf.map (homOfLE hC).op c •
        M.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op tB)
    {V : Z.Opens} (hA : V ≤ g ⁻¹ᵁ A) (hB : V ≤ g ⁻¹ᵁ B) (hCV : V ≤ g ⁻¹ᵁ C) :
    ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hA).op (pullbackUnitApp g tA) =
      Z.presheaf.map (homOfLE hCV).op (g.app C c) •
        ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hB).op
          (pullbackUnitApp g tB) := by
  have hV : V ≤ g ⁻¹ᵁ (A ⊓ B) := le_inf hA hB
  have e1 : ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hA).op
      (pullbackUnitApp g tA) =
      ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hV).op
        (pullbackUnitApp g (M.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op tA)) := by
    rw [← pullbackUnitApp_res, res_res']
  have e2 : ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hB).op
      (pullbackUnitApp g tB) =
      ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hV).op
        (pullbackUnitApp g (M.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op tB)) := by
    rw [← pullbackUnitApp_res, res_res']
  have e3 : Z.presheaf.map (homOfLE hCV).op (g.app C c) =
      Z.presheaf.map (homOfLE hV).op (g.app (A ⊓ B) (Y.presheaf.map (homOfLE hC).op c)) := by
    rw [app_resO, sres_sres]
  rw [e1, e2, e3, h, pullbackUnitApp_smul, res_smul']

/-- On `V ⊆ f⁻¹ D₊(T_k) ∩ f⁻¹ D₊(T_l)`, the pulled-back generator `T_k ^ a` of `𝒪(a)` is
`(T_k / T_l) ^ a` times the pulled-back generator `T_l ^ a`. -/
private lemma res_pb_gen_eq_smul {Z : Scheme.{u}} {r : ℕ} (f : Z ⟶ projectiveSpaceOver r S)
    (a : ℕ) (k l : Fin (r + 1)) {V : Z.Opens} (hk : V ≤ f ⁻¹ᵁ chart S r k)
    (hl : V ≤ f ⁻¹ᵁ chart S r l) :
    ((Scheme.Modules.pullback f).obj (twist S r a)).presheaf.map (homOfLE hk).op
        (pullbackUnitApp f (gen S r a k)) =
      Z.presheaf.map (homOfLE hl).op (f.app _ ((toI S r).app _ (projRatio r l k ^ a))) •
        ((Scheme.Modules.pullback f).obj (twist S r a)).presheaf.map (homOfLE hl).op
          (pullbackUnitApp f (gen S r a l)) :=
  res_pb_eq_smul f (A := chart S r k) (B := chart S r l) (C := chart S r l) (gen S r a k)
    (gen S r a l) _ inf_le_right
    (res_pb_eq_smul (toI S r) (A := projChart r k) (B := projChart r l) (C := projChart r l)
      (genI r a k) (genI r a l) (projRatio r l k ^ a) inf_le_right
      (by rw [map_pow]; exact genI_res_eq_smul r a k l inf_le_left inf_le_right)
      inf_le_left inf_le_right inf_le_right) hk hl hl

/-- On `V ⊆ f⁻¹ D₊(T_k) ∩ f⁻¹ D₊(T_l)`, the pulled-back generator `T_k ^ (-a)` of `𝒪(-a)` is
`(T_l / T_k) ^ a` times the pulled-back generator `T_l ^ (-a)`. -/
private lemma res_pb_gen_neg_eq_smul {Z : Scheme.{u}} {r : ℕ} (f : Z ⟶ projectiveSpaceOver r S)
    (a : ℕ) (k l : Fin (r + 1)) {V : Z.Opens} (hk : V ≤ f ⁻¹ᵁ chart S r k)
    (hl : V ≤ f ⁻¹ᵁ chart S r l) :
    ((Scheme.Modules.pullback f).obj (twist S r (-(a : ℤ)))).presheaf.map (homOfLE hk).op
        (pullbackUnitApp f (gen S r (-(a : ℤ)) k)) =
      Z.presheaf.map (homOfLE hk).op (f.app _ ((toI S r).app _ (projRatio r k l ^ a))) •
        ((Scheme.Modules.pullback f).obj (twist S r (-(a : ℤ)))).presheaf.map (homOfLE hl).op
          (pullbackUnitApp f (gen S r (-(a : ℤ)) l)) :=
  res_pb_eq_smul f (A := chart S r k) (B := chart S r l) (C := chart S r k)
    (gen S r (-(a : ℤ)) k) (gen S r (-(a : ℤ)) l) _ inf_le_left
    (res_pb_eq_smul (toI S r) (A := projChart r k) (B := projChart r l) (C := projChart r k)
      (genI r (-(a : ℤ)) k) (genI r (-(a : ℤ)) l) (projRatio r k l ^ a) inf_le_left
      (by rw [map_pow]; exact genI_neg_res_eq_smul r a k l inf_le_left inf_le_right)
      inf_le_left inf_le_right inf_le_left) hk hl hk

/-- The function `(x_j / x_{j₀})^{δ₁} (x'_{j'} / x'_{j'₀})^{δ₂}` on
`chartW j j' ⊓ chartW j₀ j'₀`. -/
private noncomputable abbrev coefW (S : Scheme.{u}) (n δ₁ δ₂ : ℕ) (j j' j₀ j'₀ : Fin (n + 1)) :
    Γ(pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S),
      chartW S n j j' ⊓ chartW S n j₀ j'₀) :=
  (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
      (homOfLE (fun _ h => h.2.1 : chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤
        pr₁ S n ⁻¹ᵁ chart S n j₀)).op
      ((pr₁ S n).app _ ((toI S n).app _ (projRatio n j₀ j ^ δ₁))) *
    (pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)).presheaf.map
      (homOfLE (fun _ h => h.2.2 : chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤
        pr₂ S n ⁻¹ᵁ chart S n j'₀)).op
      ((pr₂ S n).app _ ((toI S n).app _ (projRatio n j'₀ j' ^ δ₂)))

open Stacks.SectionTensorFormula in
/-- On `chartW j j' ⊓ chartW j₀ j'₀`, the generator `x_j^{δ₁} x'_{j'}^{δ₂}` is
`(x_j / x_{j₀})^{δ₁} (x'_{j'} / x'_{j'₀})^{δ₂}` times `x_{j₀}^{δ₁} x'_{j'₀}^{δ₂}`. -/
private lemma genW_res_eq_smul (δ₁ δ₂ : ℕ) (j j' j₀ j'₀ : Fin (n + 1)) :
    (twist₂ S n δ₁ δ₂).presheaf.map
        (homOfLE (inf_le_left : chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤ _)).op
        (genW S n δ₁ δ₂ j j') =
      coefW S n δ₁ δ₂ j j' j₀ j'₀ •
        (twist₂ S n δ₁ δ₂).presheaf.map
          (homOfLE (inf_le_right : chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤ _)).op
          (genW S n δ₁ δ₂ j₀ j'₀) := by
  simp only [genW, res]
  rw [map_tensorSection, map_tensorSection, res_res', res_res', res_res', res_res',
    res_pb_gen_eq_smul (pr₁ S n) δ₁ j j₀ _ (fun _ h => h.2.1 :
      chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤ pr₁ S n ⁻¹ᵁ chart S n j₀),
    res_pb_gen_eq_smul (pr₂ S n) δ₂ j' j'₀ _ (fun _ h => h.2.2 :
      chartW S n j j' ⊓ chartW S n j₀ j'₀ ≤ pr₂ S n ⁻¹ᵁ chart S n j'₀)]
  rw [tensorSection_smul_left, tensorSection_smul_right, smul_smul, coefW, mul_comm]

/-- Restricting a section of `𝒪_Y` from `T` to itself is the identity. -/
public lemma sres_id {Y : Scheme.{u}} {T : Y.Opens} (t : Γ(Y, T)) :
    Y.presheaf.map (homOfLE (le_refl T)).op t = t := by
  rw [show homOfLE (le_refl T) = 𝟙 T from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The unit `(x_j / x_{j₀})^{δ₁} (x'_{j'} / x'_{j'₀})^{δ₂} (y_{i₀} / y_i)^d`, which is
`e_{ijj'} / e_{i₀j₀j'₀}` on `U_{ijj'} ⊓ U_{i₀j₀j'₀}`. -/
private noncomputable abbrev ratioU (δ₁ δ₂ d : ℕ) (i i₀ : Fin (m + 1)) (j j' j₀ j'₀ : Fin (n + 1)) :
    Γ(X, chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀) :=
  X.presheaf.map (homOfLE (fun _ h => ⟨h.1.1, h.2.1⟩ :
      chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤
        ψ ⁻¹ᵁ (chartW S n j j' ⊓ chartW S n j₀ j'₀))).op
      (ψ.app _ (coefW S n δ₁ δ₂ j j' j₀ j'₀)) *
    X.presheaf.map (homOfLE (fun _ h => h.1.2 :
      chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ φ ⁻¹ᵁ chart S m i)).op
      (φ.app _ ((toI S m).app _ (projRatio m i i₀ ^ d)))

open Stacks.SectionTensorFormula in
/-- On `U_{ijj'} ⊓ U_{i₀j₀j'₀}`, the section `e_{ijj'}` is
`(x_j / x_{j₀})^{δ₁} (x'_{j'} / x'_{j'₀})^{δ₂} (y_{i₀} / y_i)^d` times `e_{i₀j₀j'₀}`. -/
private lemma genU_res_eq_smul (δ₁ δ₂ d : ℕ) (i i₀ : Fin (m + 1)) (j j' j₀ j'₀ : Fin (n + 1)) :
    ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
        (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))).presheaf.map
        (homOfLE (inf_le_left : chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ _)).op
        (genU ψ φ δ₁ δ₂ (-(d : ℤ)) i j j') =
      ratioU ψ φ δ₁ δ₂ d i i₀ j j' j₀ j'₀ •
        ((Scheme.Modules.pullback ψ).obj (twist₂ S n δ₁ δ₂) ⊗
          (Scheme.Modules.pullback φ).obj (twist S m (-(d : ℤ)))).presheaf.map
          (homOfLE (inf_le_right : chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ _)).op
          (genU ψ φ δ₁ δ₂ (-(d : ℤ)) i₀ j₀ j'₀) := by
  simp only [genU, res]
  rw [map_tensorSection, map_tensorSection, res_res', res_res', res_res', res_res']
  rw [res_pb_eq_smul ψ (A := chartW S n j j') (B := chartW S n j₀ j'₀)
    (C := chartW S n j j' ⊓ chartW S n j₀ j'₀) (V := chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀)
    (genW S n δ₁ δ₂ j j') (genW S n δ₁ δ₂ j₀ j'₀)
    (coefW S n δ₁ δ₂ j j' j₀ j'₀) le_rfl
    (by rw [sres_id]; exact genW_res_eq_smul δ₁ δ₂ j j' j₀ j'₀) (fun _ h => h.1.1)
    (fun _ h => h.2.1) (fun _ h => ⟨h.1.1, h.2.1⟩ : chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤
      ψ ⁻¹ᵁ (chartW S n j j' ⊓ chartW S n j₀ j'₀))]
  rw [res_pb_gen_neg_eq_smul φ d i i₀ _ (fun _ h => h.2.2 :
    chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ φ ⁻¹ᵁ chart S m i₀)]
  rw [tensorSection_smul_left, tensorSection_smul_right, smul_smul]

/-- `G_{i₀j₀j'₀} = G_{ijj'} · e_{ijj'} / e_{i₀j₀j'₀}` in the function field. -/
private lemma tripleFunction_eq_mul_ratioU (δ₁ δ₂ d : ℕ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤)) (x : X) (i i₀ : Fin (m + 1))
    (j j' j₀ j'₀ : Fin (n + 1))
    (hx : x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j')))
    (hx₀ : x ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i₀)) ∧
        x ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j₀)) ∧
        x ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j'₀))) :
    haveI : Nonempty ((chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ : X.Opens)) :=
      ⟨⟨x, ⟨⟨hx.2.1, hx.2.2⟩, hx.1⟩, ⟨⟨hx₀.2.1, hx₀.2.2⟩, hx₀.1⟩⟩⟩
    tripleFunction ψ φ δ₁ δ₂ d s x i₀ j₀ j'₀ hx₀ =
      tripleFunction ψ φ δ₁ δ₂ d s x i j j' hx *
        X.germToFunctionField _ (ratioU ψ φ δ₁ δ₂ d i i₀ j j' j₀ j'₀) := by
  have : Nonempty (chartU ψ φ i j j') := ⟨⟨x, ⟨hx.2.1, hx.2.2⟩, hx.1⟩⟩
  have : Nonempty (chartU ψ φ i₀ j₀ j'₀) := ⟨⟨x, ⟨hx₀.2.1, hx₀.2.2⟩, hx₀.1⟩⟩
  have : Nonempty ((chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ : X.Opens)) :=
    ⟨⟨x, ⟨⟨hx.2.1, hx.2.2⟩, hx.1⟩, ⟨⟨hx₀.2.1, hx₀.2.2⟩, hx₀.1⟩⟩⟩
  rw [tripleFunction_eq ψ φ δ₁ δ₂ d s x i₀ j₀ j'₀ hx₀, tripleFunction_eq ψ φ δ₁ δ₂ d s x i j j' hx]
  set e := genU ψ φ δ₁ δ₂ (-(d : ℤ)) i j j' with he
  set e₀ := genU ψ φ δ₁ δ₂ (-(d : ℤ)) i₀ j₀ j'₀ with he₀
  set h := Function.invFun (fun g : Γ(X, chartU ψ φ i j j') => g • e) (res _ le_top s) with hh
  set h₀ := Function.invFun (fun g : Γ(X, chartU ψ φ i₀ j₀ j'₀) => g • e₀) (res _ le_top s)
    with hh₀
  have hs : h • e = res _ le_top s :=
    Function.invFun_eq ((isGen_genU ψ φ δ₁ δ₂ _ i j j').bijective.2 _)
  have hs₀ : h₀ • e₀ = res _ le_top s :=
    Function.invFun_eq ((isGen_genU ψ φ δ₁ δ₂ _ i₀ j₀ j'₀).bijective.2 _)
  have key : X.presheaf.map (homOfLE (inf_le_right :
        chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ _)).op h₀ =
      X.presheaf.map (homOfLE (inf_le_left :
        chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ _)).op h *
        ratioU ψ φ δ₁ δ₂ d i i₀ j j' j₀ j'₀ := by
    apply ((isGen_genU ψ φ δ₁ δ₂ (-(d : ℤ)) i₀ j₀ j'₀).restrict inf_le_right).bijective.1
    simp only
    rw [← res_smul', hs₀, mul_smul, ← genU_res_eq_smul, ← res_smul', hs]
    exact (res_res' _ _ _ s).trans (res_res' _ _ _ s).symm
  have e₁ : X.germToFunctionField _ (X.presheaf.map (homOfLE (inf_le_right :
        chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ ≤ _)).op h₀) =
      X.germToFunctionField _ h₀ :=
    germToFunctionField_resO _ _
  rw [← e₁, key, map_mul, germToFunctionField_resO]

/-- The germ of `e_{ijj'} / e_{i₀j₀j'₀}` at a point of `U_{ijj'} ⊓ U_{i₀j₀j'₀}`. -/
private lemma germ_ratioU (δ₁ δ₂ d : ℕ) (i i₀ : Fin (m + 1)) (j j' j₀ j'₀ : Fin (n + 1)) (x : X)
    (hxV : x ∈ chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀) :
    X.presheaf.germ _ x hxV (ratioU ψ φ δ₁ δ₂ d i i₀ j j' j₀ j'₀) =
      X.presheaf.germ ((ψ ≫ pr₁ S n) ⁻¹ᵁ chart S n j₀) x hxV.2.1.1
          ((ψ ≫ pr₁ S n).app _ ((toI S n).app _ (projRatio n j₀ j))) ^ δ₁ *
        X.presheaf.germ ((ψ ≫ pr₂ S n) ⁻¹ᵁ chart S n j'₀) x hxV.2.1.2
          ((ψ ≫ pr₂ S n).app _ ((toI S n).app _ (projRatio n j'₀ j'))) ^ δ₂ *
        X.presheaf.germ (φ ⁻¹ᵁ chart S m i) x hxV.1.2
          (φ.app _ ((toI S m).app _ (projRatio m i i₀))) ^ d := by
  simp only [ratioU, coefW, map_mul, map_pow, X.presheaf.germ_res_apply, app_resO,
    Scheme.Hom.comp_app]
  rfl

end Setting

end Charts

/-- **Value of the first non-vanishing Taylor coefficient.** Let `F` be a representative of the
global section `s` of `vojtaLineBundle ψ φ δ₁ δ₂ d`, let `p` be a `K`-point of `X` whose local
ring is regular of dimension two with maximal ideal `(ς, ς')`, and let `(i°, j°, j'°)` and
`(i, j, j')` be triples non-vanishing at `p`. Let `g°` be the germ at `p` of
`G° = tripleFunction ψ φ δ₁ δ₂ d s _ i° j° j'° _`, and let `x, x', y` be representatives of the
images of `p` in `ℙⁿ`, `ℙⁿ`, `ℙᵐ` under `ψ ≫ pr₁`, `ψ ≫ pr₂`, `φ`. If
`∂_{i₁} ∂'_{i₂} g°(p) = 0` for all `i₁ ≤ i₁*`, `i₂ ≤ i₂*` with `(i₁, i₂) ≠ (i₁*, i₂*)`, then
`∂_{i₁*} ∂'_{i₂*} g°(p) = (y_{i°} / y_i)^d (x_j / x_{j°})^{δ₁} (x'_{j'} / x'_{j'°})^{δ₂} ·
∂_{i₁*} ∂'_{i₂*} F_i(ξ_j, ξ'_{j'})(p)`. -/
@[faltings "lem_bv_admissible_value_formula"]
public theorem taylorCoeff₂_eq_mul_taylorCoeff₂_eval₂ {S X : Scheme.{u}} {n m : ℕ}
    (ψ : X ⟶ pullback (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S))
    (φ : X ⟶ projectiveSpaceOver m S) (δ₁ δ₂ d : ℕ) [IrreducibleSpace X]
    (s : Γ(vojtaLineBundle ψ φ δ₁ δ₂ d, ⊤))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1) ⊕ Fin (n + 1)) Γ(S, ⊤))
    (hF : IsVojtaRepresentative ψ φ δ₁ δ₂ d s F)
    {K : Type u} [Field K] [X.Over (Spec (.of K))]
    (p : Spec (.of K) ⟶ X) [p.IsOver (Spec (.of K))]
    [IsRegularLocalRing (X.presheaf.stalk (p (closedPoint K)))]
    (hdim : ringKrullDim (X.presheaf.stalk (p (closedPoint K))) = 2)
    {ς ς' : X.presheaf.stalk (p (closedPoint K))}
    (hς : maximalIdeal (X.presheaf.stalk (p (closedPoint K))) = Ideal.span {ς, ς'})
    (i₀ i : Fin (m + 1)) (j₀ j'₀ j j' : Fin (n + 1))
    (hx₀ : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      p (closedPoint K) ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i₀)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j₀)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j'₀)))
    (hx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      p (closedPoint K) ∈ φ ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse m S ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X i)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.fst _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j)) ∧
        p (closedPoint K) ∈ (ψ ≫ pullback.snd _ _) ⁻¹ᵁ
          (projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
            Proj.basicOpen _ (MvPolynomial.X j')))
    (g₀ : X.presheaf.stalk (p (closedPoint K)))
    (hg₀ : algebraMap _ X.functionField g₀ =
      tripleFunction ψ φ δ₁ δ₂ d s (p (closedPoint K)) i₀ j₀ j'₀ hx₀)
    (i₁' i₂' : ℕ)
    (hvanish : ∀ i₁ ≤ i₁', ∀ i₂ ≤ i₂', (i₁, i₂) ≠ (i₁', i₂') →
      taylorCoeff₂ p ς ς' g₀ i₁ i₂ = 0)
    (x x' : Fin (n + 1) → K) (y : Fin (m + 1) → K) :
    letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
      fun _ => MvPolynomial.gradedAlgebra
    -- `D₊(T_k)` on the integral model of `ℙʳ`
    let D : (r : ℕ) → Fin (r + 1) → (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))).Opens := fun r k =>
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X k)
    -- the function `T_ν / T_k` on `D₊(T_k)`
    let ratio : (r : ℕ) → (k : Fin (r + 1)) → Fin (r + 1) →
        Γ(AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)), D r k) :=
      fun r k ν => Proj.awayToSection _ (MvPolynomial.X k)
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X _ k) 1 (MvPolynomial.X ν)
          (by simpa using MvPolynomial.isHomogeneous_X _ ν))
    let g : (r : ℕ) → projectiveSpaceOver r S ⟶ _ := fun r =>
      projectiveSpaceOver.toIntegralAtUniverse r S
    -- the germ at `p` of `(T_ν / T_k) ∘ f`, for `p` in the chart `f⁻¹ D₊(T_k)`
    let coord : (r : ℕ) → (f : X ⟶ projectiveSpaceOver r S) → (k : Fin (r + 1)) →
        p (closedPoint K) ∈ f ⁻¹ᵁ (g r ⁻¹ᵁ D r k) → Fin (r + 1) →
        X.presheaf.stalk (p (closedPoint K)) := fun r f k hk ν =>
      X.presheaf.germ _ _ hk (f.app _ ((g r).app _ (ratio r k ν)))
    -- the value at `p` of an element of the local ring
    let ev : X.presheaf.stalk (p (closedPoint K)) →+* K :=
      (p.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (.of K)).hom).hom
    -- `v` is a representative of the image of `p` under `f : X ⟶ ℙʳ_S`
    let IsRep : (r : ℕ) → (X ⟶ projectiveSpaceOver r S) → (Fin (r + 1) → K) → Prop :=
      fun r f v => v ≠ 0 ∧ ∀ (k : Fin (r + 1)) (hk : p (closedPoint K) ∈ f ⁻¹ᵁ (g r ⁻¹ᵁ D r k))
        (ν : Fin (r + 1)), v ν = v k * ev (coord r f k hk ν)
    let p₁ := pullback.fst (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    let p₂ := pullback.snd (projectiveSpaceOver n S ↘ S) (projectiveSpaceOver n S ↘ S)
    -- the coefficients act through the structure morphism `X ⟶ S`
    let c : Γ(S, ⊤) →+* X.presheaf.stalk (p (closedPoint K)) :=
      ((ψ ≫ p₁ ≫ (projectiveSpaceOver n S ↘ S)).appTop ≫
        X.presheaf.germ ⊤ (p (closedPoint K)) trivial).hom
    IsRep n (ψ ≫ p₁) x → IsRep n (ψ ≫ p₂) x' → IsRep m φ y →
      taylorCoeff₂ p ς ς' g₀ i₁' i₂' =
        (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j'₀) ^ δ₂ *
          taylorCoeff₂ p ς ς'
            ((F i).eval₂ c (Sum.elim (coord n (ψ ≫ p₁) j hx.2.1)
              (coord n (ψ ≫ p₂) j' hx.2.2))) i₁' i₂' := by
  intro D ratio g coord ev IsRep p₁ p₂ c hxr hx'r hyr
  classical
  have : IsDomain (X.presheaf.stalk (p (closedPoint K))) := IsRegularLocalRing.isDomain _
  have hxV : p (closedPoint K) ∈ chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ :=
    ⟨⟨⟨hx.2.1, hx.2.2⟩, hx.1⟩, ⟨⟨hx₀.2.1, hx₀.2.2⟩, hx₀.1⟩⟩
  have : Nonempty ((chartU ψ φ i j j' ⊓ chartU ψ φ i₀ j₀ j'₀ : X.Opens)) := ⟨⟨_, hxV⟩⟩
  set G := (F i).eval₂ c (Sum.elim (coord n (ψ ≫ p₁) j hx.2.1) (coord n (ψ ≫ p₂) j' hx.2.2))
    with hG
  set w := X.presheaf.germ _ _ hxV (ratioU ψ φ δ₁ δ₂ d i i₀ j j' j₀ j'₀) with hw
  have hev : ev = (Scheme.stalkClosedPointTo p).hom := rfl
  have hGalg : algebraMap _ X.functionField G =
      tripleFunction ψ φ δ₁ δ₂ d s (p (closedPoint K)) i j j' hx := by
    rw [tripleFunction_eq_eval₂ ψ φ δ₁ δ₂ d s F hF _ i j j' hx, hG, MvPolynomial.eval₂_comp_left]
    have : Nonempty (⊤ : X.Opens) := ⟨⟨p (closedPoint K), trivial⟩⟩
    have : Nonempty ((ψ ≫ p₁) ⁻¹ᵁ (g n ⁻¹ᵁ D n j)) := ⟨⟨_, hx.2.1⟩⟩
    have : Nonempty ((ψ ≫ p₂) ⁻¹ᵁ (g n ⁻¹ᵁ D n j')) := ⟨⟨_, hx.2.2⟩⟩
    congr 1
    · exact RingHom.ext fun t => Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤)
        (show p (closedPoint K) ∈ (⊤ : X.Opens) from trivial) _
    · funext ν
      cases ν with
      | inl ν => exact Scheme.algebraMap_germ_eq_germToFunctionField X hx.2.1 _
      | inr ν => exact Scheme.algebraMap_germ_eq_germToFunctionField X hx.2.2 _
  have hg : g₀ = w * G := by
    apply algebraMap_stalk_functionField_injective
    rw [hg₀, map_mul, hGalg, tripleFunction_eq_mul_ratioU ψ φ δ₁ δ₂ d s _ i i₀ j j' j₀ j'₀ hx hx₀,
      mul_comm, hw, Scheme.algebraMap_germ_eq_germToFunctionField]
  have hval : (Scheme.stalkClosedPointTo p).hom w =
      (y i₀ / y i) ^ d * (x j / x j₀) ^ δ₁ * (x' j' / x' j'₀) ^ δ₂ := by
    rw [hw, germ_ratioU, map_mul, map_mul, map_pow, map_pow, map_pow, ← hev]
    change ev (coord n (ψ ≫ p₁) j₀ hx₀.2.1 j) ^ δ₁ * ev (coord n (ψ ≫ p₂) j'₀ hx₀.2.2 j') ^ δ₂ *
      ev (coord m φ i hx.1 i₀) ^ d = _
    rw [← eq_div_of_eq_mul hxr.1 (hxr.2 j₀ hx₀.2.1) j,
      ← eq_div_of_eq_mul hx'r.1 (hx'r.2 j'₀ hx₀.2.2) j',
      ← eq_div_of_eq_mul hyr.1 (hyr.2 i hx.1) i₀]
    ring
  have hunit : IsUnit w := by
    refine isUnit_of_map_unit (Scheme.stalkClosedPointTo p).hom w (isUnit_iff_ne_zero.2 ?_)
    rw [hval]
    simp [ne_zero_of_eq_mul hxr.1 (hxr.2 j₀ hx₀.2.1), ne_zero_of_eq_mul hxr.1 (hxr.2 j hx.2.1),
      ne_zero_of_eq_mul hx'r.1 (hx'r.2 j'₀ hx₀.2.2), ne_zero_of_eq_mul hx'r.1 (hx'r.2 j' hx.2.2),
      ne_zero_of_eq_mul hyr.1 (hyr.2 i hx.1), ne_zero_of_eq_mul hyr.1 (hyr.2 i₀ hx₀.1)]
  rw [hg, taylorCoeff₂_mul_of_vanish p hdim hς hunit _ _ (hg ▸ hvanish), hval]

end Faltings.BombieriVojta
