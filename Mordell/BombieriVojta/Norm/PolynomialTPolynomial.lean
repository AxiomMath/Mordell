module
public import Mordell.BombieriVojta.Norm.PolynomialT
public import Mordell.BombieriVojta.Norm.FormNormPolynomial
public import Mordell.BombieriVojta.Norm.Relation
public import Mordell.BombieriVojta.Norm.SectionRatioEval
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import Mordell.AlgebraicGeometry.ProjectiveSpace.GenericPoint

/-!
# The `T_i` are polynomials

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k` of
characteristic zero (a number field in the source), `P` a divisor of degree one, `N ≥ 2g + 1`,
`n = N - g`, and `x₀, …, xₙ` a generic `k`-basis of `L(NP)` giving `φ_{NP} : C → ℙⁿ`, with
`ψ = φ_{NP} × φ_{NP}`. Let `φ_B : C × C → ℙᵐ` be the embedding given by a basis `y₀, …, y_m`
of `H⁰(C × C, 𝒪(B))`, `η_i = y_i / y_0`, and `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. For a
global section `s ≠ 0` of `𝒪(V)` with a representative `{F_i}`, indices `1 ≤ a, b ≤ n`, and
reduced representations `(U_i, V_i)` of the norms `Norm_{k(C × C)/k(ξ_a, ξ'_b)} η_i` in
`R = k[ξ_a, ξ'_b]`, each `T_i = G_0 / V_iᵈ ∈ k(ξ_a, ξ'_b)` lies in `R`.

Indeed `G_0` and `G_i` lie in `R` (the norms of integral elements over the integrally closed `R`),
and `G_0 U_iᵈ = G_i V_iᵈ`; as `U_i, V_i` are coprime in the factorial ring `R`, `V_iᵈ ∣ G_0`.

## Main results

* `Faltings.BombieriRoth.polynomialT_mem_range_algebraMap`: `Faltings.BombieriRoth.polynomialT`
  lies in the image of `R = k[ξ_a, ξ'_b]` in `k⟮ξ_a, ξ'_b⟯`.

## Implementation notes

The source takes `k` a number field. The argument uses only that `k` has characteristic zero,
through the degree `[k(C) : k(ξ_a)] = N` of `Faltings.BombieriRoth.finrank_adjoin_div_eq`, so the
result is stated for such `k`; it then applies over any algebraic extension of `ℚ`.

The setting is that of `Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`.
The ring `R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k`, with its algebra structure on
`k⟮ξ_a, ξ'_b⟯` pinned by `X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`, `c ↦ c`. The functions `η_i` are the
quotients `y_i / y_0` themselves.

The norm relation is stated for forms whose affine evaluations are `g · η_iᵈ`; for a
representative of `s` this is the identity of `IsVojtaRepresentative` read at the generic point of
`C × C`, where `φ_{NP}` and `φ_B` restrict to the points `(x_0 : … : x_n)` and `(y_0 : … : y_m)`.
The cancellation in `R` needs `R → k⟮ξ_a, ξ'_b⟯` injective, that is `ξ_a, ξ'_b` algebraically
independent, which is proved on a tensor chart `Γ(U) ⊗_k Γ(U)` of `C ×_k C`.

The reading at the generic point goes through general lemmas on germs: a morphism to `ℙʳ` that
restricts at the generic point to `(s₀ : … : s_r)` pulls `T_ν / T₀` back to `s_ν / s₀`
(`Faltings.BombieriRoth.exists_germ_app_ratio_eq_div`), and germs pull back along a surjection
of integral schemes (`Faltings.BombieriRoth.exists_germ_app_eq_of_surjective`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriRoth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits BombieriSiegel BombieriVojta

universe u

section Charts

open Stacks.SectionsToProjectiveSpace Stacks.ProjGlobalSectionsAppTop

/-- The germ at the generic point of a pulled-back section depends on the morphism only. -/
public theorem germ_app_congr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (e : g = g') {V : Y.Opens}
    {x : X} (h : x ∈ g ⁻¹ᵁ V) (t : Γ(Y, V)) :
    X.presheaf.germ _ x h (g.app V t) = X.presheaf.germ _ x (e ▸ h) (g'.app V t) := by
  subst e
  rfl

/-- **Pulling back along a surjection between integral schemes.** If `pr : X ⟶ C` is surjective
and `ι : k(C) → k(X)` is the pull-back on germs, then for an open `U ∋ η_C` the generic point of
`X` lies in `pr⁻¹ U` and the germ there of `pr^* t` is `ι` of the germ of `t`. -/
public theorem exists_germ_app_eq_of_surjective {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (pr : X ⟶ C) (hsurj : Function.Surjective pr) (ι : C.functionField → X.functionField)
    (hι : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι (C.germToFunctionField U t) = X.germToFunctionField (pr ⁻¹ᵁ U) (pr.app U t))
    {U : C.Opens} (hU : genericPoint C ∈ U) (t : Γ(C, U)) :
    ∃ h : genericPoint X ∈ pr ⁻¹ᵁ U, X.presheaf.germ _ (genericPoint X) h (pr.app U t) =
      ι (C.presheaf.germ U (genericPoint C) hU t) := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨z, hz⟩ := hsurj (genericPoint C)
  have hz' : z ∈ pr ⁻¹ᵁ U := by
    change pr z ∈ U
    rwa [hz]
  have : Nonempty (pr ⁻¹ᵁ U) := ⟨⟨z, hz'⟩⟩
  have hmem : genericPoint X ∈ pr ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (pr ⁻¹ᵁ U).isOpen).mpr ⟨z, trivial, hz'⟩
  exact ⟨hmem, (hι U t).symm⟩

/-- **Coefficients through the structure morphism.** If the coefficient map `c ∘ e` is the
structure map of `L`, and `ξ, ξ'` are the affine coordinates `pr₁ (x_ν / x_j)`,
`pr₂ (x_ν / x_j)`, then evaluating `F` with coefficients mapped by `e` is its affine
evaluation. -/
public theorem eval₂_map_eq_affineEvaluation {k K L ι A : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [CommRing A] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι)
    (hxj : x j ≠ 0) (δ : ℕ × ℕ)
    (F : MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) : ι ⊕ ι → ℕ × ℕ) δ)
    (e : k →+* A) (c : A →+* L) (hc : ∀ a, c (e a) = algebraMap k L a) (ξ ξ' : ι → L)
    (hξ : ∀ ν, ξ ν = pr₁ (x ν / x j)) (hξ' : ∀ ν, ξ' ν = pr₂ (x ν / x j)) :
    MvPolynomial.eval₂ c (Sum.elim ξ ξ') (MvPolynomial.map e F.1) =
      affineEvaluation pr₁ pr₂ x j δ F := by
  have hce : c.comp e = algebraMap k L := RingHom.ext hc
  rw [MvPolynomial.eval₂_map, hce, ← MvPolynomial.aeval_def, funext hξ, funext hξ']
  have hc₁ : pr₁ (x j) ≠ 0 := (map_ne_zero pr₁).mpr hxj
  have hc₂ : pr₂ (x j) ≠ 0 := (map_ne_zero pr₂).mpr hxj
  have he : (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν)) : ι ⊕ ι → L) =
      Sum.elim (fun ν => pr₁ (x j) * pr₁ (x ν / x j)) (fun ν => pr₂ (x j) * pr₂ (x ν / x j)) := by
    funext ν
    rcases ν with ν | ν
    · simp [map_div₀, mul_div_cancel₀ _ hc₁]
    · simp [map_div₀, mul_div_cancel₀ _ hc₂]
  change _ = MvPolynomial.aeval (Sum.elim (fun ν => pr₁ (x ν)) (fun ν => pr₂ (x ν))) F.1 /
    (pr₁ (x j) ^ δ.1 * pr₂ (x j) ^ δ.2)
  rw [he, aeval_sumElim_mul_of_isWeightedHomogeneous
    ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2)]
  field_simp

/-- Two morphisms out of an integral scheme that agree on `Spec` of its function field pull back
global sections to the same rational function. -/
public theorem germ_appTop_eq_of_fromSpecStalk_comp_eq {Y S : Scheme.{u}} [IsIntegral Y]
    {g g' : Y ⟶ S}
    (h : Y.fromSpecStalk (genericPoint Y) ≫ g = Y.fromSpecStalk (genericPoint Y) ≫ g')
    (t : Γ(S, ⊤)) :
    Y.presheaf.germ ⊤ (genericPoint Y) trivial (g.appTop t) =
      Y.presheaf.germ ⊤ (genericPoint Y) trivial (g'.appTop t) := by
  have : Nonempty (⊤ : (Spec (.of Y.functionField)).Opens) :=
    ⟨⟨IsLocalRing.closedPoint Y.functionField, trivial⟩⟩
  have hinj : Function.Injective (fun z : Y.functionField =>
      resTop (⊤ : (Spec (.of Y.functionField)).Opens)
        ((Scheme.ΓSpecIso (.of Y.functionField)).inv z)) :=
    (map_injective_of_isIntegral _ (homOfLE le_top)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Y.functionField)).inv).1
  apply hinj
  dsimp only
  have hc : ∀ (k₁ k₂ : Spec (.of Y.functionField) ⟶ S) (e : k₁ = k₂),
      k₁.appLE ⊤ ⊤ (fun _ _ => trivial) = k₂.appLE ⊤ ⊤ (fun _ _ => trivial) := by
    rintro _ _ rfl
    rfl
  refine (fromSpecStalk_appLE_apply (U := ⊤) (genericPoint Y) trivial (fun _ _ => trivial)
    (g.appTop t)).symm.trans (Eq.trans ?_ (fromSpecStalk_appLE_apply (U := ⊤) (genericPoint Y)
      trivial (fun _ _ => trivial) (g'.appTop t)))
  have k₁ := Scheme.Hom.comp_appLE (Y.fromSpecStalk (genericPoint Y)) g ⊤ ⊤ (fun _ _ => trivial)
  have k₂ := Scheme.Hom.comp_appLE (Y.fromSpecStalk (genericPoint Y)) g' ⊤ ⊤ (fun _ _ => trivial)
  exact congrArg (fun F => F.hom t) (k₁.symm.trans ((hc _ _ h).trans k₂))

/-- **The representative identity at the generic point.** If `{F_i}` represents `s ≠ 0` in
`𝒪(V)`, then there is `g ∈ k(C ×_k C)` with `F_i(ξ, ξ') = g · (y_i / y_0)ᵈ` for every `i`, where
`F_i(ξ, ξ')` is the affine evaluation at `ξ_ν = pr₁^*(x_ν / x_0)`, `ξ'_ν = pr₂^*(x_ν / x_0)`: the
morphisms `φ_{NP}` and `φ_B` restrict at the generic points to `(x_0 : … : x_n)` and
`(y_0 : … : y_m)`. -/
private theorem exists_affineEvaluation_eq_mul_pow_of_isVojtaRepresentative {k : Type u} [Field k]
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] {f : C ⟶ Spec (.of k)} {pr₁ pr₂ : X ⟶ C}
    (hX : IsPullback pr₁ pr₂ f f) {n m : ℕ} (x : Fin (n + 1) → C.functionField)
    (hx0 : ∀ i, x i ≠ 0) (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP) (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    [Algebra k C.functionField] [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hyspan : Ideal.span (Set.range fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) = ⊤)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i)) hyspan
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    (δ₁ δ₂ d : ℕ) (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1)) :
    ∃ g : X.functionField, ∀ j,
      affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F j) = g * (y j / y 0) ^ d := by
  have hs₁ : Function.Surjective pr₁ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.1
  have hs₂ : Function.Surjective pr₂ := fun c => (exists_fst_eq_and_snd_eq hX c).imp fun _ h => h.2
  obtain ⟨hxC, hξC⟩ := exists_germ_app_ratio_eq_div_of_chart φNP x hx0 hφNPx 0
  obtain ⟨hyX, hηX⟩ := exists_germ_app_ratio_eq_div φB y (hy 0) _ _ hφB
  have hx₁ := (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC 0).1
  have hx₂ := (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC 0).1
  have key := IsVojtaRepresentative.eval₂_eq_vojtaSectionRatio_mul_pow ψ φB δ₁ δ₂ d s hs _ hF
    (hψ₁ ▸ hx₁) (hψ₂ ▸ hx₂) hyX
  refine ⟨vojtaSectionRatio ψ φB δ₁ δ₂ d s, fun j => ?_⟩
  refine (eval₂_map_eq_affineEvaluation ι₁ ι₂ x 0 (hx0 0) (δ₁, δ₂) (F j) _ _ ?_ _ _
    ?_ ?_).symm.trans ((key j).trans ?_)
  · intro c₀
    rw [hkX]
    have e₁ : ψ ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
        pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [← Category.assoc, hψ₁, Category.assoc]
    have e₂ : C.fromSpecStalk (genericPoint C) ≫
        (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) =
        C.fromSpecStalk (genericPoint C) ≫ f := by
      rw [hφNP]
    have hC := germ_appTop_eq_of_fromSpecStalk_comp_eq (Y := C)
      (g := φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) (g' := f) e₂
      ((Scheme.ΓSpecIso (.of k)).inv c₀)
    obtain ⟨_, h₁⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      ((φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c₀))
    obtain ⟨_, h₂⟩ := exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ (U := ⊤) trivial
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c₀))
    rw [hC] at h₁
    have h₃ : (ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop =
        (pr₁ ≫ (φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))).appTop := by
      rw [e₁]
    change X.presheaf.germ ⊤ (genericPoint X) trivial ((ψ ≫ pullback.fst _ _ ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))).appTop _) = _
    rw [h₃]
    exact h₁.trans h₂.symm
  · intro ν
    refine (germ_app_congr hψ₁ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₁ hs₁ ι₁ hι₁ hxC _).snd.trans
      (congrArg ι₁ (hξC ν))
  · intro ν
    refine (germ_app_congr hψ₂ _ _).trans ?_
    exact (exists_germ_app_eq_of_surjective pr₂ hs₂ ι₂ hι₂ hxC _).snd.trans
      (congrArg ι₂ (hξC ν))
  · exact congrArg (fun z => vojtaSectionRatio ψ φB δ₁ δ₂ d s * z ^ d) (hηX j)

end Charts

section Cancellation

/-- **Cancellation of a coprime factor.** Let `R → K` be injective, `R` with gcds. If
`z₀ uᵈ = zᵢ vᵈ` in `K` with `z₀, zᵢ` in the image of `R` and `u, v` coprime, `v ≠ 0`, then
`z₀ / vᵈ` lies in the image of `R`. -/
private theorem div_pow_mem_range_of_mul_pow_eq {R K : Type*} [CommRing R]
    [DecompositionMonoid R] [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {u v : R} (huv : IsRelPrime u v) (hv : v ≠ 0) (d : ℕ) {z₀ zᵢ : K}
    (h₀ : z₀ ∈ (algebraMap R K).range) (hᵢ : zᵢ ∈ (algebraMap R K).range)
    (h : z₀ * algebraMap R K u ^ d = zᵢ * algebraMap R K v ^ d) :
    z₀ / algebraMap R K v ^ d ∈ (algebraMap R K).range := by
  obtain ⟨g₀, rfl⟩ := h₀
  obtain ⟨gᵢ, rfl⟩ := hᵢ
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
  obtain ⟨q, rfl⟩ := huv.symm.pow.dvd_of_dvd_mul_right ⟨gᵢ, by rw [hinj h, mul_comm]⟩
  exact ⟨q, by rw [map_mul, map_pow, mul_div_cancel_left₀ _
    (pow_ne_zero d ((map_ne_zero_iff _ hinj).mpr hv))]⟩

end Cancellation

open Classical in
/-- **The `T_i` are polynomials** (Bombieri). In the setting of
`Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`, let `s ≠ 0` be a
global section of `𝒪(V) = Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d` with representative `F`, let
`1 ≤ a, b ≤ n`, let `R = k[ξ_a, ξ'_b] = MvPolynomial (Fin 2) k` act on `k⟮ξ_a, ξ'_b⟯` by
`X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`, and let `(U, V)` be reduced representations of the norms of
`η_i = y_i / y_0`. Then for every `i`, `T_i = polynomialT … i = G_0 / V_iᵈ` lies in the image
of `R`. -/
@[faltings "lem_bvr_polynomial_t"]
public theorem polynomialT_mem_range_algebraMap (k : Type u) [Field k]
    [CharZero k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ genus f)
    -- the divisor `P₁` of degree one on `C`
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1) (N : ℕ) (hN : 2 * genus f + 1 ≤ N)
    {n : ℕ} (hn : n = N - genus f) (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + ((N : ℤ) • P₁) Q})
    -- (N): the basis `x` is generic
    (hG1 : SatisfiesG1 k f ((N : ℤ) • P₁) x) (hG2 : SatisfiesG2 k f x)
    (hG3 : SatisfiesG3 k f x)
    -- the product `X = C ×_k C` with its projections and diagonal
    {X : Scheme.{u}} {pr₁ pr₂ : X ⟶ C} (hX : IsPullback pr₁ pr₂ f f) [IsIntegral X]
    [IsLocallyNoetherian X] (Δ : C ⟶ X) (hΔ₁ : Δ ≫ pr₁ = 𝟙 C) (hΔ₂ : Δ ≫ pr₂ = 𝟙 C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : C ⟶ projectiveSpaceOver n (Spec (.of k))) [IsClosedImmersion φNP]
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f)
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : X ⟶ pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pr₁ ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pr₂ ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k C.functionField] (hkC : ‹Algebra k C.functionField› = functionFieldAlgebra k f)
    [Algebra k X.functionField]
    (hkX : ∀ c : k, algebraMap k X.functionField c =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        ((pr₁ ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : C.functionField →ₐ[k] X.functionField)
    (hι₁ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₁ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₁ (C.germToFunctionField U t) = X.germToFunctionField (pr₁ ⁻¹ᵁ U) (pr₁.app U t))
    (hι₂ : ∀ (U : C.Opens) [Nonempty U] [Nonempty (pr₂ ⁻¹ᵁ U)] (t : Γ(C, U)),
      ι₂ (C.germToFunctionField U t) = X.germToFunctionField (pr₂ ⁻¹ᵁ U) (pr₂.app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB) {eΔ : X} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (B : X → ℤ) (hB : ∀ w : X, B w =
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₁.base ⁻¹' {c}) then a else 0) +
      (sB + 1 : ℤ) * P₁.sum (fun c a => if IsGenericPoint w (pr₂.base ⁻¹' {c}) then a else 0) -
      (if w = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → X.functionField) (hy : ∀ i, y i ≠ 0)
    (hD : ∀ i (w : X), 0 ≤ X.ord (y i) w + B w)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : X.functionField, (∀ w : X, 0 ≤ X.ord h w + B w) →
      h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ w : X, Order.coheight w = 1 → ∃ i, X.ord (y i) w + B w = 0)
    (φB : X ⟶ projectiveSpaceOver m (Spec (.of k))) [IsClosedImmersion φB]
    (hφB : X.fromSpecStalk (genericPoint X) ≫ φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of X.functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map (Scheme.ΓSpecIso (.of X.functionField)).inv.hom))
        (X.fromSpecStalk _ ≫ pr₁ ≫ f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w w' : X,
      0 < X.ord (y i) w + B w → 0 < X.ord (y 0) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i j : Fin (m + 1),
      i.val = 1 → j.val = 2 → ∀ w w' : X, 0 < X.ord (y i) w + B w →
      0 < X.ord (y j) w' + B w' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ X.ord r w ∧ X.ord r w' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ w : X,
      0 < X.ord (y i) w + B w →
      0 ≤ X.ord (ι₁ (x a' / x 0)) w ∧ 0 ≤ X.ord (ι₂ (x b' / x 0)) w)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ q : X,
        (∀ r ∈ 𝔪,
          (∀ w : X, w ⤳ q → Order.coheight w = 1 → 0 ≤ X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) ∧
          ∃ w : X, w ⤳ q ∧ Order.coheight w = 1 ∧ 0 < X.ord
            (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) →
        ∀ w : X, w ⤳ q → Order.coheight w = 1 → X.ord (y i) w + B w = 0)
    -- the Vojta data: `d₁, d₂, d` positive integers with `δᵢ = (dᵢ + sB d) / N` integers
    (d₁ d₂ d δ₁ δ₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 0 < d)
    (hδ₁N : N * δ₁ = d₁ + sB * d) (hδ₂N : N * δ₂ = d₂ + sB * d)
    -- the section `s ≠ 0` of `𝒪(V)` and its representative with coefficients in `k`
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1))
    (a b : Fin n)
    -- the ring `R = k[ξ_a, ξ'_b]` acting on `k⟮ξ_a, ξ'_b⟯` by `X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`
    [Algebra (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k
      {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})]
    (hR : ∀ G : MvPolynomial (Fin 2) k,
      (algebraMap (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k
        {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) G : X.functionField) =
        MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] G)
    -- reduced representations `(U_i, V_i)` of the norms of `η_i = y_i / y_0`
    (U V : Fin (m + 1) → MvPolynomial (Fin 2) k)
    (hUV : IsReducedNormRepresentation (MvPolynomial (Fin 2) k)
      (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      (fun i => y i / y 0) U V)
    (i : Fin (m + 1)) :
    polynomialT ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) F (fun i => y i / y 0) U V hUV d i ∈
      (algebraMap (MvPolynomial (Fin 2) k) (IntermediateField.adjoin k
        {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})).range := by
  subst hkC
  let : Algebra k C.functionField := functionFieldAlgebra k f
  have hkC' : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  -- `ξ_a` and `ξ_b` are transcendental, `k(C)` being finite over each of `k(ξ_a)`, `k(ξ_b)`
  have hdegA := finrank_adjoin_div_eq k f hg ((N : ℤ) • P₁)
      (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hli hspan hG1 a.succ
      (Fin.succ_ne_zero a)
  have hdegB := finrank_adjoin_div_eq k f hg ((N : ℤ) • P₁)
      (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hli hspan hG1 b.succ
      (Fin.succ_ne_zero b)
  have hNpos : 0 < N := by omega
  have : FiniteDimensional (IntermediateField.adjoin k {x a.succ / x 0}) C.functionField :=
    FiniteDimensional.of_finrank_pos (hdegA ▸ hNpos)
  have : FiniteDimensional (IntermediateField.adjoin k {x b.succ / x 0}) C.functionField :=
    FiniteDimensional.of_finrank_pos (hdegB ▸ hNpos)
  have htr : Algebra.trdeg k C.functionField ≠ 0 := by
    rw [AlgebraicGeometry.trdeg_functionField_eq_one k f]; exact one_ne_zero
  have hTa : Transcendental k (x a.succ / x 0) := transcendental_of_finiteDimensional htr
  have hTb : Transcendental k (x b.succ / x 0) := transcendental_of_finiteDimensional htr
  have hta : ι₁ (x a.succ) / ι₁ (x 0) = ι₁ (x a.succ / x 0) := (map_div₀ _ _ _).symm
  have hub : ι₂ (x b.succ) / ι₂ (x 0) = ι₂ (x b.succ / x 0) := (map_div₀ _ _ _).symm
  have hv : ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] =
      ![ι₁ (x a.succ / x 0), ι₂ (x b.succ / x 0)] := by
    rw [hta, hub]
  -- `R = k[ξ_a, ξ'_b] → k⟮ξ_a, ξ'_b⟯` is injective
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})) := by
    intro p q hpq
    apply injective_aeval_of_transcendental f hX hkC' ι₁ ι₂ hι₁ hι₂ hTa hTb
    have h := congrArg Subtype.val hpq
    rwa [hR, hR, hv] at h
  -- `k(C × C)` is finite over `k⟮ξ_a, ξ'_b⟯`
  have hfin : Module.Finite
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
      X.functionField := by
    have hmap : ∀ (ι : C.functionField →ₐ[k] X.functionField) (j : Fin (n + 1)),
        ι (x j / x 0) ∈
          IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} →
        ∀ c ∈ IntermediateField.adjoin k {x j / x 0}, ι c ∈
          IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} := by
      intro ι j hj c hc
      have hle : IntermediateField.map ι (IntermediateField.adjoin k {x j / x 0}) ≤
          IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)} := by
        rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff]
        simpa using hj
      exact hle ⟨c, hc, rfl⟩
    exact finite_of_isPullback f hX ι₁ ι₂ hι₁ hι₂
      (IntermediateField.adjoin k {x a.succ / x 0}) (IntermediateField.adjoin k {x b.succ / x 0})
      _ (hmap ι₁ a.succ (IntermediateField.subset_adjoin _ _
        (by rw [← hta]; exact Set.mem_insert _ _)))
      (hmap ι₂ b.succ (IntermediateField.subset_adjoin _ _
        (by rw [← hub]; exact Set.mem_insert_of_mem _ rfl)))
  -- the norms `G_j` lie in `R`
  have hG : ∀ j, formNorm ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) (F j) ∈
      (algebraMap (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k
          {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})).range := by
    intro j
    obtain ⟨G, -, -, hGe⟩ := exists_aeval_eq_formNorm_of_isVojtaRepresentative k f hg P₁ hP₁cl
      hP₁ N hN hn x hli hspan hG1 hG2 hG3 hX Δ hΔ₁ hΔ₂ φNP hφNP hφNPx ψ hψ₁ hψ₂ rfl hkX ι₁ ι₂ hι₁
      hι₂ sB hsB heΔ B hB y hy hD hyli hyspan hybpf φB hφB hBG1 hBG1' hBG2 hBG3 d₁ d₂ d δ₁ δ₂
      hd₁ hd₂ hd hδ₁N hδ₂N s hs F hF a b j
    refine ⟨G, Subtype.ext ?_⟩
    rwa [hR, hv]
  -- the representative: `F_j(ξ, ξ') = g · η_jᵈ`
  obtain ⟨g, hgF⟩ := exists_affineEvaluation_eq_mul_pow_of_isVojtaRepresentative hX x
    hli.ne_zero φNP hφNP hφNPx ψ hψ₁ hψ₂ hkX ι₁ ι₂ hι₁ hι₂ y hy _ φB hφB δ₁ δ₂ d s hs F hF
  by_cases hg0 : g = 0
  · have h0 : formNorm ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) (F 0) = 0 := by
      rw [formNorm, hgF 0, hg0, zero_mul, Algebra.norm_zero]
    exact ⟨0, by simp [polynomialT, h0]⟩
  have : FaithfulSMul (MvPolynomial (Fin 2) k)
      (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact div_pow_mem_range_of_mul_pow_eq hinj (hUV.isRelPrime i) (hUV.ne_zero i) d (hG 0) (hG i)
    (IsReducedNormRepresentation.formNorm_mul_num_pow_eq ι₁ ι₂ x 0 a.succ b.succ
      (Fin.succ_ne_zero a) (Fin.succ_ne_zero b) (δ₁, δ₂) F g hg0 (fun j => y j / y 0)
      (div_self (hy 0)) hgF hUV i)

end Faltings.BombieriRoth
