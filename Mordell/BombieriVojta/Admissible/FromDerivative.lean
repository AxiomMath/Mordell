module
public import Mordell.BombieriVojta.Admissible.BelowCoefficient
public import Mordell.BombieriVojta.Admissible.VanishingTransfer
public import Mordell.BombieriVojta.Admissible.Comparison

/-!
# An admissible pair from a non-vanishing derivative of `T`

Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number field `k`, with the standing data of
Bombieri's Sections 9 and 10: a generic basis `x₀, …, xₙ` of `L(NP)` giving `φ_{NP}`,
`ψ = φ_{NP} × φ_{NP}`, a basis `y₀, …, y_m` of `H⁰(𝒪(B))` generic for the projections and giving
`φ_B`, and the line bundle `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(-d)` on `C × C`. Let `s ≠ 0` be a
global section of `𝒪(V)` with a representative `𝓕 = {F_i}` with coefficients in `k`, let
`K ⊇ k` be a number field and `p = (z, w)` a `K`-point of `C_K × C_K` with `z, w` outside the
exceptional set `Z`, let `1 ≤ a, b ≤ n` and `p₀ = (ξ_a(z), ξ'_b(w))`. Let `(U_i, V_i)` be
reduced representations in `R = k[ξ_a, ξ'_b]` of the norms of `η_i = y_i / y_0`, let `i₀ ≠ 0`
with `U_{i₀}(p₀) ≠ 0`, and let `T = T_{i₀} = G_0 / V_{i₀}^d`. If a divided derivative
`∂_{(i₁*, i₂*)} T` does not vanish at `p₀`, then some pair `(i₁, i₂) ≤ (i₁*, i₂*)` is admissible
for `s` at `p`.

## Main results

* `Faltings.BombieriRoth.exists_isAdmissiblePair_le_of_eval_hasseDeriv_polynomialT_ne_zero`:
  a non-vanishing divided derivative `∂_I T(p₀)` gives an admissible pair below `I`.

## Implementation notes

The setting is that of
`Faltings.BombieriRoth.eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal`: the standing
data over `k` as in `Faltings.BombieriRoth.exists_neg_le_neronPairing_of_isAdmissiblePair`, and the
source's `k̄`-points read on the base change `C_K` to a number field `K` over which they are
defined, with `s` read there as the section `s_K` of `vojtaLineBundle ψK φK δ₁ δ₂ d` represented by
`F`; admissibility (`Faltings.BombieriRoth.IsAdmissiblePair`) is for `s_K` at the `K`-point. The
value `ξ_a(z) = t₀ ∈ K` is written as: the germ of `π^* ξ_a` at `z` minus the constant `t₀` lies
in the maximal ideal of the local ring, as in `Faltings.BombieriSiegel.exceptionalSet`. The
polynomial ring `R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k`, mapped to `k(ξ_a, ξ'_b)` by
evaluation at `(ξ_a, ξ'_b)`; `T`, an element of `k(ξ_a, ξ'_b)`, is read as the polynomial `Q ∈ R`
that it is the image of, and `∂_I` is `Faltings.MvPolynomial.hasseDeriv`.

The proof is the source's. Since `z, w ∉ Z`, the local rings of `C_K` at `z` and `w` have
uniformizers `ς, ς'`. Take a local generator `e` of `𝒪(V)` near `p`
(`Faltings.exists_bijective_smul_vojtaLineBundle`) and write `s = σ e`. If `σ` lay in the ideal
`J_{i*}` of the completed local ring, then `∂_{i*} T(p₀) = 0` by
`Faltings.BombieriRoth.eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal`; so `σ ∉ J_{i*}`,
and `Faltings.BombieriRoth.exists_isAdmissiblePair_le_of_notMem_completedStalkBiorderIdeal` gives
the admissible pair.

## References

* [E. Bombieri, *The Mordell conjecture revisited*, §9, p. 633][bombieri1990]
-/

namespace Faltings.BombieriRoth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing BombieriSiegel
  BombieriVojta

universe u

/-- Outside the exceptional set `Z`, the local ring of `C` at a `k`-point has a principal maximal
ideal: otherwise `x 1 / x 0` would not be a uniformizer there, and the point would lie in `Z`. -/
private lemma exists_maximalIdeal_eq_span_of_notMem_exceptionalSet (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsLocallyNoetherian C] (D : C →₀ ℤ)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (ht : letI := functionFieldAlgebra k f; Transcendental k (x 1 / x 0))
    {z : Spec (.of k) ⟶ C} (hzk : z ≫ f = 𝟙 _) (hZ : z ∉ exceptionalSet k f D x ht) :
    ∃ g : C.presheaf.stalk (z (closedPoint k)), maximalIdeal _ = Ideal.span {g} := by
  by_contra! H
  refine hZ ⟨hzk, ?_⟩
  by_cases h0 : 0 < C.ord (x 0) (z (closedPoint k)) + D (z (closedPoint k))
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨h0, fun g _ c hc => H _ hc⟩)

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **An admissible pair from a non-vanishing derivative of `T`** (Bombieri). In the standing
setting of Sections 9–10 over a number field `k` (as in
`Faltings.BombieriRoth.eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal`), let `s ≠ 0` be
a section of `Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d` with representative `F` over `k`, `K ⊇ k` a
number field, `s_K` the section of the base-changed bundle on `C_K × C_K` represented by `F`, and
`p_K = (z, w)` a `K`-point of `C_K × C_K` with `z, w` outside
`Faltings.BombieriSiegel.exceptionalSet`, and `p₀ = (ξ_a(z), ξ'_b(w))`. Let `(U, V)` be reduced
representations of the norms of `η_i = y_i / y_0` down to `k⟮ξ_a, ξ'_b⟯`, `i₀ ≠ 0` with
`U_{i₀}(p₀) ≠ 0`, and `T = Faltings.BombieriRoth.polynomialT … i₀`. If `T` is the image of
`Q ∈ k[ξ_a, ξ'_b]` and the divided derivative `∂_{(i₁*, i₂*)} Q` does not vanish at `p₀`, then
there is a pair `i ≤ (i₁*, i₂*)` admissible for `s_K` at `p_K`. -/
@[faltings "lem_bvr_admissible_from_t"]
public theorem exists_isAdmissiblePair_le_of_eval_hasseDeriv_polynomialT_ne_zero {k : Type u}
    [Field k] [NumberField k] (X : CurveWithDegreeOneDivisor k) (hg : 2 ≤ genus X.f)
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
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
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0)
    -- the Vojta data: `d₁, d₂, d` positive integers with `δᵢ = (dᵢ + sB d) / N` integers
    (d₁ d₂ d δ₁ δ₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : 0 < d)
    (hδ₁N : N * δ₁ = d₁ + sB * d) (hδ₂N : N * δ₂ = d₂ + sB * d)
    -- the section `s ≠ 0` of `𝒪(V)` and its representative with coefficients in `k`
    (s : Γ(vojtaLineBundle ψ φB δ₁ δ₂ d, ⊤)) (hs : s ≠ 0)
    (F : Fin (m + 1) → MvPolynomial.weightedHomogeneousSubmodule k
      (Sum.elim (fun _ => ((1 : ℕ), (0 : ℕ))) (fun _ => ((0 : ℕ), (1 : ℕ))) :
        Fin (n + 1) ⊕ Fin (n + 1) → ℕ × ℕ) (δ₁, δ₂))
    (hF : IsVojtaRepresentative ψ φB δ₁ δ₂ d s
      (fun i => MvPolynomial.map (Scheme.ΓSpecIso (.of k)).inv.hom (F i).1)) :
    -- a number field `K ⊇ k` and the base change `C_K` (the `K`-block of the main inequality)
    ∀ (K : Type u) [Field K] [NumberField K] [Algebra k K]
      (CK : Scheme.{u}) [CK.Over (Spec (.of K))] (π : CK ⟶ X.C)
      (hπ : IsPullback π (CK ↘ Spec (.of K)) X.f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      [IsCurve K (CK ↘ Spec (.of K))] [IsLocallyNoetherian CK] [IsIntegral CK] [IsDominant π],
    let xK : Fin (n + 1) → CK.functionField := fun i => functionFieldMap π (x i)
    let ιS : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶ pullback X.f X.f :=
      pullback.map _ _ _ _ π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        hπ.w.symm hπ.w.symm
    ∀ (hξ₁₀ : letI := functionFieldAlgebra K (CK ↘ Spec (.of K));
        Transcendental K (xK 1 / xK 0))
      (DK : CK →₀ ℤ) (_hDK : ∀ Q, DK Q = (N : ℤ) * X.P.mapDomain Subtype.val (π Q))
      -- the base changes `ψ_K, φ_K` of `ψ, φ_B`, and the section `s_K` represented by `F`
      (ψK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        pullback (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
          (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)))
      (_hψKπ : ψK ≫ pullback.fst _ _ ≫ (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hψK₁ : ψK ≫ pullback.fst _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.fst _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (_hψK₂ : ψK ≫ pullback.snd _ _ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        ιS ≫ pullback.snd _ _ ≫ φNP ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
      (φK : pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)) ⟶
        projectiveSpaceOver m (Spec (.of K)))
      (_hφKπ : φK ≫ (projectiveSpaceOver m (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.fst _ _ ≫ (CK ↘ Spec (.of K)))
      (_hφK : φK ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of K)) =
        ιS ≫ φB ≫ projectiveSpaceOver.toIntegralAtUniverse m (Spec (.of k)))
      (sK : Γ(vojtaLineBundle ψK φK δ₁ δ₂ d, ⊤))
      (_hsK : IsVojtaRepresentative ψK φK δ₁ δ₂ d sK (fun i => MvPolynomial.map
        ((Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap k K)) (F i).1))
      -- the `K`-point `p_K = (z, w)` of `C_K × C_K`
      (pK : Spec (.of K) ⟶ pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)))
      [pK.IsOver (Spec (.of K))],
      -- `z, w ∉ Z`
      pK ≫ pullback.fst _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
      pK ≫ pullback.snd _ _ ∉ exceptionalSet K (CK ↘ Spec (.of K)) DK xK hξ₁₀ →
    -- the indices `1 ≤ a, b ≤ n` and the point `p₀ = (ξ_a(z), ξ'_b(w)) = (t₀, t₀')` of `K²`
    ∀ (a b : Fin n) (t₀ t₀' : K),
      (∃ g : CK.presheaf.stalk ((pK ≫ pullback.fst _ _) (closedPoint K)),
        algebraMap _ CK.functionField g = xK a.succ / xK 0 ∧
        g - ((Scheme.ΓSpecIso (.of K)).inv ≫ (CK ↘ Spec (.of K)).appTop ≫
          CK.presheaf.germ ⊤ _ trivial).hom t₀ ∈ maximalIdeal _) →
      (∃ g : CK.presheaf.stalk ((pK ≫ pullback.snd _ _) (closedPoint K)),
        algebraMap _ CK.functionField g = xK b.succ / xK 0 ∧
        g - ((Scheme.ΓSpecIso (.of K)).inv ≫ (CK ↘ Spec (.of K)).appTop ≫
          CK.presheaf.germ ⊤ _ trivial).hom t₀' ∈ maximalIdeal _) →
    -- `R = k[ξ_a, ξ'_b] → k(ξ_a, ξ'_b)` and reduced representations of the norms of `η_i`
    ∀ [Algebra (MvPolynomial (Fin 2) k)
        (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})],
      (∀ r : MvPolynomial (Fin 2) k,
        (algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) r :
            (pullback X.f X.f).functionField) =
          MvPolynomial.aeval ![ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)] r) →
    ∀ (Un Vd : Fin (m + 1) → MvPolynomial (Fin 2) k)
      (hUV : IsReducedNormRepresentation
        (K := IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)})
        (MvPolynomial (Fin 2) k) (fun i => y i / y 0) Un Vd)
    -- the index `i₀ ≠ 0` with `U_{i₀}(p₀) ≠ 0`
      (i₀ : Fin (m + 1)), i₀ ≠ 0 → MvPolynomial.aeval ![t₀, t₀'] (Un i₀) ≠ 0 →
    -- `T = T_{i₀}`, the image of `Q ∈ R`, with `∂_{i*} Q (p₀) ≠ 0`
    ∀ Q : MvPolynomial (Fin 2) k,
      algebraMap (MvPolynomial (Fin 2) k)
          (IntermediateField.adjoin k {ι₁ (x a.succ) / ι₁ (x 0), ι₂ (x b.succ) / ι₂ (x 0)}) Q =
        polynomialT ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) F (fun i => y i / y 0) Un Vd hUV d i₀ →
    ∀ istar : ℕ × ℕ,
      MvPolynomial.aeval ![t₀, t₀']
        (Faltings.MvPolynomial.hasseDeriv (Finsupp.single 0 istar.1 + Finsupp.single 1 istar.2) Q)
          ≠ 0 →
      ∃ i ≤ istar, IsAdmissiblePair (vojtaLineBundle ψK φK δ₁ δ₂ d) sK pK i := by
  intro K _ _ _ CK _ π hπ _ _ _ _ xK ιS hξ₁₀ DK hDK ψK hψKπ hψK₁ hψK₂ φK hφKπ hφK sK hsK pK _
    hz hw a b t₀ t₀' hp₁ hp₂ _ hR Un Vd hUV i₀ hi₀ hU Q hQ istar hT
  -- the projections `z = pr₁ ∘ p_K` and `w = pr₂ ∘ p_K` are `K`-points of `C_K`
  have hwf : (pK ≫ pullback.snd (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) ≫
      (CK ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc]
    exact comp_over_eq_id pK
  have hzf : (pK ≫ pullback.fst (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))) ≫
      (CK ↘ Spec (.of K)) = 𝟙 _ := by
    rwa [Category.assoc, pullback.condition, ← Category.assoc]
  -- outside `Z` the local rings at `z` and `w` have uniformizers `ς`, `ς'`
  obtain ⟨ς, hς⟩ := exists_maximalIdeal_eq_span_of_notMem_exceptionalSet K _ _ xK hξ₁₀ hzf hz
  obtain ⟨ς', hς'⟩ := exists_maximalIdeal_eq_span_of_notMem_exceptionalSet K _ _ xK hξ₁₀ hwf hw
  -- a local generator `e` of `𝒪(V_K)` near `p_K`, and `σ = s_K / e`
  obtain ⟨W, hxW, e, he⟩ :=
    exists_bijective_smul_vojtaLineBundle ψK φK δ₁ δ₂ d (pK (closedPoint K))
  have he' : Function.Bijective
      fun c : Γ(pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)), W) => c • e := by
    simpa using he W le_rfl
  obtain ⟨σ, hσ⟩ :=
    he'.2 ((vojtaLineBundle ψK φK δ₁ δ₂ d).presheaf.map (homOfLE le_top).op sK)
  by_cases hJ : algebraMap _ _ ((pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K))).presheaf.germ
      W _ hxW σ) ∈ completedStalkBiorderIdeal (CK ↘ Spec (.of K))
      (CK ↘ Spec (.of K)) (pK (closedPoint K)) istar.1 istar.2
  · -- `σ ∈ J_{i*}` would force `∂_{i*} T (p₀) = 0`
    exact (hT (eval_hasseDeriv_eq_zero_of_mem_completedStalkBiorderIdeal X hg N hN hn x hx hxbpf
      Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx ψ hψ₁ hψ₂ hkC hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ DB hDB y hy hyD
      hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3 d₁ d₂ d δ₁ δ₂ hd₁ hd₂ hd hδ₁N hδ₂N
      s hs F hF K CK π hπ hξ₁₀ DK hDK ψK hψKπ hψK₁ hψK₂ φK hφKπ hφK sK hsK pK hz hw a b t₀ t₀'
      hp₁ hp₂ hR Un Vd hUV i₀ hi₀ hU W hxW e he σ hσ hJ Q hQ istar.1 le_rfl istar.2
      le_rfl)).elim
  · -- otherwise `σ ∉ J_{i*}`, so `s_K ≠ 0` (its quotient `σ` would be `0 ∈ J_{i*}`), and
    -- `σ ∉ J_{i*}` gives an admissible pair below `i*`
    have hsK0 : sK ≠ 0 := by
      rintro rfl
      have hσ0 : σ = 0 := by
        refine he'.1 ?_
        change σ • e = (0 : Γ(pullback (CK ↘ Spec (.of K)) (CK ↘ Spec (.of K)), W)) • e
        exact hσ.trans (by rw [map_zero, zero_smul])
      subst hσ0
      refine hJ ?_
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
    exact exists_isAdmissiblePair_le_of_notMem_completedStalkBiorderIdeal hsK0 ς ς' hς hς' W hxW
      e he σ hσ hJ

end Faltings.BombieriRoth
