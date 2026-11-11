module
public import Mordell.BombieriVojta.Norm.NumeratorZeros

/-!
# Choice of an index `i₀` whose norm numerator does not vanish at a point

Let `C` be a smooth proper geometrically integral curve of genus `g ≥ 2` over a field `k`, with a
divisor `P` of degree one, and `X = C ×_k C`. Let `y₀, …, yₘ` be a basis of `H⁰(X, 𝒪(B))`, for
the very ample divisor `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ`, giving the embedding
`φ_B : X → ℙᵐ`, and `ηᵢ = yᵢ / y₀`. Let `x₀, …, xₙ` be a generic basis of `H⁰(C, 𝒪(N P))`,
`N ≥ 2g + 1`, `n = N - g`, and assume the `yᵢ` generic for the projections
`π_{ab} = (ξ_a, ξ'_b) : X → ℙ¹ × ℙ¹`. For
`1 ≤ a, b ≤ n` let `Norm ηᵢ = Uᵢ / Vᵢ` be reduced representations in `R = k[ξ_a, ξ'_b]`.

Then for every geometric point `p₀` of `𝔸¹ × 𝔸¹` there is an index `i₀ ≠ 0` with
`U_{i₀}(p₀) ≠ 0`. Indeed, genericity gives `i₀ ≠ 0` such that `y_{i₀}` vanishes at no point of
the fibre `π_{ab}⁻¹(p₀)`, and the zeros of `U_{i₀}` in `𝔸¹ × 𝔸¹` lie in `π_{ab}(D_{i₀})`.

## Main results

* `Faltings.exists_aeval_num_ne_zero_of_isReducedNormRepresentation`: some numerator `U i₀`,
  `i₀ ≠ 0`, of a family of reduced representations of the norms `Norm ηᵢ` does not vanish at a
  given point `p₀ : Fin 2 → k̄`.

## Implementation notes

The setting is the one of `Faltings.degreeOf_num_eq_of_isReducedNormRepresentation`, with the same
hypotheses: divisors are written through `AlgebraicGeometry.Scheme.ord` at codimension-one
points, the product is a pullback square, the embeddings `φ_{NP}` and `φ_B` are closed immersions
into `projectiveSpaceOver` restricting at the generic point to `(x₀ : … : xₙ)` and
`(y₀ : … : yₘ)`, and the genericity of the `y` is
stated on `X` over `k` through the subfields `k(ξ_{a'}, ξ'_{b'})` of `k(X)`. The ring
`R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k` with `X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`. The algebraic
closure `k̄` is any field `Ω` with `IsAlgClosure k Ω`, a point of `(𝔸¹ × 𝔸¹)(k̄)` is
`p₀ : Fin 2 → Ω`, and `U(p₀)` is `MvPolynomial.aeval p₀ U`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 633.
-/

namespace Faltings

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical BombieriSiegel in
/-- **Choice of `i₀`** (Bombieri). In the setting of
`Faltings.degreeOf_num_eq_of_isReducedNormRepresentation` (a curve `C` of genus `≥ 2` over `k` with
a divisor of degree one, `X = C ×_k C`, a basis `y` of `H⁰(X, 𝒪(B))` giving `φB` and generic for
the projections, a generic basis `x` of `H⁰(C, 𝒪(N P))` giving `φNP`), let `a, b ≠ 0` and let
`(U, V)` be a family of reduced representations of the norms of `ηᵢ = y i / y 0` from `k(X)` to
`k(ξ_a, ξ'_b)`. Then for every point `p₀` of `𝔸²` over an algebraic closure `Ω` of `k` there is
`i₀ ≠ 0` with `U i₀ (p₀) ≠ 0`. -/
@[faltings "lem_bvr_choice_i0"]
public theorem exists_aeval_num_ne_zero_of_isReducedNormRepresentation (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian C]
    (hg : 2 ≤ AlgebraicGeometry.genus f)
    -- the divisor `P₁` of degree one on `C`
    (P₁ : C →₀ ℤ) (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set C))
    (hP₁ : ∑ᶠ Q : C, P₁ Q * (f.residueDegree Q : ℤ) = 1)
    (N : ℕ) (hN : 2 * AlgebraicGeometry.genus f + 1 ≤ N)
    {n : ℕ} (hn : n = N - AlgebraicGeometry.genus f) (x : Fin (n + 1) → C.functionField)
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
    -- the embedding `φ_{NP}` given by `x`
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
          (∀ w, w ⤳ q → Order.coheight w = 1 →
            0 ≤ X.ord (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w) ∧
          (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r = 0 ∨
            ∃ w, w ⤳ q ∧ Order.coheight w = 1 ∧
              0 < X.ord (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) w)) →
        ∀ w, w ⤳ q → Order.coheight w = 1 → X.ord (y i) w + B w = 0)
    -- the projection `π_{ab}`, the ring `R = k[ξ_a, ξ'_b]` and its fraction field `K`
    (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    {K : Type u} [Field K] [Algebra (MvPolynomial (Fin 2) k) K]
    [IsFractionRing (MvPolynomial (Fin 2) k) K] [Algebra K X.functionField]
    [Algebra (MvPolynomial (Fin 2) k) X.functionField]
    [IsScalarTower (MvPolynomial (Fin 2) k) K X.functionField]
    (hRL₀ : ∀ c : k, algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.C c) =
      algebraMap k X.functionField c)
    (hRLa : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 0) =
      ι₁ (x a / x 0))
    (hRLb : algebraMap (MvPolynomial (Fin 2) k) X.functionField (MvPolynomial.X 1) =
      ι₂ (x b / x 0))
    {U V : Fin (m + 1) → MvPolynomial (Fin 2) k}
    (hU : IsReducedNormRepresentation (K := K) (MvPolynomial (Fin 2) k) (fun i => y i / y 0) U V)
    {Ω : Type*} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (p₀ : Fin 2 → Ω) :
    ∃ i₀ : Fin (m + 1), i₀ ≠ 0 ∧ MvPolynomial.aeval p₀ (U i₀) ≠ 0 := by
  obtain ⟨i, hi, hiq⟩ := hBG3 a b ha hb _ (isMaximal_ker_aeval p₀)
  refine ⟨i, hi, fun h0 => ?_⟩
  obtain ⟨q, hq, w, hwq, hw, hpos⟩ :=
    (aeval_num_eq_zero_iff_of_isReducedNormRepresentation k f hg P₁ hP₁cl hP₁ N hN hn x hli
      hspan hG1 hG2 hG3 hX Δ hΔ₁ hΔ₂ φNP hφNP hφNPx hkC hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ B hB y hy hD hyli
      hyspan hybpf φB hφB hBG1 hBG1' hBG2 hBG3 a b ha hb hRL₀ hRLa hRLb hU i hi p₀).1 h0
  exact hpos.ne' (hiq q (fun r hr => hq r (RingHom.mem_ker.1 hr)) w hwq hw)

end Faltings
