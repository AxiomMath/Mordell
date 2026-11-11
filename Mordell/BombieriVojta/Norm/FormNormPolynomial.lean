module
public import Mathlib
public import Mordell.Attr
public import Mordell.BombieriVojta.Norm.FormNorm
public import Mordell.BombieriVojta.Representative.Basic
public import Mordell.BombieriVojta.Projection.Product
public import Mordell.BombieriVojta.Projection.Degree
public import Mordell.AlgebraicGeometry.NormalScheme.Integrality
public import Mordell.Curve.Topology
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsTensorProduct
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import Mordell.Polynomial.TwoVariable
public import Mordell.CurveProduct.FunctionField

/-!
# The norms `G_i` are polynomials

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k`
of characteristic zero (a number field in the source), `P` a divisor of degree one,
`N ≥ 2g + 1`, `n = N - g`, and `x₀, …, xₙ` a generic `k`-basis of `L(NP)` giving the embedding
`φ_{NP} : C → ℙⁿ`, with `ψ = φ_{NP} × φ_{NP}`. Let `φ_B : C × C → ℙᵐ` be the embedding given by
a basis `y₀, …, y_m` of `H⁰(C × C, 𝒪(B))`, and `𝒪(V) = ψ^*𝒪(δ₁, δ₂) ⊗ φ_B^*𝒪(d)⁻¹`. For a
global section `s ≠ 0` of `𝒪(V)` with a representative `{F_i}` with coefficients in `k`, and
`1 ≤ a, b ≤ n`, the norm `G_i = Norm_{k(C × C)/k(ξ_a, ξ'_b)} F_i(ξ, ξ')` is a polynomial in
`ξ_a, ξ'_b` of degree at most `N² δ₁` in `ξ_a` and at most `N² δ₂` in `ξ'_b`.

Indeed `ξ_j` and `ξ'_j` are integral over `k[ξ_a]` and `k[ξ'_b]` by equations of degree `N`, so
`F_i(ξ, ξ')` is integral over `k[ξ_a, ξ'_b]` and its norm, of degree `N²`, lies there; the degree
bound comes from the pole order `δ₁` of `F_i(ξ, ξ')` along `X₀ × C = π_{ab}^*(∞ × ℙ¹)` (and `δ₂`
along `C × X₀`).

## Main results

* `Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative`: the norm
  `Faltings.BombieriRoth.formNorm` of `F_i(ξ, ξ')` is `P(ξ_a, ξ'_b)` for a polynomial
  `P ∈ k[X₀, X₁]` with `deg_{X₀} P ≤ N² δ₁` and `deg_{X₁} P ≤ N² δ₂`.
* `Faltings.BombieriRoth.exists_tensor_chart`: on an affine chart `U × U` of `C ×_k C`, the map
  `Γ(U) ⊗_k Γ(U) → k(C ×_k C)` is injective, and `k(C ×_k C)` is its field of fractions.
* `Faltings.BombieriRoth.injective_aeval_of_transcendental`: `pr₁^* ζ₁` and `pr₂^* ζ₂` are
  algebraically independent for `ζ₁, ζ₂ ∈ k(C)` transcendental over `k`.
* `Faltings.BombieriRoth.finite_of_isPullback`: `k(C ×_k C)` is finite over any subfield
  containing `pr₁^* K₁` and `pr₂^* K₂` for subfields `K₁, K₂` over which `k(C)` is finite.
* `Faltings.BombieriRoth.span_eq_top_of_isPullback`,
  `Faltings.BombieriRoth.finrank_le_mul_of_isPullback`: the products of basis vectors of `k(C)`
  over `K₁` and `K₂` span `k(C ×_k C)` over such a subfield `E`, so
  `[k(C ×_k C) : E] ≤ [k(C) : K₁] · [k(C) : K₂]`.

## Implementation notes

The source takes `k` a number field. The argument uses only that `k` has characteristic zero
(through the degree `[k(C) : k(ξ_a)] = N` of `Faltings.BombieriSiegel.finrank_adjoin_div_eq`), so
`Faltings.BombieriRoth.exists_aeval_eq_formNorm_of_isVojtaRepresentative` is stated for such
`k`; it then applies over any algebraic extension of `ℚ`.
The curve data are those of `Faltings.BombieriVojta.productProjectionToProjectiveLine`, and
`ℙʳ_k` is `projectiveSpaceOver r (Spec k)`, as for `Faltings.vojtaLineBundle`. The product
`C × C` is any pullback square `IsPullback pr₁ pr₂ f f`, with a diagonal `Δ`. The embedding
`φ_{NP}` is pinned by its restriction to the generic point, which is the point `(x₀ : … : xₙ)` of
`ℙⁿ` over `k(C)`, and `ψ` by its two components `φ_{NP} ∘ pr₁`, `φ_{NP} ∘ pr₂`; likewise `φ_B`
restricts to `(y₀ : … : y_m)` at the generic point of `C × C`. The function field of `C` carries
`AlgebraicGeometry.functionFieldAlgebra k f`, the function field of `C × C` the `k`-structure of
its structure morphism, and the pull-backs `pr₁^*, pr₂^*` are `k`-algebra maps pinned by their
values on germs. The divisor `B = (s + 1)(P × C) + (s + 1)(C × P) - Δ` and the genericity (B) of
the `y_i` are written through orders of vanishing at the codimension-one points of `C × C`. The
representative has coefficients in `k`, carried into `Γ(Spec k, 𝒪)` by `Scheme.ΓSpecIso`. The
polynomial ring `R = k[ξ_a, ξ'_b]` is `MvPolynomial (Fin 2) k` with `X 0 ↦ ξ_a`, `X 1 ↦ ξ'_b`.

The proof is by integrality rather than through the divisor of `G_i`. Condition (G1) says that
`x₀` and `x_a` have no common zero, so by the valuative criterion on the proper normal curve `C`,
`ξ_ν` is integral over `k[ξ_a]` and `x_ν / x_a` over `k[ξ_a⁻¹]`. Hence, with `t = pr₁^* ξ_a` and
`u = pr₂^* ξ_b`, `F_i(ξ, ξ')` is integral over `k[t, u]`, and its dehomogenisations
`F_i(ξ, ξ') t^{-δ₁}`, `F_i(ξ, ξ') u^{-δ₂}` over `k[t⁻¹, u]` and `k[t, u⁻¹]`. On an affine chart
`U × U` the sections of `C ×_k C` are `Γ(U) ⊗_k Γ(U)`, which makes `t, u` algebraically
independent and bounds `[k(C × C) : k(t, u)]` by `[k(C) : k(ξ_a)] [k(C) : k(ξ_b)] = N²`. The
three polynomial rings are integrally closed, so the norm is a polynomial in `(t, u)`, and after
division by `t^{Dδ₁}` (resp. `u^{Dδ₂}`) a polynomial in `(t⁻¹, u)` (resp. `(t, u⁻¹)`), where
`D = [k(C × C) : k(t, u)]`; this is the integral form of the pole-order bound along `X₀ × C`.
## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 9, p. 632.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriRoth

open BombieriSiegel BombieriVojta

universe u

section Evaluation

open MvPolynomial

/-- A polynomial with coefficients in `k` evaluated at elements integral over a `k`-algebra `A` is
integral over `A`. -/
public theorem isIntegral_aeval {k A L σ : Type*} [Field k] [CommRing A] [Field L] [Algebra k A]
    [Algebra A L] [Algebra k L] [IsScalarTower k A L] {γ : σ → L}
    (hγ : ∀ i, IsIntegral A (γ i)) (F : MvPolynomial σ k) : IsIntegral A (aeval γ F) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply k A L]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    exact hp.mul (hγ i)

end Evaluation

open Classical in
/-- **The norms `G_i` are polynomials** (Bombieri). Let `C` be a smooth projective geometrically
integral curve of genus `g ≥ 2` over a field `k` of characteristic zero, with structure morphism
`f`, a divisor `P` of degree one, `N ≥ 2g + 1`, `n = N - g`, and `x` a generic `k`-basis of `L(NP)`
giving `φNP : C ⟶ ℙⁿ_k`, `ψ = φNP × φNP`. Let `φB : C × C ⟶ ℙᵐ_k` be the embedding given by a basis
`y` of `H⁰(C × C, 𝒪(B))`, `B = (sB + 1)(P × C) + (sB + 1)(C × P) - Δ`, generic for the
projections. Let `s ≠ 0` be a global section of `𝒪(V) = Faltings.vojtaLineBundle ψ φB δ₁ δ₂ d`
with a representative `F` with coefficients in `k`. Then for `1 ≤ a, b ≤ n` and every `i`, the
norm `G_i = formNorm pr₁^* pr₂^* x 0 a b (δ₁, δ₂) (F i)` of `F_i(ξ, ξ')` from `k(C × C)` to
`k(ξ_a, ξ'_b)` is `G(ξ_a, ξ'_b)` for a polynomial `G ∈ k[X₀, X₁]` of degree at most `N² δ₁` in
`X₀` and at most `N² δ₂` in `X₁`. -/
@[faltings "lem_bvr_norm_g_polynomial"]
public theorem exists_aeval_eq_formNorm_of_isVojtaRepresentative (k : Type u) [Field k]
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
    (a b : Fin n) (i : Fin (m + 1)) :
    ∃ G : MvPolynomial (Fin 2) k, G.degreeOf 0 ≤ N ^ 2 * δ₁ ∧ G.degreeOf 1 ≤ N ^ 2 * δ₂ ∧
      MvPolynomial.aeval ![ι₁ (x a.succ / x 0), ι₂ (x b.succ / x 0)] G =
        (formNorm ι₁ ι₂ x 0 a.succ b.succ (δ₁, δ₂) (F i) : X.functionField) := by
  subst hkC
  let : Algebra k C.functionField := functionFieldAlgebra k f
  have : IsNormal C := isNormal_of_smooth_over_field f
  have hkC' : ∀ c : k, algebraMap k C.functionField c =
      C.presheaf.germ ⊤ (genericPoint C) trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) :=
    fun c => rfl
  set a' : Fin (n + 1) := a.succ with ha'def
  set b' : Fin (n + 1) := b.succ with hb'def
  have ha' : a' ≠ 0 := Fin.succ_ne_zero a
  have hb' : b' ≠ 0 := Fin.succ_ne_zero b
  have hx0 : ∀ j, x j ≠ 0 := hli.ne_zero
  have hmem : ∀ j Q, 0 ≤ C.ord (x j) Q + ((N : ℤ) • P₁) Q :=
    ord_add_nonneg_of_span_eq f (isClosed_of_mem_support_smul hP₁cl _) hli hspan
  -- (G1): `x 0` and `x a` have no common zero
  have hno : ∀ p : Fin (n + 1), p ≠ 0 → ∀ c : C, Order.coheight c = 1 →
      ¬(0 < C.ord (x 0) c + ((N : ℤ) • P₁) c ∧
        0 < C.ord (x p) c + ((N : ℤ) • P₁) c) := fun p hp c hc =>
    hG1 p hp c (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f
      fun h => FunctionField.coheight_genericPoint_ne_one C (h ▸ hc))
  -- so on either chart of `π_a`, the affine coordinates pull back to integral elements
  have hI : ∀ (ι : C.functionField →ₐ[k] X.functionField) (s : Set X.functionField)
      (p q : Fin (n + 1)), (∀ c : C, Order.coheight c = 1 →
        ¬(0 < C.ord (x p) c + ((N : ℤ) • P₁) c ∧
          0 < C.ord (x q) c + ((N : ℤ) • P₁) c)) →
      ι (x p / x q) ∈ s → ∀ ν, IsIntegral (Algebra.adjoin k s) (ι (x ν / x q)) :=
    fun ι s p q hpq hs ν => isIntegral_map_of_mem_integralClosure (A := Algebra.adjoin k s) ι
      (x p / x q)
      ⟨⟨_, Algebra.subset_adjoin hs⟩, rfl⟩ (fun c => ⟨algebraMap k _ c, rfl⟩)
      (div_mem_integralClosure_of_not_common_zero f hkC' (hx0 ν) (hx0 p) (hx0 q) (hmem ν)
        (hmem p) (hmem q) hpq)
  have hI₀ : ∀ p : Fin (n + 1), p ≠ 0 → ∀ c : C, Order.coheight c = 1 →
      ¬(0 < C.ord (x p) c + ((N : ℤ) • P₁) c ∧
        0 < C.ord (x 0) c + ((N : ℤ) • P₁) c) :=
    fun p hp c hc h => hno p hp c hc h.symm
  -- the coordinates `t = ξ_a`, `u = ξ'_b` on `C × C`
  set t : X.functionField := ι₁ (x a' / x 0) with htdef
  set u : X.functionField := ι₂ (x b' / x 0) with hudef
  have ht0 : t ≠ 0 := (map_ne_zero ι₁).mpr (div_ne_zero (hx0 _) (hx0 _))
  have hu0 : u ≠ 0 := (map_ne_zero ι₂).mpr (div_ne_zero (hx0 _) (hx0 _))
  have htinv : t⁻¹ = ι₁ (x 0 / x a') := by rw [htdef, ← map_inv₀, inv_div]
  have huinv : u⁻¹ = ι₂ (x 0 / x b') := by rw [hudef, ← map_inv₀, inv_div]
  -- `F_i(ξ, ξ')` and its two dehomogenisations
  have hF := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (F i).2
  set z := affineEvaluation ι₁ ι₂ x 0 (δ₁, δ₂) (F i) with hzdef
  have hc₁ : ι₁ (x 0) ≠ 0 := (map_ne_zero ι₁).mpr (hx0 0)
  have hc₂ : ι₂ (x 0) ≠ 0 := (map_ne_zero ι₂).mpr (hx0 0)
  have hca : ι₁ (x a') ≠ 0 := (map_ne_zero ι₁).mpr (hx0 a')
  have hcb : ι₂ (x b') ≠ 0 := (map_ne_zero ι₂).mpr (hx0 b')
  have hsplit : ∀ (ι : C.functionField →ₐ[k] X.functionField) (j ν : Fin (n + 1)),
      ι (x ν) = ι (x j) * ι (x ν / x j) := fun ι j ν => by
    rw [← map_mul, mul_div_cancel₀ _ (hx0 j)]
  have hzval : z = MvPolynomial.aeval (Sum.elim (fun ν => ι₁ (x ν)) (fun ν => ι₂ (x ν))) (F i).1 /
      (ι₁ (x 0) ^ δ₁ * ι₂ (x 0) ^ δ₂) := rfl
  have hev : ∀ j₁ j₂ : Fin (n + 1),
      MvPolynomial.aeval (Sum.elim (fun ν => ι₁ (x ν)) (fun ν => ι₂ (x ν))) (F i).1 =
        ι₁ (x j₁) ^ δ₁ * ι₂ (x j₂) ^ δ₂ * MvPolynomial.aeval
          (Sum.elim (fun ν => ι₁ (x ν / x j₁)) (fun ν => ι₂ (x ν / x j₂))) (F i).1 := by
    intro j₁ j₂
    have he : (Sum.elim (fun ν => ι₁ (x ν)) (fun ν => ι₂ (x ν)) : Fin (n + 1) ⊕ Fin (n + 1) → _) =
        Sum.elim (fun ν => ι₁ (x j₁) * ι₁ (x ν / x j₁)) (fun ν => ι₂ (x j₂) * ι₂ (x ν / x j₂)) := by
      funext ν
      rcases ν with ν | ν
      · exact hsplit ι₁ j₁ ν
      · exact hsplit ι₂ j₂ ν
    rw [he, aeval_sumElim_mul_of_isWeightedHomogeneous hF]
  have hz : z = MvPolynomial.aeval
      (Sum.elim (fun ν => ι₁ (x ν / x 0)) (fun ν => ι₂ (x ν / x 0))) (F i).1 := by
    rw [hzval, hev 0 0]
    exact mul_div_cancel_left₀ _ (mul_ne_zero (pow_ne_zero _ hc₁) (pow_ne_zero _ hc₂))
  have hz₁ : z * t⁻¹ ^ δ₁ = MvPolynomial.aeval
      (Sum.elim (fun ν => ι₁ (x ν / x a')) (fun ν => ι₂ (x ν / x 0))) (F i).1 := by
    rw [hzval, hev a' 0, htdef, map_div₀, inv_div, div_pow]
    field_simp
  have hz₂ : z * u⁻¹ ^ δ₂ = MvPolynomial.aeval
      (Sum.elim (fun ν => ι₁ (x ν / x 0)) (fun ν => ι₂ (x ν / x b'))) (F i).1 := by
    rw [hzval, hev 0 b', hudef, map_div₀, inv_div, div_pow]
    field_simp
  -- integrality of `F_i(ξ, ξ')` over `k[t, u]`, `k[t⁻¹, u]` and `k[t, u⁻¹]`
  have hzint : IsIntegral (Algebra.adjoin k {t, u}) z := by
    rw [hz]
    refine isIntegral_aeval ?_ _
    rintro (ν | ν)
    exacts [hI ι₁ {t, u} a' 0 (hI₀ a' ha') (Set.mem_insert _ _) ν,
      hI ι₂ {t, u} b' 0 (hI₀ b' hb') (Set.mem_insert_of_mem _ rfl) ν]
  have hz₁int : IsIntegral (Algebra.adjoin k {t⁻¹, u}) (z * t⁻¹ ^ δ₁) := by
    rw [hz₁]
    refine isIntegral_aeval ?_ _
    rintro (ν | ν)
    exacts [hI ι₁ {t⁻¹, u} 0 a' (hno a' ha') (htinv ▸ Set.mem_insert _ _) ν,
      hI ι₂ {t⁻¹, u} b' 0 (hI₀ b' hb') (Set.mem_insert_of_mem _ rfl) ν]
  have hz₂int : IsIntegral (Algebra.adjoin k {t, u⁻¹}) (z * u⁻¹ ^ δ₂) := by
    rw [hz₂]
    refine isIntegral_aeval ?_ _
    rintro (ν | ν)
    exacts [hI ι₁ {t, u⁻¹} a' 0 (hI₀ a' ha') (Set.mem_insert _ _) ν,
      hI ι₂ {t, u⁻¹} 0 b' (hno b' hb') (huinv ▸ Set.mem_insert_of_mem _ rfl) ν]
  -- `[k(C) : k(ξ_a)] = N`, and `ξ_a` is transcendental
  have hdegA := finrank_adjoin_div_eq k f hg ((N : ℤ) • P₁)
      (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hli hspan hG1 a' ha'
  have hdegB := finrank_adjoin_div_eq k f hg ((N : ℤ) • P₁)
      (isClosed_of_mem_support_smul hP₁cl _) N hN
      (finsum_smul_mul_residueDegree f hP₁ _) x hli hspan hG1 b' hb'
  have hNpos : 0 < N := by omega
  have : FiniteDimensional (IntermediateField.adjoin k {x a' / x 0}) C.functionField :=
    FiniteDimensional.of_finrank_pos (hdegA ▸ hNpos)
  have : FiniteDimensional (IntermediateField.adjoin k {x b' / x 0}) C.functionField :=
    FiniteDimensional.of_finrank_pos (hdegB ▸ hNpos)
  have htr : Algebra.trdeg k C.functionField ≠ 0 := by
    rw [AlgebraicGeometry.trdeg_functionField_eq_one k f]
    exact one_ne_zero
  have hTa : Transcendental k (x a' / x 0) := transcendental_of_finiteDimensional htr
  have hTb : Transcendental k (x b' / x 0) := transcendental_of_finiteDimensional htr
  have hTa' : Transcendental k (x 0 / x a') := by
    rw [← inv_div]; exact fun h => hTa (IsAlgebraic.inv_iff.mp h)
  have hTb' : Transcendental k (x 0 / x b') := by
    rw [← inv_div]; exact fun h => hTb (IsAlgebraic.inv_iff.mp h)
  have h₁ := injective_aeval_of_transcendental f hX hkC' ι₁ ι₂ hι₁ hι₂ hTa hTb
  have h₂ := injective_aeval_of_transcendental f hX hkC' ι₁ ι₂ hι₁ hι₂ hTa' hTb
  have h₃ := injective_aeval_of_transcendental f hX hkC' ι₁ ι₂ hι₁ hι₂ hTa hTb'
  rw [← htinv] at h₂
  rw [← huinv] at h₃
  -- `[k(C × C) : k(ξ_a, ξ'_b)] ≤ N²`
  have hmap : ∀ (ι : C.functionField →ₐ[k] X.functionField) (j : Fin (n + 1)),
      ι (x j / x 0) ∈ IntermediateField.adjoin k {t, u} →
      ∀ c ∈ IntermediateField.adjoin k {x j / x 0}, ι c ∈ IntermediateField.adjoin k {t, u} := by
    intro ι j hj c hc
    have hle : IntermediateField.map ι (IntermediateField.adjoin k {x j / x 0}) ≤
        IntermediateField.adjoin k {t, u} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff]
      simpa using hj
    exact hle ⟨c, hc, rfl⟩
  have hD := finrank_le_mul_of_isPullback f hX ι₁ ι₂ hι₁ hι₂
    (IntermediateField.adjoin k {x a' / x 0}) (IntermediateField.adjoin k {x b' / x 0})
    (IntermediateField.adjoin k {t, u})
    (hmap ι₁ a' (IntermediateField.subset_adjoin _ _ (by simp [htdef])))
    (hmap ι₂ b' (IntermediateField.subset_adjoin _ _ (by simp [hudef])))
  rw [hdegA, hdegB, ← sq] at hD
  -- the norm
  obtain ⟨G, hG0, hG1, hGe⟩ :=
    exists_degreeOf_le_aeval_eq_norm ht0 hu0 h₁ h₂ h₃ δ₁ δ₂ hzint hz₁int hz₂int
  refine ⟨G, hG0.trans (Nat.mul_le_mul_right δ₁ hD), hG1.trans (Nat.mul_le_mul_right δ₂ hD), ?_⟩
  rw [hGe]
  have hta : ι₁ (x a') / ι₁ (x 0) = t := by rw [htdef, map_div₀]
  have hub : ι₂ (x b') / ι₂ (x 0) = u := by rw [hudef, map_div₀]
  unfold formNorm
  rw [hta, hub]

end Faltings.BombieriRoth
