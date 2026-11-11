module
public import Mordell.BombieriVojta.DerivativeEstimate.PlaneRelation
public import Mordell.BombieriVojta.Projection.Degree

/-!
# The `X`-degree of the plane relations

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number field
`k`, `D` a divisor of degree `N ≥ 2g + 1` on `C` (Bombieri's `NP`, for `P` of degree one), and
`x₀, …, xₙ` a `k`-basis of the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))` inside the function field
`k(C)`. Write `ξ_{νj} = x_ν / x_j`. For `ν ≠ j` with `(ν, j) ∉ {(1, 0), (0, 1)}`, the plane
relation `g_{νj} ∈ k[Y][X]` is `r_{νj} μ_{νj}`, where `μ_{νj}` is the minimal polynomial of
`ξ_{νj}` over `k(ξ₁₀)` with `ξ₁₀` replaced by `Y`. If the basis satisfies (G1) and (G3), then
`deg_X g_{νj} = [k(ξ₁₀, ξ_{νj}) : k(ξ₁₀)] = [k(C) : k(ξ₁₀)] = N`.

## Main results

* `Faltings.BombieriSiegel.natDegree_planeRelation_eq`: under (G1) and (G3),
  `deg_X g_{νj} = N`.

## Implementation notes

As in `Faltings.BombieriSiegel.IsGenericBasis`, sections of `𝒪(D)` are rational functions: the
divisor is `D : C →₀ ℤ`, supported on closed points, of degree `∑ᶠ Q, D Q · [κ(Q) : k] = N`; `L(D)`
is `{g | g = 0 ∨ ∀ Q closed, 0 ≤ ord_Q g + D(Q)}`, and `k(C)` is a `k`-algebra through
`AlgebraicGeometry.functionFieldAlgebra k f`. The plane relation is
`Faltings.FunctionField.planeRelation` applied to `t = x₁ / x₀` and `z = x_ν / x_j`; it takes the
transcendence of `x₁ / x₀` over `k` as an argument, supplied here as the hypothesis `ht`. Its
`X`-degree is `Polynomial.natDegree` of the outer variable.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 7, pp. 627–628
-/

open AlgebraicGeometry IntermediateField Polynomial

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriSiegel

/-- Two polynomials with the same vanishing coefficients have the same degree. -/
private lemma natDegree_eq_of_coeff_eq_zero_iff {R S : Type*} [Semiring R] [Semiring S]
    {p : R[X]} {q : S[X]} (h : ∀ i, p.coeff i = 0 ↔ q.coeff i = 0) :
    p.natDegree = q.natDegree := by
  have : p.support = q.support := Finset.ext fun i => by simp [mem_support_iff, h]
  simp only [natDegree, degree, this]

/-- The `X`-degree of the plane relation of `z` over `t` is the degree of the minimal polynomial
of `z` over `k⟮t⟯`: clearing denominators by their least common multiple kills no coefficient. -/
private lemma natDegree_planeRelation (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F]
    (t z : F) (ht : Transcendental k t) :
    (Faltings.FunctionField.planeRelation k t z ht).natDegree = (minpoly k⟮t⟯ z).natDegree := by
  classical
  set μ : (RatFunc k)[X] := (minpoly k⟮t⟯ z).map
    (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom with hμ
  rw [← natDegree_map (RatFunc.algEquivOfTranscendental t ht).symm.toRingHom, ← hμ]
  set r : k[X] := μ.support.lcm fun i => (μ.coeff i).denom with hr
  have hr0 : r ≠ 0 := by
    simpa [hr, Finset.lcm_eq_zero_iff] using fun i _ => RatFunc.denom_ne_zero (μ.coeff i)
  refine natDegree_eq_of_coeff_eq_zero_iff fun i => ?_
  simp only [Faltings.FunctionField.planeRelation, ← hμ, ← hr, finsetSum_coeff,
    coeff_C_mul_X_pow, Finset.sum_ite_eq]
  split_ifs with hi
  · have hne : μ.coeff i ≠ 0 := mem_support_iff.1 hi
    obtain ⟨c, hc⟩ : (μ.coeff i).denom ∣ r := Finset.dvd_lcm hi
    have hc0 : c ≠ 0 := right_ne_zero_of_mul (hc ▸ hr0)
    rw [hc, mul_div_cancel_left₀ _ (RatFunc.denom_ne_zero _)]
    simp [hne, RatFunc.num_ne_zero hne, hc0]
  · simpa using notMem_support_iff.1 hi

/-- If `z ∈ F` and `t` generate `F` over `k`, then `[F : k⟮t⟯]` is the degree of the minimal
polynomial of `z` over `k⟮t⟯`. -/
private lemma natDegree_minpoly_eq_finrank (k : Type*) [Field k] {F : Type*} [Field F]
    [Algebra k F] (t z : F) (htop : k⟮z, t⟯ = ⊤) [FiniteDimensional k⟮t⟯ F] :
    (minpoly k⟮t⟯ z).natDegree = Module.finrank k⟮t⟯ F := by
  have hint : IsIntegral k⟮t⟯ z := IsIntegral.of_finite _ _
  rw [← IntermediateField.adjoin.finrank hint]
  have htop' : (k⟮t⟯)⟮z⟯ = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.restrictScalars_top,
      ← htop, Set.pair_comm]
  rw [htop', IntermediateField.finrank_top']

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a number
field `k`, `D` a divisor of degree `N ≥ 2g + 1` supported on closed points (Bombieri's `NP`),
and `x₀, …, xₙ` a `k`-basis of `L(D)` satisfying (G1) for `D` and (G3). Then for `ν ≠ j` with
`(ν, j) ∉ {(1, 0), (0, 1)}`, the plane relation `g_{νj}` of `x_ν / x_j` over `x₁ / x₀` has
degree `N` in `X`. -/
@[faltings "lem_bvs_plane_relations"]
public theorem natDegree_planeRelation_eq (k : Type u) [Field k] [NumberField k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x) (hG3 : SatisfiesG3 k f x)
    (ht : letI := functionFieldAlgebra k f; Transcendental k (x 1 / x 0))
    (ν j : Fin (n + 1)) (hνj : ν ≠ j) (h₁₀ : (ν, j) ≠ (1, 0)) (h₀₁ : (ν, j) ≠ (0, 1)) :
    letI := functionFieldAlgebra k f
    (Faltings.FunctionField.planeRelation k (x 1 / x 0) (x ν / x j) ht).natDegree = N := by
  letI := functionFieldAlgebra k f
  have h1 : (1 : Fin (n + 1)) ≠ 0 := by
    rcases n with _ | n
    · exact absurd (Subsingleton.elim (α := Fin 1) ν j) hνj
    · exact Fin.zero_lt_one.ne'
  have hdeg := finrank_adjoin_div_eq k f hg D hDcl N hN hD x hli hspan hG1 1 h1
  have : FiniteDimensional k⟮x 1 / x 0⟯ C.functionField :=
    FiniteDimensional.of_finrank_pos (by omega)
  rw [natDegree_planeRelation, natDegree_minpoly_eq_finrank k _ _ (hG3 ν j hνj h₁₀ h₀₁), hdeg]

end Faltings.BombieriSiegel
