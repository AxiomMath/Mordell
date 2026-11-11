module
public import Mordell.BombieriVojta.SmallSection.U0

/-!
# The space `U₂`

Let `k` be a field, `C ⊆ ℙⁿ` a curve over `k` with coordinates `x = (x_ν)` in `k(C)`, and
`U₀ ⊆ k(C × C)^{m+1}` the `k`-subspace of tuples `(F_i(ξ, ξ'))_{i=0}^m` of values of
bihomogeneous forms of bidegree `(δ₁, δ₂)` over `k`
(`Faltings.BombieriVojta.affineEvaluationTuples`). Let `P_i, Q_i ∈ k(C × C)` be the values of
the fixed polynomials with `η_i = P_i / Q_i`, and `d` a positive integer. The space
`U₂ ⊆ U₀` is the set of tuples `(u_i)_{i=0}^m ∈ U₀` solving the basic system
`(P_i Q_j)^d u_j = (P_j Q_i)^d u_i` in `k(C × C)` for all `i, j`. Each equation is `k`-linear
in the tuple, so `U₂` is a `k`-subspace.

## Main definitions

* `Faltings.BombieriVojta.affineEvaluationTuplesBasicSystem`: the space `U₂`.

## Implementation notes

As for `Faltings.BombieriVojta.affineEvaluationTuples`, `k(C)` and `k(C × C)` are arbitrary
fields `K`, `L` over `k` with `k`-algebra maps `pr₁ pr₂ : K →ₐ[k] L`, and the tuple is indexed by
an arbitrary type `σ` (the source's case is `σ = Fin (m + 1)`). The values `P_i`, `Q_i` are
arbitrary families `P Q : σ → L`; the source's standing condition `Q_i ≠ 0` is not needed to
define the subspace. `U₂` is `U₀` intersected with the solution space of the basic system.

## References

* [Bombieri1990], Sec. 8, pp. 630–631.
-/

namespace Faltings.BombieriVojta

/-- The space `U₂`: the `k`-subspace of tuples `u` in `U₀ = affineEvaluationTuples pr₁ pr₂ x j δ σ`
satisfying the basic system `(P i * Q j) ^ d * u j = (P j * Q i) ^ d * u i` for all `i j : σ`. -/
@[expose, faltings "def_bvs_space_u2"]
public noncomputable def affineEvaluationTuplesBasicSystem {k K L ι : Type*} [Field k] [Field K]
    [Field L] [Algebra k K] [Algebra k L] (pr₁ pr₂ : K →ₐ[k] L) (x : ι → K) (j : ι)
    (δ : ℕ × ℕ) (σ : Type*) (P Q : σ → L) (d : ℕ) : Submodule k (σ → L) :=
  affineEvaluationTuples pr₁ pr₂ x j δ σ ⊓
    { carrier := {u | ∀ i i' : σ, (P i * Q i') ^ d * u i' = (P i' * Q i) ^ d * u i}
      add_mem' := fun {u v} hu hv i i' => by
        simp only [Pi.add_apply, mul_add, hu i i', hv i i']
      zero_mem' := fun i i' => by simp
      smul_mem' := fun c u hu i i' => by
        simp only [Pi.smul_apply, mul_smul_comm, hu i i'] }

end Faltings.BombieriVojta
