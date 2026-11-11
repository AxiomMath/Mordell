module

public import Mordell.Height.Weil.Representative

/-!
# Galois invariance of the Weil height

The absolute logarithmic Weil height of a point of projective space over an algebraic extension
of `ℚ` does not change when a field automorphism (more generally, a field embedding over `ℚ`) is
applied to its homogeneous coordinates: `h(τ x) = h(x)`.

## Main results

* `Faltings.weilHeight_mk_map`: for `τ : K →ₐ[ℚ] L` between algebraic extensions of `ℚ` and
  a nonzero `v : ι → K`, `h((τ v_i)_i) = h((v_i)_i)`.

## Implementation notes

The action of `τ` on a point `x = (v_0 : ⋯ : v_n)` is `τ x = (τ v_0 : ⋯ : τ v_n)`; it is stated
on homogeneous coordinates through `Projectivization.mk`, for an arbitrary nonzero representative
`v`. The case `K = L = AlgebraicClosure ℚ`, `τ ∈ Aut(ℚ̄ / ℚ)` and `ι = Fin (n + 1)` is the
classical statement.

The source transports the places of `F = ℚ(v_i)_i` to those of `τ F` along `τ`. Here `τ F` is
never formed: the coordinate vector `y : ι → F` represents `[v]` through `F → K` and `[τ v]`
through `τ ∘ (F → K)`, so both heights are the same sum of local heights over the places of `F`
(`Faltings.weilHeight_eq_sumLocalHeight`).

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Sec. 2.
* [Z. Gao, *Heights*][gao2022].
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

/-- The Weil height is invariant under field embeddings over `ℚ`: if `τ : K →ₐ[ℚ] L` and
`v : ι → K` is nonzero, the point `(τ v_i)_i` of `ℙ L (ι → L)` has the same height
`Faltings.weilHeight` as the point `(v_i)_i` of `ℙ K (ι → K)`. -/
@[faltings "lem_ht_height_galois_invariant"]
public theorem weilHeight_mk_map {K L : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] {ι : Type*} [Fintype ι] [LinearOrder ι]
    (τ : K →ₐ[ℚ] L) (v : ι → K) (hv : v ≠ 0) :
    weilHeight (Projectivization.mk L (fun i => τ (v i))
        (fun h => hv (funext fun i => τ.toRingHom.injective (by simpa using congrFun h i)))) =
      weilHeight (Projectivization.mk K v hv) := by
  let F := IntermediateField.adjoin ℚ (Set.range v)
  have hF : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  -- `NumberField` uses the canonical `ℚ`-algebra of a characteristic-zero field
  have : NumberField F := { to_finiteDimensional := by convert hF; exact Subsingleton.elim _ _ }
  let y : ι → F := fun i => ⟨v i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  let : Algebra F L := (τ.toRingHom.comp (algebraMap F K)).toAlgebra
  exact (weilHeight_eq_sumLocalHeight (y := y) _ rfl).trans
    (weilHeight_eq_sumLocalHeight (y := y) _ rfl).symm

end Faltings
