module

public import Mathlib
public import Mordell.Attr

/-!
# The Veronese map

For a field `K`, a type `ι` of homogeneous coordinates and a degree `e ≥ 1`, the Veronese map
`Φ_e : ℙ(K^ι) → ℙ(K^{monomials of degree e})` sends the point with homogeneous coordinates
`x = (x_i)_{i ∈ ι}` to the point whose coordinates are all monomials
`x^I = ∏ᵢ x_i ^ I i` with `I : ι →₀ ℕ` of total degree `|I| = e`. With `ι = Fin (n + 1)` this is
`Φ_e : ℙⁿ → ℙ^{binom (n + e) n - 1}`, since there are `binom (n + e) n` such monomials.

The map is well defined: scaling `x` by `t ≠ 0` scales every `x^I` by `t ^ e`, and if
`x_i ≠ 0` then the coordinate `x^{e • eᵢ} = x_i ^ e` is nonzero.

## Main definitions

* `Faltings.veroneseMap`: the Veronese map `ℙ(K^ι) → ℙ(K^{\{I // |I| = e\}})` on points.

## Main results

* `Faltings.veroneseMap_mk`: the Veronese map sends `[x]` to `[(x^I)_{|I| = e}]`.

## Implementation notes

The Veronese map is a morphism of schemes `ℙⁿ → ℙᴺ`; here it is given by its action on
`K`-points, the projective spaces being `Projectivization K (ι → K)`. The target is indexed by
the subtype `{I : ι →₀ ℕ // I.degree = e}` of exponent vectors of total degree `e`, and the
coordinate at `I` is `I.prod fun i k => x i ^ k`.

## References

* [Hartshorne, *Algebraic Geometry*, I Ex. 2.12, II Ex. 5.13][hartshorne1977]
* [Bombieri, *The Mordell conjecture revisited*, Sec. 2][bombieri1990]
-/

@[expose] public section

namespace Faltings

open scoped LinearAlgebra.Projectivization

/-- The **Veronese map** of degree `e ≥ 1` on points: it sends `[x] ∈ ℙ(K^ι)` to the point
`[(x^I)_{|I| = e}]` whose coordinates are all monomials `x^I = ∏ᵢ xᵢ ^ I i` of total
degree `e`. -/
@[faltings "def_ht_veronese_map"]
noncomputable def veroneseMap (K : Type*) [Field K] {ι : Type*} (e : ℕ) (he : 1 ≤ e) :
    ℙ K (ι → K) → ℙ K ({I : ι →₀ ℕ // I.degree = e} → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K (fun I => I.1.prod fun i k => v.1 i ^ k) (by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp v.2
      intro h
      have := congrFun h ⟨Finsupp.single i e, by simp⟩
      change (Finsupp.single i e).prod (fun j k => v.1 j ^ k) = 0 at this
      rw [Finsupp.prod_single_index (h := fun j k => v.1 j ^ k) (pow_zero _)] at this
      exact hi (eq_zero_of_pow_eq_zero this)))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
      refine (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr ⟨t ^ e, ?_⟩
      funext I
      simp only [Pi.smul_apply, smul_eq_mul]
      obtain ⟨I, rfl⟩ := I
      change t ^ I.degree * (I.prod fun i k => b i ^ k) = I.prod fun i k => (t * b i) ^ k
      rw [Finsupp.degree_apply, Finsupp.prod, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [mul_pow])

/-- On a representative, the Veronese map is `[x] ↦ [(x^I)_{|I| = e}]`. -/
theorem veroneseMap_mk (K : Type*) [Field K] {ι : Type*} (e : ℕ) (he : 1 ≤ e) (x : ι → K)
    (hx : x ≠ 0) (hy : (fun I : {I : ι →₀ ℕ // I.degree = e} => I.1.prod fun i k => x i ^ k) ≠ 0) :
    veroneseMap K e he (Projectivization.mk K x hx) =
      Projectivization.mk K (fun I => I.1.prod fun i k => x i ^ k) hy :=
  rfl

end Faltings
