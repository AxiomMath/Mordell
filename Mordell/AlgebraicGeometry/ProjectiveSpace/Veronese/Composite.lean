module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.Veronese.Basic

/-!
# The Veronese composite of a map to projective space

Given a map `φ : X → ℙ(K^ι)` and a degree `e ≥ 1`, its Veronese composite
`φ^{(e)} = Φ_e ∘ φ : X → ℙ(K^{\{I // |I| = e\}})` is the composite of `φ` with the Veronese
map `Φ_e = Faltings.veroneseMap`. On points it sends `p` to `[(φ(p)^I)_{|I| = e}]`. For
`ι = Fin (n + 1)` the target is `ℙ^{binom (n + e) n - 1}`.

## Main definitions

* `Faltings.veroneseComposite`: the Veronese composite `φ^{(e)} = Φ_e ∘ φ`.

## Implementation notes

The Veronese map `Faltings.veroneseMap` is a map on the `K`-points of projective spaces, so
the composite is defined on points: `X` is the set of points of the variety and `φ` the map
the morphism induces on points. Nothing about `X` is needed to form the composite, so `X` is
an arbitrary type.

## References

* [Gao, *An Introduction to Diophantine Geometry*, proof of Prop. 5.1.3(iii)][gao2022]
* [Bombieri, *The Mordell conjecture revisited*, §2][bombieri1990]
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Faltings

variable (K : Type*) [Field K] {X ι : Type*}

/-- The **Veronese composite** `φ^{(e)} = Φ_e ∘ φ : X → ℙ(K^{\{I // |I| = e\}})` of a map
`φ : X → ℙ(K^ι)`, where `Φ_e` is the Veronese map of degree `e ≥ 1`. -/
@[faltings "def_ht_veronese_embedding"]
public noncomputable def veroneseComposite (e : ℕ) (he : 1 ≤ e) (φ : X → ℙ K (ι → K)) :
    X → ℙ K ({I : ι →₀ ℕ // I.degree = e} → K) :=
  veroneseMap K e he ∘ φ

end Faltings
