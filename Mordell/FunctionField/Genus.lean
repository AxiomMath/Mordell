module

public import Mordell.FunctionField.Adele.Basic

/-!
# The genus of a function field

Let `F/K` be a field extension with adele ring `𝒜_F`, integral adeles `𝒜_F(0)` and principal
adeles `P_F`. The *genus* of `F/K` is the dimension over `K` of the quotient
`𝒜_F / (𝒜_F(0) + P_F)`, where `𝒜_F(0) + P_F` is the sum of `K`-subspaces of `𝒜_F`. It is defined
with `Module.finrank`, so it is a natural number, equal to `0` when the quotient is not
finite dimensional.

## Main definitions

* `Faltings.genus K F`: the genus `g(F/K) = finrank_K (𝒜_F / (𝒜_F(0) + P_F))`.

## Implementation notes

The definition uses neither that `K` is a field nor that `F/K` is a function field, so it is stated
for a commutative ring `K` and a `K`-algebra `F` which is a field, like `Faltings.Adele`. For an
algebraic function field of one variable the quotient is finite dimensional and this is the usual
genus. The sum `𝒜_F(0) + P_F` is the supremum `Faltings.Adele.integral K F ⊔
Faltings.Adele.principal K F` in the lattice of `K`-submodules.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Definition 1.4.15,
  Corollary 1.5.5
-/

namespace Faltings

@[expose] public section

variable (K F : Type*) [CommRing K] [Field F] [Algebra K F]

/-- The *genus* `g(F/K)` of `F/K`: the `K`-dimension of `𝒜_F / (𝒜_F(0) + P_F)`, the quotient of
the adele ring by the sum of the integral and the principal adeles (`0` if it is infinite
dimensional). -/
@[faltings "def_ff_genus"]
noncomputable def genus : ℕ :=
  Module.finrank K (Adele K F ⧸ (Adele.integral K F ⊔ Adele.principal K F))

end

end Faltings
