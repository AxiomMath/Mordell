module

public import Mathlib
public import Mordell.Attr

/-!
# The generator of a function field is transcendental

Let `F/K` be an algebraic function field of one variable: `F` is a `K`-algebra together with a
compatible `RatFunc K`-algebra structure for which `F` is finite dimensional over `K(X)`. The image
`t = algebraMap (RatFunc K) F RatFunc.X` of the variable is transcendental over `K`, since
`K[X] → K(X) → F` is an injective `K`-algebra map sending `X` to `t`.

## Main results

* `Faltings.FunctionField.transcendental_algebraMap_X`: the image of `RatFunc.X` in a function
  field `F/K` is transcendental over `K`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], 1.1.1, Remark 1.1.3
-/

public section

namespace Faltings.FunctionField

/-- In a function field `F/K`, the image `t` of the variable `RatFunc.X` is transcendental
over `K`: the map `K(X) → F` is an injective field homomorphism and `X` is transcendental. -/
@[faltings "lem_ff_generator_transcendental"]
theorem transcendental_algebraMap_X (K F : Type*) [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] :
    Transcendental K (algebraMap (RatFunc K) F RatFunc.X) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) F).injective).mpr
    RatFunc.transcendental_X

end Faltings.FunctionField

end


/-!
# Function fields are finitely generated of transcendence degree one

Let `F/K` be an algebraic function field of one variable: `F` is a `K`-algebra together with a
compatible `RatFunc K`-algebra structure for which `F` is finite dimensional over `K(X)`. Then `F`
is finitely generated as a field extension of `K`, and its transcendence degree over `K` is `1`:
if `b₁, …, bₙ` is a `K(t)`-basis of `F` then `F = K(t, b₁, …, bₙ)`, and `{t}` is a transcendence
basis since `t` is transcendental over `K` and `F/K(t)` is algebraic.

## Main results

* `Faltings.FunctionField.fg_top_and_trdeg_eq_one`: for a function field `F/K`, the intermediate
  field `⊤` of `F/K` is finitely generated and `Algebra.trdeg K F = 1`.

## Implementation notes

"Finitely generated field extension" is `IntermediateField.FG` of `⊤ : IntermediateField K F`,
i.e. `F = K(S)` for a finite set `S`; this is weaker than `Algebra.FiniteType K F`, which would
ask for generation as a `K`-algebra.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], 1.1.1
* [The Stacks Project][stacks-project], Tag 0BY1
-/

public section

namespace Faltings.FunctionField

/-- The generator `X` of `K(X)` is a transcendence basis of any algebraic extension `F` of
`K(X)`: push the basis `{X}` of `K[X]` along `K[X] → K(X) → F`, both steps algebraic. -/
private lemma isTranscendenceBasis_X (K F : Type*) [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [Algebra.IsAlgebraic (RatFunc K) F] :
    IsTranscendenceBasis K fun _ : Unit ↦ algebraMap (RatFunc K) F RatFunc.X := by
  have : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors (Polynomial K))
  simpa [Function.comp_def, RatFunc.algebraMap_X] using
    ((IsTranscendenceBasis.polynomial Unit K).algebraMap_comp (A := RatFunc K)).algebraMap_comp
      (A := F)

/-- A function field `F/K` is a finitely generated field extension of `K` of transcendence
degree `1`. -/
@[faltings "lem_ff_finitely_generated_trdeg_one"]
theorem fg_top_and_trdeg_eq_one (K F : Type*) [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F] :
    (⊤ : IntermediateField K F).FG ∧ Algebra.trdeg K F = 1 := by
  have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    .of_isLocalization (RatFunc K) (nonZeroDivisors (Polynomial K))
  have : Algebra.EssFiniteType K (RatFunc K) := .comp K (Polynomial K) (RatFunc K)
  have : Algebra.EssFiniteType K F := .comp K (RatFunc K) F
  exact ⟨IntermediateField.fg_top K F,
    by simpa using (isTranscendenceBasis_X K F).lift_cardinalMk_eq_trdeg.symm⟩

end Faltings.FunctionField

end
