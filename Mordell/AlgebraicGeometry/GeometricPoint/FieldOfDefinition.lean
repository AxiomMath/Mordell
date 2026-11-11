module

public import Mathlib
public import Mordell.Attr

/-!
# The field of definition of a geometric point

Let `X` be a scheme locally of finite type over a number field `k`, and `K` an algebraic closure
of `k`. A `K`-point of `X` over `k` is a morphism `Q : Spec K ⟶ X` whose composite with the
structure morphism `X ⟶ Spec k` is `Spec` of the algebra map `k → K`. By Stacks 01J6 such a `Q`
is the same as a point `x ∈ X` (the image of the unique point of `Spec K`) together with an
embedding `ι : κ(x) → K` of the residue field. The field of definition of `Q` is the subfield
`k(Q) = ι(κ(x))` of `K`; it contains `k` because `Q` lies over `k`, so it is an intermediate
field of `K / k`.

## Main definitions

* `Faltings.fieldOfDefinition`: the field of definition `k(Q) ⊆ K` of a `K`-point `Q` of a
  `k`-scheme `X`, as an `IntermediateField k K`.

## Main results

* `Faltings.specToEquivOfField_specMap_comp`: the point and residue field embedding attached to
  `Spec f ≫ Q` are those of `Q`, with the embedding composed with `f`.

## Implementation notes

The pair `(x, ι)` attached to `Q` is the one given by
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, and `k(Q)` is the field range of `ι`. The `k`-scheme
structure of `X` is an `AlgebraicGeometry.Scheme.Over` instance, and "`Q` is a `k`-morphism" is the
equation `Q ≫ X ↘ Spec k = Spec.map (algebraMap k K)`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry, weeks 9–10*, Sec. 3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Faltings

universe u

/-- Precomposing a field-valued point `Q : Spec K ⟶ X` with `Spec f`, for `f : K ⟶ L`, keeps the
point of `X` attached to `Q` by `Scheme.SpecToEquivOfField` and composes its residue field
embedding with `f`. -/
lemma specToEquivOfField_specMap_comp {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : CommRingCat.of K ⟶ CommRingCat.of L) (Q : Spec (.of K) ⟶ X) :
    Scheme.SpecToEquivOfField L X (Spec.map f ≫ Q) =
      ⟨(Scheme.SpecToEquivOfField K X Q).1, (Scheme.SpecToEquivOfField K X Q).2 ≫ f⟩ := by
  rw [← Equiv.eq_symm_apply, Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp,
    Category.assoc, ← Scheme.SpecToEquivOfField_symm_apply, Equiv.symm_apply_apply]

/-- The field of definition `k(Q)` of a `K`-point `Q : Spec K ⟶ X` of a `k`-scheme `X`
(`K` an algebraic closure of the number field `k`): if `x ∈ X` is the image of the point of
`Spec K` and `ι : κ(x) → K` the induced embedding of residue fields, then `k(Q) = ι(κ(x))`. -/
@[faltings "def_mw_field_of_definition"]
noncomputable def fieldOfDefinition {k K : Type u} [Field k] [NumberField k] [Field K]
    [Algebra k K] [IsAlgClosure k K] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (Q : Spec (.of K) ⟶ X)
    (hQ : Q ≫ X ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    IntermediateField k K :=
  ((Scheme.SpecToEquivOfField K X Q).2).hom.fieldRange.toIntermediateField fun r => by
    set p := Scheme.SpecToEquivOfField K X Q
    have hQ' : Q = Spec.map p.2 ≫ X.fromSpecResidueField p.1 :=
      ((Scheme.SpecToEquivOfField K X).symm_apply_apply Q).symm
    obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = X.fromSpecResidueField p.1 ≫ X ↘ Spec (.of k) :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    have h : φ ≫ p.2 = CommRingCat.ofHom (algebraMap k K) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ← Category.assoc, ← hQ', hQ]
    exact ⟨φ r, congrArg (fun f => f.hom r) h⟩

end Faltings

/-!
# Fields of definition are finite

Let `X` be a scheme locally of finite type over a number field `k`, `K` an algebraic closure of
`k`, and `Q : Spec K ⟶ X` a `K`-point of `X` over `k`. If `x ∈ X` is the image of `Q` and
`ι : κ(x) → K` the induced embedding, then `κ(x)` is a finitely generated field extension of `k`
(it is the fraction field of a quotient of a finitely generated `k`-algebra) which is algebraic
over `k` (it embeds in `K`), hence finite. So the field of definition
`Faltings.fieldOfDefinition Q hQ = ι(κ(x))` is a finite extension of `k`.

## Main results

* `Faltings.exists_essFiniteType_fromSpecResidueField_comp`: for `X` locally of finite type over
  `Spec R` and `x ∈ X`, the composite `Spec κ(x) ⟶ X ⟶ Spec R` is `Spec` of an essentially finite
  type ring map `R ⟶ κ(x)`.
* `Faltings.finiteDimensional_fieldRange_residueField`: the image of `κ(x)` under a `k`-embedding
  into an algebraic extension of `k` is finite over `k`.
* `Faltings.finiteDimensional_fieldOfDefinition`: `k(Q)` is finite-dimensional over `k`.

## References

* [Stacks, Tag 01TF], [Stacks, Tag 00FV]
* X. Wu, *Diophantine geometry, weeks 9–10*, Sec. 3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Faltings

universe u

/-- The canonical map `Spec κ(y) ⟶ Spec R` is `Spec` of an essentially finite type ring map. -/
private lemma exists_essFiniteType_fromSpecResidueField_Spec (R : CommRingCat.{u})
    (y : Spec R) : ∃ h : R ⟶ (Spec R).residueField y,
      h.hom.EssFiniteType ∧ Spec.map h = (Spec R).fromSpecResidueField y := by
  have : y.asIdeal.IsPrime := y.isPrime
  refine ⟨CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R y).inv, ?_, ?_⟩
  · rw [CommRingCat.hom_comp]
    exact (RingHom.essFiniteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.Spec.residueFieldIso R y).commRingCatIsoToRingEquiv.symm.surjective).essFiniteType
  · rw [Spec.map_comp]
    exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _

/-- For `f : X ⟶ Spec R` locally of finite type and `x ∈ X`, the composite
`Spec κ(x) ⟶ X ⟶ Spec R` is `Spec` of an essentially finite type ring map `R ⟶ κ(x)`. -/
lemma exists_essFiniteType_fromSpecResidueField_comp {R : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] (x : X) :
    ∃ φ : R ⟶ X.residueField x,
      φ.hom.EssFiniteType ∧ Spec.map φ = X.fromSpecResidueField x ≫ f := by
  obtain ⟨h, hh, hSpec⟩ := exists_essFiniteType_fromSpecResidueField_Spec R (f x)
  refine ⟨h ≫ f.residueFieldMap x, ?_, ?_⟩
  · rw [CommRingCat.hom_comp]
    exact hh.comp (LocallyOfFiniteType.stalkMap f x).residueFieldMap
  · rw [Spec.map_comp, hSpec, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- Let `X` be locally of finite type over a field `k`, `x ∈ X`, and `ι : κ(x) → K` an embedding
over `k` into an algebraic extension `K / k`. Then `ι(κ(x))` is a finite extension of `k`:
`κ(x)` is essentially of finite type over `k` and algebraic (it embeds in `K`), hence finite. -/
lemma finiteDimensional_fieldRange_residueField {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (ι : X.residueField x ⟶ .of K)
    (hι : Spec.map ι ≫ X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hk : ∀ r, algebraMap k K r ∈ ι.hom.fieldRange) :
    FiniteDimensional k (ι.hom.fieldRange.toIntermediateField hk) := by
  obtain ⟨φ, hess, hφ⟩ := exists_essFiniteType_fromSpecResidueField_comp f x
  have hφι : φ ≫ ι = CommRingCat.ofHom (algebraMap k K) :=
    Spec.map_injective (by rw [Spec.map_comp, hφ, hι])
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  have : Algebra.EssFiniteType k (X.residueField x) := hess
  let ι' : X.residueField x →ₐ[k] K :=
    { ι.hom with commutes' := fun r => congrArg (fun g => g.hom r) hφι }
  have : Algebra.IsAlgebraic k (X.residueField x) :=
    Algebra.IsAlgebraic.of_injective ι' ι'.toRingHom.injective
  have : Module.Finite k (X.residueField x) := Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact (AlgEquiv.ofInjectiveField ι').toLinearEquiv.finiteDimensional

/-- The field of definition `k(Q)` of a `k̄`-point `Q` of a scheme `X` locally of finite type over
a number field `k` is a finite extension of `k`. -/
@[faltings "lem_mw_field_of_definition_finite"]
theorem finiteDimensional_fieldOfDefinition {k K : Type u} [Field k] [NumberField k] [Field K]
    [Algebra k K] [IsAlgClosure k K] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (Q : Spec (.of K) ⟶ X)
    (hQ : Q ≫ X ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    FiniteDimensional k (fieldOfDefinition Q hQ) := by
  refine finiteDimensional_fieldRange_residueField (X ↘ Spec (.of k)) _ _ ?_ _
  rw [← Category.assoc, ← hQ]
  exact congrArg (· ≫ _) ((Scheme.SpecToEquivOfField K X).symm_apply_apply Q)

end Faltings

/-!
# Points over an intermediate field

Let `X` be a scheme locally of finite type over a number field `k`, let `K` be an algebraic
closure of `k`, and let `Q : Spec K ⟶ X` be a `K`-point of `X` over `k`. For an intermediate
field `k ⊆ L ⊆ K`, the point `Q` comes from an `L`-point of `X` over `k`, i.e. is of the form
`Spec (L ⊆ K) ≫ P` for some `P : Spec L ⟶ X` over `k`, if and only if the field of definition
`Faltings.fieldOfDefinition Q hQ` is contained in `L`.

## Main results

* `Faltings.exists_spec_map_comp_eq_iff_fieldOfDefinition_le`: `Q` lies in the image of
  `X(L) → X(K)` if and only if `k(Q) ≤ L`.

## References

* [Stacks, Tag 01J6]
* X. Wu, *Diophantine geometry, weeks 9–10*, Sec. 3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Faltings

universe u

/-- For a tower `k → L → K` of fields, a morphism `Spec L ⟶ Spec k` whose composite with
`Spec K ⟶ Spec L` is the structure morphism of `Spec K` is the structure morphism of `Spec L`. -/
private lemma eq_spec_map_algebraMap_of_comp {k L K : Type u} [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (f : Spec (.of L) ⟶ Spec (.of k))
    (h : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    f = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_preimage f] at h ⊢
  rw [← Spec.map_comp] at h
  congr 1
  ext r
  apply (algebraMap L K).injective
  simpa [← IsScalarTower.algebraMap_apply] using
    congrArg (fun φ => φ.hom r) (Spec.map_injective h)

/-- A `K`-point `Q` of a `k`-scheme `X` (`K` an algebraic closure of `k`) comes from an
`L`-point over `k`, for an intermediate field `k ⊆ L ⊆ K`, if and only if its field of
definition is contained in `L`. -/
@[faltings "lem_mw_points_galois"]
theorem exists_spec_map_comp_eq_iff_fieldOfDefinition_le {k K : Type u} [Field k]
    [NumberField k] [Field K] [Algebra k K] [IsAlgClosure k K] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] (Q : Spec (.of K) ⟶ X)
    (hQ : Q ≫ X ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (L : IntermediateField k K) :
    (∃ P : Spec (.of L) ⟶ X,
      P ≫ X ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ P = Q) ↔
      fieldOfDefinition Q hQ ≤ L := by
  -- `k(Q) ≤ L` unfolds to: the residue field embedding of `Q` takes values in `L`.
  change _ ↔ Set.range (Scheme.SpecToEquivOfField K X Q).2.hom ⊆ L
  constructor
  · rintro ⟨P, -, rfl⟩
    rw [specToEquivOfField_specMap_comp]
    rintro _ ⟨a, rfl⟩
    exact ((Scheme.SpecToEquivOfField L X P).2.hom a).2
  · intro hle
    set p := Scheme.SpecToEquivOfField K X Q
    have hP : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom (p.2.hom.codRestrict L fun a => hle ⟨a, rfl⟩)) ≫
          X.fromSpecResidueField p.1 = Q := by
      rw [← Category.assoc, ← Spec.map_comp]
      exact (Scheme.SpecToEquivOfField K X).symm_apply_apply Q
    exact ⟨_, eq_spec_map_algebraMap_of_comp _ (by rw [← Category.assoc, hP, hQ]), hP⟩

end Faltings

/-!
# Points over a subfield inject

Let `k` be a number field, `k̄` an algebraic closure of `k`, `k ⊆ K ⊆ k̄` an intermediate field
and `X` a scheme locally of finite type over `k`. The map `X(K) → X(k̄)` on `k`-points, given by
precomposition with `Spec k̄ → Spec K`, is injective: a morphism `Spec K ⟶ X` is a point `x ∈ X`
together with an embedding `κ(x) → K`, and composing with the injective `K → k̄` loses nothing.

## Main results

* `Faltings.injOn_spec_map_comp`: the restriction map `X(K) → X(k̄)` is injective.

## Implementation notes

A `k`-scheme is a scheme `X` with `X.Over (Spec k)`, and `X(K)` is the set of morphisms
`P : Spec K ⟶ X` with `P ≫ X ↘ Spec k = Spec (k → K)`. The algebraic closure is any field `k̄`
with `IsAlgClosure k k̄` (for instance `AlgebraicClosure k`), and `K` is an
`IntermediateField k k̄`. Injectivity of the restriction map is stated as `Set.InjOn` of
`P ↦ Spec (K → k̄) ≫ P` on `X(K)`. The proof uses only that `Spec` of a field map is an
epimorphism of schemes, so injectivity holds on all morphisms `Spec K ⟶ X`.

## References

* [Stacks, Tag 01J6]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- For a scheme `X` locally of finite type over a number field `k`, an algebraic closure `k̄`
of `k` and an intermediate field `k ⊆ K ⊆ k̄`, the map `X(K) → X(k̄)` on `k`-points,
`P ↦ Spec.map (K → k̄) ≫ P`, is injective. -/
@[faltings "lem_mw_points_restriction_injective"]
theorem injOn_spec_map_comp {k kbar : Type u} [Field k] [NumberField k] [Field kbar]
    [Algebra k kbar] [IsAlgClosure k kbar] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (K : IntermediateField k kbar) :
    Set.InjOn (fun P : Spec (.of K) ⟶ X => Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ P)
      {P | P ≫ X ↘ Spec (.of k) = Spec.map (CommRingCat.ofHom (algebraMap k K))} :=
  fun _ _ _ _ h => (cancel_epi _).1 h

end Faltings
