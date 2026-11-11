module

public import Mathlib
public import Mordell.Attr
public import Mordell.AbelianVariety.AbelianScheme.BaseChange
public import Mordell.AbelianVariety.SpreadingOut

/-!
# Good reduction of an abelian variety

Let `A` be an abelian variety over a number field `k` and `𝔭` a finite place of `k`, that is a
nonzero prime ideal of the ring of integers `𝓞 k`. Write `𝓞_{k,(𝔭)}` for the localization of
`𝓞 k` at `𝔭`. The variety `A` has *good reduction* at `𝔭` if there is an abelian scheme `𝒜` over
`𝓞_{k,(𝔭)}` whose generic fibre `𝒜 ×_{𝓞_{k,(𝔭)}} Spec k` is isomorphic to `A` as a group scheme
over `k`. Otherwise `A` has *bad reduction* at `𝔭`.

## Main definitions

* `Faltings.HasGoodReduction`: the abelian variety `A` over `k` has good reduction at the finite
  place `𝔭`.

## Implementation notes

A finite place of `k` is a term `𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 k)`. The local ring
`𝓞_{k,(𝔭)}` is the subring `Localization.subalgebra k 𝔭.asIdeal.primeCompl _` of `k`. It is a
localization of `𝓞 k` at `𝔭`, and as a subring of `k` it comes with the inclusion into `k`.
The generic fibre is the base change along `Spec k → Spec 𝓞_{k,(𝔭)}`, the morphism `Spec.map`
of that inclusion. The group structure on the base change is carried along by
`(Over.pullback _).mapGrp`. Group schemes are bundled as `CategoryTheory.Grp` objects, and the
isomorphism is taken in that category, so it is an isomorphism of group schemes over `k`.
An abelian variety over `k` is an object `A : Over (Spec k)` with a `CategoryTheory.GrpObj`
structure whose structure morphism is proper and geometrically integral. An abelian scheme over
`W = Spec 𝓞_{k,(𝔭)}` is a group object in `Over W` whose structure morphism is flat, proper and
locally of finite presentation (with properness this is finite presentation), and all of whose
fibres `𝒜 ×_W Spec κ(w)` are abelian varieties over `κ(w)`. Both are spelled out here in these
terms.

## References

* [J.-P. Serre, J. Tate, *Good reduction of abelian varieties*][serre1968], §1
* [J. S. Milne, *Abelian varieties*][milneAV]
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain

namespace Faltings

/-- An abelian variety `A` over a number field `k` has *good reduction* at the finite place `𝔭`
if there are an abelian scheme `𝒜` over the localization `𝓞_{k,(𝔭)}` (a group scheme that is
flat, proper and locally of finite presentation, with all fibres `𝒜 ×_W Spec κ(w)` proper and
geometrically integral) and an isomorphism of group schemes over `k` between the generic fibre
`𝒜 ×_{𝓞_{k,(𝔭)}} Spec k` and `A`. -/
@[faltings "def_mw_good_reduction"]
def HasGoodReduction (k : Type u) [Field k] [NumberField k] (𝔭 : HeightOneSpectrum (𝓞 k))
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (CommRingCat.of
      (Localization.subalgebra k 𝔭.asIdeal.primeCompl
        𝔭.asIdeal.primeCompl_le_nonZeroDivisors)))),
    Flat 𝒜.X.hom ∧ IsProper 𝒜.X.hom ∧ LocallyOfFinitePresentation 𝒜.X.hom ∧
    (∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom) ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (Localization.subalgebra k 𝔭.asIdeal.primeCompl
          𝔭.asIdeal.primeCompl_le_nonZeroDivisors) k)))).mapGrp.obj 𝒜 ≅ Grp.mk A)

end Faltings


/-!
# Abelian varieties have good reduction almost everywhere

Let `A` be an abelian variety over a number field `k`. Then `A` has good reduction at all but
finitely many finite places of `k`: the set of nonzero primes `𝔭` of `𝓞 k` at which `A` has bad
reduction is finite.

The proof spreads `A` out to an abelian scheme over `𝓞 k[1/N]` for some nonzero integer `N`
(`Faltings.exists_isAbelianScheme_localizationAway_pullback_iso`). For every prime `𝔭` not
dividing `N` the ring `𝓞 k[1/N]` lies inside `𝓞_{k,(𝔭)}`, and base change of that model along
the inclusion is an abelian scheme over `𝓞_{k,(𝔭)}` with generic fibre `A`
(`Faltings.isAbelianScheme_pullbackObj`). Only finitely many primes divide `N`.

## Main results

* `Faltings.finite_setOf_mem_asIdeal`: a nonzero element of a Dedekind domain lies in only
  finitely many height-one primes.
* `Faltings.finite_setOf_not_hasGoodReduction`: the set of finite places of `k` at which `A`
  does not have good reduction (in the sense of `Faltings.HasGoodReduction`) is finite.

## References

* [J.-P. Serre, J. Tate, *Good reduction of abelian varieties*][serre1968], §1
* [J. S. Milne, *Abelian varieties*][milneAV]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain

namespace Faltings

/-- A nonzero element of a Dedekind domain lies in only finitely many height-one primes. -/
lemma finite_setOf_mem_asIdeal {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R}
    (ha : a ≠ 0) : {v : HeightOneSpectrum R | a ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {a}) (by simpa [Ideal.zero_eq_bot] using ha)).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

/-- Base changing a group scheme along `g` and then along `a` agrees, as a group scheme, with
base changing it along any `b` with `a ≫ g = b`. -/
private lemma nonempty_mapGrp_pullback_comp_iso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ Z)
    (b : X ⟶ Z) (h : a ≫ g = b) (G : Grp (Over Z)) :
    Nonempty ((Over.pullback a).mapGrp.obj ((Over.pullback g).mapGrp.obj G) ≅
      (Over.pullback b).mapGrp.obj G) := by
  subst h
  exact ⟨((Functor.mapGrpNatIso (Over.pullbackComp a g)).app G ≪≫
    (Functor.mapGrpCompIso).app G).symm⟩

/-- Localizing at a larger submonoid gives a larger subring of the fraction field. -/
private lemma localization_subalgebra_mono {R : Type*} [CommRing R] [IsDomain R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] {M M' : Submonoid R} (hM hM') (h : M ≤ M') :
    Localization.subalgebra K M hM ≤ Localization.subalgebra K M' hM' := by
  intro x hx
  simp only [← Localization.subalgebra.ofField_eq] at hx ⊢
  obtain ⟨a, s, hs, rfl⟩ := hx
  exact ⟨a, s, h hs, rfl⟩

/-- If `A` is the generic fibre of an abelian scheme over a subring `R ⊆ 𝓞_{k,(𝔭)}` of `k`,
then `A` has good reduction at `𝔭`: the base change to `𝓞_{k,(𝔭)}` is the required model. -/
private lemma hasGoodReduction_of_le {k : Type u} [Field k] [NumberField k]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] (𝔭 : HeightOneSpectrum (𝓞 k)) {R : Subalgebra (𝓞 k) k}
    (hR : R ≤ Localization.subalgebra k 𝔭.asIdeal.primeCompl
      𝔭.asIdeal.primeCompl_le_nonZeroDivisors)
    (𝒜 : Grp (Over (Spec (CommRingCat.of R))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).mapGrp.obj 𝒜 ≅
      Grp.mk A) :
    HasGoodReduction k 𝔭 A := by
  let g := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom)
  obtain ⟨e'⟩ := nonempty_mapGrp_pullback_comp_iso
    (Spec.map (CommRingCat.ofHom (algebraMap _ k))) g _ (by rw [← Spec.map_comp]) 𝒜
  obtain ⟨hF, hP, hL, hfib'⟩ := isAbelianScheme_pullbackObj g 𝒜 hfib
  exact ⟨_, hF, hP, hL, hfib', ⟨e' ≪≫ e⟩⟩

/-- An abelian variety `A` over a number field `k` has good reduction at all but finitely many
finite places of `k`. -/
@[faltings "lem_mw_good_reduction_almost_everywhere"]
theorem finite_setOf_not_hasGoodReduction (k : Type u) [Field k] [NumberField k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] :
    {𝔭 : HeightOneSpectrum (𝓞 k) | ¬ HasGoodReduction k 𝔭 A}.Finite := by
  obtain ⟨N, hN, 𝒜, hF, hP, hL, hfib, ⟨e⟩⟩ :=
    exists_isAbelianScheme_localizationAway_pullback_iso k A
  refine (finite_setOf_mem_asIdeal (Int.cast_ne_zero.mpr hN : (N : 𝓞 k) ≠ 0)).subset
    fun 𝔭 h𝔭 => ?_
  by_contra hn
  exact h𝔭 <| hasGoodReduction_of_le 𝔭
    (localization_subalgebra_mono k _ _ (Submonoid.powers_le.mpr hn)) 𝒜 hfib e

end Faltings


/-!
# Good reduction under finite extensions

Let `A` be an abelian variety over a number field `k`, let `𝔭` be a finite place of `k`, and let
`𝒜` be an abelian scheme over the local ring `𝓞_{k,(𝔭)}` together with an isomorphism of group
schemes `𝒜 ×_{𝓞_{k,(𝔭)}} Spec k ≅ A`. Let `L / k` be a finite extension and `𝔓` a finite place of
`L` lying over `𝔭`. The inclusion `k ⊆ L` restricts to a local homomorphism
`φ : 𝓞_{k,(𝔭)} → 𝓞_{L,(𝔓)}`. Then the base change `𝒜 ×_{𝓞_{k,(𝔭)}} Spec 𝓞_{L,(𝔓)}` along
`Spec φ` is an abelian scheme over `𝓞_{L,(𝔓)}`, and its generic fibre is isomorphic, as a group
scheme over `L`, to the base change `A_L = A ×_{Spec k} Spec L`.

## Main results

* `Faltings.isAbelianScheme_pullbackObj_of_liesOver`: the base change of an abelian scheme over
  `𝓞_{k,(𝔭)}` to `𝓞_{L,(𝔓)}` is an abelian scheme whose generic fibre is `A_L`.

## Implementation notes

As in `Faltings.HasGoodReduction`, the local ring `𝓞_{k,(𝔭)}` is the subring
`Localization.subalgebra k 𝔭.asIdeal.primeCompl _` of `k`, and similarly for `𝓞_{L,(𝔓)}` inside
`L`. The map `φ : 𝓞_{k,(𝔭)} →+* 𝓞_{L,(𝔓)}` is given together with its characterising property
`algebraMap 𝓞_{L,(𝔓)} L ∘ φ = algebraMap k L ∘ algebraMap 𝓞_{k,(𝔭)} k`; since
`𝓞_{L,(𝔓)} → L` is injective this determines `φ` uniquely, and it exists because `𝔓` lies over
`𝔭`. Being an abelian scheme is unfolded exactly as in `Faltings.HasGoodReduction`: a group
object in `Over W` whose structure morphism is flat, proper and locally of finite presentation,
all of whose fibres over `AlgebraicGeometry.Scheme.fromSpecResidueField` are proper and
geometrically integral. Group schemes are bundled in `CategoryTheory.Grp`, and base change of
group schemes is `(CategoryTheory.Over.pullback _).mapGrp`.

## References

* [J.-P. Serre, J. Tate, *Good reduction of abelian varieties*][serre1968], §1
* [J. S. Milne, *Abelian varieties*][milneAV]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain

namespace Faltings

/-- Base change of group schemes along equal morphisms gives isomorphic group schemes. -/
private noncomputable def mapGrpPullbackIsoOfEq {W Z : Scheme.{u}} {f f' : Z ⟶ W} (h : f = f')
    (G : Grp (Over W)) : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback f').mapGrp.obj G :=
  h ▸ Iso.refl _

/-- Base change of group schemes along two sides of a commutative square agrees: if
`a ≫ b = c ≫ d`, then pulling back a group scheme along `b` then `a` is isomorphic to pulling
it back along `d` then `c`. -/
private noncomputable def mapGrpPullbackIsoOfComm {W X Y Z : Scheme.{u}} {a : Z ⟶ X}
    {b : X ⟶ W} {c : Z ⟶ Y} {d : Y ⟶ W} (h : a ≫ b = c ≫ d) (G : Grp (Over W)) :
    (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G) ≅
      (Over.pullback c).mapGrp.obj ((Over.pullback d).mapGrp.obj G) :=
  (Functor.mapGrpCompIso (F := Over.pullback b) (G := Over.pullback a)).symm.app G ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp a b).symm).app G ≪≫
    mapGrpPullbackIsoOfEq h G ≪≫
    (Functor.mapGrpNatIso (Over.pullbackComp c d)).app G ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback d) (G := Over.pullback c)).app G

/-- Let `𝒜` be an abelian scheme over `𝓞_{k,(𝔭)}` with generic fibre isomorphic to the abelian
variety `A` over `k`, and let `𝔓` be a finite place of the finite extension `L / k` lying over `𝔭`,
with `φ : 𝓞_{k,(𝔭)} → 𝓞_{L,(𝔓)}` the restriction of `k → L`. Then `𝒜 ×_{𝓞_{k,(𝔭)}} Spec 𝓞_{L,(𝔓)}`
is an abelian scheme over `𝓞_{L,(𝔓)}` whose generic fibre is isomorphic to `A ×_{Spec k} Spec L`
as a group scheme over `L`. -/
@[faltings "lem_mw_good_reduction_extension"]
theorem isAbelianScheme_pullbackObj_of_liesOver (k L : Type u) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L]
    (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 L))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    (φ : Localization.subalgebra k 𝔭.asIdeal.primeCompl
        𝔭.asIdeal.primeCompl_le_nonZeroDivisors →+*
      Localization.subalgebra L 𝔓.asIdeal.primeCompl
        𝔓.asIdeal.primeCompl_le_nonZeroDivisors)
    (hφ : (algebraMap (Localization.subalgebra L 𝔓.asIdeal.primeCompl
        𝔓.asIdeal.primeCompl_le_nonZeroDivisors) L).comp φ =
      (algebraMap k L).comp (algebraMap (Localization.subalgebra k 𝔭.asIdeal.primeCompl
        𝔭.asIdeal.primeCompl_le_nonZeroDivisors) k))
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom]
    (𝒜 : Grp (Over (Spec (CommRingCat.of (Localization.subalgebra k 𝔭.asIdeal.primeCompl
        𝔭.asIdeal.primeCompl_le_nonZeroDivisors)))))
    [Flat 𝒜.X.hom] [IsProper 𝒜.X.hom] [LocallyOfFinitePresentation 𝒜.X.hom]
    (hfib : ∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (Localization.subalgebra k 𝔭.asIdeal.primeCompl
          𝔭.asIdeal.primeCompl_le_nonZeroDivisors) k)))).mapGrp.obj 𝒜 ≅ Grp.mk A) :
    Flat ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X.hom ∧
      IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X.hom ∧
      LocallyOfFinitePresentation
        ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X.hom ∧
      (∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj
          ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X).hom ∧
        GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj
          ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X).hom) ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
          (Localization.subalgebra L 𝔓.asIdeal.primeCompl
            𝔓.asIdeal.primeCompl_le_nonZeroDivisors) L)))).mapGrp.obj
          ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.obj
          (Grp.mk A)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    isAbelianScheme_pullbackObj (Spec.map (CommRingCat.ofHom φ)) 𝒜 hfib
  exact ⟨h₁, h₂, h₃, h₄, ⟨mapGrpPullbackIsoOfComm
    (by simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]) 𝒜 ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.mapIso e⟩⟩

end Faltings
