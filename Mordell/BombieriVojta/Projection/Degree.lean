module
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.Curve.DegreeOverRationalSubfield
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme

/-!
# The degree of the projections `π_a`

Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k` of
characteristic zero (a number field, or an algebraic extension of `ℚ`), `D` a divisor of degree
`N ≥ 2g + 1` supported on closed points (for instance `N P` for a `k`-rational point `P`), and
`x₀, …, xₙ` a `k`-basis of the Riemann–Roch space `L(D) = H⁰(C, 𝒪(D))` inside the function field
`k(C)`. Write `ξ_a = x_a / x₀`, the pull-back of the affine coordinate of `ℙ¹` by the projection
`π_a = (x₀ : x_a) : C → ℙ¹`. If the basis satisfies (G1), that is `x₀` and `x_a` have no common
zero as sections of `𝒪(D)`, then for every `a ∈ {1, …, n}` the divisor of zeros of `ξ_a` is the
divisor of zeros of the section `x_a`, of degree `deg D = N`, so `[k(C) : k(ξ_a)] = N`.

## Main results

* `Faltings.BombieriSiegel.finrank_adjoin_div_eq`: under (G1), `[k(C) : k⟮x_a / x₀⟯] = N` for
  every `a ≠ 0`.
* `Faltings.BombieriSiegel.div_notMem_range_algebraMap`: two distinct members of a linearly
  independent family have non-constant quotient.
* `Faltings.BombieriSiegel.ord_eq_zero_of_not_isClosed`: on a curve, every rational function has
  order zero at the generic point, the one non-closed point.
* `Faltings.BombieriSiegel.isClosed_singleton_of_residueDegree_eq_one`: a point of residue
  degree one is closed.
* `Faltings.BombieriSiegel.isClosed_of_mem_support_smul`,
  `Faltings.BombieriSiegel.finsum_smul_mul_residueDegree`: for a divisor `P₁` of degree one on
  closed points, `N P₁` is a divisor of degree `N` on closed points.
* `Faltings.BombieriSiegel.ord_add_nonneg_of_span_eq`: a basis of `L(D)` lies in `L(D)` at every
  point, not only at the closed ones.

## Implementation notes

As in `Faltings.BombieriSiegel.SatisfiesG1`, sections of `𝒪(D)` are rational functions: `D` is a
`C →₀ ℤ`, `L(D)` is `{g | g = 0 ∨ ∀ Q closed, 0 ≤ ord_Q g + D(Q)}` (the form of
`Faltings.BombieriSiegel.IsGenericBasis.span_eq`), its degree is `∑ᶠ Q, D(Q) · [κ(Q) : k]`, and
`k(C)` is a `k`-algebra through `AlgebraicGeometry.functionFieldAlgebra k f`. The index
`a ∈ {1, …, n}` is `a : Fin (n + 1)` with `a ≠ 0`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 8, pp. 629–630
-/

open AlgebraicGeometry IntermediateField

universe u

/- Mathlib's `[IsSimpleAddGroup G] [IsNilpotent G] : AddCommGroup G` instance is tried first for
`AddCommGroup X.functionField` and, through `IsVariety.toIsIntegral` with an unknown base field,
enumerates every `Field` instance before failing: it is switched off in this file. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Faltings.BombieriSiegel

/-- Two distinct members of a linearly independent family have non-constant quotient. -/
public lemma div_notMem_range_algebraMap {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} {x : ι → K} (hli : LinearIndependent k x) {i j : ι} (hij : i ≠ j) :
    x i / x j ∉ Set.range (algebraMap k K) := by
  rintro ⟨c, hc⟩
  refine hli.notMem_span_image (s := {j}) hij ?_
  rw [Set.image_singleton, Submodule.mem_span_singleton]
  exact ⟨c, by rw [Algebra.smul_def, hc, div_mul_cancel₀ _ (hli.ne_zero j)]⟩

open CategoryTheory in
/-- A point of residue degree one of a scheme locally of finite type over a field is closed. -/
public lemma isClosed_singleton_of_residueDegree_eq_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X} (hx : f.residueDegree x = 1) :
    IsClosed ({x} : Set X) := by
  have h := Stacks.Chow.residueDegree_eq_finrank_residueField k f x
  rw [hx] at h
  refine isClosed_singleton_of_module_finite_residueField f x ?_
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  exact Module.finite_of_finrank_eq_succ h.symm

/-- A multiple `m P₁` of a divisor supported on closed points is supported on closed points. -/
public lemma isClosed_of_mem_support_smul {X : Scheme.{u}} {P₁ : X →₀ ℤ}
    (hP₁cl : ∀ Q ∈ P₁.support, IsClosed ({Q} : Set X)) (m : ℤ) :
    ∀ Q ∈ (m • P₁).support, IsClosed ({Q} : Set X) := fun Q hQ =>
  hP₁cl Q (Finsupp.support_smul hQ)

/-- A multiple `m P₁` of a divisor `P₁` of degree one has degree `m`. -/
public lemma finsum_smul_mul_residueDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {P₁ : X →₀ ℤ}
    (hP₁ : ∑ᶠ Q : X, P₁ Q * (f.residueDegree Q : ℤ) = 1) (m : ℤ) :
    ∑ᶠ Q : X, (m • P₁) Q * (f.residueDegree Q : ℤ) = m := by
  simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc]
  rw [← mul_finsum, hP₁, mul_one]

section

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f]
  [IsLocallyNoetherian C]

/-- On a curve, the order of vanishing at a non-closed point is zero. -/
public lemma ord_eq_zero_of_not_isClosed (g : C.functionField) {Q : C}
    (hQ : ¬IsClosed ({Q} : Set C)) : C.ord g Q = 0 := by
  obtain rfl : Q = genericPoint C := by
    by_contra h
    exact hQ (Faltings.FunctionField.isClosed_singleton_of_ne_genericPoint k f h)
  exact Scheme.ord_eq_zero_of_coheight_neq_one (FunctionField.coheight_genericPoint_ne_one C) g

/-- Membership in `L(D)` at the closed points, for `D` supported on closed points, gives it at
every point: at the generic point both `ord g` and `D` vanish. -/
public lemma ord_add_nonneg_of_forall_isClosed {D : C →₀ ℤ}
    (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C)) {g : C.functionField}
    (hg : ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q) (Q : C) :
    0 ≤ C.ord g Q + D Q := by
  by_cases hQ : IsClosed ({Q} : Set C)
  · exact hg Q hQ
  · rw [ord_eq_zero_of_not_isClosed f g hQ, Finsupp.notMem_support_iff.1 (mt (hDcl Q) hQ),
      add_zero]

/-- A basis `x` of `L(D)` in the form of `Faltings.BombieriSiegel.IsGenericBasis.span_eq`, with
`D` supported on closed points, has `0 ≤ ord_Q (x i) + D(Q)` at every point `Q`. -/
public lemma ord_add_nonneg_of_span_eq {D : C →₀ ℤ}
    (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C)) {ι : Type*} {x : ι → C.functionField}
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q}) (i : ι) (Q : C) :
    0 ≤ C.ord (x i) Q + D Q :=
  letI := functionFieldAlgebra k f
  ord_add_nonneg_of_forall_isClosed f hDcl
    (((Set.ext_iff.1 hspan (x i)).1 (Submodule.subset_span ⟨i, rfl⟩)).resolve_left
      (hli.ne_zero i)) Q

/-- For `g, h ≠ 0` and an integer `d` with `div(g) + d ≥ 0`, `div(h) + d ≥ 0` at `Q` and not both
positive, the order of `g / h` at `Q`, if positive, is `ord_Q g + d`: the divisor of zeros of
`g / h` is `div(g) + d` at `Q`. -/
public lemma toNat_ord_div_eq [IsIntegral C] {g h : C.functionField} (hg : g ≠ 0) (hh : h ≠ 0)
    {Q : C} {d : ℤ} (hgd : 0 ≤ C.ord g Q + d) (hhd : 0 ≤ C.ord h Q + d)
    (hgh : ¬(0 < C.ord h Q + d ∧ 0 < C.ord g Q + d)) :
    ((C.ord (g / h) Q).toNat : ℤ) = C.ord g Q + d := by
  rw [div_eq_mul_inv, Scheme.ord_mul hg (inv_ne_zero hh), Stacks.Chow.ord_inv_functionField hh]
  omega

variable [CharZero k] [IsProjectiveVariety k f] [Smooth f] [GeometricallyIntegral f]

/-- For a non-constant `ς`, the sum `∑ᶠ Q, (ord_Q ς)⁺ · [κ(Q) : k]` in `ℤ` defining the degree of
its divisor of zeros has finite support and equals `[k(C) : k⟮ς⟯]`. -/
public lemma finrank_adjoin_eq_finsum_ord_int (ς : C.functionField)
    (hς : letI := functionFieldAlgebra k f; ς ∉ Set.range (algebraMap k C.functionField)) :
    letI := functionFieldAlgebra k f
    (Function.support fun Q => ((C.ord ς Q).toNat : ℤ) * f.residueDegree Q).Finite ∧
      (Module.finrank k⟮ς⟯ C.functionField : ℤ) =
        ∑ᶠ Q, ((C.ord ς Q).toNat : ℤ) * f.residueDegree Q := by
  let := functionFieldAlgebra k f
  obtain ⟨hfd, h⟩ := Faltings.FunctionField.finrank_adjoin_eq_finsum_ord k f ς hς
  have hpos : 0 < Module.finrank k⟮ς⟯ C.functionField := Module.finrank_pos
  have hA : (Function.support fun Q => (C.ord ς Q).toNat * f.residueDegree Q).Finite := by
    by_contra hA
    rw [finsum_of_infinite_support hA] at h
    omega
  refine ⟨hA.subset fun Q hQ => by simpa using hQ, ?_⟩
  rw [h]
  exact ((Nat.castAddMonoidHom ℤ).map_finsum hA).trans (by simp)

/-- A principal divisor of a non-constant function has degree zero: the divisors of zeros of `g`
and of `g⁻¹` both have degree `[k(C) : k⟮g⟯] = [k(C) : k⟮g⁻¹⟯]`. -/
public lemma finsum_ord_mul_residueDegree_eq_zero_of_notMem_range (g : C.functionField)
    (hg : letI := functionFieldAlgebra k f; g ∉ Set.range (algebraMap k C.functionField)) :
    (Function.support fun Q => C.ord g Q * (f.residueDegree Q : ℤ)).Finite ∧
      ∑ᶠ Q, C.ord g Q * (f.residueDegree Q : ℤ) = 0 := by
  let := functionFieldAlgebra k f
  have hg0 : g ≠ 0 := fun h => hg ⟨0, by simp [h]⟩
  have hgi : g⁻¹ ∉ Set.range (algebraMap k C.functionField) := fun ⟨c, hc⟩ =>
    hg ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
  obtain ⟨hA, h1⟩ := finrank_adjoin_eq_finsum_ord_int f g hg
  obtain ⟨hB, h2⟩ := finrank_adjoin_eq_finsum_ord_int f g⁻¹ hgi
  have hadj : k⟮g⁻¹⟯ = k⟮g⟯ := le_antisymm
    (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self k g)))
    (adjoin_simple_le_iff.2 (by simpa using inv_mem (mem_adjoin_simple_self k g⁻¹)))
  have hpt : (fun Q => C.ord g Q * (f.residueDegree Q : ℤ)) = fun Q =>
      ((C.ord g Q).toNat : ℤ) * f.residueDegree Q -
        ((C.ord g⁻¹ Q).toNat : ℤ) * f.residueDegree Q := by
    funext Q
    rw [Stacks.Chow.ord_inv_functionField hg0, ← sub_mul, Int.toNat_sub_toNat_neg]
  rw [hpt]
  refine ⟨(hA.union hB).subset (Function.support_sub _ _), ?_⟩
  rw [finsum_sub_distrib hA hB, ← h1, ← h2, hadj, sub_self]

/-- Every principal divisor has degree zero, provided `k(C)` has a non-constant element `h`: for
a constant `g = c`, the divisor of `g` is that of `c h` minus that of `h`. -/
public lemma finsum_ord_mul_residueDegree_eq_zero {g : C.functionField} (hg0 : g ≠ 0)
    {h : C.functionField}
    (hh : letI := functionFieldAlgebra k f; h ∉ Set.range (algebraMap k C.functionField)) :
    (Function.support fun Q => C.ord g Q * (f.residueDegree Q : ℤ)).Finite ∧
      ∑ᶠ Q, C.ord g Q * (f.residueDegree Q : ℤ) = 0 := by
  let := functionFieldAlgebra k f
  by_cases hg : g ∈ Set.range (algebraMap k C.functionField)
  · obtain ⟨c, rfl⟩ := hg
    have hc : c ≠ 0 := by rintro rfl; exact hg0 (map_zero _)
    have hh0 : h ≠ 0 := fun h0 => hh ⟨0, by simp [h0]⟩
    have hgh : algebraMap k C.functionField c * h ∉ Set.range (algebraMap k C.functionField) := by
      rintro ⟨d, hd⟩
      refine hh ⟨d / c, ?_⟩
      rw [map_div₀, hd, mul_div_cancel_left₀ _ hg0]
    obtain ⟨hf1, hs1⟩ := finsum_ord_mul_residueDegree_eq_zero_of_notMem_range f _ hgh
    obtain ⟨hf2, hs2⟩ := finsum_ord_mul_residueDegree_eq_zero_of_notMem_range f h hh
    have hpt : (fun Q => C.ord (algebraMap k C.functionField c) Q * (f.residueDegree Q : ℤ)) =
        fun Q => C.ord (algebraMap k C.functionField c * h) Q * (f.residueDegree Q : ℤ) -
          C.ord h Q * (f.residueDegree Q : ℤ) := by
      funext Q
      rw [Scheme.ord_mul hg0 hh0]
      ring
    rw [hpt]
    exact ⟨(hf1.union hf2).subset (Function.support_sub _ _), by
      rw [finsum_sub_distrib hf1 hf2, hs1, hs2, sub_self]⟩
  · exact finsum_ord_mul_residueDegree_eq_zero_of_notMem_range f g hg

open Classical in
/-- The degree of `ξ_a = ℓ_a / ℓ₀` is the degree of `D` on the closed points, when `ℓ₀, ℓ_a` lie
in `L(D)` (checked at closed points) and have no common zero as sections of `𝒪(D)`: the divisor
of zeros of `ξ_a` is `div(ℓ_a) + D` on the closed points, and `div(ℓ_a)` has degree zero. -/
private lemma finrank_adjoin_div_eq_finsum (D : C →₀ ℤ) {n : ℕ} {ℓ : Fin (n + 1) → C.functionField}
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k ℓ)
    (hmem : ∀ i Q, IsClosed ({Q} : Set C) → 0 ≤ C.ord (ℓ i) Q + D Q)
    (hG1 : SatisfiesG1 k f D ℓ) {a : Fin (n + 1)} (ha : a ≠ 0) :
    letI := functionFieldAlgebra k f
    (Module.finrank k⟮ℓ a / ℓ 0⟯ C.functionField : ℤ) =
      ∑ᶠ Q, (if IsClosed ({Q} : Set C) then D Q else 0) * f.residueDegree Q := by
  classical
  let := functionFieldAlgebra k f
  have hξ := div_notMem_range_algebraMap hli ha
  let E : C → ℤ := fun Q => (if IsClosed ({Q} : Set C) then D Q else 0) * f.residueDegree Q
  have hpt (Q : C) : ((C.ord (ℓ a / ℓ 0) Q).toNat : ℤ) * f.residueDegree Q =
      C.ord (ℓ a) Q * f.residueDegree Q + E Q := by
    by_cases hQ : IsClosed ({Q} : Set C)
    · simp only [E, hQ, ↓reduceIte, toNat_ord_div_eq (hli.ne_zero a) (hli.ne_zero 0)
        (hmem a Q hQ) (hmem 0 Q hQ) (hG1 a ha Q hQ)]
      ring
    · simp only [E, hQ, ↓reduceIte, ord_eq_zero_of_not_isClosed f _ hQ]
      simp
  have hf2 : (Function.support E).Finite :=
    D.support.finite_toSet.subset <| Function.support_subset_iff'.2 fun Q hQ => by
      simp only [E, Finsupp.notMem_support_iff.1 hQ, ite_self, zero_mul]
  obtain ⟨-, hrel⟩ := finrank_adjoin_eq_finsum_ord_int f _ hξ
  obtain ⟨hf1, hs1⟩ := finsum_ord_mul_residueDegree_eq_zero f (hli.ne_zero a) hξ
  rw [hrel, funext hpt, finsum_add_distrib hf1 hf2, hs1, zero_add]

end

/-- Let `C` be a smooth projective geometrically integral curve of genus `g ≥ 2` over a field `k`
of characteristic zero, `D` a divisor of degree `N ≥ 2g + 1` supported on closed points (for
instance `N P` for a divisor `P` of degree one), and `x₀, …, xₙ` a `k`-basis of `L(D)` satisfying
(G1). Then for every `a ≠ 0`, `[k(C) : k(x_a / x₀)] = N`. -/
@[faltings "lem_bvs_projection_degree"]
public theorem finrank_adjoin_div_eq (k : Type u) [Field k] [CharZero k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    [GeometricallyIntegral f] [IsLocallyNoetherian C] (hg : 2 ≤ genus f)
    (D : C →₀ ℤ) (hDcl : ∀ Q ∈ D.support, IsClosed ({Q} : Set C))
    (N : ℕ) (hN : 2 * genus f + 1 ≤ N) (hD : ∑ᶠ Q : C, D Q * (f.residueDegree Q : ℤ) = N)
    {n : ℕ} (x : Fin (n + 1) → C.functionField)
    (hli : letI := functionFieldAlgebra k f; LinearIndependent k x)
    (hspan : letI := functionFieldAlgebra k f
      ((Submodule.span k (Set.range x) : Submodule k C.functionField) : Set C.functionField) =
        {g | g = 0 ∨ ∀ Q : C, IsClosed ({Q} : Set C) → 0 ≤ C.ord g Q + D Q})
    (hG1 : SatisfiesG1 k f D x) (a : Fin (n + 1)) (ha : a ≠ 0) :
    letI := functionFieldAlgebra k f
    Module.finrank k⟮x a / x 0⟯ C.functionField = N := by
  classical
  let := functionFieldAlgebra k f
  have h := finrank_adjoin_div_eq_finsum f D hli (fun i =>
    ((Set.ext_iff.1 hspan (x i)).1 (Submodule.subset_span ⟨i, rfl⟩)).resolve_left
      (hli.ne_zero i)) hG1 ha
  have hE : (fun Q => (if IsClosed ({Q} : Set C) then D Q else 0) * (f.residueDegree Q : ℤ)) =
      fun Q => D Q * f.residueDegree Q := by
    funext Q
    split_ifs with hQ
    · rfl
    · rw [Finsupp.notMem_support_iff.1 (mt (hDcl Q) hQ)]
  rw [hE, hD] at h
  exact_mod_cast h

end Faltings.BombieriSiegel
