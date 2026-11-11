module

public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.ThetaPolarization
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import Mordell.NeronTate.Pairing.Basic
public import Mordell.BombieriVojta.Projection.GenericBasis
public import Mordell.CurveProduct.VojtaClass
public import Mordell.BombieriVojta.DerivativeEstimate.Lemma6
public import Mordell.Analysis.SphereCover
public import Mordell.BombieriVojta.Conclusion.Theorem1
public import Mordell.BombieriVojta.Mumford.ExponentialGrowth
public import Mordell.NeronTate.JacobianLattice
public import Mordell.MordellWeil.Main

/-!
# Vojta's theorem

Let `C` be a smooth projective curve of genus `g ≥ 2` over a number field `k`, with a divisor
`P` of degree one, Jacobian `J`, Abel–Jacobi map `j = j_P`, Néron form `⟨ , ⟩` of the theta class
on `J(k̄)` and norm `|z| = √⟨j z, j z⟩` for `z ∈ C(k̄)`, together with the standing data of
Bombieri's Sections 9 and 10 (a generic basis `x` of `H⁰(C, 𝒪(N P))` giving `φ_{NP}`,
`ψ = φ_{NP} × φ_{NP}`, and a basis `y` of `H⁰(C × C, 𝒪(B))` generic for the projections giving
`φ_B`). Then there is a constant `γ > 1` such that for every finite extension `K` of `k` the set
of `z ∈ C(K)` with `|z| ≥ γ` is finite, of cardinality at most `7 ^ ρ (1 + log γ / log 2)`,
where `ρ` is the rank of the Mordell–Weil group `J(K)`.

The proof is Mumford's: cover the unit sphere of `J(K) ⊗ ℝ` by `7 ^ ρ` caps of small angle; in
each cap, the points of norm at least `γ` grow exponentially by Mumford's gap principle, while
Bombieri's Theorem 1 forbids two of them in shells `|w| ≥ γ |z|`.

## Main results

* `Faltings.finite_setOf_le_neronNorm_abelJacobi`: Vojta's theorem (Bombieri's Theorem 2).

## Implementation notes

The setting is that of `Faltings.exists_neronPairing_div_le` (the angle inequality): the curve
`X : Faltings.CurveWithDegreeOneDivisor k`, its Jacobian `A`, the Abel–Jacobi map `j` and the
reduced effective Cartier divisor `D` supported on `Faltings.thetaDivisor` define
`Faltings.neronPairing` on `J(k̄)`, and the standing data live over `k` on `C` and `C ×_k C`.

A finite extension of `k` is an intermediate field `K` of `k̄ / k`, finite over `k`; every finite
extension embeds in `k̄` over `k`. As in `Faltings.finite_setOf_neronNorm_abelJacobi_lt`, `C(K)`
is the set of `z ∈ C(k̄)` whose underlying morphism factors through `Spec k̄ ⟶ Spec K`. The rank
of `J(K)` is `Module.finrank ℤ (Additive J(K))`, as in
`Faltings.exists_posDef_extension_neronPairing`. The bound on the number of points is stated
together with the finiteness of the set, so that it is not read through the junk value `0` of
`Set.ncard` on an infinite set.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 10, Theorem 2
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Faltings

open BombieriSiegel

section

open Module Metric RealInnerProductSpace
open scoped TensorProduct

/-- Inside one cone, a finite family of points of norm at least `γ`, growing like `2 ^ m` along
any chain ordered by norm and never in two shells `|w| ≥ γ |z|`, has at most
`1 + log γ / log 2` elements. -/
private lemma card_le_of_cone {ι : Type*} (pair : ι → ι → ℝ) (T : Finset ι) (γ c : ℝ)
    (hγ : 1 < γ) (hc : c ≤ γ)
    (hS : ∀ z ∈ T, γ ≤ √(pair z z))
    (hcone : ∀ z ∈ T, ∀ w ∈ T, 3 / 4 * √(pair z z) * √(pair w w) < pair z w)
    (hgap : ∀ (m : ℕ) (z : Fin (m + 1) → ι), c ≤ √(pair (z 0) (z 0)) →
      (∀ i : Fin m, √(pair (z i.castSucc) (z i.castSucc)) ≤ √(pair (z i.succ) (z i.succ))) →
      (∀ i : Fin m, z i.castSucc ≠ z i.succ) →
      (∀ i : Fin m, 3 / 4 * √(pair (z i.castSucc) (z i.castSucc)) *
          √(pair (z i.succ) (z i.succ)) < pair (z i.castSucc) (z i.succ)) →
      2 ^ m * √(pair (z 0) (z 0)) ≤ √(pair (z (Fin.last m)) (z (Fin.last m))))
    (h1 : ∀ z w, γ ≤ √(pair z z) → γ * √(pair z z) ≤ √(pair w w) →
      pair z w ≤ 3 / 4 * √(pair z z) * √(pair w w)) :
    (T.card : ℝ) ≤ 1 + Real.log γ / Real.log 2 := by
  have hlog : 0 < Real.log γ / Real.log 2 :=
    div_pos (Real.log_pos hγ) (Real.log_pos one_lt_two)
  obtain ⟨n, hn⟩ : ∃ n, T.card = n := ⟨_, rfl⟩
  cases n with
  | zero => rw [hn]; push_cast; linarith
  | succ m =>
    let e : Fin (m + 1) ≃ T := (T.equivFin.trans (finCongr hn)).symm
    let f : Fin (m + 1) → ℝ := fun i => √(pair (e i) (e i))
    let σ := Tuple.sort f
    let z : Fin (m + 1) → ι := fun i => (e (σ i) : ι)
    have hzT : ∀ i, z i ∈ T := fun i => (e (σ i)).2
    have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
    have hinj : Function.Injective z := fun a b h =>
      σ.injective (e.injective (Subtype.ext h))
    have hg := hgap m z (hc.trans (hS _ (hzT 0)))
      (fun i => hmono (Fin.castSucc_le_succ i))
      (fun i => hinj.ne (Fin.castSucc_lt_succ (i := i)).ne)
      (fun i => hcone _ (hzT _) _ (hzT _))
    have h0 : γ ≤ √(pair (z 0) (z 0)) := hS _ (hzT 0)
    have hlt : √(pair (z (Fin.last m)) (z (Fin.last m))) < γ * √(pair (z 0) (z 0)) := by
      by_contra hle
      have := h1 _ _ h0 (not_lt.1 hle)
      linarith [hcone _ (hzT 0) _ (hzT (Fin.last m))]
    have hpos : 0 < √(pair (z 0) (z 0)) := by linarith
    have h2 : (2 : ℝ) ^ m < γ := by
      by_contra h
      push Not at h
      nlinarith
    have : (m : ℝ) * Real.log 2 < Real.log γ := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) h2
    have := (lt_div_iff₀ (Real.log_pos one_lt_two)).2 this
    rw [hn]
    push_cast
    linarith

/-- **Counting by cones.** Let `v : ι → E` map a set `S` of points into a finite-dimensional real
inner product space, with `pair z w = ⟪v z, v w⟫` on `S`, and let every point of `S` have norm
`√(pair z z)` at least `γ > 1`. If chains ordered by norm in a narrow cone grow like `2 ^ m` from
norm `c ≤ γ` on, and two points in shells `|w| ≥ γ |z| ≥ γ²` are never close in angle, then `S`
is finite with at most `7 ^ dim E * (1 + log γ / log 2)` elements. -/
private lemma ncard_le_of_inner_eq {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (pair : ι → ι → ℝ) (v : ι → E) (S : Set ι) (γ c : ℝ)
    (hγ : 1 < γ) (hc : c ≤ γ)
    (hv : ∀ z ∈ S, ∀ w ∈ S, pair z w = ⟪v z, v w⟫)
    (hS : ∀ z ∈ S, γ ≤ √(pair z z))
    (hgap : ∀ (m : ℕ) (z : Fin (m + 1) → ι), c ≤ √(pair (z 0) (z 0)) →
      (∀ i : Fin m, √(pair (z i.castSucc) (z i.castSucc)) ≤ √(pair (z i.succ) (z i.succ))) →
      (∀ i : Fin m, z i.castSucc ≠ z i.succ) →
      (∀ i : Fin m, 3 / 4 * √(pair (z i.castSucc) (z i.castSucc)) *
          √(pair (z i.succ) (z i.succ)) < pair (z i.castSucc) (z i.succ)) →
      2 ^ m * √(pair (z 0) (z 0)) ≤ √(pair (z (Fin.last m)) (z (Fin.last m))))
    (h1 : ∀ z w, γ ≤ √(pair z z) → γ * √(pair z z) ≤ √(pair w w) →
      pair z w ≤ 3 / 4 * √(pair z z) * √(pair w w)) :
    S.Finite ∧ (S.ncard : ℝ) ≤ 7 ^ finrank ℝ E * (1 + Real.log γ / Real.log 2) := by
  have hB : 0 ≤ 1 + Real.log γ / Real.log 2 := by
    linarith [div_pos (Real.log_pos hγ) (Real.log_pos one_lt_two)]
  have hnorm : ∀ z ∈ S, √(pair z z) = ‖v z‖ := fun z hz => by
    rw [hv z hz z hz, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hvpos : ∀ z ∈ S, 0 < ‖v z‖ := fun z hz => by
    linarith [hnorm z hz ▸ hS z hz]
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hρ
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    have hSe : S = ∅ := Set.eq_empty_of_forall_notMem fun z hz => by
      have := hvpos z hz
      rw [Subsingleton.elim (v z) 0, norm_zero] at this
      exact lt_irrefl _ this
    subst hSe
    simp only [Set.finite_empty, Set.ncard_empty, Nat.cast_zero, true_and]
    positivity
  obtain ⟨M, C, hM, -, hcov, hC⟩ := exists_sphere_cover_inner_gt hρ
  let u : ι → E := fun z => ‖v z‖⁻¹ • v z
  let Si : Fin M → Set ι := fun i => {z | z ∈ S ∧ u z ∈ C i}
  have hSi : S ⊆ ⋃ i, Si i := fun z hz => by
    have hu : u z ∈ sphere (0 : E) 1 := by
      simp only [u, mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm (norm_pos_iff.1 (hvpos z hz))
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hu)
    exact Set.mem_iUnion.2 ⟨i, hz, hi⟩
  have hcone : ∀ i, ∀ z ∈ Si i, ∀ w ∈ Si i, 3 / 4 * √(pair z z) * √(pair w w) < pair z w := by
    intro i z hz w hw
    have h := hC i _ hz.2 _ hw.2
    simp only [u, real_inner_smul_left, real_inner_smul_right] at h
    rw [lt_inv_mul_iff₀ (hvpos w hw.1), lt_inv_mul_iff₀ (hvpos z hz.1)] at h
    rw [hnorm z hz.1, hnorm w hw.1, hv z hz.1 w hw.1]
    linarith
  have hcard : ∀ i (T : Finset ι), (T : Set ι) ⊆ Si i →
      (T.card : ℝ) ≤ 1 + Real.log γ / Real.log 2 := fun i T hT =>
    card_le_of_cone pair T γ c hγ hc (fun z hz => hS z (hT hz).1)
      (fun z hz w hw => hcone i z (hT hz) w (hT hw)) hgap h1
  have hfin : ∀ i, (Si i).Finite := fun i => by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈1 + Real.log γ / Real.log 2⌉₊ + 1)
    have h := hcard i T hT
    rw [hTc] at h
    push_cast at h
    linarith [Nat.le_ceil (1 + Real.log γ / Real.log 2)]
  have hncard : ∀ i, ((Si i).ncard : ℝ) ≤ 1 + Real.log γ / Real.log 2 := fun i => by
    rw [Set.ncard_eq_toFinset_card _ (hfin i)]
    exact hcard i _ (hfin i).coe_toFinset.subset
  refine ⟨(Set.finite_iUnion hfin).subset hSi, ?_⟩
  calc (S.ncard : ℝ) ≤ ((⋃ i, Si i).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hSi (Set.finite_iUnion hfin)
    _ ≤ ∑ i, ((Si i).ncard : ℝ) := by exact_mod_cast Set.ncard_iUnion_le_of_fintype Si
    _ ≤ ∑ _i : Fin M, (1 + Real.log γ / Real.log 2) := Finset.sum_le_sum fun i _ => hncard i
    _ = M * (1 + Real.log γ / Real.log 2) := by simp; ring
    _ ≤ 7 ^ finrank ℝ E * (1 + Real.log γ / Real.log 2) := by
        gcongr
        exact_mod_cast hM

/-- Vojta's theorem over one finite extension `K ⊆ k̄` of `k`, for a constant `γ > 1` at which
the gap principle (from norm `c ≤ γ` on) and Bombieri's Theorem 1 hold. -/
private lemma finite_setOf_le_of_finiteDimensional {k : Type u} [Field k] [NumberField k]
    (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f) (hg : 2 ≤ genus X.f)
    (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j) (D : A.J.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ)
    (hpair : ∀ z w, pair z w = neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j)))
    (γ c : ℝ) (hγ : 1 < γ) (hc : c ≤ γ)
    (hgap : ∀ (m : ℕ)
        (z : Fin (m + 1) → (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶
          Over.mk X.f)),
      c ≤ √(pair (z 0) (z 0)) →
      (∀ i : Fin m, √(pair (z i.castSucc) (z i.castSucc)) ≤ √(pair (z i.succ) (z i.succ))) →
      (∀ i : Fin m, z i.castSucc ≠ z i.succ) →
      (∀ i : Fin m, 3 / 4 * √(pair (z i.castSucc) (z i.castSucc)) *
          √(pair (z i.succ) (z i.succ)) < pair (z i.castSucc) (z i.succ)) →
      2 ^ m * √(pair (z 0) (z 0)) ≤ √(pair (z (Fin.last m)) (z (Fin.last m))))
    (h1 : ∀ z w, γ ≤ √(pair z z) → γ * √(pair z z) ≤ √(pair w w) →
      pair z w ≤ 3 / 4 * √(pair z z) * √(pair w w))
    (K : IntermediateField k kbar) [FiniteDimensional k K] :
    haveI := A.isAbelianVariety
    letI := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
    letI : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :=
      Hom.commGroup
    let ρ := Module.finrank ℤ
      (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J))
    let S := {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f |
      (∃ q : Spec (.of K) ⟶ X.C,
        z.left = Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ q) ∧
      γ ≤ √(pair z z)}
    S.Finite ∧ (S.ncard : ℝ) ≤ 7 ^ ρ * (1 + Real.log γ / Real.log 2) := by
  classical
  have := A.isAbelianVariety
  let _ := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
  let _ : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :=
    Hom.commGroup
  intro ρ S
  have : NumberField K := NumberField.of_module_finite k K
  -- the Euclidean space `ℝ ⊗ J(K)`
  let M := Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J)
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.2
    (AddGroup.fg_iff_mul_fg.2 (group_fg_points_of_numberField K A.J))
  let jV : M →ₗ[ℤ] ℝ ⊗[ℤ] M := TensorProduct.mk ℤ ℝ M 1
  have hbc : IsBaseChange ℝ jV := TensorProduct.isBaseChange ℤ M ℝ
  obtain ⟨Bf, hBf, hsymm, hpos⟩ :=
    exists_posDef_extension_neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar K jV hbc
  let core : InnerProductSpace.Core ℝ (ℝ ⊗[ℤ] M) :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by simpa using hsymm.eq y x
      re_inner_nonneg := fun x => by simpa using hpos.nonneg x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        simp_all }
  let _ : NormedAddCommGroup (ℝ ⊗[ℤ] M) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (ℝ ⊗[ℤ] M) := InnerProductSpace.ofCore core.toCore
  have hinner : ∀ a b : ℝ ⊗[ℤ] M, ⟪a, b⟫ = Bf a b := fun _ _ => rfl
  -- the class in `J(K)` of a point of `C(K)`
  let CK : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → Prop :=
    fun z => ∃ q : Spec (.of K) ⟶ X.C,
      z.left = Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ q
  have hw : ∀ z (hz : CK z), (hz.choose ≫ j.left) ≫ A.J.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := fun z hz => by
    refine (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))).1 ?_
    have hjw : j.left ≫ A.J.hom = X.f := Over.w j
    have hzw : z.left ≫ X.f = Spec.map (CommRingCat.ofHom (algebraMap k kbar)) := Over.w z
    rw [Category.assoc, hjw, ← Category.assoc, ← hz.choose_spec, hzw, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let xOf : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → M :=
    fun z => if hz : CK z then .ofMul (Over.homMk (hz.choose ≫ j.left) (hw z hz)) else 0
  have hres : ∀ z, CK z →
      (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) (by
          simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]) ≫ (xOf z).toMul) = z ≫ j := fun z hz => by
    simp only [xOf, hz, ↓reduceDIte]
    ext
    simp only [Over.comp_left, Over.homMk_left, toMul_ofMul]
    rw [← Category.assoc, ← hz.choose_spec]
  have hv : ∀ z ∈ S, ∀ w ∈ S, pair z w = ⟪jV (xOf z), jV (xOf w)⟫ := fun z hz w hw' => by
    rw [hinner, hBf, hpair]
    simp only [hres z hz.1, hres w hw'.1]
  have h := ncard_le_of_inner_eq pair (fun z => jV (xOf z)) S γ c hγ hc hv (fun z hz => hz.2)
    hgap h1
  rwa [hbc.finrank_eq] at h

end

attribute [local instance] MvPolynomial.gradedAlgebra in
open Classical in
/-- **Vojta's theorem** (Bombieri's Theorem 2). Let `X = (C, P)` be a curve of genus `g ≥ 2`
over a number field `k` with a divisor `P` of degree one, `⟨ , ⟩ = Faltings.neronPairing` its
Néron form on `J(k̄)` and `|z| = √⟨j z, j z⟩`, with the standing data of Bombieri's
Sections 9–10 over `k`. There is `γ > 1` such that for every intermediate field `K` of `k̄ / k`
finite over `k`, the set of `z ∈ C(K)` with `γ ≤ |z|` is finite with at most
`7 ^ ρ * (1 + log γ / log 2)` elements, `ρ` the rank of `J(K)`. -/
@[faltings "thm_bvr_vojta_theorem"]
public theorem finite_setOf_le_neronNorm_abelJacobi {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [IsIntegral X.C] [IsLocallyNoetherian X.C]
    -- (N): the generic basis `x` of `L(N P)`
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n : ℕ} (hn : n = N - genus X.f)
    (x : Fin (n + 1) → X.C.functionField)
    (hx : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      IsGenericBasis k X.f ((N : ℤ) • X.P.mapDomain Subtype.val) x)
    (hxbpf : ∀ c, Order.coheight c = 1 →
      ∃ i, X.C.ord (x i) c + ((N : ℤ) • X.P.mapDomain Subtype.val) c = 0)
    -- the product `C × C` and its diagonal
    [IsIntegral (pullback X.f X.f)] [IsLocallyNoetherian (pullback X.f X.f)]
    (Δ : X.C ⟶ pullback X.f X.f)
    (hΔ₁ : Δ ≫ pullback.fst X.f X.f = 𝟙 X.C) (hΔ₂ : Δ ≫ pullback.snd X.f X.f = 𝟙 X.C)
    -- the embedding `φ_{NP}` given by `x`, and `ψ = φ_{NP} × φ_{NP}`
    (φNP : X.C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hφNP : φNP ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = X.f)
    [IsClosedImmersion φNP]
    [Stacks.Ample.IsInvertibleModule X.C
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φNP).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))]
    (hφNPL : Stacks.SheafOfModules.picardClass X.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φNP).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      (N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNPx : letI : ∀ r : ℕ,
        GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) (ULift.{u} ℤ)) :=
        fun _ => MvPolynomial.gradedAlgebra
      -- the chart `φNP⁻¹ D₊(T_j)` of `C`
      let U : Fin (n + 1) → X.C.Opens := fun j =>
        φNP ⁻¹ᵁ (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) ⁻¹ᵁ
          Proj.basicOpen _ (MvPolynomial.X j))
      ∀ (j ν : Fin (n + 1)) [Nonempty (U j)],
        (X.C.germToFunctionField (U j)).hom
          (φNP.app _ ((projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).app _
            (Proj.awayToSection _ (MvPolynomial.X j)
              (HomogeneousLocalization.Away.mk
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (MvPolynomial.isHomogeneous_X _ j) 1 (MvPolynomial.X ν)
                (by simpa using MvPolynomial.isHomogeneous_X _ ν))))) =
          x ν / x j)
    (ψ : pullback X.f X.f ⟶
      pullback (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)))
    (hψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst X.f X.f ≫ φNP)
    (hψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd X.f X.f ≫ φNP)
    -- the `k`-structures of `k(C)`, `k(C × C)` and the pull-backs `pr₁^*`, `pr₂^*`
    [Algebra k X.C.functionField]
    (hkC : haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
      ‹Algebra k X.C.functionField› = functionFieldAlgebra k X.f)
    [Algebra k (pullback X.f X.f).functionField]
    (hkX : ∀ c : k, algebraMap k (pullback X.f X.f).functionField c =
      (pullback X.f X.f).presheaf.germ ⊤ (genericPoint ↥(pullback X.f X.f : Scheme.{u}))
        trivial ((pullback.fst X.f X.f ≫ X.f).appTop ((Scheme.ΓSpecIso (.of k)).inv c)))
    (ι₁ ι₂ : X.C.functionField →ₐ[k] (pullback X.f X.f).functionField)
    (hι₁ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.fst X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₁ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.fst X.f X.f) ⁻¹ᵁ U)
          ((pullback.fst X.f X.f).app U t))
    (hι₂ : ∀ (U : X.C.Opens) [Nonempty U] [Nonempty ((pullback.snd X.f X.f) ⁻¹ᵁ U)]
      (t : Γ(X.C, U)),
      ι₂ (X.C.germToFunctionField U t) =
        (pullback X.f X.f).germToFunctionField ((pullback.snd X.f X.f) ⁻¹ᵁ U)
          ((pullback.snd X.f X.f).app U t))
    -- the very ample divisor `B` on `C × C`, and the basis `y` of `H⁰(𝒪(B))` giving `φ_B`
    (sB : ℕ) (hsB : 1 ≤ sB)
    {eΔ : ↥(pullback X.f X.f : Scheme.{u})} (heΔ : IsGenericPoint eΔ (Set.range Δ.base))
    (DB : ↥(pullback X.f X.f : Scheme.{u}) → ℤ)
    (hDB : ∀ q, DB q =
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.fst X.f X.f).base ⁻¹' {c.1}) then a else 0) +
      (sB + 1 : ℤ) * X.P.sum (fun c a =>
        if IsGenericPoint q ((pullback.snd X.f X.f).base ⁻¹' {c.1}) then a else 0) -
      (if q = eΔ then 1 else 0))
    {m : ℕ} (y : Fin (m + 1) → (pullback X.f X.f).functionField)
    (hy : ∀ i, y i ≠ 0)
    (hyD : ∀ i q, 0 ≤ (pullback X.f X.f).ord (y i) q + DB q)
    (hyli : LinearIndependent k y)
    (hyspan : ∀ h : (pullback X.f X.f).functionField,
      (∀ q, 0 ≤ (pullback X.f X.f).ord h q + DB q) → h ∈ Submodule.span k (Set.range y))
    (hybpf : ∀ q : ↥(pullback X.f X.f : Scheme.{u}), Order.coheight q = 1 →
      ∃ i, (pullback X.f X.f).ord (y i) q + DB q = 0)
    (φB : pullback X.f X.f ⟶ projectiveSpaceOver m (Spec (.of k)))
    (hφB : φB ≫ (projectiveSpaceOver m (Spec (.of k)) ↘ Spec (.of k)) =
      pullback.fst X.f X.f ≫ X.f)
    [IsClosedImmersion φB]
    [Stacks.Ample.IsInvertibleModule (pullback X.f X.f)
      (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
          MvPolynomial.gradedAlgebra
       (Scheme.Modules.pullback φB).obj
          ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))]
    (hφBB : Stacks.SheafOfModules.picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace)
        (letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) :=
            MvPolynomial.gradedAlgebra
         (Scheme.Modules.pullback φB).obj
            ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse m _)).obj
              (ProjectiveSpectrum.Proj.twistingSheaf
                (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{u} ℤ)) 1)))
        ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
          _).mpr ‹_›) =
      X.vojtaClass sB sB (-1))
    (hφBy : (pullback X.f X.f).fromSpecStalk (genericPoint ↥(pullback X.f X.f : Scheme.{u})) ≫
          φB =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (fun i => (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv (y i))
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩)
          ((Ne.isUnit (hy 0)).map
            (Scheme.ΓSpecIso (.of (pullback X.f X.f).functionField)).inv.hom))
        ((pullback X.f X.f).fromSpecStalk _ ≫ pullback.fst X.f X.f ≫ X.f))
    -- (B): the coordinates `y` are generic for every projection `π_{a'b'}`
    (hBG1 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y 0) q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG1' : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i i' : Fin (m + 1),
      i.val = 1 → i'.val = 2 → ∀ q q',
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 < (pullback X.f X.f).ord (y i') q' + DB q' →
      ∃ r ∈ IntermediateField.adjoin k {ι₁ (x a' / x 0), ι₂ (x b' / x 0)},
        0 ≤ (pullback X.f X.f).ord r q ∧ (pullback X.f X.f).ord r q' < 0)
    (hBG2 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 → ∀ i : Fin (m + 1), i ≠ 0 → ∀ q,
      0 < (pullback X.f X.f).ord (y i) q + DB q →
      0 ≤ (pullback X.f X.f).ord (ι₁ (x a' / x 0)) q ∧
      0 ≤ (pullback X.f X.f).ord (ι₂ (x b' / x 0)) q)
    (hBG3 : ∀ a' b' : Fin (n + 1), a' ≠ 0 → b' ≠ 0 →
      ∀ 𝔪 : Ideal (MvPolynomial (Fin 2) k), 𝔪.IsMaximal →
      ∃ i : Fin (m + 1), i ≠ 0 ∧ ∀ p : ↥(pullback X.f X.f : Scheme.{u}),
        (∀ r ∈ 𝔪, r ≠ 0 →
          (∀ q, q ⤳ p → Order.coheight q = 1 →
            0 ≤ (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) ∧
          ∃ q, q ⤳ p ∧ Order.coheight q = 1 ∧
            0 < (pullback X.f X.f).ord
              (MvPolynomial.aeval ![ι₁ (x a' / x 0), ι₂ (x b' / x 0)] r) q) →
        ∀ q, q ⤳ p → Order.coheight q = 1 → (pullback X.f X.f).ord (y i) q + DB q = 0) :
    let pair : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f) → ℝ :=
      fun z w => neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp kbar
        (.ofMul (z ≫ j)) (.ofMul (w ≫ j))
    ∃ γ : ℝ, 1 < γ ∧ ∀ (K : IntermediateField k kbar) [FiniteDimensional k K],
      haveI := A.isAbelianVariety
      letI := isCommMonObj_of_isProper_of_geometricallyIntegral A.J
      letI : CommGroup (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J) :=
        Hom.commGroup
      let ρ := Module.finrank ℤ
        (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A.J))
      let S := {z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ Over.mk X.f |
        (∃ q : Spec (.of K) ⟶ X.C,
          z.left = Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ q) ∧
        γ ≤ √(pair z z)}
      S.Finite ∧ (S.ncard : ℝ) ≤ 7 ^ ρ * (1 + Real.log γ / Real.log 2) := by
  intro pair
  -- Bombieri's Theorem 1 and the gap principle
  obtain ⟨γ₁, hγ₁, hT1⟩ := exists_neronPairing_abelJacobi_le X A hg j hj D hrad hsupp kbar
    N hN hn x hx hxbpf Δ hΔ₁ hΔ₂ φNP hφNP hφNPL hφNPx ψ hψ₁ hψ₂ hkC hkX ι₁ ι₂ hι₁ hι₂ sB hsB heΔ
    DB hDB y hy hyD hyli hyspan hybpf φB hφB hφBB hφBy hBG1 hBG1' hBG2 hBG3
  obtain ⟨c, -, hgap⟩ := exists_two_pow_mul_neronNorm_le X A hg j hj D hrad hsupp kbar
  exact ⟨max γ₁ c, lt_max_of_lt_left hγ₁, fun K _ =>
    finite_setOf_le_of_finiteDimensional X A hg j hj D hrad hsupp kbar pair (fun _ _ => rfl)
      (max γ₁ c) c (lt_max_of_lt_left hγ₁) (le_max_right _ _) hgap
      (fun z w hz hzw => hT1 z w ((le_max_left _ _).trans hz)
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans hzw)) K⟩

end Faltings
