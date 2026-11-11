module

public import Mordell.BombieriVojta.Height.DeltaPrime
public import Mordell.NeronTate.MumfordFormula.Delta

/-!
# `h_{Δ'} = -⟨z, w⟩ + O(1)`

Let `(C, P)` be a curve of genus `g ≥ 2` over a number field `k` with a divisor `P` of degree
one, `(J, ι)` a Jacobian, `j = j_P : C → J` the Abel–Jacobi map and `⟨x, y⟩` the Néron pairing
of the theta class on `J(k̄)`; for `z, w ∈ C(k̄)` write `⟨z, w⟩ = ⟨j z, j w⟩`. Let `s ≥ 1` and
`N ≥ 2g + 1` be integers, `φ_{NP}` a projective embedding of `C` with `φ_{NP}^* 𝒪(1) ≅ 𝒪(NP)` and
`φ_B` a projective embedding of `C × C` with `φ_B^* 𝒪(1) ≅ 𝒪(B)`, where
`B = s P × C + s C × P - Δ'`. Then the height
`h_{Δ'}(z, w) = (s / N) h_{NP}(z) + (s / N) h_{NP}(w) - h_B(z, w)` of
`Faltings.BombieriVojta.heightDeltaPrime` differs from `-⟨z, w⟩` by a bounded function on
`(C × C)(k̄)`.

The proof is the Weil height machine: `(z, w) ↦ h_{NP}(z)` and `(z, w) ↦ h_{NP}(w)` are heights
for `pr₁^* cl(NP)` and `pr₂^* cl(NP)`, `h_B` is one for `cl(B)`, so by linearity `h_{Δ'}` is a
height for `cl(Δ')`, and by Mumford's theorem every height for `cl(Δ')` is `-⟨z, w⟩ + O(1)`.

## Main results

* `Faltings.BombieriVojta.exists_abs_heightDeltaPrime_add_neronPairing_le`: there is `κ₂` with
  `|h_{Δ'}(z, w) + ⟨z, w⟩| ≤ κ₂` for all `z, w ∈ C(k̄)`.

## Implementation notes

The Néron pairing `Faltings.neronPairing` lives on the curve `X` over the number field `k`, and
takes points `Spec K ⟶ C` over `Spec k`, `K` an algebraic closure of `k`. The heights
`Faltings.ProjectiveEmbedding.height`, and with them `heightDeltaPrime`, are defined on the
`K`-points of a variety over `K`. So the statement carries a curve `XK` over `K` together with
an isomorphism `e : XK.C ≅ C ×_k Spec K` over `Spec K`, identifying `XK` with the base change of
`C`; its divisor is the base change of `P`, stated on classes in `Pic(XK.C)` as the pull-back of
`[𝒪_C(P)]` along `XK.C ⟶ C`. A `K`-point `z` of `XK` gives the point `z ≫ e ≫ pr₁` of `C`
over `k`. The embeddings `φ_{NP}` and `φ_B` are taken over `K`, the base change of the source's
embeddings over `k` being one instance, and are pinned by the classes they pull `𝒪(1)` back to:
`φ_{NP}^* 𝒪(1)` is isomorphic to an invertible sheaf `LNP` of class `N • [𝒪(P)]`, and `φ_B^* 𝒪(1)`
to an invertible sheaf `LB` of class `Faltings.CurveWithDegreeOneDivisor.vojtaClass XK s s (-1)`,
the class of `B`. The source's choice of these embeddings by bases of `H⁰(C, 𝒪(NP))` and
`H⁰(C × C, 𝒪(B))` is a case of this. The `ℚ`-algebra structure on `K` is unique.

Mumford's formula `Faltings.IsHeightOfClass.exists_abs_add_neronPairing_le` is stated on the
base change `(C ×_k C)_K`, while `h_{Δ'}` lives on `C_K ×_K C_K`. The two are identified by the
canonical isomorphism of fibre products, and `cl(Δ')` is stable under this base change: the
diagonal of `C_K` is the base change of the diagonal of `C`, along a flat morphism, and `P_K` is
the pull-back of `P`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5, p. 622,
  proof of Lemma 2
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Faltings

/-! ### Base change of `C × C` and of `cl(Δ')` -/

section BaseChange

variable {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] {Y X S' S : 𝒞} {g : Y ⟶ X} {fY : Y ⟶ S'}
  {f : X ⟶ S} {π : S' ⟶ S}

/-- If `Y = X ×_S S'`, then `Y ×_{S'} Y ⟶ X ×_S X` is the base change of the first projection
`X ×_S X ⟶ X` along `Y ⟶ X`. -/
public lemma isPullback_map_fst (h : IsPullback g fY f π) :
    IsPullback (pullback.map fY fY f f g g π h.w.symm h.w.symm) (pullback.fst fY fY)
      (pullback.fst f f) g := by
  have hout : IsPullback (pullback.map fY fY f f g g π h.w.symm h.w.symm ≫ pullback.snd f f)
      (pullback.fst fY fY) f (g ≫ f) := by
    have h' := (IsPullback.of_hasPullback fY fY).flip.paste_horiz h
    rw [← h.w] at h'
    convert h' using 1
    exact pullback.lift_snd _ _ _
  exact IsPullback.of_right hout (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip

/-- If `Y = X ×_S S'`, then `Y ×_{S'} Y = (X ×_S X) ×_S S'`. -/
public lemma isPullback_map (h : IsPullback g fY f π) :
    IsPullback (pullback.map fY fY f f g g π h.w.symm h.w.symm) (pullback.fst fY fY ≫ fY)
      (pullback.fst f f ≫ f) π :=
  (isPullback_map_fst h).paste_vert h

/-- If `Y = X ×_S S'`, the diagonal of `Y` over `S'` is the base change of the diagonal of `X`
over `S`. -/
public lemma isPullback_diagonal_map (h : IsPullback g fY f π) :
    IsPullback (pullback.diagonal fY) g (pullback.map fY fY f f g g π h.w.symm h.w.symm)
      (pullback.diagonal f) := by
  have hout : IsPullback (pullback.diagonal fY ≫ pullback.fst fY fY) g g
      (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst, pullback.diagonal_fst]
    exact IsPullback.id_horiz _
  exact IsPullback.of_right hout (by apply pullback.hom_ext <;> simp)
    (isPullback_map_fst h).flip

end BaseChange

section ClassesBaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- `Stacks.Picard.schemePullbackClass_comp`, stated for `schemePullbackClassHom` so that it
rewrites. -/
public lemma schemePullbackClassHom_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : Z.picardGroup) :
    Stacks.Picard.schemePullbackClassHom a (Stacks.Picard.schemePullbackClassHom b x) =
      Stacks.Picard.schemePullbackClassHom (a ≫ b) x :=
  Stacks.Picard.schemePullbackClass_comp a b x

/-- A homomorphism carrying `a, b, c` to `a', b', c'` carries `d₁ a + d₂ b + d (c - a - b)` to
`d₁ a' + d₂ b' + d (c' - a' - b')`. -/
private lemma map_combination {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)
    {a b c : G} {a' b' c' : H} {d₁ d₂ d : ℤ} (ha : φ a = a') (hb : φ b = b') (hc : φ c = c') :
    φ (d₁ • a + d₂ • b + d • (c - a - b)) = d₁ • a' + d₂ • b' + d • (c' - a' - b') := by
  simp [ha, hb, hc]

/-- **The class of `V(d₁, d₂, d)` is stable under base change**: if `XK = (C_K, P_K)` is the base
change of `X = (C, P)` to `K`, then the pull-back of `V(d₁, d₂, d)` along
`C_K ×_K C_K ⟶ C ×_k C` is `V(d₁, d₂, d)` of `XK`. -/
public lemma schemePullbackClassHom_map_vojtaClass (X : CurveWithDegreeOneDivisor k)
    (XK : CurveWithDegreeOneDivisor K) {π : XK.C ⟶ X.C}
    (h : IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hP : XK.classP = Stacks.Picard.schemePullbackClassHom π X.classP) (d₁ d₂ d : ℤ) :
    Stacks.Picard.schemePullbackClassHom
        (pullback.map XK.f XK.f X.f X.f π π _ h.w.symm h.w.symm) (X.vojtaClass d₁ d₂ d) =
      XK.vojtaClass d₁ d₂ d := by
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
  have hΔ : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal X.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal k X.f).1
  have : Stacks.Divisors.IsEffectiveCartierDivisor (pullback.diagonal XK.f).ker :=
    (isEffectiveCartierDivisor_ker_diagonal K XK.f).1
  set β := pullback.map XK.f XK.f X.f X.f π π _ h.w.symm h.w.symm
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat β := MorphismProperty.of_isPullback (isPullback_map h).flip inferInstance
  have : Stacks.Divisors.IsPullbackDefined β (pullback.diagonal X.f).ker :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ hΔ
  have hdiag : Stacks.Picard.schemePullbackClassHom β
      (Stacks.Divisors.picardClass (pullback.diagonal X.f).ker) =
        Stacks.Divisors.picardClass (pullback.diagonal XK.f).ker := by
    refine (Stacks.Divisors.schemePullbackClass_picardClass _ _).trans ?_
    refine Stacks.Divisors.picardClass_congr ?_
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← (isPullback_diagonal_map h).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  have hpr : ∀ (p : pullback X.f X.f ⟶ X.C) (q : pullback XK.f XK.f ⟶ XK.C), β ≫ p = q ≫ π →
      Stacks.Picard.schemePullbackClassHom β (Stacks.Picard.schemePullbackClassHom p X.classP) =
        Stacks.Picard.schemePullbackClassHom q XK.classP := by
    intro p q hpq
    rw [hP, schemePullbackClassHom_comp, schemePullbackClassHom_comp, hpq]
  have h₁ := hpr (pullback.fst X.f X.f) (pullback.fst XK.f XK.f) (pullback.lift_fst _ _ _)
  have h₂ := hpr (pullback.snd X.f X.f) (pullback.snd XK.f XK.f) (pullback.lift_snd _ _ _)
  exact map_combination _ h₁ h₂ hdiag

end ClassesBaseChange

namespace BombieriVojta

/-! ### Heights of projective embeddings -/

section Heights

open Stacks.SheafOfModules

variable {k : Type u} [Field k] {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)}
  [IsProjectiveVariety k f] [Smooth f]

/-- The rational combination `(s/N) (N a ⊗ 1) + (s/N) (N b ⊗ 1) - (v ⊗ 1)` in `G ⊗ ℚ` is
`(s a + s b - v) ⊗ 1`, for `N ≠ 0`. -/
private lemma lTensor_mulLeft_combination {G : Type*} [AddCommGroup G] (a b v : G) (s : ℤ)
    {N : ℕ} (hN : (N : ℚ) ≠ 0) :
    LinearMap.lTensor G (LinearMap.mulLeft ℤ (1 : ℚ))
        (LinearMap.lTensor G (LinearMap.mulLeft ℤ ((s : ℚ) / N)) (((N : ℤ) • a) ⊗ₜ[ℤ] (1 : ℚ)) +
          LinearMap.lTensor G (LinearMap.mulLeft ℤ ((s : ℚ) / N))
            (((N : ℤ) • b) ⊗ₜ[ℤ] (1 : ℚ))) +
      LinearMap.lTensor G (LinearMap.mulLeft ℤ (-1 : ℚ)) (v ⊗ₜ[ℤ] (1 : ℚ)) =
      (s • a + s • b - v) ⊗ₜ[ℤ] (1 : ℚ) := by
  have hq : (N : ℤ) • ((s : ℚ) / N) = s • (1 : ℚ) := by
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
    push_cast
    field_simp
  simp only [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one]
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, hq, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul,
    ← TensorProduct.add_tmul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one,
    ← TensorProduct.add_tmul, sub_eq_add_neg]

/-- **`h_{Δ'}` is a height of `cl(Δ')`**: on `C ×_K C`, for projective embeddings `φNP` of `C`
with `φNP^* 𝒪(1)` of class `N [P]` (`N ≠ 0`) and `φB` of `C ×_K C` with `φB^* 𝒪(1)` of class
`cl(B) = s pr₁^* [P] + s pr₂^* [P] - cl(Δ')`, the function
`(s / N) h_{NP}(z) + (s / N) h_{NP}(w) - h_B(z, w)` is a height associated to `cl(Δ')`. -/
private lemma isHeightOfClass_vojtaClass [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    (X : CurveWithDegreeOneDivisor k) [Smooth X.f]
    [IsProjectiveVariety k (pullback.fst X.f X.f ≫ X.f)] [Smooth (pullback.fst X.f X.f ≫ X.f)]
    {s : ℤ} {N n m : ℕ} (hN : N ≠ 0) (φNP : ProjectiveEmbedding X.f n) (LNP : X.C.Modules)
    [hLNP : Stacks.Ample.IsInvertibleModule X.C LNP]
    (hcNP : picardClass X.C.presheaf (Stacks.RingedSpace.structureIsSheaf X.C.toRingedSpace) LNP
      (IsInvertible.ofAlgebraicGeometry _ _ LNP hLNP) = (N : ℤ) • X.classP)
    (hφNP : Nonempty ((Scheme.Modules.pullback
        (φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ LNP))
    (φB : ProjectiveEmbedding (pullback.fst X.f X.f ≫ X.f) m) (LB : (pullback X.f X.f).Modules)
    [hLB : Stacks.Ample.IsInvertibleModule (pullback X.f X.f) LB]
    (hcB : picardClass (pullback X.f X.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback X.f X.f).toRingedSpace) LB
        (IsInvertible.ofAlgebraicGeometry _ _ LB hLB) = X.vojtaClass s s (-1))
    (hφB : Nonempty ((Scheme.Modules.pullback
        (φB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≅ LB)) :
    IsHeightOfClass (pullback.fst X.f X.f ≫ X.f) (X.vojtaClass 0 0 1 ⊗ₜ (1 : ℚ)) fun p =>
      (s : ℝ) / N * φNP.height ⟨p.1 ≫ pullback.fst X.f X.f, by rw [Category.assoc, p.2]⟩ +
        (s : ℝ) / N * φNP.height ⟨p.1 ≫ pullback.snd X.f X.f, by
          rw [Category.assoc, ← pullback.condition, p.2]⟩ - φB.height p := by
  have h₁ := (isHeightOfClass_height φNP).comp (pullback.fst X.f X.f) rfl
  have h₂ := (isHeightOfClass_height φNP).comp (pullback.snd X.f X.f) pullback.condition.symm
  convert (h₁.linearCombination h₂ ((s : ℚ) / N) ((s : ℚ) / N)).linearCombination
    (isHeightOfClass_height φB) 1 (-1) using 1
  · simp only [(embeddingClass_apply_of_eq_picardClass_of_iso φNP LNP hφNP).trans hcNP,
      (embeddingClass_apply_of_eq_picardClass_of_iso φB LB hφB).trans hcB, LinearMap.rTensor_tmul,
      AddMonoidHom.coe_toIntLinearMap, map_zsmul]
    rw [lTensor_mulLeft_combination _ _ _ s (by exact_mod_cast hN)]
    congr 1
    simp only [CurveWithDegreeOneDivisor.vojtaClass, CurveWithDegreeOneDivisor.classP,
      ← schemePullbackClassHom_eq_pullbackPicardHom]
    module
  · funext p
    push_cast
    ring

end Heights

/-! ### `h_{Δ'} = -⟨z, w⟩ + O(1)` -/

/-- **`h_{Δ'} = -⟨z, w⟩ + O(1)`.** Let `X = (C, P)` be a curve of genus `g ≥ 2` over a number
field `k` with a divisor of degree one, `A` a Jacobian, `j = j_P` the Abel–Jacobi map, `D` the
reduced divisor with support the theta divisor, `K = k̄`, and `XK` the base change of `X` to `K`
through `e : XK.C ≅ C ×_k Spec K`. Let `s ≥ 1`, `N ≥ 2g + 1`, `φNP` a projective embedding of
`XK` with `φNP^* 𝒪(1) ≅ 𝒪(NP)` and `φB` one of `XK × XK` with `φB^* 𝒪(1) ≅ 𝒪(B)`,
`B = s P × C + s C × P - Δ'`. Then there is `κ₂` with
`|heightDeltaPrime XK φNP φB s N z w + ⟨j z, j w⟩| ≤ κ₂` for all `K`-points `z, w` of `XK`,
where `⟨·, ·⟩ = neronPairing`. -/
@[faltings "lem_bv_height_delta_prime"]
public theorem exists_abs_heightDeltaPrime_add_neronPairing_le {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (Nat.le_of_succ_le hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] [Algebra ℚ K]
    (XK : CurveWithDegreeOneDivisor K)
    (e : XK.C ≅ pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (he : e.hom ≫ pullback.snd _ _ = XK.f)
    (hP : (XK.P.sum fun x n =>
        haveI : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
        haveI : IsCurve K XK.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one XK.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal XK.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)) =
      Stacks.Picard.schemePullbackClassHom (e.hom ≫ pullback.fst _ _) (X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)))
    (s : ℤ) (hs : 1 ≤ s) (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) {n m : ℕ}
    (φNP : haveI : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
      ProjectiveEmbedding XK.f n)
    (LNP : XK.C.Modules) [hLNP : Stacks.Ample.IsInvertibleModule XK.C LNP]
    (hLNP : Stacks.SheafOfModules.picardClass XK.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) LNP
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ LNP hLNP) =
      (N : ℤ) • XK.P.sum fun x n =>
        haveI : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
        haveI : IsCurve K XK.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one XK.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal XK.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x))
    (hφNP : Nonempty ((Scheme.Modules.pullback
        (φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ LNP))
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m)
    (LB : (pullback XK.f XK.f).Modules)
    [hLB : Stacks.Ample.IsInvertibleModule (pullback XK.f XK.f) LB]
    (hLB : Stacks.SheafOfModules.picardClass (pullback XK.f XK.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback XK.f XK.f).toRingedSpace) LB
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ LB hLB) =
      XK.vojtaClass s s (-1))
    (hφB : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      Nonempty ((Scheme.Modules.pullback
        (φB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≅ LB)) :
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    let pt : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) := fun z =>
      Over.homMk (z.1 ≫ e.hom ≫ pullback.fst _ _) (by
        simp only [Over.mk_hom, Category.assoc, pullback.condition]
        rw [← Category.assoc e.hom, he, ← Category.assoc, z.2]
        simp)
    ∃ κ₂ : ℝ, ∀ z w, |heightDeltaPrime XK φNP φB s N z w +
      neronPairing X A (Nat.le_of_succ_le hg) j hj D hrad hsupp K
        (.ofMul (pt z ≫ j)) (.ofMul (pt w ≫ j))| ≤ κ₂ := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain rfl : ‹Algebra ℚ K› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  intro pt
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  have : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
  have := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
  have := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).2.2
  have : Smooth (pullback.fst XK.f XK.f ≫ XK.f) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have : GeometricallyIntegral (pullback.fst X.f X.f ≫ X.f) :=
    Cube.geometricallyIntegral_fst_comp X.f X.f
  have : IsVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
  have : IsProjectiveVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1.isProjective.baseChange _⟩
  have hpbK : IsPullback (e.hom ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (IsPullback.of_hasPullback _ _).of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp [← he]) (by simp) (by simp)
  have hpbS := isPullback_map hpbK
  let Ψ := hpbS.isoPullback
  have hh := (isHeightOfClass_vojtaClass XK (N := N) (by omega) φNP LNP
    hLNP hφNP φB LB hLB hφB).comp Ψ.inv hpbS.isoPullback_inv_snd
  rw [LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap,
    ← schemePullbackClassHom_eq_pullbackPicardHom,
    ← schemePullbackClassHom_map_vojtaClass X XK hpbK hP 0 0 1,
    schemePullbackClassHom_comp, hpbS.isoPullback_inv_fst] at hh
  obtain ⟨B, hB⟩ := hh.exists_abs_add_neronPairing_le X A (Nat.le_of_succ_le hg) j hj D hrad
    hsupp K
  refine ⟨B, fun z w => ?_⟩
  have hzw : (pullback.lift z.1 w.1 (z.2.trans w.2.symm) ≫ Ψ.hom) ≫ pullback.snd _ _ = 𝟙 _ := by
    rw [Category.assoc, hpbS.isoPullback_hom_snd, pullback.lift_fst_assoc, z.2]
  convert hB ⟨_, hzw⟩ using 3
  · simp only [heightDeltaPrime, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd]
  · congr 3 <;> ext <;> simp [pt, Ψ]

end BombieriVojta

end Faltings

end
