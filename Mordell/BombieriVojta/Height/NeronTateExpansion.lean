module

public import Mordell.BombieriVojta.Height.DeltaPrime
public import Mordell.BombieriVojta.Height.DeltaPrimeNeronPairing
public import Mordell.BombieriVojta.Height.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import Mordell.NeronTate.MumfordFormula.Delta
public import Mordell.NeronTate.MumfordFormula.NP
public import Mordell.NeronTate.MumfordFormula.Theta
public import Mordell.NeronTate.PhiMap
public import Mordell.Jacobian.Theta.Symmetry
public import Mordell.NeronTate.Pairing.CauchySchwarz
public import Mordell.CurveProduct.Intersection
public import Mordell.NeronTate.Pairing.LinearPartBound

/-!
# Expansion of `h_V` in Néron–Tate terms

Let `(C, P)` be a curve over a number field `k` with a divisor `P` of degree one, of genus
`g ≥ 2`, with Jacobian `J`, Abel–Jacobi map `j = j_P`, and Néron pairing `⟨x, y⟩` on `J(k̄)`;
for `z, w ∈ C(k̄)` write `⟨z, w⟩ = ⟨j z, j w⟩` and `|z| = √⟨z, z⟩`. Let `N ≥ 2g + 1`,
`φ_{NP}` the embedding of `C` by a basis of `H⁰(C, 𝒪(NP))`, `s ≥ 1`, and `φ_B` the embedding
of `C × C` by a basis of `H⁰(C × C, 𝒪(B))`, `B = s P × C + s C × P - Δ'`. Then there are
constants `κ₁, κ₂, κ₃ ≥ 0` such that for all integers `d₁, d₂, d` and all `(z, w) ∈ (C × C)(k̄)`
the height `h_V` of `V = d₁ P × C + d₂ C × P + d Δ'` satisfies
`|h_V(z, w) - (d₁ / 2g |z|² + d₂ / 2g |w|² - d ⟨z, w⟩)|`
`  ≤ κ₃ / 2g (|d₁| |z| + |d₂| |w|) + κ₁ / N (|d₁| + |d₂|) + κ₂ |d|`.

The proof is Bombieri's. Exactly, `h_V = (d₁ / N) h_{NP}(z) + (d₂ / N) h_{NP}(w) + d h_{Δ'}(z, w)`.
By the height machine `h_{Δ'}` is a height of `cl(Δ')`, hence `-⟨z, w⟩ + O(1)` by Mumford's
formula; Mumford's formula for the diagonal gives `h_{NP} = (N / g) ĥ_{θ⁻} + O(1)`; and
`ĥ_{θ⁻} = ½ |z|² - ½ ĥ_{θ - θ⁻}` with `ĥ_{θ - θ⁻} = ⟨·, y₀⟩`, which is bounded by `|y₀| |z|`
(Riemann's symmetry and Cauchy–Schwarz).

## Main results

* `Faltings.exists_abs_vojtaHeight_sub_neronPairing_le`: the expansion of `h_V`.

## Implementation notes

Heights (`Faltings.ProjectiveEmbedding.height`, hence
`Faltings.CurveWithDegreeOneDivisor.vojtaHeight`) are defined on `K`-points of a variety over
`K`, while the Néron pairing `Faltings.neronPairing` is defined on `K`-points over `k` of the
Jacobian of the curve over `k`. The curve `XK = (C_K, P_K)` over the algebraic closure `K` of
`k` is therefore given together with a cartesian square `π : C_K ⟶ C` over
`Spec K ⟶ Spec k`; a `K`-point `z` of `C_K` is the `K`-point `z ≫ π` of `C` over `k`, and
`⟨z, w⟩ = neronPairing … K (j (z ≫ π)) (j (w ≫ π))`. The embeddings `φ_{NP}` and `φ_B` of
`C_K` and `C_K ×_K C_K` are the morphisms
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver` of bases of the global sections of
invertible sheaves whose classes are the pull-backs along `π` and `π × π` of `N • [𝒪_C(P)]` and
of `Faltings.CurveWithDegreeOneDivisor.vojtaClass X s s (-1) = [𝒪(B)]`. The square `|z|²` is
written `⟨z, z⟩`, which is nonnegative.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990], Section 5, p. 622,
  proof of Lemma 2
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct MonObj

universe u

namespace Faltings

open BombieriVojta

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- Pulling back a class `pr^* c ⊗ 1` along `a` gives `(a ≫ pr)^* c ⊗ 1`. -/
private lemma rTensor_pullbackPicardHom_tmul {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (h : a ≫ b = c) (x : Z.picardGroup) :
    LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom a).toIntLinearMap
        (Stacks.Picard.schemePullbackClassHom b x ⊗ₜ[ℤ] (1 : ℚ)) =
      Stacks.Picard.schemePullbackClassHom c x ⊗ₜ[ℤ] (1 : ℚ) := by
  rw [LinearMap.rTensor_tmul, AddMonoidHom.coe_toIntLinearMap,
    ← schemePullbackClassHom_eq_pullbackPicardHom, schemePullbackClassHom_comp, h]

/-- `1 ⊗ x` base-changed along a pull-back of classes is `1 ⊗ (pull-back of x)`. -/
private lemma baseChange_schemePullbackClassHom_one_tmul {X Y : Scheme.{u}} (a : X ⟶ Y)
    (x : Stacks.Picard.ofScheme Y) :
    (Stacks.Picard.schemePullbackClassHom a).toIntLinearMap.baseChange ℚ ((1 : ℚ) ⊗ₜ x) =
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom a x := by
  rw [LinearMap.baseChange_tmul]
  rfl

/-- Inversion on the base change `A_K` lies over inversion on `A`. -/
private lemma inv_left_comp_pullback_fst {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Over (Spec (.of k))) [GrpObj A] :
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A
    ι[JK].left ≫ pullback.fst A.hom φK = pullback.fst A.hom φK ≫ ι[A].left := by
  intro φK JK
  change ((Over.pullback φK).map ι[A]).left ≫ _ = _
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- On the base change `A_K` of a group scheme `A`, the class `θ_K - θ_K⁻` (with
`θ_K⁻ = [-1]^* θ_K`) is the pull-back of `θ - [-1]^* θ`. -/
private lemma sub_baseChange_pullbackInv_eq {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Over (Spec (.of k))) [GrpObj A] (c : Stacks.Picard.ofScheme A.left) :
    let φK := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let JK : Over (Spec (.of K)) := (Over.pullback φK).obj A
    (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φK) c -
        (Stacks.Picard.schemePullbackClassHom ι[JK].left).toIntLinearMap.baseChange ℚ
          ((1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φK) c) =
      (1 : ℚ) ⊗ₜ Stacks.Picard.schemePullbackClassHom (pullback.fst A.hom φK)
        (c - Stacks.Picard.schemePullbackClassHom ι[A].left c) := by
  dsimp only
  rw [baseChange_schemePullbackClassHom_one_tmul, schemePullbackClassHom_comp,
    inv_left_comp_pullback_fst,
    ← schemePullbackClassHom_comp, ← TensorProduct.tmul_sub, map_sub]

/-! ### Heights of projective embeddings -/

section Heights

open Stacks.SheafOfModules

/-- For the morphism `φ` to `ℙⁿ` of generating sections of an invertible sheaf `L`,
`φ^* 𝒪(1) ≅ L`. -/
private lemma nonempty_pullback_twistingSheafAtUniverse_iso {X S : Scheme.{u}} {n : ℕ}
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (n + 1) → Γ(L, ⊤))
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks s) (f : X ⟶ S) :
    Nonempty ((Scheme.Modules.pullback
      (Stacks.ProjectiveFromSections.toProjectiveSpaceOver s hs f ≫
        projectiveSpaceOver.toIntegralAtUniverse n S)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L) := by
  obtain ⟨α, hiso, -⟩ :=
    AlgebraicGeometry.exists_iso_twistingSheafAtUniverse_toProjectiveSpaceAtUniverse s hs
  rw [Stacks.ProjectiveFromSections.toProjectiveSpaceOver_snd]
  exact ⟨asIso α⟩

variable {k : Type u} [Field k] {Y : Scheme.{u}} {f : Y ⟶ Spec (.of k)}
  [IsProjectiveVariety k f] [Smooth f]

/-- If `φ^* 𝒪(1) ≅ L` and `[L] = b^* c`, then `h_φ ∘ a` is a height of `(a ≫ b)^* c` for any
`a : Y' ⟶ Y` over `k`. -/
private lemma isHeightOfClass_height_comp [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k] {n : ℕ}
    {Y' Z : Scheme.{u}} {f' : Y' ⟶ Spec (.of k)} [IsProjectiveVariety k f'] [Smooth f']
    (φ : ProjectiveEmbedding f n) (L : Y.Modules) [hL : Stacks.Ample.IsInvertibleModule Y L]
    (hφ : Nonempty ((Scheme.Modules.pullback
      (φ.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L))
    {b : Y ⟶ Z} {c : Stacks.Picard.ofScheme Z}
    (hc : Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL) =
      Stacks.Picard.schemePullbackClassHom b c)
    {a : Y' ⟶ Y} (ha : a ≫ f = f') {t : Y' ⟶ Z} (ht : a ≫ b = t) :
    IsHeightOfClass f' (Stacks.Picard.schemePullbackClassHom t c ⊗ₜ (1 : ℚ))
      (fun x => φ.height ⟨x.1 ≫ a, by rw [Category.assoc, ha, x.2]⟩) := by
  have h := (isHeightOfClass_height φ).comp a ha
  rwa [embeddingClass_apply_of_eq_picardClass_of_iso φ L hφ, hc,
    rTensor_pullbackPicardHom_tmul ht] at h

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
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]; push_cast; field_simp
  simp only [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one]
  rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, hq, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul,
    ← TensorProduct.add_tmul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one,
    ← TensorProduct.add_tmul, sub_eq_add_neg]

/-- **`h_{Δ'}` is a height of `s pr₁^* a + s pr₂^* a - b`**: on `Y ×_k Y`, for projective
embeddings `φNP` of `Y` with `φNP^* 𝒪(1)` of class `N a` (`N ≠ 0`) and `φB` of `Y ×_k Y` with
`φB^* 𝒪(1)` of class `b`, the function `(s / N) h_{NP}(z) + (s / N) h_{NP}(w) - h_B(z, w)` is a
height associated to `s pr₁^* a + s pr₂^* a - b`. -/
private lemma isHeightOfClass_combination [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k]
    [IsProjectiveVariety k (pullback.fst f f ≫ f)] [Smooth (pullback.fst f f ≫ f)]
    {s : ℤ} {N n m : ℕ} (hN : N ≠ 0) (a : Stacks.Picard.ofScheme Y)
    (b : Stacks.Picard.ofScheme (pullback f f)) (φNP : ProjectiveEmbedding f n) (LNP : Y.Modules)
    [hLNP : Stacks.Ample.IsInvertibleModule Y LNP]
    (hcNP : picardClass Y.presheaf (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) LNP
      (IsInvertible.ofAlgebraicGeometry _ _ LNP hLNP) = (N : ℤ) • a)
    (hφNP : Nonempty ((Scheme.Modules.pullback
        (φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ LNP))
    (φB : ProjectiveEmbedding (pullback.fst f f ≫ f) m) (LB : (pullback f f).Modules)
    [hLB : Stacks.Ample.IsInvertibleModule (pullback f f) LB]
    (hcB : picardClass (pullback f f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback f f).toRingedSpace) LB
        (IsInvertible.ofAlgebraicGeometry _ _ LB hLB) = b)
    (hφB : Nonempty ((Scheme.Modules.pullback
        (φB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≅ LB)) :
    IsHeightOfClass (pullback.fst f f ≫ f)
      ((s • Stacks.Picard.schemePullbackClassHom (pullback.fst f f) a +
        s • Stacks.Picard.schemePullbackClassHom (pullback.snd f f) a - b) ⊗ₜ (1 : ℚ)) fun p =>
      (s : ℝ) / N * φNP.height ⟨p.1 ≫ pullback.fst f f, by rw [Category.assoc, p.2]⟩ +
        (s : ℝ) / N * φNP.height ⟨p.1 ≫ pullback.snd f f, by
          rw [Category.assoc, ← pullback.condition, p.2]⟩ - φB.height p := by
  have h₁ := (isHeightOfClass_height φNP).comp (pullback.fst f f) rfl
  have h₂ := (isHeightOfClass_height φNP).comp (pullback.snd f f) pullback.condition.symm
  convert (h₁.linearCombination h₂ ((s : ℚ) / N) ((s : ℚ) / N)).linearCombination
    (isHeightOfClass_height φB) 1 (-1) using 1
  · simp only [(embeddingClass_apply_of_eq_picardClass_of_iso φNP LNP hφNP).trans hcNP,
      (embeddingClass_apply_of_eq_picardClass_of_iso φB LB hφB).trans hcB, LinearMap.rTensor_tmul,
      AddMonoidHom.coe_toIntLinearMap]
    rw [map_zsmul, map_zsmul, lTensor_mulLeft_combination _ _ _ s (by exact_mod_cast hN)]
    simp only [← schemePullbackClassHom_eq_pullbackPicardHom]
  · funext p
    push_cast
    ring

end Heights

/-! ### The final estimate -/

/-- `|a / c * x| ≤ |a| / c * B` for `c > 0` and `|x| ≤ B`. -/
private lemma abs_div_mul_le {c x B : ℝ} (a : ℝ) (hc : 0 < c) (h : |x| ≤ B) :
    |a / c * x| ≤ |a| / c * B := by
  rw [abs_mul, abs_div, abs_of_pos hc]; gcongr

/-- The real-number bookkeeping of the expansion: from
`h_V = (d₁ / N) H(z) + (d₂ / N) H(w) + d D`, `|H - (N / g) f| ≤ B₁`, `|D + ⟨z, w⟩| ≤ B₂`,
`f = ½ |·|² - ½ e` and `|e| ≤ κ |·|`. -/
private lemma abs_sub_le_of_expansion {N g d₁ d₂ d v Hz Hw D pzz pww pzw fz fw ez ew B₁ B₂ κ
    sz sw : ℝ} (hN : 0 < N) (hg : 0 < g) (hv : v = d₁ / N * Hz + d₂ / N * Hw + d * D)
    (hz : |Hz - N / g * fz| ≤ B₁) (hw : |Hw - N / g * fw| ≤ B₁) (hD : |D + pzw| ≤ B₂)
    (hfz : fz = 1 / 2 * pzz - 1 / 2 * ez) (hfw : fw = 1 / 2 * pww - 1 / 2 * ew)
    (hez : |ez| ≤ κ * sz) (hew : |ew| ≤ κ * sw) :
    |v - (d₁ / (2 * g) * pzz + d₂ / (2 * g) * pww - d * pzw)| ≤
      κ / (2 * g) * (|d₁| * sz + |d₂| * sw) + B₁ / N * (|d₁| + |d₂|) + B₂ * |d| := by
  have key : v - (d₁ / (2 * g) * pzz + d₂ / (2 * g) * pww - d * pzw) =
      d₁ / N * (Hz - N / g * fz) + d₂ / N * (Hw - N / g * fw) + d * (D + pzw) -
        d₁ / (2 * g) * ez - d₂ / (2 * g) * ew := by
    subst hv hfz hfw
    field_simp
    ring
  rw [key]
  have h₁ := abs_div_mul_le d₁ hN hz
  have h₂ := abs_div_mul_le d₂ hN hw
  have h₃ : |d * (D + pzw)| ≤ |d| * B₂ := by rw [abs_mul]; gcongr
  have h₄ := abs_div_mul_le d₁ (by positivity : (0 : ℝ) < 2 * g) hez
  have h₅ := abs_div_mul_le d₂ (by positivity : (0 : ℝ) < 2 * g) hew
  rw [show κ / (2 * g) * (|d₁| * sz + |d₂| * sw) + B₁ / N * (|d₁| + |d₂|) + B₂ * |d| =
      |d₁| / N * B₁ + |d₂| / N * B₁ + |d| * B₂ + |d₁| / (2 * g) * (κ * sz) +
        |d₂| / (2 * g) * (κ * sw) by ring]
  rw [abs_le] at h₁ h₂ h₃ h₄ h₅ ⊢
  constructor <;> linarith

/-! ### The expansion -/

/-- **Expansion of `h_V` in Néron–Tate terms, for embeddings given by their pull-backs of
`𝒪(1)`.** As `Faltings.exists_abs_vojtaHeight_sub_neronPairing_le`, with the embeddings `φNP`,
`φB` pinned by isomorphisms `φNP^* 𝒪(1) ≅ L`, `φB^* 𝒪(1) ≅ M` in place of bases of `Γ(L, ⊤)`,
`Γ(M, ⊤)`. -/
theorem exists_abs_vojtaHeight_sub_neronPairing_le_of_nonempty_iso {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] [Algebra ℚ K]
    (XK : CurveWithDegreeOneDivisor K) (π : XK.C ⟶ X.C)
    (hπ : IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {n m : ℕ} (φNP : ProjectiveEmbedding XK.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) (s : ℤ) (hs : 1 ≤ s)
    (L : XK.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule XK.C L]
    (hL : Stacks.SheafOfModules.picardClass XK.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      Stacks.Picard.schemePullbackClassHom π ((N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)))
    (M : (pullback XK.f XK.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback XK.f XK.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback XK.f XK.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      Stacks.Picard.schemePullbackClassHom (pullback.map XK.f XK.f X.f X.f π π
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) hπ.w.symm hπ.w.symm)
        (X.vojtaClass s s (-1)))
    (hφL : Nonempty ((Scheme.Modules.pullback
      (φNP.hom ≫ projectiveSpaceOver.toIntegralAtUniverse n _)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅ L))
    (hφM : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      Nonempty ((Scheme.Modules.pullback
        (φB.hom ≫ projectiveSpaceOver.toIntegralAtUniverse m _)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} m) ≅ M)) :
    letI : XK.C.Over (Spec (.of K)) := ⟨XK.f⟩
    letI : (pullback XK.f XK.f).Over (Spec (.of K)) := ⟨pullback.fst XK.f XK.f ≫ XK.f⟩
    haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    -- the `K`-point `z ≫ π` of `C` over `k`
    let pt : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) := fun z =>
      Over.homMk (z.1 ≫ π) (by simp [hπ.w, reassoc_of% z.2])
    -- the Néron pairing `⟨z, w⟩ = ⟨j z, j w⟩`
    let pair : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} → ℝ := fun z w =>
      neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp K
        (.ofMul (pt z ≫ j)) (.ofMul (pt w ≫ j))
    let g : ℝ := genus X.f
    ∃ κ₁ κ₂ κ₃ : ℝ, 0 ≤ κ₁ ∧ 0 ≤ κ₂ ∧ 0 ≤ κ₃ ∧ ∀ (d₁ d₂ d : ℤ) (z w),
      |XK.vojtaHeight φNP φB s N d₁ d₂ d z w -
          (d₁ / (2 * g) * pair z z + d₂ / (2 * g) * pair w w - d * pair z w)| ≤
        κ₃ / (2 * g) * (|(d₁ : ℝ)| * √(pair z z) + |(d₂ : ℝ)| * √(pair w w)) +
          κ₁ / N * (|(d₁ : ℝ)| + |(d₂ : ℝ)|) + κ₂ * |(d : ℝ)| := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain rfl : ‹Algebra ℚ K› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  intro pt pair g
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
  have : Smooth XK.f := SmoothOfRelativeDimension.smooth 1 XK.f
  have := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
  have := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).2.2
  have : Smooth (pullback.fst XK.f XK.f ≫ XK.f) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
  have := A.isAbelianVariety
  have hg1 : 1 ≤ genus X.f := one_le_two.trans hg
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hgpos : (0 : ℝ) < g := by
    change (0 : ℝ) < (genus X.f : ℝ); exact_mod_cast hg1
  -- **κ₂**: `h_{Δ'}` is a height of `cl(Δ')`, so `h_{Δ'} = -⟨z, w⟩ + O(1)` by Mumford
  have : GeometricallyIntegral (pullback.fst X.f X.f ≫ X.f) :=
    Cube.geometricallyIntegral_fst_comp X.f X.f
  have : IsVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
  have : IsProjectiveVariety K (pullback.snd (pullback.fst X.f X.f ≫ X.f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(IsSmoothProjectiveCurve.surface_pullback k X.f X.f).1.isProjective.baseChange _⟩
  have hpbS := isPullback_map hπ
  have h₁ : pullback.fst XK.f XK.f ≫ π = pullback.map XK.f XK.f X.f X.f π π
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) hπ.w.symm hπ.w.symm ≫
        pullback.fst X.f X.f := (pullback.lift_fst _ _ _).symm
  have h₂ : pullback.snd XK.f XK.f ≫ π = pullback.map XK.f XK.f X.f X.f π π
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) hπ.w.symm hπ.w.symm ≫
        pullback.snd X.f X.f := (pullback.lift_snd _ _ _).symm
  generalize pullback.map XK.f XK.f X.f X.f π π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    hπ.w.symm hπ.w.symm = β at hM hpbS h₁ h₂
  obtain ⟨Ψ, hΨfst, hΨsnd, hΨhom⟩ : ∃ Ψ : pullback XK.f XK.f ≅
      pullback (pullback.fst X.f X.f ≫ X.f) (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      Ψ.inv ≫ β = pullback.fst _ _ ∧ Ψ.inv ≫ pullback.fst XK.f XK.f ≫ XK.f = pullback.snd _ _ ∧
        Ψ.hom ≫ pullback.snd _ _ = pullback.fst XK.f XK.f ≫ XK.f :=
    ⟨hpbS.isoPullback, hpbS.isoPullback_inv_fst, hpbS.isoPullback_inv_snd,
      hpbS.isoPullback_hom_snd⟩
  have hcl : (s • Stacks.Picard.schemePullbackClassHom (pullback.fst XK.f XK.f)
        (Stacks.Picard.schemePullbackClassHom π X.classP) +
      s • Stacks.Picard.schemePullbackClassHom (pullback.snd XK.f XK.f)
        (Stacks.Picard.schemePullbackClassHom π X.classP) -
      Stacks.Picard.schemePullbackClassHom β (X.vojtaClass s s (-1))) =
      Stacks.Picard.schemePullbackClassHom β (X.vojtaClass 0 0 1) := by
    rw [schemePullbackClassHom_comp, schemePullbackClassHom_comp, h₁, h₂,
      ← schemePullbackClassHom_comp, ← schemePullbackClassHom_comp]
    rw [← map_zsmul (Stacks.Picard.schemePullbackClassHom β) s,
      ← map_zsmul (Stacks.Picard.schemePullbackClassHom β) s, ← map_add, ← map_sub]
    congr 1
    rw [CurveWithDegreeOneDivisor.vojtaClass_eq, CurveWithDegreeOneDivisor.vojtaClass_eq]
    module
  have hL' : Stacks.SheafOfModules.picardClass XK.C.presheaf
      (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      (N : ℤ) • Stacks.Picard.schemePullbackClassHom π X.classP := by
    rw [hL, map_zsmul]; rfl
  have hh₀ := isHeightOfClass_combination (s := s) hN0
    (Stacks.Picard.schemePullbackClassHom π X.classP) _ φNP L hL' hφL φB M hM hφM
  have hh := hh₀.comp Ψ.inv hΨsnd
  rw [hcl] at hh
  rw [rTensor_pullbackPicardHom_tmul hΨfst] at hh
  obtain ⟨B₂, hB₂⟩ := hh.exists_abs_add_neronPairing_le X A hg1 j hj D hrad hsupp K
  have hΨβ : Ψ.hom ≫ pullback.fst _ _ = β := by rw [← hΨfst, Iso.hom_inv_id_assoc]
  have hΔ : ∀ z w, |heightDeltaPrime XK φNP φB s N z w + pair z w| ≤ B₂ := by
    intro z w
    have hs : (pullback.lift z.1 w.1 (z.2.trans w.2.symm) ≫ Ψ.hom) ≫ pullback.snd _ _ =
        𝟙 _ := by
      rw [Category.assoc, hΨhom, pullback.lift_fst_assoc, z.2]
    convert hB₂ ⟨_, hs⟩ using 3
    · simp only [heightDeltaPrime, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        pullback.lift_fst, pullback.lift_snd]
    · simp only [pair]
      congr 2 <;> ext <;> simp [pt, reassoc_of% hΨβ, ← h₁, ← h₂, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
  -- **κ₁**: `h_{NP} = (N / g) ĥ_{θ⁻} + O(1)` (Mumford's formula for the diagonal)
  obtain ⟨e, he_fst, he_inv_snd⟩ : ∃ e : XK.C ≅
      pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
      e.hom ≫ pullback.fst _ _ = π ∧ e.inv ≫ XK.f = pullback.snd _ _ :=
    ⟨hπ.isoPullback, hπ.isoPullback_hom_fst, hπ.isoPullback_inv_snd⟩
  have he_inv_fst : e.inv ≫ π = pullback.fst _ _ := by rw [← he_fst, Iso.inv_hom_id_assoc]
  have : IsVariety K (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := ⟨⟩
  have : IsProjectiveVariety K
      (pullback.snd X.f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    ⟨(IsProjectiveVariety.isProjective (f := X.f)).baseChange _⟩
  have h₁ := isHeightOfClass_height_comp φNP L hφL (c := (N : ℤ) • X.classP)
    (by rw [hL', map_zsmul]) he_inv_snd he_inv_fst
  let θ := Stacks.Divisors.picardClass D
  let θm := Stacks.Picard.schemePullbackClassHom ι[A.J].left θ
  obtain ⟨f₁, hf₁⟩ := exists_isNeronTateHeight A.J K ((1 : ℚ) ⊗ₜ θm)
  obtain ⟨f₂, hf₂⟩ := exists_isNeronTateHeight A.J K ((1 : ℚ) ⊗ₜ (θ - θm))
  rw [baseChange_schemePullbackClassHom_one_tmul] at hf₁ hf₂
  obtain ⟨B₁, hB₁⟩ := IsHeightOfClass.exists_abs_sub_neronTateHeight_le X A hg1 j hj D hrad
    hsupp K N (by omega) _ f₁ h₁ hf₁
  have hTM := neronTateHeight_pullbackInv_eq_half_neronPairing_sub X A hg1 j hj D hrad hsupp K
    f₁ f₂ hf₁ hf₂
  obtain ⟨y₀, hy₀⟩ := exists_neronPairing_eq_of_isNeronTateHeight_sub_neg X A hg1 j hj D hrad
    hsupp K
  have hodd x := (hy₀ f₂ (by rw [sub_baseChange_pullbackInv_eq]; exact hf₂) x).2
  -- the point `z` of `C_K` as a section of `C ×_k Spec K ⟶ Spec K`
  let sec : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
      {p : Spec (.of K) ⟶ pullback X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))) //
        p ≫ pullback.snd _ _ = 𝟙 _} := fun z =>
    ⟨z.1 ≫ e.hom, by rw [Category.assoc, ← he_inv_snd, Iso.hom_inv_id_assoc, z.2]⟩
  have hNP : ∀ z, |φNP.height z - (N : ℝ) / g * f₁ ⟨pullback.lift (pt z ≫ j).left (𝟙 _)
      (by rw [Over.w (pt z ≫ j), Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩| ≤
        max B₁ 0 := by
    intro z
    refine le_trans (le_of_eq ?_) ((hB₁ (sec z)).trans (le_max_left _ _))
    congr 4
    · exact Subtype.ext (by change z.1 = (z.1 ≫ e.hom) ≫ e.inv; simp)
    · refine Subtype.ext (pullback.hom_ext ?_ ?_)
      · rw [pullback.lift_fst, pullback.lift_fst]
        change (z.1 ≫ π) ≫ j.left = (z.1 ≫ e.hom) ≫ pullback.fst _ _ ≫ j.left
        rw [Category.assoc, Category.assoc, reassoc_of% he_fst]
      · rw [pullback.lift_snd, pullback.lift_snd]
  refine ⟨max B₁ 0, max B₂ 0, √(neronPairing X A hg1 j hj D hrad hsupp K y₀ y₀),
    le_max_right _ _, le_max_right _ _, Real.sqrt_nonneg _, fun d₁ d₂ d z w => ?_⟩
  refine abs_sub_le_of_expansion hNpos hgpos ?_ (hNP z) (hNP w)
    ((hΔ z w).trans (le_max_left _ _)) (hTM (.ofMul (pt z ≫ j))) (hTM (.ofMul (pt w ≫ j)))
    (hodd _) (hodd _)
  simp only [CurveWithDegreeOneDivisor.vojtaHeight, heightDeltaPrime]
  push_cast
  ring

/-- **Expansion of `h_V` in Néron–Tate terms.** Let `X = (C, P)` be a curve over a number
field `k` of genus `g ≥ 2`, `A` a Jacobian with Abel–Jacobi map `j`, `K` an algebraic closure
of `k`, and `XK` a curve over `K` with a cartesian square `π : XK.C ⟶ X.C` over
`Spec K ⟶ Spec k`. Let `φNP`, `φB` be the embeddings of `XK.C` and `XK.C ×_K XK.C` by bases of
the global sections of invertible sheaves of classes the pull-backs of `N • [𝒪(P)]`
(`2g + 1 ≤ N`) and of `vojtaClass X s s (-1)` (`1 ≤ s`). Write `⟨z, w⟩` for
`neronPairing` at `j (z ≫ π)`, `j (w ≫ π)` and `|z| = √⟨z, z⟩`. Then there are `κ₁ κ₂ κ₃ ≥ 0`
such that for all integers `d₁ d₂ d` and all `K`-points `z w` of `XK.C`,
`|vojtaHeight XK φNP φB s N d₁ d₂ d z w - (d₁ / 2g ⟨z, z⟩ + d₂ / 2g ⟨w, w⟩ - d ⟨z, w⟩)|` is at
most `κ₃ / 2g (|d₁| |z| + |d₂| |w|) + κ₁ / N (|d₁| + |d₂|) + κ₂ |d|`. -/
@[faltings "lem_bv_height_vojta_expansion"]
theorem exists_abs_vojtaHeight_sub_neronPairing_le {k : Type u} [Field k]
    [NumberField k] (X : CurveWithDegreeOneDivisor k) (A : Jacobian k X.f)
    (hg : 2 ≤ genus X.f) (j : Over.mk X.f ⟶ A.J) (hj : IsAbelJacobiMap X A j)
    (D : A.J.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hrad : D.radical = D)
    (hsupp : (D.support : Set A.J.left) = thetaDivisor X A (one_le_two.trans hg) j hj)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K] [Algebra ℚ K]
    (XK : CurveWithDegreeOneDivisor K) (π : XK.C ⟶ X.C)
    (hπ : IsPullback π XK.f X.f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {n m : ℕ} (φNP : ProjectiveEmbedding XK.f n)
    (φB : haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
      ProjectiveEmbedding (pullback.fst XK.f XK.f ≫ XK.f) m)
    (N : ℕ) (hN : 2 * genus X.f + 1 ≤ N) (s : ℤ) (hs : 1 ≤ s)
    (L : XK.C.Modules) [hLinv : Stacks.Ample.IsInvertibleModule XK.C L]
    (hL : Stacks.SheafOfModules.picardClass XK.C.presheaf
        (Stacks.RingedSpace.structureIsSheaf XK.C.toRingedSpace) L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hLinv) =
      Stacks.Picard.schemePullbackClassHom π ((N : ℤ) • X.P.sum fun x n =>
        haveI : Smooth X.f := SmoothOfRelativeDimension.smooth 1 X.f
        haveI : IsCurve k X.f := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one X.f
        haveI := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal X.f x
        n • Stacks.Divisors.picardClass (Stacks.Zeta.pointIdeal x)))
    (M : (pullback XK.f XK.f).Modules) [hMinv : Stacks.Ample.IsInvertibleModule _ M]
    (hM : Stacks.SheafOfModules.picardClass (pullback XK.f XK.f).presheaf
        (Stacks.RingedSpace.structureIsSheaf (pullback XK.f XK.f).toRingedSpace) M
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hMinv) =
      Stacks.Picard.schemePullbackClassHom (pullback.map XK.f XK.f X.f X.f π π
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) hπ.w.symm hπ.w.symm)
        (X.vojtaClass s s (-1))) :
    letI : XK.C.Over (Spec (.of K)) := ⟨XK.f⟩
    letI : (pullback XK.f XK.f).Over (Spec (.of K)) := ⟨pullback.fst XK.f XK.f ≫ XK.f⟩
    haveI := (IsSmoothProjectiveCurve.surface_pullback K XK.f XK.f).1
    haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.trans ℚ k K
    ∀ (x : Module.Basis (Fin (n + 1)) K Γ(L, ⊤))
      (hx : Stacks.ProjectiveFromSections.GeneratesStalks ⇑x),
      φNP.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑x hx XK.f →
    ∀ (y : Module.Basis (Fin (m + 1)) K Γ(M, ⊤))
      (hy : Stacks.ProjectiveFromSections.GeneratesStalks ⇑y),
      φB.hom = Stacks.ProjectiveFromSections.toProjectiveSpaceOver ⇑y hy
        (pullback.fst XK.f XK.f ≫ XK.f) →
    -- the `K`-point `z ≫ π` of `C` over `k`
    let pt : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Over.mk X.f) := fun z =>
      Over.homMk (z.1 ≫ π) (by simp [hπ.w, reassoc_of% z.2])
    -- the Néron pairing `⟨z, w⟩ = ⟨j z, j w⟩`
    let pair : {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} →
        {p : Spec (.of K) ⟶ XK.C // p ≫ XK.f = 𝟙 _} → ℝ := fun z w =>
      neronPairing X A (one_le_two.trans hg) j hj D hrad hsupp K
        (.ofMul (pt z ≫ j)) (.ofMul (pt w ≫ j))
    let g : ℝ := genus X.f
    ∃ κ₁ κ₂ κ₃ : ℝ, 0 ≤ κ₁ ∧ 0 ≤ κ₂ ∧ 0 ≤ κ₃ ∧ ∀ (d₁ d₂ d : ℤ) (z w),
      |XK.vojtaHeight φNP φB s N d₁ d₂ d z w -
          (d₁ / (2 * g) * pair z z + d₂ / (2 * g) * pair w w - d * pair z w)| ≤
        κ₃ / (2 * g) * (|(d₁ : ℝ)| * √(pair z z) + |(d₂ : ℝ)| * √(pair w w)) +
          κ₁ / N * (|(d₁ : ℝ)| + |(d₂ : ℝ)|) + κ₂ * |(d : ℝ)| := by
  intro x hx hφNP y hy hφB
  exact exists_abs_vojtaHeight_sub_neronPairing_le_of_nonempty_iso X A hg j hj D hrad hsupp K XK π
    hπ φNP φB N hN s hs L hL M hM
    (by rw [hφNP]; exact nonempty_pullback_twistingSheafAtUniverse_iso _ hx _)
    (by rw [hφB]; exact nonempty_pullback_twistingSheafAtUniverse_iso _ hy _)

end Faltings
