module

public import Mordell.Height.Class.Functoriality
public import Mordell.Height.Class.AmpleBoundedBelow
public import Mordell.Height.Class.Northcott
public import Mordell.MordellWeil.TorsionLifting

/-!
# The Néron–Tate height of an even ample class is a descent height

Let `A` be an abelian variety over a number field `k`, `𝓜` an ample invertible sheaf on `A`
which is even (`[-1]^* 𝓜 ≅ 𝓜`), `r ≥ 1` and `φ : A → ℙⁿ_k` a closed immersion with
`φ^* 𝒪(1) ≅ 𝓜^{⊗ r}`, and `c` the class of `𝓜`. Let `h_c` be a height associated to `c` on
`A(k̄)`, and `B` a symmetric biadditive form and `L` an additive function on `A(k̄)` with
`h_c = ½ B(x, x) + L(x) + O(1)`. Then for every `m ≥ 2` the function `q(P) = ½ B(P, P)` is a
descent height for `m` on `A(k)`:

* for every `Q ∈ A(k)` there is `C₁(Q)` with `q(P + Q) ≤ 2 q(P) + C₁(Q)` for all `P`;
* there is `C₂` with `q(m P) ≥ m² q(P) - C₂` for all `P`;
* for every `C₃` the set `{P ∈ A(k) : q(P) ≤ C₃}` is finite.

## Main results

* `Faltings.descentHeight_half_bilinear_of_numberField`: `q(P) = ½ B(P, P)` satisfies the three
  conditions above on `A(k)`.

## Implementation notes

The abelian variety is a group object `A` in `Over (Spec k)` whose structure morphism is proper
and geometrically integral. Its points `A(k) = Over.mk (𝟙 (Spec k)) ⟶ A` and
`A(k̄) = Over.mk (Spec k̄ → Spec k) ⟶ A` are groups under `CategoryTheory.Hom.group`, written
multiplicatively; `A(k) → A(k̄)` is precomposition with `Spec k̄ → Spec k`, and `[-1]` is the
inverse `ι[A]` of the group object. The forms are real functions with their laws stated
pointwise: `B (x * y) z = B x z + B y z`, `B x y = B y x`, `L (x * y) = L x + L y`.

Heights in the sense of `Faltings.IsHeightOfClass` live on the `k̄`-points of a variety over
`k̄`, so `h_c` is a function on the sections of the base change
`A_{k̄} = A ×_{Spec k} Spec k̄ → Spec k̄`, associated to the pullback of `c ⊗ 1` along
`A_{k̄} → A`; a point `x ∈ A(k̄)` is read as the section `(x, 𝟙)` of `A_{k̄}`. The base change
is assumed smooth and projective over `k̄` and `A` projective over `k`, as these notions require;
all three hold for an abelian variety over a field of characteristic zero carrying the
embedding `φ`. The embedding `φ` is a `Faltings.ProjectiveEmbedding` and `φ^* 𝒪(1) ≅ 𝓜^{⊗ r}` is
the equality `[φ^* 𝒪(1)] = r [𝓜]` in `Pic(A)`; evenness is `[-1]^* [𝓜] = [𝓜]`. A descent height
is written out as its three conditions, the last as Mathlib's `Northcott`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
* J. S. Milne, *Abelian varieties*, Theorem I.16.7
* J.-P. Serre, *Lectures on the Mordell–Weil theorem*, Chapter 4
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped MonObj

universe u

namespace Faltings

/-- A function `f : G → ℝ` turning products into sums sends inverses to negatives. -/
private lemma map_inv_of_map_mul {G : Type*} [Group G] {f : G → ℝ}
    (hf : ∀ x y, f (x * y) = f x + f y) (x : G) : f x⁻¹ = -f x :=
  congrArg Multiplicative.toAdd (map_inv (MonoidHom.mk' (Multiplicative.ofAdd ∘ f) hf) x)

/-- A function `f : G → ℝ` turning products into sums sends `m`-th powers to `m`-fold multiples. -/
private lemma map_pow_of_map_mul {G : Type*} [Group G] {f : G → ℝ}
    (hf : ∀ x y, f (x * y) = f x + f y) (x : G) (m : ℕ) : f (x ^ m) = m * f x :=
  (congrArg Multiplicative.toAdd (map_pow (MonoidHom.mk' (Multiplicative.ofAdd ∘ f) hf) x m)).trans
    (nsmul_eq_mul m (f x))

/-- The parallelogram law for the diagonal of a symmetric biadditive form on a group. -/
private lemma diag_mul_add_diag_mul_inv {H : Type*} [Group H] {B : H → H → ℝ}
    (hBadd : ∀ x y z, B (x * y) z = B x z + B y z) (hBsymm : ∀ x y, B x y = B y x) (x y : H) :
    B (x * y) (x * y) + B (x * y⁻¹) (x * y⁻¹) = 2 * B x x + 2 * B y y := by
  have hBadd' : ∀ x y z, B z (x * y) = B z x + B z y := fun x y z => by
    rw [hBsymm, hBadd, hBsymm x, hBsymm y]
  simp only [hBadd, hBadd', map_inv_of_map_mul (f := (B · _)) (hBadd · · _),
    map_inv_of_map_mul (f := B _) (hBadd' · · _), hBsymm y x]
  ring

/-- The diagonal of a symmetric biadditive form on a group is homogeneous of degree two. -/
private lemma diag_pow {H : Type*} [Group H] {B : H → H → ℝ}
    (hBadd : ∀ x y z, B (x * y) z = B x z + B y z) (hBsymm : ∀ x y, B x y = B y x) (x : H)
    (m : ℕ) : B (x ^ m) (x ^ m) = (m : ℝ) ^ 2 * B x x := by
  rw [map_pow_of_map_mul (f := (B · _)) (hBadd · · _), hBsymm,
    map_pow_of_map_mul (f := (B · _)) (hBadd · · _), hBsymm]
  ring

/-- If `h = ½ B(x, x) + L + O(1)` with `B` biadditive and `L` additive, and `h` is even up to
`O(1)` at `x`, then `L x` is bounded: the quadratic part is even and the linear part is odd. -/
private lemma abs_additive_le_of_even {H : Type*} [Group H] {B : H → H → ℝ}
    (hBadd : ∀ x y z, B (x * y) z = B x z + B y z) (hBsymm : ∀ x y, B x y = B y x)
    {L : H → ℝ} (hL : ∀ x y, L (x * y) = L x + L y) {h : H → ℝ} {C₀ C₂ : ℝ}
    (hC₀ : ∀ x, |h x - (B x x / 2 + L x)| ≤ C₀) {x : H} (hx : |h x⁻¹ - h x| ≤ C₂) :
    |L x| ≤ C₀ + C₂ / 2 := by
  have e := hC₀ x⁻¹
  rw [map_inv_of_map_mul (f := (B · _)) (hBadd · · _), hBsymm,
    map_inv_of_map_mul (f := (B · _)) (hBadd · · _), hBsymm, map_inv_of_map_mul hL] at e
  have e' := hC₀ x
  rw [abs_le] at *
  constructor <;> linarith [e.1, e.2, e'.1, e'.2, hx.1, hx.2]

/-- The abstract descent-height argument: let `q = ½ B(t ·, t ·)` for a symmetric biadditive
`B` on `H` and a homomorphism `t : G →* H`. If `h = ½ B(x, x) + L(x) + O(1)` with `L` additive,
`h ∘ t` is even up to `O(1)`, bounded below and has the Northcott property, then `q` satisfies
the three descent conditions. -/
private lemma descent_of_biadditive {G H : Type*} [Group G] [Group H] (t : G →* H)
    (B : H → H → ℝ) (hBadd : ∀ x y z, B (x * y) z = B x z + B y z)
    (hBsymm : ∀ x y, B x y = B y x) (L : H → ℝ) (hL : ∀ x y, L (x * y) = L x + L y)
    (h : H → ℝ) (hhB : ∃ C : ℝ, ∀ x, |h x - (B x x / 2 + L x)| ≤ C)
    (hN : Northcott fun P => h (t P)) (hlb : ∃ C : ℝ, ∀ P, C ≤ h (t P))
    (heven : ∃ C : ℝ, ∀ P, |h (t P⁻¹) - h (t P)| ≤ C) (m : ℕ) :
    let q := fun P => B (t P) (t P) / 2
    (∀ Q, ∃ C : ℝ, ∀ P, q (P * Q) ≤ 2 * q P + C) ∧
      (∃ C : ℝ, ∀ P, (m : ℝ) ^ 2 * q P - C ≤ q (P ^ m)) ∧ Northcott q := by
  intro q
  obtain ⟨C₀, hC₀⟩ := hhB
  obtain ⟨C₁, hC₁⟩ := hlb
  obtain ⟨C₂, hC₂⟩ := heven
  set E := C₀ + (C₀ + C₂ / 2) with hE
  have hqw (P : G) : |q P - h (t P)| ≤ E := by
    have e1 := hC₀ (t P)
    have e2 := abs_additive_le_of_even hBadd hBsymm hL hC₀ (x := t P) (by simpa using hC₂ P)
    simp only [q]
    rw [abs_le] at *
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hE]
  have hqlb (P : G) : C₁ - E ≤ q P := by linarith [(abs_le.1 (hqw P)).1, hC₁ P]
  refine ⟨fun Q => ⟨2 * q Q + (E - C₁), fun P => ?_⟩, ⟨0, fun P => ?_⟩,
    ⟨fun c => (hN.finite_le (c + E)).subset fun P hP => ?_⟩⟩
  · have := hqlb (P * Q⁻¹)
    simp only [q, map_mul, map_inv] at this ⊢
    linarith [diag_mul_add_diag_mul_inv hBadd hBsymm (t P) (t Q)]
  · simp [q, map_pow, diag_pow hBadd hBsymm, mul_div_assoc]
  · simp only [Set.mem_ofPred_eq] at hP ⊢
    linarith [(abs_le.1 (hqw P)).1]

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {Y : Scheme.{u}}
  {fY : Y ⟶ Spec (.of k)} [IsProjectiveVariety k fY]
  [IsProjectiveVariety K (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))]

/-- The class of `𝒪(1)` on `ℙⁿ_K` is the pullback of the class of `𝒪(1)` on `ℙⁿ_k`. -/
private lemma picardClass_twistOver_baseChange (n : ℕ) :
    (projectiveSpaceOver n (Spec (.of K))).picardClass
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of K)) 1)
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1) =
      Stacks.SheafOfModules.pullbackPicardClass
        (projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1)
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1) := by
  have e : projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) :=
    (projectiveSpaceOverMap_snd n _).symm
  refine ((projectiveSpaceOver n (Spec (.of K))).picardClass_eq_iff _ _ _ _).2 ⟨?_⟩
  exact (Scheme.Modules.pullbackCongr e).app _ ≪≫
    (RingedSpaceModuleAdjunction.modulePullbackComp
      (projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toLRSHom.toShHom
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).toLRSHom.toShHom).app _

/-- The base change to `K` of the class of an invertible sheaf `M` on `Y` with
`[φ^* 𝒪(1)] = r [M]` for a projective embedding `φ` and `r ≥ 1` is ample. -/
private lemma isAmpleClass_baseChange (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    {n r : ℕ} (hr : 1 ≤ r) (φ : ProjectiveEmbedding fY n)
    (hφ : Stacks.SheafOfModules.pullbackPicardClass φ.hom
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1)
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1) =
      (r : ℤ) • Y.picardClass M ‹_›) :
    IsAmpleClass (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _) (Y.picardClass M ‹_›) ⊗ₜ[ℤ]
        (1 : ℚ)) := by
  have hX := IsPullback.of_hasPullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let ψ := ProjectiveEmbedding.baseChange hX φ
  let L := (Scheme.Modules.pullback ψ.hom).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of K)))
  refine ⟨r, L, inferInstance, by exact_mod_cast hr,
    ⟨1, le_rfl, n, ψ, ⟨Stacks.Ample.tensorPowModuleOneIso _ L⟩⟩, ?_⟩
  rw [TensorProduct.smul_tmul', ← map_zsmul, ← hφ]
  congr 1
  have hT := Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n
    (Spec (.of k)) 1
  have hTK := Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n
    (Spec (.of K)) 1
  calc _ = Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _)
        (Stacks.SheafOfModules.pullbackPicardHom φ.hom
          ((projectiveSpaceOver n (Spec (.of k))).picardClass
            (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1) hT)) :=
        congrArg _ (Stacks.SheafOfModules.pullbackPicardHom_picardClass _ _ _).symm
    _ = Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _ ≫ φ.hom)
          ((projectiveSpaceOver n (Spec (.of k))).picardClass
            (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1) hT) :=
        (Stacks.SheafOfModules.pullbackPicardHom_comp_apply _ _ _).symm
    _ = Stacks.SheafOfModules.pullbackPicardHom ψ.hom
          (Stacks.SheafOfModules.pullbackPicardHom
            (projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            ((projectiveSpaceOver n (Spec (.of k))).picardClass
              (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1) hT)) := by
        rw [← Stacks.SheafOfModules.pullbackPicardHom_comp_apply]
        exact congrArg (fun g => Stacks.SheafOfModules.pullbackPicardHom g _)
          (baseChangeHom_comp_projectiveSpaceOverMap hX φ).symm
    _ = Stacks.SheafOfModules.pullbackPicardHom ψ.hom
          ((projectiveSpaceOver n (Spec (.of K))).picardClass
            (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of K)) 1) hTK) :=
        congrArg _ ((Stacks.SheafOfModules.pullbackPicardHom_picardClass _ _ _).trans
          (picardClass_twistOver_baseChange n).symm)
    _ = _ := Stacks.SheafOfModules.pullbackPicardHom_picardClass _ _ _

end BaseChange

/-- Let `A` be an abelian variety over a number field `k`, `𝓜` an even ample invertible sheaf
on `A`, `φ : A → ℙⁿ_k` a projective embedding with `[φ^* 𝒪(1)] = r [𝓜]`, `r ≥ 1`, and `h` a
height on `A(k̄)` associated to the class of `𝓜`. If `B` is a symmetric biadditive form and `L`
an additive function on `A(k̄)` with `h = ½ B(x, x) + L(x) + O(1)`, then for `m ≥ 2` the
function `q(P) = ½ B(P, P)` is a descent height for `m` on `A(k)`. -/
@[faltings "lem_mw_neron_tate_descent_height"]
theorem descentHeight_half_bilinear_of_numberField (k : Type u) [Field k] [NumberField k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [Algebra ℚ kbar] [Algebra.IsAlgebraic ℚ kbar]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] [IsProjectiveVariety k A.hom]
    [IsProjectiveVariety kbar
      (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    [Smooth (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (M : A.left.Modules) [Stacks.Ample.IsInvertibleModule A.left M] (hM : IsAmple A.hom M)
    (heven : Stacks.SheafOfModules.pullbackPicardHom ι[A].left (A.left.picardClass M ‹_›) =
      A.left.picardClass M ‹_›)
    (n r : ℕ) (hr : 1 ≤ r) (φ : ProjectiveEmbedding A.hom n)
    (hφ : Stacks.SheafOfModules.pullbackPicardClass φ.hom
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec (.of k)) 1)
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n _ 1) =
      (r : ℤ) • A.left.picardClass M ‹_›)
    (h : {p : Spec (.of kbar) ⟶ pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) //
      p ≫ pullback.snd _ _ = 𝟙 _} → ℝ)
    (hh : IsHeightOfClass (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _) (A.left.picardClass M ‹_›) ⊗ₜ[ℤ]
        (1 : ℚ)) h)
    (B : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) →
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) → ℝ)
    (hBadd : ∀ x y z, B (x * y) z = B x z + B y z) (hBsymm : ∀ x y, B x y = B y x)
    (L : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) → ℝ)
    (hL : ∀ x y, L (x * y) = L x + L y)
    (hhB : ∃ C : ℝ, ∀ x,
      |h ⟨pullback.lift x.left (𝟙 _) (by simpa using x.w), pullback.lift_snd _ _ _⟩ -
        (B x x / 2 + L x)| ≤ C)
    (m : ℕ) (hm : 2 ≤ m) :
    let toBar : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) →
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) := fun P =>
      Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
        (V := Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp) ≫ P
    let q := fun P => B (toBar P) (toBar P) / 2
    (∀ Q, ∃ C : ℝ, ∀ P, q (P * Q) ≤ 2 * q P + C) ∧
      (∃ C : ℝ, ∀ P, (m : ℝ) ^ 2 * q P - C ≤ q (P ^ m)) ∧ Northcott q := by
  intro toBar q
  -- the `k̄`-points of `A_{k̄}` attached to points of `A(k̄)`
  let bar : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) →
      {p : Spec (.of kbar) ⟶ pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) //
        p ≫ pullback.snd _ _ = 𝟙 _} := fun x =>
    ⟨pullback.lift x.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
  let s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (by simp)
  let t : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶ A) :=
    { toFun := fun P => s ≫ P
      map_one' := MonObj.comp_one s
      map_mul' := fun P Q => MonObj.comp_mul s P Q }
  have hev : ∃ C : ℝ, ∀ x, |h (bar x⁻¹) - h (bar x)| ≤ C := by
    let g : pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) ⟶
        pullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) :=
      pullback.map _ _ _ _ ι[A].left (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hg : g ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [g]
    have h1 := IsHeightOfClass.comp g hg hh
    have hc : LinearMap.rTensor ℚ (Stacks.SheafOfModules.pullbackPicardHom g).toIntLinearMap
        (Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _) (A.left.picardClass M ‹_›)
          ⊗ₜ[ℤ] (1 : ℚ)) =
        Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _) (A.left.picardClass M ‹_›)
          ⊗ₜ[ℤ] (1 : ℚ) := by
      rw [LinearMap.rTensor_tmul]
      congr 1
      change Stacks.SheafOfModules.pullbackPicardHom g
        (Stacks.SheafOfModules.pullbackPicardHom (pullback.fst _ _) _) = _
      rw [← Stacks.SheafOfModules.pullbackPicardHom_comp_apply]
      have : g ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) =
          pullback.fst _ _ ≫ ι[A].left := by simp [g]
      rw [this, Stacks.SheafOfModules.pullbackPicardHom_comp_apply, heven]
    rw [hc] at h1
    obtain ⟨C, hC⟩ := h1.exists_abs_sub_le hh
    refine ⟨C, fun x => ?_⟩
    have hx : bar x⁻¹ = ⟨(bar x).1 ≫ g, by rw [Category.assoc, hg, (bar x).2]⟩ := by
      apply Subtype.ext
      apply pullback.hom_ext <;> simp [bar, g, Hom.inv_def, pullback.lift_fst_assoc]
    rw [hx]
    exact hC _
  have hamp := isAmpleClass_baseChange (K := kbar) M hr φ hφ
  have hN : Northcott fun P => h (bar (t P)) := by
    let F : FieldOfDefinition kbar
        (pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) k :=
      { model := A.left, toSpec := A.hom, isVariety := inferInstance, iso := Iso.refl _,
        iso_hom_snd := by simp }
    have hdeg (P : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) :
        F.pointDegree (bar (t P)).1 (bar (t P)).2 ≤ 1 := by
      have hle : F.pointResidueField (bar (t P)).1 (bar (t P)).2 ≤ ⊥ := by
        intro x hx
        rw [IntermediateField.mem_bot]
        refine fieldRange_descResidueField_le (algebraMap k kbar) P.left ?_ hx
        simp [F, bar, t, s]
      rw [FieldOfDefinition.pointDegree, le_bot_iff.1 hle, IntermediateField.finrank_bot]
    have hinj : Function.Injective fun P => bar (t P) := by
      intro P Q hPQ
      have e := congrArg (fun p => p.1 ≫ pullback.fst _ _) hPQ
      simp only [bar, t, s, pullback.lift_fst] at e
      have := epi_spec_map_algebraMap k kbar
      exact Over.OverMorphism.ext ((cancel_epi _).1 (by simpa using e))
    refine ⟨fun c => ((hh.finite_setOf_pointDegree_le_and_le F hamp 1 le_rfl c).preimage
      hinj.injOn).subset fun P hP => ⟨hdeg P, hP⟩⟩
  obtain ⟨Cl, hCl⟩ := hh.exists_le_of_isAmpleClass hamp
  obtain ⟨Ce, hCe⟩ := hev
  exact descent_of_biadditive t B hBadd hBsymm L hL (fun x => h (bar x)) hhB hN
    ⟨Cl, fun P => hCl _⟩ ⟨Ce, fun P => by simpa using hCe (t P)⟩ m

end Faltings
