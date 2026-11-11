module

public import Mordell.MordellWeil.DescentHeight
public import Mordell.MordellWeil.Weak
public import Mordell.NeronTate.Existence
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import Mordell.Jacobian.PicZeroFunctor

/-!
# The Mordell–Weil theorem

Let `A` be an abelian variety over a number field `k`. Then the group `A(k)` of `k`-rational
points of `A` is finitely generated.

The group `A(k)` is commutative because `A` is, and by the weak Mordell–Weil theorem
`A(k) / 2 A(k)` is finite. Let `ψ` be a projective embedding of `A` and `ℳ = Ψ^* 𝒪(1)` for the
Segre product `Ψ = ([-1]^* ψ) ⊗ ψ`, again a projective embedding; then
`ℳ ≅ [-1]^* ψ^* 𝒪(1) ⊗ ψ^* 𝒪(1)` is ample and even. A Néron–Tate height of the class of `ℳ`
on `A_{k̄}` gives a height `h` of that class with `h = ½ B(x, x) + L(x) + O(1)`, `B` symmetric
biadditive and `L` additive, so `q(P) = ½ B(P, P)` is a descent height for `2` on `A(k)`, and
the descent theorem `CommGroup.fg_of_descent` concludes.

## Main results

* `Faltings.group_fg_of_numberField`: for an abelian variety `A` over a number field `k`, the
  group `A(k)` is finitely generated.
* `Faltings.group_fg_points_of_numberField`: for an abelian variety `A` over a field `k` and a
  number field `K` with `k → K`, the group `A(K)` is finitely generated.

## Implementation notes

An abelian variety over `k` is a group object `A` in `Over (Spec k)` whose structure morphism
is proper and geometrically integral. The `k`-points `A(k)` are the morphisms
`Over.mk (𝟙 (Spec k)) ⟶ A`, a group under `CategoryTheory.Hom.group`, written
multiplicatively; finite generation is therefore `Group.FG`.

The even ample sheaf is built directly as `Ψ^* 𝒪(1)` for the Segre product
`Ψ = (ψ ∘ [-1]) ⊗ ψ`, rather than through an embedding `φ` with `[-1]^* φ = σ ∘ φ` for an
automorphism `σ` of `ℙⁿ`, which would need `σ^* 𝒪(1) ≅ 𝒪(1)`.

## References

* [E. Bombieri, *The Mordell conjecture revisited*][bombieri1990]
* X. Wu, *Diophantine geometry*, Theorem 5.1
* J. S. Milne, *Abelian varieties*, Theorem I.16.7
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Theorem VIII.6.7
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped MonObj

universe u

namespace Faltings

/-- **Descent for `m = 2`.** A commutative group `G` with `G / G²` finite carrying a descent
height `q` for `2` (`q(P Q) ≤ 2 q(P) + C₁(Q)`, `4 q(P) - C₂ ≤ q(P²)`, Northcott) is finitely
generated. -/
private lemma group_fg_of_descentHeight_two {G : Type*} [Group G]
    (hcomm : ∀ a b : G, a * b = b * a)
    (hfi : (Subgroup.closure (Set.range fun P : G => P ^ 2)).FiniteIndex) (q : G → ℝ)
    (h₁ : ∀ Q, ∃ C : ℝ, ∀ P, q (P * Q) ≤ 2 * q P + C)
    (h₂ : ∃ C : ℝ, ∀ P, ((2 : ℕ) : ℝ) ^ 2 * q P - C ≤ q (P ^ 2)) (h₃ : Northcott q) :
    Group.FG G := by
  let : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  choose c hc using h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine CommGroup.fg_of_descent (h := q) (n := 2) (a := 2) (b := 4) (c₀ := C₂)
    (c := fun g => c g⁻¹) (by norm_num) (by norm_num)
    (Subgroup.closure_eq (powMonoidHom 2 : G →* G).range ▸ hfi) (fun g x => ?_) (fun x => ?_)
  · simpa [mul_inv_cancel_comm] using hc g⁻¹ (g * x)
  · have := hC₂ x
    norm_num at this ⊢
    linarith

/-- The class of the pullback `f^* L` of an invertible sheaf, in the spelling
`Scheme.Modules.pullback`, is the pullback `f^* [L]` of its class. -/
private lemma picardClass_pullback_eq_pullbackPicardHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L] :
    X.picardClass ((Scheme.Modules.pullback f).obj L)
        (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback f L) =
      Stacks.SheafOfModules.pullbackPicardHom f (Y.picardClass L ‹_›) :=
  ((Scheme.picardClass_eq_iff X _ _ _ _).mpr
    ⟨((Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjointUniq
      (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        f.toLRSHom.toShHom)).app L⟩).trans
    (Stacks.SheafOfModules.pullbackPicardHom_picardClass f L _).symm

/-- The class of `𝒪(1)` on `ℙʳ_S`. -/
private noncomputable abbrev twistClass (r : ℕ) (S : Scheme.{u}) :
    Stacks.Picard.ofScheme (projectiveSpaceOver r S) :=
  (projectiveSpaceOver r S).picardClass
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver r S 1)
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver r S 1)

/-- The class of `(f ⊗ ψ)^* 𝒪(1)` for a Segre product is `f^* [𝒪(1)] + ψ^* [𝒪(1)]`. -/
private lemma picardClass_pullback_segreProduct {S X : Scheme.{u}} {r m : ℕ}
    (f : X ⟶ projectiveSpaceOver r S) (ψ : X ⟶ projectiveSpaceOver m S)
    (h : f ≫ projectiveSpaceOver r S ↘ S = ψ ≫ projectiveSpaceOver m S ↘ S) :
    X.picardClass ((Scheme.Modules.pullback (segreProduct f ψ h)).obj
        (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver (r * m + r + m) S 1))
        (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _) =
      Stacks.SheafOfModules.pullbackPicardHom f (twistClass r S) +
        Stacks.SheafOfModules.pullbackPicardHom ψ (twistClass m S) := by
  obtain ⟨e⟩ := nonempty_pullback_segreProduct_projectiveSpaceTwistingSheaf_iso f ψ h
  have hL := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback f
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r S)
  have hN := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback ψ
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf m S)
  have hLN := Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ hL hN
  exact ((Scheme.picardClass_eq_iff X _ _ _ hLN).mpr ⟨e⟩).trans <|
    (X.picardClass_tensorSheaf _ _ hL hN hLN).symm.trans <|
      congrArg₂ (· + ·) (picardClass_pullback_eq_pullbackPicardHom f _)
        (picardClass_pullback_eq_pullbackPicardHom ψ _)

/-- For an involution `σ` of `X` and a morphism `ψ : X ⟶ ℙᵐ_S`, the class of
`((ψ ∘ σ) ⊗ ψ)^* 𝒪(1)` is `σ`-invariant. -/
private lemma pullbackPicardHom_picardClass_segreProduct_involution {S X : Scheme.{u}} {m : ℕ}
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (ψ : X ⟶ projectiveSpaceOver m S)
    (h : (σ ≫ ψ) ≫ projectiveSpaceOver m S ↘ S = ψ ≫ projectiveSpaceOver m S ↘ S) :
    Stacks.SheafOfModules.pullbackPicardHom σ
        (X.picardClass ((Scheme.Modules.pullback (segreProduct (σ ≫ ψ) ψ h)).obj
          (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver (m * m + m + m) S 1))
          (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _)) =
      X.picardClass ((Scheme.Modules.pullback (segreProduct (σ ≫ ψ) ψ h)).obj
          (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver (m * m + m + m) S 1))
          (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _) := by
  rw [picardClass_pullback_segreProduct, map_add,
    ← Stacks.SheafOfModules.pullbackPicardHom_comp_apply,
    ← Stacks.SheafOfModules.pullbackPicardHom_comp_apply, ← Category.assoc, hσ,
    Category.id_comp, add_comm]

/-- For a field extension `K/k`, a `K`-point `x` of a `k`-group `A` is the `K`-point `(x, 1)` of
the base change `A_K`; this is a group homomorphism `A(K) →* A_K(K)`. -/
private noncomputable def toBaseChangePoint (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : Over (Spec (.of k))) [GrpObj A] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) →*
      (Over.mk (𝟙 (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) :=
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have key : ∀ x : Over.mk g ⟶ A,
      (Over.homMk (pullback.lift x.left (𝟙 _) (by simp)) (pullback.lift_snd _ _ _) :
        Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback g).obj A) =
      Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _) ≫
        (Over.pullback g).map x := fun x => by
    ext1
    apply pullback.hom_ext <;>
      simp only [Over.mk_hom, Over.comp_left, Over.homMk_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.id_comp]
  { toFun := fun x => Over.homMk (pullback.lift x.left (𝟙 _) (by simp))
      (pullback.lift_snd _ _ _)
    map_one' := by
      change _ = (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback g).obj A)
      rw [key, Functor.map_one, MonObj.comp_one]
      rfl
    map_mul' := fun x y => by
      change _ = (_ : Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback g).obj A) * _
      rw [key, key, key, Functor.map_mul, MonObj.comp_mul]
      rfl }

/-- **Mordell–Weil theorem.** Let `A` be an abelian variety over a number field `k`. Then the
group `A(k)` of `k`-points of `A` is finitely generated. -/
@[faltings "thm_mw_mordell_weil"]
theorem group_fg_of_numberField
    (k : Type u) [Field k] [NumberField k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] :
    Group.FG (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProperVariety k A.hom := .mk (toIsVariety := .mk)
  have : IsAbelianVariety k A := ⟨⟩
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have : IsProjectiveVariety k A.hom :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)⟩
  let kbar := AlgebraicClosure k
  have : Algebra.IsAlgebraic ℚ kbar := Algebra.IsAlgebraic.trans ℚ k kbar
  let g : Spec (.of kbar) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
  let A' := (Over.pullback g).obj A
  have : IsVariety kbar (pullback.snd A.hom g) :=
    (inferInstance : IsAbelianVariety kbar A').toIsProperVariety.toIsVariety
  have : IsProjectiveVariety kbar (pullback.snd A.hom g) :=
    ⟨isProjectiveMorphism_of_isProjective_of_isAffine (f := A'.hom)
      (isProjective_of_isAbelianVariety kbar A')⟩
  have : Smooth (pullback.snd A.hom g) := smooth_of_isAbelianVariety kbar A'
  -- a projective embedding `ψ` of `A`
  obtain ⟨n, ψ, hψ, hψA⟩ : ∃ (n : ℕ) (ψ : A.left ⟶ projectiveSpaceOver n (Spec (.of k))),
      IsClosedImmersion ψ ∧ ψ ≫ pullback.fst _ _ = A.hom :=
    isProjectiveMorphism_of_isProjective_of_isAffine (f := A.hom)
      (isProjective_of_isAbelianVariety k A)
  let ψe : ProjectiveEmbedding A.hom n := ⟨ψ, hψ, hψA⟩
  -- the Segre product `Ψ = (ψ ∘ [-1]) ⊗ ψ` and the even ample sheaf `ℳ = Ψ^* 𝒪(1)`
  have hι : (ι[A].left ≫ ψ) ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) =
      ψ ≫ projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k) := by
    rw [Category.assoc, ψe.hom_over, Over.w]
  obtain ⟨⟨Ψ, hΨ, hΨA⟩, rfl⟩ :=
    ProjectiveEmbedding.exists_hom_eq_segreProduct (ι[A].left ≫ ψ) ψe hι
  let φ : ProjectiveEmbedding A.hom (n * n + n + n) := ⟨_, hΨ, hΨA⟩
  let O1 := Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver (n * n + n + n) (Spec (.of k)) 1
  let M : A.left.Modules := (Scheme.Modules.pullback φ.hom).obj O1
  have : Stacks.Ample.IsInvertibleModule A.left M :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback φ.hom O1
  have hM : IsAmple A.hom M :=
    ⟨1, le_rfl, n * n + n + n, φ, ⟨Stacks.Ample.tensorPowModuleOneIso _ M⟩⟩
  have heven := pullbackPicardHom_picardClass_segreProduct_involution ι[A].left
    (by rw [← Over.comp_left, GrpObj.inv_comp_inv]; rfl) ψ hι
  have hφM : Stacks.SheafOfModules.pullbackPicardClass φ.hom O1
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver _ _ 1) =
      ((1 : ℕ) : ℤ) • A.left.picardClass M ‹_› := by
    rw [Nat.cast_one, one_smul]
    exact (Stacks.SheafOfModules.pullbackPicardHom_picardClass φ.hom O1 _).symm.trans
      (picardClass_pullback_eq_pullbackPicardHom φ.hom O1).symm
  -- a Néron–Tate height of the class of `ℳ` on `A_{k̄}`
  -- and read on `A(k̄)` through `A(k̄) →* A_{k̄}(k̄)`
  obtain ⟨f, ⟨h, hh, C, hC⟩, b, hbs, ℓ, hf⟩ := exists_isNeronTateHeight_of_isAlgebraic A'
    ((1 : ℚ) ⊗ₜ Stacks.SheafOfModules.pullbackPicardHom (pullback.fst A.hom g)
      (A.left.picardClass M ‹_›))
  rw [TensorProduct.comm_tmul] at hh
  let e := toBaseChangePoint k kbar A
  obtain ⟨h₁, h₂, h₃⟩ := descentHeight_half_bilinear_of_numberField k kbar A M hM heven
    (n * n + n + n) 1 le_rfl φ hφM h hh (fun x y => b (.ofMul (e x)) (.ofMul (e y)))
    (fun x y z => by simp only [map_mul, ofMul_mul, map_add, AddMonoidHom.add_apply])
    (fun x y => hbs _ _) (fun x => ℓ (.ofMul (e x)))
    (fun x y => by simp only [map_mul, ofMul_mul, map_add])
    ⟨C, fun x => by
      have := hC ⟨pullback.lift x.left (𝟙 _) (by simp [g]), pullback.lift_snd _ _ _⟩
      rwa [hf, abs_sub_comm] at this⟩ 2 le_rfl
  exact group_fg_of_descentHeight_two (fun a b => CommSemigroup.mul_comm a b)
    (finiteIndex_closure_range_pow_of_numberField k A two_ne_zero) _ h₁ h₂ h₃

/-- **Mordell–Weil over an extension.** For an abelian variety `A` over a field `k` and a number
field `K` with `k → K`, the group `A(K)` of morphisms `Spec K ⟶ A` over `Spec k` is finitely
generated: it is isomorphic to the group `A_K(K)` of `K`-points of the base change `A_K`, which
is finitely generated by `Faltings.group_fg_of_numberField`. -/
theorem group_fg_points_of_numberField {k : Type u} [Field k] (K : Type u) [Field K]
    [NumberField K] [Algebra k K] (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A] :
    Group.FG (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have := group_fg_of_numberField K ((Over.pullback φ).obj A)
  let u : Over.mk φ ⟶ (Over.map φ).obj (Over.mk (𝟙 (Spec (.of K)))) := Over.homMk (𝟙 _)
  let v : (Over.map φ).obj (Over.mk (𝟙 (Spec (.of K)))) ⟶ Over.mk φ := Over.homMk (𝟙 _)
  let E := GroupScheme.pointsMulEquiv φ A (Over.mk (𝟙 (Spec (.of K))))
  refine Group.fg_of_surjective (f := ((yonedaMonObj A).map u.op).hom.comp E.toMonoidHom)
    fun x => ⟨E.symm (v ≫ x), ?_⟩
  change u ≫ E (E.symm (v ≫ x)) = x
  rw [MulEquiv.apply_symm_apply, ← Category.assoc]
  convert Category.id_comp x
  ext
  simp [u, v]

end Faltings


/-!
# The Mordell–Weil theorem for the Jacobian of a curve

Let `C` be a smooth projective geometrically integral curve over a number field `k`, and let
`(J, ι)` be a Jacobian of `C`: an abelian variety `J` over `k` together with a morphism of
functors `ι : P⁰_C ⟶ J` from the relative Picard functor of degree zero of `C` to the functor of
points `T ↦ J(T)` of `J`, such that `ι(T) : P⁰_C(T) → J(T)` is bijective for every `k`-scheme
`T` with `C(T) ≠ ∅`. Then the group `J(k)` of `k`-rational points of `J` is finitely generated.

## Main results

* `Faltings.group_fg_jacobian_of_numberField`: for a Jacobian `(J, ι)` of a curve `C` over a
  number field `k`, the group `J(k)` is finitely generated.

## Implementation notes

The curve is `f : C ⟶ Spec k` with `[Faltings.IsSmoothProjectiveCurve k f]`, and `P⁰_C` is
`Faltings.relativePicZeroFunctor k f`, a functor on `Over (Spec k)` valued in abelian groups.
An abelian variety over `k` is a group object `J` of `Over (Spec k)` whose structure morphism is
proper and geometrically integral. Its functor of points is `yoneda.obj J`, and `ι` is a natural
transformation from `P⁰_C` composed with the forgetful functor to it; bijectivity of `ι(T)` is
`IsIso` in the category of types, and `C(T) ≠ ∅` is the existence of a `k`-morphism
`T ⟶ Over.mk f`. The `k`-points `J(k)` are the morphisms `Over.mk (𝟙 (Spec k)) ⟶ J`, a group
under `CategoryTheory.Hom.group`, written multiplicatively, so finite generation is `Group.FG`.

The proof uses only that `J` is an abelian variety over `k`: it is the Mordell–Weil theorem
`Faltings.group_fg_of_numberField`, and the curve `C` and the map `ι` play no role in it.

## References

* [Bombieri, *The Mordell conjecture revisited*], Section 5.
* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Section 1.
* X. Wu, *Diophantine geometry*, Theorem 5.1.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped MonObj

namespace Faltings

/-- **Mordell–Weil theorem for Jacobians.** Let `f : C ⟶ Spec k` be a smooth projective
geometrically integral curve over a number field `k`, and let `(J, ι)` be a Jacobian of `C`: an
abelian variety `J` over `k` and a morphism `ι` from the relative Picard functor of degree zero
`Faltings.relativePicZeroFunctor k f` to the functor of points of `J`, bijective on every
`k`-scheme `T` admitting a `k`-morphism `T ⟶ C`. Then the group `J(k)` of `k`-points of `J` is
finitely generated. -/
@[faltings "thm_mw_mordell_weil_jacobian"]
theorem group_fg_jacobian_of_numberField
    (k : Type u) [Field k] [NumberField k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f]
    (J : Over (Spec (CommRingCat.of k))) [GrpObj J] [IsProper J.hom]
    [GeometricallyIntegral J.hom]
    (ιJ : relativePicZeroFunctor k f ⋙ forget AddCommGrpCat ⟶ yoneda.obj J)
    (hιJ : ∀ T : Over (Spec (CommRingCat.of k)), Nonempty (T ⟶ Over.mk f) →
      IsIso (ιJ.app (op T))) :
    Group.FG (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J) :=
  group_fg_of_numberField k J

end Faltings
