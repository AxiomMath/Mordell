module
public import Mordell.Jacobian.Basic
public import Mordell.AlgebraicGeometry.GroupScheme.BaseChangePoints

/-!
# The Jacobian commutes with field extension

Let `C` be a smooth projective curve over a field `k`, with structure morphism
`f : C ⟶ Spec k`, let `(J, ι)` be a Jacobian of `C`, and let `K/k` be a field extension, with
`π : Spec K ⟶ Spec k`. The base change `C_K = C ×_k K` is again a smooth projective curve, and
`J_K = J ×_k K` is a Jacobian of it, with the morphism of functors `ι_K` obtained by restricting
`ι` to `K`-schemes: for a `K`-scheme `T`, regarded as a `k`-scheme `T_k` through `π`, the
canonical isomorphism `C_K ×_K T ≅ C ×_k T_k` identifies `P⁰_{C_K}(T)` with `P⁰_C(T_k)`, and
`J_K(T) = Hom_K(T, J_K)` is `Hom_k(T_k, J) = J(T_k)` by composing with the projection
`J_K ⟶ J`; `ι_K(T)` is `ι(T_k)` read through these identifications.

## Main results

* `Faltings.Jacobian.exists_baseChange`: `C_K` is a smooth projective curve over `K`, and it has
  a Jacobian whose abelian variety is `J_K`, with the group law and abelian-variety structure of
  the base change, and whose morphism `ι_K` is the restriction of `ι`.
* `Faltings.Jacobian.map_add_of_baseChange`: any restriction `ι_K` of `ι` is additive.
* `Faltings.Jacobian.isIso_app_of_baseChange`: any restriction `ι_K` of `ι` is bijective on
  every `K`-scheme `T` with `C_K(T) ≠ ∅`.

## Implementation notes

The base change of `J` is `(Over.pullback π).obj J`, with the group law and the abelian-variety
structure given by `AlgebraicGeometry.grpObjPullbackObj` and
`AlgebraicGeometry.isAbelianVariety_pullbackObj`; the base-changed curve is
`pullback.snd f π`. That it is a smooth projective curve over `K` is part of the conclusion of
`Faltings.Jacobian.exists_baseChange` (smoothness of relative dimension one and projectivity are
stable under base change), since it is needed to form `P⁰_{C_K}` and `Jacobian K C_K` at all.

The morphism `ι_K` is characterised elementwise: whenever a fibrewise-degree-zero class `b` on
`C_K ×_K T` is the pull-back of a class `a` on `C ×_k T_k` along the canonical morphism
`C_K ×_K T ⟶ C ×_k T_k`, the point `ι_K(T)[b]` composed with the projection `J_K ⟶ J` is
`ι(T_k)[a]`. Since that canonical morphism is an isomorphism, this determines `ι_K`. The
Jacobian of `C_K` is given together with its equation to the structure literal
`⟨J_K, _, ι_K, _, _⟩`, so that its abelian variety is `J_K` definitionally.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. III, Theorem 1.6 and Remark 1.4.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Picard
  Stacks.RigidifiedPicard

universe u

namespace Faltings

section Transport

variable {k k' : Type u} [Field k] [Field k'] {C C' : Scheme.{u}}
  (f : C ⟶ Spec (.of k)) (f' : C' ⟶ Spec (.of k'))

private lemma hdim_of_curve [IsSmoothProjectiveCurve k f] :
    ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s =>
  (topologicalKrullDim_fiber_spec f s).trans_le
    (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)

/-- The fibrewise degree is compatible with pull-back along any cartesian square over the
bases. -/
public lemma degree_smallSchemePullbackClassHom_of_isPullback
    [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve k' f']
    (hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (hdim' : ∀ s, topologicalKrullDim ↥(f'.fiber s) ≤ 1)
    {T : Over (Spec (.of k))} {T' : Over (Spec (.of k'))}
    (e : bc f' T' ⟶ bc f T) (h : T'.left ⟶ T.left)
    (he : IsPullback e (bcProj f' T') (bcProj f T) h) (x : smallOfScheme (bc f T)) :
    degree f' hdim' T' (smallSchemePullbackClassHom e x) = degree f hdim T x ∘ h := by
  simp only [degree, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    smallEquiv_smallSchemePullbackClassHom]
  exact relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback he _ _ _

/-- Pull-back along a cartesian square over the bases, as a map of the groups `P⁰`. -/
private noncomputable def picZeroMap [IsSmoothProjectiveCurve k f]
    [IsSmoothProjectiveCurve k' f']
    {T : Over (Spec (.of k))} {T' : Over (Spec (.of k'))}
    (e : bc f' T' ⟶ bc f T) (h : T'.left ⟶ T.left)
    (he : IsPullback e (bcProj f' T') (bcProj f T) h) :
    (relativePicZeroFunctor k f).obj (op T) →+ (relativePicZeroFunctor k' f').obj (op T') :=
  QuotientAddGroup.map _ _
    (((smallSchemePullbackClassHom e).comp
        (degree f (hdim_of_curve f) T).ker.subtype).codRestrict
      (degree f' (hdim_of_curve f') T').ker fun x => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
          degree_smallSchemePullbackClassHom_of_isPullback f f' (hdim_of_curve f)
            (hdim_of_curve f') e h he,
          (AddMonoidHom.mem_ker.1 x.2)]
        rfl)
    (by
      rintro x ⟨y, hy⟩
      refine ⟨smallSchemePullbackClassHom h y, ?_⟩
      change _ = smallSchemePullbackClassHom e (x : _)
      rw [show (x : smallOfScheme (bc f T)) = _ from hy.symm, smallSchemePullbackClassHom_comp,
        smallSchemePullbackClassHom_comp, he.w])

private lemma picZeroMap_picZeroMap {k'' : Type u} [Field k''] {C'' : Scheme.{u}}
    (f'' : C'' ⟶ Spec (.of k'')) [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve k' f']
    [IsSmoothProjectiveCurve k'' f'']
    {T : Over (Spec (.of k))} {T' : Over (Spec (.of k'))} {T'' : Over (Spec (.of k''))}
    (e : bc f' T' ⟶ bc f T) (h : T'.left ⟶ T.left)
    (he : IsPullback e (bcProj f' T') (bcProj f T) h)
    (e' : bc f'' T'' ⟶ bc f' T') (h' : T''.left ⟶ T'.left)
    (he' : IsPullback e' (bcProj f'' T'') (bcProj f' T') h')
    (e'' : bc f'' T'' ⟶ bc f T) (h'' : T''.left ⟶ T.left)
    (he'' : IsPullback e'' (bcProj f'' T'') (bcProj f T) h'') (hcomp : e' ≫ e = e'')
    (y : (relativePicZeroFunctor k f).obj (op T)) :
    picZeroMap f' f'' e' h' he' (picZeroMap f f' e h he y) = picZeroMap f f'' e'' h'' he'' y := by
  induction y using QuotientAddGroup.induction_on with
  | H a =>
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    apply Subtype.ext
    simp [smallSchemePullbackClassHom_comp, hcomp]

private lemma picZeroMap_mk [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve k' f']
    {T : Over (Spec (.of k))} {T' : Over (Spec (.of k'))}
    (e : bc f' T' ⟶ bc f T) (h : T'.left ⟶ T.left)
    (he : IsPullback e (bcProj f' T') (bcProj f T) h)
    (a : (degree f (hdim_of_curve f) T).ker) (b : (degree f' (hdim_of_curve f') T').ker)
    (hab : (b : smallOfScheme (bc f' T')) = smallSchemePullbackClassHom e a) :
    picZeroMap f f' e h he (QuotientAddGroup.mk a) = QuotientAddGroup.mk b := by
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  congr 1
  exact Subtype.ext hab.symm

private lemma isPullback_id_bc (T : Over (Spec (.of k))) :
    IsPullback (𝟙 (bc f T)) (bcProj f T) (bcProj f T) (𝟙 T.left) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

private lemma picZeroMap_id [IsSmoothProjectiveCurve k f] {T : Over (Spec (.of k))}
    (y : (relativePicZeroFunctor k f).obj (op T)) :
    picZeroMap f f (𝟙 _) (𝟙 _) (isPullback_id_bc f T) y = y := by
  induction y using QuotientAddGroup.induction_on with
  | H a =>
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    apply Subtype.ext
    simp

/-- Pulling back along a square and then along a second one whose composite with the first is
the identity of `C ×_k T` gives back the original class. -/
private lemma picZeroMap_picZeroMap_of_comp_eq_id [IsSmoothProjectiveCurve k f]
    [IsSmoothProjectiveCurve k' f'] {T : Over (Spec (.of k))} {T' : Over (Spec (.of k'))}
    (e : bc f' T' ⟶ bc f T) (h : T'.left ⟶ T.left)
    (he : IsPullback e (bcProj f' T') (bcProj f T) h)
    (e' : bc f T ⟶ bc f' T') (h' : T.left ⟶ T'.left)
    (he' : IsPullback e' (bcProj f T) (bcProj f' T') h') (hcomp : e' ≫ e = 𝟙 _)
    (y : (relativePicZeroFunctor k f).obj (op T)) :
    picZeroMap f' f e' h' he' (picZeroMap f f' e h he y) = y :=
  (picZeroMap_picZeroMap f f' f e h he e' h' he' _ _ (isPullback_id_bc f T) hcomp y).trans
    (picZeroMap_id f y)

private lemma relativePicZeroFunctor_map_eq [IsSmoothProjectiveCurve k f]
    {T U : Over (Spec (.of k))} (g : T ⟶ U) (y : (relativePicZeroFunctor k f).obj (op U)) :
    (relativePicZeroFunctor k f).map g.op y =
      picZeroMap f f (bcMap f g) g.left (bcMap_isPullback_proj f g) y := by
  induction y using QuotientAddGroup.induction_on with
  | H a => rfl

end Transport

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k))

set_option hygiene false in
/-- The structure morphism `Spec K ⟶ Spec k` of the field extension. -/
local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The canonical isomorphism `C_K ×_K T ≅ C ×_k T` for a `K`-scheme `T`. -/
private noncomputable def baseChangeIso (T : Over (Spec (.of K))) :
    bc (pullback.snd f π) T ≅ bc f ((Over.map π).obj T) :=
  pullbackLeftPullbackSndIso f _ T.hom

@[reassoc]
private lemma baseChangeIso_hom_fst (T : Over (Spec (.of K))) :
    (baseChangeIso f T).hom ≫ pullback.fst f (T.hom ≫ π) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

@[reassoc]
private lemma baseChangeIso_hom_snd (T : Over (Spec (.of K))) :
    (baseChangeIso f T).hom ≫ pullback.snd f (T.hom ≫ π) = pullback.snd _ _ :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- Any morphism `C_K ×_K T ⟶ C ×_k T` built from the two projections is `baseChangeIso`. -/
private lemma pullback_lift_eq_baseChangeIso_hom (T : Over (Spec (.of K))) (w) :
    (pullback.lift (pullback.fst (pullback.snd f π) T.hom ≫ pullback.fst f π)
        (pullback.snd _ T.hom) w : bc (pullback.snd f π) T ⟶ bc f ((Over.map π).obj T)) =
      (baseChangeIso f T).hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; exact (baseChangeIso_hom_fst f T).symm
  · rw [pullback.lift_snd]; exact (baseChangeIso_hom_snd f T).symm

private lemma isPullback_baseChangeIso_hom (T : Over (Spec (.of K))) :
    IsPullback (baseChangeIso f T).hom (bcProj (pullback.snd f π) T)
      (bcProj f ((Over.map π).obj T)) (𝟙 T.left) :=
  IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact baseChangeIso_hom_snd f T⟩

private lemma isPullback_baseChangeIso_inv (T : Over (Spec (.of K))) :
    IsPullback (baseChangeIso f T).inv (bcProj f ((Over.map π).obj T))
      (bcProj (pullback.snd f π) T) (𝟙 T.left) :=
  @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _) ⟨by
    exact ((Iso.inv_comp_eq _).2 (baseChangeIso_hom_snd f T).symm).trans
      (Category.comp_id _).symm⟩

private lemma baseChangeIso_hom_bcMap {T U : Over (Spec (.of K))} (g : T ⟶ U) :
    (baseChangeIso f T).hom ≫ bcMap f ((Over.map π).map g) =
      bcMap (pullback.snd f π) g ≫ (baseChangeIso f U).hom := by
  apply pullback.hom_ext
  · simp [bcMap, baseChangeIso_hom_fst]
  · simp [bcMap, baseChangeIso_hom_snd, baseChangeIso_hom_snd_assoc]

variable [IsSmoothProjectiveCurve k f] [IsSmoothProjectiveCurve K (pullback.snd f π)]

/-- `P⁰_{C_K}(T) ≃ P⁰_C(T)`: pull-back along `C ×_k T ≅ C_K ×_K T`. -/
private noncomputable def picZeroBaseChangeEquiv (T : Over (Spec (.of K))) :
    (relativePicZeroFunctor K (pullback.snd f π)).obj (op T) ≃+
      (relativePicZeroFunctor k f).obj (op ((Over.map π).obj T)) where
  toFun := picZeroMap _ f (baseChangeIso f T).inv (𝟙 T.left) (isPullback_baseChangeIso_inv f T)
  invFun := picZeroMap f _ (baseChangeIso f T).hom (𝟙 T.left) (isPullback_baseChangeIso_hom f T)
  left_inv := picZeroMap_picZeroMap_of_comp_eq_id _ f _ _ (isPullback_baseChangeIso_inv f T) _ _
    (isPullback_baseChangeIso_hom f T) (Iso.hom_inv_id _)
  right_inv := picZeroMap_picZeroMap_of_comp_eq_id f _ _ _ (isPullback_baseChangeIso_hom f T) _ _
    (isPullback_baseChangeIso_inv f T) (Iso.inv_hom_id _)
  map_add' := map_add _

private lemma picZeroBaseChangeEquiv_apply (T : Over (Spec (.of K))) (y) :
    picZeroBaseChangeEquiv f T y =
      picZeroMap _ f (baseChangeIso f T).inv (𝟙 T.left) (isPullback_baseChangeIso_inv f T) y :=
  rfl

private lemma picZeroBaseChangeEquiv_symm_apply (T : Over (Spec (.of K))) (x) :
    (picZeroBaseChangeEquiv f T).symm x =
      picZeroMap f _ (baseChangeIso f T).hom (𝟙 T.left) (isPullback_baseChangeIso_hom f T) x :=
  rfl

private lemma picZeroBaseChangeEquiv_mk (T : Over (Spec (.of K)))
    (a : (degree f (hdim_of_curve f) ((Over.map π).obj T)).ker)
    (b : (degree _ (hdim_of_curve (pullback.snd f π)) T).ker)
    (hb : (b : smallOfScheme _) = smallSchemePullbackClassHom (baseChangeIso f T).hom a) :
    picZeroBaseChangeEquiv f T (QuotientAddGroup.mk b) = QuotientAddGroup.mk a :=
  ((AddEquiv.symm_apply_eq _).1 <| (picZeroBaseChangeEquiv_symm_apply f T _).trans
    (picZeroMap_mk f _ _ _ (isPullback_baseChangeIso_hom f T) a b hb)).symm

private lemma picZeroBaseChangeEquiv_map {T U : Over (Spec (.of K))} (g : T ⟶ U) (y) :
    picZeroBaseChangeEquiv f T ((relativePicZeroFunctor K (pullback.snd f π)).map g.op y) =
      (relativePicZeroFunctor k f).map ((Over.map π).map g).op
        (picZeroBaseChangeEquiv f U y) := by
  have he := (isPullback_baseChangeIso_inv f T).paste_horiz (bcMap_isPullback_proj _ g)
  rw [relativePicZeroFunctor_map_eq, relativePicZeroFunctor_map_eq,
    picZeroBaseChangeEquiv_apply, picZeroBaseChangeEquiv_apply,
    picZeroMap_picZeroMap _ _ _ _ _ _ _ _ _ _ _ he rfl,
    picZeroMap_picZeroMap _ _ _ _ _ _ _ _ _ _ _ he]
  rw [Iso.comp_inv_eq, Category.assoc, ← baseChangeIso_hom_bcMap, Iso.inv_hom_id_assoc]

end BaseChange

/-- Transposing along `Over.map π ⊣ Over.pullback π` and then projecting back to the original
object recovers the morphism. -/
private lemma mapPullbackAdj_homEquiv_left_fst {D : Type*} [Category D] [HasPullbacks D]
    {X Y : D} (p : X ⟶ Y) (T : Over X) (J : Over Y) (m : (Over.map p).obj T ⟶ J) :
    ((Over.mapPullbackAdj p).homEquiv T J m).left ≫ pullback.fst _ _ = m.left := by
  simp only [Adjunction.homEquiv_unit, Over.comp_left, Over.mapPullbackAdj_unit_app,
    Over.homMk_left, Over.pullback_map_left, Category.assoc]
  erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]

section Restriction

open scoped MonObj

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
  [IsSmoothProjectiveCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))]

/-- `ι_K(T)`: the composite `P⁰_{C_K}(T) ≃ P⁰_C(T) → J(T) ≃ J_K(T)`. -/
private noncomputable def baseChangeιApp (A : Jacobian k f) (T : Over (Spec (.of K)))
    (y : (relativePicZeroFunctor K
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj (op T)) :
    T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J :=
  (Over.mapPullbackAdj _).homEquiv T A.J
    (A.ι.app (op ((Over.map _).obj T)) (picZeroBaseChangeEquiv f T y))

/-- `ι_K`, as a morphism of set-valued functors on `K`-schemes. -/
private noncomputable def baseChangeι (A : Jacobian k f) :
    relativePicZeroFunctor K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⋙
        forget AddCommGrpCat ⟶
      yoneda.obj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J) where
  app T := TypeCat.ofHom (baseChangeιApp f A T.unop)
  naturality T U g := by
    ext y
    change baseChangeιApp f A _ ((relativePicZeroFunctor K _).map g.unop.op y) =
      g.unop ≫ baseChangeιApp f A _ y
    rw [baseChangeιApp, baseChangeιApp, picZeroBaseChangeEquiv_map,
      ← Adjunction.homEquiv_naturality_left]
    exact congrArg _ (NatTrans.naturality_apply A.ι _ _)

/-- `ι_K(T)` sends sums to products. -/
private lemma baseChangeιApp_add (A : Jacobian k f) (T : Over (Spec (.of K))) (x y) :
    baseChangeιApp f A T (x + y) = baseChangeιApp f A T x * baseChangeιApp f A T y := by
  simp only [baseChangeιApp, map_add, A.map_add, mapPullbackAdj_homEquiv_mul]

/-- `ι_K(T)` is bijective when `C_K(T) ≠ ∅`: a `K`-point of `C_K` gives a `k`-point of `C`. -/
private lemma baseChangeιApp_bijective (A : Jacobian k f) (T : Over (Spec (.of K)))
    (s : T ⟶ Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    Function.Bijective (baseChangeιApp f A T) := by
  have hJ := A.isIso_app ((Over.map _).obj T) ⟨Over.homMk (s.left ≫ pullback.fst _ _) (by
    simpa [pullback.condition] using Over.w s =≫ Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  rw [isIso_iff_bijective] at hJ
  exact ((Over.mapPullbackAdj _).homEquiv T A.J).bijective.comp
    (hJ.comp (picZeroBaseChangeEquiv f T).bijective)

/-- `ι_K(T)` followed by the projection `J_K ⟶ J` is `ι(T_k)`, on classes matched by the
canonical isomorphism `C_K ×_K T ≅ C ×_k T`. -/
private lemma baseChangeιApp_left_fst (A : Jacobian k f) (T : Over (Spec (.of K)))
    (a : (degree f (hdim_of_curve f)
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)).ker)
    (b : (degree _ (hdim_of_curve
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) T).ker)
    (hb : (b : smallOfScheme _) = smallSchemePullbackClassHom (baseChangeIso f T).hom a) :
    (baseChangeιApp f A T (QuotientAddGroup.mk b)).left ≫ pullback.fst _ _ =
      (A.ι.app (op _) (QuotientAddGroup.mk a)).left := by
  refine (mapPullbackAdj_homEquiv_left_fst _ _ _ _).trans ?_
  rw [picZeroBaseChangeEquiv_mk f T a b hb]

end Restriction

/-- Projective morphisms are stable under base change. -/
public lemma isProjectiveMorphism_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (pullback.snd f g) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have hP := isPullback_projectiveSpaceOverMap n g
  let i' : pullback f g ⟶ projectiveSpaceOver n S' :=
    hP.lift (pullback.fst f g ≫ i) (pullback.snd f g) (by
      rw [Category.assoc]
      change pullback.fst f g ≫ i ≫ projectiveSpaceOver n S ↘ S = _
      rw [hif]; exact pullback.condition)
  have hsq : IsPullback (pullback.fst f g) i' i (projectiveSpaceOverMap n g) := by
    refine IsPullback.of_bot ?_ (hP.lift_fst _ _ _).symm hP
    rw [hP.lift_snd]
    change IsPullback (pullback.fst f g) (pullback.snd f g) (i ≫ projectiveSpaceOver n S ↘ S) g
    rw [hif]; exact IsPullback.of_hasPullback f g
  exact ⟨n, i', MorphismProperty.of_isPullback hsq hi, hP.lift_snd _ _ _⟩

/-- The base change of a curve along a morphism of spectra of fields is a curve. -/
public lemma isSmoothProjectiveCurve_pullback_snd {k K : Type u} [Field k] [Field K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (g : Spec (.of K) ⟶ Spec (.of k)) : IsSmoothProjectiveCurve K (pullback.snd f g) :=
  have : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f g) inferInstance
  have : IsVariety K (pullback.snd f g) := ⟨⟩
  have : IsProjectiveVariety K (pullback.snd f g) :=
    ⟨isProjectiveMorphism_pullback_snd f g (IsProjectiveVariety.isProjective (k := k))⟩
  ⟨⟩

/-- **The Jacobian commutes with field extension.** Let `(J, ι)` be a Jacobian of the smooth
projective curve `f : C ⟶ Spec k`, and `K/k` a field extension with `π : Spec K ⟶ Spec k`.
Then `C_K = pullback.snd f π` is a smooth projective curve over `K`, and it has a Jacobian
`B = (J_K, ι_K)` with `J_K = (Over.pullback π).obj J`, the base-changed abelian variety with its
base-changed group law, and `ι_K : P⁰_{C_K} ⟶ J_K(-)` the restriction of `ι`: if a
fibrewise-degree-zero class `b` on `C_K ×_K T` is the pull-back of a class `a` on `C ×_k T`
along the canonical morphism `C_K ×_K T ⟶ C ×_k T`, then `ι_K(T)[b]` followed by the projection
`J_K ⟶ J` is `ι(T)[a]`. -/
@[faltings "lem_nt_jacobian_base_change"]
public theorem Jacobian.exists_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
    (A : Jacobian k f) :
    ∃ (_ : IsSmoothProjectiveCurve K
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (B : Jacobian K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (ι' : relativePicZeroFunctor K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⋙
          forget AddCommGrpCat ⟶
        yoneda.obj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J))
      (hadd : ∀ (T : (Over (Spec (.of K)))ᵒᵖ) (x y : (relativePicZeroFunctor K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj T),
        ι'.app T (x + y) =
          @HMul.hMul (T.unop ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
              A.J) _ _ (@instHMul _ (Hom.group).toMul) (ι'.app T x) (ι'.app T y))
      (hiso : ∀ T : Over (Spec (.of K)),
        Nonempty (T ⟶ Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) →
          IsIso (ι'.app (op T))),
      B = { J := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A.J
            isAbelianVariety := @isAbelianVariety_pullbackObj k K _ _ _ A.J _ A.isAbelianVariety
            ι := ι'
            map_add := hadd
            isIso_app := hiso } ∧
      ∀ (T : Over (Spec (.of K)))
        (x : (relativePicZeroFunctor k f).obj
          (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)))
        (y : (relativePicZeroFunctor K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj (op T)),
        (∃ a b, x = QuotientAddGroup.mk a ∧ y = QuotientAddGroup.mk b ∧
          (b : smallOfScheme
              (bc (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T)) =
            smallSchemePullbackClassHom
            (pullback.lift
              (pullback.fst
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T.hom ≫
                pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              (pullback.snd _ T.hom) (by
                simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
                  pullback.condition_assoc]) :
              bc (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) T ⟶
                bc f ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T))
            (a : smallOfScheme
              (bc f ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)))) →
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left := by
  have hC :=
    isSmoothProjectiveCurve_pullback_snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  refine ⟨hC, _, baseChangeι f A, fun T => baseChangeιApp_add f A T.unop, fun T ⟨s⟩ =>
    (isIso_iff_bijective _).2 (baseChangeιApp_bijective f A T s), rfl, ?_⟩
  rintro T x y ⟨a, b, rfl, rfl, hb⟩
  rw [pullback_lift_eq_baseChangeIso_hom] at hb
  exact baseChangeιApp_left_fst f A T a b hb

section Additivity

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option hygiene false in
/-- The structure morphism `Spec K ⟶ Spec k` of the field extension. -/
local notation "π" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- A `K`-morphism into `A_K` is determined by its composite with the projection `A_K ⟶ A`. -/
private lemma pullback_hom_ext_of_left_fst (A : Over (Spec (.of k))) {T : Over (Spec (.of K))}
    {u v : T ⟶ (Over.pullback π).obj A}
    (h : u.left ≫ pullback.fst A.hom π = v.left ≫ pullback.fst A.hom π) : u = v := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  have hu := Over.w u
  have hv := Over.w v
  simp only [Over.pullback_obj_hom] at hu hv
  rw [hu, hv]

variable {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f]
  [IsSmoothProjectiveCurve K (pullback.snd f π)]

/-- A restriction `ι_K` of `ι` is `y ↦ (ι(T_k)(y_k))_K`, with `y_k` the class of `y` on
`C ×_k T_k`. -/
private lemma baseChange_app_eq_homEquiv (A : Jacobian k f)
    (ι' : relativePicZeroFunctor K (pullback.snd f π) ⋙ forget AddCommGrpCat ⟶
      yoneda.obj ((Over.pullback π).obj A.J))
    (hι'c : ∀ (T : Over (Spec (.of K)))
        (x : (relativePicZeroFunctor k f).obj (op ((Over.map π).obj T)))
        (y : (relativePicZeroFunctor K (pullback.snd f π)).obj (op T)),
        (∃ a b, x = QuotientAddGroup.mk a ∧ y = QuotientAddGroup.mk b ∧
          (b : smallOfScheme (bc (pullback.snd f π) T)) =
            smallSchemePullbackClassHom
            (pullback.lift
              (pullback.fst (pullback.snd f π) T.hom ≫ pullback.fst f π)
              (pullback.snd _ T.hom) (by
                simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
                  pullback.condition_assoc]) :
              bc (pullback.snd f π) T ⟶ bc f ((Over.map π).obj T))
            (a : smallOfScheme (bc f ((Over.map π).obj T)))) →
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left)
    (T : Over (Spec (.of K))) (z : (relativePicZeroFunctor K (pullback.snd f π)).obj (op T)) :
    ι'.app (op T) z = (Over.mapPullbackAdj π).homEquiv T A.J
      (A.ι.app (op ((Over.map π).obj T)) (picZeroBaseChangeEquiv f T z)) := by
  apply pullback_hom_ext_of_left_fst
  rw [mapPullbackAdj_homEquiv_left_fst]
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (picZeroBaseChangeEquiv f T z)
  let b : (degree _ (hdim_of_curve (pullback.snd f π)) T).ker :=
    ⟨smallSchemePullbackClassHom (baseChangeIso f T).hom a, by
      rw [AddMonoidHom.mem_ker, degree_smallSchemePullbackClassHom_of_isPullback f _
        (hdim_of_curve f) (hdim_of_curve _) (baseChangeIso f T).hom (𝟙 T.left)
        (isPullback_baseChangeIso_hom f T),
        (AddMonoidHom.mem_ker.1 a.2)]
      rfl⟩
  have hz : z = QuotientAddGroup.mk b := by
    rw [← (picZeroBaseChangeEquiv f T).symm_apply_apply z, ← ha]
    exact (picZeroBaseChangeEquiv_symm_apply f _ _).trans
      (picZeroMap_mk f _ _ _ (isPullback_baseChangeIso_hom f T) a b rfl)
  refine hι'c T _ z ⟨a, b, ha.symm, hz, ?_⟩
  rw [pullback_lift_eq_baseChangeIso_hom]

/-- **The restriction `ι_K` of `ι` is bijective where `C_K` has points.** If
`ι' : P⁰_{C_K} ⟶ J_K(-)` restricts the morphism `ι` of a Jacobian `(J, ι)` of `C`, in the sense of
`Faltings.Jacobian.exists_baseChange`, then `ι'(T)` is bijective for every `K`-scheme `T` with
`C_K(T) ≠ ∅`: a `T`-point of `C_K` gives a `T_k`-point of `C`. -/
public theorem Jacobian.isIso_app_of_baseChange (A : Jacobian k f)
    (ι' : relativePicZeroFunctor K (pullback.snd f π) ⋙ forget AddCommGrpCat ⟶
      yoneda.obj ((Over.pullback π).obj A.J))
    (hι'c : ∀ (T : Over (Spec (.of K)))
        (x : (relativePicZeroFunctor k f).obj (op ((Over.map π).obj T)))
        (y : (relativePicZeroFunctor K (pullback.snd f π)).obj (op T)),
        (∃ a b, x = QuotientAddGroup.mk a ∧ y = QuotientAddGroup.mk b ∧
          (b : smallOfScheme (bc (pullback.snd f π) T)) =
            smallSchemePullbackClassHom
            (pullback.lift
              (pullback.fst (pullback.snd f π) T.hom ≫ pullback.fst f π)
              (pullback.snd _ T.hom) (by
                simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
                  pullback.condition_assoc]) :
              bc (pullback.snd f π) T ⟶ bc f ((Over.map π).obj T))
            (a : smallOfScheme (bc f ((Over.map π).obj T)))) →
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left)
    (T : Over (Spec (.of K))) (hT : Nonempty (T ⟶ Over.mk (pullback.snd f π))) :
    IsIso (ι'.app (op T)) := by
  obtain ⟨s⟩ := hT
  have hJ := A.isIso_app ((Over.map π).obj T) ⟨Over.homMk (s.left ≫ pullback.fst _ _) (by
    simpa [pullback.condition] using Over.w s =≫ π)⟩
  rw [isIso_iff_bijective] at hJ
  rw [isIso_iff_bijective]
  have h : (ι'.app (op T) : _ → _) = fun z => (Over.mapPullbackAdj π).homEquiv T A.J
      (A.ι.app (op ((Over.map π).obj T)) (picZeroBaseChangeEquiv f T z)) :=
    funext (baseChange_app_eq_homEquiv f A ι' hι'c T)
  rw [h]
  exact ((Over.mapPullbackAdj π).homEquiv T A.J).bijective.comp
    (hJ.comp (picZeroBaseChangeEquiv f T).bijective)

/-- **The restriction `ι_K` of `ι` is additive.** If `ι' : P⁰_{C_K} ⟶ J_K(-)` restricts the
morphism `ι` of a Jacobian `(J, ι)` of `C`, in the sense of `Faltings.Jacobian.exists_baseChange`,
then each `ι'(T)` sends sums in `P⁰_{C_K}(T)` to products in `J_K(T)`. -/
public theorem Jacobian.map_add_of_baseChange (A : Jacobian k f)
    (ι' : relativePicZeroFunctor K (pullback.snd f π) ⋙ forget AddCommGrpCat ⟶
      yoneda.obj ((Over.pullback π).obj A.J))
    (hι'c : ∀ (T : Over (Spec (.of K)))
        (x : (relativePicZeroFunctor k f).obj (op ((Over.map π).obj T)))
        (y : (relativePicZeroFunctor K (pullback.snd f π)).obj (op T)),
        (∃ a b, x = QuotientAddGroup.mk a ∧ y = QuotientAddGroup.mk b ∧
          (b : smallOfScheme (bc (pullback.snd f π) T)) =
            smallSchemePullbackClassHom
            (pullback.lift
              (pullback.fst (pullback.snd f π) T.hom ≫ pullback.fst f π)
              (pullback.snd _ T.hom) (by
                simp only [Over.map_obj_hom, Category.assoc, pullback.condition,
                  pullback.condition_assoc]) :
              bc (pullback.snd f π) T ⟶ bc f ((Over.map π).obj T))
            (a : smallOfScheme (bc f ((Over.map π).obj T)))) →
        (ι'.app (op T) y).left ≫ pullback.fst _ _ = (A.ι.app (op _) x).left)
    (T : (Over (Spec (.of K)))ᵒᵖ) (x y : (relativePicZeroFunctor K (pullback.snd f π)).obj T) :
    ι'.app T (x + y) =
      @HMul.hMul (T.unop ⟶ (Over.pullback π).obj A.J) (T.unop ⟶ (Over.pullback π).obj A.J)
        (T.unop ⟶ (Over.pullback π).obj A.J) _ (ι'.app T x) (ι'.app T y) := by
  have key := baseChange_app_eq_homEquiv f A ι' hι'c T.unop
  rw [key, key, key, (picZeroBaseChangeEquiv f T.unop).map_add,
    A.map_add (op ((Over.map π).obj T.unop)), mapPullbackAdj_homEquiv_mul]

end Additivity

end Faltings
