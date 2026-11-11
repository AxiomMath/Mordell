module
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The rigidity lemma

Let `G` be a proper group scheme over an algebraically closed field `K` such that `G ×_K G` is
integral, and let `F : G × G ⟶ G` be a morphism of `K`-schemes with `F(e, y) = e` and
`F(x, e) = e`. Then `F` is constant with value `e`.

## Main results

* `Faltings.rigidity`: the rigidity lemma ([MilAV] Ch. I, Theorem 1.1, for `V = W = G`).

## Implementation notes

The proof follows that of
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, with the
commutator replaced by `F`: the morphism `(x, y) ↦ (x, F(x, y))` is proper and contracts
the fibre over `e` to a point, so by Zariski's main theorem it has finite fibres over a
neighbourhood of `e`; each fibre `{x} × G` is irreducible and proper, so `F(x, -)` is constant,
and its value is `F(x, e) = e`.

## References

* [MilAV] J. S. Milne, *Abelian Varieties*, Ch. I, Theorem 1.1.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

universe u

namespace Faltings

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The rigidity lemma** ([MilAV] Ch. I, Theorem 1.1, for `V = W = G`). Let `G` be a proper
group scheme over an algebraically closed field `K` with `G ×_K G` integral. A morphism
`F : G × G ⟶ G` that is trivial on `e × G` and on `G × e` is the constant morphism at `e`. -/
public theorem rigidity {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [IsProper G.hom]
    [IsIntegral (G ⊗ G).left] [GrpObj G]
    (F : G ⊗ G ⟶ G) (h₁ : η[G] ▷ G ≫ F = toUnit _ ≫ η[G])
    (h₂ : G ◁ η[G] ≫ F = toUnit _ ≫ η[G]) :
    F = toUnit _ ≫ η[G] := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : Nonempty (Spec (.of K)) := ⟨point⟩
  have : Nonempty (𝟙_ (Over (Spec (.of K)))).left := ⟨point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsProper (F.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (F.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated G.hom := inferInstance
  have : IsReduced (G ⊗ G).left := inferInstance
  have : IsClosedImmersion ((lift η[G] η[G]).left ≫ (fst G G).left) := by
    simpa only [Over.tensorUnit_left, Over.tensorObj_left, Over.lift_left, Over.fst_left,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app] using
      inferInstanceAs (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[G]).left := .of_comp _ (g := (fst G G).left)
  let φ : G ⊗ G ⟶ G ⊗ G := lift (fst _ _) F
  have : IsProper (φ.left ≫ (fst G G).left) := by
    simpa only [Over.tensorObj_left, Over.lift_left, Over.fst_left, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, Over.tensorUnit_left, φ]
  have : IsProper φ.left := .of_comp _ (fst G G).left
  ext1
  have H : φ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆ {(lift η[G] η[G]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[G]).left.isClosedMap _ hpoint).preimage φ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa only [Over.tensorObj_left, Category.assoc])
        (by simp only [Over.w, Over.tensorUnit_hom])
        (by simpa only [Over.tensorObj_left, Scheme.Hom.comp_base, TopCat.hom_comp,
          ContinuousMap.comp_apply])
    have H₁ : c = fc.left ≫ (η[G] ▷ G).left := by
      dsimp
      ext
      · simp only [this, Over.lift_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.id_left,
          Over.comp_left, Over.tensorObj_left, Over.homMk_left, Over.snd_left, Category.assoc,
          Over.whiskerRight_left_fst, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left,
          PullbackCone.mk_π_app, Category.id_comp, S, fc]
      · simp only [Over.lift_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.id_left,
          Over.comp_left, Over.tensorObj_left, Over.homMk_left, Over.snd_left, Category.assoc,
          Over.whiskerRight_left_snd, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          S, fc]
    have H₂ : fc ≫ η ▷ G ≫ φ = lift η η := by
      ext1
      · simp only [comp_lift, whiskerRight_fst, lift_fst_assoc, Category.id_comp,
          lift_whiskerRight_assoc, lift_fst, S, fc, φ]
      · simp only [φ, Category.assoc, lift_snd]
        rw [h₁, ← Category.assoc, toUnit_unique (fc ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact hc₂ <| by simp only [Over.tensorObj_left, Over.tensorUnit_left, Over.lift_left, H₁,
      Over.tensorUnit_hom, ← Over.comp_left, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      Category.assoc, H₂,
      Set.mem_singleton_iff]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    φ.left (fst G G).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, φ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have hLQF := ((IsFinite.iff_isProper_and_locallyQuasiFinite _).1 H).2
  have H (x : U) : ((pullback.fst G.hom G.hom) ⁻¹' {x.1} ∩ Set.range ⇑φ.left).Finite := by
    refine ((((φ.left.imageι ≫ (fst G G).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ φ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by
      ext
      simp only [Set.mem_preimage, Scheme.Opens.ι_apply, Set.mem_singleton_iff, SetLike.coe_eq_coe]
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G G).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact φ.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq G.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by
      simpa only [Over.tensorObj_left, Over.fst_left, Set.image_singleton] using
        (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by
      simp only [Over.tensorUnit_left, Over.tensorObj_left, Over.fst_left, pointOfClosedPoint_comp,
        Over.tensorUnit_hom])
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    have hφe : (fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G]) ≫ φ = fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G] := by
      ext1
      · simp only [φ, Category.assoc, lift_fst]
      · simp only [φ, Category.assoc, lift_snd]
        rw [h₂, whiskerLeft_snd, toUnit_unique (toUnit (G ⊗ 𝟙_ _)) (snd G (𝟙_ _))]
    have : φ.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ φ.left.continuous
        φ.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp only [Over.tensorObj_left, Over.fst_left, Set.mem_preimage, Set.mem_singleton_iff,
            Over.lift_left, Set.preimage_inter, Set.preimage_range, Set.inter_univ,
            ← Scheme.Hom.comp_apply, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
            imp_self, φ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        have hr1 : Set.range (toUnit G ≫ x).left = {(fst G G).left y} := by
          ext p
          constructor
          · rintro ⟨q, rfl⟩
            rw [Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
            exact pointOfClosedPoint_apply G.hom _ hx _
          · intro hp
            refine ⟨η[G].left point, ?_⟩
            rw [hp, Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
            exact pointOfClosedPoint_apply G.hom _ hx _
        have hr2 : Set.range (Over.Hom.left (𝟙 G)) = Set.univ :=
          Set.eq_univ_of_forall fun p => ⟨p, by rw [Over.id_left]; rfl⟩
        rw [Set.image_univ]
        refine Eq.trans ?_ (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).symm
        rw [hr1, hr2, Set.preimage_univ, Set.inter_univ, Over.fst_left]
        rfl
      · exact ⟨y, subset_closure (by simp only [Over.tensorObj_left, Over.fst_left,
          Set.mem_preimage, Set.mem_singleton_iff]), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp only [Over.tensorObj_left, Over.fst_left, Over.comp_left, Over.tensorUnit_left,
            Over.tensorUnit_hom, Set.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc,
            Over.whiskerLeft_left_fst, Over.rightUnitor_inv_left_fst, Category.comp_id,
            Set.mem_singleton_iff, xe]
        · change φ.left ((fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G]).left y) =
            (fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G]).left y
          rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφe]
    have h3 := congrArg (snd G G).left this
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd] at h3
    rw [h3]
    have e3 : (fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G]) ≫ snd G G = toUnit _ ≫ η[G] := by
      rw [Category.assoc, Category.assoc, whiskerLeft_snd, ← Category.assoc, ← Category.assoc,
        toUnit_unique ((fst G G ≫ (ρ_ G).inv) ≫ snd G (𝟙_ _)) (toUnit _)]
    change (snd G G).left ((fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G]).left y) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e3]
  · simp only [Over.tensorObj_left, Over.w, Over.tensorObj_hom, Over.comp_left,
      Over.tensorUnit_left,
      Over.toUnit_left, Category.assoc, Over.tensorUnit_hom, Category.comp_id]

end Faltings
