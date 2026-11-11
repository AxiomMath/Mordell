module

public import Mordell.AlgebraicGeometry.ProjectiveSpace.SegreVeronese.Basic
public import Mordell.CurveProduct.VojtaClass
public import Mordell.Height.Machine.EmbeddingGroup
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.StandardChart
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesGenericPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.BasicUnconditional

/-!
# Tensor powers of an invertible module and monomial sections

Words of exponent vectors, the tensor power `A^{⊗(k+1)}` of a module, the monomial section
`x_{w₀} ⋯ x_{w_k}` along a word, its restriction to `{x_i ≠ 0}` and invertibility of tensor powers.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LinearAlgebra.Projectivization
open Stacks.SectionsToProjectiveSpace Stacks.SectionsToProjectiveSpace.C1573

universe u

namespace Faltings.CurveWithDegreeOneDivisor

section Helpers

variable {n : ℕ}

/-! ### Monomials as words in the variables -/

section Words

/-- The list of variables, with multiplicity, of an exponent vector of total degree `δ` has length
`δ`. -/
public theorem length_toList_toMultiset {δ : ℕ} (a : {a : Fin (n + 1) →₀ ℕ // a.degree = δ}) :
    (Finsupp.toMultiset a.1).toList.length = δ := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  exact a.2

/-- A word `w : Fin (k + 1) → Fin (n + 1)` in which each variable `l` occurs `a l` times, for an
exponent vector `a` of total degree `k + 1`. -/
@[expose] public noncomputable def word {δ k : ℕ} (a : {a : Fin (n + 1) →₀ ℕ // a.degree = δ})
    (hk : δ = k + 1) : Fin (k + 1) → Fin (n + 1) :=
  fun j => (Finsupp.toMultiset a.1).toList.get ⟨j, by rw [length_toList_toMultiset, hk]; exact j.2⟩

/-- The product of `t` over the variables of `a`, with multiplicity, is the monomial
`∏ l, t l ^ a l`. -/
public theorem prod_map_toMultiset {M : Type*} [CommMonoid M] (t : Fin (n + 1) → M)
    (a : Fin (n + 1) →₀ ℕ) :
    ((Finsupp.toMultiset a).map t).prod = a.prod fun l e => t l ^ e := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Multiset.map_add, Multiset.prod_add, hf, hg,
      Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add])]
  | single l e =>
    rw [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul,
      Finsupp.prod_single_index (by simp)]
    simp

/-- The product along the word of a monomial is the monomial. -/
public theorem prod_word {M : Type*} [CommMonoid M] (t : Fin (n + 1) → M) {δ k : ℕ}
    (a : {a : Fin (n + 1) →₀ ℕ // a.degree = δ}) (hk : δ = k + 1) :
    ∏ j, t (word a hk j) = a.1.prod fun l e => t l ^ e := by
  rw [← prod_map_toMultiset, ← Multiset.coe_toList (Finsupp.toMultiset a.1), Multiset.map_coe,
    Multiset.prod_coe, ← Fin.prod_univ_fun_getElem]
  exact Fintype.prod_equiv (finCongr (by rw [length_toList_toMultiset, hk])) _ _ (fun j => rfl)

/-- The word of a pure power `x_i ^ (k + 1)` is constant. -/
public theorem word_single {δ k : ℕ} (i : Fin (n + 1)) (h : (Finsupp.single i δ).degree = δ)
    (hk : δ = k + 1) (j : Fin (k + 1)) : word ⟨Finsupp.single i δ, h⟩ hk j = i := by
  have hmem : word ⟨_, h⟩ hk j ∈ Finsupp.toMultiset (Finsupp.single i δ) :=
    Multiset.mem_toList.1 (List.get_mem _ _)
  have := Finsupp.support_single_subset ((Finsupp.mem_toMultiset _ _).1 hmem)
  simpa using this

end Words

/-! ### Tensor powers of an invertible module and their monomial sections -/

section Powers

open Stacks.ProjectiveFromSections Stacks.SectionProduct Opposite

variable {Y : Scheme.{u}}

/-- The `(k + 1)`-fold tensor power `A ⊗ (A ⊗ (⋯ ⊗ A))`. -/
@[expose] public noncomputable def powMod (A : Y.Modules) : ℕ → Y.Modules
  | 0 => A
  | k + 1 => Scheme.Modules.tensorObj A (powMod A k)

/-- Every tensor power `powMod A k` of an invertible module `A` is invertible. -/
public theorem isInvertibleModule_powMod (A : Y.Modules) [Stacks.Ample.IsInvertibleModule Y A] :
    ∀ k, Stacks.Ample.IsInvertibleModule Y (powMod A k)
  | 0 => ‹_›
  | k + 1 => haveI := isInvertibleModule_powMod A k
      Stacks.SectionProduct.isInvertibleModule_tensorObj A (powMod A k)

attribute [local instance] isInvertibleModule_powMod

/-- The product of two sections over `U`, a section of the tensor product. -/
@[expose] public noncomputable abbrev tsec {M N : Y.Modules} (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    Γ(Scheme.Modules.tensorObj M N, U) :=
  Stacks.SheafOfModules.tensorSectionsAt Y.sheaf.obj Y.ringCatSheaf.property (op U) M N s t

/-- Restricting a product of two global sections to `W` is the product of their restrictions. -/
public theorem resT_tsec {M N : Y.Modules} (W : Y.Opens) (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    resT (L := Scheme.Modules.tensorObj M N) W (tsec ⊤ s t) = tsec W (resT W s) (resT W t) :=
  map_tensorSectionsAt M N (homOfLE le_top) s t

/-- The product of sections is bilinear: `(a • s) ⊗ (b • t) = (a * b) • (s ⊗ t)`. -/
public theorem tsec_smul_smul {M N : Y.Modules} {U : Y.Opens} (a b : Γ(Y, U)) (s : Γ(M, U))
    (t : Γ(N, U)) : tsec U (a • s) (b • t) = (a * b) • tsec U s t :=
  tensorSectionsAt_smul_smul M N a b s t

variable {A : Y.Modules} (x : Fin (n + 1) → Γ(A, ⊤))

/-- The section `x_{w 0} ⊗ (x_{w 1} ⊗ (⋯ ⊗ x_{w k}))` of the `(k + 1)`-fold tensor power. -/
@[expose] public noncomputable def powSec : (k : ℕ) → (Fin (k + 1) → Fin (n + 1)) → Γ(powMod A k, ⊤)
  | 0, w => x (w 0)
  | k + 1, w => tsec (M := A) (N := powMod A k) ⊤ (x (w 0)) (powSec k (Fin.tail w))

variable [Stacks.Ample.IsInvertibleModule Y A]

/-- The nonvanishing open of the monomial section `powSec x k w` is contained in that of its first
factor `x (w 0)`. -/
public theorem nvOpen_powSec_le : ∀ (k : ℕ) (w : Fin (k + 1) → Fin (n + 1)),
    nvOpen (powMod A k) (powSec x k w) ≤ nvOpen A (x (w 0))
  | 0, _ => le_rfl
  | k + 1, _ => (nvOpen_tensorSectionsAt A (powMod A k) _ _).le.trans inf_le_left

/-- The nonvanishing open of `x i` is contained in that of the pure power
`x_i ⊗ (x_i ⊗ (⋯ ⊗ x_i))`. -/
public theorem le_nvOpen_powSec_const (i : Fin (n + 1)) : ∀ k : ℕ,
    nvOpen A (x i) ≤ nvOpen (powMod A k) (powSec x k fun _ => i)
  | 0 => le_rfl
  | k + 1 => (le_inf le_rfl (le_nvOpen_powSec_const i k)).trans
      (nvOpen_tensorSectionsAt A (powMod A k) _ _).ge

/-- **Restricting a monomial section to an open where `x_i` does not vanish**:
`x_{w 0} ⋯ x_{w k} = (∏ⱼ x_{w j} / x_i) · x_i ^ (k + 1)`. -/
public theorem resT_powSec {i : Fin (n + 1)} {W : Y.Opens} (hW : W ≤ nvOpen A (x i)) :
    ∀ (k : ℕ) (w : Fin (k + 1) → Fin (n + 1)),
      resT W (powSec x k w) =
        (∏ j, div (x i) hW (resT W (x (w j)))) • resT W (powSec x k fun _ => i)
  | 0, w => by
      simp only [powSec, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      exact (div_smul (x i) hW _).symm
  | k + 1, w => by
      change resT (L := Scheme.Modules.tensorObj A (powMod A k)) W
          (tsec ⊤ (x (w 0)) (powSec x k (Fin.tail w))) =
        (∏ j, div (x i) hW (resT W (x (w j)))) •
          resT (L := Scheme.Modules.tensorObj A (powMod A k)) W
            (tsec ⊤ (x i) (powSec x k (Fin.tail fun _ => i)))
      rw [Fin.prod_univ_succ (fun j => div (x i) hW (resT W (x (w j)))), resT_tsec, resT_tsec,
        resT_powSec hW k (Fin.tail w)]
      conv_lhs => rw [← div_smul (x i) hW (resT W (x (w 0)))]
      rw [tsec_smul_smul]
      rfl

end Powers

end Helpers

end Faltings.CurveWithDegreeOneDivisor
