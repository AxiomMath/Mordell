module
public import Mordell.Analysis.MahlerMeasure.Basic

/-!
# Multiplicativity of the Mahler measure in several variables

For nonzero polynomials `f, g ∈ ℂ[t_i : i ∈ σ]` in finitely many variables, the Mahler measure
is multiplicative: `M(fg) = M(f) M(g)`. This follows from `log |fg| = log |f| + log |g|` and the
integrability of `log |f(e^{2πiθ})|` on the unit cube.

## Main results

* `Faltings.MvPolynomial.mahlerMeasure_mul`: `M(f * g) = M(f) * M(g)` for `f, g ≠ 0`.
* `Faltings.MvPolynomial.mahlerMeasure_prod`: `M(∏_j f_j) = ∏_j M(f_j)` for nonzero `f_j`.

## Implementation notes

The variables are indexed by an arbitrary finite type `σ` rather than by `{1, …, n}`.

The source deduces from the integrability of `log |f|` that `f` vanishes only on a null subset
of the torus. Since `Real.log 0 = 0`, integrability does not give this here; it is
`Faltings.ae_eval_exp_ne_zero_mvPolynomial`, proved by slicing along one variable.

## References

* [Z. Gao, *Heights*][gao2022], §1.3.
* [E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*][bombieri2006], 1.6.
-/

namespace Faltings

namespace MvPolynomial

open Real MeasureTheory

/-- The Mahler measure of polynomials in several variables over `ℂ` is multiplicative on nonzero
polynomials: `M(f * g) = M(f) * M(g)`. -/
@[faltings "lem_ht_mahler_several_variables"]
public theorem mahlerMeasure_mul {σ : Type*} [Fintype σ] {f g : _root_.MvPolynomial σ ℂ}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    mahlerMeasure (f * g) = mahlerMeasure f * mahlerMeasure g := by
  rw [mahlerMeasure_of_ne_zero (mul_ne_zero hf hg), mahlerMeasure_of_ne_zero hf,
    mahlerMeasure_of_ne_zero hg, ← Real.exp_add, Set.pi_univ_Icc]
  congr 1
  rw [show (Set.Icc (fun _ : σ ↦ (0 : ℝ)) fun _ ↦ 1) = Set.Icc 0 1 from rfl,
    ← integral_add (integrableOn_log_norm_eval_exp_mvPolynomial hf)
      (integrableOn_log_norm_eval_exp_mvPolynomial hg)]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_eval_exp_ne_zero_mvPolynomial hf, ae_eval_exp_ne_zero_mvPolynomial hg]
    with θ h1 h2
  simp only [map_mul, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)

/-- The Mahler measure of `1` is `1`. -/
public theorem mahlerMeasure_one {σ : Type*} [Fintype σ] :
    mahlerMeasure (1 : _root_.MvPolynomial σ ℂ) = 1 := by
  rw [mahlerMeasure_of_ne_zero one_ne_zero]
  simp

/-- The Mahler measure is multiplicative on finite products of nonzero polynomials. -/
public theorem mahlerMeasure_prod {σ ι : Type*} [Fintype σ] (s : Finset ι)
    (f : ι → _root_.MvPolynomial σ ℂ) (hf : ∀ j ∈ s, f j ≠ 0) :
    mahlerMeasure (∏ j ∈ s, f j) = ∏ j ∈ s, mahlerMeasure (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mahlerMeasure_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mahlerMeasure_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end MvPolynomial

end Faltings
