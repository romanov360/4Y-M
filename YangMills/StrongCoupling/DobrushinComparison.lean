import Mathlib

/-!
# The arithmetic core of the W₁ Dobrushin comparison

Lemma `comparison` of `strong-coupling/forest/main.tex` has two halves.

1. **Measure theory.** A minimising coupling of two measures invariant under the single-site
   updates outside a set `S` satisfies `ρ e ≤ ∑ e', C e e' * ρ e'` for every `e ∉ S`, where
   `ρ e` is the expected link distance. This needs Kantorovich couplings and is not formalised
   here (item G1 of `strong-coupling/forest/A4_LEAN.md`).
2. **Arithmetic.** From those inequalities, a weighted Dobrushin condition gives decay. This file
   proves that half for a finite index set, in two forms:

* `comparison_weighted` : the column-weighted form used in the paper,
  `∑_{e ∉ S} w e ρ e ≤ θ D / (1 - θ) · ∑_{z ∈ S} w z`,
  assuming `∑_e w e C e e' ≤ θ w e'` for every `e'`, and `ρ ≤ D` on `S`.
  With `S = ∅` it gives `ρ = 0` off `S`, i.e. uniqueness (`comparison_empty`).
* `decay_rowweighted` : the row-weighted (Bassalygo–Dobrushin) form,
  `ρ i ≤ B / (1 - α) · exp (-m d i k)`, when `ρ ≤ C ρ + b`, `b i ≤ B exp (-m d i k)`,
  and the weighted row sums `∑_j C i j exp (m d i j)` are at most `α < 1`.
  `sup_bound` is the case `m = 0`.

The paper allows infinitely many sites with summable weights. The finite case is the one
that finite-volume Gibbs measures need, and the infinite case follows from it by a limit,
which is not done here.
-/

open Finset Real

namespace YangMills.StrongCoupling.Comparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Column-weighted comparison.** The arithmetic of Lemma `comparison`. -/
theorem comparison_weighted (S : Finset ι) (C : ι → ι → ℝ) (w ρ : ι → ℝ)
    (θ D : ℝ) (hθ : θ < 1) (hθ0 : 0 ≤ θ)
    (hC : ∀ e e', 0 ≤ C e e') (hw : ∀ e, 0 ≤ w e) (hρ : ∀ e, 0 ≤ ρ e)
    (hρS : ∀ z ∈ S, ρ z ≤ D)
    (hmin : ∀ e ∉ S, ρ e ≤ ∑ e', C e e' * ρ e')
    (hcol : ∀ e', ∑ e, w e * C e e' ≤ θ * w e') :
    ∑ e ∈ Sᶜ, w e * ρ e ≤ θ * D / (1 - θ) * ∑ z ∈ S, w z := by
  set X := ∑ e ∈ Sᶜ, w e * ρ e
  set Y := ∑ z ∈ S, w z * ρ z
  -- Step 1: X ≤ θ (X + Y).
  have h1 : X ≤ ∑ e ∈ Sᶜ, w e * ∑ e', C e e' * ρ e' := by
    apply sum_le_sum
    intro e he
    exact mul_le_mul_of_nonneg_left (hmin e (by simpa using he)) (hw e)
  have h2 : ∑ e ∈ Sᶜ, w e * ∑ e', C e e' * ρ e' ≤ ∑ e, w e * ∑ e', C e e' * ρ e' := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro e _ _
    exact mul_nonneg (hw e) (sum_nonneg fun e' _ => mul_nonneg (hC e e') (hρ e'))
  have h3 : ∑ e, w e * ∑ e', C e e' * ρ e' = ∑ e', (∑ e, w e * C e e') * ρ e' := by
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have h4 : ∑ e', (∑ e, w e * C e e') * ρ e' ≤ ∑ e', θ * (w e' * ρ e') := by
    apply sum_le_sum
    intro e' _
    calc (∑ e, w e * C e e') * ρ e' ≤ (θ * w e') * ρ e' :=
          mul_le_mul_of_nonneg_right (hcol e') (hρ e')
      _ = θ * (w e' * ρ e') := by ring
  have h5 : ∑ e', θ * (w e' * ρ e') = θ * (X + Y) := by
    rw [← mul_sum, ← sum_compl_add_sum S]
  have hX : X ≤ θ * (X + Y) := by linarith
  -- Step 2: Y ≤ D ∑ w.
  have hY : Y ≤ D * ∑ z ∈ S, w z := by
    rw [mul_sum]
    apply sum_le_sum
    intro z hz
    calc w z * ρ z ≤ w z * D := mul_le_mul_of_nonneg_left (hρS z hz) (hw z)
      _ = D * w z := by ring
  -- Step 3: solve.
  have hpos : 0 < 1 - θ := by linarith
  have hX' : X * (1 - θ) ≤ θ * Y := by linarith
  have hXle : X ≤ θ * Y / (1 - θ) := by rw [le_div_iff₀ hpos]; linarith
  calc X ≤ θ * Y / (1 - θ) := hXle
    _ ≤ θ * (D * ∑ z ∈ S, w z) / (1 - θ) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left hY hθ0
    _ = θ * D / (1 - θ) * ∑ z ∈ S, w z := by ring

/-- With `S = ∅` and positive weights, the distances vanish: uniqueness. -/
theorem comparison_empty (C : ι → ι → ℝ) (w ρ : ι → ℝ) (θ : ℝ) (hθ : θ < 1) (hθ0 : 0 ≤ θ)
    (hC : ∀ e e', 0 ≤ C e e') (hw : ∀ e, 0 < w e) (hρ : ∀ e, 0 ≤ ρ e)
    (hmin : ∀ e, ρ e ≤ ∑ e', C e e' * ρ e')
    (hcol : ∀ e', ∑ e, w e * C e e' ≤ θ * w e') :
    ∀ e, ρ e = 0 := by
  have h := comparison_weighted (∅ : Finset ι) C w ρ θ 0 hθ hθ0 hC (fun e => (hw e).le) hρ
    (by simp) (fun e _ => hmin e) hcol
  simp only [compl_empty, sum_empty, mul_zero] at h
  have hz := (sum_eq_zero_iff_of_nonneg (fun e _ => mul_nonneg (hw e).le (hρ e))).mp
    (le_antisymm h (sum_nonneg fun e _ => mul_nonneg (hw e).le (hρ e)))
  intro e
  have := hz e (mem_univ e)
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (hw e).ne'
  · exact h0

omit [DecidableEq ι] in
/-- **Row-weighted decay** (Bassalygo–Dobrushin form). `d` is a pseudometric (only the
triangle inequality through `k` and `0 ≤ m` are used). -/
theorem decay_rowweighted [Nonempty ι] (C : ι → ι → ℝ) (ρ b : ι → ℝ) (d : ι → ι → ℝ)
    (k : ι) (m α B : ℝ) (hm : 0 ≤ m) (hα : α < 1)
    (hC : ∀ i j, 0 ≤ C i j) (hρ : ∀ i, 0 ≤ ρ i)
    (htri : ∀ i j, d i k ≤ d i j + d j k)
    (hrec : ∀ i, ρ i ≤ ∑ j, C i j * ρ j + b i)
    (hb : ∀ i, b i ≤ B * exp (-(m * d i k)))
    (hrow : ∀ i, ∑ j, C i j * exp (m * d i j) ≤ α) :
    ∀ i, ρ i ≤ B / (1 - α) * exp (-(m * d i k)) := by
  -- M = max over i of ρ i · exp (m d i k)
  set f : ι → ℝ := fun i => ρ i * exp (m * d i k)
  obtain ⟨i₀, -, hi₀⟩ := exists_max_image (univ : Finset ι) f univ_nonempty
  set M := f i₀
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (hρ i) (exp_pos _).le
  have hM0 : 0 ≤ M := hf0 i₀
  have hfM : ∀ i, f i ≤ M := fun i => hi₀ i (mem_univ i)
  have key : ∀ i, f i ≤ α * M + B := by
    intro i
    have e1 : f i ≤ (∑ j, C i j * ρ j + b i) * exp (m * d i k) :=
      mul_le_mul_of_nonneg_right (hrec i) (exp_pos _).le
    have e2 : b i * exp (m * d i k) ≤ B := by
      calc b i * exp (m * d i k) ≤ B * exp (-(m * d i k)) * exp (m * d i k) :=
            mul_le_mul_of_nonneg_right (hb i) (exp_pos _).le
        _ = B := by rw [mul_assoc, ← exp_add]; simp
    have e3 : ∀ j, C i j * ρ j * exp (m * d i k) ≤ C i j * exp (m * d i j) * M := by
      intro j
      have hexp : exp (m * d i k) ≤ exp (m * d i j) * exp (m * d j k) := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left (htri i j) hm
        linarith
      calc C i j * ρ j * exp (m * d i k)
          ≤ C i j * ρ j * (exp (m * d i j) * exp (m * d j k)) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (hC i j) (hρ j))
        _ = C i j * exp (m * d i j) * f j := by simp only [f]; ring
        _ ≤ C i j * exp (m * d i j) * M :=
            mul_le_mul_of_nonneg_left (hfM j) (mul_nonneg (hC i j) (exp_pos _).le)
    have e4 : (∑ j, C i j * ρ j) * exp (m * d i k) ≤ α * M := by
      rw [sum_mul]
      calc ∑ j, C i j * ρ j * exp (m * d i k) ≤ ∑ j, C i j * exp (m * d i j) * M :=
            sum_le_sum fun j _ => e3 j
        _ = (∑ j, C i j * exp (m * d i j)) * M := by rw [sum_mul]
        _ ≤ α * M := mul_le_mul_of_nonneg_right (hrow i) hM0
    calc f i ≤ (∑ j, C i j * ρ j + b i) * exp (m * d i k) := e1
      _ = (∑ j, C i j * ρ j) * exp (m * d i k) + b i * exp (m * d i k) := by ring
      _ ≤ α * M + B := add_le_add e4 e2
  have hpos : 0 < 1 - α := by linarith
  have hMB : M ≤ B / (1 - α) := by
    rw [le_div_iff₀ hpos]; have := key i₀; linarith
  intro i
  have hi : ρ i * exp (m * d i k) ≤ B / (1 - α) := (hfM i).trans hMB
  have hE : 0 < exp (m * d i k) := exp_pos _
  calc ρ i = ρ i * exp (m * d i k) * exp (-(m * d i k)) := by
        rw [mul_assoc, ← exp_add]; simp
    _ ≤ B / (1 - α) * exp (-(m * d i k)) :=
        mul_le_mul_of_nonneg_right hi (exp_pos _).le

omit [DecidableEq ι] in
/-- The case `m = 0`: a uniform bound `ρ ≤ B / (1 - α)`. -/
theorem sup_bound [Nonempty ι] (C : ι → ι → ℝ) (ρ b : ι → ℝ) (α B : ℝ) (hα : α < 1)
    (hC : ∀ i j, 0 ≤ C i j) (hρ : ∀ i, 0 ≤ ρ i)
    (hrec : ∀ i, ρ i ≤ ∑ j, C i j * ρ j + b i) (hb : ∀ i, b i ≤ B)
    (hrow : ∀ i, ∑ j, C i j ≤ α) :
    ∀ i, ρ i ≤ B / (1 - α) := by
  intro i
  have := decay_rowweighted C ρ b (fun _ _ => 0) (Classical.arbitrary ι) 0 α B le_rfl hα hC hρ
    (fun _ _ => by simp) hrec (fun i => by simpa using hb i) (fun i => by simpa using hrow i) i
  simpa using this

end YangMills.StrongCoupling.Comparison
