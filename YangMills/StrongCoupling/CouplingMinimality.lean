import YangMills.StrongCoupling.DobrushinComparison

/-!
# Minimality supplies a discrepancy recurrence without stationarity

This is an abstract finite-dimensional interface. `P` may be a type of
couplings with fixed marginals, `d p i` an expected coordinate discrepancy,
and `update i` a coupling obtained by a local coupled update. No existence
of couplings, measurable update kernels, or minimisers is asserted here.

A weighted-cost minimiser need not be invariant under individual coupled
updates. Minimality and preservation of the other discrepancies suffice.
The final theorem feeds this recurrence into the existing comparison core.
-/

open Finset

namespace YangMills.StrongCoupling.CouplingMinimality

variable {ι P : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite weighted discrepancy cost of an abstract coupling. -/
def cost (w : ι → ℝ) (d : P → ι → ℝ) (p : P) : ℝ := ∑ i, w i * d p i

/-- A local update changes only its own summand in the total cost. -/
lemma cost_update (w : ι → ℝ) (d : P → ι → ℝ) (p q : P) (i : ι)
    (hfix : ∀ j, j ≠ i → d q j = d p j) :
    cost w d q = cost w d p + w i * (d q i - d p i) := by
  have hterm : ∀ j, w j * d q j = w j * d p j +
      if j = i then w i * (d q i - d p i) else 0 := by
    intro j
    by_cases h : j = i
    · subst j; simp only [ite_true]; ring
    · simp [h, hfix j h]
  simp only [cost, hterm, sum_add_distrib]
  simp

/-- Approximate cost minimality gives the local discrepancy inequality,
with its precise weight-dependent error. No sign hypotheses on d or b. -/
theorem recurrence_with_error (w : ι → ℝ) (d : P → ι → ℝ) (p q : P)
    (C : ι → ι → ℝ) (b : ι → ℝ) (i : ι) (ε : ℝ) (hw : 0 < w i)
    (hmin : cost w d p ≤ cost w d q + ε)
    (hfix : ∀ j, j ≠ i → d q j = d p j)
    (hstep : d q i ≤ ∑ j, C i j * d p j + b i) :
    d p i ≤ ∑ j, C i j * d p j + b i + ε / w i := by
  have hc := cost_update w d p q i hfix
  have hlocal : w i * d p i ≤ w i * d q i + ε := by linarith
  have hstep' := mul_le_mul_of_nonneg_left hstep hw.le
  apply (mul_le_mul_iff_right₀ hw).mp
  have hne : w i ≠ 0 := ne_of_gt hw
  have he : w i * (ε / w i) = ε := by field_simp
  rw [mul_add, he]
  linarith

/-- Exact cost minimality replaces stationary-coupling invariance. -/
theorem recurrence_of_minimality (w : ι → ℝ) (d : P → ι → ℝ) (p q : P)
    (C : ι → ι → ℝ) (b : ι → ℝ) (i : ι) (hw : 0 < w i)
    (hmin : cost w d p ≤ cost w d q)
    (hfix : ∀ j, j ≠ i → d q j = d p j)
    (hstep : d q i ≤ ∑ j, C i j * d p j + b i) :
    d p i ≤ ∑ j, C i j * d p j + b i := by
  simpa using recurrence_with_error w d p q C b i 0 hw
    (by simpa using hmin) hfix hstep

/-- The finite weighted boundary comparison from minimality of the coupling
cost. The hypotheses concerning the abstract updates remain explicit. -/
theorem comparison_of_minimality (S : Finset ι) (w : ι → ℝ)
    (d : P → ι → ℝ) (p : P) (update : ι → P) (C : ι → ι → ℝ)
    (θ D : ℝ) (hθ : θ < 1) (hθ0 : 0 ≤ θ)
    (hC : ∀ i j, 0 ≤ C i j) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 0 ≤ d p i) (hD : ∀ i ∈ S, d p i ≤ D)
    (hmin : ∀ i ∉ S, cost w d p ≤ cost w d (update i))
    (hfix : ∀ i ∉ S, ∀ j, j ≠ i → d (update i) j = d p j)
    (hstep : ∀ i ∉ S, d (update i) i ≤ ∑ j, C i j * d p j)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j) :
    ∑ i ∈ Sᶜ, w i * d p i ≤ θ * D / (1 - θ) * ∑ j ∈ S, w j := by
  apply Comparison.comparison_weighted S C w (d p) θ D hθ hθ0 hC
    (fun i => (hw i).le) hd hD _ hcol
  intro i hi
  simpa using recurrence_of_minimality w d p (update i) C (fun _ => 0) i
    (hw i) (hmin i hi) (hfix i hi) (by simpa using hstep i hi)

end YangMills.StrongCoupling.CouplingMinimality
