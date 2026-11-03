import YangMills.StrongCoupling.CouplingMinimality

/-!
# The coupling half of the W₁ Dobrushin comparison (G1): interface

Companion to `DobrushinComparison.lean` (item G1 of `strong-coupling/forest/A4_LEAN.md`).

* `resolvent_comparison`: `ρ ≤ C ρ + b` with weighted column sums `≤ θ < 1` gives
  `∑ w ρ ≤ (1 / (1 - θ)) ∑ w b`.
* `decay_with_floor`: `decay_rowweighted` with an extra constant source `ε`, at the price
  `ε / (1 - α₀)`. A spatially uniform update error therefore leaves an additive
  floor even when the nonconstant part decays exponentially.
* Couplings: coupled updates with the right marginals map couplings to couplings
  (`coupled_update_isCoupling`); one coupled update integrated against a coupling (`bind_step_le`);
  the discrepancy recurrence for a coupling that one coupled update cannot improve
  (`minimal_recurrence`), which is what the minimising coupling of Lemma `comparison` provides; the
  real recurrence and the weighted comparison (`minimal_comparison`); and expectations bounded by
  coordinate discrepancies (`observable_bound`).

The hypothesis `hmin` uses local non-improvement rather than simultaneous invariance
under the coupled updates. No claim about generic failure of invariance is needed.

Not proved here: for the SU(2) specification, measurable coupled updates whose expected discrepancy
is bounded by the Dobrushin coefficients (`hstep`), and the existence of the minimising coupling
(weak compactness of the couplings, continuity of `∑ w ∫ D`). Finite index sets only; no
infinite-volume limit.
-/

open Finset Real Matrix

namespace YangMills.StrongCoupling.WassersteinBridge

section Arithmetic

variable {ι : Type*} [Fintype ι]

/-- Exchange of the order of summation in `∑ i, w i * (C x) i`. -/
lemma weighted_mulVec_eq (C : Matrix ι ι ℝ) (w x : ι → ℝ) :
    ∑ i, w i * (C *ᵥ x) i = ∑ j, (∑ i, w i * C i j) * x j := by
  simp only [mulVec, dotProduct, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- One step of the column condition on a nonnegative vector. -/
lemma weighted_mulVec_le (C : Matrix ι ι ℝ) (w x : ι → ℝ) (θ : ℝ)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j) (hx : ∀ j, 0 ≤ x j) :
    ∑ i, w i * (C *ᵥ x) i ≤ θ * ∑ i, w i * x i := by
  rw [weighted_mulVec_eq, mul_sum]
  exact sum_le_sum fun j _ => by
    calc (∑ i, w i * C i j) * x j ≤ (θ * w j) * x j := mul_le_mul_of_nonneg_right (hcol j) (hx j)
      _ = θ * (w j * x j) := by ring

/-- **Weighted comparison with a source.** A nonnegative subsolution `ρ ≤ C ρ + b` of a weighted
column contraction satisfies `∑ w ρ ≤ (1 / (1 - θ)) ∑ w b`. Only `w ≥ 0`, `ρ ≥ 0` and `θ < 1` are
used; `C ≥ 0`, `b ≥ 0`, `w > 0` and `θ ≥ 0` are not needed. -/
theorem resolvent_comparison (C : Matrix ι ι ℝ) (w ρ b : ι → ℝ) (θ : ℝ) (hθ : θ < 1)
    (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, 0 ≤ ρ i)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j)
    (hrec : ∀ i, ρ i ≤ (C *ᵥ ρ) i + b i) :
    ∑ i, w i * ρ i ≤ 1 / (1 - θ) * ∑ i, w i * b i := by
  have h1 : ∑ i, w i * ρ i ≤ ∑ i, w i * (C *ᵥ ρ) i + ∑ i, w i * b i := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hrec i) (hw i)
  have h2 := weighted_mulVec_le C w ρ θ hcol hρ
  have hpos : 0 < 1 - θ := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  nlinarith

end Arithmetic

section Decay

variable {ι : Type*} [Fintype ι]

/-- **Decay with a floor.** If `ρ ≤ C ρ + B e^{-m d(·,k)} + ε`, with weighted row sums `≤ αₘ < 1`
and plain row sums `≤ α₀ < 1`, then `ρ i ≤ B / (1 - αₘ) e^{-m d(i,k)} + ε / (1 - α₀)`.
Proved from `decay_rowweighted` applied to `max (ρ - ε / (1 - α₀)) 0`. Compared with
`decay_rowweighted`: the source has the extra constant `ε`; `B ≥ 0` is assumed (there it is not);
`ρ ≥ 0` is **not** assumed, and `ι` may be empty. -/
theorem decay_with_floor (C : ι → ι → ℝ) (ρ : ι → ℝ) (d : ι → ι → ℝ) (k : ι)
    (m αm α0 B ε : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hαm : αm < 1) (hα0 : α0 < 1)
    (hC : ∀ i j, 0 ≤ C i j) (htri : ∀ i j, d i k ≤ d i j + d j k)
    (hrowm : ∀ i, ∑ j, C i j * exp (m * d i j) ≤ αm) (hrow0 : ∀ i, ∑ j, C i j ≤ α0)
    (hrec : ∀ i, ρ i ≤ ∑ j, C i j * ρ j + B * exp (-(m * d i k)) + ε) :
    ∀ i, ρ i ≤ B / (1 - αm) * exp (-(m * d i k)) + ε / (1 - α0) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact fun i => isEmptyElim i
  have hpos0 : 0 < 1 - α0 := by linarith
  set τ := ε / (1 - α0) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hε hpos0.le
  have hτid : τ * α0 + ε - τ = 0 := by
    rw [hτ]; field_simp; ring
  set σ : ι → ℝ := fun i => max (ρ i - τ) 0 with hσ
  have hσ0 : ∀ i, 0 ≤ σ i := fun i => le_max_right _ _
  have hσrec : ∀ i, σ i ≤ ∑ j, C i j * σ j + B * exp (-(m * d i k)) := by
    intro i
    have hb0 : 0 ≤ B * exp (-(m * d i k)) := mul_nonneg hB (exp_pos _).le
    have hsum : ∑ j, C i j * (ρ j - τ) ≤ ∑ j, C i j * σ j :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hC i j)
    have hsplit : ∑ j, C i j * ρ j = ∑ j, C i j * (ρ j - τ) + τ * ∑ j, C i j := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    have hτC : τ * ∑ j, C i j ≤ τ * α0 := mul_le_mul_of_nonneg_left (hrow0 i) hτ0
    have h1 : ρ i - τ ≤ ∑ j, C i j * σ j + B * exp (-(m * d i k)) := by
      linarith [hrec i]
    have h2 : 0 ≤ ∑ j, C i j * σ j + B * exp (-(m * d i k)) :=
      add_nonneg (sum_nonneg fun j _ => mul_nonneg (hC i j) (hσ0 j)) hb0
    exact max_le h1 h2
  have hdec := Comparison.decay_rowweighted C σ (fun i => B * exp (-(m * d i k))) d k m αm B
    hm hαm hC hσ0 htri hσrec (fun _ => le_rfl) hrowm
  intro i
  have h3 := hdec i
  have h4 : ρ i - τ ≤ σ i := le_max_left _ _
  linarith

/-- With `d ≥ 0` and `m ≥ 0`, the plain row sums are at most the weighted row sums. -/
theorem row_sum_le_weighted (C : ι → ι → ℝ) (d : ι → ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hd : ∀ i j, 0 ≤ d i j) (hC : ∀ i j, 0 ≤ C i j) (i : ι) :
    ∑ j, C i j ≤ ∑ j, C i j * exp (m * d i j) :=
  sum_le_sum fun j _ => le_mul_of_one_le_right (hC i j) (one_le_exp (mul_nonneg hm (hd i j)))

/-- `decay_with_floor` with `α₀ = αₘ`, for `d ≥ 0`. A separately known smaller `α₀` gives the
sharper floor of `decay_with_floor`. -/
theorem decay_with_floor_of_nonneg (C : ι → ι → ℝ) (ρ : ι → ℝ) (d : ι → ι → ℝ) (k : ι)
    (m αm B ε : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hαm : αm < 1)
    (hC : ∀ i j, 0 ≤ C i j) (hd : ∀ i j, 0 ≤ d i j) (htri : ∀ i j, d i k ≤ d i j + d j k)
    (hrowm : ∀ i, ∑ j, C i j * exp (m * d i j) ≤ αm)
    (hrec : ∀ i, ρ i ≤ ∑ j, C i j * ρ j + B * exp (-(m * d i k)) + ε) :
    ∀ i, ρ i ≤ B / (1 - αm) * exp (-(m * d i k)) + ε / (1 - αm) :=
  decay_with_floor C ρ d k m αm αm B ε hm hB hε hαm hαm hC htri hrowm
    (fun i => (row_sum_le_weighted C d m hm hd hC i).trans (hrowm i)) hrec

end Decay

section Coupling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `γ` is a coupling of `μ` and `ν`: its marginals are `μ` and `ν`. -/
def IsCoupling (μ ν : Measure Ω) (γ : Measure (Ω × Ω)) : Prop :=
  γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν

/-- **Coupling bound for observables.** If `‖f x - f y‖ₑ ≤ D (x, y)` and `γ` couples `μ` and `ν`,
then `|∫ f dμ - ∫ f dν| ≤ ∫ D dγ`. -/
theorem coupling_integral_diff_le {μ ν : Measure Ω} {γ : Measure (Ω × Ω)}
    (hγ : IsCoupling μ ν γ) {f : Ω → ℝ} (hfm : Measurable f) (hμ : Integrable f μ)
    (hν : Integrable f ν) (D : Ω × Ω → ℝ≥0∞) (hD : ∀ p, ‖f p.1 - f p.2‖ₑ ≤ D p) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ∫⁻ p, D p ∂γ := by
  obtain ⟨h1, h2⟩ := hγ
  have hm1 : ∫ x, f x ∂μ = ∫ p, f p.1 ∂γ := by
    rw [← h1, integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable]
  have hm2 : ∫ x, f x ∂ν = ∫ p, f p.2 ∂γ := by
    rw [← h2, integral_map measurable_snd.aemeasurable hfm.aestronglyMeasurable]
  have hi1 : Integrable (fun p : Ω × Ω => f p.1) γ :=
    (integrable_map_measure hfm.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (by rw [h1]; exact hμ)
  have hi2 : Integrable (fun p : Ω × Ω => f p.2) γ :=
    (integrable_map_measure hfm.aestronglyMeasurable measurable_snd.aemeasurable).mp
      (by rw [h2]; exact hν)
  rw [hm1, hm2, ← integral_sub hi1 hi2, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ p, (f p.1 - f p.2) ∂γ‖ₑ ≤ ∫⁻ p, ‖f p.1 - f p.2‖ₑ ∂γ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p, D p ∂γ := lintegral_mono hD

/-- **Coupled updates preserve couplings.** Let `Q` be a kernel on pairs whose marginals are the
single updates, `(Q p).map fst = K p.1` and `(Q p).map snd = K' p.2`. If `μ` is `K`-invariant and
`ν` is `K'`-invariant (as Gibbs measures are under their heat-bath updates), then `Q` maps
couplings of `μ` and `ν` to couplings of `μ` and `ν`. -/
theorem coupled_update_isCoupling {μ ν : Measure Ω} {γ : Measure (Ω × Ω)}
    (hγ : IsCoupling μ ν γ) (K K' : Kernel Ω Ω) (Q : Kernel (Ω × Ω) (Ω × Ω))
    (hQ1 : ∀ p, (Q p).map Prod.fst = K p.1) (hQ2 : ∀ p, (Q p).map Prod.snd = K' p.2)
    (hK : μ.bind K = μ) (hK' : ν.bind K' = ν) : IsCoupling μ ν (γ.bind Q) := by
  obtain ⟨h1, h2⟩ := hγ
  constructor
  · ext s hs
    rw [Measure.map_apply measurable_fst hs,
      Measure.bind_apply (measurable_fst hs) Q.measurable.aemeasurable]
    have hQs : ∀ p, Q p (Prod.fst ⁻¹' s) = K p.1 s := fun p => by
      rw [← Measure.map_apply measurable_fst hs, hQ1]
    simp_rw [hQs]
    rw [← hK, Measure.bind_apply hs K.measurable.aemeasurable, ← h1,
      lintegral_map (K.measurable_coe hs) measurable_fst]
  · ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.bind_apply (measurable_snd hs) Q.measurable.aemeasurable]
    have hQs : ∀ p, Q p (Prod.snd ⁻¹' s) = K' p.2 s := fun p => by
      rw [← Measure.map_apply measurable_snd hs, hQ2]
    simp_rw [hQs]
    rw [← hK', Measure.bind_apply hs K'.measurable.aemeasurable, ← h2,
      lintegral_map (K'.measurable_coe hs) measurable_snd]

/-- One coupled update integrated against `γ`: if `∫ D i d(Q p) ≤ ∑ⱼ c j · D j p + β p` for every
pair `p`, then `∫ D i d(γ Q) ≤ ∑ⱼ c j ∫ D j dγ + ∫ β dγ`. -/
theorem bind_step_le {ι : Type*} [Fintype ι] (γ : Measure (Ω × Ω))
    (Q : Kernel (Ω × Ω) (Ω × Ω)) (D : ι → Ω × Ω → ℝ≥0∞) (hD : ∀ j, Measurable (D j))
    (c : ι → ℝ≥0∞) (β : Ω × Ω → ℝ≥0∞) (hβ : Measurable β) (i : ι)
    (hstep : ∀ p, ∫⁻ q, D i q ∂(Q p) ≤ ∑ j, c j * D j p + β p) :
    ∫⁻ p, D i p ∂(γ.bind Q) ≤ ∑ j, c j * ∫⁻ p, D j p ∂γ + ∫⁻ p, β p ∂γ := by
  calc ∫⁻ p, D i p ∂(γ.bind Q) = ∫⁻ p, ∫⁻ q, D i q ∂(Q p) ∂γ :=
        Measure.lintegral_bind Q.measurable.aemeasurable (hD i).aemeasurable
    _ ≤ ∫⁻ p, (∑ j, c j * D j p + β p) ∂γ := lintegral_mono hstep
    _ = ∑ j, c j * ∫⁻ p, D j p ∂γ + ∫⁻ p, β p ∂γ := by
        rw [lintegral_add_right _ hβ, lintegral_finsetSum _ fun j _ => (hD j).const_mul _]
        congr 1
        exact sum_congr rfl fun j _ => lintegral_const_mul _ (hD j)

/-- **Discrepancy recurrence from a coupling that one coupled update cannot improve.** If
`∫ D i dγ ≤ ∫ D i d(γ Q)` and one coupled update bounds the expected discrepancy at `i` by
`∑ⱼ c j · D j + β`, then `ρ i ≤ ∑ⱼ c j ρ j + ∫ β dγ`, where `ρ j = ∫ D j dγ`. The minimising
coupling of Lemma `comparison` gives `hmin` (the update changes only the coordinate `i`, and
`coupled_update_isCoupling` keeps the result a coupling); invariance `γ.bind Q = γ` is the case of
equality. Values in `[0, ∞]`, so no integrability is assumed. -/
theorem minimal_recurrence {ι : Type*} [Fintype ι] (γ : Measure (Ω × Ω))
    (Q : Kernel (Ω × Ω) (Ω × Ω)) (D : ι → Ω × Ω → ℝ≥0∞) (hD : ∀ j, Measurable (D j))
    (c : ι → ℝ≥0∞) (β : Ω × Ω → ℝ≥0∞) (hβ : Measurable β) (i : ι)
    (hmin : ∫⁻ p, D i p ∂γ ≤ ∫⁻ p, D i p ∂(γ.bind Q))
    (hstep : ∀ p, ∫⁻ q, D i q ∂(Q p) ≤ ∑ j, c j * D j p + β p) :
    ∫⁻ p, D i p ∂γ ≤ ∑ j, c j * ∫⁻ p, D j p ∂γ + ∫⁻ p, β p ∂γ :=
  hmin.trans (bind_step_le γ Q D hD c β hβ i hstep)

/-- A global finite weighted-cost minimum supplies the measure-level local
non-improvement hypothesis. Existence of such a minimum and the update's
marginals are separate obligations. -/
theorem local_nonimprovement_of_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Measure (Ω × Ω)) (Q : Kernel (Ω × Ω) (Ω × Ω))
    (D : ι → Ω × Ω → ℝ≥0∞) (w : ι → ℝ) (i : ι) (hw : 0 < w i)
    (hfin : ∀ j, ∫⁻ p, D j p ∂γ ≠ ∞)
    (hfin' : ∀ j, ∫⁻ p, D j p ∂(γ.bind Q) ≠ ∞)
    (hfix : ∀ j, j ≠ i → ∫⁻ p, D j p ∂(γ.bind Q) = ∫⁻ p, D j p ∂γ)
    (hmin : CouplingMinimality.cost w
        (fun μ j => (∫⁻ p, D j p ∂μ).toReal) γ ≤
      CouplingMinimality.cost w
        (fun μ j => (∫⁻ p, D j p ∂μ).toReal) (γ.bind Q)) :
    ∫⁻ p, D i p ∂γ ≤ ∫⁻ p, D i p ∂(γ.bind Q) := by
  have hc := CouplingMinimality.cost_update w
    (fun μ j => (∫⁻ p, D j p ∂μ).toReal) γ (γ.bind Q) i
    (fun j hj => congrArg ENNReal.toReal (hfix j hj))
  have hr : (∫⁻ p, D i p ∂γ).toReal ≤ (∫⁻ p, D i p ∂(γ.bind Q)).toReal := by
    nlinarith
  exact (ENNReal.toReal_le_toReal (hfin i) (hfin' i)).mp hr

/-- The recurrence in `[0, ∞]`, with real coefficients and finite values, gives the real recurrence
`ρ ≤ C ρ + b` and the weighted comparison `resolvent_comparison`. -/
theorem comparison_of_recurrence {ι : Type*} [Fintype ι] (X Y : ι → ℝ≥0∞)
    (C : Matrix ι ι ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hrec : ∀ i, X i ≤ ∑ j, ENNReal.ofReal (C i j) * X j + Y i)
    (hX : ∀ i, X i ≠ ∞) (hY : ∀ i, Y i ≠ ∞)
    (w : ι → ℝ) (θ : ℝ) (hθ : θ < 1) (hw : ∀ i, 0 ≤ w i)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j) :
    (∀ i, (X i).toReal ≤ (C *ᵥ fun j => (X j).toReal) i + (Y i).toReal) ∧
      ∑ i, w i * (X i).toReal ≤ 1 / (1 - θ) * ∑ i, w i * (Y i).toReal := by
  have hreal : ∀ i, (X i).toReal ≤ (C *ᵥ fun j => (X j).toReal) i + (Y i).toReal := by
    intro i
    have hterm : ∀ j ∈ (univ : Finset ι), ENNReal.ofReal (C i j) * X j ≠ ∞ :=
      fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hX j)
    have hsum : ∑ j, ENNReal.ofReal (C i j) * X j ≠ ∞ := ENNReal.sum_ne_top.mpr hterm
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum, hY i⟩) (hrec i)
    rw [ENNReal.toReal_add hsum (hY i), ENNReal.toReal_sum hterm] at h'
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hC i _)] at h'
    exact h'
  exact ⟨hreal, resolvent_comparison C w _ _ θ hθ hw (fun i => ENNReal.toReal_nonneg) hcol hreal⟩

/-- **From a minimising coupling to the weighted comparison.** If no single coupled update improves
the expected discrepancy of `γ` at any site (`hmin`), the coefficients are real with `C i j ≥ 0`,
and the discrepancies are finite, then `ρ = (∫ D i dγ)ᵢ` satisfies `ρ ≤ C ρ + b` with
`b = (∫ β i dγ)ᵢ`, and `∑ w ρ ≤ (1 / (1 - θ)) ∑ w b`. The hypotheses `hmin` and `hstep` are what
G1 has to supply for a specification. -/
theorem minimal_comparison {ι : Type*} [Fintype ι] (γ : Measure (Ω × Ω))
    (Q : ι → Kernel (Ω × Ω) (Ω × Ω))
    (D : ι → Ω × Ω → ℝ≥0∞) (hD : ∀ j, Measurable (D j))
    (hmin : ∀ i, ∫⁻ p, D i p ∂γ ≤ ∫⁻ p, D i p ∂(γ.bind (Q i)))
    (C : Matrix ι ι ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (β : ι → Ω × Ω → ℝ≥0∞) (hβ : ∀ i, Measurable (β i))
    (hstep : ∀ i p, ∫⁻ q, D i q ∂(Q i p) ≤ ∑ j, ENNReal.ofReal (C i j) * D j p + β i p)
    (hDfin : ∀ i, ∫⁻ p, D i p ∂γ ≠ ∞) (hβfin : ∀ i, ∫⁻ p, β i p ∂γ ≠ ∞)
    (w : ι → ℝ) (θ : ℝ) (hθ : θ < 1) (hw : ∀ i, 0 ≤ w i)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j) :
    (∀ i, (∫⁻ p, D i p ∂γ).toReal ≤
        (C *ᵥ fun j => (∫⁻ p, D j p ∂γ).toReal) i + (∫⁻ p, β i p ∂γ).toReal) ∧
      ∑ i, w i * (∫⁻ p, D i p ∂γ).toReal ≤
        1 / (1 - θ) * ∑ i, w i * (∫⁻ p, β i p ∂γ).toReal :=
  comparison_of_recurrence (fun i => ∫⁻ p, D i p ∂γ) (fun i => ∫⁻ p, β i p ∂γ) C hC
    (fun i => minimal_recurrence γ (Q i) D hD (fun j => ENNReal.ofReal (C i j)) (β i) (hβ i) i
      (hmin i) (hstep i)) hDfin hβfin w θ hθ hw hcol

/-- Weighted comparison from a finite global cost minimum and local coupled
updates. This discharges the local `hmin` interface, not existence of the
minimum or of the specification-dependent kernels. -/
theorem cost_minimal_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Measure (Ω × Ω)) (Q : ι → Kernel (Ω × Ω) (Ω × Ω))
    (D : ι → Ω × Ω → ℝ≥0∞) (hD : ∀ j, Measurable (D j))
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hmin : ∀ i, CouplingMinimality.cost w
        (fun μ j => (∫⁻ p, D j p ∂μ).toReal) γ ≤
      CouplingMinimality.cost w
        (fun μ j => (∫⁻ p, D j p ∂μ).toReal) (γ.bind (Q i)))
    (hfix : ∀ i j, j ≠ i →
      ∫⁻ p, D j p ∂(γ.bind (Q i)) = ∫⁻ p, D j p ∂γ)
    (hfin : ∀ j, ∫⁻ p, D j p ∂γ ≠ ∞)
    (hfin' : ∀ i j, ∫⁻ p, D j p ∂(γ.bind (Q i)) ≠ ∞)
    (C : Matrix ι ι ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (β : ι → Ω × Ω → ℝ≥0∞) (hβ : ∀ i, Measurable (β i))
    (hstep : ∀ i p, ∫⁻ q, D i q ∂(Q i p) ≤
      ∑ j, ENNReal.ofReal (C i j) * D j p + β i p)
    (hβfin : ∀ i, ∫⁻ p, β i p ∂γ ≠ ∞)
    (θ : ℝ) (hθ : θ < 1)
    (hcol : ∀ j, ∑ i, w i * C i j ≤ θ * w j) :
    ∑ i, w i * (∫⁻ p, D i p ∂γ).toReal ≤
      1 / (1 - θ) * ∑ i, w i * (∫⁻ p, β i p ∂γ).toReal := by
  have hn : ∀ i, ∫⁻ p, D i p ∂γ ≤ ∫⁻ p, D i p ∂(γ.bind (Q i)) :=
    fun i => local_nonimprovement_of_cost γ (Q i) D w i (hw i)
      hfin (hfin' i) (hfix i) (hmin i)
  exact (minimal_comparison γ Q D hD hn C hC β hβ hstep hfin hβfin
    w θ hθ (fun i => (hw i).le) hcol).2

/-- **Observables from coordinate discrepancies.** If `‖f x - f y‖ₑ ≤ ∑ᵢ aᵢ Dᵢ(x, y)` and `γ`
couples `μ` and `ν`, then `|∫ f dμ - ∫ f dν| ≤ ∑ᵢ aᵢ ∫ Dᵢ dγ`. With `minimal_comparison` this
turns the discrepancy bounds into bounds on expectations. -/
theorem observable_bound {ι : Type*} [Fintype ι] {μ ν : Measure Ω} {γ : Measure (Ω × Ω)}
    (hγ : IsCoupling μ ν γ) {f : Ω → ℝ} (hfm : Measurable f) (hμ : Integrable f μ)
    (hν : Integrable f ν) (D : ι → Ω × Ω → ℝ≥0∞) (hD : ∀ j, Measurable (D j)) (a : ι → ℝ≥0∞)
    (hf : ∀ p, ‖f p.1 - f p.2‖ₑ ≤ ∑ j, a j * D j p) :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ∑ j, a j * ∫⁻ p, D j p ∂γ := by
  have h := coupling_integral_diff_le hγ hfm hμ hν (fun p => ∑ j, a j * D j p) hf
  rw [lintegral_finsetSum _ fun j _ => (hD j).const_mul _] at h
  refine h.trans (le_of_eq (sum_congr rfl fun j _ => lintegral_const_mul _ (hD j)))

end Coupling

end YangMills.StrongCoupling.WassersteinBridge
