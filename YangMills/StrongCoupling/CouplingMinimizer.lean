import YangMills.StrongCoupling.WassersteinBridge

/-!
# A continuous coupling cost attains its minimum on a compact metric space

This supplies existence of a global cost minimiser for finite compact metric
spin spaces. It does not construct a measurable family of conditional
optimal couplings or establish a specification-dependent one-step estimate.
-/

open MeasureTheory Set

namespace YangMills.StrongCoupling.CouplingMinimizer

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- Probability couplings with fixed marginals, in the weak topology. -/
def couplings (μ ν : ProbabilityMeasure Ω) : Set (ProbabilityMeasure (Ω × Ω)) :=
  {γ | γ.map measurable_fst.aemeasurable = μ ∧
    γ.map measurable_snd.aemeasurable = ν}

theorem couplings_nonempty (μ ν : ProbabilityMeasure Ω) :
    (couplings μ ν).Nonempty := by
  let γ : ProbabilityMeasure (Ω × Ω) :=
    ⟨(μ : Measure Ω).prod (ν : Measure Ω), inferInstance⟩
  refine ⟨γ, ?_, ?_⟩
  · apply Subtype.ext
    simp [γ, ProbabilityMeasure.map, Measure.map_fst_prod]
  · apply Subtype.ext
    simp [γ, ProbabilityMeasure.map, Measure.map_snd_prod]

theorem couplings_isClosed (μ ν : ProbabilityMeasure Ω) :
    IsClosed (couplings μ ν) := by
  exact (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst)
    continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)

theorem couplings_isCompact (μ ν : ProbabilityMeasure Ω) :
    IsCompact (couplings μ ν) :=
  (couplings_isClosed μ ν).isCompact

/-- The global continuous-cost minimising coupling exists. -/
theorem exists_minimizer (μ ν : ProbabilityMeasure Ω) (c : C(Ω × Ω, ℝ)) :
    ∃ γ ∈ couplings μ ν, ∀ π ∈ couplings μ ν,
      (∫ p, c p ∂(γ : Measure (Ω × Ω))) ≤
        ∫ p, c p ∂(π : Measure (Ω × Ω)) := by
  exact (couplings_isCompact μ ν).exists_isMinOn (couplings_nonempty μ ν)
    (ProbabilityMeasure.continuous_integral_continuousMap c).continuousOn

/-- Identification with the marginal-based interface of WassersteinBridge. -/
theorem mem_couplings_iff (μ ν : ProbabilityMeasure Ω)
    (γ : ProbabilityMeasure (Ω × Ω)) :
    γ ∈ couplings μ ν ↔ WassersteinBridge.IsCoupling
      (μ : Measure Ω) (ν : Measure Ω) (γ : Measure (Ω × Ω)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨congrArg ProbabilityMeasure.toMeasure h1,
      congrArg ProbabilityMeasure.toMeasure h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩

end YangMills.StrongCoupling.CouplingMinimizer
