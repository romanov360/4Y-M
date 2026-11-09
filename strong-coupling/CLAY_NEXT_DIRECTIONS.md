Directions after Hexagon v7 (upstream main c794c07) and James's message of 2026-11-07. The 2026-11-06 plan (old #1–#8) is exhausted and is summarized at the end of the ranked list.

## Where things stand

Hexagon v7 reduces the mass gap to three inputs (Conclusion; Thm `avgtransfer`, Cor `bpuptuning`). Until all three are proved, the gap is not proved:

- **(H1)** The covariance bound at the coarsest scale, along the tuning. See Prop 130 `prop:bpcoarsezero`, Cor 149 `cor:bpfibH1`, and the sufficient condition in Prop 168 `prop:bppathsuff`.
- **(H2)** The split inequality at weak coupling, uniform in depth and volume. See Thm 114 `thm:bpsplitcond`. Prop 656 `prop:h2volume` shows that the naive version depends on the volume.
- **(E)** A nontrivial continuum limit (`ssec:limitE`).

New in main:
- Commit d90d88b: sharp Gaussian block decay and the Wilson fibre criterion.
- `gaussian-decay-section.tex` and `fibre-heatbath-section.tex`.

Only lean01–lean03 are in main. lean05 is not.

The OpenAI existence claim is still unreleased. If it holds, it bears on (E), not on (H1) or (H2) as Hexagon states them.

## Ranked directions

**A. A 4D SU(2) Gaussian fibre theorem, mapped into Thm 114. Highest priority.**
- Fix the 4D data explicitly: the section, the block map c, the curvature operator and the fibres F_{x'}.
- Prove the geometric hypotheses on the lattice. Get a stable decomposition with constants independent of depth and volume.
- Extend the variance estimate from linear observables to all of Gaussian L².
- Deliverable: explicit constants in the Gaussian model for the three hypotheses of Thm 114: (F) C_F, (X) ρ and (D) R. State the result as "Thm 114 holds with …".
- Build on:
  - d90d88b and `gaussian-decay-section.tex`;
  - `thm:bprowgauss`;
  - `cor:bprowFC` (Gaussian row sums (log b)/b).
- Ask James what lean05 covers (4D aligned covers?) and whether it is coming to main.

**B. Nonlinear (H2), organized around Thm 114 and Thm 181 (`thm:bpdeviation`).**
- **What Thm 114 gives.** It yields S(n',n; C_F/(1−η), (n'/(bn))⁴/(1−ρ²−η)), with η = ρ(RC_F)^{1/2}/n'².
- **Per-scale quantities.** Take n_j = 2n_{j−1}, so n'/(bn) = 1 when b = 2. Set η_{k,j} = ρ√(R C_F)/n_j² and δ_{k,j} = ρ² + η_{k,j}.
- **Target.** C_F ≤ C*, δ_{k,j} ≤ q < 1 and sup_k Σ_j δ_{k,j} ≤ S, all independent of depth and volume.
- **Consequence (checked).** C_A ≤ C*/(1−q), and Π_j C_B ≤ Π_j (1−δ_j)^{−1} ≤ exp(S/(1−q)), using −log(1−x) ≤ x/(1−q) on [0,q].
- **Where the content is.** η is summable automatically because n_j² grows geometrically. So the real condition is Σ_j ρ_j² ≤ S: the exterior constant (X) must decay along the scales.
- **Inputs.** The (X) and (D) bounds have to come from A. Thm 181 handles the deviation term when the chain does not compose exactly.
- **Status (2026-11-08): the Gaussian route for B is closed.**
  - In the abelian Gaussian model ρ₁ ≈ 0.8 is flat across scales, so Π C_B ≈ n_k^1.7 and (B′) fails (A_GAUSSIAN_FIBRE_4D.md §8–8.2).
  - This failure is forced: free Maxwell is gapless, so no block map can give it a uniform BP constant.
  - A therefore supplies (F), (X) and (D) per scale only. The decay ρ_j → 0 must come from input the free field lacks.
- **Next for B: find the non-Gaussian source of ρ_j decay.**
  1. *Coarse end.* At the last few scales the effective coupling is strong. A strong-coupling cluster expansion (Osterwalder–Seiler type) should give ρ_j ≤ Cβ_j^{1/4}-style smallness directly. Make this explicit for the BP exterior constant, and find the scale k* past which it holds.
  2. *~~Bridge~~ (corrected).* The old idea was a finite head of non-decaying scales plus a summable tail. That is wrong. Under asymptotic freedom the near-Gaussian scales are the **UV** ones (j near k), and there are ~k of them, not a fixed number. So bounded Γ needs C_{B,j} → 1 at the UV scales, at a summable rate. The next step is a candidate **no-go** (A_GAUSSIAN_FIBRE_4D §8.3). If the *optimal* Gaussian C_B is > 1, and the optimal C_B is continuous near the Gaussian, then Γ_0 ≥ (C_B^G − ε)^{#UV scales} → ∞, and Cor bpuptuning cannot apply as framed. Test this with the first-chaos lower bound C_B^lin (a generalized eigenproblem on the cluster).
  3. *Interface.* State the input needed from confinement (an area law, or a string tension bounded below) as a hypothesis on ρ_j, in the spirit of Chatterjee's mass gap ⇒ area law, but in reverse.
- **Sanity rule for B.** Any proposed mechanism for ρ_j decay that also applies to the free Maxwell field is wrong. Check every candidate against §8.2 first.

**C. An (H1) computational campaign on Prop 168, on the cluster with ≤ 64 CPUs. Diagnostics only.**
- **What to measure.** The partial sums Σ_{e≠j} |Cov_{π_V}(a_e^X, a_j^Y)|, against the threshold (1−h_{b−2})/3.
- **Order of runs:**
  1. against coarse volume at fixed depth k;
  2. varying k;
  3. stressing the conditioning V.
- **Where the sum accumulates.** Record the contribution from each of:
  - the 3 links sharing j's base point;
  - nearby shells;
  - distant shells, fitting the decay exponent (Prop 168 needs p > 4, with S_p = 3 + 320(1+1/(p−4)));
  - exceptional configurations.
- **Limits.** Sampled conditioning cannot establish the supremum over V, X and Y.
- **Control.** Prop `prop:bphidden`(ii) is a warning case: a mixture of product laws for which the sum grows with the volume. Run it as a control.

**D. Keep (E) alive with one concrete programme.**
- Fix one gauge-invariant observable, such as a smeared plaquette or a small Wilson loop, and one normalization.
- Targets for its separated correlations:
  - a nonzero limit;
  - uniform moments;
  - rotation restoration;
  - convergence.
- Every use of MIX must cite an independent infrared input, so the gap is never an assumed premise.

**Closed or parked (the 2026-11-06 plan; details in the log):**
- #1 ball certificate: interface drafted; waits on the OpenAI text.
- #2 marginal coupling: parked, gain O(β).
- #3 feasibility: done, L* = 2, heuristic only.
- #4 RP weak gap: no-go.
- #5 Polchinski: dropped.
- #6 Tomboulis: closed.
- #7 3D: folded into the others.

The old #8 deferred (H1) and (H2). That is reversed: they are now the main line. James's dump9 composition results are now the frame for B (Thm 181), not just a no-go.

## Suggested sequencing

| When | What |
|---|---|
| Week 1 | **A:** write out the 4D section, block map, curvature operator and fibres; confirm lean05's scope with James. **C:** first fixed-depth volume scan on the cluster. |
| Weeks 2–3 | **A:** stable decomposition and the Gaussian L² variance bound. **B:** ~~bound ρ_j along the scales using A~~ (closed: forced to fail in the Gaussian model). Now: strong-coupling bound on ρ_j at the coarse end, plus the finite-head/summable-tail form of Cor bpuptuning. |
| Weeks 3–4 | **C:** depth scan and conditioning stress. **D:** pick the observable and list every MIX dependency. |
| On OpenAI release | Read it against D and the #1 interface. |

Sources:
- [KITP working-group statement](https://www.kitp.ucsb.edu/sites/default/files/YM_working_group.pdf)
- [AI Weekly](https://aiweekly.co/alerts/openai-hands-eth-kakeya-yang-mills-proofs-to-reviewers)
- [IBTimes](https://co.ibtimes.com/openai-yang-mills-proof-review-2338)
- [Quantum Research Center](https://quantumresearch.center/news/articles/openai-yang-mills-existence/)
- [Chatterjee, strong mass gap implies area law (arXiv 2006.16229)](https://arxiv.org/pdf/2006.16229v2)
- [BBD Polchinski survey (arXiv 2307.07619)](https://arxiv.org/pdf/2307.07619)
- [sinh-Gordon log-Sobolev (arXiv 2609.28091)](https://arxiv.org/pdf/2609.28091)
- [Langevin dynamics of lattice Yang–Mills–Higgs (arXiv 2401.13299)](https://arxiv.org/pdf/2401.13299)
- [Chevyrev–Shen (arXiv 2503.03060)](https://arxiv.org/abs/2503.03060v2)
- [Dimock, Bałaban RG II (arXiv 1212.5562)](https://arxiv.org/pdf/1212.5562)
- [Wikipedia: Yang–Mills existence and mass gap](https://en.wikipedia.org/wiki/Yang%E2%80%93Mills_existence_and_mass_gap)

## Progress log

- **2026-11-06, #5 dropped.** Falsifier `strong-coupling/forest/experiments/polchinski2d/` (cluster job 1677160): for the single-plaquette SU(2) measure e^{β cos θ} on S³ (2D axial gauge), the multiscale curvature rate along the heat flow divided by the exact Poincaré gap is 0.59, 0.51, 0.33, 0.11, 0.007 at β = 0.5, 1, 2, 4, 8, which is exponential decay. The flow restores convexity only at t* ≈ 0.4, and the antipodal curvature ≈ −2β is paid for before then. β ≥ 16 rows are numerical underflow. Heuristic proxy for the BBD criterion, not a theorem about it.
- **2026-11-06, benchmark frozen** (see `forest/BALL_CERTIFICATE.md`): SU(2) 0.351, SU(3) 0.77. The 0.348/0.52 figures were a stale README.
- **2026-11-06, #1 interface drafted:** `forest/BALL_CERTIFICATE.md`.
- **#3 running:** `strong-coupling/forest/experiments/linresp/`.
- 2026-11-06: **#3 done** (job 1676562). L* = 2 for β ∈ [2.0, 2.6] at L=8, T=16. Caveats:
  C(r≥2) is at the noise level, and this is a weak-form periodic-state heuristic, not a
  sup-ω influence. Decision rule (L* ≤ 4) says continue with #1/#2 at small L and favours
  **#4** (weak gap in the RP state) over #6.
- 2026-11-06: **#2 step 5.1 done** (job 1679093). Reduced specification is worse in raw
  Lipschitz form (row 5.40 → 6.54 at L=2, β_W=0.30). See MARGINAL_COUPLING_T1 §6.
  Next is the second-derivative bound for the Z-terms.
- 2026-11-06: **#2 parked.** Variants (a) Hessian bound and (b) one-j marginalization give at most an
  11% drop in total boundary influence (L=2, β_W=0.30), shrinking with L and β (MARGINAL_COUPLING_T1 §6a–b).
  Next: **#4**.
- 2026-11-06: **#4 closed** (`forest/RP_WEAK_GAP_4.md`). The correlation-level RP criterion is a no-go, because
  effective masses are non-increasing (log-convexity), so finite data only bound the gap from above. The chessboard
  version reduces to C2 = (D). This also means #3's L* = 2 has no rigorous force. Next: **#6**.
- 2026-11-06: **#6 audited** (`forest/TOMBOULIS_AUDIT_6.md`). The gap localizes to (★′), monotonicity of the vortex
  ratio Z⁻/Z under c_j ↦ αc_j, or to the global continuation step. (★′) holds exactly in 2D for every group,
  including U(1), so 2D tests are uninformative. The decisive test is 4D U(1) vs SU(2) (small Monte Carlo job).
  This is not a route to the gap.
- 2026-11-06: **#7 started: #2 retested in 3D** (job 1681239, MARGINAL_COUPLING_T1 §6c). The gain is 18% at β_W = 0.30, 11% at 0.45,
  6% at 0.55 (L = 2), shrinking with L. It is O(β) by construction (β²/4 vs β weights). #2 is parked in both 3D and 4D.
  Remaining #7 content: #1 is dimension-free, #5 was dropped. Status: every concrete route is parked or closed except waiting for
  the OpenAI text (#1 interface) and the optional #6 Monte Carlo test.
- 2026-11-06: **#6 closed** (job 1681808, TOMBOULIS_AUDIT_6 §6). The (★′) proxy holds for 4D U(1) in its Coulomb phase (Δ < 0 at 11–16σ),
  so the Tomboulis failure is in the global continuation/eq. 5.21, not in the vortex inequality. Plan exhausted; next is the OpenAI text (#1 interface).
- 2026-11-07: **Plan replaced** after Hexagon v7 (main c794c07) and James's message, with four directions:
  - A: a 4D Gaussian fibre theorem, mapped into Thm 114.
  - B: nonlinear (H2) via Thm 114 and Thm 181.
  - C: diagnostics for the Prop 168 covariance sums.
  - D: a continuum programme.

  Checked that Π C_B ≤ exp(S/(1−q)). The real summability condition is Σ_j ρ_j² ≤ S.
- 2026-11-07: **A week 1 written** (`forest/A_GAUSSIAN_FIBRE_4D.md`). 4D data collected. In the Gaussian model, (F) and (X)
  reduce to the first Wiener chaos with the same constants (Lemmas A1, A2). (D) does not: open item A-D (mixed chaos
  overlaps through non-local coarse factors). Computation plan for λ_F, ρ_1, R_1 set; the lean05 question is drafted, not sent.
- 2026-11-07: **C run 1 done** (job 1695040, `forest/H1_PATHCOV.md`). Negative on method: Σ|Ĉov| equals its time-permuted null
  to < 0.4% at β_W ≤ 1.5, and scales by √2 on half the data, so it is the sampling-noise floor (∝ #pairs/√T), not Prop 168's sum.
  A ~10% excess at β_W = 2.3 is unresolved (possibly autocorrelation). Run 2 needs debiased per-shell estimators before b = 8, random V, or bphidden.
- 2026-11-07: **C run 2 submitted** (ym-pathcov-c2-debiased). Split-block unbiased estimator of per-shell ‖Cov‖_F² with jackknife
  errors, checked first on a synthetic hidden-mixture control with known truth (amp 0 and 0.1, L = 4, 6, 8). Chains: b = 4 at L = 4, 6, 8
  and b = 6 at L = 4, β_W ∈ {1.5, 2.3}, 3000 measurements each.
- 2026-11-07: **A/B: Gaussian ρ_1 job submitted** (ym-gaussrho-a1, job 1696054). Abelian Gaussian model: computes the first-chaos
  (X) constant (exact on all of L² by Lemma A2) via div-free path currents, the Hodge Green's function and the cube Hessian
  pseudo-inverse. Covers b = 3, 4, n'/b = 1, 2, 3, L = 6 vs 8 and cube offset. Selftests: Hodge identity, cube block, 0 ≤ ratio ≤ 1.
  The decision is ρ_1 vs n'/b: decreasing feeds B (Σ ρ_j² < ∞); flat near 1 blocks B as framed.
- 2026-11-07: **A week 2, (D):** Lemma A3 gives the exact chaos expansion w = Σ_{S≠∅} B^{⊗S}⊗A^{⊗rest}⊗I, which is orthogonal in |S|. A-D reduces to one combinatorial bound c_k(s) on symmetrized contractions. It is still open; the naive bound is C(k,s)². See forest/A_GAUSSIAN_FIBRE_4D.md §6. The C run 2 and ρ_1 jobs are still running.
- 2026-11-07: **D part 1:** the observable is fixed (24-plaquette action density at 0, Z_k = 𝒩_k(ε)^{−1/2}) and every MIX use in §limitE is listed (forest/D_E_OBSERVABLE.md). Finding: the *nontriviality* of the limit currently comes from the gap (Prop limitEnorm(ii)), which violates the D rule. Next: D1 (γ_k audit of limitEtwo), D2 (MIX-free nontriviality), D3 (audit limitEexact).
- 2026-11-07: **D part 2:** D1 is done. Lem limitEbox and Thm limitEtwo(i)–(iii) use only invariance and RP (γ_k ≤ 1). This **corrects part 1**: under Z_k = 𝒩_k(ε)^{−1/2}, nontriviality ⇔ the (NE)-type ratio (Cor limitEtwo(b)), with no gap. For n = 2, (E) is MIX-free modulo (SD)⇔(UV) and (NE). Those are the D targets now. D3 (limitEexact) and n ≥ 3 moments are still open.
- 2026-11-07: **D part 3 (audit complete):** D3 is done. Cor limitEexact uses only compactness and the O(4) subgroup dichotomy. MIX enters (E) only as a conclusion (clustering, continuum gap), never as a premise. The remaining (E) inputs are (SD)⇔(UV), (NE), (M_s) for n ≥ 3, (U_s) and (W_s).
- 2026-11-07: **A-D reduced to the first chaos (Lemma A4, forest/A_GAUSSIAN_FIBRE_4D.md §7).** With the Fock exponential law Γ(T) = (Γ(T_1)⊗Γ(T_2))Γ(J) and polar decomposition, the k-dependence disappears. R ≤ R_∠ = sup_x Σ_y ‖P_{V_x}P_{V_y}‖, where V_x = ran((I−P_c)P_𝓕 on C'_x). So in the Gaussian model Thm 114 holds on all of L² with (λ_F, ρ_1, R_∠). The open input is R_∠ < ∞ uniformly in volume: the leak subspaces of distant cubes must be almost orthogonal. Next: compute the principal angles numerically, and prove the decay from Thm blockdecay.
- 2026-11-07: **ρ_1 result (forest/A_GAUSSIAN_FIBRE_4D.md §8).**
  - ρ_1 ∈ [0.79, 0.86], volume-stable to 1e-3, so (X) holds uniformly.
  - It is flat in n'/b (0.79, 0.83, 0.835 at n'/b = 1, 2, 3). Hence **Σ_j ρ_j² diverges, and B as framed fails in the Gaussian model.**
  - B must be reframed. Options: use the uniform ρ < 1 as a per-scale contraction, or use a block map whose exterior constant decays.
  - The R_∠ (principal-angle) job ym-gaussangle-a4 is submitted, job 1698522.
- 2026-11-07: **C run 2 result (forest/H1_PATHCOV.md).**
  - The planted control passes: 1–3% recovery, null |Z| ≤ 1.1.
  - After debiasing, β_W = 1.5 has no covariance at all. β_W = 2.3, b = 4 has covariance only in shells 0–1, and the sum (0.56 → 0.58, L = 6 → 8) is volume-stable. At b = 6 it is zero.
  - This is consistent with Prop 168. Next: a β_W depth scan and a random-V stress test.
- 2026-11-07: **B quantified under flat ρ (forest/A_GAUSSIAN_FIBRE_4D.md §8.1).**
  - Π_{j≤k} C_B ≈ n_k^α with α = log₂(1/(1−ρ²)) ≈ 1.7 (range 1.4–1.9). So B degrades to a power law rather than failing.
  - New target (B′): does the (H2) chain absorb C_B growth n_k^α with α < 2?
  - Fallback: a smeared block map.
  - The R_∠ job 1698522 is queued (per-user CPU limit).
- 2026-11-07: **(B′) answered (forest/A_GAUSSIAN_FIBRE_4D.md §8.2).**
  - Cor bpuptuning needs Γ = ΠC_B bounded uniformly in k, so the n_k^α loss of §8.1 empties the gap bound and (B′) fails.
  - This is forced: the Gaussian model is free Maxwell (gapless), so a bounded Γ there would prove a false gap.
  - The Gaussian model therefore tests (F), (X) and (D) per scale, but cannot test the ρ_j decay. That decay must come from non-abelian or confining input.
  - B matters only for the gap: by the D audit, (E) does not use MIX as a premise.
- 2026-11-07: **C run 3 submitted** (ym-pathcov-c3-depth, job 1701862). Same debiased estimator at b = 4, L = 6, 8: β_W ∈ {3.0, 4.0} with V = id, plus Haar-random V at β_W = 2.3. Decision: an equal significant shell sum at L = 6 and 8 means Prop 168 is volume-stable through β_W = 4. The R_∠ job 1698522 is still queued.
- 2026-11-08: **R_∠ job 1698522 failed its self-test; resubmitted as job 1703021.**
  - The Pythagoras check Var(u) − Var(P_𝓕u) = u_inᵀK_in⁺u_in came out at 9e-4 instead of ~1e-12.
  - Cause: coarse path currents keep their torus-harmonic part (constant per direction). The Green function drops that part, but K_in⁺ acting on u_in does not.
  - Fix: remove the harmonic part from u before conditioning. The self-test now asserts the identity to 1e-8.
  - The same inconsistency is in gauss_rho's ρ₁, so the published ρ₁ values carry a bias of about this size. That is below the ±0.02 offset spread, so the §8 conclusions are unchanged. The new self-test prints both values at b = 3, L = 4, n' = 3, to size the bias exactly.
  - C run 3 (job 1701862) is running.
- 2026-11-08: **R_∠ at L = 4 (forest/A_GAUSSIAN_FIBRE_4D.md §9).**
  - R_∠ = 4.08 at (b, L, n') = (3, 4, 3) and 3.84 at (4, 4, 4). Face overlap 0.155, edge 0.07; the d_∞ = 2 shell sits at a 2–5e-3 floor and sums to about 0.7.
  - The fix to the harmonic mode shifts ρ₁ by only 3e-4, so §8 stands.
  - The three L = 6 configurations crashed (gesdd did not converge) and are rerunning with gesvd as job 1703813. They decide whether R_∠ is volume-stable or diverges with L, which is the question of whether the decay exponent exceeds 4.
- 2026-11-08: **Direction B redirected.** The Gaussian route is closed, because (B′) fails and the failure is forced. B now targets the non-Gaussian source of ρ_j decay: strong-coupling smallness at the coarse end, a finite-head/summable-tail form of Cor bpuptuning, and confinement input stated as a hypothesis on ρ_j. A and C will be revisited when the R_∠ volume test and C run 3 finish.
- 2026-11-08: **B step 2 corrected; candidate UV no-go.** A finite head is wrong, because the near-Gaussian scales are the UV ones and there are ~k of them (A_GAUSSIAN_FIBRE_4D §8.3). Submitted the first-chaos lower bound C_B^lin (b = 2, n' = 2n; (L,n) = (6,2),(8,2),(6,3),(8,3)). The test functions are linear in the coarse variables, so Var(f|c) = 0 and the bound holds for every C_A. If C_B^lin > 1 and flat, Step 1 of the no-go holds without the finite-size assumption.
- 2026-11-08: **The sufficient input is stated precisely** (A_GAUSSIAN_FIBRE_4D §8.4). The framework needs exactly (U): uniform BP(ℓ/a, ϖ) at a fixed physical scale. The tower is one route to (U), and §8.3 suggests it is blocked in the UV. Next: does a gap imply (U)? Test this in the massive Gaussian model. R_∠ (3,6,3) is at 71 of 125 z-classes; C run 3 and C_B^lin (job 1709673) are still running.
- 2026-11-08: **Gap ⇒ (U)? test submitted** (§8.4 next step 1). This is the free massive abelian lattice field, first chaos, in infinite volume via Fourier symbols. It computes ϖ_n for BP(n, ϖ) at lattice mass mℓ/n, for mℓ ∈ {0.5, 1, 2, 4} and n ≤ 8. If ϖ_n is flat in n, a gap implies (U) in the Gaussian model.
- 2026-11-08: **R_∠ volume test done** (§9.1). (3,6,3) gives 4.81 against 4.08 at L = 4. The far-overlap floor scales like 1/V, so it looks like a global-mode O(1) term; (D) is not refuted. Next for A: project out the global modes, or run L = 8. **Massive Gaussian, first run** (§8.4): ϖ_n decays slowly (about n^{-0.25}), but this is driven by the k = 0 longitudinal Proca mode, so the test is inconclusive. A transverse-only rerun up to n = 10 is submitted. C run 3 and C_B^lin are still running.

- 2026-11-08: **Results in.** (1) C run 3: Prop 168 is volume-stable through β_W = 4 (CSbound_sig 13.96–14.05 at β_W = 3 and 24.6–25.0 at β_W = 4, for L = 6, 8). Haar V gives ≈0 (H1_PATHCOV run 3). (2) C_B^lin = 0.658 (n = 2) and 0.724 (n = 3). It is volume-stable but below 1, so it is inconclusive for §8.3 step 1. (3) The transverse massive Gaussian ϖ_n still decays (mℓ = 1: .0385 → .0306 over n = 2..8). So (U) looks strictly stronger than a gap even for the free field, and "gap ⇒ (U)" is doubtful (A_GAUSSIAN_FIBRE_4D §10). Next: analytic small-k asymptotics of ϖ_n to decide decay vs. log approach; C_B^lin at larger n.
- 2026-11-08: **Small-k analysis of the (U) test** (A_GAUSSIAN_FIBRE_4D §10). At k → 0, ϖ_n = (mℓ)² q(n)/n⁶, and continuum scaling suggests a positive limit. On that reading the n ≤ 8 decay is an O(1/n) lattice correction, and "gap ⇒ (U)" may survive for the free field. This revises the previous entry. A sparse exact run of q(n) up to n = 24 is submitted to decide.
- 2026-11-08: **Gap ⇒ (U) holds in the free massive field (first chaos).** The sparse exact k → 0 computation to n = 24 shows ϖ_n → ≈0.020 at mℓ = 1 (fit c₀ + c₁/n, stable to 0.020–0.021) and ≈0.074 at mℓ = 2. The n ≤ 8 decay was an O(1/n) lattice correction (A_GAUSSIAN_FIBRE_4D §10). So the precise sufficient input (U) is not stronger than a gap in the free theory. Next: (i) the analytic continuum constant c₀ (curl variational problem on the unit cube) and a proof of convergence; (ii) higher chaos and non-linear observables; (iii) C_B^lin at larger n.
- 2026-11-08: **Continuum constant found.** ϖ_∞(k→0) = (mℓ)²⟨1,(−Δ_D+(mℓ)²)⁻¹1⟩ on the unit 3-cube: 0.0196 at mℓ = 1 and 0.0719 at mℓ = 2, matching the lattice extrapolation. The trial-field version gives a rigorous lower bound that is uniform in n (§10). Next: prove that the infimum over k is at k → 0; reduce higher chaos to the first by second quantization; C_B^lin at larger n.
- 2026-11-08: **Higher chaos is reduced to the first chaos** by the Amit Gaussian Gibbs-sampler theorem (block resampling = Γ(P_Λ)) (§10). Free-field "gap ⇒ (U)" now rests only on (a) the k-infimum being at k → 0 and (b) the infinite-volume extension. C_B^lin at n = 4 (L = 8, 9) is submitted.
- 2026-11-08: **C_B^lin(n = 4, L = 8) = 0.770.** The sequence 0.658 / 0.724 / 0.770 extrapolates to 0.86–0.91, which is below 1 but drifting up, so it is inconclusive for §8.3 step 1. L = 9 is still running. Remaining for the free field: prove the k-infimum is at k → 0, and do the infinite-volume Amit extension. Then the main open question returns to Yang–Mills: a uniform two-scale comparison E_{ℓ/a} ≳ E_{ℓ₀/a} (§8.4) as the route to (U).
- 2026-11-08: C_B^lin(n = 4, L = 9) = 0.7685, so the result is volume-stable to 0.2%. The numerical items in the plan are now all done. What remains is proof work: (a) k-infimum at k → 0 for the free massive field; (b) Amit reduction in infinite volume; (c) the Yang–Mills two-scale comparison for (U).

## Next phase (from 2026-11-08, branch research/next-steps-3)

Where things stand: (U) ⇒ gap holds in general (Thm `avgtransfer`). Gap ⇒ (U) holds in the free massive field, modulo steps 1–2 below. So, in the free theory, (U) and a mass gap are equivalent inputs. The plan, in order:

1. **Prove the k-infimum is at k → 0** (free field). First a fine radial numerical scan at |k| = t/n along 5 directions for n = 8, 12, 16. Then a monotonicity proof.
2. **Amit reduction in infinite volume.** Write out the finite-torus to L → ∞ argument that reduces all observables to linear ones.
3. **Two-scale comparison in the free field.** Compute E_{ℓ/a} against E_{ℓ₀/a} exactly, using the `gauss_k0` machinery, and check whether the constant is uniform in a. This shapes the Yang–Mills form of (U).
4. **(U) with interactions.** Measure ϖ_n at fixed physical ℓ in an interacting gapped model, compact U(1) in 3D or SU(2) in 2D/3D, using the path-covariance Monte Carlo setup. Flat in a supports gap ⇒ (U) beyond Gaussians.
5. Deprioritized: C_B^lin at larger n.

- 2026-11-08: Step 1 numerical scan submitted (ym-gaussmass-kscan).
- 2026-11-08: **Step 2 closed** (§10.1). A two-line positivity lemma, avg P^{⊗m} ≤ (avg P) ⊗ 1, reduces BP on all gauge-invariant observables to the first chaos, in any volume, with no appeal to Amit. Free-field gap ⇒ (U) now rests only on step 1 (k-infimum at k → 0); its numerical scan is submitted.

- 2026-11-08: Next-phase step 1 numerically confirmed. The k-scan over 35 groups (n ≤ 16, mℓ ∈ {1,4}, 5 directions) is monotone in |k| with the minimum at k → 0; see A_GAUSSIAN_FIBRE_4D §10.2. A proof of the monotonicity is open. Step 3 (free-field two-scale comparison, cubes of side n and n/2 at fixed mℓ, n ≤ 16) has been submitted.
- 2026-11-08: Next-phase step 3 done for the free field (A_GAUSSIAN_FIBRE_4D §10.3). The two-scale constant C(n) for ℓ/ℓ0 = 2 is 1.38, 1.07, 1.01, 0.99 at n = 4–16 and converges to ≈ 0.97. The infimum sits at the zone boundary (a UV effect); the IR ratio is stable at ≈ c(mℓ)/c(mℓ/2). Remaining: step 4, (U) in an interacting model (compact U(1) in 3D first), and a proof of the step-1 monotonicity.
- 2026-11-08: Step 4 started with 3D compact U(1) (monopole-gapped). `strong-coupling/forest/experiments/u1bp/u1bp.c` estimates ϖ_n directly from the definition: E Var(f | outside cube) / (n³ Var(f)/V), with nested conditional heat-bath resampling of non-adjacent cubes. Observables are sin θ₁₂ at k = 0 and at the smallest k, plus plaquette energies. The mass m(β) comes from slice correlators. The grid is β ∈ {1.6, 1.9, 2.2}, n ∈ {2,3,4,6,8}, L = 32, plus an n = L selftest (should give ϖ = 1) and an inner-thinning check. Test: do the ϖ curves collapse in m(β)·n with no downward drift in β?
- 2026-11-08: **Step 4, compact U(1)₃ result (A_GAUSSIAN_FIBRE_4D §10.4).** ϖ_n at fixed m·ℓ does not collapse. It falls about 0.6× per halving of m·a (0.67, 0.39, 0.24 at mℓ ≈ 2.35; about 3σ per step), roughly ϖ ∝ (ma)^0.75. So (U) fails along this line although the theory is gapped. Caveat: U(1)₃ has two scales (m ≪ e² as β → ∞), so this refutes gap ⇒ (U) only for theories with a scale hierarchy. Next: **3D SU(2)** (one scale, m/g² fixed), which is the decisive interacting test. Reuse u1bp.c with SU(2) heat-bath (Kennedy–Pendleton), the observable Re tr of plaquettes at small k, and the 0++ mass from slice correlators.

**2026-11-08 — step 4b (3D SU(2)) submitted.** Same conditional cube-resampling estimator as the U(1) run, now with quaternion links
(Kennedy–Pendleton heat-bath + overrelaxation). Observables: w×w Wilson loops, w = 1, 2, 3, at k = 0 (all planes) and at
k = 2π/L along x1 and x3; cubes spaced n+4 and observable box margin 3 so no loop touches two cubes. The only scale is g², so
ℓg² = 4n/β labels the continuum line: β ∈ {5, 7.5, 10} with n chosen to hit ℓg² ∈ {1.6, 2.4, 3.2, 4.8}, L = 32, 1200
configurations each, plus an n = L selftest (ϖ = 1) and a thinning check. Decision: collapse vs ℓg² with no drift in β
supports gap ⇒ (U) in a single-scale gauge theory; a U(1)-like ≈0.6× drop per halving of a means (U) is strictly stronger.
- 2026-11-09: **Step 4b, SU(2)₃ result (A_GAUSSIAN_FIBRE_4D §10.5).** Selftest and thinning pass. ϖ stays O(1) (1.1–1.7) on the whole grid. At fixed ℓg², halving a multiplies ϖ by 0.86–0.90, much weaker than U(1)₃'s 0.6, but coherent across observables (33/36 ratios < 1, each ≈ 0.6σ). Constant + O(a) and a slow power law a^{≈0.2} cannot be separated yet. So this is no refutation of gap ⇒ (U), and not yet a confirmation. Next (after the PR): 4–5× statistics plus β ≈ 15.
- 2026-11-09: **k-infimum, uniform proof (A_GAUSSIAN_FIBRE_4D §10.2).** Proved inf_k ϖ_k ≥ ϖ_n(k→0)/5 for the transverse free massive symbol, uniformly in n and μ: a phase-modulated k = 0 maximiser as trial field, plus an exact symbol identity for ½[K̂(p+k)+K̂(p−k)]. With the trial-field bound this gives (U) for the first chaos with constant c(mℓ)/5. Best constant numerically ≈ 1.06; strict monotonicity remains numerical.
- 2026-11-09: **SU(2)₃ high-statistics rerun submitted.** 5000 configurations per point (≈4×), β ∈ {5, 7.5, 10, 15}, β = 15 on L = 48 with n ∈ {6, 9, 12, 18}. Decision: fit c₀ + c₁a against c·a^p at each ℓg². Launcher: experiments/su2bp/run_hi.sh.
- 2026-11-09: **SU(2)₃ high-statistics result (A_GAUSSIAN_FIBRE_4D §10.6).** The drift persists (β15/β5 = 0.83 on average, 36/36 < 1). The c₀ + c₁a fit gives c₀ ≈ 1.0 ± 0.12 > 0 at every ℓg², but a power law a^{0.14–0.20} fits equally well. This is weak support for (U) under the pre-registered rule, not a decision. Next: β ≈ 20–30 at fixed Lg² with a lower-variance (multilevel) estimator.

## Working queue toward the next PR (from 2026-11-09, branch research/next-steps-3)

Status: 7 commits since PR #289 (6df33b1), all notes in this file and forest/A_GAUSSIAN_FIBRE_4D.md, pushed to the fork, no PR
open. Gap found: the code behind these results (and behind #289) was never committed, because `.gitignore` excludes
`/research/`, where it lives. The PR is ready when every numerical claim since #289 can be reproduced from tracked files.
Work the list in order and tick each item as it lands.

1. [x] **Record the SU(2)₃ result** (done 2026-11-09, §10.5) (job finished, 14/14 lines). Write A_GAUSSIAN_FIBRE_4D §10.5 and a log entry above.
   First read: selftest ϖ ≈ 0.88–1.05 ± 0.2–0.35 (passes); thinning s = 10 vs s = 4 agree; ϖ > 1 everywhere, falls with ℓg²
   (W1_kx1: β = 5: 1.68 → 1.23; β = 10: 1.43 → 1.14 over ℓg² = 1.6 → 4.8). At fixed ℓg² there is a mild downward drift in β,
   within about 1σ, so collapse and a U(1)-like drift cannot be separated yet. Before writing, run su2bp/analyze.py on the
   output and quote its numbers, not this first read.
2. [x] **Track the experiment code.** (done 2026-11-09: all 8 directories, launchers rewritten to plain `python`; cluster request plans left out) Move the code that backs the results since #289, and ideally #289 too, into
   `strong-coupling/forest/experiments/`, starting with `gaussrho/` (gauss_k0, gauss_kscan, gauss_twoscale, gauss_massU, …),
   `u1bp/` and `su2bp/` (.c, analyze.py, plan*.json). Leave the `run*.sh` launchers untracked, because they name the cluster.
   Replace them with one README per experiment: build line, `python` / `cc` invocation, plan file, expected output format.
   Decide whether to include pathcov, linresp, polchinski2d, reduced_dobrushin and vortex_mc (they back earlier sections).
3. [x] **Commit the raw result files** (done: gaussrho, u1bp, su2bp; older pathcov/linresp outputs not recovered) each § cites (small JSON lines, such as the SU(2) output), next to their experiment.
   Strip any paths.
4. [x] **Fix references.** (done) Point notes that cite `research/experiments/...` (e.g. the step-4 entry above) to the new tracked
   paths.
5. [x] **Pre-PR checks.** (passed 2026-11-09) Grep the full `upstream/main...HEAD` diff for forbidden strings and for `/home/` and `/n/` paths.
   Confirm no `__pycache__`, PDFs or binaries are included. Make sure it merges cleanly into upstream/main.
6. [x] **Open the PR** (#290, 2026-11-09) to creelie/4Y-M `main`. Summary: step 2 closed; free-field k-infimum and two-scale results;
   U(1)₃ drift; SU(2)₃ first result; reproducible code.

After the PR (next research items, not blocking it): a higher-statistics SU(2)₃ rerun (4–5× nconf) to decide collapse vs
drift at fixed ℓg²; a proof of the step-1 monotonicity in k.

- 2026-11-09 — Submitted the fixed-box SU(2)₃ pass (L·g² = 12.8 for every β; β = 5, 7.5, 20, 25 added to the existing β = 10, 15). This removes the box confound of the β ≤ 15 pass. Decision rule: β25/β10 ≥ 0.95 at equal ℓg² → plateau (supports (U)); ≤ 0.85 → continued drift. Launcher: `forest/experiments/su2bp/run_fixbox.sh`. The multilevel estimator is deferred; this pass uses 5 inner resamples instead of 3.

- 2026-11-09 — **Bug found while diagnosing the "errors stuck at 0.09":** the su2bp/u1bp jackknife over-stated errors by √20. Fixed, data files corrected, §10.7 erratum written. True per-point error ≈ 0.02. With it: the SU(2)₃ drift is significant (β15/β5 ≈ 0.82, 7–12σ), and c₀ + c₁a fits better than c·aᵖ (χ² 1.4 vs 8.9 / 7 dof), c₀ ≈ 1.0 ± 0.03. The multilevel estimator is dropped (not needed: numerator noise 0.1–0.2%, denominator 1–2.5%, no autocorrelation). The fixed-box run (job running) decides; its analysis uses the fixed formula (the in-run analyze.py is the old one, so rerun analyze on its .dat files).

- 2026-11-09 — Fixed-box run, interim (β = 20/25 partly done): no finite-box effect (β = 5 at L = 16 = at L = 32). c₀ + c₁a over β = 5–25 fits (χ² 7.9/15, c₀ ≈ 0.98–1.09 ± 0.02); c·aᵖ disfavoured (χ² 29.9/15). The pre-registered β25/β10 rule lands in the gap (0.89–0.92), as the linear model predicts. A_GAUSSIAN_FIBRE_4D §10.8. Next: final numbers when the job ends, then merge PR #290.

- 2026-11-09 — Fixed-box run final (§10.8): c₀ + c₁a χ² 9.4/15, c₀ ≈ 0.98–1.08 ± 0.016; c·aᵖ χ² 31.7/15 (disfavoured, p-value 0.007). Pre-registered rule inconclusive (0.89–0.92). SU(2)₃ evidence for (U): favoured, not proven. PR #290 complete and ready to merge. Next directions (new PR): 4D SU(2) analogue of §10.8 at modest β; sharpen the free-field factor 5 to 1.

## 2026-11-09 — branch research/next-steps-4 (after PR #290 merged)

Started direction (a): 4D SU(2) analogue of §10.8. New `forest/experiments/su2bp4d/` (su2bp4d.c, the 3D
estimator generalised to D = 4; pure-Python analyze4d.py; run.sh). Plan: fixed box L·√σ ≈ 2.1–2.2 at
β = 2.4, 2.5, 2.6 (L = 8, 12, 16), cubes at n/L = 1/4, 3/8, 1/2, plus an n = L selftest (ϖ must be 1).
Short local checks: plaquette 0.61 at β = 2.3 (matches the known ≈0.60); selftest consistent with 1.
