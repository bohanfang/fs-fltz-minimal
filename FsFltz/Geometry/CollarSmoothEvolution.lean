import FsFltz.Geometry.CollarSmoothDependence
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth dependence of actual collar evolutions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189,
and `sec:lean`, lines 788–814. The smoothness convention is `C∞`
with extension across parameter endpoints (lines 119–122).

The pointwise linearization on continuous paths is itself a bounded
linear operator of the derivative path. Induction on the differentiability
order therefore upgrades the proved strict derivative of superposition
to every finite order, and hence to `C∞`. Applied to the literal Picard
residual, this supplies higher-order smoothness through the native
implicit-function theorem, without assuming regularity of a flow.

In charts, finite-order Picard regularity transfers to native local
integral curves. Uniqueness identifies these with the actual evolution;
connected real time propagates each finite regularity order. To obtain
joint time-and-point regularity, adjoin a constant real parameter `r`
and use the smooth field `(0, r • v)`. Its time-one map is precisely
`(r, x) ↦ (r, φ r x)`. Time suspension gives joint dependence on both
times for a nonautonomous field. Applied to the constructed collar
velocity, these results produce an actual smooth correction of a compact
presentation, with the canonical collar equation needed for completion
gluing. Completions and the original compact presentation are supplied;
their existence and the geometric target remain pending.
-/

noncomputable section
open scoped ContDiff Classical NNReal
open Set Filter Topology Metric Function

namespace FsFltz.Geometry.CollarFlow

section Superposition

variable {X F G : Type} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative-path-to-operator map is bounded linear. Its norm
bound makes higher derivatives of superposition continuous in the path norm. -/
def pathLinearizationCLM : C(X, F →L[ℝ] G) →L[ℝ] (C(X, F) →L[ℝ] C(X, G)) :=
  LinearMap.mkContinuous
    { toFun := pathLinearization (X := X) (F := F) (G := G)
      map_add' := by intro D E; ext β t; rfl
      map_smul' := by intro c D; ext β t; simp }
    1 (fun D => by simpa using norm_pathLinearization_le D)

@[simp] theorem pathLinearizationCLM_apply (D : C(X, F →L[ℝ] G)) :
    pathLinearizationCLM D = pathLinearization D := rfl

variable [ProperSpace F]

/-- Smooth superposition preserves every finite differentiability order.
The induction uses the actual pointwise derivative already proved for the
path norm, rather than an assumed differentiable solution family. -/
theorem contDiff_pathComposition_nat {n : ℕ} {f : F → G}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun β : C(X, F) => (⟨f, hf.continuous⟩ : C(F, G)).comp β) := by
  induction n generalizing G with
  | zero =>
      apply contDiff_zero.mpr
      exact ContinuousMap.continuous_comp'.comp (continuous_id.prodMk continuous_const)
  | succ n ih =>
      change ContDiff ℝ ((n : ℕ∞ω) + 1) _
      apply contDiff_succ_iff_hasFDerivAt.mpr
      let D : C(X, F) → C(X, F →L[ℝ] G) := fun α =>
        (⟨fderiv ℝ f, (hf.of_le (by simp : (1 : ℕ∞ω) ≤ (n + 1 : ℕ))).continuous_fderiv
          (by simp)⟩ : C(F, F →L[ℝ] G)).comp α
      refine ⟨fun α => pathLinearizationCLM (D α), ?_, ?_⟩
      · exact pathLinearizationCLM.contDiff.comp (ih (hf.fderiv_right (by simp)))
      · intro α
        exact (hasStrictFDerivAt_pathComposition (hf.of_le (by simp)) α).hasFDerivAt

/-- Smooth fields induce smooth superposition on continuous paths over a
compact parameter space. Here `∞` means `C∞`, not analytic regularity. -/
theorem contDiff_pathComposition {f : F → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun β : C(X, F) => (⟨f, hf.continuous⟩ : C(F, G)).comp β) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_pathComposition_nat (hf.of_le (by simp))

end Superposition

section Implicit

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [ProperSpace F] {a b : ℝ} {t₀ : Icc a b}

/-- The literal Picard equation upgrades a continuous solution family to
the smoothness order of the field. The path derivative is a proved Neumann
perturbation of the identity, so implicit solvability is not an input. -/
theorem contDiffAt_of_picard_equation_nat {n : ℕ} (hn : 0 < n)
    {f : F → F} (hf : ContDiff ℝ n f)
    (β : F → C(Icc a b, F)) (x₀ : F) (hβ : ContinuousAt β x₀)
    (hpicard : ∀ᶠ x in 𝓝 x₀,
      β x = constantPath x + pathIntegral t₀ ((⟨f, hf.continuous⟩ : C(F, F)).comp (β x)))
    (hsmall : ‖(pathIntegral t₀).comp (pathLinearization
      ((⟨fderiv ℝ f, (hf.of_le (show (1 : ℕ∞ω) ≤ n by
        exact_mod_cast Nat.succ_le_iff.mpr hn)).continuous_fderiv (by simp)⟩ :
        C(F, F →L[ℝ] F)).comp (β x₀)))‖ < 1) :
    ContDiffAt ℝ n β x₀ := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_le_iff.mpr hn)
  let V := pathIntegral (F := F) t₀
  let C := constantPath (X := Icc a b) (F := F)
  let N : C(Icc a b, F) → C(Icc a b, F) :=
    fun α => (⟨f, hf.continuous⟩ : C(F, F)).comp α
  let A := V.comp (pathLinearization
    ((⟨fderiv ℝ f, hf₁.continuous_fderiv (by simp)⟩ : C(F, F →L[ℝ] F)).comp (β x₀)))
  let R : F × C(Icc a b, F) → C(Icc a b, F) := fun p => p.2 - C p.1 - V (N p.2)
  let R' : F × C(Icc a b, F) →L[ℝ] C(Icc a b, F) :=
    ContinuousLinearMap.snd ℝ _ _ - C.comp (ContinuousLinearMap.fst ℝ _ _) -
      A.comp (ContinuousLinearMap.snd ℝ _ _)
  have hR : HasStrictFDerivAt R R' (x₀, β x₀) :=
    (hasStrictFDerivAt_snd.sub (C.hasStrictFDerivAt.comp _ hasStrictFDerivAt_fst)).sub
      (V.hasStrictFDerivAt.comp _
        ((hasStrictFDerivAt_pathComposition hf₁ (β x₀)).comp (x₀, β x₀)
          (f := Prod.snd) hasStrictFDerivAt_snd))
  have hpartial : R'.comp (ContinuousLinearMap.inr ℝ F C(Icc a b, F)) = 1 - A := by
    ext α t
    simp [R']
  have hA : ‖A‖ < 1 := hsmall
  obtain ⟨u, hu⟩ := IsUnit.one_sub_of_norm_lt_one (x := A) hA
  have hinv : (fderiv ℝ R (x₀, β x₀) ∘L ContinuousLinearMap.inr ℝ F C(Icc a b, F)).IsInvertible := by
    rw [hR.hasFDerivAt.fderiv, hpartial]
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ _ u, hu⟩
  have hcR : ContDiffAt ℝ n R (x₀, β x₀) :=
    ((contDiff_snd.sub (C.contDiff.comp contDiff_fst)).sub
      (V.contDiff.comp ((contDiff_pathComposition_nat hf).comp contDiff_snd))).contDiffAt
  have hn' : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn.ne'
  have hzero : R (x₀, β x₀) = 0 := by
    dsimp [R, C, V, N]
    nth_rw 1 [hpicard.self_of_nhds]
    abel
  have heq := (continuousAt_id.prodMk hβ).eventually
    (hcR.eventually_apply_eq_iff_implicitFunction hn' hinv)
  apply (hcR.contDiffAt_implicitFunction hn' hinv).congr_of_eventuallyEq
  filter_upwards [heq, hpicard] with x hx hpx
  symm
  apply hx.mp
  rw [hzero]
  dsimp [R, C, V, N]
  nth_rw 1 [hpx]
  abel

end Implicit

section LocalDependence

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [ProperSpace F]

/-- Actual local integral curves of a `Cⁿ` Euclidean field have `Cⁿ`
dependence on their initial point, in the continuous-path norm.
The common lifetime, curves, and regularity are all produced from the
field; no differentiable solution or flow is supplied as input. -/
theorem exists_contDiff_local_picard_family_nat {f : F → F}
    (n : ℕ) (hn : 0 < n) (hf : ContDiff ℝ n f) (x₀ : F) :
    ∃ (ε : ℝ) (hε : 0 < ε) (r : ℝ), 0 < r ∧
      ∃ β : F → C(Icc (-ε) ε, F), ContinuousOn β (ball x₀ r) ∧
        ∀ x ∈ ball x₀ r,
          β x ⟨0, by constructor <;> linarith⟩ = x ∧
          ContDiffAt ℝ n β x ∧
          ∀ (t : ℝ) (ht : t ∈ Ioo (-ε) ε),
            HasDerivAt (fun u => β x (projIcc (-ε) ε (by linarith) u))
              (f (β x ⟨t, Ioo_subset_Icc_self ht⟩)) t := by
  obtain ⟨ε, hε, R, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one (hf.of_le (show (1 : ℕ∞ω) ≤ n by exact_mod_cast Nat.succ_le_iff.mpr hn)).contDiffAt
  obtain ⟨M₀, hM₀⟩ := ((isCompact_closedBall x₀ (R : ℝ)).image
    ((hf.of_le (show (1 : ℕ∞ω) ≤ n by exact_mod_cast Nat.succ_le_iff.mpr hn)).continuous_fderiv (by simp))).isBounded.exists_norm_le
  let M : ℝ := max M₀ 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound : ∀ y ∈ closedBall x₀ (R : ℝ), ‖fderiv ℝ f y‖ ≤ M := by
    intro y hy
    exact (hM₀ _ ⟨y, hy, rfl⟩).trans (by dsimp [M]; linarith [le_max_left M₀ 0])
  let δ : ℝ := min ε (1 / (2 * M))
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδM : δ * M < 1 := by
    have h := min_le_right ε (1 / (2 * M))
    have hd : δ ≤ 1 / (2 * M) := h
    have hm := mul_le_mul_of_nonneg_right hd hM.le
    have heq : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    rw [heq] at hm
    linarith
  let t₀ : Icc (-δ) δ := ⟨0, by constructor <;> linarith⟩
  have hpl' : IsPicardLindelof (fun _ => f) t₀ x₀ R r L K :=
    (hpl 0).shrink_time t₀ rfl (by linarith) (by linarith)
  obtain ⟨β, hc, hβ⟩ := exists_continuous_picard_family hf.continuous hpl'
  have hc' := hc.mono (ball_subset_closedBall (x := x₀) (ε := (r : ℝ)))
  refine ⟨δ, hδ, r, NNReal.coe_pos.mpr hr, β, hc', ?_⟩
  intro x hx
  have hx' := ball_subset_closedBall hx
  refine ⟨(hβ x hx').2.1, ?_, ?_⟩
  · apply contDiffAt_of_picard_equation_nat hn hf β x
      (hc'.continuousAt (isOpen_ball.mem_nhds hx))
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hβ y (ball_subset_closedBall hy)).1
    · let D : C(Icc (-δ) δ, F →L[ℝ] F) :=
        (⟨fderiv ℝ f, (hf.of_le (show (1 : ℕ∞ω) ≤ n by exact_mod_cast Nat.succ_le_iff.mpr hn)).continuous_fderiv (by simp)⟩ : C(F, F →L[ℝ] F)).comp (β x)
      have hD : ‖D‖ ≤ M := (ContinuousMap.norm_le _ hM.le).mpr
        (fun t => hbound _ ((hβ x hx').2.2.1 t))
      have hV : ‖pathIntegral (F := F) t₀‖ ≤ δ := by
        simpa only [t₀, sub_zero, zero_sub, neg_neg, max_self] using
          norm_pathIntegral_le (F := F) t₀
      exact lt_of_le_of_lt ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hV ((norm_pathLinearization_le D).trans hD)
          (norm_nonneg _) hδ.le)) hδM
  · intro t ht
    exact ((hβ x hx').2.2.2 ⟨t, Ioo_subset_Icc_self ht⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

end LocalDependence

section LocalField

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [ProperSpace F] [HasContDiffBump F]

omit [CompleteSpace F] [ProperSpace F] in
/-- A finite-order field near a point has a globally equally regular representative agreeing
on a ball around that point. Smooth cutoffs are used only for localization. -/
theorem exists_contDiff_localRepresentative_nat {f : F → F} {x₀ : F}
    (n : ℕ) (hf : ContDiffAt ℝ n f x₀) :
    ∃ g : F → F, ContDiff ℝ n g ∧ ∃ ρ : ℝ, 0 < ρ ∧ EqOn g f (ball x₀ ρ) := by
  obtain ⟨R, hR, hregular⟩ := Metric.eventually_nhds_iff_ball.mp (hf.eventually (by simp))
  let χ : ContDiffBump x₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let g : F → F := fun x => χ x • f x
  have hg : ContDiff ℝ n g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hx' : x ∈ ball x₀ R := by
        rw [χ.tsupport_eq] at hx
        exact closedBall_subset_ball (by dsimp [χ]; linarith) hx
      exact χ.contDiffAt.smul (hregular x hx')
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [g, hy, Pi.zero_apply, zero_smul]
  refine ⟨g, hg, R / 4, by positivity, ?_⟩
  intro x hx
  simp only [g, χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

/-- Chart-local fields have actual common local integral curves with
finite-order smooth initial-point dependence. The curves can be required to
remain in any specified neighborhood. All regularity comes from the
constructed Picard family and the smooth Picard residual. -/
theorem exists_neighborhood_contDiff_local_solution_nat {f : F → F} {x₀ : F}
    (n : ℕ) (hn : 0 < n) (hf : ContDiffAt ℝ n f x₀) {S : Set F} (hS : S ∈ 𝓝 x₀) :
    ∃ U : Set F, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ γ : F × ℝ → F, ContinuousOn γ (U ×ˢ univ) ∧
        (∀ x ∈ U, γ (x, 0) = x) ∧
        (∀ x ∈ U, ∀ t ∈ Ioo (-ε) ε, γ (x, t) ∈ S ∧
          HasDerivAt (fun u => γ (x, u)) (f (γ (x, t))) t) ∧
        ∀ x ∈ U, ∀ t : ℝ, ContDiffAt ℝ n (fun y => γ (y, t)) x := by
  obtain ⟨g, hg, ρ, hρ, heq⟩ := exists_contDiff_localRepresentative_nat n hf
  obtain ⟨ε, hε, r, hr, β, hc, hβ⟩ := exists_contDiff_local_picard_family_nat n hn hg x₀
  let π : ℝ → Icc (-ε) ε := projIcc (-ε) ε (by linarith)
  let γ : F × ℝ → F := fun p => β p.1 (π p.2)
  have hcont : ContinuousOn γ (ball x₀ r ×ˢ univ) :=
    continuous_eval.comp_continuousOn
      ((hc.comp continuousOn_fst (fun _ hp => hp.1)).prodMk
        (((show Continuous π from continuous_projIcc).comp continuous_snd).continuousOn))
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hπ₀ : π 0 = ⟨0, by constructor <;> linarith⟩ := projIcc_of_mem _ _
  have hγ₀ : γ (x₀, 0) = x₀ := by
    simpa only [γ, hπ₀] using (hβ x₀ hx₀).1
  have hn : γ ⁻¹' (S ∩ ball x₀ ρ) ∈ 𝓝 (x₀, (0 : ℝ)) :=
    (hcont.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hx₀, mem_univ _⟩)).preimage_mem_nhds
      (by rw [hγ₀]; exact inter_mem hS (ball_mem_nhds _ hρ))
  obtain ⟨P, hP, T, hT, hPT⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨σ, hσ, hσsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hP (ball_mem_nhds _ hr))
  obtain ⟨τ, hτ, hτsub⟩ := Metric.mem_nhds_iff.mp hT
  let δ : ℝ := min ε τ
  have hδ : 0 < δ := lt_min hε hτ
  have htime {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : t ∈ ball 0 τ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    have hdτ : δ ≤ τ := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨ball x₀ σ, isOpen_ball, mem_ball_self hσ, δ, hδ, γ,
    hcont.mono (prod_mono (fun _ hx => (hσsub hx).2) Subset.rfl), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [γ, hπ₀] using (hβ x (hσsub hx).2).1
  · intro x hx t ht
    have hmem : γ (x, t) ∈ S ∩ ball x₀ ρ := hPT ⟨(hσsub hx).1, hτsub (htime ht)⟩
    have htε : t ∈ Ioo (-ε) ε :=
      Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _) ht
    refine ⟨hmem.1, ?_⟩
    have hd := (hβ x (hσsub hx).2).2.2 t htε
    have hproj : π t = ⟨t, Ioo_subset_Icc_self htε⟩ := projIcc_of_mem _ _
    change HasDerivAt (fun u => γ (x, u)) (g (β x ⟨t, Ioo_subset_Icc_self htε⟩)) t at hd
    rw [← hproj] at hd
    exact hd.congr_deriv (heq hmem.2)
  · intro x hx t
    exact (ContinuousMap.evalCLM ℝ (π t)).contDiff.contDiffAt.comp x
      (hβ x (hσsub hx).2).2.1

end LocalField

section ManifoldLocal

open scoped Manifold
variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [ProperSpace F] [HasContDiffBump F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

set_option backward.isDefEq.respectTransparency false in
/-- A native manifold field has actual common local integral curves with
finite-order smooth dependence on their initial points. The chart solutions
are constructed from the field, and their containment in the chart target
is proved before transferring either the ODE or the initial-point regularity. -/
theorem exists_neighborhood_contMDiff_local_integralCurve_nat (n : ℕ) (hn : 0 < n)
    {v : (x : Q) → TangentSpace I x} {x₀ : Q}
    (hv : ContMDiffAt I ((I).tangent) n
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)) x₀) :
    ∃ U : Set Q, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ β : Q × ℝ → Q, ContinuousOn β (U ×ˢ Ioo (-ε) ε) ∧
        ∀ x ∈ U, β (x, 0) = x ∧
          IsMIntegralCurveOn (fun t => β (x, t)) v (Ioo (-ε) ε) ∧
          ∀ t ∈ Ioo (-ε) ε, ContMDiffAt I I n (fun y => β (y, t)) x := by
  let e := extChartAt I x₀
  let f : F → F := fun y =>
    tangentCoordChange I (e.symm y) x₀ (e.symm y) (v (e.symm y))
  have hcf : ContDiffAt ℝ n f (e x₀) := by
    rw [contMDiffAt_iff] at hv
    exact (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨A, hA, hx₀, ε, hε, α, hαcont, hα₀, hα, hαdiff⟩ :=
    exists_neighborhood_contDiff_local_solution_nat n hn hcf (extChartAt_target_mem_nhds x₀)
  let U : Set Q := e.source ∩ e ⁻¹' A
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) hA
  have hxU : x₀ ∈ U := ⟨mem_extChartAt_source x₀, hx₀⟩
  let β : Q × ℝ → Q := fun p => e.symm (α (e p.1, p.2))
  have hcont : ContinuousOn (fun p : Q × ℝ => α (e p.1, p.2)) (U ×ˢ Ioo (-ε) ε) :=
    hαcont.comp (((continuousOn_extChartAt x₀).comp continuousOn_fst
      (fun _ hp => hp.1.1)).prodMk continuousOn_snd) (fun _ hp => ⟨hp.1.2, mem_univ _⟩)
  refine ⟨U, hUopen, hxU, ε, hε, β,
    (continuousOn_extChartAt_symm x₀).comp hcont (fun p hp => (hα _ hp.1.2 _ hp.2).1), ?_⟩
  intro x hx
  refine ⟨by change e.symm (α (e x, 0)) = x; rw [hα₀ _ hx.2, e.left_inv hx.1], ?_, ?_⟩
  · intro t ht
    let xₜ : Q := e.symm (α (e x, t))
    have htarget : α (e x, t) ∈ e.target := (hα _ hx.2 _ ht).1
    have hsrc : xₜ ∈ e.source := e.map_target htarget
    have hself := mem_extChartAt_source (I := I) xₜ
    have hd := (hα _ hx.2 _ ht).2
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' htarget).comp
        (f := fun u => α (e x, u)) hd.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ (fun u => α (e x, u))) (v xₜ) t
    have he : f (α (e x, t)) = tangentCoordChange I xₜ x₀ xₜ (v xₜ) := rfl
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hself,
      ← tangentCoordChange_comp (x := x₀) ⟨⟨hself, hsrc⟩, hself⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ (hd.congr_deriv he)
    apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by rw [I.range_eq_univ]; exact univ_mem)
    rw [← e.right_inv htarget]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hsrc, hself⟩
  · intro t ht
    have htarget : α (e x, t) ∈ e.target := (hα _ hx.2 _ ht).1
    have he : ContMDiffAt I 𝓘(ℝ, F) n e x :=
      contMDiffAt_extChartAt' (by simpa only [← extChartAt_source I x₀] using hx.1)
    have ha : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) n (fun y => α (y, t)) (e x) :=
      contMDiffAt_iff_contDiffAt.mpr (hαdiff _ hx.2 t)
    have hi : ContMDiffAt 𝓘(ℝ, F) I n e.symm (α (e x, t)) :=
      (contMDiffWithinAt_extChartAt_symm_target x₀ htarget).contMDiffAt
        (extChartAt_target_mem_nhds' htarget)
    exact (hi.comp (e x) (f := fun y => α (y, t)) ha).comp x (f := e) he

end ManifoldLocal

section ManifoldGlobal

open scoped Manifold
variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [ProperSpace F] [HasContDiffBump F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Every time map of an actual all-real evolution of a smooth field is
`Cⁿ` in the initial point. Local regularity is proved
from Picard solutions; uniqueness and connected real time propagate it
along the entire trajectory. -/
theorem contMDiff_of_isMIntegralCurve_nat (n : ℕ) (hn : 0 < n)
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    (φ : ℝ → Q → Q) (hself : ∀ x, φ 0 x = x)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) v) :
    ∀ t : ℝ, ContMDiff I I n (φ t) := by
  have hv₁ := hv.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hcomp : ∀ s t x, φ s (φ t x) = φ (s + t) x := by
    intro s t x
    exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hφ (φ t x)) ((hφ x).comp_add t)
      (by simp only [comp_apply, zero_add, hself])) s
  have hlocal : ∀ x₀, ∃ U : Set Q, IsOpen U ∧ x₀ ∈ U ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ U, ∀ t ∈ Ioo (-ε) ε,
        ContMDiffAt I I n (φ t) y := by
    intro x₀
    obtain ⟨U, hU, hx₀, ε, hε, β, _, hβ⟩ :=
      exists_neighborhood_contMDiff_local_integralCurve_nat n hn ((hv x₀).of_le (by simp))
    refine ⟨U, hU, hx₀, ε, hε, ?_⟩
    intro y hy t ht
    apply ((hβ y hy).2.2 t ht).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hy] with z hz
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
      hv₁ ((hφ z).isMIntegralCurveOn _) (hβ z hz).2.1
      (by rw [hself, (hβ z hz).1]) ht
  intro t x
  let S : Set ℝ := {u | ContMDiffAt I I n (φ u) x}
  have hnear (u : ℝ) : ∀ᶠ w in 𝓝 u, w ∈ S ↔ u ∈ S := by
    obtain ⟨U, hU, hy, ε, hε, H⟩ := hlocal (φ u x)
    have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    have hleft : ∀ᶠ w in 𝓝 u, w - u ∈ Ioo (-ε) ε :=
      ((continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using isOpen_Ioo.mem_nhds hzero))
    have hright : ∀ᶠ w in 𝓝 u, u - w ∈ Ioo (-ε) ε :=
      ((continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
        (by simpa using isOpen_Ioo.mem_nhds hzero))
    have horbit : ∀ᶠ w in 𝓝 u, φ w x ∈ U :=
      (hφ x).continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
    filter_upwards [hleft, hright, horbit] with w hw₁ hw₂ hw₃
    constructor
    · intro hw
      have he := (H _ hw₃ _ hw₂).comp x (f := φ w) hw
      simpa only [comp_def, hcomp, sub_add_cancel, S, mem_ofPred_eq] using he
    · intro hu
      have he := (H _ hy _ hw₁).comp x (f := φ u) hu
      simpa only [comp_def, hcomp, sub_add_cancel, S, mem_ofPred_eq] using he
  have hSopen : IsOpen S := isOpen_iff_eventually.mpr (fun u hu =>
    (hnear u).mono (fun _ hw => hw.mpr hu))
  have hScompl : IsOpen Sᶜ := isOpen_iff_eventually.mpr (fun u hu =>
    (hnear u).mono (fun _ hw => fun h => hu (hw.mp h)))
  have hS : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
  have hmem : (0 : ℝ) ∈ S := by
    have he : φ 0 = id := funext hself
    change ContMDiffAt I I n (φ 0) x
    rw [he]
    exact contMDiffAt_id
  rcases isClopen_iff.mp hS with he | he
  · simp only [he, notMem_empty] at hmem
  · change t ∈ S
    rw [he]
    exact mem_univ _

/-- All finite orders combine to smooth initial-point dependence of each
time map of the actual evolution. -/
theorem contMDiff_of_isMIntegralCurve
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    (φ : ℝ → Q → Q) (hself : ∀ x, φ 0 x = x)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) v) :
    ∀ t : ℝ, ContMDiff I I ∞ (φ t) := by
  intro t
  apply contMDiff_infty.mpr
  intro n
  by_cases hn : 0 < n
  · exact contMDiff_of_isMIntegralCurve_nat n hn hv φ hself hφ t
  · have hn' : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (contMDiff_of_isMIntegralCurve_nat 1 zero_lt_one hv φ hself hφ t).of_le (by simp)

end ManifoldGlobal

section TimeRescaling

open scoped Manifold
variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- Adjoin a constant real parameter to an autonomous field. -/
def constantParameterLift (v : (x : Q) → TangentSpace I x)
    (p : ℝ × Q) : TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
  (0, v p.2)

omit [I.Boundaryless] in
/-- Time rescaling is a smooth field on parameter times manifold. -/
theorem contMDiff_timeRescaledField
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle I Q))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p : ℝ × Q => (⟨p, p.1 • constantParameterLift v p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) := by
  have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hl : ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p : ℝ × Q => (⟨p, constantParameterLift v p⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) :=
    contMDiff_equivTangentBundleProd_symm.comp
      ((ht.comp contMDiff_fst).prodMk (hv.comp contMDiff_snd))
  exact contMDiff_fst.smul_section hl

variable [CompleteSpace F] [FiniteDimensional ℝ F] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Time rescaling turns the proved smooth fixed-time dependence into
joint smooth time-and-initial-point dependence. The lifted evolution is
defined from the actual integral curves, with its ODE checked directly. -/
theorem contMDiff_joint_of_isMIntegralCurve
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    (φ : ℝ → Q → Q) (hself : ∀ x, φ 0 x = x)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) v) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : ℝ × Q => φ p.1 p.2) := by
  let Ψ : ℝ → (ℝ × Q) → ℝ × Q := fun t p => (p.1, φ (t * p.1) p.2)
  have hΨself : ∀ p, Ψ 0 p = p := by
    intro p
    simp only [Ψ, zero_mul, hself]
  have hΨ : ∀ p, IsMIntegralCurve (fun t => Ψ t p)
      (fun q => q.1 • constantParameterLift v q) := by
    intro p t
    have hd := (hφ p.2).comp_mul p.1 t
    apply ((hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) p.1 t).prodMk hd).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    change ((0 : ℝ), r • (p.1 • v (φ (t * p.1) p.2))) =
      r • (p.1 • ((0 : ℝ), v (φ (t * p.1) p.2)))
    simp
  have hs := contMDiff_of_isMIntegralCurve (contMDiff_timeRescaledField hv) Ψ hΨself hΨ 1
  simpa only [comp_def, Ψ, one_mul] using contMDiff_snd.comp hs

end TimeRescaling

section Nonautonomous

open scoped Manifold
variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]
  [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ, F) ∞ Q] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Actual all-real solutions of a smooth time-dependent field depend
jointly smoothly on initial time, final time, and initial point. Suspension
reduces this to the proved autonomous joint regularity theorem. -/
theorem contMDiff_joint_of_hasMFDerivAt
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    (Φ : ℝ → ℝ → Q → Q) (hself : ∀ s x, Φ s s x = x)
    (hΦ : ∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u => Φ s u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s t x)))) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))) 𝓘(ℝ, F) ∞
      (fun p : ℝ × (ℝ × Q) => Φ p.1 p.2.1 p.2.2) := by
  let Ψ : ℝ → (ℝ × Q) → ℝ × Q := fun t p =>
    (t + p.1, Φ p.1 (t + p.1) p.2)
  have hΨself : ∀ p, Ψ 0 p = p := by
    rintro ⟨s, x⟩
    simp only [Ψ, zero_add, hself]
  have hΨ : ∀ p, IsMIntegralCurve (fun t => Ψ t p) (timeSuspension Z) := by
    intro p
    have hl : IsMIntegralCurve (fun t => (t, Φ p.1 t p.2)) (timeSuspension Z) :=
      fun t => hasMFDerivAt_lift (hΦ p.1 p.2 t)
    exact hl.comp_add p.1
  have hs := contMDiff_joint_of_isMIntegralCurve (contMDiff_timeSuspension hZ) Ψ hΨself hΨ
  have hi : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))) ∞
      (fun p : ℝ × (ℝ × Q) => (p.2.1 - p.1, (p.1, p.2.2))) := by
    exact ((contMDiff_fst.comp contMDiff_snd).sub contMDiff_fst).prodMk
      (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))
  simpa only [comp_def, Ψ, sub_add_cancel] using contMDiff_snd.comp (hs.comp hi)

end Nonautonomous

end FsFltz.Geometry.CollarFlow

namespace FsFltz.Geometry.Completion

open SmoothManifold
open scoped Manifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- The actual supported collar evolution is jointly `C∞` on the whole
extension manifold and both real time parameters. Its inverse, boundary
fixation, carrier preservation, and full smaller-collar interpolation
remain the equations of the constructed evolution. -/
theorem exists_collarVelocity_globalSmoothHomeomorph :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point))
        (H : ℝ → ℝ → E.domain.extension.Point ≃ₜ E.domain.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        𝓘(ℝ, Model d) ∞
        (fun p : ℝ × (ℝ × E.domain.extension.Point) => H p.1 p.2.1 p.2.2) ∧
      (∀ s x, H s s x = x) ∧
      (∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => H s u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (H s t x)))) ∧
      (∀ s t u x, H t u (H s t x) = H s u x) ∧
      (∀ s t, (H s t).symm = H t s) ∧
      (∀ x ∉ Prod.snd '' K, ∀ s t, H s t x = x) ∧
      (∀ (s t : ℝ) (x : E.domain.boundary.Point),
        H s t (E.domain.boundaryInclusion.map x) = E.domain.boundaryInclusion.map x) ∧
      (∀ s t x, H s t x ∈ E.domain.carrier ↔ x ∈ E.domain.carrier) ∧
      ∀ q ∈ univ ×ˢ Ioo (-δ) δ, ∀ t ∈ Icc (0 : ℝ) 1,
        H 0 t (C.compactPresentationInterpolation C' h (0, q)) =
          C.compactPresentationInterpolation C' h (t, q) := by
  obtain ⟨δ, hδ, Z, K, H, hZ, hK, hzero, _, hself, hΦ, hcomp, hinv,
    hsupport, hboundary, hcarrier, hcollar⟩ := C.exists_collarVelocity_globalHomeomorph C' h
  exact ⟨δ, hδ, Z, K, H, hZ, hK, hzero,
    CollarFlow.contMDiff_joint_of_hasMFDerivAt hZ (fun s t => H s t) hself hΦ,
    hself, hΦ, hcomp, hinv, hsupport, hboundary, hcarrier, hcollar⟩

set_option backward.isDefEq.respectTransparency false in
/-- The produced smooth collar evolution corrects a supplied compact
presentation to one agreeing exactly with the intrinsic, radius-preserving
collar comparison on a common two-sided collar. The correction fixes the
original boundary map and preserves the compact carrier exactly. -/
theorem exists_collarAdapted_domainPresentation :
    ∃ h' : DomainPresentationEquiv D.domain E.domain,
      h'.boundaryEquiv = h.boundaryEquiv ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ univ ×ˢ Ioo (-δ) δ,
        C'.inclusion.map (h'.extensionEquiv (C.presentationCollarPoint q)) =
          C'.endMap (h.boundaryEquiv q.1, q.2) := by
  obtain ⟨δ₀, hδ₀, Z, K, H, _, _, _, hs, hself, _, hcomp, hinv, _, hboundary,
    hcarrier, hcollar⟩ := C.exists_collarVelocity_globalSmoothHomeomorph C' h
  have hm : ∀ s t : ℝ,
      ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (H s t) := by
    intro s t
    exact hs.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  let A (s t : ℝ) : E.domain.extension.SmoothEquiv E.domain.extension :=
    { __ := (H s t).toEquiv
      contMDiff_toFun := hm s t
      contMDiff_invFun := by
        change ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ (H s t).symm
        rw [hinv]
        exact hm t s }
  let g : D.domain.extension.SmoothEquiv E.domain.extension :=
    h.extensionEquiv.trans (A 1 0)
  have hg : g '' D.domain.carrier = E.domain.carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcarrier 1 0 _).mpr ((h.mem_carrier_iff x).mpr hx)
    · intro hy
      refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
      apply (h.mem_carrier_iff _).mp
      change h.extensionEquiv (h.extensionEquiv.symm ((H 1 0).symm y)) ∈ E.domain.carrier
      rw [h.extensionEquiv.apply_symm_apply]
      apply (hcarrier 1 0 _).mp
      simpa only [Homeomorph.apply_symm_apply] using hy
  let h' : DomainPresentationEquiv D.domain E.domain :=
    { extensionEquiv := g
      carrier := hg
      boundaryEquiv := h.boundaryEquiv
      boundary_square := by
        intro x
        change H 1 0 (h.extensionEquiv (D.domain.boundaryInclusion.map x)) = _
        rw [h.boundary_square]
        exact hboundary 1 0 (h.boundaryEquiv x) }
  obtain ⟨δ₁, hδ₁, hwidth⟩ := C.exists_common_compactPresentationInterpolationWidth C' h
  let δ : ℝ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  refine ⟨h', rfl, δ, hδ, ?_⟩
  intro q hq
  have hq₀ : q ∈ univ ×ˢ Ioo (-δ₀) δ₀ :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _))
      (min_le_left _ _)) hq
  have hq₁ : q ∈ univ ×ˢ Ioo (-δ₁) δ₁ :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _))
      (min_le_right _ _)) hq
  have hdom₀ := hwidth (show ((0 : ℝ), q) ∈ Icc (0 : ℝ) 1 ×ˢ
    (univ ×ˢ Ioo (-δ₁) δ₁) from ⟨⟨le_rfl, zero_le_one⟩, hq₁⟩)
  have hdom₁ := hwidth (show ((1 : ℝ), q) ∈ Icc (0 : ℝ) 1 ×ˢ
    (univ ×ˢ Ioo (-δ₁) δ₁) from ⟨⟨zero_le_one, le_rfl⟩, hq₁⟩)
  have he := congrArg (H 1 0) (hcollar q hq₀ 1 ⟨zero_le_one, le_rfl⟩)
  rw [hcomp, C.compactPresentationInterpolation_one C' h q hdom₁] at he
  rw [hself, C.compactPresentationInterpolation_zero] at he
  have htgt : (h.boundaryEquiv q.1, q.2) ∈ C'.presentationCollarSourceDomain := by
    have ht := hdom₀.2
    change C.presentationCollarInterpolation C' h (0, q) ∈ C'.presentationCollarSourceDomain at ht
    rwa [C.presentationCollarInterpolation_zero] at ht
  change C'.inclusion.map (H 1 0 (h.extensionEquiv (C.presentationCollarPoint q))) = _
  rw [← he, C'.inclusionMap_presentationCollarPoint _ htgt]

set_option backward.isDefEq.respectTransparency false in
/-- A supplied compact domain presentation extends, after the constructed
smooth collar correction, to an actual smooth presentation of the supplied
completions. Compact and cylindrical equations hold with the same boundary
map. No negative-radius compatibility is assumed of the original map.
This is a presentation theorem; it does not assert primitive preservation. -/
theorem exists_completionPresentation_of_domainPresentation :
    ∃ h' : DomainPresentationEquiv D.domain E.domain,
      h'.boundaryEquiv = h.boundaryEquiv ∧
      Nonempty (CompletionPresentationEquiv C C' h') := by
  obtain ⟨h', hb, δ, hδ, hcollar⟩ := C.exists_collarAdapted_domainPresentation C' h
  let U : Set (D.domain.boundary.Point × ℝ) := univ ×ˢ Ioi (-δ)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioi
  have hpos : univ ×ˢ Ici (0 : ℝ) ⊆ U := by
    intro q hq
    exact ⟨mem_univ _, by have hr : 0 ≤ q.2 := hq.2; change -δ < q.2; linarith⟩
  refine ⟨h', hb, ⟨C.presentationEquivOfCollar C' h' U hU hpos ?_⟩⟩
  intro q hq x hx he
  have hr : q.2 ≤ 0 := (C.endMap_mem_compact_iff q).mp ⟨x, hx, he⟩
  have hq' : q ∈ univ ×ˢ Ioo (-δ) δ :=
    ⟨mem_univ _, ⟨hq.2, lt_of_le_of_lt hr hδ⟩⟩
  have hsrc : q ∈ C.presentationCollarSourceDomain := ⟨x, he⟩
  have hpoint : C.presentationCollarPoint q = x :=
    C.inclusion.embedding.injective ((C.inclusionMap_presentationCollarPoint q hsrc).trans he.symm)
  rw [← hpoint, hb]
  exact hcollar q hq'

end FsFltz.Geometry.Completion
