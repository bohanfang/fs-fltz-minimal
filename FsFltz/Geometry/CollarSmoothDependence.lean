import FsFltz.Geometry.CollarContinuousDependence
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Analytic linearization of local collar evolution

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and
`sec:lean`, lines 788–814. These analytic producers concern the passage
from actual continuous Picard solutions to differentiable dependence.
They do not assert the geometric target `thm:target`, lines 352–429.

For a continuously differentiable map on a proper normed space, its
superposition map on continuous paths over a compact space is strictly
Fréchet differentiable. Its derivative applies the pointwise derivative
to a path variation. To prove the uniform remainder estimate, put all
nearby paths in a single compact ball, use uniform continuity of the
derivative there, and apply the mean value theorem on the small ball
around each point of the original path. Taking the supremum proves the
strict derivative in the path norm.

Integration from the initial time is a bounded linear operator on the
same path space. The Picard residual at a solution has path derivative
`1 - A`, where `A` is integration composed with pointwise linearization.
On a sufficiently short interval, its norm bound gives `‖A‖ < 1`, so the
Neumann inverse and the implicit-function theorem apply. The native
Picard fixed points form a continuous family of actual integral curves.
Their literal integral equations identify them locally with the implicit
solution; consequently their initial-point dependence is strictly
differentiable. The residual and invertibility are proved, rather than
assumed as extra properties of a flow.

A smooth cutoff extends a locally `C¹` field to a global `C¹` field.
Shrinking the time and initial-point neighborhoods keeps the constructed
curves where the extension equals the original field. Chart changes then
transfer their derivatives to actual manifold integral curves. Uniqueness
identifies these local solutions with any given all-real evolution.
The times at which its map is differentiable at a fixed initial point
form a clopen set: small positive and negative time maps propagate the
property in both directions. This set contains zero, so connectedness
of real time gives differentiability of every time map. Suspending a
time-dependent field as an autonomous field on `ℝ × Q` supplies the same
result for two-time evolutions.

The final theorem consumes the actual collar evolution constructed from
completion data and obtains differentiable homeomorphisms with
differentiable inverses, preserving all of its stated equations and
support properties. For smooth fields, `CollarSmoothEvolution` upgrades
this to joint `C∞` dependence on both times and the initial point and
constructs the corresponding collar correction and completed
presentation. Coherent choices for varying completions remain pending.
No geometric comparison chain is proved in this module.
-/

noncomputable section
open scoped ContDiff Classical NNReal
open Set Filter Topology Metric Function

namespace FsFltz.Geometry.CollarFlow

section Superposition

variable {X F G : Type} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pointwise application of a continuous family of linear maps, with its
actual supremum-norm bound. -/
def pathLinearization (D : C(X, F →L[ℝ] G)) : C(X, F) →L[ℝ] C(X, G) :=
  LinearMap.mkContinuous
    { toFun := fun β => ⟨fun t => D t (β t), D.continuous.clm_apply β.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖D‖ (fun β => (ContinuousMap.norm_le _ (by positivity)).mpr (fun t => by
      calc
        ‖D t (β t)‖ ≤ ‖D t‖ * ‖β t‖ := (D t).le_opNorm _
        _ ≤ ‖D‖ * ‖β‖ := mul_le_mul (D.norm_coe_le_norm t)
          (β.norm_coe_le_norm t) (norm_nonneg (β t)) (norm_nonneg D)))

@[simp] theorem pathLinearization_apply (D : C(X, F →L[ℝ] G))
    (β : C(X, F)) (t : X) : pathLinearization D β t = D t (β t) := rfl

theorem norm_pathLinearization_le (D : C(X, F →L[ℝ] G)) :
    ‖pathLinearization D‖ ≤ ‖D‖ := by
  unfold pathLinearization
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg D) _

/-- The bounded linear map sending an initial point to the constant path. -/
def constantPath : F →L[ℝ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.const X
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (fun x => by simpa using (ContinuousMap.norm_le _ (norm_nonneg x)).mpr (fun _ => le_rfl))

@[simp] theorem constantPath_apply (x : F) (t : X) :
    constantPath (X := X) x t = x := rfl

/-- The derivative of pointwise composition on continuous paths is the
pointwise derivative. Strict differentiability supplies the analytic
regularity needed by the implicit-function theorem for Picard equations;
no initial-point regularity of a flow is assumed. -/
theorem hasStrictFDerivAt_pathComposition [ProperSpace F] {f : F → G}
    (hf : ContDiff ℝ 1 f) (α : C(X, F)) :
    HasStrictFDerivAt (fun β : C(X, F) => (⟨f, hf.continuous⟩ : C(F, G)).comp β)
      (pathLinearization ((⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ :
        C(F, F →L[ℝ] G)).comp α)) α := by
  apply HasStrictFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have huc := (isCompact_closedBall (0 : F) (‖α‖ + 1)).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc c hc
  let r : ℝ := min δ 1 / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ 1]
  have hrone : r < 1 := by dsimp [r]; linarith [min_le_right δ 1]
  have hball : ∀ t : X, ball (α t) r ⊆ closedBall 0 (‖α‖ + 1) := by
    intro t y hy
    rw [mem_closedBall, dist_zero_right]
    have hd : ‖y - α t‖ < r := by simpa only [mem_ball, dist_eq_norm] using hy
    calc
      ‖y‖ ≤ ‖y - α t‖ + ‖α t‖ := by simpa only [add_comm] using norm_le_insert' y (α t)
      _ ≤ ‖α‖ + 1 := by linarith [α.norm_coe_le_norm t]
  have hnear : ∀ᶠ p : C(X, F) × C(X, F) in 𝓝 (α, α),
      p.1 ∈ ball α r ∧ p.2 ∈ ball α r :=
    (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hr⟩
  filter_upwards [hnear] with p hp
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hleft : p.1 t ∈ ball (α t) r := by
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ((p.1 - α).norm_coe_le_norm t)
      (show ‖p.1 - α‖ < r by simpa only [mem_ball, dist_eq_norm] using hp.1)
  have hright : p.2 t ∈ ball (α t) r := by
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ((p.2 - α).norm_coe_le_norm t)
      (show ‖p.2 - α‖ < r by simpa only [mem_ball, dist_eq_norm] using hp.2)
  have hbound : ∀ y ∈ ball (α t) r, ‖fderiv ℝ f y - fderiv ℝ f (α t)‖ ≤ c := by
    intro y hy
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hcontrol y (hball t hy) (α t) (hball t (mem_ball_self hr))
    exact lt_of_lt_of_le hy (le_of_lt hrδ)
  have hrem := (convex_ball (α t) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun y _ => (hf.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
    hbound hright hleft
  exact hrem.trans (mul_le_mul_of_nonneg_left ((p.1 - p.2).norm_coe_le_norm t) hc.le)

end Superposition

section Volterra

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b : ℝ} (t₀ : Icc a b)

/-- Integration from the initial time on the full continuous path space.
Projection to the closed time interval gives a continuous global extension
of each integrand; no extension regularity is assumed. -/
def pathIntegral : C(Icc a b, F) →L[ℝ] C(Icc a b, F) :=
  LinearMap.mkContinuous
    { toFun := fun β =>
        ⟨fun t => ∫ u in (t₀ : ℝ)..(t : ℝ),
          β (projIcc a b (t₀.2.1.trans t₀.2.2) u),
          (intervalIntegral.continuous_primitive (fun c d =>
            (β.continuous.comp continuous_projIcc).intervalIntegrable c d) t₀).comp
              continuous_subtype_val⟩
      map_add' := by
        intro β γ
        ext t
        exact intervalIntegral.integral_add
          ((β.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((γ.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro c β
        ext t
        exact intervalIntegral.integral_smul c _ }
    (max (b - t₀) (t₀ - a)) (fun β =>
      (ContinuousMap.norm_le _ (mul_nonneg
        (le_max_of_le_left (sub_nonneg.mpr t₀.2.2)) (norm_nonneg β))).mpr (fun t => by
        calc
          ‖∫ u in (t₀ : ℝ)..(t : ℝ), β (projIcc a b (t₀.2.1.trans t₀.2.2) u)‖
            ≤ ‖β‖ * |(t : ℝ) - t₀| :=
              intervalIntegral.norm_integral_le_of_norm_le_const (fun _ _ => β.norm_coe_le_norm _)
          _ ≤ max (b - t₀) (t₀ - a) * ‖β‖ := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right
              (abs_sub_le_max_sub t.2.1 t.2.2 _) (norm_nonneg β)))

@[simp] theorem pathIntegral_apply (β : C(Icc a b, F)) (t : Icc a b) :
    pathIntegral t₀ β t = ∫ u in (t₀ : ℝ)..(t : ℝ),
      β (projIcc a b (t₀.2.1.trans t₀.2.2) u) := rfl

theorem norm_pathIntegral_le : ‖pathIntegral (F := F) t₀‖ ≤ max (b - t₀) (t₀ - a) := by
  unfold pathIntegral
  apply LinearMap.mkContinuous_norm_le
  exact le_max_of_le_left (sub_nonneg.mpr t₀.2.2)

end Volterra

section Implicit

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [ProperSpace F] {a b : ℝ} {t₀ : Icc a b}

private theorem isInvertible_one_sub_of_norm_lt_one
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1) : (1 - A).IsInvertible := by
  obtain ⟨u, hu⟩ := IsUnit.one_sub_of_norm_lt_one hA
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u, hu⟩

/-- A continuous family satisfying the actual Picard equation is strictly
differentiable in its initial point when its linearized integral operator
is a contraction. The hypothesis concerns only the explicit linearization,
not differentiability of the solution family. -/
theorem hasStrictFDerivAt_of_picard_equation {f : F → F} (hf : ContDiff ℝ 1 f)
    (β : F → C(Icc a b, F)) (x₀ : F) (hβ : ContinuousAt β x₀)
    (hpicard : ∀ᶠ x in 𝓝 x₀,
      β x = constantPath x + pathIntegral t₀ ((⟨f, hf.continuous⟩ : C(F, F)).comp (β x)))
    (hsmall : ‖(pathIntegral t₀).comp (pathLinearization
      ((⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ : C(F, F →L[ℝ] F)).comp (β x₀)))‖ < 1) :
    ∃ B : F →L[ℝ] C(Icc a b, F), HasStrictFDerivAt β B x₀ := by
  let V := pathIntegral (F := F) t₀
  let C := constantPath (X := Icc a b) (F := F)
  let N : C(Icc a b, F) → C(Icc a b, F) :=
    fun α => (⟨f, hf.continuous⟩ : C(F, F)).comp α
  let A := V.comp (pathLinearization
    ((⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ : C(F, F →L[ℝ] F)).comp (β x₀)))
  let R : F × C(Icc a b, F) → C(Icc a b, F) := fun p => p.2 - C p.1 - V (N p.2)
  let R' : F × C(Icc a b, F) →L[ℝ] C(Icc a b, F) :=
    ContinuousLinearMap.snd ℝ _ _ - C.comp (ContinuousLinearMap.fst ℝ _ _) -
      A.comp (ContinuousLinearMap.snd ℝ _ _)
  have hR : HasStrictFDerivAt R R' (x₀, β x₀) :=
    (hasStrictFDerivAt_snd.sub (C.hasStrictFDerivAt.comp _ hasStrictFDerivAt_fst)).sub
      (V.hasStrictFDerivAt.comp _
        ((hasStrictFDerivAt_pathComposition hf (β x₀)).comp (x₀, β x₀)
          (f := Prod.snd) hasStrictFDerivAt_snd))
  have hpartial : R'.comp (ContinuousLinearMap.inr ℝ F C(Icc a b, F)) = 1 - A := by
    ext α t
    simp [R']
  have hinv : (R'.comp (ContinuousLinearMap.inr ℝ F C(Icc a b, F))).IsInvertible := by
    rw [hpartial]
    exact isInvertible_one_sub_of_norm_lt_one A hsmall
  have hzero : R (x₀, β x₀) = 0 := by
    dsimp [R, C, V, N]
    nth_rw 1 [hpicard.self_of_nhds]
    abel
  have heq := hR.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have heq' := (continuousAt_id.prodMk hβ).eventually heq
  have hψ := hR.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  refine ⟨_, hψ.congr_of_eventuallyEq ?_⟩
  filter_upwards [heq', hpicard] with x hx hpx
  apply hx.mp
  rw [hzero]
  dsimp [R, C, V, N]
  nth_rw 1 [hpx]
  abel

end Implicit

section PicardFamily

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {a b : ℝ} {t₀ : Icc a b} {x₀ : F} {R r L K : ℝ≥0}

/-- Native Picard fixed points form a continuous family in the full
continuous-path norm and satisfy the literal integral equation. The
equation, bounds, and integral curves are conclusions of the construction. -/
theorem exists_continuous_picard_family {f : F → F} (hf : Continuous f)
    (hpl : IsPicardLindelof (fun _ => f) t₀ x₀ R r L K) :
    ∃ β : F → C(Icc a b, F), ContinuousOn β (closedBall x₀ r) ∧
      ∀ x ∈ closedBall x₀ r,
        β x = constantPath x + pathIntegral t₀ ((⟨f, hf⟩ : C(F, F)).comp (β x)) ∧
        β x t₀ = x ∧ (∀ t, β x t ∈ closedBall x₀ R) ∧
        ∀ t : Icc a b,
          HasDerivWithinAt (fun u => β x (projIcc a b (t₀.2.1.trans t₀.2.2) u))
            (f (β x t)) (Icc a b) t := by
  have H := fun x (hx : x ∈ closedBall x₀ r) =>
    ODE.FunSpace.exists_isFixedPt_next hpl hx
  choose γ hγ using H
  let β : F → C(Icc a b, F) := fun x =>
    if hx : x ∈ closedBall x₀ r then (γ x hx).toContinuousMap else 0
  have hβ (x : F) (hx : x ∈ closedBall x₀ r) :
      β x = (γ x hx).toContinuousMap := by simp only [β, dite_eq_left hx]
  obtain ⟨L', hdist⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hpl
  have hlip : LipschitzOnWith L' β (closedBall x₀ r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hβ x hx, hβ y hy]
    exact hdist x y hx hy (γ x hx) (γ y hy) (hγ x hx) (hγ y hy)
  refine ⟨β, hlip.continuousOn, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext t
    rw [hβ x hx, ODE.FunSpace.toContinuousMap_apply_eq_apply]
    nth_rw 1 [← hγ x hx]
    rw [ODE.FunSpace.next_apply, ODE.picard_apply, ContinuousMap.add_apply,
      constantPath_apply, pathIntegral_apply]
    congr 1
  · rw [hβ x hx, ODE.FunSpace.toContinuousMap_apply_eq_apply, ← hγ x hx,
      ODE.FunSpace.next_apply₀]
  · intro t
    rw [hβ x hx, ODE.FunSpace.toContinuousMap_apply_eq_apply]
    exact (γ x hx).mem_closedBall hpl.mul_max_le
  · intro t
    rw [hβ x hx]
    have hd := ODE.hasDerivWithinAt_picard_Icc t₀.2 hpl.continuousOn_uncurry
      (γ x hx).continuous_compProj.continuousOn
      (fun _ _ => (γ x hx).compProj_mem_closedBall hpl.mul_max_le) x t.2
    rw [ODE.FunSpace.compProj_of_mem t.2] at hd
    simp only [ODE.FunSpace.toContinuousMap_apply_eq_apply]
    apply hd.congr_of_mem _ t.2
    intro u hu
    change (γ x hx).compProj u = ODE.picard (fun _ => f) t₀ x (γ x hx).compProj u
    rw [ODE.FunSpace.compProj_of_mem hu]
    nth_rw 1 [← hγ x hx]
    exact ODE.FunSpace.next_apply hpl hx (γ x hx)

end PicardFamily

section LocalDependence

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [ProperSpace F]

/-- Actual local integral curves of a `C¹` Euclidean field have strict
Fréchet dependence on their initial point, in the continuous-path norm.
The common lifetime, curves, and derivative are all produced from the
field; no differentiable solution or flow is supplied as input. -/
theorem exists_strictlyDifferentiable_local_picard_family {f : F → F}
    (hf : ContDiff ℝ 1 f) (x₀ : F) :
    ∃ (ε : ℝ) (hε : 0 < ε) (r : ℝ), 0 < r ∧
      ∃ β : F → C(Icc (-ε) ε, F), ContinuousOn β (ball x₀ r) ∧
        ∀ x ∈ ball x₀ r,
          β x ⟨0, by constructor <;> linarith⟩ = x ∧
          (∃ B : F →L[ℝ] C(Icc (-ε) ε, F), HasStrictFDerivAt β B x) ∧
          ∀ (t : ℝ) (ht : t ∈ Ioo (-ε) ε),
            HasDerivAt (fun u => β x (projIcc (-ε) ε (by linarith) u))
              (f (β x ⟨t, Ioo_subset_Icc_self ht⟩)) t := by
  obtain ⟨ε, hε, R, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf.contDiffAt
  obtain ⟨M₀, hM₀⟩ := ((isCompact_closedBall x₀ (R : ℝ)).image
    (hf.continuous_fderiv (by simp))).isBounded.exists_norm_le
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
  · apply hasStrictFDerivAt_of_picard_equation hf β x
      (hc'.continuousAt (isOpen_ball.mem_nhds hx))
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hβ y (ball_subset_closedBall hy)).1
    · let D : C(Icc (-δ) δ, F →L[ℝ] F) :=
        (⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ : C(F, F →L[ℝ] F)).comp (β x)
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
/-- A `C¹` field near a point has a globally `C¹` representative agreeing
on a ball around that point. Smooth cutoffs are used only for localization. -/
theorem exists_contDiff_localRepresentative {f : F → F} {x₀ : F}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ g : F → F, ContDiff ℝ 1 g ∧ ∃ ρ : ℝ, 0 < ρ ∧ EqOn g f (ball x₀ ρ) := by
  obtain ⟨R, hR, hregular⟩ := Metric.eventually_nhds_iff_ball.mp (hf.eventually (by simp))
  let χ : ContDiffBump x₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let g : F → F := fun x => χ x • f x
  have hg : ContDiff ℝ 1 g := by
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
differentiable initial-point dependence. The curves can be required to
remain in any specified neighborhood. All regularity comes from the
constructed Picard family and its proved path derivative. -/
theorem exists_neighborhood_differentiable_local_solution {f : F → F} {x₀ : F}
    (hf : ContDiffAt ℝ 1 f x₀) {S : Set F} (hS : S ∈ 𝓝 x₀) :
    ∃ U : Set F, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ γ : F × ℝ → F, ContinuousOn γ (U ×ˢ univ) ∧
        (∀ x ∈ U, γ (x, 0) = x) ∧
        (∀ x ∈ U, ∀ t ∈ Ioo (-ε) ε, γ (x, t) ∈ S ∧
          HasDerivAt (fun u => γ (x, u)) (f (γ (x, t))) t) ∧
        ∀ x ∈ U, ∀ t : ℝ, DifferentiableAt ℝ (fun y => γ (y, t)) x := by
  obtain ⟨g, hg, ρ, hρ, heq⟩ := exists_contDiff_localRepresentative hf
  obtain ⟨ε, hε, r, hr, β, hc, hβ⟩ := exists_strictlyDifferentiable_local_picard_family hg x₀
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
    obtain ⟨B, hB⟩ := (hβ x (hσsub hx).2).2.1
    exact ((ContinuousMap.evalCLM ℝ (π t)).hasFDerivAt.comp x hB.hasFDerivAt).differentiableAt

end LocalField

section ManifoldLocal

open scoped Manifold
variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [ProperSpace F] [HasContDiffBump F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q]

set_option backward.isDefEq.respectTransparency false in
/-- A native manifold field has actual common local integral curves with
differentiable dependence on their initial points. The chart solutions
are constructed from the field, and their containment in the chart target
is proved before transferring either the ODE or the initial-point derivative. -/
theorem exists_neighborhood_differentiable_local_integralCurve
    {v : (x : Q) → TangentSpace I x} {x₀ : Q}
    (hv : ContMDiffAt I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)) x₀) :
    ∃ U : Set Q, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ β : Q × ℝ → Q, ContinuousOn β (U ×ˢ Ioo (-ε) ε) ∧
        ∀ x ∈ U, β (x, 0) = x ∧
          IsMIntegralCurveOn (fun t => β (x, t)) v (Ioo (-ε) ε) ∧
          ∀ t ∈ Ioo (-ε) ε, MDifferentiableAt I I (fun y => β (y, t)) x := by
  let e := extChartAt I x₀
  let f : F → F := fun y =>
    tangentCoordChange I (e.symm y) x₀ (e.symm y) (v (e.symm y))
  have hcf : ContDiffAt ℝ 1 f (e x₀) := by
    rw [contMDiffAt_iff] at hv
    exact (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨A, hA, hx₀, ε, hε, α, hαcont, hα₀, hα, hαdiff⟩ :=
    exists_neighborhood_differentiable_local_solution hcf (extChartAt_target_mem_nhds x₀)
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
    have he : MDifferentiableAt I 𝓘(ℝ, F) e x :=
      mdifferentiableAt_extChartAt (by simpa only [← extChartAt_source I x₀] using hx.1)
    have ha : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun y => α (y, t)) (e x) :=
      mdifferentiableAt_iff_differentiableAt.mpr (hαdiff _ hx.2 t)
    have hi : MDifferentiableAt 𝓘(ℝ, F) I e.symm (α (e x, t)) :=
      (mdifferentiableWithinAt_extChartAt_symm htarget).mdifferentiableAt
        (by rw [I.range_eq_univ]; exact univ_mem)
    exact (hi.comp (e x) (f := fun y => α (y, t)) ha).comp x (f := e) he

end ManifoldLocal

section ManifoldGlobal

open scoped Manifold
variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [ProperSpace F] [HasContDiffBump F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Every time map of an actual all-real evolution of a `C¹` field is
manifold differentiable in the initial point. Local regularity is proved
from Picard solutions; uniqueness and connected real time propagate it
along the entire trajectory. -/
theorem mdifferentiable_of_isMIntegralCurve
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    (φ : ℝ → Q → Q) (hself : ∀ x, φ 0 x = x)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) v) :
    ∀ t : ℝ, MDifferentiable I I (φ t) := by
  have hcomp : ∀ s t x, φ s (φ t x) = φ (s + t) x := by
    intro s t x
    exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv (hφ (φ t x)) ((hφ x).comp_add t)
      (by simp only [comp_apply, zero_add, hself])) s
  have hlocal : ∀ x₀, ∃ U : Set Q, IsOpen U ∧ x₀ ∈ U ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ U, ∀ t ∈ Ioo (-ε) ε,
        MDifferentiableAt I I (φ t) y := by
    intro x₀
    obtain ⟨U, hU, hx₀, ε, hε, β, _, hβ⟩ :=
      exists_neighborhood_differentiable_local_integralCurve (hv x₀)
    refine ⟨U, hU, hx₀, ε, hε, ?_⟩
    intro y hy t ht
    apply ((hβ y hy).2.2 t ht).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hy] with z hz
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
      hv ((hφ z).isMIntegralCurveOn _) (hβ z hz).2.1
      (by rw [hself, (hβ z hz).1]) ht
  intro t x
  let S : Set ℝ := {u | MDifferentiableAt I I (φ u) x}
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
    change MDifferentiableAt I I (φ 0) x
    rw [he]
    exact mdifferentiableAt_id
  rcases isClopen_iff.mp hS with he | he
  · simp only [he, notMem_empty] at hmem
  · change t ∈ S
    rw [he]
    exact mem_univ _

end ManifoldGlobal

section Nonautonomous

open scoped Manifold
variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]
  [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ, F) ∞ Q] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Every time map of actual solutions of a smooth time-dependent field
is differentiable in the initial point. The suspended autonomous evolution
uses the proved global initial-point dependence theorem. -/
theorem mdifferentiable_of_hasMFDerivAt
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    (Φ : ℝ → ℝ → Q → Q) (hself : ∀ s x, Φ s s x = x)
    (hΦ : ∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u => Φ s u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s t x)))) :
    ∀ s t : ℝ, MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) (Φ s t) := by
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
  have hm := mdifferentiable_of_isMIntegralCurve
    ((contMDiff_timeSuspension hZ).of_le (by simp)) Ψ hΨself hΨ
  intro s t x
  have hi : MDifferentiableAt 𝓘(ℝ, F) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F))
      (fun y : Q => (s, y)) x := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have he := mdifferentiableAt_snd.comp x
    (f := fun y => Ψ (t - s) (s, y)) ((hm (t - s) (s, x)).comp x hi)
  simpa only [comp_def, Ψ, sub_add_cancel] using he

end Nonautonomous

end FsFltz.Geometry.CollarFlow

namespace FsFltz.Geometry
namespace Completion

open SmoothManifold
open scoped Manifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

/-- The actual compactly supported collar evolution has differentiable
time maps and differentiable inverses. This preserves its literal ODE,
boundary fixation, carrier preservation, and collar interpolation equation.
The joint `C∞` upgrade is proved by
`exists_collarVelocity_globalSmoothHomeomorph` in
`CollarSmoothEvolution`. -/
theorem exists_collarVelocity_globalDifferentiableHomeomorph :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point))
        (H : ℝ → ℝ → E.domain.extension.Point ≃ₜ E.domain.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      Continuous (fun p : ℝ × (ℝ × E.domain.extension.Point) => H p.1 p.2.1 p.2.2) ∧
      (∀ s t, MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (H s t)) ∧
      (∀ s t, MDifferentiable 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (H s t).symm) ∧
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
  obtain ⟨δ, hδ, Z, K, H, hZ, hK, hzero, hc, hself, hΦ, hcomp, hinv,
    hsupport, hboundary, hcarrier, hcollar⟩ := C.exists_collarVelocity_globalHomeomorph C' h
  have hm := CollarFlow.mdifferentiable_of_hasMFDerivAt hZ (fun s t => H s t) hself hΦ
  refine ⟨δ, hδ, Z, K, H, hZ, hK, hzero, hc, hm, ?_, hself, hΦ, hcomp, hinv,
    hsupport, hboundary, hcarrier, hcollar⟩
  intro s t
  rw [hinv]
  exact hm t s

end Completion
end FsFltz.Geometry
