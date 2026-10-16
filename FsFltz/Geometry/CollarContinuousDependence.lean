import FsFltz.Geometry.CollarEvolution

/-!
# Continuous dependence for the constructed collar evolution

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and
`sec:lean`, lines 788–814. Local chart Picard estimates give joint
continuity in the initial point and time. Uniqueness identifies those
local solutions with any existing all-real evolution. Its composition law
then propagates continuity to every real time. Applied to the actual
supported collar evolution, this supplies a family of homeomorphisms.

For finite-dimensional smooth fields, `CollarSmoothEvolution` proves the
stronger joint `C∞` dependence and applies it to the actual supported
collar evolution. Coherent choices for varying completions remain
pending. These continuity results do not prove the geometric target
`thm:target`, lines 352–429.
-/

noncomputable section
open scoped Manifold ContDiff Classical NNReal
open Set Filter Topology Function Metric

namespace FsFltz.Geometry
namespace CollarFlow

private theorem exists_bounded_continuous_solution
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ → F → F} {a b : ℝ} {t₀ : Icc a b} {x₀ : F} {R r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ R r L K) :
    ∃ α : F × ℝ → F,
      (∀ x ∈ closedBall x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => α (x, u))
          (f t (α (x, t))) (Icc a b) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ univ) ∧
      ∀ x ∈ closedBall x₀ r, ∀ t, α (x, t) ∈ closedBall x₀ R := by
  have H := fun x (hx : x ∈ closedBall x₀ r) =>
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose γ hγ using H
  let α : F × ℝ → F := fun p =>
    if hx : p.1 ∈ closedBall x₀ r then (γ p.1 hx).compProj p.2 else 0
  have hα (x : F) (hx : x ∈ closedBall x₀ r) (t : ℝ) :
      α (x, t) = (γ x hx).compProj t := by simp only [α, dite_eq_left hx]
  have hbound : ∀ x ∈ closedBall x₀ r, ∀ t, α (x, t) ∈ closedBall x₀ R := by
    intro x hx t
    rw [hα x hx t]
    exact (γ x hx).compProj_mem_closedBall hf.mul_max_le
  refine ⟨α, ?_, ?_, hbound⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hα x hx, ODE.FunSpace.compProj_val, ← hγ, ODE.FunSpace.next_apply₀]
    · intro t ht
      apply (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        ((γ x hx).continuous_compProj.continuousOn.congr (fun u _ => hα x hx u))
        (fun u _ => hbound x hx u) x ht).congr_of_mem _ ht
      intro u hu
      rw [hα x hx u]
      nth_rw 1 [← hγ]
      rw [ODE.FunSpace.compProj_of_mem hu, ODE.FunSpace.next_apply]
      simp only [α, dite_eq_left hx]
  · obtain ⟨L', hdist⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
    · intro x hx
      exact (γ x hx).continuous_compProj.continuousOn.congr (fun u _ => hα x hx u)
    · intro t _
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [hα x hx, hα y hy, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
        ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
        ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
      have : Nonempty (Icc a b) := ⟨t₀⟩
      exact ContinuousMap.dist_le_iff_of_nonempty.mp
        (hdist x y hx hy (γ x hx) (γ y hy) (hγ x hx) (hγ y hy)) _

section Local

variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q]

set_option backward.isDefEq.respectTransparency false in
/-- Local integration in one chart with jointly continuous dependence on
the initial point and time. The curves stay in the chart for a common
positive lifetime; both containment and continuity come from actual
Picard fixed points. -/
theorem exists_neighborhood_continuous_local_integralCurve [CompleteSpace F]
    {v : (x : Q) → TangentSpace I x} {x₀ : Q}
    (hv : ContMDiffAt I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)) x₀) :
    ∃ U : Set Q, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ β : Q × ℝ → Q, ContinuousOn β (U ×ˢ univ) ∧
        ∀ x ∈ U, β (x, 0) = x ∧
          IsMIntegralCurveOn (fun t => β (x, t)) v (Ioo (-ε) ε) := by
  let e := extChartAt I x₀
  let f : F → F := fun y =>
    tangentCoordChange I (e.symm y) x₀ (e.symm y) (v (e.symm y))
  have hcf : ContDiffAt ℝ 1 f (e x₀) := by
    rw [contMDiffAt_iff] at hv
    exact (hv.2.contDiffAt (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))).snd
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hcf
  obtain ⟨R, hR, hRt⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I) x₀)
  have hra : r ≤ a := by
    have hm := (hpl 0).mul_max_le
    have hnonneg : (0 : ℝ) ≤ L * max (0 + ε - 0) (0 - (0 - ε)) := by
      simp only [zero_add, sub_zero, zero_sub, neg_neg, max_self]
      positivity
    exact NNReal.coe_le_coe.mp (by linarith)
  let a' : ℝ≥0 := min a ⟨R / 2, by positivity⟩
  let r' : ℝ≥0 := a' / 2
  have ha' : 0 < a' := lt_min (lt_of_lt_of_le hr hra)
    (NNReal.coe_pos.mp (half_pos hR))
  have hr' : r' < a' := half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ := (hpl 0).exists_shrink_radius hε (min_le_left _ _) hr'
  let U : Set Q := e.source ∩ e ⁻¹' ball (e x₀) r'
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) isOpen_ball
  have hx₀ : x₀ ∈ U := ⟨mem_extChartAt_source x₀,
    mem_ball_self (NNReal.coe_pos.mpr (half_pos ha'))⟩
  obtain ⟨α, hα, hαcont, hαball⟩ := exists_bounded_continuous_solution hpl'
  have hαtarget {x : Q} (hx : x ∈ U) (t : ℝ) : α (e x, t) ∈ e.target := by
    apply hRt
    apply closedBall_subset_ball (show (a' : ℝ) < R from
      lt_of_le_of_lt (NNReal.coe_le_coe.mpr (min_le_right _ _)) (half_lt_self hR))
    exact hαball _ (ball_subset_closedBall hx.2) t
  let β : Q × ℝ → Q := fun p => e.symm (α (e p.1, p.2))
  have hc : ContinuousOn (fun p : Q × ℝ => α (e p.1, p.2)) (U ×ˢ univ) :=
    hαcont.comp (((continuousOn_extChartAt x₀).comp continuousOn_fst
      (fun _ hp => hp.1.1)).prodMk continuousOn_snd)
      (fun _ hp => ⟨ball_subset_closedBall hp.1.2, mem_univ _⟩)
  refine ⟨U, hUopen, hx₀, ε', hε', β,
    (continuousOn_extChartAt_symm x₀).comp hc (fun p hp => hαtarget hp.1 p.2), ?_⟩
  intro x hx
  have hxball := ball_subset_closedBall hx.2
  refine ⟨by change e.symm (α (e x, 0)) = x; rw [(hα _ hxball).1, e.left_inv hx.1], ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (0 - ε') (0 + ε') := by simpa using ht
  let xₜ : Q := e.symm (α (e x, t))
  have hsrc : xₜ ∈ e.source := e.map_target (hαtarget hx t)
  have hself := mem_extChartAt_source (I := I) xₜ
  have hd : HasDerivAt (fun u => α (e x, u)) (f (α (e x, t))) t :=
    ((hα _ hxball).2 t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' (hαtarget hx t)).comp
      (f := fun u => α (e x, u)) hd.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ (fun u => α (e x, u))) (v xₜ) t
  have he : f (α (e x, t)) = tangentCoordChange I xₜ x₀ xₜ (v xₜ) := rfl
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hself,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hself, hsrc⟩, hself⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ (hd.congr_deriv he)
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by rw [I.range_eq_univ]; exact univ_mem)
  rw [← e.right_inv (hαtarget hx t)]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hsrc, hself⟩

end Local

private theorem continuous_of_local_continuous_action
    {Q : Type} [TopologicalSpace Q] (φ : ℝ → Q → Q)
    (hself : ∀ x, φ 0 x = x)
    (hcomp : ∀ s t x, φ s (φ t x) = φ (s + t) x)
    (hcurve : ∀ x, Continuous (fun t => φ t x))
    (hlocal : ∀ x, ∃ U : Set Q, IsOpen U ∧ x ∈ U ∧
      ∃ ε : ℝ, 0 < ε ∧
        ContinuousOn (fun p : ℝ × Q => φ p.1 p.2) (Ioo (-ε) ε ×ˢ U)) :
    Continuous (fun p : ℝ × Q => φ p.1 p.2) := by
  have htime : ∀ t x, ContinuousAt (φ t) x := by
    intro t x
    let S : Set ℝ := {u | ContinuousAt (φ u) x}
    have hnear (u : ℝ) : ∀ᶠ w in 𝓝 u, w ∈ S ↔ u ∈ S := by
      obtain ⟨U, hU, hy, ε, hε, hc⟩ := hlocal (φ u x)
      have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
      have hleft : ∀ᶠ w in 𝓝 u, w - u ∈ Ioo (-ε) ε :=
        ((continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
          (by simpa using isOpen_Ioo.mem_nhds hzero))
      have hright : ∀ᶠ w in 𝓝 u, u - w ∈ Ioo (-ε) ε :=
        ((continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using isOpen_Ioo.mem_nhds hzero))
      have horbit : ∀ᶠ w in 𝓝 u, φ w x ∈ U :=
        (hcurve x).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
      filter_upwards [hleft, hright, horbit] with w hw₁ hw₂ hw₃
      constructor
      · intro hw
        have hl : ContinuousAt (fun p : ℝ × Q => φ p.1 p.2) (u - w, φ w x) :=
          hc.continuousAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hw₂, hw₃⟩)
        have hi : ContinuousAt (fun z : Q => (u - w, φ w z)) x :=
          continuousAt_const.prodMk hw
        have he := hl.comp (f := fun z : Q => (u - w, φ w z)) hi
        simpa only [comp_def, hcomp, sub_add_cancel, S, mem_ofPred_eq] using he
      · intro hu
        have hl : ContinuousAt (fun p : ℝ × Q => φ p.1 p.2) (w - u, φ u x) :=
          hc.continuousAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hw₁, hy⟩)
        have hi : ContinuousAt (fun z : Q => (w - u, φ u z)) x :=
          continuousAt_const.prodMk hu
        have he := hl.comp (f := fun z : Q => (w - u, φ u z)) hi
        simpa only [comp_def, hcomp, sub_add_cancel, S, mem_ofPred_eq] using he
    have hSopen : IsOpen S := isOpen_iff_eventually.mpr (fun u hu =>
      (hnear u).mono (fun _ hw => hw.mpr hu))
    have hScompl : IsOpen Sᶜ := isOpen_iff_eventually.mpr (fun u hu =>
      (hnear u).mono (fun _ hw => fun h => hu (hw.mp h)))
    have hS : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
    have hmem : (0 : ℝ) ∈ S := by
      have he : φ 0 = id := funext hself
      change ContinuousAt (φ 0) x
      rw [he]
      exact continuousAt_id
    rcases isClopen_iff.mp hS with he | he
    · simp only [he, notMem_empty] at hmem
    · change t ∈ S
      rw [he]
      exact mem_univ _
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  obtain ⟨U, hU, hy, ε, hε, hc⟩ := hlocal (φ t x)
  have hl : ContinuousAt (fun p : ℝ × Q => φ p.1 p.2) (t - t, φ t x) :=
    hc.continuousAt ((isOpen_Ioo.prod hU).mem_nhds
    (show (t - t, φ t x) ∈ Ioo (-ε) ε ×ˢ U by
      simpa using And.intro (And.intro (neg_lt_zero.mpr hε) hε) hy))
  have hi : ContinuousAt (fun p : ℝ × Q => (p.1 - t, φ t p.2)) (t, x) :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      ((htime t x).comp continuousAt_snd)
  have he := hl.comp (f := fun p : ℝ × Q => (p.1 - t, φ t p.2)) hi
  simpa only [comp_def, hcomp, sub_add_cancel] using he

section Global

variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q]
  [CompleteSpace F] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- An all-real family of integral curves of a `C¹` field is jointly
continuous in time and its initial point. Initial-point regularity is
proved by comparison with the local Picard family; it is not a hypothesis
on the supplied curves. Uniqueness also produces the composition law
needed to propagate that regularity along the entire trajectory. -/
theorem continuous_of_isMIntegralCurve
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    (φ : ℝ → Q → Q) (hself : ∀ x, φ 0 x = x)
    (hφ : ∀ x, IsMIntegralCurve (fun t => φ t x) v) :
    Continuous (fun p : ℝ × Q => φ p.1 p.2) := by
  have hcomp : ∀ s t x, φ s (φ t x) = φ (s + t) x := by
    intro s t x
    exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv (hφ (φ t x)) ((hφ x).comp_add t)
      (by simp only [comp_apply, zero_add, hself])) s
  apply continuous_of_local_continuous_action φ hself hcomp (fun x => (hφ x).continuous)
  intro x₀
  obtain ⟨U, hU, hx₀, ε, hε, β, hβcont, hβ⟩ :=
    exists_neighborhood_continuous_local_integralCurve (hv x₀)
  refine ⟨U, hU, hx₀, ε, hε, ?_⟩
  apply (hβcont.comp continuous_swap.continuousOn
    (fun p hp => ⟨hp.2, mem_univ p.1⟩)).congr
  intro p hp
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
    hv ((hφ p.2).isMIntegralCurveOn _) (hβ p.2 hp.2).2
    (by rw [hself, (hβ p.2 hp.2).1]) hp.1

end Global

section Nonautonomous

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ, F) ∞ Q]
  [CompleteSpace F] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Joint continuity in initial time, terminal time, and initial point of
actual solutions to a smooth time-dependent field. Time suspension reduces
the assertion to the proved autonomous dependence theorem. -/
theorem continuous_of_hasMFDerivAt
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    (Φ : ℝ → ℝ → Q → Q) (hself : ∀ s x, Φ s s x = x)
    (hΦ : ∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u => Φ s u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s t x)))) :
    Continuous (fun p : ℝ × (ℝ × Q) => Φ p.1 p.2.1 p.2.2) := by
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
  have hc := continuous_of_isMIntegralCurve
    ((contMDiff_timeSuspension hZ).of_le (by simp)) Ψ hΨself hΨ
  have hi : Continuous (fun p : ℝ × (ℝ × Q) =>
      (p.2.1 - p.1, (p.1, p.2.2))) := by fun_prop
  have he := continuous_snd.comp (hc.comp hi)
  simpa only [comp_def, Ψ, sub_add_cancel] using he

end Nonautonomous

/-- An evolution with the proved joint continuity and inverse identities
is a native homeomorphism at each pair of times. Its inverse is precisely
the same evolution with the two times exchanged. -/
def evolutionHomeomorph {Q : Type} [TopologicalSpace Q]
    (Φ : ℝ → ℝ → Q → Q)
    (hc : Continuous (fun p : ℝ × (ℝ × Q) => Φ p.1 p.2.1 p.2.2))
    (hinv : ∀ s t x, Φ t s (Φ s t x) = x) (s t : ℝ) : Q ≃ₜ Q where
  toEquiv := ⟨Φ s t, Φ t s, hinv s t, hinv t s⟩
  continuous_toFun := hc.comp (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))
  continuous_invFun := hc.comp (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))

end CollarFlow

namespace Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed collar velocity integrates to a jointly continuous
family of native homeomorphisms on the entire extension. The family fixes
the boundary, preserves the compact carrier exactly, and agrees on the
full smaller collar with the specified interpolation. The vector field,
solutions, support, and initial-point continuity are all produced from
the original completion data. The joint `C∞` upgrade is proved by
`exists_collarVelocity_globalSmoothHomeomorph` in
`CollarSmoothEvolution`. -/
theorem exists_collarVelocity_globalHomeomorph :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point))
        (H : ℝ → ℝ → E.domain.extension.Point ≃ₜ E.domain.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      Continuous (fun p : ℝ × (ℝ × E.domain.extension.Point) => H p.1 p.2.1 p.2.2) ∧
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
  obtain ⟨δ, hδ, Z, K, Φ, hZ, hK, hzero, hself, hΦ, hcomp, hinv, _,
    hsupport, hboundary, hcarrier, hcollar⟩ := C.exists_collarVelocity_globalEvolution C' h
  have hc := CollarFlow.continuous_of_hasMFDerivAt hZ Φ hself hΦ
  let H := CollarFlow.evolutionHomeomorph Φ hc hinv
  refine ⟨δ, hδ, Z, K, H, hZ, hK, hzero, hc, hself, hΦ, hcomp, ?_,
    hsupport, hboundary, hcarrier, hcollar⟩
  intro s t
  ext x
  rfl

end Completion
end FsFltz.Geometry
