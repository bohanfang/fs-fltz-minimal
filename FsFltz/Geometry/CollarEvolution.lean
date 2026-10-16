import FsFltz.Geometry.CollarFlow
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Uniform local integration and continuation of supported collar fields

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–189, and `sec:lean`,
lines 788–814. Quantitative Picard–Lindelöf bounds keep nearby initial-value
solutions in one chart and provide a common positive lifetime. A finite
cover makes that lifetime uniform on a compact set. The time suspension
has a uniform lifetime globally: use a compact enlarged time slab times
the spatial support, and straight time lines outside that set. Native
uniform-time continuation therefore gives all-real solutions of the
constructed supported collar field. Uniqueness gives the composition and
inverse identities, boundary fixing, compact spatial support, and agreement
with the prescribed interpolation on the full smaller collar.

Continuous time trajectories and the inverse identities also preserve the
compact carrier exactly. A trajectory meeting the frontier must be the
stationary boundary trajectory, by the inverse identity. A trajectory
starting off the frontier therefore avoids it. The preimage of the carrier
has empty frontier, hence is clopen in connected real time, so membership
is constant. This uses the domain's actual frontier and boundary inclusion;
it requires no globally defined boundary defining function.

`CollarSmoothEvolution` proves joint `C∞` dependence on both real times
and the initial point, then uses the evolution to correct compact
presentations and extend them to supplied completions. Coherent choices
for varying completions remain pending. These existence results do not
prove the target `thm:target`, lines 352–429.
-/

noncomputable section
open scoped Manifold ContDiff Classical NNReal
open Set Filter Topology Function Metric

namespace FsFltz.Geometry
namespace CollarFlow

private theorem exists_bounded_solution
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ → F → F} {a b : ℝ} {t₀ : Icc a b} {x₀ x : F} {R r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ R r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → F, α t₀ = x ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t) ∧
      ∀ t, α t ∈ closedBall x₀ R := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, fun _ => α.compProj_mem_closedBall hf.mul_max_le⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le) x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

section Local

variable {F H Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I 1 Q]

set_option backward.isDefEq.respectTransparency false in
/-- Nearby initial points have actual native integral curves on one common
positive time interval. The uniform lifetime and chart containment are
derived from Picard–Lindelöf bounds, rather than assumed. -/
theorem exists_neighborhood_uniform_local_integralCurve [CompleteSpace F]
    {v : (x : Q) → TangentSpace I x} {x₀ : Q}
    (hv : ContMDiffAt I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)) x₀) :
    ∃ U ∈ 𝓝 x₀, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ U,
      ∃ γ : ℝ → Q, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
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
  have hU : U ∈ 𝓝 x₀ := inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds _ (by
      exact NNReal.coe_pos.mpr (half_pos ha'))))
  refine ⟨U, hU, ε', hε', ?_⟩
  intro x hx
  obtain ⟨α, hα₀, hα, hαball⟩ := exists_bounded_solution hpl' (ball_subset_closedBall hx.2)
  have hαtarget (t : ℝ) : α t ∈ e.target := by
    apply hRt
    apply (closedBall_subset_ball (show (a' : ℝ) < R from
      lt_of_le_of_lt (NNReal.coe_le_coe.mpr (min_le_right _ _)) (half_lt_self hR)))
    exact hαball t
  refine ⟨e.symm ∘ α, by rw [comp_apply, hα₀, e.left_inv hx.1], ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (0 - ε') (0 + ε') := by simpa using ht
  let xₜ : Q := e.symm (α t)
  have hsrc : xₜ ∈ e.source := e.map_target (hαtarget t)
  have hself := mem_extChartAt_source (I := I) xₜ
  have hd : HasDerivAt α (f (α t)) t :=
    (hα t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' (hαtarget t)).comp hd.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ α) (v xₜ) t
  have he : f (α t) = tangentCoordChange I xₜ x₀ xₜ (v xₜ) := rfl
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hself,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hself, hsrc⟩, hself⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ (hd.congr_deriv he)
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ (by rw [I.range_eq_univ]; exact univ_mem)
  rw [← e.right_inv (hαtarget t)]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hsrc, hself⟩

private theorem exists_pos_le_on_finset {X : Type} (S : Finset X) (e : X → ℝ)
    (he : ∀ x, 0 < e x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ ≤ e x := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨δ, hδ, hle⟩ := ih
    refine ⟨min δ (e x), lt_min hδ (he x), ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle y hy)

/-- A compact set has one common local integration time. Its finite cover
uses the proved neighborhood-uniform producer, rather than pointwise
existence alone. -/
theorem exists_compact_uniform_local_integralCurve [CompleteSpace F]
    {v : (x : Q) → TangentSpace I x}
    (hv : ContMDiff I ((I).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle I Q)))
    {K : Set Q} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K,
      ∃ γ : ℝ → Q, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  have hlocal := fun x => exists_neighborhood_uniform_local_integralCurve (hv x)
  choose U hU e he H using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_on_finset S e he
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨γ, hγ₀, hγ⟩ := H y x hxy
  exact ⟨γ, hγ₀, hγ.mono (Ioo_subset_Ioo (neg_le_neg (hle y hy)) (hle y hy))⟩

end Local

section Supported

variable {F Q : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Q] [ChartedSpace F Q] [IsManifold 𝓘(ℝ, F) ∞ Q]
  [CompleteSpace F] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
omit [T2Space Q] in
/-- The time suspension has a uniform local lifetime on the entire
spacetime manifold. Compactness is used on an enlarged bounded time slab
times the spatial support. Off that set, explicit straight time lines solve
the equation for one unit of time. The suspension itself is not compactly
supported. -/
theorem exists_uniform_local_timeSuspension
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {K : Set (ℝ × Q)} (hK : IsCompact K) (hzero : ∀ p ∉ K, Z p.1 p.2 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℝ × Q,
      ∃ α : ℝ → ℝ × Q, α 0 = p ∧
        IsMIntegralCurveOn α (timeSuspension Z) (Ioo (-ε) ε) := by
  obtain ⟨B, hB⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  let T : ℝ := max B 0 + 1
  let L : Set Q := Prod.snd '' K
  have hL : IsCompact L := hK.image continuous_snd
  obtain ⟨ε₀, hε₀, H⟩ := exists_compact_uniform_local_integralCurve
    ((contMDiff_timeSuspension hZ).of_le (by simp)) (isCompact_Icc.prod hL)
  let ε := min ε₀ 1
  have hε : 0 < ε := lt_min hε₀ zero_lt_one
  refine ⟨ε, hε, ?_⟩
  intro p
  by_cases hp : p ∈ Icc (-T) T ×ˢ L
  · obtain ⟨α, hα₀, hα⟩ := H p hp
    exact ⟨α, hα₀, hα.mono (Ioo_subset_Ioo
      (neg_le_neg (min_le_left _ _)) (min_le_left _ _))⟩
  · have hlinezero : ∀ s ∈ Ioo (-ε) ε, Z (s + p.1) p.2 = 0 := by
      intro s hs
      apply hzero (s + p.1, p.2)
      intro hmem
      have hspace : p.2 ∈ L := ⟨(s + p.1, p.2), hmem, rfl⟩
      have htime : p.1 ∉ Icc (-T) T := fun ht => hp ⟨ht, hspace⟩
      have hbound : |s + p.1| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB _ ⟨(s + p.1, p.2), hmem, rfl⟩
      have hεone : ε ≤ 1 := min_le_right _ _
      have hBT : B ≤ max B 0 := le_max_left _ _
      have habs := abs_le.mp hbound
      simp only [mem_Icc, not_and_or, not_le] at htime
      rcases htime with htime | htime <;> dsimp only [T] at htime <;> linarith [hs.1, hs.2]
    refine ⟨fun s => (s + p.1, p.2), by simp, ?_⟩
    intro s hs
    have ht := hasMFDerivAt_iff_hasFDerivAt.mpr
      ((hasDerivAt_id s).add_const p.1).hasFDerivAt
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply (ht.prodMk (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, F)) p.2 s)).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change ℝ at r
    simp only [timeSuspension, hlinezero s hs, ContinuousLinearMap.prod_apply,
      zero_apply]
    change (r • (1 : ℝ), (0 : F)) = r • ((1 : ℝ), (0 : F))
    simp

set_option backward.isDefEq.respectTransparency false in
/-- A smooth field supported in a compact spacetime set has actual
solutions through every initial point for all real times. Native uniform
time continuation is applied only after the uniform lifetime has been
proved. Scalar uniqueness identifies the suspended time coordinate with
the original real time. -/
theorem exists_global_solution
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {K : Set (ℝ × Q)} (hK : IsCompact K) (hzero : ∀ p ∉ K, Z p.1 p.2 = 0)
    (t₀ : ℝ) (x₀ : Q) :
    ∃ γ : ℝ → Q, γ t₀ = x₀ ∧ ∀ t : ℝ,
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))) := by
  obtain ⟨ε, hε, H⟩ := exists_uniform_local_timeSuspension hZ hK hzero
  obtain ⟨α, hα₀, hα⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn
    ((contMDiff_timeSuspension hZ).of_le (by simp)) hε H (t₀, x₀)
  let β : ℝ → ℝ × Q := α ∘ (· - t₀)
  have hβ : IsMIntegralCurve β (timeSuspension Z) := isMIntegralCurve_comp_sub.mpr hα
  have hβ₀ : β t₀ = (t₀, x₀) := by simp only [β, comp_apply, sub_self, hα₀]
  have htime : ∀ t : ℝ, HasDerivAt (fun s => (β s).1) (1 : ℝ) t := by
    intro t
    have hf := (hasMFDerivAt_fst (β t)).comp t (hβ t)
    have hd := (hasMFDerivAt_iff_hasFDerivAt.mp hf).hasDerivAt
    apply hd.congr_deriv
    change (1 : ℝ) • (1 : ℝ) = 1
    simp
  have htimeEq : (fun s => (β s).1) = id := by
    apply ODE_solution_unique_univ (t₀ := t₀)
      (v := fun (_ : ℝ) (_ : ℝ) => (1 : ℝ)) (s := fun _ => univ) (K := 0)
      (fun _ => (LipschitzWith.const 1).lipschitzOnWith)
    · exact fun t => ⟨htime t, mem_univ _⟩
    · exact fun t => ⟨hasDerivAt_id t, mem_univ _⟩
    · exact congrArg Prod.fst hβ₀
  refine ⟨fun t => (β t).2, congrArg Prod.snd hβ₀, ?_⟩
  intro t
  have hs := (hasMFDerivAt_snd (β t)).comp t (hβ t)
  apply hs.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  simp [timeSuspension, congrFun htimeEq t]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace F] in
/-- The native uniqueness theorem also applies to all-real nonautonomous
solutions. This is used to compare the constructed global curves. -/
theorem eq_of_hasMFDerivAt
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {γ γ' : ℝ → Q} {t₀ : ℝ}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ t))))
    (hγ' : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (γ' t))))
    (heq : γ t₀ = γ' t₀) : γ = γ' := by
  have hl : IsMIntegralCurve (fun t => (t, γ t)) (timeSuspension Z) :=
    fun t => hasMFDerivAt_lift (hγ t)
  have hr : IsMIntegralCurve (fun t => (t, γ' t)) (timeSuspension Z) :=
    fun t => hasMFDerivAt_lift (hγ' t)
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := t₀)
    ((contMDiff_timeSuspension hZ).of_le (by simp)) hl hr (by simp only [heq])
  exact congrArg (fun f => fun t => (f t).2) he

set_option backward.isDefEq.respectTransparency false in
/-- Global existence and native uniqueness produce an actual two-time
evolution, with its composition law, inverse, and compact spatial support.
No continuity or smoothness in the initial point is asserted here. -/
theorem exists_global_evolution
    {Z : ℝ → (x : Q) → TangentSpace 𝓘(ℝ, F) x}
    (hZ : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, F) Q)))
    {K : Set (ℝ × Q)} (hK : IsCompact K) (hzero : ∀ p ∉ K, Z p.1 p.2 = 0) :
    ∃ Φ : ℝ → ℝ → Q → Q,
      (∀ s x, Φ s s x = x) ∧
      (∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u => Φ s u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s t x)))) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s t x, Φ t s (Φ s t x) = x) ∧
      (∀ s t, Function.Bijective (Φ s t)) ∧
      ∀ x ∉ Prod.snd '' K, ∀ s t, Φ s t x = x := by
  have H := fun s x => exists_global_solution hZ hK hzero s x
  choose γ hγ₀ hγ using H
  let Φ : ℝ → ℝ → Q → Q := fun s t x => γ s x t
  have hself : ∀ s x, Φ s s x = x := hγ₀
  have hcomp : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x := by
    intro s t u x
    exact congrFun (eq_of_hasMFDerivAt hZ (hγ t (Φ s t x)) (hγ s x)
      (by exact hγ₀ t (Φ s t x))) u
  have hinv : ∀ s t x, Φ t s (Φ s t x) = x := by
    intro s t x
    rw [hcomp, hself]
  refine ⟨Φ, hself, hγ, hcomp, hinv, ?_, ?_⟩
  · intro s t
    exact (Equiv.mk (Φ s t) (Φ t s) (hinv s t) (hinv t s)).bijective
  · intro x hx s t
    have hc : ∀ u, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun _ : ℝ => x) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u x)) := by
      intro u
      rw [hzero (u, x) (fun hp => hx ⟨(u, x), hp, rfl⟩)]
      simpa only [ContinuousLinearMap.smulRight_zero] using
        hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) x u
    exact congrFun (eq_of_hasMFDerivAt hZ (hγ s x) hc (hγ₀ s x)) t

end Supported

end CollarFlow

namespace CompactDomain

/-- An invertible evolution with continuous time trajectories and fixed
boundary preserves the compact carrier exactly. The proof uses connected
real time and the actual frontier; no global defining function or
initial-point continuity is required. -/
theorem mem_carrier_iff_of_continuous_evolution {d : ℕ} (D : CompactDomain d)
    (Φ : ℝ → ℝ → D.extension.Point → D.extension.Point)
    (hcontinuous : ∀ s x, Continuous (fun t => Φ s t x))
    (hself : ∀ s x, Φ s s x = x)
    (hinv : ∀ s t x, Φ t s (Φ s t x) = x)
    (hboundary : ∀ (s t : ℝ) (y : D.boundary.Point),
      Φ s t (D.boundaryInclusion.map y) = D.boundaryInclusion.map y)
    (s t : ℝ) (x : D.extension.Point) :
    Φ s t x ∈ D.carrier ↔ x ∈ D.carrier := by
  by_cases hx : x ∈ frontier D.carrier
  · rw [← D.boundary_range] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [hboundary]
  · let γ : ℝ → D.extension.Point := fun u => Φ s u x
    have havoid : ∀ u, γ u ∉ frontier D.carrier := by
      intro u hu
      have hrange : γ u ∈ Set.range D.boundaryInclusion.map := by
        rwa [D.boundary_range]
      obtain ⟨y, hy⟩ := hrange
      have he : γ u = x := by
        calc
          γ u = Φ u s (γ u) := by rw [← hy, hboundary]
          _ = x := hinv s u x
      exact hx (he ▸ hu)
    have hfrontier : frontier (γ ⁻¹' D.carrier) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact havoid u ((hcontinuous s x).frontier_preimage_subset D.carrier hu)
    have hclopen : IsClopen (γ ⁻¹' D.carrier) :=
      isClopen_iff_frontier_eq_empty.mpr hfrontier
    have hmem : γ t ∈ D.carrier ↔ γ s ∈ D.carrier := by
      change t ∈ γ ⁻¹' D.carrier ↔ s ∈ γ ⁻¹' D.carrier
      rcases isClopen_iff.mp hclopen with he | he <;> rw [he] <;> simp
    simpa only [γ, hself] using hmem

end CompactDomain

namespace Completion
open SmoothManifold

variable {d : ℕ} {D E : LiouvilleDomain d} (C : Completion D) (C' : Completion E)
  (h : DomainPresentationEquiv D.domain E.domain)

set_option backward.isDefEq.respectTransparency false in
/-- The actual supported collar field has a global, invertible evolution.
Its full smaller collar agrees with the prescribed interpolation at both
parameter endpoints, its boundary is fixed pointwise, and the compact
carrier is preserved exactly. This consumes
the cutoff producer and the all-real continuation theorem; an evolution
is not supplied among the hypotheses. The joint smooth upgrade is proved
by `exists_collarVelocity_globalSmoothHomeomorph` in
`CollarSmoothEvolution`. -/
theorem exists_collarVelocity_globalEvolution :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (Z : ℝ → (x : E.domain.extension.Point) → E.domain.extension.Tangent x)
        (K : Set (ℝ × E.domain.extension.Point))
        (Φ : ℝ → ℝ → E.domain.extension.Point → E.domain.extension.Point),
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ((𝓘(ℝ, Model d)).tangent) ∞
        (fun p : ℝ × E.domain.extension.Point =>
          (⟨p.2, Z p.1 p.2⟩ : TangentBundle 𝓘(ℝ, Model d) E.domain.extension.Point)) ∧
      IsCompact K ∧ (∀ p ∉ K, Z p.1 p.2 = 0) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s x t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun u => Φ s u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z t (Φ s t x)))) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s t x, Φ t s (Φ s t x) = x) ∧
      (∀ s t, Function.Bijective (Φ s t)) ∧
      (∀ x ∉ Prod.snd '' K, ∀ s t, Φ s t x = x) ∧
      (∀ (s t : ℝ) (x : E.domain.boundary.Point),
        Φ s t (E.domain.boundaryInclusion.map x) = E.domain.boundaryInclusion.map x) ∧
      (∀ s t x, Φ s t x ∈ E.domain.carrier ↔ x ∈ E.domain.carrier) ∧
      ∀ q ∈ univ ×ˢ Ioo (-δ) δ, ∀ t ∈ Icc (0 : ℝ) 1,
        Φ 0 t (C.compactPresentationInterpolation C' h (0, q)) =
          C.compactPresentationInterpolation C' h (t, q) := by
  obtain ⟨ε, hε, δ, hδ, Z, K, hZ, hK, hzero, hboundary, hode⟩ :=
    C.exists_compactlySupported_collarVelocity_open_time C' h
  obtain ⟨Φ, hself, hΦ, hcomp, hinv, hbij, hsupport⟩ :=
    CollarFlow.exists_global_evolution hZ hK hzero
  have hfix : ∀ (s t : ℝ) (x : E.domain.boundary.Point),
      Φ s t (E.domain.boundaryInclusion.map x) = E.domain.boundaryInclusion.map x := by
    intro s t x
    have hc : ∀ u, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d)
        (fun _ : ℝ => E.domain.boundaryInclusion.map x) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z u (E.domain.boundaryInclusion.map x))) := by
      intro u
      rw [hboundary]
      simpa only [ContinuousLinearMap.smulRight_zero] using
        hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Model d))
          (E.domain.boundaryInclusion.map x) u
    exact congrFun (CollarFlow.eq_of_hasMFDerivAt hZ (hΦ s _) hc (hself s _)) t
  have hcontinuous : ∀ s x, Continuous (fun t => Φ s t x) := by
    intro s x
    exact continuous_iff_continuousAt.mpr (fun t => (hΦ s x t).continuousAt)
  refine ⟨δ, hδ, Z, K, Φ, hZ, hK, hzero,
    hself, hΦ, hcomp, hinv, hbij, hsupport, hfix,
    E.domain.mem_carrier_iff_of_continuous_evolution Φ hcontinuous hself hinv hfix, ?_⟩
  intro q hq t ht
  exact C.eqOn_collarInterpolation_of_hasMFDerivAt C' h hZ hε hode hq
    (fun u _ => hΦ 0 _ u) (hself 0 _) ht

end Completion
end FsFltz.Geometry
