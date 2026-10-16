import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # A single smooth neighborhood for a globally smooth implicit equation

Pointwise `ContDiffAt ∞` alone does not supply a common smooth neighborhood.
The local uniqueness equation and the globally smooth defining function do.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A globally smooth implicit equation has one open neighborhood on which
its actual scalar implicit function is smooth, with a local uniqueness equation. -/
theorem exists_smooth_implicit_neighborhood {f : E × ℝ → ℝ} {a : E × ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hi : (fderiv ℝ f a ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible) :
    ∃ (r : E → ℝ) (U : Set E) (O : Set (E × ℝ)),
      IsOpen U ∧ a.1 ∈ U ∧ IsOpen O ∧ a ∈ O ∧
      ContDiffOn ℝ ∞ r U ∧ r a.1 = a.2 ∧
      (∀ x ∈ U, (x, r x) ∈ O ∧ f (x, r x) = f a) ∧
      (∀ z ∈ O, f z = f a ↔ r z.1 = z.2) := by
  let r := hf.contDiffAt.implicitFunction (by simp) hi
  have hr : ContDiffAt ℝ ∞ r a.1 :=
    hf.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hra : r a.1 = a.2 := hf.contDiffAt.implicitFunction_apply_self (by simp) hi
  have hpartial : Continuous (fun z => fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ E ℝ) :=
    (hf.continuous_fderiv (by simp)).clm_comp continuous_const
  have hevent : ∀ᶠ z in 𝓝 a,
      (f z = f a ↔ r z.1 = z.2) ∧
      (fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible :=
    (hf.contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp) hi).and
      (hpartial.tendsto a |>.eventually hi.eventually_nhds)
  obtain ⟨O, hOsub, hOopen, haO⟩ := mem_nhds_iff.mp hevent
  have hgraph : Tendsto (fun x => (x, r x)) (𝓝 a.1) (𝓝 a) := by
    simpa only [id_eq, hra, Prod.mk.eta] using
      (continuousAt_id.prodMk hr.continuousAt).tendsto
  have hnear : ∀ᶠ x in 𝓝 a.1, ContDiffAt ℝ 1 r x ∧ (x, r x) ∈ O :=
    ((hr.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).and
      (hgraph.eventually (hOopen.mem_nhds haO))
  obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hnear
  refine ⟨r, U, O, hUopen, haU, hOopen, haO, ?_, hra, ?_, ?_⟩
  · intro x hx
    have hxr := hUsub hx
    let z : E × ℝ := (x, r x)
    have hzi := (hOsub hxr.2).2
    let rx := hf.contDiffAt.implicitFunction (by simp) hzi
    have hxs : ContDiffAt ℝ ∞ rx x :=
      hf.contDiffAt.contDiffAt_implicitFunction (by simp) hzi
    have hrx : rx x = r x := hf.contDiffAt.implicitFunction_apply_self (by simp) hzi
    have ht : Tendsto (fun w => (w, rx w)) (𝓝 x) (𝓝 z) := by
      simpa only [id_eq, hrx, z] using (continuousAt_id.prodMk hxs.continuousAt).tendsto
    have heq : r =ᶠ[𝓝 x] rx := by
      filter_upwards [ht.eventually (hOopen.mem_nhds hxr.2),
        hf.contDiffAt.eventually_apply_implicitFunction (by simp) hzi] with w hw hf'
      exact (hOsub hw).1.mp (hf'.trans ((hOsub hxr.2).1.mpr rfl))
    exact (hxs.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro x hx
    exact ⟨(hUsub hx).2, (hOsub (hUsub hx).2).1.mpr rfl⟩
  · intro z hz
    exact (hOsub hz).1

end FsFltz
