import FsFltz.Geometry.TailoringCompletedGradingWeight
import FsFltz.Geometry.CompletionDynamics

/-!
# Smooth compression of an actual cylindrical completion into its compact part

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`geometric-part-fsf-proof.tex`, `lem:grading`, lines 1994–2089.
The explicit cylindrical weight gives a smooth variable negative flow time
which sends every completed point into the compact carrier. This supplies
the geometric input for comparing grading classes from compact data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.LiouvilleDomain.FlowCollar
open SmoothManifold

variable {d : ℕ} {D : LiouvilleDomain d} (C : FlowCollar D)

/-- A smooth negative-flow compression, defined at every real parameter. -/
def compactCompression (t : ℝ) (z : C.cylindricalCompletion.ambient.manifold.Point) :
    C.cylindricalCompletion.ambient.manifold.Point :=
  C.cylindricalCompletion.ambient.completeFlow.flow
    (-t * (Real.log (C.radialWeight z.val) + C.width)) z

@[simp] theorem compactCompression_zero (z : C.cylindricalCompletion.ambient.manifold.Point) :
    C.compactCompression 0 z = z := by
  simp [compactCompression]

/-- The compression is jointly smooth, including at both endpoints. -/
theorem compactCompression_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
      (fun p : ℝ × C.cylindricalCompletion.ambient.manifold.Point =>
        C.compactCompression p.1 p.2) := by
  have hw : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞
      (fun z : C.cylindricalCompletion.ambient.manifold.Point => Real.log (C.radialWeight z.val)) :=
    fun z => (Real.contDiffAt_log.mpr (C.radialWeight_positive z.val).ne').contMDiffAt.comp z
      (C.smooth_radialWeight z)
  exact C.cylindricalCompletion.ambient.completeFlow.smooth_action.comp
    ((contMDiff_fst.neg.mul ((hw.comp contMDiff_snd).add contMDiff_const)).prodMk contMDiff_snd)

/-- At parameter one every point lies in the actual compact carrier. -/
theorem compactCompression_one_mem (z : C.cylindricalCompletion.ambient.manifold.Point) :
    C.compactCompression 1 z ∈ C.localizedDomain.domain.carrier := by
  let E := C.cylindricalCompletion
  have hinc : E.inclusion.map '' C.localizedDomain.domain.carrier =
      C.localizedDomain.domain.carrier := by
    change id '' _ = _
    exact image_id _
  have hcover : z ∈ E.inclusion.map '' C.localizedDomain.domain.carrier ∪
      E.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
    rw [E.covering]
    exact mem_univ _
  rcases hcover with hcompact | hend
  · have hz : z ∈ C.localizedDomain.domain.carrier := by
      simpa only [hinc] using hcompact
    have hw : C.radialWeight z.val = 1 := C.radialWeight_carrier z.val hz
    have hm := E.negative_flow_mem hcompact C.positive_width.le
    rw [hinc] at hm
    simpa only [compactCompression, hw, Real.log_one, zero_add, neg_mul, one_mul] using hm
  · obtain ⟨⟨x, r⟩, hr, rfl⟩ := hend
    have htime : -(Real.log (C.radialWeight (E.endMap (x, r)).val) + C.width) + r =
        CollarStretch.inverse C.positive_width r - C.width := by
      rw [C.radialWeight_cylindricalEnd x r hr.2, Real.log_exp]
      ring
    have hb : E.inclusion.map (C.localizedDomain.domain.boundaryInclusion.map x) ∈
        E.inclusion.map '' C.localizedDomain.domain.carrier :=
      mem_image_of_mem _ (C.localizedDomain.domain.boundaryInclusion_mem_carrier x)
    have hm := E.negative_flow_mem hb
      (sub_nonneg.mpr (CollarStretch.inverse_lt C.positive_width r).le)
    change C.cylindricalCompletion.ambient.completeFlow.flow
      (-1 * (Real.log (C.radialWeight (E.endMap (x, r)).val) + C.width))
      (E.endMap (x, r)) ∈ _
    have hf := E.end_flow x r
    rw [hf] at htime
    rw [neg_one_mul, hf, ← Flow.map_add, htime]
    have he : CollarStretch.inverse C.positive_width r - C.width =
        -(C.width - CollarStretch.inverse C.positive_width r) := by ring
    rw [he]
    rwa [hinc] at hm

end FsFltz.Geometry.LiouvilleDomain.FlowCollar
