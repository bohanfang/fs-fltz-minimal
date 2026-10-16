import FsFltz.Geometry.IntrinsicBoundary
import FsFltz.Geometry.BoundaryNondegeneracy
import FsFltz.Geometry.LocalInverse

/-!
# Local invertibility of a transverse intrinsic collar map

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. The local collar differential is computed from
its actual seam identity and time derivative. Strict normal transversality
proves invertibility; no invertible-differential certificate is an input.
This coordinate result does not construct a compact uniform collar or a
completion gluing.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
namespace IntrinsicCollar

/-- The normal flow velocity and boundary tangent directions form the
actual differential of the collar map at its seam. -/
def differential (k : ℕ) (w : Model (k + 1)) :
    ℝ × Model k →L[ℝ] Model (k + 1) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight w).coprod (boundaryInsert k)

@[simp] theorem differential_apply {k : ℕ} (w : Model (k + 1)) (q : ℝ × Model k) :
    differential k w q = q.1 • w + boundaryInsert k q.2 := rfl

/-- A local seam identity fixes the tangential derivative; the genuine
time derivative fixes the normal derivative. Together they determine the
total derivative, including for a zero-dimensional boundary model. -/
theorem fderiv_eq_differential {k : ℕ}
    {c : ℝ × Model k → Model (k + 1)} {u : Model k} {w : Model (k + 1)}
    (hc : DifferentiableAt ℝ c (0, u))
    (hseam : (fun v => c (0, v)) =ᶠ[𝓝 u] boundaryInsert k)
    (htime : HasDerivAt (fun t => c (t, u)) w 0) :
    fderiv ℝ c (0, u) = differential k w := by
  let L := fderiv ℝ c (0, u)
  have hinr : HasFDerivAt (fun v : Model k => ((0 : ℝ), v))
      (ContinuousLinearMap.inr ℝ ℝ (Model k)) u := by
    convert (hasFDerivAt_const (0 : ℝ) u).prodMk (hasFDerivAt_id u) using 1 <;> rfl
  have hinl : HasFDerivAt (fun t : ℝ => (t, u))
      (ContinuousLinearMap.inl ℝ ℝ (Model k)) 0 := by
    convert (hasFDerivAt_id (0 : ℝ)).prodMk (hasFDerivAt_const u (0 : ℝ)) using 1 <;> rfl
  have hLr : L.comp (ContinuousLinearMap.inr ℝ ℝ (Model k)) = boundaryInsert k :=
    (hc.hasFDerivAt.comp u hinr).unique
      ((boundaryInsert k).hasFDerivAt.congr_of_eventuallyEq hseam)
  have hLl : L.comp (ContinuousLinearMap.inl ℝ ℝ (Model k)) =
      ContinuousLinearMap.toSpanSingleton ℝ w :=
    (hc.hasFDerivAt.comp 0 hinl).unique htime.hasFDerivAt
  apply ContinuousLinearMap.ext
  intro q
  change L q = q.1 • w + boundaryInsert k q.2
  have hsplit : q = (q.1, 0) + (0, q.2) := by ext <;> simp
  conv_lhs => rw [hsplit, map_add]
  have hl := congrArg (fun A : ℝ →L[ℝ] Model (k + 1) => A q.1) hLl
  have hr := congrArg (fun A : Model k →L[ℝ] Model (k + 1) => A q.2) hLr
  exact congrArg₂ (fun x y => x + y) hl hr

/-- Nonzero normal velocity is sufficient for invertibility. The spanning
lemma uses the actual boundary inclusion and its first-coordinate kernel. -/
theorem differential_bijective {k : ℕ} (w : Model (k + 1)) (hw : w 0 ≠ 0) :
    Function.Bijective (differential k w) := by
  have hi : Function.Injective (boundaryInsert k).toLinearMap := by
    intro v v' h
    have h' := congrArg (boundaryDrop k) h
    simpa using h'
  let p : Model (k + 1) →ₗ[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin (k + 1) => ℝ) 0).toLinearMap
  have hbij := tangent_prod_span_bijective (boundaryInsert k).toLinearMap p w hi
    (fun v => boundaryInsert_zero v) hw
    (by simp only [finrank_euclideanSpace_fin])
  have hswap := hbij.comp (LinearEquiv.prodComm ℝ ℝ (Model k)).bijective
  convert hswap using 1
  funext q
  exact add_comm _ _

/-- A smooth map with the genuine boundary seam and positive normal flow
velocity has a smooth local inverse. Invertibility is proved from the seam
and transversality, rather than supplied as an input hypothesis. -/
theorem isLocalDiffeomorphAt_of_seam_transverse {k : ℕ}
    {c : ℝ × Model k → Model (k + 1)} {U : Set (ℝ × Model k)}
    {u : Model k} {w : Model (k + 1)}
    (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c U) (hu : (0, u) ∈ U)
    (hseam : (fun v => c (0, v)) =ᶠ[𝓝 u] boundaryInsert k)
    (htime : HasDerivAt (fun t => c (t, u)) w 0) (hw : 0 < w 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞ c (0, u) := by
  apply isLocalDiffeomorphAt_of_bijective_mfderiv_manifold hU hc.contMDiffOn hu
  rw [mfderiv_eq_fderiv, fderiv_eq_differential
    ((hc.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)) hseam htime]
  exact differential_bijective w (ne_of_gt hw)

end IntrinsicCollar
end FsFltz.Geometry
