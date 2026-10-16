import FsFltz.Geometry.IntrinsicExteriorDerivative
import FsFltz.Geometry.IntrinsicLiouvilleExtension

/-!
# Smoothness and square-zero for the native exterior derivative

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions and
`def:pair`, lines 119–160, and `sec:lean`, lines 783–814. The actual native
derivative preserves smooth open extension germs and squares to zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The coordinate derivative of a locally extendible form is itself locally
extendible. Its smooth germ is obtained by differentiating the same source
germ, rather than supplied as separate regularity data. -/
theorem isLocallyExtendibleForm_of_hasExteriorDerivative {r : ℕ}
    {α : Form k M r} {omega : Form k M (r + 1)}
    (hα : IsLocallyExtendibleForm α) (hd : HasExteriorDerivative α omega) :
    IsLocallyExtendibleForm omega := by
  intro e he x hx
  obtain ⟨β, U, hU, hxU, hβ, hag⟩ := hα e he x hx
  obtain ⟨hD, hDag⟩ := exists_exteriorDerivative_extension he hd hU hxU hβ hag
  exact ⟨extDeriv β, U, hU, hxU, hD, hDag⟩

/-- The form-determined native exterior derivative preserves local smooth
extension across the boundary. -/
theorem isLocallyExtendibleForm_exteriorDerivative {r : ℕ}
    (α : Form k M r) (hα : IsLocallyExtendibleForm α) :
    IsLocallyExtendibleForm (exteriorDerivative α) :=
  isLocallyExtendibleForm_of_hasExteriorDerivative hα
    (hasExteriorDerivative_exteriorDerivative α hα)

/-- The actual native exterior derivative squares to zero, including on the
boundary. Both derivatives are computed from the same smooth extension germ. -/
theorem exteriorDerivative_exteriorDerivative {r : ℕ}
    (α : Form k M r) (hα : IsLocallyExtendibleForm α) :
    exteriorDerivative (exteriorDerivative α) = 0 := by
  funext x
  let e := chartAt (EuclideanHalfSpace (k + 1)) x
  have he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M := chart_mem_atlas _ x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hy : e.extend (𝓡∂ (k + 1)) x ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  obtain ⟨β, U, hU, hxU, hβ, hag⟩ := hα e he x hx
  obtain ⟨hD, hDag⟩ := exists_exteriorDerivative_extension he
    (hasExteriorDerivative_exteriorDerivative α hα) hU hxU hβ hag
  have hDa : DifferentiableAt ℝ (extDeriv β) (e.extend (𝓡∂ (k + 1)) x) :=
    (hD.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  change (extDerivWithin (formInChart e (exteriorDerivative α))
    (e.extend (𝓡∂ (k + 1))).target (e.extend (𝓡∂ (k + 1)) x)).compContinuousLinearMap
      (chartTangentMap e x) = 0
  rw [extDerivWithin_eq_extension hy hDa hDag,
    extDeriv_extDeriv_apply (hβ.contDiffAt (hU.mem_nhds hxU)) (by simp)]
  apply ContinuousAlternatingMap.ext
  intro vs
  rfl

end FsFltz.Geometry.IntrinsicLiouville
