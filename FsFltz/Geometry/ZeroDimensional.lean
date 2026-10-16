import FsFltz.Geometry.FlowBridge
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# Full cores of zero-dimensional ribbons

The actual complete flow in dimension zero is stationary. Consequently its
full core is the entire compact domain, as required by `def:pair`, lines
159–160, and the rank-one check in `sec:lean`, lines 825–830, of
`geoemtric-part-fsf.tex`. No identity-flow hypothesis is supplied.
-/

noncomputable section
open scoped Manifold ContDiff

namespace FsFltz.Geometry
open SmoothManifold

/-- A native zero-dimensional compact domain is a finite set. -/
theorem CompactDomain.finite_of_dimension_zero (D : CompactDomain 0) :
    D.carrier.Finite := by
  let : Subsingleton (Model 0) := ⟨fun _ _ => PiLp.ext (fun i => Fin.elim0 i)⟩
  let : DiscreteTopology (Model 0) := inferInstance
  let : DiscreteTopology D.extension.Point :=
    ChartedSpace.discreteTopology (Model 0) D.extension.Point
  exact D.compact.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)

/-- A zero-dimensional completed Liouville manifold has stationary flow. -/
theorem CompleteLiouvilleManifold.flow_eq_self_of_dimension_zero
    (X : CompleteLiouvilleManifold 0) (t : ℝ) (x : X.manifold.Point) :
    X.completeFlow.flow t x = x := by
  have hz : X.field x = 0 := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (X.smooth_field.contMDiff_section.of_le (by simp))
    (X.completeFlow.isMIntegralCurve x) (isMIntegralCurve_const hz)
    (by simp only [Flow.map_zero_apply])
  exact congrFun heq t

/-- In dimension zero the full intrinsic completion core is the whole domain. -/
theorem Completion.core_eq_carrier_of_dimension_zero
    {D : LiouvilleDomain 0} (C : Completion D) : C.core = D.domain.carrier := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx, fun t _ => ?_⟩
    rw [C.ambient.flow_eq_self_of_dimension_zero]
    exact ⟨x, hx, rfl⟩

/-- The embedded full core of a rank-one pair is its entire embedded ribbon. -/
theorem WitnessedPair.embeddedCore_eq_ribbon_of_rank_one (P : WitnessedPair 1) :
    P.embeddedCore = P.ribbonEmbedding.map '' P.ribbonDomain.domain.carrier := by
  unfold WitnessedPair.embeddedCore
  rw [Completion.core_eq_carrier_of_dimension_zero]

end FsFltz.Geometry
