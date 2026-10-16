import FsFltz.Geometry.TailoringHittingCompletionFlow
import FsFltz.Geometry.BoundaryContact

/-!
# The whole-ribbon boundary map at the strict tailoring junction

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1905.
The boundary representative and shift are derived from the actual inclusion
marking and the regional native hitting trajectory. The assertions hold on
every compact ribbon point, rather than merely on the intrinsic core.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold

/-- A marked rounded completion and a regional native hit determine the
same actual boundary representative on the entire ribbon. The smooth shift
is minus the forward hitting time. -/
theorem LiouvilleDomain.FlowCollar.exists_boundaryEquiv_of_regional_cutoff_ribbon_hits
    {n : ℕ} (P : WitnessedPair n) {D : LiouvilleDomain (2 * n)}
    (C : D.FlowCollar)
    (i : P.ambientDomain.domain.Point → C.cylindricalCompletion.ambient.manifold.Point)
    (q : InclusionMarking P.ambientCompletion C.cylindricalCompletion.ambient i)
    (M : SmoothManifold (2 * n)) (e : D.domain.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hprimitive : D.liouville.primitive = D.domain.extension.pullback M e.map α)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    (A k : ℝ) (himage : e.map '' D.domain.carrier = {y | ρ y ≤ A})
    (hnd : ∀ y, ρ y ≤ A → M.Nondegenerate (M.exteriorDerivative α) y)
    (G : Flow ℝ (ℝ × M.Point))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × M.Point) => G p.1 p.2))
    (hnative : ∀ y t, ρ (G t (k, y)).2 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2) (M.liouvilleVector α) t)
    (hout : ∀ y, ρ y = A → 0 < M.scalarDerivative ρ y (M.liouvilleVector α y))
    (j : P.ribbonDomain.domain.extension.Point → D.domain.boundary.Point)
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (start : P.ribbonDomain.domain.extension.Point → M.Point)
    (hstart : ∀ x ∈ P.ribbonDomain.domain.carrier,
      e.map (C.originalInclusion.map
        (i ⟨P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x),
          P.ambientDomain.domain.boundaryInclusion_mem_carrier (P.ribbonEmbedding.map x)⟩)) =
        start x)
    (htime : ∀ x ∈ P.ribbonDomain.domain.carrier, 0 < τ x)
    (hboundary : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ρ (e.map (D.domain.boundaryInclusion.map (j x))) = A)
    (hhit : ∀ x ∈ P.ribbonDomain.domain.carrier,
      (G (τ x) (k, start x)).2 = e.map (D.domain.boundaryInclusion.map (j x))) :
    ∃ ψ : P.ambientDomain.domain.boundary.SmoothEquiv D.domain.boundary,
      ∃ s : P.ambientDomain.domain.boundary.Point → ℝ,
        ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s ∧
        (∀ b r, q.equiv (P.ambientCompletion.endMap (b, r)) =
          C.cylindricalCompletion.endMap (ψ b, r + s b)) ∧
        P.ambientDomain.domain.boundary.pullback D.domain.boundary ψ
          (D.domain.boundaryForm D.liouville.primitive) =
          (fun b => Real.exp (-s b) •
            P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive b) ∧
        ∀ x ∈ P.ribbonDomain.domain.carrier,
          ψ (P.ribbonEmbedding.map x) = j x ∧ s (P.ribbonEmbedding.map x) = -τ x := by
  obtain ⟨ψ, s, hs, hend, hcontact⟩ := P.ambientCompletion.exists_boundaryEquiv_with_pullback
    C.cylindricalCompletion q.equiv q.primitive
  rw [C.localized_boundaryForm] at hcontact
  refine ⟨ψ, s, hs, hend, hcontact, ?_⟩
  intro x hx
  let z := i ⟨P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x),
    P.ambientDomain.domain.boundaryInclusion_mem_carrier (P.ribbonEmbedding.map x)⟩
  have hz : (G (τ x) (k, e.map (C.originalInclusion.map z))).2 =
      e.map (D.domain.boundaryInclusion.map (j x)) := by
    rw [hstart x hx]
    exact hhit x hx
  have hcompleted := C.regional_cutoff_hitting_eq_completed_end M e α hα hprimitive
    ρ hρ A k himage hnd G hG hnative hout (htime x hx) z (j x) (hboundary x hx) hz
  have hq : q.equiv (P.ambientCompletion.endMap (P.ribbonEmbedding.map x, 0)) = z := by
    rw [P.ambientCompletion.endMap_zero]
    exact q.inclusion ⟨P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x),
      P.ambientDomain.domain.boundaryInclusion_mem_carrier (P.ribbonEmbedding.map x)⟩
  have hcoordinates := hend (P.ribbonEmbedding.map x) 0
  rw [zero_add] at hcoordinates
  exact (C.cylindricalCompletion.endMap_eq_iff
    (ψ (P.ribbonEmbedding.map x)) (j x) (s (P.ribbonEmbedding.map x)) (-τ x)).mp
    (hcoordinates.symm.trans (hq.trans hcompleted.2))

end FsFltz.Geometry
