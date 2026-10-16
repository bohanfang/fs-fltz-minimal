import FsFltz.Geometry.TailoringStrictHittingBoundary
import FsFltz.Geometry.WitnessInterpolation

/-!
# The incoming strict-junction witness and its actual interpolation

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1896–1913.
The actual boundary shift constructs the incoming positive factor. Its
agreement with the constructed hitting witness is proved on the full compact
ribbon, so logarithmic interpolation is an actual pair deformation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
namespace WitnessedPair

/-- The incoming witness is the exponential of the actual strict end shift,
written in the target boundary section. -/
def strictIncomingWitness {n : ℕ} (P Q : WitnessedPair n)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (y : Q.ambientDomain.domain.boundary.Point) : ℝ := Real.exp (s (ψ.symm y))

theorem strictIncomingWitness_smooth {n : ℕ} (P Q : WitnessedPair n)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (hs : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s) :
    ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ (P.strictIncomingWitness Q ψ s) :=
  Real.contDiff_exp.contMDiff.comp (hs.comp ψ.symm.contMDiff)

theorem strictIncomingWitness_positive {n : ℕ} (P Q : WitnessedPair n)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (y : Q.ambientDomain.domain.boundary.Point) : 0 < P.strictIncomingWitness Q ψ s y :=
  Real.exp_pos _

/-- The negative hitting-time restriction and the actual whole-ribbon square
force the two globally positive witnesses to agree on every ribbon point.
No equality of intrinsic cores is used. -/
theorem strictIncomingWitness_eq_on_ribbon {n : ℕ} (P Q : WitnessedPair n)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (h : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (h.map x))
    (hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x)
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      Q.witness (Q.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x)) :
    ∀ y ∈ Q.ribbonDomain.domain.carrier,
      P.strictIncomingWitness Q ψ s (Q.ribbonEmbedding.map y) =
        Q.witness (Q.ribbonEmbedding.map y) := by
  intro y hy
  let x := h.inverse y
  have hx : x ∈ P.ribbonDomain.domain.carrier := h.maps_target hy
  have hh : h.map x = y := h.right_inverse y hy
  have hsquare' : Q.ribbonEmbedding.map y = ψ (P.ribbonEmbedding.map x) := by
    rw [← hh]
    exact (hsquare x hx).symm
  change Real.exp (s (ψ.symm (Q.ribbonEmbedding.map y))) = _
  rw [hsquare', ψ.symm_apply_apply, hshift x hx]
  exact (hwitness x hx).symm.trans (congrArg Q.witness (hsquare x hx).symm)

/-- Construct the actual positive-witness deformation. Its reverse is the
source's incoming-to-hitting interpolation; every ribbon primitive and both
completed ambients stay fixed throughout this very family. -/
def strictIncomingWitnessDeformation {n : ℕ} (P Q : WitnessedPair n)
    (ψ : P.ambientDomain.domain.boundary.SmoothEquiv Q.ambientDomain.domain.boundary)
    (s : P.ambientDomain.domain.boundary.Point → ℝ)
    (hs : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s)
    (h : CompactDomainDiffeomorph P.ribbonDomain.domain Q.ribbonDomain.domain)
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (h.map x))
    (hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x)
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      Q.witness (Q.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x)) : PairDeformation n :=
  Q.witnessDeformation (P.strictIncomingWitness Q ψ s)
    (P.strictIncomingWitness_smooth Q ψ s hs) (P.strictIncomingWitness_positive Q ψ s)
    (P.strictIncomingWitness_eq_on_ribbon Q ψ s h τ hsquare hshift hwitness)

end WitnessedPair
end FsFltz.Geometry
