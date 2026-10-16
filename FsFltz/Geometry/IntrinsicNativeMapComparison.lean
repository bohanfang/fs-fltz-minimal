import FsFltz.Geometry.IntrinsicNativeMapCompletion
import FsFltz.Geometry.ScaledLiouvilleFlowTransport

/-!
# Native prescribed maps with constructed presentations and completions

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–189, and
`sec:lean`, lines 803–814. Original native primitive germs, symplecticity
and outwardness independently construct the two spatial presentations.
Their actual Liouville collars construct the completions. The prescribed
native map then extends to a completed equivalence retaining its map and
inverse on the entire compact carriers, its full primitive scale, and the
original completion boundary and same-radius end maps. The primitive
equation determines transport of the actual fields, complete flows and
full native cores along that same completed equivalence.

No presentation, completion or ambient equivalence is a headline input.
These positive-dimensional foundations assert no geometric comparison
chain, endpoint core equality, grading or full-fiber marking.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (k + 1)) N]

namespace NativeLiouvillePresentation

/-- A native compact square and equivariance of the actual complete flows
transport the full native core. Surjectivity of the native map transports
the entire compact carrier, so the confinement statement concerns every
nonnegative real time. -/
theorem core_transport_of_native_square
    {α : Form k M 1} {β : Form k N 1}
    (P : NativeLiouvillePresentation α) (Q : NativeLiouvillePresentation β)
    (C : Completion P.domain) (C' : Completion Q.domain) (h : M ≃ N)
    (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hsquare : ∀ x, e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x)))
    (hflow : ∀ z t, e (C.ambient.completeFlow.flow t z) = C'.ambient.completeFlow.flow t (e z))
    (x : M) : P.inclusion x ∈ C.core ↔ Q.inclusion (h x) ∈ C'.core := by
  have hP : C.inclusion.map '' P.domain.domain.carrier =
      range (fun z => C.inclusion.map (P.inclusion z)) := by
    rw [← P.carrier_range, ← range_comp']
  have hQ : C'.inclusion.map '' Q.domain.domain.carrier =
      range (fun z => C'.inclusion.map (Q.inclusion z)) := by
    rw [← Q.carrier_range, ← range_comp']
  have hx : P.inclusion x ∈ P.domain.domain.carrier := P.carrier_range ▸ mem_range_self x
  have hy : Q.inclusion (h x) ∈ Q.domain.domain.carrier := Q.carrier_range ▸ mem_range_self (h x)
  have ht (t : ℝ) : e (C.ambient.completeFlow.flow t (C.inclusion.map (P.inclusion x))) =
      C'.ambient.completeFlow.flow t (C'.inclusion.map (Q.inclusion (h x))) := by
    rw [hflow, hsquare]
  change (P.inclusion x ∈ P.domain.domain.carrier ∧ _) ↔
    (Q.inclusion (h x) ∈ Q.domain.domain.carrier ∧ _)
  rw [hP, hQ]
  simp only [hx, hy, true_and]
  constructor
  · intro hc t ht'
    obtain ⟨z, hz⟩ := hc t ht'
    exact ⟨h z, (hsquare z).symm.trans ((congrArg e hz).trans (ht t))⟩
  · intro hc t ht'
    obtain ⟨z, hz⟩ := hc t ht'
    refine ⟨h.symm z, e.injective ?_⟩
    change e (C.inclusion.map (P.inclusion (h.symm z))) =
      e (C.ambient.completeFlow.flow t (C.inclusion.map (P.inclusion x)))
    rw [hsquare, h.apply_symm_apply, ht]
    exact hz

end NativeLiouvillePresentation

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N] [IsManifold (𝓡∂ (k + 1)) ∞ N]

/-- Original native Liouville data and a prescribed positive constant-scale
native diffeomorphism construct both independent presentations, their actual
completions and the completed comparison. The returned compact squares
retain the specified map and its native inverse, and the same completed
map transports the actual fields, all-real-time flows and full native core. -/
theorem exists_scaledNativeCompletionComparison
    (α : Form k M 1) (β : Form k N 1)
    (hα : IsLocallyExtendibleForm α) (hβ : IsLocallyExtendibleForm β)
    (hndα : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hndβ : ∀ y, Nondegenerate (exteriorDerivative β) y)
    (houtα : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (houtβ : ∀ x : IntrinsicBoundary.Point k N,
      ∃ (rho : N → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector β (exteriorDerivative β) x.val)))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (c : ℝ) (hc : 0 < c)
    (hscale : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = c • α x) :
    ∃ (P : NativeLiouvillePresentation (k := k) α) (Q : NativeLiouvillePresentation (k := k) β)
      (C : Completion P.domain) (C' : Completion Q.domain)
      (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        c • C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x))) ∧
      (∀ y : N, e.symm (C'.inclusion.map (Q.inclusion y)) =
        C.inclusion.map (P.inclusion (h.symm y))) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        C'.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) ∧
      (∀ z, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) e z
        (C.ambient.field z) = C'.ambient.field (e z)) ∧
      (∀ z t, e (C.ambient.completeFlow.flow t z) = C'.ambient.completeFlow.flow t (e z)) ∧
      (∀ x, P.inclusion x ∈ C.core ↔ Q.inclusion (h x) ∈ C'.core) := by
  obtain ⟨P⟩ := exists_nativeLiouvillePresentation α hα hndα houtα
  obtain ⟨Q⟩ := exists_nativeLiouvillePresentation β hβ hndβ houtβ
  obtain ⟨e, b, hp, hsquare, hinverse, hboundary, hend⟩ :=
    P.exists_scaledConstructedCompletionEquiv_of_nativeDiffeomorph Q h hgerm c hc hscale
  have hflow := P.localizedCompletion.ambient.map_flow_of_scaled_primitive
    Q.localizedCompletion.ambient e c hp
  refine ⟨P.localized, Q.localized, P.localizedCompletion, Q.localizedCompletion,
    e, b, hp, hsquare, hinverse, hboundary, hend, ?_, hflow, ?_⟩
  · exact P.localizedCompletion.ambient.map_field_of_scaled_primitive
      Q.localizedCompletion.ambient e c hp
  · exact P.localized.core_transport_of_native_square Q.localized
      P.localizedCompletion Q.localizedCompletion h.toEquiv e hsquare hflow

/-- Primitive-preserving original native data construct a strict completed
comparison, together with its actual independent presentations and
completions. Every compact, inverse, boundary and end formula refers to the
same prescribed native map and the same returned completions. -/
theorem exists_strictNativeCompletionComparison
    (α : Form k M 1) (β : Form k N 1)
    (hα : IsLocallyExtendibleForm α) (hβ : IsLocallyExtendibleForm β)
    (hndα : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hndβ : ∀ y, Nondegenerate (exteriorDerivative β) y)
    (houtα : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val)))
    (houtβ : ∀ x : IntrinsicBoundary.Point k N,
      ∃ (rho : N → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector β (exteriorDerivative β) x.val)))
    (h : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M N ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := k) h)
    (hprimitive : ∀ x, (β (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) h x) = α x) :
    ∃ (P : NativeLiouvillePresentation (k := k) α) (Q : NativeLiouvillePresentation (k := k) β)
      (C : Completion P.domain) (C' : Completion Q.domain)
      (e : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
      (b : P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary),
      C.ambient.manifold.pullback C'.ambient.manifold e C'.ambient.primitive =
        C.ambient.primitive ∧
      (∀ x : M, e (C.inclusion.map (P.inclusion x)) = C'.inclusion.map (Q.inclusion (h x))) ∧
      (∀ y : N, e.symm (C'.inclusion.map (Q.inclusion y)) =
        C.inclusion.map (P.inclusion (h.symm y))) ∧
      (∀ x, e (C.inclusion.map (P.domain.domain.boundaryInclusion.map x)) =
        C'.inclusion.map (Q.domain.domain.boundaryInclusion.map (b x))) ∧
      (∀ x r, 0 ≤ r → e (C.endMap (x, r)) = C'.endMap (b x, r)) ∧
      (∀ z, mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) e z
        (C.ambient.field z) = C'.ambient.field (e z)) ∧
      (∀ z t, e (C.ambient.completeFlow.flow t z) = C'.ambient.completeFlow.flow t (e z)) ∧
      (∀ x, P.inclusion x ∈ C.core ↔ Q.inclusion (h x) ∈ C'.core) := by
  simpa only [one_smul] using exists_scaledNativeCompletionComparison α β hα hβ hndα hndβ
    houtα houtβ h hgerm 1 (by norm_num) (by simpa only [one_smul] using hprimitive)

end FsFltz.Geometry.IntrinsicLiouville
