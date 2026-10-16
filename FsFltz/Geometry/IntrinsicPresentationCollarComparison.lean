import FsFltz.Geometry.IntrinsicCompletionField
import FsFltz.Geometry.IntrinsicBoundaryPresentation
import FsFltz.Geometry.CompletionCollarExtension
import FsFltz.Geometry.SmoothIntegralCurveRightUniqueness

/-!
# Native identity and the actual completion collars

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–158,
`def:chain`, lines 171–189, and `sec:lean`, lines 805–813.
The boundary map and field equations below are consequences of the original
native presentation, rather than additional inclusion-extension inputs.
They feed the radius-preserving comparison of actual completion collars.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation
open SmoothManifold

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The actual native boundary maps onto the literal carrier frontier. -/
theorem frontier_eq_native_boundary {α : Form k M 1}
    (P : NativeLiouvillePresentation α) :
    frontier P.domain.domain.carrier = P.inclusion '' (𝓡∂ (k + 1)).boundary M := by
  have he := P.carrierEquiv.image_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  rw [P.domain.domain.boundary_eq_frontier] at he
  calc
    frontier P.domain.domain.carrier =
        Subtype.val '' (Subtype.val ⁻¹' frontier P.domain.domain.carrier) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z, P.domain.domain.compact.isClosed.frontier_subset hz⟩, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    _ = Subtype.val '' (P.carrierEquiv '' (𝓡∂ (k + 1)).boundary M) := by rw [he]
    _ = P.inclusion '' (𝓡∂ (k + 1)).boundary M := by
      rw [image_image]
      congr 1
      exact funext P.carrier_square

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Full tangent pullback transfers symplectic nondegeneracy to the native
source, including every boundary tangent. -/
theorem native_nondegenerate {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (x : M) :
    Nondegenerate (exteriorDerivative α) x := by
  intro v hv
  apply (P.tangent_bijective x).1
  rw [map_zero]
  apply P.domain.liouville.symplectic.2.2 (P.inclusion x)
    (P.carrier_range ▸ mem_range_self x)
  intro w
  obtain ⟨u, rfl⟩ := (P.tangent_bijective x).2 w
  have h := congrArg (fun eta => eta ![v, u]) (congrFun P.differential x)
  convert h.trans (hv u) using 1
  apply congrArg (P.domain.domain.extension.exteriorDerivative P.domain.liouville.primitive
    (P.inclusion x))
  funext j
  fin_cases j <;> rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The native primitive and its full exterior derivative determine the
actual presentation field on every original point. -/
theorem field_inclusion {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (x : M) :
    P.domain.liouville.field (P.inclusion x) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x
        (liouvilleVector α (exteriorDerivative α) x) := by
  have hx := P.carrier_range ▸ mem_range_self x
  exact (P.domain.liouville.field_eq_liouvilleVector _ hx).trans
    (liouvilleVector_extension_eq P.domain.domain.extension P.inclusion α
      P.domain.liouville.primitive P.native_nondegenerate (congrFun P.primitive)
      (congrFun P.differential) x (P.tangent_bijective x).2
      (P.domain.liouville.symplectic.2.2 _ hx))

variable [T2Space M] [SecondCountableTopology M]

/-- The original native boundary presentation is obtained from its carrier
diffeomorphism and actual boundary inclusion, without a supplied boundary map. -/
def nativeBoundaryEquiv {α : Form k M 1} (P : NativeLiouvillePresentation α) :
    (IntrinsicBoundary.smoothManifold k M).SmoothEquiv P.domain.domain.boundary :=
  boundaryPresentationEquiv P.domain.domain P.inclusion P.smooth_inclusion
    P.embedding.injective (fun x => (P.tangent_bijective x).1) P.frontier_eq_native_boundary

@[simp] theorem nativeBoundaryEquiv_inclusion {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (x : IntrinsicBoundary.Point k M) :
    P.domain.domain.boundaryInclusion.map (P.nativeBoundaryEquiv x) = P.inclusion x.val :=
  boundaryPresentationEquiv_inclusion P.domain.domain P.inclusion P.smooth_inclusion
    P.embedding.injective (fun x => (P.tangent_bijective x).1) P.frontier_eq_native_boundary x

/-- The boundary identification induced by retaining the same native points. -/
def nativeBoundaryComparison {α : Form k M 1} (P Q : NativeLiouvillePresentation α) :
    P.domain.domain.boundary.SmoothEquiv Q.domain.domain.boundary :=
  P.nativeBoundaryEquiv.symm.trans Q.nativeBoundaryEquiv

@[simp] theorem nativeBoundaryComparison_native {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (x : IntrinsicBoundary.Point k M) :
    P.nativeBoundaryComparison Q (P.nativeBoundaryEquiv x) = Q.nativeBoundaryEquiv x := by
  change Q.nativeBoundaryEquiv (P.nativeBoundaryEquiv.symm (P.nativeBoundaryEquiv x)) = _
  rw [P.nativeBoundaryEquiv.symm_apply_apply]

/-- The constructed open compact collar comparison retains every original
native boundary point. This is its exact seam equation. -/
theorem compactCollarComparison_native_boundary {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (C : Completion P.domain)
    (K : Completion Q.domain) (x : IntrinsicBoundary.Point k M)
    (hx : P.inclusion x.val ∈ C.compactCollarNeighborhood K (P.nativeBoundaryComparison Q)) :
    C.compactCollarExtensionMap K (P.nativeBoundaryComparison Q)
      ⟨P.inclusion x.val, hx⟩ = Q.inclusion x.val := by
  have h := C.compactCollarExtensionMap_boundary K (P.nativeBoundaryComparison Q)
    (P.nativeBoundaryEquiv x)
  rw [P.nativeBoundaryComparison_native Q x, Q.nativeBoundaryEquiv_inclusion] at h
  simpa only [P.nativeBoundaryEquiv_inclusion] using h

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M] in
/-- The actual completed inclusion transports the native Liouville field;
only the original carrier equation of the completion is used. -/
theorem completed_field_inclusion {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (C : Completion P.domain) (x : M) :
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
      (C.inclusion.map ∘ P.inclusion) x
        (liouvilleVector α (exteriorDerivative α) x) =
      C.ambient.field (C.inclusion.map (P.inclusion x)) := by
  rw [mfderiv_comp x
    (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
    (P.smooth_inclusion.mdifferentiableAt (by simp))]
  change mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    C.inclusion.map (P.inclusion x)
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) P.inclusion x
        (liouvilleVector α (exteriorDerivative α) x)) = _
  rw [← P.field_inclusion]
  exact C.field_on_domain _ (P.carrier_range ▸ mem_range_self x)

/-- A native inward integral curve beginning on the original boundary is
the actual negative-time completed flow, including time zero. No extension
germ of the native inclusion is supplied. -/
theorem completed_inclusion_eq_negative_flow {α : Form k M 1}
    (P : NativeLiouvillePresentation α) (C : Completion P.domain)
    {γ : ℝ → M} {δ : ℝ} (x : IntrinsicBoundary.Point k M)
    (hγ : IsMIntegralCurveOn γ
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (hzero : γ 0 = x.val) (t : ℝ) (ht : t ∈ Ico 0 δ) :
    C.inclusion.map (P.inclusion (γ t)) = C.endMap (P.nativeBoundaryEquiv x, -t) := by
  let f := C.inclusion.map ∘ P.inclusion
  have hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ f :=
    C.inclusion.map.contMDiff.comp P.smooth_inclusion
  have hpushed : IsMIntegralCurveOn (f ∘ γ)
      (fun z => -C.ambient.field z) (Ico 0 δ) := by
    intro s hs
    have hd := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp_hasMFDerivWithinAt
      s (hγ s hs)
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) f (γ s)
      (r • (-liouvilleVector α (exteriorDerivative α) (γ s))) =
      r • (-C.ambient.field (f (γ s)))
    rw [map_smul, map_neg, P.completed_field_inclusion C]
    rfl
  have hflow : IsMIntegralCurve
      (fun s => C.ambient.completeFlow.flow (-s) (f x.val))
      (fun z => -C.ambient.field z) := by
    have hn : (-1 : ℝ) • C.ambient.field = (fun z => -C.ambient.field z) := by
      funext z
      exact neg_one_smul ℝ _
    rw [← hn]
    simpa only [Function.comp_def, mul_neg_one] using
      (C.ambient.completeFlow.isMIntegralCurve (f x.val)).comp_mul (-1)
  have hneg : C.ambient.manifold.IsSmoothVectorField (fun z => -C.ambient.field z) := by
    intro a
    convert (C.ambient.smooth_field a).neg using 1
    funext y
    exact map_neg _ _
  have heq := C.ambient.manifold.eqOn_of_isMIntegralCurveOn_Ico hneg hpushed
    (hflow.isMIntegralCurveOn (Ico 0 δ))
    (by simp only [Function.comp_def, hzero, neg_zero, Flow.map_zero_apply])
  rw [C.end_flow, P.nativeBoundaryEquiv_inclusion]
  exact heq ht

/-- Radius-preserving comparison of the actual completion collars retains
the original native points on every supplied native inward trajectory. -/
theorem compactCollarComparison_native_inward {α : Form k M 1}
    (P Q : NativeLiouvillePresentation α) (C : Completion P.domain)
    (K : Completion Q.domain) {γ : ℝ → M} {δ : ℝ}
    (x : IntrinsicBoundary.Point k M)
    (hγ : IsMIntegralCurveOn γ
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (hzero : γ 0 = x.val) (t : ℝ) (ht : t ∈ Ico 0 δ)
    (hx : P.inclusion (γ t) ∈ C.compactCollarNeighborhood K (P.nativeBoundaryComparison Q)) :
    C.compactCollarExtensionMap K (P.nativeBoundaryComparison Q)
      ⟨P.inclusion (γ t), hx⟩ = Q.inclusion (γ t) := by
  apply K.inclusion.embedding.injective
  rw [C.inclusionMap_compactCollarExtensionMap]
  have hcoords : C.compactCollarEndCoordinates K (P.nativeBoundaryComparison Q)
      ⟨P.inclusion (γ t), hx⟩ = (P.nativeBoundaryEquiv x, -t) := by
    apply C.endMap_injective
    rw [C.endMap_compactCollarEndCoordinates]
    exact P.completed_inclusion_eq_negative_flow C x hγ hzero t ht
  rw [hcoords, P.nativeBoundaryComparison_native]
  exact (Q.completed_inclusion_eq_negative_flow K x hγ hzero t ht).symm

end FsFltz.Geometry.IntrinsicLiouville.NativeLiouvillePresentation
