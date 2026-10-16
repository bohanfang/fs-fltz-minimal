import FsFltz.Geometry.TailoringCotangentEndpointNative
import FsFltz.Geometry.BoundaryContact
import FsFltz.Geometry.PairRestriction

/-!
# Transport of the actual retained ribbon to the standard cotangent endpoint

Source: `geometric-part-fsf-proof.tex`, `prop:endpoint`, lines 1922–1959;
`geoemtric-part-fsf.tex`, `def:chain`, lines 171–199, and
`eq:coreendpoint`, lines 402–413. The endpoint pair and its positive witness
are constructed on the identical ribbon domain and completion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

local instance endpointPairCotangentCharts : ChartedSpace (Model (2 * n)) (Cotangent n) :=
  (cotangentManifold n).charts
local instance endpointPairCotangentSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (Cotangent n) :=
  (cotangentManifold n).smooth

namespace Geometry.WitnessedPair

variable (P : WitnessedPair n)
  (ψ : P.ambientDomain.domain.boundary.SmoothEquiv (standardCotangentDisk n).domain.boundary)
  (s : P.ambientDomain.domain.boundary.Point → ℝ)
  (hs : ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, ℝ) ∞ s)
  (hψ : P.ambientDomain.domain.boundary.pullback (standardCotangentDisk n).domain.boundary ψ
    ((standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n)) =
      fun x => Real.exp (-s x) •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x)

/-- The actual endpoint witness compensates precisely the induced end shift. -/
def cotangentEndpointWitness (y : (standardCotangentDisk n).domain.boundary.Point) : ℝ :=
  Real.exp (s (ψ.symm y)) * P.witness (ψ.symm y)

include hψ in
theorem cotangentEndpointWitness_pullback :
    P.ambientDomain.domain.boundary.pullback (standardCotangentDisk n).domain.boundary ψ
      (fun y => P.cotangentEndpointWitness ψ s y •
        (standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) y) =
      fun x => P.witness x •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x := by
  funext x
  have he := congrFun hψ x
  change (((standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) (ψ x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model (2 * n - 1))
      𝓘(ℝ, Model (2 * n - 1)) ψ x)) = _ at he
  change (P.cotangentEndpointWitness ψ s (ψ x) •
    (standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) (ψ x)).compContinuousLinearMap _ = _
  apply ContinuousAlternatingMap.ext
  intro vs
  have heval := congrArg (fun α => α vs) he
  change (standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) (ψ x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, Model (2 * n - 1)) ψ x (vs i)) =
    Real.exp (-s x) *
    P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x vs at heval
  change P.cotangentEndpointWitness ψ s (ψ x) *
    ((standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) (ψ x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, Model (2 * n - 1)) ψ x (vs i))) = P.witness x *
    P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x vs
  rw [heval]
  simp only [cotangentEndpointWitness, ψ.symm_apply_apply]
  have hc : (Real.exp (s x) * P.witness x) * Real.exp (-s x) = P.witness x := by
    rw [mul_assoc, mul_comm (P.witness x), ← mul_assoc, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, one_mul]
  rw [← mul_assoc, hc]

/-- An actual smooth embedding of the same whole ribbon into the cotangent boundary. -/
def cotangentEndpointEmbedding :
    P.ribbonDomain.domain.extension.SmoothEmbedding (standardCotangentDisk n).domain.boundary where
  map := ⟨ψ ∘ P.ribbonEmbedding.map, ψ.contMDiff.comp P.ribbonEmbedding.map.contMDiff⟩
  embedding := ψ.toHomeomorph.isEmbedding.comp P.ribbonEmbedding.embedding
  immersion := by
    intro x
    change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, Model (2 * n - 1)) (ψ ∘ P.ribbonEmbedding.map) x)
    rw [mfderiv_comp x (ψ.contMDiff.mdifferentiableAt (by simp))
      (P.ribbonEmbedding.map.contMDiff.mdifferentiableAt (by simp))]
    exact (ψ.isInvertible_mfderiv (by simp)).injective.comp (P.ribbonEmbedding.immersion x)

/-- The actual cotangent pair retains the original ribbon domain and completion. -/
def cotangentEndpointPair : WitnessedPair n where
  ambientDomain := standardCotangentDisk n
  ambientCompletion := standardCotangentCompletion n
  ribbonDomain := P.ribbonDomain
  ribbonCompletion := P.ribbonCompletion
  ribbonEmbedding := P.cotangentEndpointEmbedding ψ
  witness := P.cotangentEndpointWitness ψ s
  smooth_witness := (Real.contDiff_exp.contMDiff.comp (hs.comp ψ.symm.contMDiff)).mul
    (P.smooth_witness.comp ψ.symm.contMDiff)
  positive_witness := fun y => mul_pos (Real.exp_pos _) (P.positive_witness _)
  ribbon_primitive := by
    intro x hx
    change P.ribbonDomain.domain.extension.pullback (standardCotangentDisk n).domain.boundary
      (ψ ∘ P.ribbonEmbedding.map)
      (fun y => P.cotangentEndpointWitness ψ s y •
        (standardCotangentDisk n).domain.boundaryForm (lambdaCanForm n) y) x = _
    rw [P.ribbonDomain.domain.extension.pullback_comp P.ambientDomain.domain.boundary
      (standardCotangentDisk n).domain.boundary
      (P.ribbonEmbedding.map.contMDiff.mdifferentiable (by simp))
      (ψ.contMDiff.mdifferentiable (by simp)),
      P.cotangentEndpointWitness_pullback ψ s hψ]
    exact P.ribbon_primitive x hx

/-- The endpoint has the standard inclusion, unit-disk image, and radial end. -/
def cotangentEndpoint : CotangentPairData n where
  pair := P.cotangentEndpointPair ψ s hs hψ
  marking := Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) (Cotangent n) ∞
  primitive := (cotangentManifold n).pullback_id (lambdaCanForm n)
  domain_image := by
    change id '' (standardCotangentDisk n).domain.carrier = cotangentDisk
    rw [image_id, standardCotangentDisk_carrier]
  boundary_image := standardCotangentDisk_boundary_range n
  standard_end := fun _ _ _ => rfl

theorem cotangentEndpoint_embeddedCore :
    (P.cotangentEndpoint ψ s hs hψ).embeddedCore =
      (standardCotangentDisk n).domain.boundaryInclusion.map '' (ψ '' P.embeddedCore) := by
  change ((standardCotangentDisk n).domain.boundaryInclusion.map ∘ ψ ∘
    P.ribbonEmbedding.map) '' P.ribbonCompletion.core = _
  rw [image_comp, image_comp]
  rfl

end Geometry.WitnessedPair

/-- The literal boundary coordinates fixed by an endpoint's standard marking. -/
def CotangentPairData.boundaryCoordinates (E : CotangentPairData n)
    (x : E.pair.ambientDomain.domain.boundary.Point) : Cotangent n :=
  E.marking (E.pair.ambientCompletion.inclusion.map
    (E.pair.ambientDomain.domain.boundaryInclusion.map x))

/-- Every actual strict cotangent marking constructs a permitted terminal
step, with the identity on the retained ribbon and scale exactly one. -/
theorem exists_cotangentEndpoint_of_strictMarking (P : WitnessedPair n)
    (f : P.ambientManifold.SmoothEquiv (cotangentManifold n))
    (hf : P.ambientManifold.pullback (cotangentManifold n) f
      (lambdaCanForm n) = P.ambientCompletion.ambient.primitive) :
    ∃ E : CotangentPairData n, ∃ J : CompletionIdentification P E.pair,
      J.ambientEquiv.trans E.marking = f ∧
      E.pair.ribbonDomain = P.ribbonDomain ∧
      HEq E.pair.ribbonCompletion P.ribbonCompletion ∧
      HEq J.ribbonEquiv.map (id : P.ribbonDomain.domain.extension.Point →
        P.ribbonDomain.domain.extension.Point) ∧ J.scale = 1 ∧
      (∀ x, E.pair.witness (J.boundaryEquiv x) = Real.exp (J.shift x) * P.witness x) ∧
      E.embeddedCore = E.boundaryCoordinates ''
        (J.boundaryEquiv '' P.embeddedCore) := by
  obtain ⟨ψ, s, hs, hend, hψ⟩ := P.ambientCompletion.exists_boundaryEquiv_with_pullback
    (standardCotangentCompletion n) f hf
  let E := P.cotangentEndpoint ψ s hs hψ
  let J : CompletionIdentification P E.pair :=
    { ambientEquiv := f
      primitive := hf
      boundaryEquiv := ψ
      shift := s
      smooth_shift := hs
      induced_at_infinity := fun x => ⟨0, fun r _ => hend x r⟩
      boundary_primitive := hψ
      ribbonEquiv := CompactDomainDiffeomorph.refl _
      scale := 1
      positive_scale := zero_lt_one
      ribbon_primitive := by
        intro x _
        change P.ribbonDomain.domain.extension.pullback P.ribbonDomain.domain.extension id
          P.ribbonDomain.liouville.primitive x = 1 • P.ribbonDomain.liouville.primitive x
        rw [P.ribbonDomain.domain.extension.pullback_id, one_smul]
      ribbon_square := fun _ _ => rfl }
  refine ⟨E, J, ?_, rfl, HEq.rfl, HEq.rfl, rfl, ?_,
    P.cotangentEndpoint_embeddedCore ψ s hs hψ⟩
  · exact Diffeomorph.ext (fun _ => rfl)
  · intro x
    change P.cotangentEndpointWitness ψ s (ψ x) = _
    simp only [Geometry.WitnessedPair.cotangentEndpointWitness, ψ.symm_apply_apply]
    rfl

end FsFltz
