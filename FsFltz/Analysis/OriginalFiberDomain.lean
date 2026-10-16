import FsFltz.Analysis.OriginalFiberCompleteFlow
import FsFltz.Analysis.LaurentSurjectivity
import FsFltz.Geometry.RegularSublevelDomain
import FsFltz.Geometry.FlowAbsorptionMarking

/-!
# Actual compact fiber domains and full-fiber inclusion markings

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and `prop:allinitial`, lines 923–930; `geoemtric-part-fsf.tex`, `g:initial`,
lines 370–384. The literal quadratic truncation of the constructed full
far-fiber model has its restricted primitive and strictly outward intrinsic
Liouville field. Compact exhaustion bands and the actual complete fiber
flow give negative entry. The native completion theorem then constructs
the actual full-fiber inclusion marking. This does not yet embed the
compact fiber domain as the ribbon in a rounded ambient boundary.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Function

namespace FsFltz.Geometry
open SmoothManifold

set_option backward.isDefEq.respectTransparency false in
private def completePrimitiveOfCompleteAmbient {d : ℕ}
    (X : CompleteLiouvilleManifold d) : CompletePrimitive X.manifold X.primitive where
  smooth_primitive := X.smooth_primitive
  symplectic := X.symplectic
  smooth_field := by
    have he : X.field = X.manifold.liouvilleVector X.primitive :=
      funext X.field_eq_liouvilleVector
    rw [← he]
    exact X.smooth_field
  contraction := fun x v => by
    rw [← X.field_eq_liouvilleVector x]
    exact X.contraction x v
  completeFlow :=
    { flow := X.completeFlow.flow
      smooth_action := X.completeFlow.smooth_action
      solves := by
        intro x t a ha
        rw [← X.field_eq_liouvilleVector]
        exact X.completeFlow.solves x t a ha }

section Original

variable {n : ℕ} (I : ToricInput n) {Aamb R : ℝ}
  (hamb : AmbientEndBound I Aamb)
  (hR : max 1 (sublevelMagnitudeSup I Aamb) < R)

local notation "F" => originalFullFiberModel I hamb hR
local notation "η" => (phi0 ∘ SmoothEmbedding.map
  (FullFiberModel.embedding (originalFullFiberModel I hamb hR)))

/-- The quadratic potential is smooth on the whole actual full fiber. -/
theorem contMDiff_originalFullFiber_phi0 :
    ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ η := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact contMDiff_original_phi0.comp (F).embedding.map.contMDiff

/-- All intrinsic quadratic sublevels are compact, including the empty
negative sublevels. Closedness of the literal fiber gives the positive case. -/
theorem isCompact_originalFullFiber_phi0_sublevel_all (B : ℝ) :
    IsCompact {x : (F).ambient.manifold.Point | η x ≤ B} := by
  by_cases hB : 0 ≤ B
  · exact isCompact_originalFiber_phi0_sublevel I (F).embedding (F).image B hB
  · have he : {x : (F).ambient.manifold.Point | η x ≤ B} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hnonneg : 0 ≤ η x :=
        div_nonneg (realSquaredNorm_nonneg ((F).embedding.map x).1) (by norm_num)
      exact hB (hnonneg.trans hx)
    rw [he]
    exact isCompact_empty

variable {Afib : ℝ} (hfib : FiberEndBound I Aamb R Afib)
include hfib

/-- Every valid fiber end bound controls the actual intrinsic exhaustion
derivative on and above its level, on this very full-fiber model. -/
theorem scalarDerivative_originalFullFiber_phi0_pos
    (x : (F).ambient.manifold.Point) (hx : Afib ≤ η x) :
    0 < (F).ambient.manifold.scalarDerivative η x
      ((F).ambient.manifold.liouvilleVector (F).ambient.primitive x) := by
  rw [← (F).primitive]
  exact scalarDerivative_phi0_original_farFiber_pos I hamb hR hfib
    (F).embedding (F).image x hx

variable {Aminus : ℝ} (hAminus : Afib < Aminus)
include hAminus

/-- Every point of the actual whole fiber enters the larger quadratic
sublevel in finite negative time under that model's complete intrinsic flow. -/
theorem originalFullFiber_absorbs_phi0_sublevel (x : (F).ambient.manifold.Point) :
    ∃ T : ℝ, 0 ≤ T ∧ η ((F).ambient.completeFlow.flow (-T) x) ≤ Aminus := by
  apply (F).ambient.completeFlow.exists_nonneg_time_scalar_le η
    (contMDiff_originalFullFiber_phi0 I hamb hR) (F).ambient.smooth_field
    (isCompact_originalFullFiber_phi0_sublevel_all I hamb hR) Aminus
  intro y hy
  rw [(F).ambient.field_eq_liouvilleVector]
  exact scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib y (hAminus.le.trans hy)

omit hfib hAminus in
private theorem compact_defining_sublevel :
    IsCompact {x : (F).ambient.manifold.Point | η x - Aminus ≤ 0} := by
  simpa only [sub_nonpos] using
    isCompact_originalFullFiber_phi0_sublevel_all I hamb hR Aminus

omit hfib hAminus in
set_option backward.isDefEq.respectTransparency false in
private theorem defining_scalarDerivative (x : (F).ambient.manifold.Point)
    (v : (F).ambient.manifold.Tangent x) :
    (F).ambient.manifold.scalarDerivative (fun y => η y - Aminus) x v =
      (F).ambient.manifold.scalarDerivative η x v := by
  unfold scalarDerivative
  change mfderiv _ _ (η - fun _ => Aminus) x v = _
  rw [mfderiv_sub ((contMDiff_originalFullFiber_phi0 I hamb hR).mdifferentiable (by simp) x)
    mdifferentiableAt_const, mfderiv_const, sub_zero]
  rfl

private theorem defining_outward (x : (F).ambient.manifold.Point)
    (hx : η x - Aminus = 0) :
    0 < (F).ambient.manifold.scalarDerivative (fun y => η y - Aminus) x
      ((F).ambient.manifold.liouvilleVector (F).ambient.primitive x) := by
  rw [defining_scalarDerivative I hamb hR]
  exact scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib x
    (by have he := sub_eq_zero.mp hx; rw [he]; exact hAminus.le)

/-- The actual quadratic truncation of the full far fiber, with its
restricted primitive, native smooth boundary and outward intrinsic field.
No positive-dimensional hypothesis is imposed; rank one has empty boundary. -/
def originalFiberLiouvilleDomain : LiouvilleDomain (2 * n - 2) :=
  regularSublevelLiouvilleDomain (F).ambient.manifold (fun x => η x - Aminus)
    ((contMDiff_originalFullFiber_phi0 I hamb hR).sub_const Aminus)
    (compact_defining_sublevel I hamb hR) (F).ambient.primitive
    (F).ambient.smooth_primitive (F).ambient.symplectic
    (defining_outward I hamb hR hfib hAminus)

/-- The native carrier is exactly the prescribed quadratic fiber truncation. -/
theorem originalFiberLiouvilleDomain_carrier :
    (originalFiberLiouvilleDomain I hamb hR hfib hAminus).domain.carrier =
      {x : (F).ambient.manifold.Point | η x ≤ Aminus} := by
  ext x
  change η x - Aminus ≤ 0 ↔ η x ≤ Aminus
  exact sub_nonpos

set_option backward.isDefEq.respectTransparency false in
/-- The native frontier is the prescribed quadratic level in the actual fiber. -/
theorem originalFiberLiouvilleDomain_frontier :
    frontier (originalFiberLiouvilleDomain I hamb hR hfib hAminus).domain.carrier =
      {x : (F).ambient.manifold.Point | η x = Aminus} := by
  have h := regularSublevelLiouvilleDomain_frontier (F).ambient.manifold
    (fun x => η x - Aminus) ((contMDiff_originalFullFiber_phi0 I hamb hR).sub_const Aminus)
    (compact_defining_sublevel I hamb hR) (F).ambient.primitive
    (F).ambient.smooth_primitive (F).ambient.symplectic
    (defining_outward I hamb hR hfib hAminus)
  simpa only [originalFiberLiouvilleDomain, sub_eq_zero] using h

/-- The actual intrinsic complete flow and its proved negative entry
construct a native completion of the compact quadratic fiber domain. -/
def originalFiberCompletion :
    Completion (originalFiberLiouvilleDomain I hamb hR hfib hAminus) :=
  FlowAbsorptionMarking.completionOfSublevelAbsorption
    (originalFiberLiouvilleDomain I hamb hR hfib hAminus)
    (completePrimitiveOfCompleteAmbient (F).ambient) η
    (contMDiff_originalFullFiber_phi0 I hamb hR)
    (originalFiberLiouvilleDomain_frontier I hamb hR hfib hAminus)
    (fun x hx => scalarDerivative_originalFullFiber_phi0_pos I hamb hR hfib x
      (hAminus.le.trans hx))
    (originalFiberLiouvilleDomain_carrier I hamb hR hfib hAminus)
    (originalFullFiber_absorbs_phi0_sublevel I hamb hR hfib hAminus)

/-- Inclusion extends to an actual primitive-preserving diffeomorphism
onto the whole specified full-fiber model, induced by its actual intrinsic
flow for every real boundary radius. -/
def originalFiberInclusionMarking :
    InclusionMarking (originalFiberCompletion I hamb hR hfib hAminus) (F).ambient
      (fun x => x.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 2)) (F).ambient.manifold.Point ∞
  primitive := (F).ambient.manifold.pullback_id (F).ambient.primitive
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- The actual full-fiber inclusion marking is available from every chosen
native completion of this same quadratic fiber domain. -/
def originalFiberInclusionMarkingOfCompletion
    (C : Completion (originalFiberLiouvilleDomain I hamb hR hfib hAminus)) :
    InclusionMarking C (F).ambient (fun x => x.val) :=
  C.transportInclusionMarking (originalFiberCompletion I hamb hR hfib hAminus)
    (F).ambient (fun x => x.val) (originalFiberInclusionMarking I hamb hR hfib hAminus)

/-- The embedded carrier is literally the entire prescribed fiber
truncation in the original ambient. No selected component is substituted. -/
theorem originalFiberLiouvilleDomain_image :
    (F).embedding.map '' (originalFiberLiouvilleDomain I hamb hR hfib hAminus).domain.carrier =
      InitialRibbon I R Aminus := by
  rw [originalFiberLiouvilleDomain_carrier I hamb hR hfib hAminus]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hf : (F).embedding.map x ∈ FullFiber I R := by
      rw [← (F).image]
      exact ⟨x, rfl⟩
    exact ⟨hf, hx⟩
  · rintro ⟨hW, hphi⟩
    have hf : y ∈ range (F).embedding.map := by rw [(F).image]; exact hW
    obtain ⟨x, rfl⟩ := hf
    exact ⟨x, hphi, rfl⟩

/-- Surjectivity of the original Laurent superpotential and actual negative
entry make this precise compact fiber truncation nonempty. -/
theorem originalFiberLiouvilleDomain_nonempty :
    (originalFiberLiouvilleDomain I hamb hR hfib hAminus).domain.carrier.Nonempty := by
  obtain ⟨y, hy⟩ := I.fullFiber_nonempty R
  rw [← (F).image] at hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨T, _, hentry⟩ := originalFullFiber_absorbs_phi0_sublevel I hamb hR hfib hAminus x
  refine ⟨(F).ambient.completeFlow.flow (-T) x, ?_⟩
  rw [originalFiberLiouvilleDomain_carrier I hamb hR hfib hAminus]
  exact hentry

end Original
end FsFltz.Geometry
