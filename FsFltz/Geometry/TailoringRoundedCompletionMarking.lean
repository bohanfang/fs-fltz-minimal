import FsFltz.Geometry.TailoringRoundedAbsorption
import FsFltz.Geometry.BoundaryOutwardAbsorptionMarking

/-!
# Individual inclusion completion maps for rounded tailoring domains

Source: `geometric-part-fsf-proof.tex`, marked-deformation subsection,
lines 1279–1303. Actual rounded absorption constructs primitive-preserving
completion maps with the prescribed literal compact inclusion.
Joint smoothness of their parameter family remains a separate producer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

/-- Expose the existing complete flow as a flow of the canonical
primitive-determined field. Its actual action is unchanged. -/
def CompleteLiouvilleManifold.completePrimitive {d : ℕ} (P : CompleteLiouvilleManifold d) :
    CompletePrimitive P.manifold P.primitive where
  smooth_primitive := P.smooth_primitive
  symplectic := P.symplectic
  smooth_field := by
    convert P.smooth_field using 1
    funext x
    exact (P.field_eq_liouvilleVector x).symm
  contraction := by
    intro x v
    rw [← P.field_eq_liouvilleVector]
    exact P.contraction x v
  completeFlow :=
    { flow := P.completeFlow.flow
      smooth_action := P.completeFlow.smooth_action
      solves := by
        intro x t a ha
        rw [← P.field_eq_liouvilleVector]
        exact P.completeFlow.solves x t a ha }

/-- The actual native projection of a localized collar has the identity
differential on its native tangent fibers. -/
theorem LiouvilleDomain.FlowCollar.mfderiv_originalInclusion {d : ℕ}
    {D : LiouvilleDomain d} (C : LiouvilleDomain.FlowCollar D)
    (z : C.localizedDomain.domain.extension.Point) :
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.originalInclusion.map z =
      ContinuousLinearMap.id ℝ (Model d) := by
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (fun y => y.val.val) z = _
  erw [D.neighborhoodDomain.extension.mfderiv_comp_restrict_val D.domain.extension
    C.neighborhood z
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model d)) (n := ∞)).mdifferentiableAt (by simp)),
    D.domain.extension.mfderiv_restrict_val]
  rfl

/-- Localization changes no point of the compact piece under the actual
native projection. -/
theorem LiouvilleDomain.FlowCollar.image_originalInclusion_carrier {d : ℕ}
    {D : LiouvilleDomain d} (C : LiouvilleDomain.FlowCollar D) :
    C.originalInclusion.map '' C.localizedDomain.domain.carrier = D.domain.carrier := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    let z := C.cylindricalCompactHomeomorph.symm ⟨x, hx⟩
    refine ⟨z.val, z.property, ?_⟩
    have h := congrArg Subtype.val (C.cylindricalCompactHomeomorph.apply_symm_apply ⟨x, hx⟩)
    exact h

/-- Any existing completion localizes to the collar presentation with its
ambient, primitive, complete flow and all-real end law unchanged. The actual
canonical local field agrees with the original field on the compact piece. -/
def Completion.localizeToFlowCollar {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (k : LiouvilleDomain.FlowCollar D) : Completion k.localizedDomain where
  ambient := C.ambient
  inclusion :=
    { map := ⟨C.inclusion.map ∘ k.originalInclusion.map,
        C.inclusion.map.contMDiff.comp k.originalInclusion.map.contMDiff⟩
      embedding := C.inclusion.embedding.comp k.originalInclusion.embedding
      immersion := by
        intro z
        change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
          (C.inclusion.map ∘ k.originalInclusion.map) z)
        rw [mfderiv_comp z (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
          (k.originalInclusion.map.contMDiff.mdifferentiableAt (by simp)),
          k.mfderiv_originalInclusion]
        exact C.inclusion.immersion z.val.val }
  primitive_on_domain := by
    intro z hz
    change k.localizedDomain.domain.extension.pullback C.ambient.manifold
      (C.inclusion.map ∘ k.originalInclusion.map) C.ambient.primitive z = _
    rw [k.localizedDomain.domain.extension.pullback_comp D.domain.extension C.ambient.manifold
      (k.originalInclusion.map.contMDiff.mdifferentiable (by simp))
      (C.inclusion.map.contMDiff.mdifferentiable (by simp))]
    unfold SmoothManifold.pullback
    rw [k.mfderiv_originalInclusion]
    change D.domain.extension.pullback C.ambient.manifold C.inclusion.map C.ambient.primitive
      z.val.val = k.localizedDomain.liouville.primitive z
    rw [C.primitive_on_domain z.val.val hz, k.original_primitive]
  field_on_domain := by
    intro z hz
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d)
      (C.inclusion.map ∘ k.originalInclusion.map) z (k.localizedDomain.liouville.field z) = _
    rw [mfderiv_comp z (C.inclusion.map.contMDiff.mdifferentiableAt (by simp))
      (k.originalInclusion.map.contMDiff.mdifferentiableAt (by simp)),
      k.mfderiv_originalInclusion]
    have hf : k.localizedDomain.liouville.field z = D.liouville.field z.val.val :=
      (k.stretchedField_carrier z hz).symm.trans (k.stretchedField_original_carrier z hz)
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) C.inclusion.map z.val.val
      (k.localizedDomain.liouville.field z) = _
    rw [hf]
    exact C.field_on_domain z.val.val hz
  endMap := C.endMap
  smooth_endMap := C.smooth_endMap
  end_flow := C.end_flow
  end_embedding := C.end_embedding
  end_immersion := C.end_immersion
  end_primitive := by
    intro b r v s
    rw [k.localized_boundaryForm]
    exact C.end_primitive b r v s
  covering := by
    change (C.inclusion.map ∘ k.originalInclusion.map) '' k.localizedDomain.domain.carrier ∪
      C.endMap '' (univ ×ˢ Ici (0 : ℝ)) = univ
    rw [image_comp, k.image_originalInclusion_carrier]
    exact C.covering
  overlap := by
    intro b r hr
    change C.endMap (b, r) ∉ (C.inclusion.map ∘ k.originalInclusion.map) ''
      k.localizedDomain.domain.carrier
    rw [image_comp, k.image_originalInclusion_carrier]
    exact C.overlap b r hr

/-- Boundary outwardness and actual negative absorption construct an
inclusion marking from the native cylindrical completion chosen by the
collar existence theorem. Its compact formula is the literal native
open-subset inclusion into the prescribed complete ambient. -/
def CompleteLiouvilleManifold.regularSublevelInclusionMarking {d : ℕ}
    (P : CompleteLiouvilleManifold d) (ρ : P.manifold.Point → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcompact : IsCompact {x : P.manifold.Point | ρ x ≤ 0})
    (hout : ∀ x, ρ x = 0 →
      0 < P.manifold.scalarDerivative ρ x (P.manifold.liouvilleVector P.primitive x))
    (habsorb : ∀ x : P.manifold.Point, ∃ T : ℝ, 0 ≤ T ∧
      ρ (P.completeFlow.flow (-T) x) ≤ 0) :
    let D := regularSublevelLiouvilleDomain P.manifold ρ hρ hcompact
      P.primitive P.smooth_primitive P.symplectic hout
    InclusionMarking D.flowCollar.cylindricalCompletion P
      (fun x => D.flowCollar.originalInclusion.map x.val) := by
  let D := regularSublevelLiouvilleDomain P.manifold ρ hρ hcompact
    P.primitive P.smooth_primitive P.symplectic hout
  let k := D.flowCollar
  let C₀ := BoundaryOutwardAbsorptionMarking.completionOfBoundaryOutwardAbsorption
    D P.completePrimitive ρ hρ
    (regularSublevelLiouvilleDomain_frontier P.manifold ρ hρ hcompact
      P.primitive P.smooth_primitive P.symplectic hout) hout rfl habsorb
  let C₁ := C₀.localizeToFlowCollar k
  let C := k.cylindricalCompletion
  refine
    { equiv := (C.comparisonPresentation C₁).equiv
      primitive := C.comparison_primitive C₁
      inclusion := fun x => C.comparison_compact C₁ x.val x.property
      flow_induced := ?_ }
  intro b r
  change (C.comparisonPresentation C₁).equiv (C.endMap (b, r)) =
    P.completeFlow.flow r
      ((C.comparisonPresentation C₁).equiv
        (C.inclusion.map (k.localizedDomain.domain.boundaryInclusion.map b)))
  rw [C.comparison_end C₁,
    C.comparison_compact C₁ _ (k.localizedDomain.domain.boundaryInclusion_mem_carrier b)]
  rfl

end FsFltz.Geometry

namespace FsFltz
open Geometry
variable {n : ℕ}
local instance roundedCompletionMarkingLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- Actual individual inclusion completion markings, with literal projected
rounded carrier and the actual tailoring primitive at every compact point.
Both source and target completions are constructed from native collars;
there is no completeness or completion marking hypothesis. -/
theorem tailoringFamily_exists_uniform_rounded_completion_markings
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ t : ℝ, 0 < t → ∀ u, φEnd (t • u) = t ^ 2 * φEnd u)
    {REnd : ℝ} (hREnd : 0 < REnd)
    (heq : ∀ u, REnd ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    {D : ℝ} (hD : 0 < D) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, Aminus < D ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < D ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K ≥ Kstar, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ (hcompact : IsCompact {y : LGSpace n | φ y.1 - D ^ 2 * β ^ 2 / 2 ≤ 0})
        (hω : (lgManifold n).IsSymplecticOn ((lgManifold n).exteriorDerivative
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K)) univ)
        (hout : ∀ y : (lgManifold n).Point, φ y.1 - D ^ 2 * β ^ 2 / 2 = 0 →
          0 < (lgManifold n).scalarDerivative (fun z => φ z.1 - D ^ 2 * β ^ 2 / 2) y
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β s) K) y)),
      let E := tailoringPotentialOuterDomain I hφ β s K (D ^ 2 * β ^ 2 / 2) hcompact hω hout
      ∀ C : LiouvilleDomain.FlowCollar E,
      let P := C.cylindricalCompletion.ambient
      let q : P.manifold.Point → ℝ := fun z => tailoringRoundedDefiningFunction
        I φ β s R (D ^ 2 * β ^ 2 / 2) m (C.originalInclusion.map z)
      ∃ (hcompactq : IsCompact {z : P.manifold.Point | q z ≤ 0})
        (houtq : ∀ z, q z = 0 →
          0 < P.manifold.scalarDerivative q z (P.manifold.liouvilleVector P.primitive z)),
      let B := regularSublevelLiouvilleDomain P.manifold q
        ((contMDiff_tailoringRoundedDefiningFunction I hφ β s R (D ^ 2 * β ^ 2 / 2) m).comp
          C.originalInclusion.map.contMDiff) hcompactq P.primitive P.smooth_primitive P.symplectic houtq
      (∀ z ∈ B.domain.carrier, B.liouville.primitive z =
        (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K z.val.val) ∧
      C.originalInclusion.map '' (B.flowCollar.originalInclusion.map ''
        B.flowCollar.localizedDomain.domain.carrier) =
          tailoringRoundedDomain I φ β s R (D ^ 2 * β ^ 2 / 2) m ∧
      Nonempty (InclusionMarking B.flowCollar.cylindricalCompletion P
        (fun z => B.flowCollar.originalInclusion.map z.val)) := by
  obtain ⟨Bo, _hBo, ho⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  obtain ⟨BD, _hBD, hDdata⟩ := tailoringFamily_exists_uniform_potential_sublevel_data
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hREnd heq hD
  let β₀ := max 1 (max Bo BD)
  refine ⟨β₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβo : Bo ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβD : BD ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hcompact, _hnonempty, hdata⟩ := hDdata β hβD
  obtain ⟨Kstar, hKstar, hout⟩ := ho β hβo
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout R hR Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK s hs
  obtain ⟨hω, hb⟩ := hdata s hs K (hKstar.le.trans hK)
  refine ⟨hcompact, hω, hb, ?_⟩
  intro E C
  let P := C.cylindricalCompletion.ambient
  let q₀ := tailoringRoundedDefiningFunction I φ β s R (D ^ 2 * β ^ 2 / 2) m
  let q : P.manifold.Point → ℝ := fun z => q₀ (C.originalInclusion.map z)
  have hq₀ := contMDiff_tailoringRoundedDefiningFunction I hφ β s R (D ^ 2 * β ^ 2 / 2) m
  have hq : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ q :=
    hq₀.comp C.originalInclusion.map.contMDiff
  have hsubset : {z : P.manifold.Point | q z ≤ 0} ⊆ C.localizedDomain.domain.carrier := by
    intro z hz
    have hφz := (tailoringRoundedDomain_subset I φ β s (D ^ 2 * β ^ 2 / 2) hR m hz).1
    change φ z.val.val.1 - D ^ 2 * β ^ 2 / 2 ≤ 0
    exact sub_nonpos.mpr hφz
  have hcompactq : IsCompact {z : P.manifold.Point | q z ≤ 0} :=
    C.localizedDomain.domain.compact.of_isClosed_subset
      (isClosed_le hq.continuous continuous_const) hsubset
  have hp : ∀ y ∈ E.domain.carrier, 0 ≤ q₀ y →
      0 < (lgManifold n).scalarDerivative q₀ y (E.liouville.field y) := by
    intro y hy hqy
    exact hout m hm hmd K hK s hs y (sub_nonpos.mp hy) hqy
  have houtq : ∀ z : P.manifold.Point, q z = 0 →
      0 < P.manifold.scalarDerivative q z (P.manifold.liouvilleVector P.primitive z) := by
    intro z hz
    have hzc := hsubset hz.le
    rw [← P.field_eq_liouvilleVector]
    change 0 < C.localizedDomain.domain.extension.scalarDerivative
      (fun y => q₀ (C.originalInclusion.map y)) z (P.field z)
    rw [C.scalarDerivative_originalInclusion q₀ hq₀]
    erw [C.cylindricalCompletion_original_field z hzc]
    exact hp z.val.val hzc hz.ge
  have habsorb : ∀ z : P.manifold.Point, ∃ T : ℝ, 0 ≤ T ∧ q (P.completeFlow.flow (-T) z) ≤ 0 := by
    intro z
    obtain ⟨T, hT, _hc, he⟩ := C.exists_nonneg_time_original_scalar_le q₀ hq₀ 0 hp z
    exact ⟨T, hT, he⟩
  refine ⟨hcompactq, houtq, ?_, ?_,
    ⟨P.regularSublevelInclusionMarking q hq hcompactq houtq habsorb⟩⟩
  · intro z hz
    exact C.cylindricalCompletion_original_primitive z (hsubset hz)
  · rw [LiouvilleDomain.FlowCollar.image_originalInclusion_carrier]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hypot := (tailoringRoundedDomain_subset I φ β s (D ^ 2 * β ^ 2 / 2) hR m hy).1
      have hyE : y ∈ E.domain.carrier := sub_nonpos.mpr hypot
      let z := C.cylindricalCompactHomeomorph.symm ⟨y, hyE⟩
      have he : C.originalInclusion.map z.val = y :=
        congrArg Subtype.val (C.cylindricalCompactHomeomorph.apply_symm_apply ⟨y, hyE⟩)
      refine ⟨z.val, ?_, he⟩
      change q₀ (C.originalInclusion.map z.val) ≤ 0
      rw [he]
      exact hy

end FsFltz
