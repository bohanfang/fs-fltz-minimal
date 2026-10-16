import FsFltz.Geometry.EmbeddedCarrierCompactMap
import FsFltz.Geometry.NativeCompactMapCompletion
import FsFltz.Geometry.TailoringFiberMarking
import FsFltz.Geometry.TailoringRoundedMarkingFamilyUniform

/-!
# Full-fiber markings on the retained tailored ribbon

Source: `geometric-part-fsf-proof.tex`, `eq:fiberends`, lines 1208–1237,
and the marked family, lines 1304–1314; `geoemtric-part-fsf.tex`,
`def:chain`, lines 171–189. The complete intrinsic fiber primitive and
its outward truncation transfer to the exact supplied ribbon completion.
The conclusion is pointwise; no smooth full-fiber marking family is claimed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The full-fiber outward truncation marking transfers to an arbitrary
supplied completion of the exact retained ribbon. The compact map and
primitive equality are derived from the full carrier image. -/
theorem exists_inclusionMarking_of_retained_tailoringRibbon
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (β s A : ℝ) (N : SmoothManifold (2 * n - 2))
    (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β s y = 1})
    (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
    (hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x))
    (D : LiouvilleDomain (2 * n - 2)) (hD : D.domain.carrier.Nonempty)
    (W : D.domain.extension.SmoothEmbedding (lgManifold n))
    (hW : W.map '' D.domain.carrier =
      {y | tailoringFamily I β s y = 1 ∧ φ y.1 ≤ A})
    (hμ : ∀ x ∈ D.domain.carrier,
      D.liouville.primitive x = D.domain.extension.pullback (lgManifold n) W.map
        (lambdaPotentialForm φ) x)
    (C : Completion D) :
    let E := tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend
      I β s j himage P A hpos
    ∃ h : CompactDomainDiffeomorph D.domain E.domain,
      (∀ x ∈ D.domain.carrier, j.map (h.map x) = W.map x) ∧
      (∀ x ∈ D.domain.carrier,
        D.domain.extension.pullback N h.map P.toCompleteLiouvilleManifold.primitive x =
          D.liouville.primitive x) ∧
      ∃ q : InclusionMarking C P.toCompleteLiouvilleManifold (fun x => h.map x.val),
        ∀ b r, q.equiv (C.endMap (b, r)) = P.completeFlow.flow r
          (h.map (D.domain.boundaryInclusion.map b)) := by
  let E := tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend
    I β s j himage P A hpos
  have hEimage := tailoringFiberOutwardDomain_image hφ hEnd1 hEnd hhom hc hlower hL hend
    I β s j himage P A hpos
  obtain ⟨h, hsquare, _hinverse⟩ := D.domain.exists_compactDiffeomorph_of_embeddedCarrier
    E.domain (lgManifold n) hD W j (hW.trans hEimage.symm)
  have hp (x) (hx : x ∈ D.domain.carrier) :
      D.domain.extension.pullback E.domain.extension h.map E.liouville.primitive x =
        D.liouville.primitive x := by
    change D.domain.extension.pullback N h.map
      (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x = _
    erw [h.pullback_of_embeddedCarrier (lgManifold n) W j hsquare (lambdaPotentialForm φ) x hx]
    exact (hμ x hx).symm
  let C' := tailoringFiberOutwardCompletion hφ hEnd1 hEnd hhom hc hlower hL hend
    I β s j himage P A hpos
  obtain ⟨e, _b, he, hecompact, _heboundary, _heend⟩ :=
    C.exists_strictEquiv_of_compactDiffeomorph C' h hp
  let q : InclusionMarking C P.toCompleteLiouvilleManifold (fun x => h.map x.val) :=
    { equiv := e
      primitive := he
      inclusion := fun x => hecompact x.val x.property
      flow_induced := fun b r => by
        rw [C.end_flow, C.ambient.map_flow P.toCompleteLiouvilleManifold e he] }
  refine ⟨h, hsquare, hp, q, ?_⟩
  intro b r
  rw [q.flow_induced, q.inclusion
    ⟨D.domain.boundaryInclusion.map b, D.domain.boundaryInclusion_mem_carrier b⟩]
  rfl

/-- Uniform actual full-fiber inclusion markings on every retained
tailoring ribbon completion. The finite geometric input produces the
complete full fiber and its truncation; no marking is an input. -/
theorem tailoringFamily_exists_uniform_retainedRibbon_fullFiber_markings
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∀ D : LiouvilleDomain (2 * n - 2), D.domain.carrier.Nonempty →
      ∀ W : D.domain.extension.SmoothEmbedding (lgManifold n),
        W.map '' D.domain.carrier = {y | tailoringFamily I β s y = 1 ∧ φ y.1 ≤ A} →
      (∀ x ∈ D.domain.carrier,
        D.liouville.primitive x = D.domain.extension.pullback (lgManifold n) W.map
          (lambdaPotentialForm φ) x) →
      ∀ C : Completion D,
        ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
          (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
          (i : D.domain.Point → N.Point),
          range j.map = {y | tailoringFamily I β s y = 1} ∧
          (∀ x, j.map (i x) = W.map x.val) ∧
          ∃ q : InclusionMarking C P.toCompleteLiouvilleManifold i,
            ∀ b r, q.equiv (C.endMap (b, r)) = P.completeFlow.flow r
              (i ⟨D.domain.boundaryInclusion.map b,
                D.domain.boundaryInclusion_mem_carrier b⟩) := by
  obtain ⟨F, hF, β₀, hβ₀, hfull⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ s hs A hA D hD W hW hμ C
  obtain ⟨N, j, P, himage, hsub⟩ := hfull β hβ s hs
  obtain ⟨hpos, _himage, _hcompletion, _hmarks⟩ := hsub A hA
  obtain ⟨h, hsquare, _hp, q, hqend⟩ := exists_inclusionMarking_of_retained_tailoringRibbon
    I hφ hEnd1 hEnd hhom hc hlower hL hend β s A N j himage P hpos D hD W hW hμ C
  exact ⟨N, j, P, (fun x => h.map x.val), himage,
    (fun x => hsquare x.val x.property), q, hqend⟩

end FsFltz.Geometry
