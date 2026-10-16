import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalMapExtensionData
import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalChartChanges
import FsFltz.Geometry.IntrinsicNativeCompletionCanonicalCoordinateTopology
import FsFltz.Geometry.RealOpenMapExtension

/-!
# Chart independence of real-open extensions into the original canonical bundle

Source: `geoemtric-part-fsf.tex`, smooth-extension convention (119–122),
`def:maslov` (212–244), and `sec:lean` (766–836). Arbitrary full bundle maps
are transferred between independently constructed original charts by the
proved actual real-open chart changes. Projection continuity permits
shrinking to the target overlap; for section graphs the projection is the
identity. No extension theorem from bare boundary smoothness is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}
  (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hmix : HasRealMixedGerms (δ := δ) C)
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

include hjoint hC hinv hmix P in
/-- A local extension of the entire map in some covering charts gives one
in every pair of covering original charts, after shrinking. -/
theorem originalTotalChartMapExtensions_of_localMapExtensions
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hf : Continuous (fun x => (f x).proj))
    (hlocal : HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f) :
    HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f := by
  intro c d p hp hdp
  obtain ⟨e, j, r, hr, hrp, hfj, U, G, hrU, hG, hUe, hret⟩ := hlocal (c.inclusion p)
  obtain ⟨A, hpA, hAr, hAf, _⟩ := exists_originalTotalCanonicalBaseChangeGerm
    hδ C hemb hboundary hzero J hjoint hmix c e p r hp hr hrp.symm
  obtain ⟨B, hfjB, _, hBf, _⟩ := exists_originalTotalCanonicalChartChangeGerm
    hδ C hemb hboundary hzero J N hjoint hC hinv hmix P j d (f (c.inclusion p)) hfj hdp
  have hGr : G (e.baseCoordinate r) =
      j.coordinateAt N hjoint hC hinv (f (c.inclusion p)) hfj := by
    obtain ⟨hj, hgj⟩ := hret r hr hrU
    simpa only [hrp] using hgj
  obtain ⟨V, hpV, hVA, hVU, hHV⟩ := RealOpenMapExtension.exists_composition_domain
    A B U G hG hpA (hAr.symm ▸ hrU) (by rw [hAr, hGr]; exact hfjB)
  have hOe : IsOpen e.totalDomain := by
    rw [e.totalDomain_eq_baseSet N hjoint hC hinv]
    exact (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero
      hjoint J N hC hinv e).open_baseSet
  have hOd : IsOpen d.totalDomain := by
    rw [d.totalDomain_eq_baseSet N hjoint hC hinv]
    exact (originalTotalCanonicalTensorPretrivialization hδ C hemb hboundary hzero
      hjoint J N hC hinv d).open_baseSet
  obtain ⟨Ve, hpVe, hVec, hVe⟩ := c.exists_rawCoordinate_neighborhood hjoint p hp hOe
    (show c.inclusion p ∈ e.totalDomain from ⟨r, hr, hrp⟩)
  obtain ⟨Vd, hpVd, hVdc, hVd⟩ := c.exists_rawCoordinate_neighborhood hjoint p hp
    (hOd.preimage hf) hdp
  let W : TopologicalSpace.Opens c.RealBase := (V ⊓ Ve) ⊓ Vd
  refine ⟨W, fun y => B (G (A y)), ⟨⟨hpV, hpVe⟩, hpVd⟩,
    hHV.mono (fun _ hy => hy.1.1), (fun _ hy => hVec hy.1.2), ?_⟩
  intro q hq hqW
  have hqe : c.inclusion q ∈ e.totalDomain := hVe q hq hqW.1.2
  have hqd : (f (c.inclusion q)).proj ∈ d.totalDomain := hVd q hq hqW.2
  have hAq : A (c.baseCoordinate q) = e.baseCoordinate hqe.choose :=
    hAf q hqe.choose hq hqe.choose_spec.1 hqe.choose_spec.2.symm (hVA hqW.1.1)
  have hqU : e.baseCoordinate hqe.choose ∈ U := hAq ▸ (hVU _ hqW.1.1).1
  obtain ⟨hqj, hGq⟩ := hret hqe.choose hqe.choose_spec.1 hqU
  have hGq' : G (e.baseCoordinate hqe.choose) =
      j.coordinateAt N hjoint hC hinv (f (c.inclusion q))
        (hqe.choose_spec.2 ▸ hqj) := by
    simpa only [hqe.choose_spec.2] using hGq
  refine ⟨hqd, ?_⟩
  change B (G (A (c.baseCoordinate q))) = _
  rw [hAq, hGq']
  apply hBf
  have hBq := (hVU _ hqW.1.1).2
  rwa [hAq, hGq'] at hBq

include hjoint hC hinv P in
/-- Actual section-independent chart coverage supplies covering charts for
the source and image of any map. Thus the all-chart condition is not vacuous. -/
theorem originalTotalLocalMapExtensions_of_chartMapExtensions
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hchart : HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f) :
    HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f := by
  intro x
  obtain ⟨c, hxc⟩ := exists_originalTotalCanonicalChart
    hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq x
  obtain ⟨d, hfd⟩ := exists_originalTotalCanonicalChart
    hδ C hemb hboundary hzero hjoint J N hC hinv P hJI hJE hJsq (f x).proj
  rw [← c.totalDomain_eq_baseSet N hjoint hC hinv] at hxc
  rw [← d.totalDomain_eq_baseSet N hjoint hC hinv] at hfd
  rcases hxc with ⟨p, hp, hpx⟩
  refine ⟨c, d, p, hp, hpx, hfd, ?_⟩
  simpa only [hpx] using hchart c d p hp (hpx.symm ▸ hfd)

include hjoint hC hinv hmix P in
/-- The source's local extension convention is independent of all covering
original charts, using the actual coframe cover and real-open changes. -/
theorem originalTotalLocalMapExtensions_iff_chartMapExtensions
    (hJI : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJE : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
      Bundle.TotalSpace ℂ (OriginalTotalCanonicalTensorSquare C J N))
    (hf : Continuous (fun x => (f x).proj)) :
    HasOriginalTotalLocalMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f ↔
      HasOriginalTotalChartMapExtensions hδ C hemb hboundary hzero J N hjoint hC hinv f :=
  ⟨originalTotalChartMapExtensions_of_localMapExtensions
      hδ C hemb hboundary hzero J N hjoint hC hinv hmix P f hf,
    originalTotalLocalMapExtensions_of_chartMapExtensions
      hδ C hemb hboundary hzero J N hjoint hC hinv P hJI hJE hJsq f⟩

end FsFltz.Geometry.IntrinsicCompletionGluing
