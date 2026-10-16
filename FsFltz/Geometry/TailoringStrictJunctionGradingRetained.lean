import FsFltz.Geometry.TailoringStrictJunctionGrading

/-!
# The retained strict junction with its actual ambient grading map

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1919,
`lem:grading`, lines 1994–2030, and `sec:assembly`, lines 2159–2233.
Regional hitting data construct the strict map and witness interpolation.
Their grading retains the very incoming map and its compact native square.
The completed hitting lift is the final specified geometric arrow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Regional hitting equations and an actual lift on this completed hitting
family produce the three-arrow graded incoming junction, retaining the
same strict marking and the tensor it pulls back. -/
theorem CompletedHittingRibbonFamily.exists_graded_strictJunction_of_regional_hits
    {n : ℕ} (P : WitnessedPair n)
    {D : CompactDomain (2 * n)} {L : Parameter → LiouvilleStructure D}
    {j : Parameter → P.ribbonDomain.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D P.ribbonDomain L j b)
    (i : P.ambientDomain.domain.Point →
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient.manifold.Point)
    (q : InclusionMarking P.ambientCompletion
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient i)
    (M : SmoothManifold (2 * n)) (e : D.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hprimitive : (L parameterZero).primitive = D.extension.pullback M e.map α)
    (ρ : M.Point → ℝ) (hρ : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ ρ)
    (A k : ℝ) (himage : e.map '' D.carrier = {y | ρ y ≤ A})
    (hnd : ∀ y, ρ y ≤ A → M.Nondegenerate (M.exteriorDerivative α) y)
    (G : Flow ℝ (ℝ × M.Point))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × M.Point) => G p.1 p.2))
    (hnative : ∀ y t, ρ (G t (k, y)).2 ≤ A →
      IsMIntegralCurveAt (fun s => (G s (k, y)).2) (M.liouvilleVector α) t)
    (hout : ∀ y, ρ y = A → 0 < M.scalarDerivative ρ y (M.liouvilleVector α y))
    (τ : P.ribbonDomain.domain.extension.Point → ℝ)
    (start : P.ribbonDomain.domain.extension.Point → M.Point)
    (hstart : ∀ x ∈ P.ribbonDomain.domain.carrier,
      e.map ((H.ambient.collars parameterZero).originalInclusion.map
        (i ⟨P.ambientDomain.domain.boundaryInclusion.map (P.ribbonEmbedding.map x),
          P.ambientDomain.domain.boundaryInclusion_mem_carrier (P.ribbonEmbedding.map x)⟩)) = start x)
    (htime : ∀ x ∈ P.ribbonDomain.domain.carrier, 0 < τ x)
    (hboundary : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ρ (e.map (D.boundaryInclusion.map ((j parameterZero).map x))) = A)
    (hhit : ∀ x ∈ P.ribbonDomain.domain.carrier,
      (G (τ x) (k, start x)).2 = e.map (D.boundaryInclusion.map ((j parameterZero).map x)))
    (hwitness : ∀ x ∈ P.ribbonDomain.domain.carrier,
      b parameterZero ((j parameterZero).map x) = Real.exp (-τ x))
    (hne : P.ribbonDomain.domain.carrier.Nonempty)
    (u : H.deformation.source.Maslov) (v : H.deformation.target.Maslov)
    (gH : GradedPairDeformation H.deformation u v) :
    ∃ J : StrictHittingJunction P H.deformation,
      ∃ datum : P.Maslov,
        HEq J.identification.ambientEquiv q.equiv ∧
        datum.tensor = pullbackSquaredTensor P.ambientManifold
          H.deformation.source.ambientManifold q.equiv u.tensor ∧
        Nonempty (GradedComparisonChain P J.chain datum v) := by
  let A₀ := H.ambient.collars parameterZero
  let F₀ := H.ribbon.collars parameterZero
  let Q := H.deformation.source
  obtain ⟨ψ, s, hs, hend, hcontact, hwhole⟩ :=
    A₀.exists_boundaryEquiv_of_regional_cutoff_ribbon_hits P i q M e α hα hprimitive
      ρ hρ A k himage hnd G hG hnative hout (j parameterZero).map τ start
      hstart htime hboundary hhit
  obtain ⟨h, hproj, hp⟩ := F₀.exists_originalCompactComparison hne
  have hsquare : ∀ x ∈ P.ribbonDomain.domain.carrier,
      ψ (P.ribbonEmbedding.map x) = Q.ribbonEmbedding.map (h.map x) := by
    intro x hx
    change ψ (P.ribbonEmbedding.map x) = (j parameterZero).map (F₀.originalInclusion.map (h.map x))
    rw [hproj x (h.contains_source hx)]
    exact (hwhole x hx).1
  have hshift : ∀ x ∈ P.ribbonDomain.domain.carrier, s (P.ribbonEmbedding.map x) = -τ x :=
    fun x hx => (hwhole x hx).2
  have hw : ∀ x ∈ P.ribbonDomain.domain.carrier,
      Q.witness (Q.ribbonEmbedding.map (h.map x)) = Real.exp (-τ x) := by
    intro x hx
    change b parameterZero ((j parameterZero).map (F₀.originalInclusion.map (h.map x))) = _
    rw [hproj x (h.contains_source hx)]
    exact hwitness x hx
  have hc : P.ambientDomain.domain.boundary.pullback Q.ambientDomain.domain.boundary ψ
      (Q.ambientDomain.domain.boundaryForm Q.ambientDomain.liouville.primitive) =
      fun x => Real.exp (-s x) •
        P.ambientDomain.domain.boundaryForm P.ambientDomain.liouville.primitive x := by
    change P.ambientDomain.domain.boundary.pullback D.boundary ψ
      (A₀.localizedDomain.domain.boundaryForm A₀.localizedDomain.liouville.primitive) = _
    rw [A₀.localized_boundaryForm]
    exact hcontact
  exact StrictHittingJunction.exists_graded_of_strict_maps P H.deformation
    q.equiv q.primitive ψ s hs hend hc h hp τ hsquare hshift hw u v gH

local instance strictJunctionGradingLGCharts {n : ℕ} : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance strictJunctionGradingLGSmooth {n : ℕ} : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

/-- The retained marked prefix supplies the actual comparison map into this
same hitting collar. The native compact square and induced source tensor
remain visible alongside the grading of the exact constructed junction. -/
theorem PotentialTailoringMarkedPrefix.exists_graded_strictJunction_into_retained_hitting
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ)
    (S : IntrinsicShrinkingData P.tailoring.deformation.target)
    {L : Parameter → LiouvilleStructure P.tailoring_ambient_marking.domain}
    {j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
      P.tailoring_ambient_marking.domain.boundary}
    {b : Parameter → P.tailoring_ambient_marking.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily P.tailoring_ambient_marking.domain
      (S.pair parameterOne).ribbonDomain L j b)
    (hL : (L parameterZero).primitive = P.tailoring_ambient_marking.domain.extension.pullback
      (lgManifold n) P.tailoring_ambient_marking.nativeEmbedding.map
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K))
    (hboundary : range (P.tailoring_ambient_marking.nativeEmbedding.comp
      P.tailoring_ambient_marking.domain.boundaryInclusion).map =
      {y | φ y.1 = Cplus ^ 2 * β ^ 2 / 2})
    (hnd : ∀ y : LGSpace n, (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) y)
    (hout : ∀ y : LGSpace n, φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K) y))
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hnative : ∀ y t, φ (G t (K, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
      IsMIntegralCurveAt (fun s => (G s (K, y)).2)
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t)
    (τ : (S.pair parameterOne).ribbonDomain.domain.extension.Point → ℝ)
    (htime : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier, 0 < τ x)
    (hhit : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      (G (τ x) (K, (P.tailoring.ribbon_marking parameterOne).embedding.map
        ((S.fiberEmbedding (P.tailoring.ribbon_marking parameterOne) parameterOne).map x))).2 =
      (P.tailoring_ambient_marking.nativeEmbedding.comp
        P.tailoring_ambient_marking.domain.boundaryInclusion).map ((j parameterZero).map x))
    (hwitness : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      b parameterZero ((j parameterZero).map x) = Real.exp (-τ x))
    (u : H.deformation.source.Maslov) (v : H.deformation.target.Maslov)
    (gH : GradedPairDeformation H.deformation u v) :
    ∃ i : (S.pair parameterOne).ambientDomain.domain.Point →
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient.manifold.Point,
      ∃ q : InclusionMarking (S.pair parameterOne).ambientCompletion
        (H.ambient.collars parameterZero).cylindricalCompletion.ambient i,
        (∀ x : (S.pair parameterOne).ambientDomain.domain.Point,
          (P.tailoring_ambient_marking.nativeEmbedding.comp
            (H.ambient.collars parameterZero).originalInclusion).map (i x) =
              (P.tailoring.embedding parameterOne).map x.val) ∧
        ∃ J : StrictHittingJunction (S.pair parameterOne) H.deformation,
          ∃ datum : (S.pair parameterOne).Maslov,
            HEq J.identification.ambientEquiv q.equiv ∧
            datum.tensor = pullbackSquaredTensor (S.pair parameterOne).ambientManifold
              H.deformation.source.ambientManifold q.equiv u.tensor ∧
            Nonempty (GradedComparisonChain (S.pair parameterOne) J.chain datum v) := by
  let O := P.tailoring_ambient_marking
  let F := S.pair parameterOne
  let M := P.tailoring.ribbon_marking parameterOne
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K
  obtain ⟨i, q, hi⟩ := P.exists_marking_into_hitting_collar (L parameterZero)
    (H.ambient.collars parameterZero) hL
  have hstart : ∀ x ∈ F.ribbonDomain.domain.carrier,
      O.nativeEmbedding.map ((H.ambient.collars parameterZero).originalInclusion.map
        (i ⟨F.ambientDomain.domain.boundaryInclusion.map (F.ribbonEmbedding.map x),
          F.ambientDomain.domain.boundaryInclusion_mem_carrier (F.ribbonEmbedding.map x)⟩)) =
        M.embedding.map ((S.fiberEmbedding M parameterOne).map x) := by
    intro x hx
    exact (hi ⟨F.ambientDomain.domain.boundaryInclusion.map (F.ribbonEmbedding.map x),
      F.ambientDomain.domain.boundaryInclusion_mem_carrier (F.ribbonEmbedding.map x)⟩).trans
      (S.fiberEmbedding_compact M parameterOne x hx).symm
  have himage : O.nativeEmbedding.map '' O.domain.carrier =
      {y : LGSpace n | φ y.1 ≤ Cplus ^ 2 * β ^ 2 / 2} := by
    rw [O.native_image]
    ext y
    change φ y.1 - Cplus ^ 2 * β ^ 2 / 2 ≤ 0 ↔ φ y.1 ≤ Cplus ^ 2 * β ^ 2 / 2
    exact sub_nonpos
  have hhitboundary : ∀ x ∈ F.ribbonDomain.domain.carrier,
      φ (O.nativeEmbedding.map (O.domain.boundaryInclusion.map ((j parameterZero).map x))).1 =
        Cplus ^ 2 * β ^ 2 / 2 := by
    intro x _
    exact (Set.ext_iff.mp hboundary _).mp (mem_range_self ((j parameterZero).map x))
  obtain ⟨J, datum, hmap, htensor, gJ⟩ := H.exists_graded_strictJunction_of_regional_hits F i q (lgManifold n) O.nativeEmbedding α
    ((lgManifold n).isSmoothForm_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_tailoringFamily_lgManifold I β 1) K)
    hL (fun y => φ y.1) (contMDiff_potentialValue hφ) (Cplus ^ 2 * β ^ 2 / 2) K
    himage (fun y _ => hnd y) G hG hnative hout τ
    (fun x => M.embedding.map ((S.fiberEmbedding M parameterOne).map x))
    hstart htime hhitboundary hhit hwitness
    (S.pair_ribbon_nonempty (P.tailoring.ribbon_nonempty parameterOne) parameterOne) u v gH
  exact ⟨i, q, hi, J, datum, hmap, htensor, gJ⟩

end FsFltz
