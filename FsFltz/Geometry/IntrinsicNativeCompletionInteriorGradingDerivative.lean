import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCoframeDescent

/-!
# The actual slice derivative in native interior grading coordinates

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
The retained real inverse germ agrees with the original slice inverse at
every interval parameter. Differentiating this agreement identifies its
interior-chart derivative with the actual slice derivative, preceded by
the inverse differential of the original interior inclusion and the original
interior chart. No smooth inverse family or derivative equation is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section InteriorDerivative

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
  (hC : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ p : Half δ (IntrinsicBoundary.Point k M),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C p.val) ↔ p.val.1 = 0)
  (hinv : ∀ p ∈ Half δ (IntrinsicBoundary.Point k M),
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C q) = q)
  (hzero : ∀ b : IntrinsicBoundary.Point k M, C (0, b) = b.val)

include hC hinv in
/-- The actual native interior inclusion has a continuous inverse
differential in the original completion atlas. -/
theorem isInvertible_mfderiv_completionInterior (w : IntrinsicInterior.Point k M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) w).IsInvertible := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let A : Model (k + 1) →L[ℝ] Model (k + 1) :=
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
    (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) w
  have hA := bijective_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero w
  change A.IsInvertible
  refine ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA.1)
    (LinearMap.range_eq_top.mpr hA.2), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective A _ _

include hC hinv in
/-- Differentiate an actual local interior factorization of a completion
slice map, then express it in the fixed original interior chart. The only
agreement hypothesis is equality of values on a neighborhood. -/
theorem mfderiv_interiorChart_of_completionInterior_factorization
    (N : SmoothManifold d)
    (S : letI := completionChartedSpace hδ C hemb hboundary hzero
      Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
        (Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) N.Point ∞)
    (g : N.Point → IntrinsicInterior.Point k M) (y : N.Point)
    (hg : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) g y)
    (heq : letI := completionChartedSpace hδ C hemb hboundary hzero
      S.symm =ᶠ[𝓝 y]
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) ∘ g))
    (u : IntrinsicInterior.Point k M) (hchart : g y ∈ (chartAt (Model (k + 1)) u).source) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1))
      ((chartAt (Model (k + 1)) u) ∘ g) y =
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
          (chartAt (Model (k + 1)) u) (g y)).comp
          ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
            (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val))
            (g y)).inverse.comp
            (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) S.symm y)) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let j := interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
  have hj := (contMDiff_completionInterior hδ C hemb hC hboundary hinv hzero).mdifferentiableAt
    (by simp) (x := g y)
  have hd : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) S.symm y =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j (g y)).comp
        (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) g y) := by
    exact heq.mfderiv_eq.trans (mfderiv_comp y hj hg)
  have hji := isInvertible_mfderiv_completionInterior hδ C hemb hC hboundary hinv hzero (g y)
  rw [mfderiv_comp y ((mdifferentiable_chart (I := 𝓘(ℝ, Model (k + 1))) u).mdifferentiableAt
    hchart) hg, hd]
  ext v
  simp only [j, ContinuousLinearMap.comp_apply, hji.inverse_apply_self]

end InteriorDerivative

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
  (α : Parameter → Form k M 1)
  (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair t).ambientDomain.domain.Point ∞)
  (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
  (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
    (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
  (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair t).ambientDomain.domain.boundary)
  (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
  (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
    (e parameterZero (R t.val x)).val = (e t x).val)
  {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
    (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Equality with the total interior inverse forces equality with the
literal original completion slice inverse, using the original slice inclusion. -/
theorem ambientNativeSliceDiffeomorph_symm_eq_interior_of_total
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (w : IntrinsicInterior.Point k M)
    (heq : (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
      totalInterior (fun t p => C t p.val) (s, w)) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y =
        interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) w := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  apply sliceIn_injective (fun t p => C t p.val) s
  rw [Q.sliceIn_ambientNativeSliceDiffeomorph_symm hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend, heq]
  exact (sliceIn_original (fun t p => C t p.val) s w.val).symm

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- On each interval slice, the spatial differential of the produced real
interior inverse germ in the retained interior chart is the differential
of the original native slice inverse in those same coordinates. The
native inclusion differential is inverted only after its invertibility
has been proved; agreement is required solely at interval values. -/
theorem ambientNativeSliceDiffeomorph_symm_interiorChart_mfderiv
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ g U)
    (heq : ∀ (s : Parameter) y, (s.val, y) ∈ U →
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
        totalInterior (fun t p => C t p.val) (s, g (s.val, y)))
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val, y) ∈ U) (u : IntrinsicInterior.Point k M)
    (hchart : g (s.val, y) ∈ (chartAt (Model (k + 1)) u).source) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => chartAt (Model (k + 1)) u (g (s.val, z))) y =
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
          (chartAt (Model (k + 1)) u) (g (s.val, y))).comp
          ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
            (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val))
            (g (s.val, y))).inverse.comp
            (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
              (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
                hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y)) := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let S := Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => g (s.val, z)) y :=
    ((hg.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hUy : ∀ᶠ z in 𝓝 y, (s.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  have hs : S.symm =ᶠ[𝓝 y]
      (interiorIn (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) ∘
        fun z => g (s.val, z)) := by
    filter_upwards [hUy] with z hz
    exact Q.ambientNativeSliceDiffeomorph_symm_eq_interior_of_total hdim α e hp hc b hb hsquareB
      R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend
      s z (g (s.val, z)) (heq s z hz)
  exact mfderiv_interiorChart_of_completionInterior_factorization hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s) Q.source.ambientManifold S (fun z => g (s.val, z))
    y hgs hs u hchart

end FsFltz.Geometry.PairDeformation
