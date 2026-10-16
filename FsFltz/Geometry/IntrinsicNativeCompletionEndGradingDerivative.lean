import FsFltz.Geometry.IntrinsicNativeCompletionFamilySliceEquiv
import FsFltz.Geometry.IntrinsicNativeCompletionCoframeDescent

/-!
# The actual slice derivative in native cylinder grading coordinates

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244;
`g:chain`, lines 407–413; and `sec:lean`, lines 788–814.
The retained real end inverse agrees with the original cylinder at every
interval parameter. Its original boundary–radial chart differential is
the actual native slice differential preceded by the inverse differential
of the original full cylinder, the original collar-time sign change, and
the original product chart. The inverse-cylinder differential is proved
from the original smooth inverse germ, without an assumed derivative law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section EndCoordinates

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] {δ : ℝ}

local instance endDerivativeBandCoordinateCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance endDerivativeProductCoordinateCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

/-- The original full cylinder written in boundary–outward-radius order.
The cylinder's first coordinate is inward time, so the radius is its negative. -/
def endBandCoordinates (p : Band δ (IntrinsicBoundary.Point k M)) :
    IntrinsicBoundary.Point k M × ℝ := (p.val.2, -p.val.1)

/-- The retained change from cylinder time to outward radius is smooth
for the original cylinder atlas and the original product atlas. -/
theorem contMDiff_endBandCoordinates :
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
      (endBandCoordinates (k := k) (M := M) (δ := δ)) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_snd.comp (contMDiff_band_val δ)).prodMk
    (contMDiff_fst.comp (contMDiff_band_val δ)).neg

/-- The actual boundary–outward-radius coordinates have an invertible
differential, using a smooth local inverse into the original full band. -/
theorem isInvertible_mfderiv_endBandCoordinates (p : Band δ (IntrinsicBoundary.Point k M)) :
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).IsInvertible := by
  classical
  let e := endBandCoordinates (k := k) (M := M) (δ := δ)
  let q : IntrinsicBoundary.Point k M × ℝ → Band δ (IntrinsicBoundary.Point k M) :=
    fun v => if h : -v.2 < δ then ⟨(-v.2, v.1), h, mem_univ _⟩ else p
  have hn : ∀ᶠ v : IntrinsicBoundary.Point k M × ℝ in 𝓝 (e p), -v.2 < δ :=
    (isOpen_lt continuous_snd.neg continuous_const).mem_nhds (by
      change -(-p.val.1) < δ
      simpa only [neg_neg] using (show p.val.1 < δ from p.property.1))
  have hqval : Subtype.val ∘ q =ᶠ[𝓝 (e p)] fun v => (-v.2, v.1) := by
    filter_upwards [hn] with v hv
    simp only [q, Function.comp_apply, dite_eq_left hv]
  have hq : ContMDiffAt 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) ∞ q (e p) := by
    apply contMDiffAt_band_iff_val.mpr
    have hraw : ContMDiff 𝓘(ℝ, Model k × ℝ)
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ (fun v : IntrinsicBoundary.Point k M × ℝ => (-v.2, v.1)) := by
      rw [modelWithCornersSelf_prod (E := Model k) (F := ℝ)]
      exact contMDiff_snd.neg.prodMk contMDiff_fst
    exact hraw.contMDiffAt.congr_of_eventuallyEq hqval
  have hleft : q ∘ e = id := by
    funext p'
    have hp' : -(e p').2 < δ := by
      simpa only [e, endBandCoordinates, neg_neg] using (show p'.val.1 < δ from p'.property.1)
    apply Subtype.ext
    change (q (e p')).val = p'.val
    dsimp only [q]
    rw [dite_eq_left hp']
    simp only [e, endBandCoordinates, neg_neg]
  have hright : e ∘ q =ᶠ[𝓝 (e p)] id := by
    filter_upwards [hn] with v hv
    simp only [Function.comp_apply, q, dite_eq_left hv, e, endBandCoordinates, neg_neg, id_eq]
  have hqp : q (e p) = p := congrFun hleft p
  have hed := contMDiff_endBandCoordinates (k := k) (M := M) (δ := δ)
  have hl : (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model (k + 1)) q (e p)).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) e p) =
        ContinuousLinearMap.id ℝ (Model (k + 1)) := by
    rw [← mfderiv_comp p (hq.mdifferentiableAt (by simp)) (hed.mdifferentiableAt (by simp)),
      hleft, mfderiv_id]
    rfl
  have heqdiff : mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) (e ∘ q) (e p) =
      ContinuousLinearMap.id ℝ (Model k × ℝ) :=
    hright.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  have hr := mfderiv_comp (e p)
    (hed.mdifferentiableAt (by simp) (x := q (e p))) (hq.mdifferentiableAt (by simp))
  rw [heqdiff, hqp] at hr
  exact ContinuousLinearMap.IsInvertible.of_inverse hr.symm hl

end EndCoordinates

section EndDerivative

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

local instance endDerivativeBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance endDerivativeProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance endDerivativeProductSmooth :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

include hC hinv in
/-- The actual full-cylinder inclusion has a continuous inverse
differential in the unchanged original completion atlas. -/
theorem isInvertible_mfderiv_completionCylinder (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) p).IsInvertible := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let A : Model (k + 1) →L[ℝ] Model (k + 1) :=
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) p
  have hA := bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero p
  change A.IsInvertible
  refine ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA.1)
    (LinearMap.range_eq_top.mpr hA.2), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective A _ _

include hC hinv in
/-- The original boundary–radius chart of an actual completion inverse
has the actual slice differential, preceded by the inverse full-cylinder
differential and the retained time-to-radius coordinate change. Agreement
is equality of values on a neighborhood, rather than a derivative hypothesis. -/
theorem mfderiv_endChart_of_completionCylinder_factorization
    (N : SmoothManifold d)
    (S : letI := completionChartedSpace hδ C hemb hboundary hzero
      Diffeomorph 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
        (Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) N.Point ∞)
    (g : N.Point → IntrinsicBoundary.Point k M × ℝ) (y : N.Point)
    (hg : MDifferentiableAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model k × ℝ) g y)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpoint : letI := completionChartedSpace hδ C hemb hboundary hzero
      S.symm y = cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) p)
    (hcoord : endBandCoordinates p = g y)
    (heq : letI := completionChartedSpace hδ C hemb hboundary hzero
      ∀ᶠ z in 𝓝 y, ∃ p' : Band δ (IntrinsicBoundary.Point k M),
        endBandCoordinates p' = g z ∧
        S.symm z = cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val) p')
    (u : IntrinsicBoundary.Point k M × ℝ) (hchart : g y ∈ (chartAt (Model k × ℝ) u).source) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model k × ℝ)
      ((chartAt (Model k × ℝ) u) ∘ g) y =
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (g y)).comp
          ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
            ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
              (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)) p).inverse.comp
              (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model (k + 1)) S.symm y))) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let j := cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)
  obtain ⟨q, hq, hqp, hqright⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero p
  have hj := (contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt
    (by simp) (x := p)
  have hji := isInvertible_mfderiv_completionCylinder hδ C hemb hC hboundary hinv hzero p
  have hleft : q ∘ j =ᶠ[𝓝 p] id := by
    have hn := (continuous_cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C p.val)).continuousAt.eventually
      hqright
    filter_upwards [hn] with p' hp'
    exact cylinder_injective _ hemb.injective hp'
  have hdleft : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) q (j p)).comp
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p) =
        ContinuousLinearMap.id ℝ (Model (k + 1)) := by
    rw [← mfderiv_comp p (hq.mdifferentiableAt (by simp)) hj]
    exact hleft.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  have hqd : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) q (j p) =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse := by
    let J : Model (k + 1) →L[ℝ] Model (k + 1) := mfderiv
      𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p
    let D : Model (k + 1) →L[ℝ] Model (k + 1) := mfderiv
      𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) q (j p)
    have hi : J.IsInvertible := hji
    change D.comp J = ContinuousLinearMap.id ℝ (Model (k + 1)) at hdleft
    change D = J.inverse
    calc
      D = D.comp (ContinuousLinearMap.id ℝ _) := by rw [ContinuousLinearMap.comp_id]
      _ = D.comp (J.comp J.inverse) := by rw [hi.self_comp_inverse]
      _ = (D.comp J).comp J.inverse := (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = J.inverse := by rw [hdleft, ContinuousLinearMap.id_comp]
  have hqS : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ q (S.symm y) := by
    rwa [hpoint]
  have hqSy : q (S.symm y) = p := by rw [hpoint]; exact hqp
  have hnear : (chartAt (Model k × ℝ) u) ∘ g =ᶠ[𝓝 y]
      ((chartAt (Model k × ℝ) u) ∘ endBandCoordinates) ∘ (q ∘ S.symm) := by
    have hqr := S.symm.contMDiff.continuous.continuousAt.eventually (hpoint.symm ▸ hqright)
    filter_upwards [heq, hqr] with z hz hqz
    obtain ⟨p', hp'coord, hp'⟩ := hz
    have hqz' : q (S.symm z) = p' := cylinder_injective _ hemb.injective (hqz.trans hp')
    change chartAt (Model k × ℝ) u (g z) = chartAt (Model k × ℝ) u (endBandCoordinates (q (S.symm z)))
    rw [hqz', hp'coord]
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Model k × ℝ)) u).mdifferentiableAt hchart
  have he := contMDiff_endBandCoordinates (k := k) (M := M) (δ := δ)
  have hψ : MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ)
      ((chartAt (Model k × ℝ) u) ∘ endBandCoordinates) p :=
    (hcoord.symm ▸ hc).comp p (he.mdifferentiableAt (by simp))
  have hqSdiff := hqS.mdifferentiableAt (by simp)
  have hSdiff := S.symm.contMDiff.mdifferentiableAt (by simp) (x := y)
  have hψq : MDifferentiableAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ)
      ((chartAt (Model k × ℝ) u) ∘ endBandCoordinates) ((q ∘ S.symm) y) := by
    change MDifferentiableAt _ _ _ (q (S.symm y))
    rw [hqSy]
    exact hψ
  have hderiv : mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model k × ℝ)
      ((chartAt (Model k × ℝ) u) ∘ g) y = mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model k × ℝ)
        (((chartAt (Model k × ℝ) u) ∘ endBandCoordinates) ∘ (q ∘ S.symm)) y :=
    hnear.mfderiv_eq
  rw [mfderiv_comp y hc hg] at hderiv
  have hψd : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ)
      ((chartAt (Model k × ℝ) u) ∘ endBandCoordinates) ((q ∘ S.symm) y) :
      Model (k + 1) →L[ℝ] (Model k × ℝ)) =
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ) (chartAt (Model k × ℝ) u) (g y)).comp
          (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p) := by
    change mfderiv _ _ _ (q (S.symm y)) = _
    rw [hqSy, mfderiv_comp p (hcoord.symm ▸ hc) (he.mdifferentiableAt (by simp)), hcoord]
  have hqSd : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) q (S.symm y) :
      Model (k + 1) →L[ℝ] Model (k + 1)) =
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j p).inverse := by
    rw [hpoint]
    exact hqd
  rw [mfderiv_comp y hc hg, hderiv, mfderiv_comp y hψq (hqSdiff.comp y hSdiff),
    mfderiv_comp y hqSdiff hSdiff, hψd, hqSd]
  rfl

end EndDerivative

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


local instance endGradingDerivativeBandCharts :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance endGradingDerivativeProductCharts :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- Equality with the retained total cylinder inverse forces equality
with the literal original completion slice inverse on that cylinder. -/
theorem ambientNativeSliceDiffeomorph_symm_eq_cylinder_of_total
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (heq : (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
      totalCylinder (fun t p => C t p.val) (s, p)) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
      hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y =
        cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) p := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  apply sliceIn_injective (fun t p => C t p.val) s
  rw [Q.sliceIn_ambientNativeSliceDiffeomorph_symm hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend, heq]
  exact (sliceIn_cylinder (fun t p => C t p.val) s p).symm

include hdim α hp hc hb hsquareB hR hC hboundary hinv hzero hjoint hmix hode in
/-- At every interval parameter, the spatial differential of the produced
end inverse in the original boundary–radius chart is the derivative of
the actual native slice inverse in those same coordinates. The exact
cylinder point is retained, including the sign of collar time. -/
theorem ambientNativeSliceDiffeomorph_symm_endChart_mfderiv
    (U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)) (hU : IsOpen U)
    (g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ)
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U)
    (heq : ∀ (s : Parameter) y, (s.val, y) ∈ U →
      ∃ p : Band δ (IntrinsicBoundary.Point k M),
        p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
        (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
          totalCylinder (fun t p => C t p.val) (s, p))
    (s : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point)
    (hy : (s.val, y) ∈ U) (u : IntrinsicBoundary.Point k M × ℝ)
    (hchart : g (s.val, y) ∈ (chartAt (Model k × ℝ) u).source)
    (p : Band δ (IntrinsicBoundary.Point k M))
    (hpcoord : p.val = (-(g (s.val, y)).2, (g (s.val, y)).1)) :
    letI := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => chartAt (Model k × ℝ) u (g (s.val, z))) y =
        (mfderiv 𝓘(ℝ, Model k × ℝ) 𝓘(ℝ, Model k × ℝ)
          (chartAt (Model k × ℝ) u) (g (s.val, y))).comp
          ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k × ℝ) endBandCoordinates p).comp
            ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
              (cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val)) p).inverse.comp
              (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
                (Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
                  hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s).symm y))) := by
  let := completionChartedSpace hδ (C s) (hemb s) (hboundary s) (hzero s)
  let S := Q.ambientNativeSliceDiffeomorph hdim α e hp hc b hb hsquareB R hR hsquareA
    hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s
  have hgm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model k × ℝ) ∞ g U := by
    rwa [modelWithCornersSelf_prod]
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => g (s.val, z)) y :=
    ((hgm.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hcoord : endBandCoordinates p = g (s.val, y) := by
    dsimp only [endBandCoordinates]
    rw [hpcoord]
    simp only [neg_neg]
  have hpoint : S.symm y = cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) p := by
    obtain ⟨p', hp'coord, hp'⟩ := heq s y hy
    have hpp : p' = p := Subtype.ext (hp'coord.trans hpcoord.symm)
    rw [hpp] at hp'
    exact Q.ambientNativeSliceDiffeomorph_symm_eq_cylinder_of_total hdim α e hp hc b hb hsquareB
      R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s y p hp'
  have hUy : ∀ᶠ z in 𝓝 y, (s.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  have hs : ∀ᶠ z in 𝓝 y, ∃ p' : Band δ (IntrinsicBoundary.Point k M),
      endBandCoordinates p' = g (s.val, z) ∧
        S.symm z = cylinder (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) p' := by
    filter_upwards [hUy] with z hz
    obtain ⟨p', hp'coord, hp'⟩ := heq s z hz
    refine ⟨p', ?_, ?_⟩
    · dsimp only [endBandCoordinates]
      rw [hp'coord]
      simp only [neg_neg]
    · exact Q.ambientNativeSliceDiffeomorph_symm_eq_cylinder_of_total hdim α e hp hc b hb hsquareB
        R hR hsquareA hδ C hemb hC hboundary hinv hzero hjoint hmix hode q hqnative hqend s z p' hp'
  exact mfderiv_endChart_of_completionCylinder_factorization hδ (C s) (hemb s) (hC s)
    (hboundary s) (hinv s) (hzero s) Q.source.ambientManifold S (fun z => g (s.val, z))
    y hgs p hpoint hcoord hs u hchart

end FsFltz.Geometry.PairDeformation
