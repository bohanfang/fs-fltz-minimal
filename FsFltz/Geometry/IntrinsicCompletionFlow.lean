import FsFltz.Geometry.IntrinsicCompletionPrimitive
import FsFltz.Geometry.PrescribedCylinderCompleteFlow

/-!
# Complete flow on the actual intrinsic half-infinite quotient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and `sec:lean`,
lines 783–814. Native boundary charts give actual outward cylinder charts
with radius `r = -t`. Their derivatives, primitive laws and compact-complement
coverage are derived on the constructed quotient, before applying compact
continuation. No radial ODE or complete flow is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

section BoundaryCharts

variable {k : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Model k) B]
  [IsManifold 𝓘(ℝ, Model k) ∞ B] {δ : ℝ} (hδ : 0 < δ)

/-- Actual outward coordinates, with an existing boundary point as fallback
outside their open radial domain. This does not assume an inhabited boundary. -/
def outwardChartBand (b : B) (p : ℝ × Model k) : Band δ B :=
  if hp : -p.1 < δ then ⟨(-p.1, (chartAt (Model k) b).symm p.2), hp, mem_univ _⟩
  else ⟨(0, b), hδ, mem_univ _⟩

omit [IsManifold 𝓘(ℝ, Model k) ∞ B] in
theorem outwardChartBand_val (b : B) {p : ℝ × Model k} (hp : -δ < p.1) :
    (outwardChartBand hδ b p).val = (-p.1, (chartAt (Model k) b).symm p.2) := by
  simp only [outwardChartBand, dite_eq_left (by linarith : -p.1 < δ)]

local instance : ChartedSpace (Model (k + 1)) (Band δ B) := bandChartedSpace δ
local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ B) := band_isManifold δ

/-- Native boundary-chart inverses and sign reversal produce smooth coordinates
on the full, unbounded attached cylinder. -/
theorem contMDiffAt_outwardChartBand (b : B) {p : ℝ × Model k}
    (hp : p ∈ Ioi (-δ) ×ˢ (chartAt (Model k) b).target) :
    ContMDiffAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞
      (outwardChartBand hδ b) p := by
  apply contMDiffAt_band_iff_val.mpr
  have hb := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Model k)) (n := ∞)
      (chart_mem_atlas (Model k) b)) hp.2
  have hs : ContMDiffAt 𝓘(ℝ, ℝ × Model k) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞
      (fun q : ℝ × Model k => (-q.1, (chartAt (Model k) b).symm q.2)) p :=
    by
      have hf : ContMDiffAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, ℝ) ∞ Prod.fst p :=
        (contDiff_fst (𝕜 := ℝ) (n := ∞)).contMDiff.contMDiffAt
      have hg : ContMDiffAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model k) ∞ Prod.snd p :=
        (contDiff_snd (𝕜 := ℝ) (n := ∞)).contMDiff.contMDiffAt
      exact hf.neg.prodMk (hb.comp p hg)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.prod (chartAt (Model k) b).open_target).mem_nhds hp]
    with q hq
  exact outwardChartBand_val hδ b hq.1

/-- The actual boundary projection in these coordinates has the standard
spatial differential, including its zero radial coefficient. -/
theorem mfderiv_boundaryProjection_outwardChartBand (b : B) {p : ℝ × Model k}
    (hp : p ∈ Ioi (-δ) ×ˢ (chartAt (Model k) b).target) :
    (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k)
      (fun q : Band δ B => q.val.2) (outwardChartBand hδ b p)).comp
        (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1))
          (outwardChartBand hδ b) p) =
      (mfderiv 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) (chartAt (Model k) b).symm p.2).comp
        (ContinuousLinearMap.snd ℝ ℝ (Model k)) := by
  have hproj := contMDiff_snd.comp (contMDiff_band_val (k := k) (B := B) δ)
  have hb := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Model k)) (n := ∞)
      (chart_mem_atlas (Model k) b)) hp.2
  have heq : ((fun q : Band δ B => q.val.2) ∘ outwardChartBand hδ b) =ᶠ[𝓝 p]
      (chartAt (Model k) b).symm ∘ Prod.snd := by
    filter_upwards [(isOpen_Ioi.prod (chartAt (Model k) b).open_target).mem_nhds hp]
      with q hq
    exact congrArg Prod.snd (outwardChartBand_val hδ b hq.1)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ × Model k)) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, Model k)) p (hproj.mdifferentiableAt (by simp))
    ((contMDiffAt_outwardChartBand hδ b hp).mdifferentiableAt (by simp))
  have he := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ × Model k)) (I' := 𝓘(ℝ, Model k))
  have hright := mfderiv_comp (I := 𝓘(ℝ, ℝ × Model k)) (I' := 𝓘(ℝ, Model k))
    (I'' := 𝓘(ℝ, Model k)) p (hb.mdifferentiableAt (by simp))
    (show MDifferentiableAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model k) Prod.snd p from
      (hasMFDerivAt_iff_hasFDerivAt.mpr hasFDerivAt_snd).mdifferentiableAt)
  rw [mfderiv_eq_fderiv, hasFDerivAt_snd.fderiv] at hright
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun A => A v) hchain).symm.trans
    ((congrArg (fun A => A v) he).trans (congrArg (fun A => A v) hright))

/-- The outward chart has an actual smooth right inverse germ, so its
differential covers every tangent of the attached cylinder. -/
theorem surjective_mfderiv_outwardChartBand (b : B) {p : ℝ × Model k}
    (hp : p ∈ Ioi (-δ) ×ˢ (chartAt (Model k) b).target) :
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1))
      (outwardChartBand hδ b) p) := by
  let q := outwardChartBand hδ b p
  let g : Band δ B → ℝ × Model k := fun z => (-z.val.1, chartAt (Model k) b z.val.2)
  have hq : q.val = (-p.1, (chartAt (Model k) b).symm p.2) :=
    outwardChartBand_val hδ b hp.1
  have hqs : q.val.2 ∈ (chartAt (Model k) b).source := by
    rw [hq]
    exact (chartAt (Model k) b).map_target hp.2
  have hg : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ × Model k) ∞ g q := by
    have hv := (contMDiff_band_val (k := k) (B := B) δ).contMDiffAt (x := q)
    have hb := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Model k)) (n := ∞)
        (chart_mem_atlas (Model k) b)) hqs
    exact (contMDiffAt_fst.comp q hv).neg.prodMk_space
      (hb.comp q (contMDiffAt_snd.comp q hv))
  have hgp : g q = p := by
    simp only [g, hq, neg_neg, (chartAt (Model k) b).right_inv hp.2, Prod.mk.eta]
  have heq : outwardChartBand hδ b ∘ g =ᶠ[𝓝 q] id := by
    have hs : ∀ᶠ z : Band δ B in 𝓝 q, z.val.2 ∈ (chartAt (Model k) b).source :=
      (continuous_snd.comp continuous_subtype_val).continuousAt.eventually
        ((chartAt (Model k) b).open_source.mem_nhds hqs)
    filter_upwards [hs] with z hz
    apply Subtype.ext
    have hr : -δ < (g z).1 := neg_lt_neg (show z.val.1 < δ from z.property.1)
    change (outwardChartBand hδ b (g z)).val = z.val
    rw [outwardChartBand_val hδ b hr]
    simp only [g, neg_neg, (chartAt (Model k) b).left_inv hz, Prod.mk.eta]
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1))
      (outwardChartBand hδ b) (g q) := by
    rw [hgp]
    exact (contMDiffAt_outwardChartBand hδ b hp).mdifferentiableAt (by simp)
  have hd := mfderiv_comp (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, ℝ × Model k))
    (I'' := 𝓘(ℝ, Model (k + 1))) q hf (hg.mdifferentiableAt (by simp))
  have hid : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (outwardChartBand hδ b ∘ g) q = ContinuousLinearMap.id ℝ _ :=
    heq.mfderiv_eq.trans (by rw [mfderiv_id]; rfl)
  rw [hid, hgp] at hd
  intro v
  exact ⟨mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ × Model k) g q v,
    (congrArg (fun A => A v) hd).symm⟩

end BoundaryCharts

section Native

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]
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

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ
local instance : IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

/-- A native boundary chart parametrizes the actual quotient cylinder at every
outward radius `r > -δ`. -/
def outwardChart (b : IntrinsicBoundary.Point k M) (p : ℝ × Model k) :
    Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) :=
  cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
    (outwardChartBand hδ b p)

include hemb hC hboundary hinv hzero in
omit [T2Space M] [SecondCountableTopology M] in
theorem contMDiffOn_outwardChart (b : IntrinsicBoundary.Point k M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ContMDiffOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞
      (outwardChart hδ C b) (Ioi (-δ) ×ˢ (chartAt (Model k) b).target) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  intro p hp
  exact ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).contMDiffAt.comp p
    (contMDiffAt_outwardChartBand hδ b hp)).contMDiffWithinAt

include hemb hC hboundary hinv hzero in
omit [T2Space M] [SecondCountableTopology M] in
theorem surjective_mfderiv_outwardChart (b : IntrinsicBoundary.Point k M)
    {p : ℝ × Model k} (hp : p ∈ Ioi (-δ) ×ˢ (chartAt (Model k) b).target) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1))
      (outwardChart hδ C b) p) := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  change Function.Surjective (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1))
    (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) ∘
      outwardChartBand hδ b) p)
  rw [mfderiv_comp p
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((contMDiffAt_outwardChartBand hδ b hp).mdifferentiableAt (by simp))]
  exact (bijective_mfderiv_cylinder hδ C hemb hC hboundary hinv hzero _).surjective.comp
    (surjective_mfderiv_outwardChartBand hδ b hp)

omit [T2Space M] [SecondCountableTopology M] in
/-- The quotient's bounded truncation forces every outside point into an
actual outward chart beyond radius one. Empty boundary needs no special case. -/
theorem outwardChart_covers_outside_truncation
    (x : Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))
    (hx : x ∉ truncation hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) 1) :
    ∃ b y r, y ∈ (chartAt (Model k) b).target ∧ 1 ≤ r ∧ outwardChart hδ C b (r, y) = x := by
  rcases original_endIn_cover hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) x
    with ho | ⟨p, rfl⟩
  · exact (hx (Or.inl ho)).elim
  · have hr : 1 < p.val.1 := by
      by_contra hn
      exact hx (Or.inr ⟨p, le_of_not_gt hn, rfl⟩)
    refine ⟨p.val.2, chartAt (Model k) p.val.2 p.val.2, p.val.1,
      (chartAt (Model k) p.val.2).map_source (mem_chart_source _ _), hr.le, ?_⟩
    unfold outwardChart endIn
    congr 1
    apply Subtype.ext
    have hpRadius : -δ < p.val.1 :=
      lt_of_lt_of_le (neg_lt_zero.mpr hδ) (show 0 ≤ p.val.1 from p.property.1)
    rw [outwardChartBand_val hδ _ (p := (p.val.1, chartAt (Model k) p.val.2 p.val.2)) hpRadius]
    exact Prod.ext rfl ((chartAt (Model k) p.val.2).left_inv (mem_chart_source _ _))

/-- Pulling the actual global primitive through the produced chart gives
the whole standard cylinder one-form, including every radial tangent. -/
theorem primitive_outwardChart
    (α : IntrinsicLiouville.Form k M 1)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) lam =
        cylinderPrimitive δ α)
    (b : IntrinsicBoundary.Point k M) {p : ℝ × Model k}
    (hp : p ∈ Ioi (-δ) ×ˢ (chartAt (Model k) b).target) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    (lam (outwardChart hδ C b p)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) (outwardChart hδ C b) p) =
      PrescribedCylinder.cylinderPrimitive
        ((IntrinsicBoundary.smoothManifold k M).formInChart b (IntrinsicBoundary.restrictForm α)) p := by
  let := completionChartedSpace hδ C hemb hboundary hzero
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let j := cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  let g : ℝ × Model k → Band δ (IntrinsicBoundary.Point k M) := outwardChartBand hδ b
  have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ × Model k)) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, Model (k + 1))) p
    ((contMDiff_cylinder hδ C hemb hC hboundary hinv hzero).mdifferentiableAt (by simp))
    ((contMDiffAt_outwardChartBand hδ b hp).mdifferentiableAt (by simp))
  have hval := outwardChartBand_val hδ b hp.1
  have hproj := mfderiv_boundaryProjection_outwardChartBand hδ b hp
  change (lam (j (g p))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) (j ∘ g) p) = _
  rw [hd]
  ext vs
  have he := congrArg (fun η => η (fun n =>
      mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) g p (vs n)))
    (congrFun hcylinder (g p))
  change lam (j (g p)) (fun n =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) j (g p)
        (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) g p (vs n))) = _ at he ⊢
  rw [he]
  change Real.exp (-(g p).val.1) *
    IntrinsicBoundary.restrictForm α (g p).val.2 (fun n =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection (g p)
        (mfderiv 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) g p (vs n))) = _
  rw [show (g p).val.1 = -p.1 from congrArg Prod.fst hval,
    show (g p).val.2 = (chartAt (Model k) b).symm p.2 from congrArg Prod.snd hval,
    neg_neg]
  apply congrArg (fun z : ℝ => Real.exp p.1 * z)
  change IntrinsicBoundary.restrictForm α ((chartAt (Model k) b).symm p.2) _ =
    IntrinsicBoundary.restrictForm α ((chartAt (Model k) b).symm p.2) _
  apply congrArg (IntrinsicBoundary.restrictForm α ((chartAt (Model k) b).symm p.2))
  funext n
  exact congrArg (fun A => A (vs n)) hproj

/-- Compact continuation applies to the actual quotient and its whole
cylinder law. Its normed-space chart hypotheses are proved above. -/
theorem exists_completeLiouvilleFlow [CompactSpace M]
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hlam : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm lam)
    (hnd : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative lam) x)
    (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) lam =
        cylinderPrimitive δ α) :
    Nonempty (CompleteLiouvilleFlow (completionManifold hδ C hemb hC hboundary hinv hzero)
      ((completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector lam)) := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  apply PrescribedCylinder.exists_completeLiouvilleFlow_of_prescribedCylinder X lam hlam hnd
    (fun _ : IntrinsicBoundary.Point k M => δ) (fun _ => hδ)
    (fun b => (chartAt (Model k) b).target) (fun b => (chartAt (Model k) b).open_target)
    (outwardChart hδ C) (contMDiffOn_outwardChart hδ C hemb hC hboundary hinv hzero)
    (fun b => (IntrinsicBoundary.smoothManifold k M).formInChart b
      (IntrinsicBoundary.restrictForm α))
    (IntrinsicBoundary.isSmoothForm_restrictForm α hα)
    (fun b p hp => primitive_outwardChart hδ C hemb hC hboundary hinv hzero α lam hcylinder b hp)
    (fun b p hp => surjective_mfderiv_outwardChart hδ C hemb hC hboundary hinv hzero b hp)
    (isCompact_truncation hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) 1)
    (outwardChart_covers_outside_truncation hδ C)

/-- Local native collar data construct a single global primitive with its
all-real complete flow on the actual half-infinite quotient. Both compact
pullbacks and the full exponential end law are retained. -/
theorem exists_primitive_completeFlow [CompactSpace M]
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (hnd : ∀ x, IntrinsicLiouville.Nondegenerate (IntrinsicLiouville.exteriorDerivative α) x)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hZ : IntrinsicLiouville.Contraction α (IntrinsicLiouville.exteriorDerivative α) Z)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) (fun x => -Z x) (Ico 0 δ)) :
    let X := completionManifold hδ C hemb hC hboundary hinv hzero
    let N := IntrinsicCollarGluing.extensionManifold hδ C hemb hC hboundary hinv hzero
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    let c := fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val
    letI := completionChartedSpace hδ C hemb hboundary hzero
    ∃ lam : X.Form 1, X.IsSmoothForm lam ∧
      N.pullback X (finiteIn c) lam =
        IntrinsicCollarGluing.gluedPrimitive hδ C hemb hC hboundary hinv hzero α ∧
      (fun x => (lam (original c x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (original c) x)) = α ∧
      P.pullback X (cylinder c) lam = cylinderPrimitive δ α ∧
      (∀ x, X.Nondegenerate (X.exteriorDerivative lam) x) ∧
      Nonempty (CompleteLiouvilleFlow X (X.liouvilleVector lam)) := by
  obtain ⟨lam, hlam, hfinite, hnative, hcylinder, hn⟩ :=
    exists_smooth_symplectic_primitive hδ C hemb hC hboundary hinv hzero α hα hnd Z hZ hode
  exact ⟨lam, hlam, hfinite, hnative, hcylinder, hn,
    exists_completeLiouvilleFlow hδ C hemb hC hboundary hinv hzero α hα lam hlam hn hcylinder⟩

/-- The literal end curve uses the original boundary point at each radius;
outside its signed source it has the same harmless existing-point fallback. -/
def outwardEndMap (p : IntrinsicBoundary.Point k M × ℝ) :
    Space (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) :=
  outwardChart hδ C p.1 (p.2, chartAt (Model k) p.1 p.1)

omit [T2Space M] [SecondCountableTopology M] in
theorem outwardEndMap_eq_cylinder (p : IntrinsicBoundary.Point k M × ℝ) (hp : -δ < p.2) :
    outwardEndMap hδ C p = cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
      (⟨(-p.2, p.1), neg_lt.mp hp, mem_univ _⟩ : Band δ (IntrinsicBoundary.Point k M)) := by
  unfold outwardEndMap outwardChart
  congr 1
  apply Subtype.ext
  rw [outwardChartBand_val hδ _ (p := (p.2, chartAt (Model k) p.1 p.1)) hp]
  exact Prod.ext rfl ((chartAt (Model k) p.1).left_inv (mem_chart_source _ _))

/-- The actual quotient cylinder curves solve the canonical Liouville ODE,
derived from their full primitive law and actual differentials. -/
theorem isMIntegralCurveOn_outwardEndMap
    (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α)
    (lam : (completionManifold hδ C hemb hC hboundary hinv hzero).Form 1)
    (hlam : (completionManifold hδ C hemb hC hboundary hinv hzero).IsSmoothForm lam)
    (hnd : ∀ x, (completionManifold hδ C hemb hC hboundary hinv hzero).Nondegenerate
      ((completionManifold hδ C hemb hC hboundary hinv hzero).exteriorDerivative lam) x)
    (hcylinder : (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (completionManifold hδ C hemb hC hboundary hinv hzero)
      (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)) lam =
        cylinderPrimitive δ α) (b : IntrinsicBoundary.Point k M) :
    letI := completionChartedSpace hδ C hemb hboundary hzero
    IsMIntegralCurveOn (fun r => outwardEndMap hδ C (b, r))
      ((completionManifold hδ C hemb hC hboundary hinv hzero).liouvilleVector lam) (Ioi (-δ)) := by
  let X := completionManifold hδ C hemb hC hboundary hinv hzero
  let := completionChartedSpace hδ C hemb hboundary hzero
  exact PrescribedCylinder.isMIntegralCurveOn_radial X lam hlam (outwardChart hδ C b)
    (chartAt (Model k) b).open_target
    (contMDiffOn_outwardChart hδ C hemb hC hboundary hinv hzero b)
    ((IntrinsicBoundary.smoothManifold k M).formInChart b (IntrinsicBoundary.restrictForm α))
    (IntrinsicBoundary.isSmoothForm_restrictForm α hα b)
    (fun p hp => primitive_outwardChart hδ C hemb hC hboundary hinv hzero α lam hcylinder b hp)
    (fun p hp => surjective_mfderiv_outwardChart hδ C hemb hC hboundary hinv hzero b hp)
    (fun p _ => hnd (outwardChart hδ C b p))
    ((chartAt (Model k) b).map_source (mem_chart_source _ _))

end Native

end FsFltz.Geometry.IntrinsicCompletionGluing
