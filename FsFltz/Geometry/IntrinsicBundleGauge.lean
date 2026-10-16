import FsFltz.Geometry.IntrinsicSmoothBundle
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth changes of bundle coordinates near a seam

Source: `geoemtric-part-fsf.tex`, `def:chain`, 163–169, and `sec:lean`,
788–814. A smooth parameter retraction staying in a chart overlap turns
the actual transition into a smooth change of fibre coordinates. Choosing
the retraction to be the identity near a seam makes the corrected charts
agree there. These are local ingredients for a smooth trivialization;
no global bundle trivialization or completed-family correspondence is
asserted in this module.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A smooth real reparametrization stays in a prescribed interval, is
the identity near an interior point, and is constant outside a bounded
neighborhood. It is built from an ordinary smooth bump function. -/
theorem exists_smooth_reparam_Ioo {u c v : ℝ} (huc : u < c) (hcv : c < v) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ (∀ s, σ s ∈ Ioo u v) ∧
      σ =ᶠ[𝓝 c] id ∧ ∃ r > 0, ∀ s, r ≤ |s - c| → σ s = c := by
  let r := min (c - u) (v - c) / 2
  have hr : 0 < r := half_pos (lt_min (sub_pos.mpr huc) (sub_pos.mpr hcv))
  have hru : r < c - u := by
    have hm := min_le_left (c - u) (v - c)
    dsimp [r] at *
    linarith
  have hrv : r < v - c := by
    have hm := min_le_right (c - u) (v - c)
    dsimp [r] at *
    linarith
  let b : ContDiffBump c := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let σ : ℝ → ℝ := fun s => c + (s - c) * b s
  have hσ : ContDiff ℝ ∞ σ :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul b.contDiff)
  have hconstant (s : ℝ) (hs : r ≤ |s - c|) : σ s = c := by
    have hb : b s = 0 := b.zero_of_le_dist (by simpa only [Real.dist_eq] using hs)
    simp [σ, hb]
  refine ⟨σ, hσ, ?_, ?_, r, hr, hconstant⟩
  · intro s
    have hbound : |σ s - c| < r := by
      by_cases hs : |s - c| < r
      · have hnonneg := b.nonneg (x := s)
        have hle := b.le_one (x := s)
        have habs : |(s - c) * b s| ≤ |s - c| := by
          rw [abs_mul, abs_of_nonneg hnonneg]
          nlinarith [abs_nonneg (s - c)]
        simpa only [σ, add_sub_cancel_left] using habs.trans_lt hs
      · rw [hconstant s (le_of_not_gt hs), sub_self, abs_zero]
        exact hr
    obtain ⟨hleft, hright⟩ := abs_lt.mp hbound
    constructor <;> linarith
  · filter_upwards [b.eventuallyEq_one] with s hs
    change b s = 1 at hs
    change c + (s - c) * b s = s
    rw [hs]
    ring

/-- Every interior point of an open subset of the interval admits a
smooth real reparametrization into that subset, equal to the identity
near the point. Thus the cutoff needed for a chart overlap is constructed,
rather than supplied as geometric input. -/
theorem exists_smooth_reparam_in_open {S : Set Parameter} (hS : IsOpen S)
    (c : Parameter) (hc : c ∈ S) (hc0 : 0 < c.val) (hc1 : c.val < 1) :
    ∃ σ : ℝ → Parameter, ContDiff ℝ ∞ (fun s => (σ s).val) ∧
      (∀ s, σ s ∈ S) ∧ (fun s => (σ s).val) =ᶠ[𝓝 c.val] id ∧
      ∃ r > 0, ∀ s, r ≤ |s - c.val| → σ s = c := by
  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp hS
  have hcO : c.val ∈ O := by
    change c ∈ Subtype.val ⁻¹' O
    rwa [hOS]
  obtain ⟨u, v, hcv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hO.inter isOpen_Ioo).mem_nhds ⟨hcO, hc0, hc1⟩)
  obtain ⟨f, hf, hfmem, hfid, r, hr, hfconst⟩ :=
    exists_smooth_reparam_Ioo hcv.1 hcv.2
  let σ : ℝ → Parameter := fun s =>
    ⟨f s, (hsub (hfmem s)).2.1.le, (hsub (hfmem s)).2.2.le⟩
  refine ⟨σ, hf, ?_, hfid, r, hr, ?_⟩
  · intro s
    rw [← hOS]
    exact (hsub (hfmem s)).1
  · intro s hs
    exact Subtype.ext (hfconst s hs)

variable {d : ℕ} {H F : Type*} [TopologicalSpace H] [TopologicalSpace F]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H F]
  {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace F E)] [SmoothCompactBundle I (F := F) E]

/-- The actual reparametrized transition defines a smooth diffeomorphism
of the product, preserving time. Its inverse is the reversed transition
at the same parameter, so invertibility is proved on the native fibres. -/
def reparametrizedTransitionDiffeomorph
    (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) :
    Diffeomorph ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod I) (ℝ × F) (ℝ × F) ∞ where
  toFun p := (p.1, e.coordChange e' (σ p.1) p.2)
  invFun p := (p.1, e'.coordChange e (σ p.1) p.2)
  left_inv p := by
    dsimp
    rw [e.coordChange_coordChange e' e (hoverlap p.1).1 (hoverlap p.1).2,
      e.coordChange_same_apply (hoverlap p.1).1]
  right_inv p := by
    dsimp
    rw [e'.coordChange_coordChange e e' (hoverlap p.1).2 (hoverlap p.1).1,
      e'.coordChange_same_apply (hoverlap p.1).2]
  contMDiff_toFun := contMDiff_fst.prodMk
    ((SmoothCompactBundle.smoothTransition e he e' he').contMDiff_reparam σ hσ hoverlap)
  contMDiff_invFun := contMDiff_fst.prodMk
    ((SmoothCompactBundle.smoothTransition e' he' e he).contMDiff_reparam σ hσ
      (fun s => ⟨(hoverlap s).2, (hoverlap s).1⟩))

/-- On interval parameters, the smooth product diffeomorphism is an
actual product homeomorphism preserving the first coordinate. -/
def reparametrizedTransitionHomeomorph
    (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) :
    Parameter × F ≃ₜ Parameter × F where
  toFun p := (p.1, e.coordChange e' (σ p.1.val) p.2)
  invFun p := (p.1, e'.coordChange e (σ p.1.val) p.2)
  left_inv p := by
    dsimp
    rw [e.coordChange_coordChange e' e (hoverlap p.1.val).1 (hoverlap p.1.val).2,
      e.coordChange_same_apply (hoverlap p.1.val).1]
  right_inv p := by
    dsimp
    rw [e'.coordChange_coordChange e e' (hoverlap p.1.val).2 (hoverlap p.1.val).1,
      e'.coordChange_same_apply (hoverlap p.1.val).2]
  continuous_toFun := continuous_fst.prodMk
    (((SmoothCompactBundle.smoothTransition e he e' he').contMDiff_reparam σ hσ hoverlap).continuous.comp
      (continuous_subtype_val.prodMap continuous_id))
  continuous_invFun := continuous_fst.prodMk
    (((SmoothCompactBundle.smoothTransition e' he' e he).contMDiff_reparam σ hσ
      (fun s => ⟨(hoverlap s).2, (hoverlap s).1⟩)).continuous.comp
        (continuous_subtype_val.prodMap continuous_id))

/-- Correct one actual bundle chart by the reparametrized transition to
another. The base open set is unchanged. -/
def gaugeTrivialization (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) :
    Trivialization F (π F E) where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.transHomeomorph
    (reparametrizedTransitionHomeomorph e e' he he' σ hσ hoverlap)
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by
    ext p
    change (reparametrizedTransitionHomeomorph e e' he he' σ hσ hoverlap).symm p ∈
      e.target ↔ p ∈ e.baseSet ×ˢ univ
    rw [e.mem_target]
    simp only [mem_prod, mem_univ, and_true]
    rfl
  proj_toFun := e.proj_toFun

@[simp]
theorem gaugeTrivialization_apply (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet) (p : TotalSpace F E) :
    gaugeTrivialization e e' he he' σ hσ hoverlap p =
      ((e p).1, e.coordChange e' (σ (e p).1.val) (e p).2) := rfl

/-- Wherever the reparametrization is the identity, the corrected chart
equals the other chart literally, on its whole fibre. -/
theorem gaugeTrivialization_eq_of_reparam_eq (e e' : Trivialization F (π F E))
    (he : e ∈ trivializationAtlas F E) (he' : e' ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ e.baseSet ∩ e'.baseSet)
    (p : TotalSpace F E) (hp : p.proj ∈ e.baseSet)
    (hσp : σ p.proj.val = p.proj) :
    gaugeTrivialization e e' he he' σ hσ hoverlap p = e' p := by
  have hp' : p.proj ∈ e'.baseSet := by
    rw [← hσp]
    exact (hoverlap p.proj.val).2
  rw [gaugeTrivialization_apply, e.coe_fst' hp, hσp,
    e.coordChange_apply_snd e' hp]
  exact Prod.ext (e'.coe_fst' hp').symm rfl

/-- Splice two actual bundle charts at an interior seam, using a smooth
base-dependent correction of the right chart. Unlike a constant seam
correction, this construction can agree with the left chart on an open
neighborhood of the seam. The open-neighborhood assertion is proved below. -/
def gaugeSpliceTrivialization (eL eR : Trivialization F (π F E))
    (heL : eL ∈ trivializationAtlas F E) (heR : eR ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hσc : σ c.val = c) : Trivialization F (π F E) :=
  eL.piecewiseLeOfEq (gaugeTrivialization eR eL heR heL σ hσ hoverlap) c hcL hcR
    (fun p hp => (gaugeTrivialization_eq_of_reparam_eq eR eL heR heL σ hσ
      hoverlap p (hp ▸ hcR) (by simpa only [hp] using hσc)).symm)

theorem gaugeSpliceTrivialization_apply (eL eR : Trivialization F (π F E))
    (heL : eL ∈ trivializationAtlas F E) (heR : eR ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hσc : σ c.val = c) (p : TotalSpace F E) :
    gaugeSpliceTrivialization eL eR heL heR σ hσ hoverlap c hcL hcR hσc p =
      if p.proj ≤ c then eL p else gaugeTrivialization eR eL heR heL σ hσ hoverlap p := by
  classical
  rfl

/-- Near the seam the entire spliced chart, on every fibre, is literally
the left chart. This removes the seam from the remaining smoothness proof. -/
theorem gaugeSpliceTrivialization_eventually_eq (eL eR : Trivialization F (π F E))
    (heL : eL ∈ trivializationAtlas F E) (heR : eR ∈ trivializationAtlas F E)
    (σ : ℝ → Parameter) (hσ : ContDiff ℝ ∞ (fun s => (σ s).val))
    (hoverlap : ∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hσc : σ c.val = c) (hσnear : (fun s => (σ s).val) =ᶠ[𝓝 c.val] id) :
    ∀ᶠ t in 𝓝 c, ∀ p : TotalSpace F E, p.proj = t →
      gaugeSpliceTrivialization eL eR heL heR σ hσ hoverlap c hcL hcR hσc p = eL p := by
  have hnear : ∀ᶠ t : Parameter in 𝓝 c, σ t.val = t := by
    filter_upwards [hσnear.comp_tendsto continuous_subtype_val.continuousAt] with t ht
    exact Subtype.ext ht
  filter_upwards [hnear, eR.open_baseSet.mem_nhds hcR] with t ht htR
  intro p hp
  rw [gaugeSpliceTrivialization_apply]
  split_ifs
  · rfl
  · exact gaugeTrivialization_eq_of_reparam_eq eR eL heR heL σ hσ hoverlap p
      (hp ▸ htR) (by simpa only [hp] using ht)

/-- Two atlas charts meeting at an interior parameter give an actual
spliced chart with an explicitly smooth transition correction and literal
agreement with the left chart near the seam. The smooth reparametrization
is constructed from the overlap. This statement does not yet assert that
the spliced chart belongs to the original designated atlas. -/
theorem exists_gaugeSpliceTrivialization (eL eR : Trivialization F (π F E))
    (heL : eL ∈ trivializationAtlas F E) (heR : eR ∈ trivializationAtlas F E)
    (c : Parameter) (hcL : c ∈ eL.baseSet) (hcR : c ∈ eR.baseSet)
    (hc0 : 0 < c.val) (hc1 : c.val < 1) :
    ∃ σ : ℝ → Parameter, ContDiff ℝ ∞ (fun s => (σ s).val) ∧
      (∀ s, σ s ∈ eR.baseSet ∩ eL.baseSet) ∧
      ∃ T : Trivialization F (π F E),
        T.baseSet = (Iic c).ite eL.baseSet eR.baseSet ∧
        (∀ p : TotalSpace F E, T p = if p.proj ≤ c then eL p else
          ((eR p).1, eR.coordChange eL (σ (eR p).1.val) (eR p).2)) ∧
        ∀ᶠ t in 𝓝 c, ∀ p : TotalSpace F E, p.proj = t → T p = eL p := by
  obtain ⟨σ, hσ, hoverlap, hnear, _⟩ := exists_smooth_reparam_in_open
    (eR.open_baseSet.inter eL.open_baseSet) c ⟨hcR, hcL⟩ hc0 hc1
  have hσc : σ c.val = c := Subtype.ext hnear.eq_of_nhds
  refine ⟨σ, hσ, hoverlap,
    gaugeSpliceTrivialization eL eR heL heR σ hσ hoverlap c hcL hcR hσc,
    rfl, ?_, ?_⟩
  · intro p
    rw [gaugeSpliceTrivialization_apply, gaugeTrivialization_apply]
  · exact gaugeSpliceTrivialization_eventually_eq
      eL eR heL heR σ hσ hoverlap c hcL hcR hσc hnear

end FsFltz.Geometry.IntrinsicSmoothBundle
