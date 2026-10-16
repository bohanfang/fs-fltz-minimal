import FsFltz.Geometry.IntrinsicCompletionAtlas
import FsFltz.Geometry.IntrinsicGluingPrimitive
import FsFltz.Geometry.SmoothFormOpenGluing

/-!
# The primitive on the full half-infinite cylinder

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158, and
`sec:lean`, lines 805–814. The native time coordinate is inward, so the
prescribed completion primitive is `exp(-t)` times the actual boundary
restriction. It agrees with the finite cylinder on every tangent.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- The actual open half-infinite cylinder as a smooth manifold. -/
def bandManifold {k : ℕ} (δ : ℝ) (B : SmoothManifold k) : SmoothManifold (k + 1) where
  Point := Band δ B.Point
  topology := inferInstance
  charts := bandChartedSpace δ
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := band_isManifold δ

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M] [T2Space M] [SecondCountableTopology M]

/-- The actual boundary projection on the whole attached cylinder. -/
def boundaryProjection {δ : ℝ} (p : Band δ (IntrinsicBoundary.Point k M)) :
    IntrinsicBoundary.Point k M := p.val.2

omit [T2Space M] [SecondCountableTopology M] in
theorem contMDiff_boundaryProjection (δ : ℝ) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) ∞
      (boundaryProjection : Band δ (IntrinsicBoundary.Point k M) → _) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  exact contMDiff_snd.comp (contMDiff_band_val δ)

/-- The full completion cylinder has its prescribed one-form. -/
def cylinderPrimitive (δ : ℝ) (α : IntrinsicLiouville.Form k M 1) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).Form 1 :=
  fun p => Real.exp (-p.val.1) •
    ((bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (IntrinsicBoundary.smoothManifold k M) boundaryProjection
      (IntrinsicBoundary.restrictForm α) p)

theorem isSmoothForm_cylinderPrimitive (δ : ℝ) (α : IntrinsicLiouville.Form k M 1)
    (hα : IntrinsicLiouville.IsLocallyExtendibleForm α) :
    (bandManifold δ (IntrinsicBoundary.smoothManifold k M)).IsSmoothForm
      (cylinderPrimitive δ α) := by
  let N := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  have hp : N.IsSmoothForm
      (N.pullback (IntrinsicBoundary.smoothManifold k M) boundaryProjection
        (IntrinsicBoundary.restrictForm α)) :=
    N.isSmoothForm_pullback_one (IntrinsicBoundary.smoothManifold k M)
      ⟨boundaryProjection, contMDiff_boundaryProjection δ⟩ (IntrinsicBoundary.restrictForm α)
      (IntrinsicBoundary.isSmoothForm_restrictForm α hα)
  have ht : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : N.Point => p.val.1) := contMDiff_fst.comp (contMDiff_band_val δ)
  exact hp.function_smul (Real.contDiff_exp.contMDiff.comp ht.neg)

/-- The same literal coordinates pull the full cylinder primitive back to
its already constructed finite-window primitive. -/
theorem pullback_cylinderPrimitive_finiteBandIn (δ : ℝ)
    (α : IntrinsicLiouville.Form k M 1) :
    (IntrinsicCollarGluing.bandManifold δ (IntrinsicBoundary.smoothManifold k M)).pullback
      (bandManifold δ (IntrinsicBoundary.smoothManifold k M)) finiteBandIn
      (cylinderPrimitive δ α) = IntrinsicCollarGluing.cylinderPrimitive δ α := by
  let N := IntrinsicCollarGluing.bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
  let := IntrinsicCollarGluing.bandChartedSpace (k := k)
    (B := IntrinsicBoundary.Point k M) δ
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  have hd := mfderiv_comp
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, Model k)) (f := finiteBandIn)
    (g := (boundaryProjection : Band δ (IntrinsicBoundary.Point k M) → _))
  funext q
  have hchain := hd q ((contMDiff_boundaryProjection δ).mdifferentiableAt (by simp))
    ((contMDiff_finiteBandIn δ).mdifferentiableAt (by simp))
  ext vs
  change Real.exp (-q.val.1) *
    IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection (finiteBandIn q)
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) finiteBandIn q (vs n))) = _
  change Real.exp (-q.val.1) *
    IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection (finiteBandIn q)).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) finiteBandIn q)) (vs n)) = _
  rw [← hchain]
  rfl

/-- Nonpositive inward-time translation is defined on the entire actual cylinder. -/
def inwardShift {δ : ℝ} (a : ℝ) (ha : a ≤ 0)
    (p : Band δ (IntrinsicBoundary.Point k M)) : Band δ (IntrinsicBoundary.Point k M) :=
  ⟨(p.val.1 + a, p.val.2), ⟨by
    change p.val.1 + a < δ
    exact lt_of_le_of_lt (add_le_of_nonpos_right ha)
      (show p.val.1 < δ from p.property.1), mem_univ _⟩⟩

omit [T2Space M] [SecondCountableTopology M] in
theorem contMDiff_inwardShift (δ a : ℝ) (ha : a ≤ 0) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (inwardShift a ha : Band δ (IntrinsicBoundary.Point k M) → _) := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  have ht := contMDiff_fst.comp (contMDiff_band_val (k := k)
    (B := IntrinsicBoundary.Point k M) δ)
  have hb := contMDiff_snd.comp (contMDiff_band_val (k := k)
    (B := IntrinsicBoundary.Point k M) δ)
  intro p
  exact contMDiffAt_band_iff_val.mpr ((ht.add (contMDiff_const (c := a))).prodMk hb).contMDiffAt

omit [T2Space M] [SecondCountableTopology M] in
/-- Translation's inverse is smooth on an actual neighborhood of each image,
so its derivative is bijective even though the translation is not onto globally. -/
theorem bijective_mfderiv_inwardShift {δ : ℝ} (a : ℝ) (ha : a ≤ 0)
    (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (inwardShift a ha) p) := by
  classical
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let g : Band δ (IntrinsicBoundary.Point k M) → Band δ (IntrinsicBoundary.Point k M) :=
    fun q => if hq : q.val.1 - a < δ then
      ⟨(q.val.1 - a, q.val.2), hq, mem_univ _⟩ else p
  have hn : ∀ᶠ q : Band δ (IntrinsicBoundary.Point k M) in 𝓝 (inwardShift a ha p),
      q.val.1 - a < δ :=
    ((continuous_fst.comp continuous_subtype_val).sub continuous_const).continuousAt.eventually
      (Iio_mem_nhds (by simpa [inwardShift] using p.property.1))
  have heq : (Subtype.val ∘ g) =ᶠ[𝓝 (inwardShift a ha p)]
      (fun q => (q.val.1 - a, q.val.2)) := by
    filter_upwards [hn] with q hq
    simp only [g, dite_eq_left hq, Function.comp_apply]
  have hg : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ g
      (inwardShift a ha p) := by
    apply contMDiffAt_band_iff_val.mpr
    have ht := contMDiff_fst.comp (contMDiff_band_val (k := k)
      (B := IntrinsicBoundary.Point k M) δ)
    have hb := contMDiff_snd.comp (contMDiff_band_val (k := k)
      (B := IntrinsicBoundary.Point k M) δ)
    exact ((ht.sub (contMDiff_const (c := a))).prodMk hb).contMDiffAt.congr_of_eventuallyEq heq
  have hleft : g ∘ inwardShift a ha = id := by
    funext q
    have hq : (inwardShift a ha q).val.1 - a < δ := by
      simpa [inwardShift] using q.property.1
    simp only [Function.comp_apply, g, dite_eq_left hq]
    apply Subtype.ext
    change (q.val.1 + a - a, q.val.2) = q.val
    simp
  have hd := mfderiv_comp p (hg.mdifferentiableAt (by simp))
    ((contMDiff_inwardShift δ a ha).mdifferentiableAt (by simp))
  rw [hleft, mfderiv_id] at hd
  have hi : Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1))
      (inwardShift a ha) p) := by
    intro v w hvw
    have heval (u : Model (k + 1)) := congrArg (fun A => A u) hd
    exact (heval v).trans ((congrArg
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) g (inwardShift a ha p)) hvw).trans
        (heval w).symm)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- Time translation scales the same actual cylinder one-form by a
nonzero constant; this law holds on every tangent of the full cylinder. -/
theorem pullback_cylinderPrimitive_inwardShift (δ a : ℝ) (ha : a ≤ 0)
    (α : IntrinsicLiouville.Form k M 1) :
    let P := bandManifold δ (IntrinsicBoundary.smoothManifold k M)
    P.pullback P (inwardShift a ha) (cylinderPrimitive δ α) =
      fun p => Real.exp (-a) • cylinderPrimitive δ α p := by
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  have hd := mfderiv_comp
    (I := 𝓘(ℝ, Model (k + 1))) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, Model k)) (f := inwardShift a ha)
    (g := (boundaryProjection : Band δ (IntrinsicBoundary.Point k M) → _))
  funext q
  have hchain := hd q ((contMDiff_boundaryProjection δ).mdifferentiableAt (by simp))
    ((contMDiff_inwardShift δ a ha).mdifferentiableAt (by simp))
  ext vs
  change Real.exp (-(q.val.1 + a)) *
    IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
      ((mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection (inwardShift a ha q)).comp
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) (inwardShift a ha) q)) (vs n)) = _
  rw [← hchain]
  change Real.exp (-(q.val.1 + a)) *
    IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection q (vs n)) = _
  rw [neg_add, Real.exp_add]
  change (Real.exp (-q.val.1) * Real.exp (-a)) *
    IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
      mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection q (vs n)) =
    Real.exp (-a) * (Real.exp (-q.val.1) *
      IntrinsicBoundary.restrictForm α q.val.2 (fun n =>
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model k) boundaryProjection q (vs n)))
  ring

end FsFltz.Geometry.IntrinsicCompletionGluing
