import FsFltz.Geometry.IntrinsicCollarGluingSmooth
import FsFltz.Geometry.IntrinsicCollarGluingInclusion
import FsFltz.Geometry.IntrinsicCollarCarrier
import FsFltz.Geometry.IntrinsicCylinderTime

/-!
# Regular defining functions from the constructed collar atlas

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The defining function is minus the actual time coordinate,
transported through the cylinder's constructed smooth inverse. Its sublevel
and zero-level identities use the proved original carrier and frontier.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCollarGluing

section Coordinates

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {δ : ℝ} (hδ : 0 < δ) (C : Half δ B → M) (hC : IsOpenEmbedding C)

/-- The actual cylinder inverse, extended to a total map using a chosen
cylinder point only outside the cylinder's open image. -/
def cylinderInverse (p : Band δ B) : Extension C → Band δ B := by
  let : Nonempty (Band δ B) := ⟨p⟩
  exact (((isOpenEmbedding_cylinder hδ C hC).toOpenPartialHomeomorph
    (cylinder C)).symm : Extension C → Band δ B)

@[simp] theorem cylinderInverse_cylinder (p q : Band δ B) :
    cylinderInverse hδ C hC p (cylinder C q) = q := by
  let : Nonempty (Band δ B) := ⟨p⟩
  exact (isOpenEmbedding_cylinder hδ C hC).toOpenPartialHomeomorph_left_inv (cylinder C)

theorem cylinder_cylinderInverse (p : Band δ B) {z : Extension C}
    (hz : z ∈ range (cylinder C)) : cylinder C (cylinderInverse hδ C hC p z) = z := by
  let : Nonempty (Band δ B) := ⟨p⟩
  exact (isOpenEmbedding_cylinder hδ C hC).toOpenPartialHomeomorph_right_inv (cylinder C) hz

/-- Minus the actual inward time is the original carrier's defining coordinate. -/
def cylinderRho (p : Band δ B) : Extension C → ℝ :=
  fun z => -bandTime (cylinderInverse hδ C hC p z)

@[simp] theorem cylinderRho_cylinder (p q : Band δ B) :
    cylinderRho hδ C hC p (cylinder C q) = -q.val.1 := by
  simp [cylinderRho, bandTime]

/-- The defining coordinate has exactly the original carrier as its local sublevel. -/
theorem cylinderRho_nonpos_iff (p : Band δ B) {z : Extension C}
    (hz : z ∈ range (cylinder C)) :
    cylinderRho hδ C hC p z ≤ 0 ↔ z ∈ range (original C) := by
  obtain ⟨q, rfl⟩ := hz
  rw [cylinderRho_cylinder, neg_nonpos]
  exact (Set.ext_iff.mp (preimage_cylinder_range_original C) q).symm

/-- The defining coordinate's zero level is exactly the actual carrier frontier. -/
theorem cylinderRho_zero_iff (p : Band δ B) {z : Extension C}
    (hz : z ∈ range (cylinder C)) :
    cylinderRho hδ C hC p z = 0 ↔ z ∈ frontier (range (original C)) := by
  obtain ⟨q, rfl⟩ := hz
  rw [cylinderRho_cylinder, neg_eq_zero]
  exact (cylinder_mem_frontier_range_original hδ C hC q).symm

end Coordinates

section Native

variable {k : ℕ} {M : Type} [TopologicalSpace M]
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

local instance definingBandChartedSpace :
    ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace δ

local instance definingBandIsManifold :
    IsManifold 𝓘(ℝ, Model (k + 1)) ∞ (Band δ (IntrinsicBoundary.Point k M)) :=
  band_isManifold δ

include hC hinv

/-- The actual cylinder inverse is smooth throughout its open image, derived
from the inverse germs of its charts in the constructed mixed atlas. -/
theorem contMDiffOn_cylinderInverse (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (cylinderInverse hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb p)
      (range (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  intro z hz
  obtain ⟨q, rfl⟩ := hz
  obtain ⟨g, hg, _, heq⟩ := cylinder_inverse_germ hδ C hemb hC hboundary hinv hzero q
  apply (hg.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [heq] with z hz
  exact (congrArg (cylinderInverse hδ _ hemb p) hz).symm.trans
    (cylinderInverse_cylinder hδ _ hemb p (g z))

/-- Minus cylinder time is smooth on a genuine open neighborhood of every
original boundary point, not merely as a pointwise smooth germ. -/
theorem contMDiffOn_cylinderRho (p : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    ContMDiffOn 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞
      (cylinderRho hδ (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val) hemb p)
      (range (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val))) := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  exact (contMDiff_bandTime δ).neg.comp_contMDiffOn
    (contMDiffOn_cylinderInverse hδ C hemb hC hboundary hinv hzero p)

/-- Nonzero time differential and the actual cylinder chain rule prove
regularity of the defining coordinate at every cylinder point. -/
theorem mfderiv_cylinderRho_ne_zero (p q : Band δ (IntrinsicBoundary.Point k M)) :
    letI := extensionChartedSpace hδ C hemb hboundary hzero
    mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ)
      (cylinderRho hδ (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) hemb p)
      (cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q) ≠ 0 := by
  let := extensionChartedSpace hδ C hemb hboundary hzero
  let := extension_isManifold hδ C hemb hC hboundary hinv hzero
  let C₀ := fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val
  let rho := cylinderRho hδ C₀ hemb p
  have hj := contMDiff_cylinder hδ C hemb hC hboundary hinv hzero
  have hr := (contMDiffOn_cylinderRho hδ C hemb hC hboundary hinv hzero p).contMDiffAt
    ((isOpenEmbedding_cylinder hδ C₀ hemb).isOpen_range.mem_nhds (mem_range_self q))
  have heq : rho ∘ cylinder C₀ = -(bandTime : Band δ (IntrinsicBoundary.Point k M) → ℝ) :=
    funext (fun z => cylinderRho_cylinder hδ C₀ hemb p z)
  have hd := mfderiv_comp (f := cylinder C₀) (g := rho) q
    (hr.mdifferentiableAt (by simp)) (hj.mdifferentiableAt (by simp))
  rw [heq, mfderiv_neg] at hd
  intro hz
  rw [hz] at hd
  have hzeroTime : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ)
      (bandTime : Band δ (IntrinsicBoundary.Point k M) → ℝ) q = 0 := by
    simpa using congrArg Neg.neg hd
  exact mfderiv_bandTime_ne_zero q hzeroTime

/-- The boundaryless smooth extension produced by the actual interior/cylinder
atlas. Its topology and points are exactly the constructed collar quotient. -/
def extensionManifold [T2Space M] [SecondCountableTopology M] : SmoothManifold (k + 1) where
  Point := Extension (fun q : Half δ (IntrinsicBoundary.Point k M) => C q.val)
  topology := inferInstance
  charts := extensionChartedSpace hδ C hemb hboundary hzero
  hausdorff := t2Space_extension hδ _ hemb
  secondCountable := secondCountableTopology_extension hδ _ hemb hboundary hzero
  smooth := extension_isManifold hδ C hemb hC hboundary hinv hzero

/-- A genuine regular local defining function on the entire open cylinder
patch of the produced extension. -/
def cylinderBoundaryDefiningFunction [T2Space M] [SecondCountableTopology M]
    (p q : Band δ (IntrinsicBoundary.Point k M)) :
    BoundaryDefiningFunction (extensionManifold hδ C hemb hC hboundary hinv hzero)
      (range (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)))
      (cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) q) where
  neighbourhood := range (cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val))
  open_neighbourhood := (isOpenEmbedding_cylinder hδ _ hemb).isOpen_range
  mem_neighbourhood := mem_range_self q
  rho := cylinderRho hδ _ hemb p
  smooth_rho := contMDiffOn_cylinderRho hδ C hemb hC hboundary hinv hzero p
  sublevel := fun _ hz => (cylinderRho_nonpos_iff hδ _ hemb p hz).symm
  zero_level := fun _ hz => (cylinderRho_zero_iff hδ _ hemb p hz).symm
  regular := mfderiv_cylinderRho_ne_zero hδ C hemb hC hboundary hinv hzero p q

/-- Every point of the actual original carrier's frontier has a regular
defining function produced by the collar, without a supplied presentation. -/
def boundaryDefiningFunction [T2Space M] [SecondCountableTopology M]
    (x : (extensionManifold hδ C hemb hC hboundary hinv hzero).Point)
    (hx : x ∈ frontier
      (range (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val)))) :
    BoundaryDefiningFunction (extensionManifold hδ C hemb hC hboundary hinv hzero)
      (range (original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val))) x := by
  apply Classical.choice
  rw [frontier_range_original hδ _ hemb hboundary hzero] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨?_⟩
  let b : IntrinsicBoundary.Point k M := ⟨m, hm⟩
  let p : Half δ (IntrinsicBoundary.Point k M) := ⟨(0, b), ⟨le_rfl, hδ⟩, mem_univ _⟩
  have hp : original (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) m =
      cylinder (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) (halfToBand hδ p) := by
    simpa [p, hzero b] using original_collar_eq_cylinder hδ
      (fun r : Half δ (IntrinsicBoundary.Point k M) => C r.val) p
  rw [hp]
  exact cylinderBoundaryDefiningFunction hδ C hemb hC hboundary hinv hzero
    (halfToBand hδ p) (halfToBand hδ p)

end Native

end FsFltz.Geometry.IntrinsicCollarGluing
