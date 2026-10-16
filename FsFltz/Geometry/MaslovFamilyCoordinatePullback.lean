import FsFltz.Geometry.Maslov
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Coordinate regularity of a given Maslov family under real smooth map germs

Source: `geoemtric-part-fsf.tex`, smoothness convention, lines 119–122;
`def:maslov`, lines 212–232; `g:chain`, lines 407–413; and `sec:lean`,
lines 794–814. The compatible structure and full squared canonical tensor
come from an independently given `MaslovFamily`. A time-preserving coordinate
map with invertible spatial derivative at its center pulls their actual raw
chart coefficients back to smooth coefficients on a smaller real-open set.
The conclusion imposes no complex-structure equation outside the interval.
This is a foundational regularity lemma, not a construction of the target chain.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of the spatial slice of a real parameter coordinate map. -/
def coordinateSpatialDerivative (φ : ℝ × F → Model (2 * n)) (z : ℝ × F) :
    F →L[ℝ] Model (2 * n) :=
  fderiv ℝ (fun y => φ (z.1, y)) z.2

/-- The spatial derivative is the vertical restriction of the joint derivative. -/
theorem coordinateSpatialDerivative_eq_comp_inr
    (φ : ℝ × F → Model (2 * n)) {z : ℝ × F}
    (hφ : DifferentiableAt ℝ φ z) :
    coordinateSpatialDerivative φ z =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ ℝ F) := by
  exact (hφ.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv

/-- Joint smoothness on a real-open set gives smooth spatial derivatives. -/
theorem contDiffOn_coordinateSpatialDerivative
    (φ : ℝ × F → Model (2 * n)) {U : Set (ℝ × F)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U) :
    ContDiffOn ℝ ∞ (coordinateSpatialDerivative φ) U := by
  apply ((hφ.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ F))).congr
  intro z hz
  exact coordinateSpatialDerivative_eq_comp_inr φ
    ((hφ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

/-- Pull the actual raw chart endomorphism back through the spatial derivative. -/
def coordinatePullbackAlmostComplex (N : SmoothManifold (2 * n)) (a : N.Point)
    (J : ℝ → AlmostComplexField N) (φ : ℝ × F → Model (2 * n)) (z : ℝ × F) :
    F →L[ℝ] F :=
  (coordinateSpatialDerivative φ z).inverse.comp
    ((almostComplexInChart N a (J z.1) (φ z)).comp (coordinateSpatialDerivative φ z))

/-- Pull every slot of the actual full squared tensor back by the same derivative. -/
def coordinatePullbackSquaredTensor (N : SmoothManifold (2 * n)) (a : N.Point)
    (T : ℝ → N.Point → SquaredCanonicalTensor n)
    (φ : ℝ × F → Model (2 * n)) (z : ℝ × F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ⊕ Fin n => F) ℂ :=
  (squaredTensorInChart N a (T z.1) (φ z)).compContinuousLinearMap
    (fun _ => coordinateSpatialDerivative φ z)

/-- Local smooth coefficient fields pull back through a time-preserving map
on a smaller real-open neighborhood. This analytic statement requires no
complex law and no data on the rest of the parameter interval. -/
theorem exists_coordinateCoefficientPullback_regularNeighborhood [CompleteSpace F]
    (A : ℝ × Model (2 * n) → Model (2 * n) →L[ℝ] Model (2 * n))
    (T : ℝ × Model (2 * n) → SquaredCanonicalTensor n)
    (φ : ℝ × F → Model (2 * n))
    {U : Set (ℝ × F)} {W : Set (ℝ × Model (2 * n))}
    (hU : IsOpen U) (hW : IsOpen W) (hφ : ContDiffOn ℝ ∞ φ U)
    (hA : ContDiffOn ℝ ∞ A W) (hT : ContDiffOn ℝ ∞ T W)
    (p : ℝ × F) (hpU : p ∈ U) (hpW : (p.1, φ p) ∈ W)
    (hpInv : (coordinateSpatialDerivative φ p).IsInvertible) :
    ∃ V : Set (ℝ × F), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V, (z.1, φ z) ∈ W ∧ (coordinateSpatialDerivative φ z).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun z => (coordinateSpatialDerivative φ z).inverse.comp
        ((A (z.1, φ z)).comp (coordinateSpatialDerivative φ z))) V ∧
      ContDiffOn ℝ ∞ (fun z => (T (z.1, φ z)).compContinuousLinearMap
        (fun _ => coordinateSpatialDerivative φ z)) V := by
  have hD := contDiffOn_coordinateSpatialDerivative φ hU hφ
  let C := U ∩ (coordinateSpatialDerivative φ) ⁻¹' {L | L.IsInvertible}
  have hC : IsOpen C := hD.continuousOn.isOpen_inter_preimage
    hU ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let q : ℝ × F → ℝ × Model (2 * n) := fun z => (z.1, φ z)
  have hq : ContDiffOn ℝ ∞ q U := contDiffOn_fst.prodMk hφ
  let V := C ∩ q ⁻¹' W
  have hV : IsOpen V := (hq.mono inter_subset_left).continuousOn.isOpen_inter_preimage
    hC hW
  have hVU : V ⊆ U := fun _ hz => hz.1.1
  have hDV : ContDiffOn ℝ ∞ (coordinateSpatialDerivative φ) V := hD.mono hVU
  have hDi : ContDiffOn ℝ ∞ (fun z => (coordinateSpatialDerivative φ z).inverse) V := by
    intro z hz
    exact hz.1.2.contDiffAt_map_inverse.comp_contDiffWithinAt z (hDV z hz)
  have hAV : ContDiffOn ℝ ∞ (fun z => A (z.1, φ z)) V :=
    hA.comp (hq.mono hVU) (fun _ hz => hz.2)
  have hTV : ContDiffOn ℝ ∞ (fun z => T (z.1, φ z)) V :=
    hT.comp (hq.mono hVU) (fun _ hz => hz.2)
  refine ⟨V, hV, ⟨⟨hpU, hpInv⟩, hpW⟩, hVU,
    (fun _ hz => ⟨hz.2, hz.1.2⟩), hDi.clm_comp (hAV.clm_comp hDV), ?_⟩
  exact (((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin n ⊕ Fin n => F) (fun _ => Model (2 * n)) ℂ).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr (fun _ => hDV))).clm_apply hTV)

namespace MaslovFamily

/-- A given Maslov family's chart coefficients remain smooth after a real
coordinate pullback near an interval point. Invertibility is required only at
the center and is recovered throughout the smaller neighborhood. -/
theorem exists_coordinatePullback_regularNeighborhood [CompleteSpace F]
    {N : SmoothManifold (2 * n)} {eta : ℝ → N.Form 2}
    (h : MaslovFamily N eta) (a : N.Point) (φ : ℝ × F → Model (2 * n))
    {U : Set (ℝ × F)} (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    (p : Parameter × F) (hpU : (p.1.val, p.2) ∈ U)
    (hpTarget : φ (p.1.val, p.2) ∈ (chartAt (Model (2 * n)) a).target)
    (hpInv : (coordinateSpatialDerivative φ (p.1.val, p.2)).IsInvertible) :
    ∃ V : Set (ℝ × F), IsOpen V ∧ (p.1.val, p.2) ∈ V ∧ V ⊆ U ∧
      (∀ z ∈ V, φ z ∈ (chartAt (Model (2 * n)) a).target ∧
        (coordinateSpatialDerivative φ z).IsInvertible) ∧
      ContDiffOn ℝ ∞ (coordinatePullbackAlmostComplex N a h.J φ) V ∧
      ContDiffOn ℝ ∞ (coordinatePullbackSquaredTensor N a h.tensor φ) V := by
  obtain ⟨WJ, hWJ, hWJcover, hJ⟩ := h.smoothJ a
  obtain ⟨WT, hWT, hWTcover, hT⟩ := h.smoothSection a
  let B := U ∩ φ ⁻¹' (chartAt (Model (2 * n)) a).target
  have hB : IsOpen B := hφ.continuousOn.isOpen_inter_preimage hU
    (chartAt (Model (2 * n)) a).open_target
  obtain ⟨V, hV, hpV, hVB, hmap, hK, hTensor⟩ :=
    exists_coordinateCoefficientPullback_regularNeighborhood
      (fun z => almostComplexInChart N a (h.J z.1) z.2)
      (fun z => squaredTensorInChart N a (h.tensor z.1) z.2) φ
      hB (hWJ.inter hWT) (hφ.mono inter_subset_left)
      (hJ.mono inter_subset_left) (hT.mono inter_subset_right) (p.1.val, p.2)
      ⟨hpU, hpTarget⟩
      ⟨hWJcover ⟨p.1.property, hpTarget⟩, hWTcover ⟨p.1.property, hpTarget⟩⟩ hpInv
  exact ⟨V, hV, hpV, (fun _ hz => (hVB hz).1),
    (fun z hz => ⟨(hVB hz).2, (hmap z hz).2⟩), hK, hTensor⟩

end MaslovFamily

end FsFltz.Geometry
