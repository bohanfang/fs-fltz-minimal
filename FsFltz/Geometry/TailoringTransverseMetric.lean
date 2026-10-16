import FsFltz.Geometry.TailoringNativeGradientLinearization
import FsFltz.Geometry.TailoringNormalCoordinates
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The actual metric induced on transverse defining coordinates

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1718–1724.
The surjective differential of the actual transverse map has a unique
metric-normal right inverse. Its induced metric transports the positive
normal derivative of the actual native Liouville field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

section MetricNormal

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Forget continuity in a continuous bilinear form, preserving its values. -/
def metricBilinForm (G : V →L[ℝ] V →L[ℝ] ℝ) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w => G v w)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

@[simp] theorem metricBilinForm_apply (G : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    metricBilinForm G v w = G v w := rfl

/-- A surjective differential has a right inverse in the actual metric
normal to its kernel. Positivity constructs the complement. -/
theorem exists_metricNormal_rightInverse
    [FiniteDimensional ℝ V]
    (D : V →L[ℝ] F) (G : V →L[ℝ] V →L[ℝ] ℝ)
    (hD : Surjective D) (hsym : ∀ v w, G v w = G w v)
    (hpos : ∀ v, v ≠ 0 → 0 < G v v) :
    ∃ L : F →L[ℝ] V,
      D.comp L = ContinuousLinearMap.id ℝ F ∧
      ∀ z w, D w = 0 → G (L z) w = 0 := by
  let g := metricBilinForm G
  let W := g.orthogonal D.ker
  have hg : g.IsSymm := ⟨hsym⟩
  have hdj : Disjoint D.ker W := by
    apply Submodule.disjoint_def.mpr
    intro v hv hvW
    have hz : G v v = 0 := hvW v hv
    by_contra hne
    exact (hpos v hne).ne' hz
  have hc : IsCompl D.ker W :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hg.isRefl).mpr hdj
  let d := D.comp W.subtypeL
  have hbij : Bijective d := by
    constructor
    · intro v w he
      have hzero : D ((v : V) - (w : V)) = 0 := by
        change D (v : V) = D (w : V) at he
        rw [map_sub, he, sub_self]
      have hz := Submodule.disjoint_def.mp hdj _ hzero (W.sub_mem v.property w.property)
      exact Subtype.ext (sub_eq_zero.mp hz)
    · intro z
      obtain ⟨v, hv⟩ := hD z
      have hv' : v ∈ D.ker ⊔ W := hc.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨k, hk, w, hw, he⟩ := Submodule.mem_sup.mp hv'
      refine ⟨⟨w, hw⟩, ?_⟩
      change D w = z
      rw [← hv, ← he, map_add, show D k = 0 from hk, zero_add]
  let e := (LinearEquiv.ofBijective d.toLinearMap hbij).toContinuousLinearEquiv
  let L := W.subtypeL.comp e.symm.toContinuousLinearMap
  refine ⟨L, ?_, ?_⟩
  · ext z
    exact e.apply_symm_apply z
  · intro z w hw
    rw [hsym]
    exact (e.symm z).property w hw

/-- Pairing with a normal lift ignores precisely the kernel component
removed by the right inverse. -/
theorem metricNormal_lift_pairing
    (D : V →L[ℝ] F) (G : V →L[ℝ] V →L[ℝ] ℝ) (L : F →L[ℝ] V)
    (hL : D.comp L = ContinuousLinearMap.id ℝ F)
    (horth : ∀ z w, D w = 0 → G (L z) w = 0)
    (hsym : ∀ v w, G v w = G w v) (z : F) (v : V) :
    G (L (D v)) (L z) = G v (L z) := by
  have hright (u : F) : D (L u) = u := congrArg (fun A : F →L[ℝ] F => A u) hL
  have hk : D (L (D v) - v) = 0 := by rw [map_sub, hright, sub_self]
  have h := horth z (L (D v) - v) hk
  rw [← hsym (L (D v) - v) (L z), map_sub, sub_apply] at h
  exact sub_eq_zero.mp h

/-- The metric-normal lift is unique, so the construction introduces no
independent complement choices when the differential and metric are fixed. -/
theorem eq_of_metricNormal_lifts
    (D : V →L[ℝ] F) (G : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < G v v) (v w : V)
    (hv : ∀ u, D u = 0 → G v u = 0)
    (hw : ∀ u, D u = 0 → G w u = 0) (he : D v = D w) : v = w := by
  have hk : D (v - w) = 0 := by rw [map_sub, he, sub_self]
  have hz : G (v - w) (v - w) = 0 := by
    rw [G.map_sub, sub_apply, hv _ hk, hw _ hk, sub_self]
  by_contra hne
  exact (hpos _ (sub_ne_zero.mpr hne)).ne' hz

end MetricNormal

section FixedCoverMetric

variable {n : ℕ} {s : Finset (Lattice n)}

/-- The literal real-angular tangent plane of the critical face fiber. -/
def faceFiberPlane (q : s → ℝ) : Submodule ℝ (TangentCoordinates n) :=
  (faceRealTangent q).prod (faceRealTangent q)

@[simp] theorem mem_faceFiberPlane (q : s → ℝ) (W : TangentCoordinates n) :
    W ∈ faceFiberPlane q ↔ W.1 ∈ faceRealTangent q ∧ W.2 ∈ faceRealTangent q := Iff.rfl

/-- The actual Hessian metric as a continuous bilinear form in cover coordinates. -/
def faceHessianMetricCLM (H : RealSpace n →L[ℝ] RealSpace n) :
    TangentCoordinates n →L[ℝ] TangentCoordinates n →L[ℝ] ℝ :=
  (∑ i : Fin n,
    ((ContinuousLinearMap.proj i).comp (H.comp (ContinuousLinearMap.fst ℝ _ _))).smulRight
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))) +
  ∑ i : Fin n,
    ((ContinuousLinearMap.proj i).comp (H.comp (ContinuousLinearMap.snd ℝ _ _))).smulRight
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem faceHessianMetricCLM_apply
    (H : RealSpace n →L[ℝ] RealSpace n) (V W : TangentCoordinates n) :
    faceHessianMetricCLM H V W = faceHessianMetric H V W := by
  simp [faceHessianMetricCLM, faceHessianMetric, smul_eq_mul]

theorem faceHessianMetricCLM_symm (H : RealSpace n →L[ℝ] RealSpace n)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (V W : TangentCoordinates n) :
    faceHessianMetricCLM H V W = faceHessianMetricCLM H W V := by
  simp only [faceHessianMetricCLM_apply, faceHessianMetric, hHsym]

theorem faceHessianMetricCLM_pos (H : RealSpace n →L[ℝ] RealSpace n)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (V : TangentCoordinates n) (hV : V ≠ 0) : 0 < faceHessianMetricCLM H V V := by
  have hnonneg (e : RealSpace n) : 0 ≤ ∑ i, H e i * e i := by
    by_cases he : e = 0
    · simp [he]
    · exact (hH e he).le
  rw [faceHessianMetricCLM_apply, faceHessianMetric]
  by_cases hr : V.1 = 0
  · have ha : V.2 ≠ 0 := fun ha => hV (Prod.ext hr ha)
    exact add_pos_of_nonneg_of_pos (hnonneg _) (hH _ ha)
  · exact add_pos_of_pos_of_nonneg (hH _ hr) (hnonneg _)

def faceFiberMetric (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) :
    faceFiberPlane q →L[ℝ] faceFiberPlane q →L[ℝ] ℝ :=
  (faceHessianMetricCLM H).bilinearComp (faceFiberPlane q).subtypeL (faceFiberPlane q).subtypeL

@[simp] theorem faceFiberMetric_apply
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (V W : faceFiberPlane q) :
    faceFiberMetric H q V W = faceHessianMetric H V W := by
  simp [faceFiberMetric]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transverse differential on the fixed cover fiber plane. It does
not depend on the torus angle or the native chart. -/
def faceFiberTransverseDifferential (Q : RealSpace n →L[ℝ] E)
    (H : RealSpace n →L[ℝ] RealSpace n) (v₀ : s) (q r : s → ℝ) :
    faceFiberPlane q →L[ℝ] E × (s.erase v₀.val → ℝ) :=
  (conormalTransverseLinearMap Q H s v₀.val r).comp (faceFiberPlane q).subtypeL

theorem exists_fixed_faceTransverse_normalLift
    (Q : RealSpace n →L[ℝ] E) (hQsurj : Surjective Q)
    (H : RealSpace n →L[ℝ] RealSpace n) (hHsurj : Surjective H)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (v₀ : s) (q r : s → ℝ) (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (hA : Surjective (faceLevelMap s))
    (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ))
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R) :
    ∃ L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q,
      (faceFiberTransverseDifferential Q H v₀ q r).comp L =
        ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)) ∧
      ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
        faceFiberMetric H q (L z) W = 0 := by
  apply exists_metricNormal_rightInverse
  · intro z
    obtain ⟨W, hW₁, hW₂, hW⟩ := conormalTransverseLinearMap_surjective_on_fiber
      Q hQsurj H hHsurj s v₀ q r hq hr hQ hA B R hB hnormal z
    exact ⟨⟨W, hW₁, hW₂⟩, hW⟩
  · intro V W
    exact faceHessianMetricCLM_symm H hHsym V W
  · intro V hV
    apply faceHessianMetricCLM_pos H hH V
    exact fun h => hV (Subtype.ext h)

end FixedCoverMetric

namespace NativeFaceHessianChart

variable {n d : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}

/-- The true native tangent and the fixed cover fiber plane are
continuously linearly equivalent by the actual lift differential. -/
def coverFiberEquiv (C : NativeFaceHessianChart φ s H q lam N j a x) :
    Model d ≃L[ℝ] faceFiberPlane q := by
  let D := fderiv ℝ C.lift (chartAt (Model d) a a)
  let e := D.codRestrict (faceFiberPlane q) (fun v => (C.tangent_range _).mp ⟨v, rfl⟩)
  apply LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective e.toLinearMap ?_)
  constructor
  · intro v w he
    exact C.immersion (congrArg Subtype.val he)
  · intro W
    obtain ⟨v, hv⟩ := (C.tangent_range W).mpr W.property
    exact ⟨v, Subtype.ext hv⟩

@[simp] theorem coverFiberEquiv_coe_apply
    (C : NativeFaceHessianChart φ s H q lam N j a x) (v : Model d) :
    (C.coverFiberEquiv v : TangentCoordinates n) =
      fderiv ℝ C.lift (chartAt (Model d) a a) v := rfl

theorem coordinateMetric_eq_faceFiberMetric
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1) (v w : Model d) :
    C.coordinateMetric (chartAt (Model d) a a) v w =
      faceFiberMetric H q (C.coverFiberEquiv v) (C.coverFiberEquiv w) := by
  rw [coordinateMetric_apply, C.center, faceFiberMetric_apply,
    coverFiberEquiv_coe_apply, coverFiberEquiv_coe_apply]
  exact congrArg (fun K => faceHessianMetric K
    (fderiv ℝ C.lift (chartAt (Model d) a a) v)
    (fderiv ℝ C.lift (chartAt (Model d) a a) w)) hHφ.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transport the one fixed cover normal lift into a native chart. -/
def transverseNormalLift (C : NativeFaceHessianChart φ s H q lam N j a x)
    (v₀ : s) (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q) :
    (E × (s.erase v₀.val → ℝ)) →L[ℝ] Model d :=
  C.coverFiberEquiv.symm.toContinuousLinearMap.comp L

@[simp] theorem coverFiberEquiv_transverseNormalLift
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (v₀ : s) (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (z : E × (s.erase v₀.val → ℝ)) :
    C.coverFiberEquiv (C.transverseNormalLift v₀ L z) = L z :=
  C.coverFiberEquiv.apply_symm_apply _

theorem transverse_fderiv_eq_coverFiber
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ)) :
    fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
      (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a) =
      (faceFiberTransverseDifferential Q H v₀ q r).comp
        C.coverFiberEquiv.toContinuousLinearMap := by
  rw [C.transverse_fderiv_eq Q v₀.val hΦ r hmon, ← hHΦ]
  rfl

theorem transverseNormalLift_rightInverse
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ))) :
    (fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
      (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a)).comp
      (C.transverseNormalLift v₀ L) = ContinuousLinearMap.id ℝ _ := by
  rw [C.transverse_fderiv_eq_coverFiber Q v₀ hΦ hHΦ r hmon]
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    coverFiberEquiv_transverseNormalLift]
  exact congrArg (fun A : (E × (s.erase v₀.val → ℝ)) →L[ℝ] _ => A z) hL

end NativeFaceHessianChart

/-- The induced transverse metric is defined on one fixed target space.
At the critical torus its data depend only on the common radial point. -/
def fixedFaceTransverseMetric {n : ℕ} {s : Finset (Lattice n)}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (v₀ : s)
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q) :
    (E × (s.erase v₀.val → ℝ)) →L[ℝ] (E × (s.erase v₀.val → ℝ)) →L[ℝ] ℝ :=
  (faceFiberMetric H q).bilinearComp L L

section TransverseMetric

variable {n : ℕ} {s : Finset (Lattice n)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (H : RealSpace n →L[ℝ] RealSpace n) (q : s → ℝ) (v₀ : s)
  (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)

@[simp] theorem fixedFaceTransverseMetric_apply (z w : E × (s.erase v₀.val → ℝ)) :
    fixedFaceTransverseMetric H q v₀ L z w = faceFiberMetric H q (L z) (L w) := rfl

theorem fixedFaceTransverseMetric_symm
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (z w : E × (s.erase v₀.val → ℝ)) :
    fixedFaceTransverseMetric H q v₀ L z w = fixedFaceTransverseMetric H q v₀ L w z :=
  faceHessianMetricCLM_symm H hHsym (L z) (L w)

theorem fixedFaceTransverseMetric_pos (Q : RealSpace n →L[ℝ] E) (r : s → ℝ)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (z : E × (s.erase v₀.val → ℝ)) (hz : z ≠ 0) :
    0 < fixedFaceTransverseMetric H q v₀ L z z := by
  apply faceHessianMetricCLM_pos H hH
  intro hzero
  have he := congrArg (fun A : (E × (s.erase v₀.val → ℝ)) →L[ℝ] _ => A z) hL
  have hLz : L z = 0 := Subtype.ext hzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hLz,
    map_zero] at he
  exact hz he.symm

end TransverseMetric

namespace NativeFaceHessianChart

variable {n d : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold d} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transverse linearization of the actual native coordinate field,
using the normal lift of one fixed transverse differential. -/
def transverseLinearization (C : NativeFaceHessianChart φ s H q lam N j a x)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E) (v₀ : s)
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q) :
    (E × (s.erase v₀.val → ℝ)) →L[ℝ] (E × (s.erase v₀.val → ℝ)) :=
  (fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
    (j.map ((chartAt (Model d) a).symm y))) (chartAt (Model d) a a)).comp
    ((fderiv ℝ C.coordinateField (chartAt (Model d) a a)).comp (C.transverseNormalLift v₀ L))

theorem transverseLinearization_metric_pairing
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (horth : ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
      faceFiberMetric H q (L z) W = 0)
    (z w : E × (s.erase v₀.val → ℝ)) :
    fixedFaceTransverseMetric H q v₀ L (C.transverseLinearization Φ Q v₀ L z) w =
      C.coordinateMetric (chartAt (Model d) a a)
        (fderiv ℝ C.coordinateField (chartAt (Model d) a a) (C.transverseNormalLift v₀ L z))
        (C.transverseNormalLift v₀ L w) := by
  rw [fixedFaceTransverseMetric_apply, C.coordinateMetric_eq_faceFiberMetric hHφ,
    C.coverFiberEquiv_transverseNormalLift]
  unfold transverseLinearization
  rw [C.transverse_fderiv_eq_coverFiber Q v₀ hΦ hHΦ r hmon]
  exact metricNormal_lift_pairing _ _ L hL horth
    (fun V W => faceHessianMetricCLM_symm H hHsym V W) w _

/-- The chart lift is normal to the actual full-span conormal branch,
because the transverse kernel is exactly that branch tangent. -/
theorem transverseNormalLift_conormal_orthogonal
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (Q : RealSpace n →L[ℝ] E)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (v₀ : s) (r : s → ℝ) (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v)
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (horth : ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
      faceFiberMetric H q (L z) W = 0)
    (z : E × (s.erase v₀.val → ℝ)) (W : TangentCoordinates n)
    (hW : W ∈ faceConormalTangent s H q) :
    faceHessianMetric H
      (fderiv ℝ C.lift (chartAt (Model d) a a) (C.transverseNormalLift v₀ L z)) W = 0 := by
  have hmem := (mem_faceConormalTangent s H q W).mp hW
  have ha : W.2 ∈ faceRealTangent q := by
    rw [mem_faceRealTangent, hmem.2.2, map_zero]
  let W' : faceFiberPlane q := ⟨W, hmem.1, ha⟩
  have hk : faceFiberTransverseDifferential Q H v₀ q r W' = 0 :=
    (conormalTransverseLinearMap_eq_zero_iff Q _ hQ H s rfl v₀ q r hq hr W
      ⟨hmem.1, ha⟩).mpr hW
  have he := congrArg Subtype.val (C.coverFiberEquiv_transverseNormalLift v₀ L z)
  change fderiv ℝ C.lift (chartAt (Model d) a a) (C.transverseNormalLift v₀ L z) =
    (L z : TangentCoordinates n) at he
  rw [he]
  simpa only [faceFiberMetric_apply] using horth z W' hk

end NativeFaceHessianChart

namespace NativeFaceHessianChart

variable {n : ℕ} {φ : RealSpace n → ℝ} {s : Finset (Lattice n)}
  {H : RealSpace n →L[ℝ] RealSpace n} {q : s → ℝ} {lam : ℝ}
  {N : SmoothManifold (2 * n - 2)} {j : N.SmoothEmbedding (lgManifold n)}
  {a : N.Point} {x : TangentCoordinates n}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal transverse rate in the same native chart as the field. -/
def coordinateTransverseRate (C : NativeFaceHessianChart φ s H q lam N j a x)
    (Φ : RealSpace n → RealSpace n) (Q : RealSpace n →L[ℝ] E) (v₀ : s)
    (y : Model (2 * n - 2)) : E × (s.erase v₀.val → ℝ) :=
  fderiv ℝ (fun z => conormalTransverseCoordinates Φ Q s v₀.val
    (j.map ((chartAt (Model (2 * n - 2)) a).symm z))) y (C.coordinateField y)

/-- Differentiate the actual transverse rate. The second derivative of
the defining map contributes zero because the actual field vanishes. -/
theorem coordinateTransverseRate_fderiv
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) :
    fderiv ℝ (C.coordinateTransverseRate Φ Q v₀) (chartAt (Model (2 * n - 2)) a a) =
      (fderiv ℝ (fun y => conormalTransverseCoordinates Φ Q s v₀.val
        (j.map ((chartAt (Model (2 * n - 2)) a).symm y)))
        (chartAt (Model (2 * n - 2)) a a)).comp
        (fderiv ℝ C.coordinateField (chartAt (Model (2 * n - 2)) a a)) := by
  let ca := chartAt (Model (2 * n - 2)) a a
  let δ := conormalTransverseCoordinates Φ Q s v₀.val
  let f := fun y => δ (j.map ((chartAt (Model (2 * n - 2)) a).symm y))
  have hs : ContDiffAt ℝ ∞ (δ ∘ lgCover) x := by
    let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    exact ((contMDiffAt_conormalTransverseCoordinates_native Q s v₀.val
      (lgCover x) hΦ).comp x (contMDiff_lgCover n).contMDiffAt).contDiffAt
  have hf : ContDiffAt ℝ ∞ f ca := by
    apply ((C.center.symm ▸ hs).comp ca C.smooth).congr_of_eventuallyEq
    filter_upwards [C.cover] with y hy
    exact (congrArg δ hy).symm
  have hD := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hZ := (C.coordinateField_smooth hφ
    (fun b => tailoring_fullFiber_nondegenerate I β hφ hc hlower hpi j himage b)).differentiableAt
      (by simp)
  have hz : C.coordinateField ca = 0 :=
    C.coordinateField_zero I β hφ hc hlower hpi himage hgood
  change fderiv ℝ (fun y => fderiv ℝ f y (C.coordinateField y)) ca =
    (fderiv ℝ f ca).comp (fderiv ℝ C.coordinateField ca)
  rw [(hD.hasFDerivAt.clm_apply hZ.hasFDerivAt).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, hz, map_zero, add_zero]
  rfl

/-- The transported positive operator is the derivative of the actual
transverse rate evaluated on the constructed normal lift. -/
theorem transverseLinearization_eq_rate_derivative
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1)
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q) :
    C.transverseLinearization Φ Q v₀ L =
      (fderiv ℝ (C.coordinateTransverseRate Φ Q v₀)
        (chartAt (Model (2 * n - 2)) a a)).comp (C.transverseNormalLift v₀ L) := by
  rw [C.coordinateTransverseRate_fderiv I β hφ hc hlower hpi himage hgood Q v₀ hΦ]
  rfl

/-- The pairing of the actual transverse linearization is the literal
constrained Hessian on the one fixed normal lift. In particular, these
pairings have no angle or native-chart dependence when cover data agree. -/
theorem transverseLinearization_metric_eq_faceConstrainedPairing
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (horth : ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
      faceFiberMetric H q (L z) W = 0)
    (z w : E × (s.erase v₀.val → ℝ)) :
    fixedFaceTransverseMetric H q v₀ L (C.transverseLinearization Φ Q v₀ L z) w =
      faceConstrainedPairing s H q lam (L z) (L w) := by
  rw [C.transverseLinearization_metric_pairing Q v₀ hΦ hHΦ hHφ hHsym r hmon L hL horth,
    C.coordinate_linearization I β hφ hc hlower hpi himage hgood]
  change fderiv ℝ (fderiv ℝ (fun y => φ
    (j.map ((chartAt (Model (2 * n - 2)) a).symm y)).1))
    (chartAt (Model (2 * n - 2)) a a) (C.transverseNormalLift v₀ L z)
    (C.transverseNormalLift v₀ L w) = _
  rw [C.hessian]
  have he (u : E × (s.erase v₀.val → ℝ)) :=
    congrArg Subtype.val (C.coverFiberEquiv_transverseNormalLift v₀ L u)
  exact congrArg₂ (faceConstrainedPairing s H q lam) (he z) (he w)

/-- Positivity of the actual native derivative transports to the one fixed
transverse metric. The native positivity is proved from the actual gradient
and Hessian blocks, rather than supplied as an expansion hypothesis. -/
theorem fixed_transverse_linearization_pos
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v) (hlam : 0 < lam)
    {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R)
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (horth : ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
      faceFiberMetric H q (L z) W = 0)
    (z : E × (s.erase v₀.val → ℝ)) (hz : z ≠ 0) :
    0 < fixedFaceTransverseMetric H q v₀ L (C.transverseLinearization Φ Q v₀ L z) z := by
  rw [C.transverseLinearization_metric_pairing Q v₀ hΦ hHΦ hHφ hHsym r hmon L hL horth]
  apply C.coordinate_linearization_pos_on_conormal_normal I β hφ hc hlower hpi himage
    hgood hB hnormal hHsym hH hq hlam
  · intro hzero
    have he := congrArg (fun A : (E × (s.erase v₀.val → ℝ)) →L[ℝ] _ => A z)
      (C.transverseNormalLift_rightInverse Q v₀ hΦ hHΦ r hmon L hL)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      hzero, map_zero] at he
    exact hz he.symm
  · exact C.transverseNormalLift_conormal_orthogonal Q hQ v₀ r hq hr L horth z

theorem fixed_transverse_linearization_selfadjoint
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q)
    (hL : (faceFiberTransverseDifferential Q H v₀ q r).comp L =
      ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)))
    (horth : ∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
      faceFiberMetric H q (L z) W = 0)
    (z w : E × (s.erase v₀.val → ℝ)) :
    fixedFaceTransverseMetric H q v₀ L (C.transverseLinearization Φ Q v₀ L z) w =
      fixedFaceTransverseMetric H q v₀ L z (C.transverseLinearization Φ Q v₀ L w) := by
  rw [fixedFaceTransverseMetric_symm H q v₀ L hHsym z _,
    C.transverseLinearization_metric_pairing Q v₀ hΦ hHΦ hHφ hHsym r hmon L hL horth,
    C.transverseLinearization_metric_pairing Q v₀ hΦ hHΦ hHφ hHsym r hmon L hL horth,
    C.coordinate_linearization_selfadjoint I β hφ hc hlower hpi himage hgood,
    C.coordinateMetric_symm hφ]

/-- Compose the actual submersion, metric normal construction and native
gradient producer. The resulting metric is defined using only fixed cover
data, and the positive operator is the actual differentiated transverse rate. -/
theorem exists_fixed_metric_positive_transverse_linearization
    (C : NativeFaceHessianChart φ s H q lam N j a x)
    (I : ToricInput n) (β : ℝ) (hφ : ContDiff ℝ ∞ φ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1})
    (hgood : ∀ᶠ p in 𝓝 (lgCover x), ∀ v ∈ tailoringExponents I,
      tailoringCutoff I β v p.1 = 0 ∨ tailoringCutoff I β v p.1 = 1)
    {Φ : RealSpace n → RealSpace n} (Q : RealSpace n →L[ℝ] E)
    (hQsurj : Surjective Q)
    (hQ : ∀ u, Q u = 0 ↔ u ∈ Submodule.span ℝ (positiveCone s))
    (v₀ : s) (hΦ : ContDiffAt ℝ ∞ Φ x.1) (hHΦ : H = fderiv ℝ Φ x.1)
    (hHφ : H = fderiv ℝ (coordinateGradient φ) x.1) (hHsurj : Surjective H)
    (hHsym : ∀ X Y, (∑ i, H X i * Y i) = ∑ i, H Y i * X i)
    (hH : ∀ e : RealSpace n, e ≠ 0 → 0 < ∑ i, H e i * e i)
    (r : s → ℝ) (hmon : ∀ v : s, monomial 1 v.val (lgCover x) = (r v : ℂ))
    (hq : ∀ v, 0 < q v) (hr : ∀ v, 0 < r v) (hlam : 0 < lam)
    (hA : Surjective (faceLevelMap s))
    (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ))
    (hB : (faceLevelMap s).comp B = ContinuousLinearMap.id ℝ (s → ℝ))
    (hnormal : H.comp B = (faceNormalMap s).comp R) :
    ∃ L : (E × (s.erase v₀.val → ℝ)) →L[ℝ] faceFiberPlane q,
      (faceFiberTransverseDifferential Q H v₀ q r).comp L =
        ContinuousLinearMap.id ℝ (E × (s.erase v₀.val → ℝ)) ∧
      (∀ z W, faceFiberTransverseDifferential Q H v₀ q r W = 0 →
        faceFiberMetric H q (L z) W = 0) ∧
      (∀ z w, fixedFaceTransverseMetric H q v₀ L z w =
        fixedFaceTransverseMetric H q v₀ L w z) ∧
      (∀ z, z ≠ 0 → 0 < fixedFaceTransverseMetric H q v₀ L z z) ∧
      C.transverseLinearization Φ Q v₀ L =
        (fderiv ℝ (C.coordinateTransverseRate Φ Q v₀)
          (chartAt (Model (2 * n - 2)) a a)).comp (C.transverseNormalLift v₀ L) ∧
      (∀ z w, fixedFaceTransverseMetric H q v₀ L (C.transverseLinearization Φ Q v₀ L z) w =
        fixedFaceTransverseMetric H q v₀ L z (C.transverseLinearization Φ Q v₀ L w)) ∧
      (∀ z, z ≠ 0 → 0 < fixedFaceTransverseMetric H q v₀ L
        (C.transverseLinearization Φ Q v₀ L z) z) := by
  obtain ⟨L, hL, horth⟩ := exists_fixed_faceTransverse_normalLift Q hQsurj H hHsurj
    hHsym hH v₀ q r hq hr hQ hA B R hB hnormal
  exact ⟨L, hL, horth, fixedFaceTransverseMetric_symm H q v₀ L hHsym,
    fixedFaceTransverseMetric_pos H q v₀ L Q r hL hH,
    C.transverseLinearization_eq_rate_derivative I β hφ hc hlower hpi himage hgood Q v₀ hΦ L,
    C.fixed_transverse_linearization_selfadjoint I β hφ hc hlower hpi himage hgood
      Q v₀ hΦ hHΦ hHφ hHsym r hmon L hL horth,
    C.fixed_transverse_linearization_pos I β hφ hc hlower hpi himage hgood Q hQ
      v₀ hΦ hHΦ hHφ hHsym hH r hmon hq hr hlam hB hnormal L hL horth⟩

end NativeFaceHessianChart

end FsFltz
