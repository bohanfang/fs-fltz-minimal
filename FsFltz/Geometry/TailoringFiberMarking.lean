import FsFltz.Analysis.TailoringCompleteFlow
import FsFltz.Analysis.TailoringIntrinsicExhaustion
import FsFltz.Geometry.PotentialFiberMarking

/-!
# Actual full tailored-fiber truncation markings

Source: `geometric-part-fsf-proof.tex`, `subsec:fiberends`, lines 1198–1237.
The actual complete restricted primitive and whole-end intrinsic exhaustion
estimate construct every large full-fiber truncation and its inclusion
completion marking. No parameter-smooth family or nonempty tailored fiber
is inferred from regularity alone.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

section Domain
variable {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (I : ToricInput n) (β s : ℝ)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β s y = 1})

include hφ hEnd1 hEnd hhom hc hlower hL hend himage
/-- Closedness of the entire literal tailored fiber makes all actual
potential sublevels compact on that same fiber realization. -/
theorem isCompact_tailoringFiber_potential_sublevel (A : ℝ) :
    IsCompact {x : N.Point | φ (j.map x).1 ≤ A} := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hclosed : IsClosed (range j.map) := by
    rw [himage]
    exact isClosed_eq (contMDiff_tailoringFamily_lgManifold I β s).continuous continuous_const
  have hj : Topology.IsClosedEmbedding j.map := ⟨j.embedding, hclosed⟩
  exact hj.isCompact_preimage (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A)

omit hEnd1 hEnd hhom hc hlower hL hend himage in
private theorem tailoring_fiber_defining_derivative (A : ℝ) (x : N.Point) (v : N.Tangent x) :
    N.scalarDerivative (fun y => φ (j.map y).1 - A) x v =
      N.scalarDerivative (fun y => φ (j.map y).1) x v := by
  unfold scalarDerivative
  change mfderiv _ _ ((fun y => φ (j.map y).1) - fun _ => A) x v = _
  rw [mfderiv_sub ((contMDiff_potential_W_level_value hφ j).mdifferentiable (by simp) x)
    mdifferentiableAt_const, mfderiv_const, sub_zero]
  rfl

variable (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
    (A : ℝ) (hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x))

private theorem tailoring_fiber_defining_compact :
    IsCompact {x : N.Point | φ (j.map x).1 - A ≤ 0} := by
  simpa only [sub_nonpos] using
    isCompact_tailoringFiber_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage A

omit hEnd1 hEnd hhom hc hlower hL hend himage in
include hpos in
private theorem tailoring_fiber_defining_outward (x : N.Point) (hx : φ (j.map x).1 - A = 0) :
    0 < N.scalarDerivative (fun y => φ (j.map y).1 - A) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) := by
  rw [tailoring_fiber_defining_derivative hφ j A]
  exact hpos x (le_of_eq (sub_eq_zero.mp hx).symm)

/-- The native full potential truncation of the tailored fiber. The actual
complete primitive and outward boundary datum are produced by the uniform
geometric consumer below. -/
def tailoringFiberOutwardDomain : LiouvilleDomain (2 * n - 2) :=
  regularSublevelLiouvilleDomain N (fun x => φ (j.map x).1 - A)
    ((contMDiff_potential_W_level_value hφ j).sub_const A)
    (tailoring_fiber_defining_compact hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage A)
    _ P.smooth_primitive P.symplectic (tailoring_fiber_defining_outward hφ j A hpos)

local notation "Dfib" => tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos

/-- The entire carrier is the literal potential sublevel of the full fiber. -/
theorem tailoringFiberOutwardDomain_carrier :
    (Dfib).domain.carrier = {x : N.Point | φ (j.map x).1 ≤ A} := by
  ext x
  change φ (j.map x).1 - A ≤ 0 ↔ φ (j.map x).1 ≤ A
  exact sub_nonpos

/-- The actual native frontier is the chosen potential level. -/
theorem tailoringFiberOutwardDomain_frontier :
    frontier (Dfib).domain.carrier = {x : N.Point | φ (j.map x).1 = A} := by
  have h := regularSublevelLiouvilleDomain_frontier N (fun x => φ (j.map x).1 - A)
    ((contMDiff_potential_W_level_value hφ j).sub_const A)
    (tailoring_fiber_defining_compact hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage A)
    _ P.smooth_primitive P.symplectic (tailoring_fiber_defining_outward hφ j A hpos)
  simpa only [tailoringFiberOutwardDomain, sub_eq_zero] using h

include hpos in
/-- The actual complete intrinsic fiber flow enters its literal truncation. -/
theorem tailoringFiber_absorbs_outward_sublevel (x : N.Point) :
    ∃ T : ℝ, 0 ≤ T ∧ φ (j.map (P.completeFlow.flow (-T) x)).1 ≤ A := by
  apply P.completeFlow.exists_nonneg_time_scalar_le (fun y => φ (j.map y).1)
    (contMDiff_potential_W_level_value hφ j) P.smooth_field
    (isCompact_tailoringFiber_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage) A
  exact hpos

/-- The whole actual intrinsic flow constructs the sublevel completion. -/
def tailoringFiberOutwardCompletion : Completion Dfib :=
  FlowAbsorptionMarking.completionOfSublevelAbsorption Dfib P (fun y => φ (j.map y).1)
    (contMDiff_potential_W_level_value hφ j)
    (tailoringFiberOutwardDomain_frontier hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)
    hpos (tailoringFiberOutwardDomain_carrier hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)
    (tailoringFiber_absorbs_outward_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)

/-- The flow-built completion is marked onto the same entire literal fiber. -/
def tailoringFiberOutwardInclusionMarking :
    InclusionMarking (tailoringFiberOutwardCompletion hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)
      P.toCompleteLiouvilleManifold (fun x => x.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 2)) N.Point ∞
  primitive := N.pullback_id _
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- Every chosen completion of the same actual truncation has its full
tailored-fiber inclusion marking. -/
def tailoringFiberOutwardInclusionMarkingOfCompletion (C : Completion Dfib) :
    InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val) :=
  C.transportInclusionMarking
    (tailoringFiberOutwardCompletion hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)
    P.toCompleteLiouvilleManifold (fun x => x.val)
    (tailoringFiberOutwardInclusionMarking hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos)

/-- The embedded compact carrier is the full literal tailored truncation. -/
theorem tailoringFiberOutwardDomain_image :
    j.map '' (Dfib).domain.carrier = {y | tailoringFamily I β s y = 1 ∧ φ y.1 ≤ A} := by
  rw [tailoringFiberOutwardDomain_carrier]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hy : j.map x ∈ range j.map := ⟨x, rfl⟩
    rw [himage] at hy
    exact ⟨hy, hx⟩
  · rintro ⟨hf, hφ⟩
    have hy : y ∈ range j.map := by rw [himage]; exact hf
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, hφ, rfl⟩
end Domain

/-- One threshold gives actual completion markings of every later full
potential truncation of the literal tailored level-one fiber. The chosen
potential and full fiber remain fixed during each construction, and every
chosen completion of the constructed truncation is marked. Nonemptiness
of the tailored level and parameter-smooth family data are not conclusions. -/
theorem _root_.FsFltz.tailoringFamily_exists_uniform_fullFiber_markings
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ∃ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (P : CompletePrimitive N (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)))
        (himage : range j.map = {y | tailoringFamily I β s y = 1}),
      ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∃ hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
        0 < N.scalarDerivative (fun y => φ (j.map y).1) x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x),
      let E := tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos
      j.map '' E.domain.carrier = {y | tailoringFamily I β s y = 1 ∧ φ y.1 ≤ A} ∧
        Nonempty (Completion E) ∧ ∀ C : Completion E,
          Nonempty (InclusionMarking C P.toCompleteLiouvilleManifold (fun x => x.val)) := by
  obtain ⟨Bfull, _hBfull, hfull⟩ := tailoringFamily_exists_uniform_completeFullFiber
    I hφ hc hU hlower hupper hEnd hhom hL hend
  obtain ⟨F, hF, Bout, _hBout, hout⟩ := tailoringFamily_exists_uniform_whole_end_intrinsic_exhaustion
    I hφ hc hU hlower hupper hEnd hhom hL hend
  obtain ⟨_d, _hd, _R, _hR, Bπ, _hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (L ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bφ : ℝ := (2 * max V 0 + 1) / F
  let β₀ : ℝ := max 1 (max Bfull (max Bout (max Bπ Bφ)))
  refine ⟨F, hF, β₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro β hβ s hs
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ₁
  have hβfull : Bfull ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβout : Bout ≤ β := (le_max_left _ _).trans
    ((le_max_right Bfull _).trans ((le_max_right 1 _).trans hβ))
  have hβπ : Bπ ≤ β := (le_max_left _ _).trans ((le_max_right Bout _).trans
    ((le_max_right Bfull _).trans ((le_max_right 1 _).trans hβ)))
  have hβφ : Bφ ≤ β := (le_max_right _ _).trans ((le_max_right Bout _).trans
    ((le_max_right Bfull _).trans ((le_max_right 1 _).trans hβ)))
  have hlevel : V < F ^ 2 * β ^ 2 / 2 := by
    have hb : 2 * max V 0 + 1 ≤ F * β := by
      have h := (div_le_iff₀ hF).mp hβφ
      simpa only [mul_comm] using h
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 1) hb 2
    nlinarith only [hsq, le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  have hlevelpos : 0 < F ^ 2 * β ^ 2 / 2 := by positivity
  obtain ⟨N, j, himage, ⟨P⟩⟩ := hfull β hβfull s hs
  refine ⟨N, j, P, himage, ?_⟩
  intro A hA
  have hpi : ∀ y, tailoringFamily I β s y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β s) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β hβπ s hs y _).2.2 (by simp only [hy, norm_one, le_refl])
  have hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) := by
    intro x hx
    have hφpos : 0 < φ (j.map x).1 := hlevelpos.trans_le (hA.trans hx)
    have hxEnd : L < ‖(WithLp.toLp 2 (j.map x).1 : EuclideanSpace ℝ (Fin n))‖ := by
      by_contra hn
      have hsq : realSquaredNorm (j.map x).1 ≤ L ^ 2 := by
        simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using
          (sq_le_sq₀ (norm_nonneg _) hL.le).mpr (le_of_not_gt hn)
      have hm : j.map x ∈ {y : LGSpace n | phi0 y ≤ L ^ 2 / 2} := by
        change realSquaredNorm (j.map x).1 / 2 ≤ L ^ 2 / 2
        linarith only [hsq]
      have hb := hV (mem_image_of_mem (fun y : LGSpace n => φ y.1) hm)
      change φ (j.map x).1 ≤ V at hb
      exact (not_le_of_gt hlevel) ((hA.trans hx).trans hb)
    let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 (j.map x).1)
    have he : metricRadialSq H (j.map x).1 = 2 * φ (j.map x).1 :=
      metricRadialSq_potential_eq_two_mul hEnd1 hEnd hhom hc hlower hL hend _ hxEnd
    have hr : F * β ≤ Real.sqrt (metricRadialSq H (j.map x).1) := by
      rw [he]
      apply (Real.le_sqrt (mul_nonneg hF.le hβpos.le) (by positivity)).mpr
      nlinarith only [hA.trans hx]
    have hval : tailoringFamily I β s (j.map x) = 1 := by
      have hm : j.map x ∈ range j.map := ⟨x, rfl⟩
      rwa [himage] at hm
    have hd := hout β hβout s hs N j x
      (tailoringFamily_levelEmbedding_tangent_range I hφ hc hlower β s 1 hpi j himage x)
      hr (by simp only [hval, norm_one]; norm_num)
    change metricRadialSq H (j.map x).1 / 2 ≤
      N.scalarDerivative ((fun y => φ y.1) ∘ j.map) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) at hd
    rw [he] at hd
    change 2 * φ (j.map x).1 / 2 ≤
      N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) at hd
    have hd' : φ (j.map x).1 ≤ N.scalarDerivative (fun y => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) := by
      linarith only [hd]
    exact hφpos.trans_le hd'
  refine ⟨hpos, ?_, ?_, ?_⟩
  · exact tailoringFiberOutwardDomain_image hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos
  · exact ⟨tailoringFiberOutwardCompletion hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos⟩
  · intro C
    exact ⟨tailoringFiberOutwardInclusionMarkingOfCompletion hφ hEnd1 hEnd hhom hc hlower hL hend I β s j himage P A hpos C⟩

end FsFltz.Geometry
