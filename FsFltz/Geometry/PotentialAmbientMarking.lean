import FsFltz.Geometry.PotentialAmbientCompleteFlow
import FsFltz.Geometry.RegularSublevelDomain
import FsFltz.Geometry.FlowAbsorptionMarking

/-!
# Full potential sublevels and their actual ambient inclusion markings

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and `lem:absorption`, lines 444–468. Every sufficiently large literal
potential sublevel is completed by the actual native holomorphic Liouville
flow onto the given quotient ambient, for all finite nonnegative K.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

section Domain

variable {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K)

local notation "P" => potential_W_ambientCompletePrimitive hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK

include hφ

private theorem potential_ambient_defining_derivative (A : ℝ)
    (y : (lgManifold n).Point) (v : (lgManifold n).Tangent y) :
    (lgManifold n).scalarDerivative (fun y => (fun y : (lgManifold n).Point => φ (Prod.fst y)) y - A) y v =
      (lgManifold n).scalarDerivative (fun y : (lgManifold n).Point => φ (Prod.fst y)) y v := by
  unfold scalarDerivative
  change mfderiv _ _ ((fun y : (lgManifold n).Point => φ (Prod.fst y)) - fun _ => A) y v = _
  rw [mfderiv_sub ((contMDiff_potentialValue hφ).mdifferentiable (by simp) y)
    mdifferentiableAt_const, mfderiv_const, sub_zero]
  rfl

variable (A : ℝ)
    (hpos : ∀ y : (lgManifold n).Point, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun y : (lgManifold n).Point => φ (Prod.fst y)) y ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) y))

include hEnd1 hEnds hhom hc hlower hL hend in
private theorem potential_ambient_defining_compact :
    IsCompact {y : (lgManifold n).Point | (fun y : (lgManifold n).Point => φ (Prod.fst y)) y - A ≤ 0} := by
  have h := isCompact_potential_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend A
  simp only [sub_nonpos]
  exact h

include hpos

/-- The native compact domain is the full literal potential sublevel.
The uniform geometric theorem below proves its outward condition. -/
def potential_W_ambientOutwardDomain : LiouvilleDomain (2 * n) :=
  regularSublevelLiouvilleDomain (lgManifold n) (fun y => (fun y : (lgManifold n).Point => φ (Prod.fst y)) y - A)
    ((contMDiff_potentialValue hφ).sub_const A)
    (potential_ambient_defining_compact hφ hEnd1 hEnds hhom hc hlower hL hend A)
    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) ((lgManifold n).isSmoothForm_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I) K)
    (isSymplecticOn_potential_W_ambient hφ hc hlower I hK)
    (fun y hy => by
      rw [potential_ambient_defining_derivative hφ A]
      exact hpos y (le_of_eq (sub_eq_zero.mp hy).symm))

local notation "D" => potential_W_ambientOutwardDomain hφ hEnd1 hEnds hhom hc hlower hL hend I hK A hpos

/-- Exact carrier of the native potential domain. -/
theorem potential_W_ambientOutwardDomain_carrier :
    (D).domain.carrier = {y : LGSpace n | φ y.1 ≤ A} := by
  ext y
  change φ y.1 - A ≤ 0 ↔ φ y.1 ≤ A
  exact sub_nonpos

/-- Exact native frontier of the potential domain. -/
theorem potential_W_ambientOutwardDomain_frontier :
    frontier (D).domain.carrier = {y : LGSpace n | φ y.1 = A} := by
  have h := regularSublevelLiouvilleDomain_frontier (lgManifold n) (fun y => (fun y : (lgManifold n).Point => φ (Prod.fst y)) y - A)
    ((contMDiff_potentialValue hφ).sub_const A)
    (potential_ambient_defining_compact hφ hEnd1 hEnds hhom hc hlower hL hend A)
    ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K) ((lgManifold n).isSmoothForm_rankTwoPrimitive
      (isSmoothForm_lambdaPotentialForm hφ) (contMDiff_W_lgManifold I) K)
    (isSymplecticOn_potential_W_ambient hφ hc hlower I hK)
    (fun y hy => by
      rw [potential_ambient_defining_derivative hφ A]
      exact hpos y (le_of_eq (sub_eq_zero.mp hy).symm))
  simp only [sub_eq_zero] at h
  exact h

/-- The actual ambient flow enters the full potential truncation in finite
negative time. -/
theorem potential_W_ambient_absorbs_outward_sublevel (y : (lgManifold n).Point) :
    ∃ T : ℝ, 0 ≤ T ∧ φ ((P).completeFlow.flow (-T) y).1 ≤ A := by
  apply (P).completeFlow.exists_nonneg_time_scalar_le (fun y : (lgManifold n).Point => φ (Prod.fst y))
    (contMDiff_potentialValue hφ) (P).smooth_field
    (isCompact_potential_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend) A
  exact hpos

/-- The flow-built completion of this same full literal ambient sublevel. -/
def potential_W_ambientOutwardCompletion : Completion D :=
  FlowAbsorptionMarking.completionOfSublevelAbsorption D P (fun y : (lgManifold n).Point => φ (Prod.fst y))
    (contMDiff_potentialValue hφ)
    (potential_W_ambientOutwardDomain_frontier hφ hEnd1 hEnds hhom hc hlower hL hend I hK A hpos)
    hpos (potential_W_ambientOutwardDomain_carrier hφ hEnd1 hEnds hhom hc hlower hL hend I hK A hpos)
    (potential_W_ambient_absorbs_outward_sublevel hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK A hpos)

/-- The marking agrees with inclusion on the compact domain and with
the actual native ambient flow on every boundary cylinder point. -/
def potential_W_ambientOutwardInclusionMarking :
    InclusionMarking (potential_W_ambientOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK A hpos)
      (P).toCompleteLiouvilleManifold (fun y => y.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model (2 * n)) (lgManifold n).Point ∞
  primitive := (lgManifold n).pullback_id ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (W I) K)
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- Every completion of this same native domain has its actual ambient
inclusion-induced marking. -/
def potential_W_ambientOutwardInclusionMarkingOfCompletion (C : Completion D) :
    InclusionMarking C (P).toCompleteLiouvilleManifold (fun y => y.val) :=
  C.transportInclusionMarking
    (potential_W_ambientOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK A hpos)
    (P).toCompleteLiouvilleManifold (fun y => y.val)
    (potential_W_ambientOutwardInclusionMarking hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I hK A hpos)

include hEnds hhom hc hU hlower hupper hL hend in
omit hpos hK in
/-- The actual ambient derivative is positive above one common potential
level for the whole coefficient path and every finite nonnegative K. -/
theorem ToricInput.coefficientPath_potential_ambient_outward :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ K : ℝ, 0 ≤ K →
      ∀ y : (lgManifold n).Point, A₀ ≤ φ y.1 →
        0 < (lgManifold n).scalarDerivative (fun y => φ y.1) y
          ((lgManifold n).liouvilleVector
            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
              (W (I.alongCoefficientPath t)) K) y) := by
  obtain ⟨q, hq, Lmargin, hLmargin, hmargin⟩ :=
    I.coefficientPath_metric_quantitative_ambient_margin hc hU
  let Lbig := max L Lmargin
  have hLbig : 0 < Lbig := hL.trans_le (le_max_left _ _)
  obtain ⟨B, hB⟩ := (isCompact_phi0_sublevel (n := n) (Lbig ^ 2 / 2)
    (by positivity)).exists_bound_of_continuousOn
      (hφ.continuous.comp continuous_fst).continuousOn
  let A₀ := max B 0 + 1
  have hA₀ : 0 < A₀ := by dsimp [A₀]; linarith [le_max_right B 0]
  refine ⟨A₀, hA₀, ?_⟩
  intro t ht K hK y hy
  have hout : Lbig < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra h
    have hs := (sq_le_sq₀ (norm_nonneg _) hLbig.le).mpr (le_of_not_gt h)
    have hx : phi0 y ≤ Lbig ^ 2 / 2 := by
      have hs' : realSquaredNorm y.1 ≤ Lbig ^ 2 := by
        simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using hs
      change realSquaredNorm y.1 / 2 ≤ Lbig ^ 2 / 2
      linarith
    have hb : φ y.1 ≤ B := (Real.le_norm_self _).trans (hB y hx)
    dsimp [A₀] at hy
    linarith [le_max_left B 0]
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 x.1)
  have hs : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
    inner_fderiv_gradient_symmetric
      (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
  have hl : ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v := hlower _
  have hu : ∀ v, inner ℝ (H v) v ≤ U * ‖v‖ ^ 2 := hupper _
  have hnorm : Real.sqrt (realSquaredNorm x.1) =
      ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n)))]
    congr 1
    simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
  obtain ⟨ha, hm⟩ := hmargin t ht (lgCover x)
    (show Lmargin ≤ Real.sqrt (realSquaredNorm (lgCover x).1) by
      rw [lgCover, hnorm]; exact (le_max_right _ _).trans hout.le) H hs hl hu
  have hr : 0 < metricRadialSq H x.1 :=
    (mul_pos hc (sq_pos_of_pos (hLbig.trans hout))).trans_le (hl (WithLp.toLp 2 x.1))
  have hqpos : 0 < potentialMetricMargin H (I.alongCoefficientPath t) (lgCover x) :=
    (mul_pos (mul_pos hq (Real.sqrt_pos.mpr hr))
      (sq_pos_of_pos ((I.alongCoefficientPath t).maxMonomialMagnitude_pos (lgCover x)))).trans_le hm
  have hx : L < ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ :=
    lt_of_le_of_lt (le_max_left _ _) hout
  rw [(liouville_identities_potential_W_on_homogeneous_end
    hφ hc hlower hEnds hhom hL hend (I.alongCoefficientPath t) x hx hK).2]
  exact div_pos (add_pos_of_pos_of_nonneg hr (mul_nonneg hK hqpos.le))
    (by positivity)

include hEnd1 hEnds hhom hc hU hlower hupper hL hend in
omit hpos hK in
/-- Above one derived coefficient-path level, every full literal potential
sublevel has an actual completion and every chosen completion is marked
onto the given whole ambient by inclusion and its native flow. -/
theorem ToricInput.coefficientPath_exists_potentialAmbient_markings :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ K : ℝ, ∀ hK : 0 ≤ K,
      ∀ A : ℝ, A₀ ≤ A →
      ∃ hpos : ∀ y : (lgManifold n).Point, A ≤ φ y.1 →
        0 < (lgManifold n).scalarDerivative (fun y => φ y.1) y
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (W (I.alongCoefficientPath t)) K) y),
      let Damb := potential_W_ambientOutwardDomain hφ hEnd1 hEnds hhom hc hlower hL hend
        (I.alongCoefficientPath t) hK A hpos
      let Pamb := potential_W_ambientCompletePrimitive hφ hEnd1 hEnds hhom hc hU hlower hupper
        hL hend (I.alongCoefficientPath t) hK
      Damb.domain.carrier = {y : LGSpace n | φ y.1 ≤ A} ∧
        Nonempty (Completion Damb) ∧ ∀ C : Completion Damb,
          Nonempty (InclusionMarking C Pamb.toCompleteLiouvilleManifold (fun y => y.val)) := by
  obtain ⟨A₀, hA₀, hout⟩ := ToricInput.coefficientPath_potential_ambient_outward
    hφ hEnds hhom hc hU hlower hupper hL hend I
  refine ⟨A₀, hA₀, ?_⟩
  intro t ht K hK A hA
  have hpos : ∀ y : (lgManifold n).Point, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun y => φ y.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (W (I.alongCoefficientPath t)) K) y) :=
    fun y hy => hout t ht K hK y (hA.trans hy)
  refine ⟨hpos, ?_, ?_, ?_⟩
  · exact potential_W_ambientOutwardDomain_carrier hφ hEnd1 hEnds hhom hc hlower hL hend
      (I.alongCoefficientPath t) hK A hpos
  · exact ⟨potential_W_ambientOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend
      (I.alongCoefficientPath t) hK A hpos⟩
  · intro C
    exact ⟨potential_W_ambientOutwardInclusionMarkingOfCompletion hφ hEnd1 hEnds hhom hc hU
      hlower hupper hL hend (I.alongCoefficientPath t) hK A hpos C⟩

end Domain
end FsFltz.Geometry
