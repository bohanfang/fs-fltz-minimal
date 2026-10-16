import FsFltz.Geometry.PotentialFiberCompleteFlowNative
import FsFltz.Geometry.RegularSublevelDomain
import FsFltz.Geometry.FlowAbsorptionMarking
import FsFltz.Analysis.LaurentSurjectivity

/-!
# Actual potential-fiber truncations and their full-fiber markings

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and matching truncations, lines 1011–1049. The proved intrinsic outwardness
and actual complete fiber flow construct negative entry and a native
completion marking for every truncation above the common logarithmic
threshold. The compact fiber is the literal full potential sublevel.
-/

noncomputable section
set_option autoImplicit false
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
    (I : ToricInput n) (w : ℂ) (ha : ∀ y, W I y = w → 0 < a I y)
    {N : SmoothManifold (2 * n - 2)} (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | W I y = w})

local notation "η" => (fun x : N.Point => φ (Prod.fst (j.map x)))
local notation "μ" => N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)
local notation "P" => potential_W_levelCompletePrimitive hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage

include hφ

/-- Smoothness of the actual potential on the given full fiber. -/
theorem contMDiff_potential_W_level_value :
    ContMDiff 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ) ∞ η := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  exact (contMDiff_potentialValue hφ).comp j.map.contMDiff

private theorem potential_fiber_defining_derivative (A : ℝ) (x : N.Point) (v : N.Tangent x) :
    N.scalarDerivative (fun y => η y - A) x v = N.scalarDerivative η x v := by
  unfold scalarDerivative
  change mfderiv _ _ (η - fun _ => A) x v = _
  rw [mfderiv_sub ((contMDiff_potential_W_level_value hφ j).mdifferentiable (by simp) x)
    mdifferentiableAt_const, mfderiv_const, sub_zero]
  rfl

variable (A : ℝ)
    (hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y : N.Point => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x))

include hEnd1 hEnds hhom hc hlower hL hend himage in
private theorem potential_fiber_defining_compact : IsCompact {x : N.Point | η x - A ≤ 0} := by
  simpa only [Function.comp_apply, sub_nonpos] using
    isCompact_potential_W_level_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend I w j himage A

include hpos in
private theorem potential_fiber_defining_outward (x : N.Point) (hx : η x - A = 0) :
    0 < N.scalarDerivative (fun y => η y - A) x (N.liouvilleVector μ x) := by
  rw [potential_fiber_defining_derivative hφ j A]
  exact hpos x (le_of_eq (sub_eq_zero.mp hx).symm)

/-- The native regular-sublevel domain used by the full geometric consumer
below. The explicit derivative condition is a boundary datum for this
definition; the uniform theorem proves that condition from the chosen end. -/
def potential_W_levelOutwardDomain : LiouvilleDomain (2 * n - 2) :=
  regularSublevelLiouvilleDomain N (fun x => η x - A)
    ((contMDiff_potential_W_level_value hφ j).sub_const A)
    (potential_fiber_defining_compact hφ hEnd1 hEnds hhom hc hlower hL hend I w j himage A)
    μ (N.isSmoothForm_pullback_one (lgManifold n) j.map _ (isSmoothForm_lambdaPotentialForm hφ))
    (isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage)
    (potential_fiber_defining_outward hφ j A hpos)

local notation "D" => potential_W_levelOutwardDomain hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos

/-- The constructed domain carrier is the full literal potential truncation. -/
theorem potential_W_levelOutwardDomain_carrier :
    (D).domain.carrier = {x : N.Point | η x ≤ A} := by
  ext x
  change η x - A ≤ 0 ↔ η x ≤ A
  exact sub_nonpos

/-- Its native frontier is precisely the actual chosen potential level. -/
theorem potential_W_levelOutwardDomain_frontier :
    frontier (D).domain.carrier = {x : N.Point | η x = A} := by
  have h := regularSublevelLiouvilleDomain_frontier N (fun x => η x - A)
    ((contMDiff_potential_W_level_value hφ j).sub_const A)
    (potential_fiber_defining_compact hφ hEnd1 hEnds hhom hc hlower hL hend I w j himage A)
    μ (N.isSmoothForm_pullback_one (lgManifold n) j.map _ (isSmoothForm_lambdaPotentialForm hφ))
    (isSymplecticOn_potential_W_level hφ hc hU hlower hupper I w ha j himage)
    (potential_fiber_defining_outward hφ j A hpos)
  simpa only [potential_W_levelOutwardDomain, sub_eq_zero] using h

include hpos in
/-- The actual full fiber flow enters the literal truncation in negative time. -/
theorem potential_W_level_absorbs_outward_sublevel (x : N.Point) :
    ∃ T : ℝ, 0 ≤ T ∧ η ((P).completeFlow.flow (-T) x) ≤ A := by
  apply (P).completeFlow.exists_nonneg_time_scalar_le η
    (contMDiff_potential_W_level_value hφ j) (P).smooth_field
    (isCompact_potential_W_level_sublevel hφ hEnd1 hEnds hhom hc hlower hL hend I w j himage) A
  exact hpos

/-- The actual intrinsic flow and negative entry construct a native
completion of this full literal potential truncation. -/
def potential_W_levelOutwardCompletion : Completion D :=
  FlowAbsorptionMarking.completionOfSublevelAbsorption D P η
    (contMDiff_potential_W_level_value hφ j)
    (potential_W_levelOutwardDomain_frontier hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)
    hpos (potential_W_levelOutwardDomain_carrier hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)
    (potential_W_level_absorbs_outward_sublevel hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)

/-- The flow-built completion is marked onto the whole actual full fiber. -/
def potential_W_levelOutwardInclusionMarking :
    InclusionMarking (potential_W_levelOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)
      (P).toCompleteLiouvilleManifold (fun x => x.val) where
  equiv := Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 2)) N.Point ∞
  primitive := N.pullback_id μ
  inclusion := fun _ => rfl
  flow_induced := fun _ _ => rfl

/-- Every chosen completion of this same literal truncation has the actual
full-fiber marking, transported from the constructed flow completion. -/
def potential_W_levelOutwardInclusionMarkingOfCompletion (C : Completion D) :
    InclusionMarking C (P).toCompleteLiouvilleManifold (fun x => x.val) :=
  C.transportInclusionMarking
    (potential_W_levelOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)
    (P).toCompleteLiouvilleManifold (fun x => x.val)
    (potential_W_levelOutwardInclusionMarking hφ hEnd1 hEnds hhom hc hU hlower hupper hL hend I w ha j himage A hpos)

/-- No component is selected: the embedded compact carrier equals the
full literal potential truncation of the original complex level. -/
theorem potential_W_levelOutwardDomain_image :
    j.map '' (D).domain.carrier = {y | W I y = w ∧ φ y.1 ≤ A} := by
  rw [potential_W_levelOutwardDomain_carrier]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hy : j.map x ∈ range j.map := ⟨x, rfl⟩
    rw [himage] at hy
    exact ⟨hy, hx⟩
  · rintro ⟨hW, hφ⟩
    have hy : y ∈ range j.map := by rw [himage]; exact hW
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, hφ, rfl⟩

/-- Actual Laurent surjectivity and negative entry prove the full compact
fiber truncation is nonempty, without choosing a component. -/
theorem potential_W_levelOutwardDomain_nonempty : (D).domain.carrier.Nonempty := by
  obtain ⟨y, hy⟩ := I.W_surjective w
  have hyrange : y ∈ range j.map := by rw [himage]; exact hy
  obtain ⟨x, rfl⟩ := hyrange
  obtain ⟨T, _, hentry⟩ := potential_W_level_absorbs_outward_sublevel hφ hEnd1 hEnds hhom
    hc hU hlower hupper hL hend I w ha j himage A hpos x
  refine ⟨(P).completeFlow.flow (-T) x, ?_⟩
  rw [potential_W_levelOutwardDomain_carrier]
  exact hentry

include hEnd1 hEnds hhom hc hU hlower hupper hL hend in
/-- Uniform actual completion markings for every sufficiently large
truncation of every far full fiber on the prescribed coefficient path.
The regularity and outwardness witnesses are proved conclusions. The
chosen potential, whole fiber realization, truncation radius, and arbitrary
completion all remain the supplied ones. -/
theorem ToricInput.coefficientPath_exists_potentialFiber_markings (Aamb : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, β₀ ≤ β → Aamb ≤ F ^ 2 * β ^ 2 / 2 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, B < ‖w‖ → ‖w‖ ≤ Real.exp β →
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
        (himage : range j.map = {y | W (I.alongCoefficientPath t) y = w})
        (A : ℝ), F ^ 2 * β ^ 2 / 2 ≤ A →
      ∃ ha : ∀ y, W (I.alongCoefficientPath t) y = w → 0 < a (I.alongCoefficientPath t) y,
      ∃ hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
        0 < N.scalarDerivative (fun y : N.Point => φ (j.map y).1) x
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x),
      let Dfib := potential_W_levelOutwardDomain hφ hEnd1 hEnds hhom hc hU hlower hupper
        hL hend (I.alongCoefficientPath t) w ha j himage A hpos
      let Pfib := potential_W_levelCompletePrimitive hφ hEnd1 hEnds hhom hc hU hlower hupper
        hL hend (I.alongCoefficientPath t) w ha j himage
      Dfib.domain.carrier.Nonempty ∧
        j.map '' Dfib.domain.carrier = {y | W (I.alongCoefficientPath t) y = w ∧ φ y.1 ≤ A} ∧
        Nonempty (Completion Dfib) ∧ ∀ C : Completion Dfib,
          Nonempty (InclusionMarking C Pfib.toCompleteLiouvilleManifold (fun x => x.val)) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨B, hB, hregular⟩ := I.coefficientPath_a_pos_of_large_value
  obtain ⟨F, hF, β₀, hβ₀, hout⟩ := I.coefficientPath_potentialPath_intrinsic_fiber_outward
    (hφ.comp e.contDiff) (hEnd1.comp e.contDiff)
    (fun u hu => (hEnds (e u) (by simpa [e] using hu)).comp u e.contDiff.contDiffAt)
    (fun r hr u => by simpa only [Function.comp_apply, map_smul] using hhom r hr (e u))
    hc hlower hupper hL (fun u hu => by simpa [e] using hend (e u) hu) Aamb
  refine ⟨B, hB, F, hF, β₀, hβ₀, ?_⟩
  intro β hβ
  refine ⟨(hout β hβ).1, ?_⟩
  intro t ht w hfar hw N j himage A hA
  have ha : ∀ y, W (I.alongCoefficientPath t) y = w → 0 < a (I.alongCoefficientPath t) y := by
    intro y hy
    exact hregular t ht y (by rwa [hy])
  have hψ : potentialPath (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2 / 2)
      (φ ∘ e) 1 ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm = φ := by
    ext u
    simp only [potentialPath_one, Function.comp_apply]
    exact congrArg φ (e.apply_symm_apply u)
  have hpos : ∀ x : N.Point, A ≤ φ (j.map x).1 →
      0 < N.scalarDerivative (fun y : N.Point => φ (j.map y).1) x
        (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)) x) := by
    intro x hx
    have hW : ‖W (I.alongCoefficientPath t) (j.map x)‖ ≤ Real.exp β := by
      have hval : W (I.alongCoefficientPath t) (j.map x) = w := by
        have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
        rwa [himage] at hx
      rwa [hval]
    have h := (hout β hβ).2 t ht 1 (by constructor <;> norm_num) (2 * n - 2) N j x
      (potential_W_levelEmbedding_tangent_range (I.alongCoefficientPath t) w ha j himage x)
      (by simpa only [hψ] using hA.trans hx) hW
    have hp := h.2
    change 0 < N.scalarDerivative
      ((fun y => (potentialPath (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2 / 2)
        (φ ∘ e) 1 ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) y.1) ∘ j.map) x
      (N.liouvilleVector (N.pullback (lgManifold n) j.map
        (lambdaPotentialForm (potentialPath (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2 / 2)
          (φ ∘ e) 1 ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm))) x) at hp
    rw [hψ] at hp
    exact hp
  refine ⟨ha, hpos, ?_, ?_, ?_, ?_⟩
  · exact potential_W_levelOutwardDomain_nonempty hφ hEnd1 hEnds hhom hc hU hlower hupper hL
      hend (I.alongCoefficientPath t) w ha j himage A hpos
  · exact potential_W_levelOutwardDomain_image hφ hEnd1 hEnds hhom hc hU hlower hupper hL
      hend (I.alongCoefficientPath t) w ha j himage A hpos
  · exact ⟨potential_W_levelOutwardCompletion hφ hEnd1 hEnds hhom hc hU hlower hupper hL
      hend (I.alongCoefficientPath t) w ha j himage A hpos⟩
  · intro C
    exact ⟨potential_W_levelOutwardInclusionMarkingOfCompletion hφ hEnd1 hEnds hhom hc hU
      hlower hupper hL hend (I.alongCoefficientPath t) w ha j himage A hpos C⟩

end Domain
end FsFltz.Geometry
