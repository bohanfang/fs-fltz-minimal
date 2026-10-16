import FsFltz.Analysis.FiniteSupportGrowth
import FsFltz.ToricPolytopeFaces
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Strict maximizer regions meet every ball at their incident points

Source: `geometric-part-fsf-proof.tex`, `lem:potential`, lines 606–613.
The positivity of a maximizer's convolution coefficient follows because
every ball at that maximizer meets its open strict-maximizer region in
positive volume. The exposing direction here is derived from the actual
input's extreme-point equality and its proved polytope face API.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology
open MeasureTheory

variable {n : ℕ}

/-- The directions in which the prescribed actual input vertex uniquely
maximizes the support pairing. -/
def strictMaximizerRegion (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) : Set (RealSpace n) :=
  {z | ∀ w : {w : Lattice n // w ∈ I.vertices},
    w ≠ v → pairing w.val z < pairing v.val z}

/-- Every actual vertex admits a direction which strictly exposes it.
This uses the equality with the polytope's extreme points, rather than
assuming that every coefficient exponent is exposed. -/
theorem ToricInput.exists_strictMaximizer (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) :
    (strictMaximizerRegion I v).Nonempty := by
  have hvext : latticeReal v.val ∈ (latticePolytope I.vertices).extremePoints ℝ := by
    rw [← I.vertices_exact]
    exact ⟨v.val, v.property, rfl⟩
  have hE := I.isExposed_of_convex_isExtreme (convex_singleton (latticeReal v.val))
    (isExtreme_singleton.mpr hvext)
  obtain ⟨L, hL⟩ := hE (Set.singleton_nonempty _)
  have hvmax := ((Set.ext_iff.mp hL _).mp (Set.mem_singleton _)).2
  let d : RealSpace n := fun j => L ((Pi.basisFun ℝ (Fin n)) j)
  have hpair (w : Lattice n) : L (latticeReal w) = pairing w d := by
    rw [← (Pi.basisFun ℝ (Fin n)).sum_repr (latticeReal w)]
    simp only [map_sum, map_smul, Pi.basisFun_repr, latticeReal, pairing, d, smul_eq_mul]
  refine ⟨d, ?_⟩
  intro w hw
  have hwQ : latticeReal w.val ∈ latticePolytope I.vertices :=
    subset_convexHull ℝ _ ⟨w.val, w.property, rfl⟩
  have hle : L (latticeReal w.val) ≤ L (latticeReal v.val) := hvmax _ hwQ
  have hne : L (latticeReal w.val) ≠ L (latticeReal v.val) := by
    intro he
    have hwmax : ∀ x ∈ latticePolytope I.vertices, L x ≤ L (latticeReal w.val) := by
      intro x hx
      rw [he]
      exact hvmax x hx
    have hwv : latticeReal w.val = latticeReal v.val :=
      (Set.ext_iff.mp hL _).mpr ⟨hwQ, hwmax⟩
    exact hw (Subtype.ext (latticeReal_injective hwv))
  simpa only [hpair] using lt_of_le_of_ne hle hne

/-- The strict-maximizer region is a finite intersection of open linear
half-spaces in the original dual coordinate space. -/
theorem isOpen_strictMaximizerRegion (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) : IsOpen (strictMaximizerRegion I v) := by
  classical
  unfold strictMaximizerRegion
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (by unfold pairing; fun_prop) (by unfold pairing; fun_prop)

/-- Adding any positive multiple of a strict exposing direction to a
direction at which `v` maximizes makes `v` the unique maximizer. -/
theorem strictMaximizerRegion_add_smul (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {y d : RealSpace n}
    (hy : pairing v.val y = supportHeight I y)
    (hd : d ∈ strictMaximizerRegion I v) {t : ℝ} (ht : 0 < t) :
    y + t • d ∈ strictMaximizerRegion I v := by
  intro w hw
  have hwy : pairing w.val y ≤ pairing v.val y := by
    rw [hy]
    exact I.pairing_le_supportHeight y w
  have hwd := hd w hw
  have hpair (a : Lattice n) : pairing a (y + t • d) = pairing a y + t * pairing a d := by
    simp [pairing, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
  rw [hpair, hpair]
  nlinarith

/-- Every ball at an incident maximizer meets its strict-maximizer region.
The witness is a small positive perturbation in a strictly exposing direction. -/
theorem ToricInput.ball_inter_strictMaximizerRegion_nonempty (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {y : RealSpace n}
    (hy : pairing v.val y = supportHeight I y) {ε : ℝ} (hε : 0 < ε) :
    (Metric.ball y ε ∩ strictMaximizerRegion I v).Nonempty := by
  obtain ⟨d, hd⟩ := I.exists_strictMaximizer v
  have hcont : ContinuousAt (fun t : ℝ => y + t • d) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, y + t • d ∈ Metric.ball y ε :=
    hcont.eventually_mem (by simpa using Metric.ball_mem_nhds y hε)
  obtain ⟨t, ht, htball⟩ := hev.exists_gt
  exact ⟨y + t • d, htball, strictMaximizerRegion_add_smul I v hy hd ht⟩

/-- The incident strict-maximizer part of every ball has strictly positive
native volume, supplying the geometric part of the positive kernel weight. -/
theorem ToricInput.volume_ball_inter_strictMaximizerRegion_pos (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {y : RealSpace n}
    (hy : pairing v.val y = supportHeight I y) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (Metric.ball y ε ∩ strictMaximizerRegion I v) := by
  exact (Metric.isOpen_ball.inter (isOpen_strictMaximizerRegion I v)).measure_pos volume
    (I.ball_inter_strictMaximizerRegion_nonempty v hy hε)

/-- The same nonempty open set in the convolution's displacement
coordinates, where the kernel is strictly positive inside the zero ball. -/
theorem ToricInput.ball_zero_inter_sub_strictMaximizerRegion_nonempty (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {y : RealSpace n}
    (hy : pairing v.val y = supportHeight I y) {ε : ℝ} (hε : 0 < ε) :
    (Metric.ball 0 ε ∩ {t | y - t ∈ strictMaximizerRegion I v}).Nonempty := by
  obtain ⟨z, hzball, hz⟩ := I.ball_inter_strictMaximizerRegion_nonempty v hy hε
  refine ⟨y - z, ?_, ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hzball
  · change y - (y - z) ∈ strictMaximizerRegion I v
    simpa only [sub_sub_cancel] using hz

/-- Positive native volume in exactly the convolution displacement set
used to prove strict positivity of an incident vertex coefficient. -/
theorem ToricInput.volume_ball_zero_inter_sub_strictMaximizerRegion_pos (I : ToricInput n)
    (v : {v : Lattice n // v ∈ I.vertices}) {y : RealSpace n}
    (hy : pairing v.val y = supportHeight I y) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (Metric.ball 0 ε ∩ {t | y - t ∈ strictMaximizerRegion I v}) := by
  have hopen : IsOpen {t : RealSpace n | y - t ∈ strictMaximizerRegion I v} :=
    (isOpen_strictMaximizerRegion I v).preimage (continuous_const.sub continuous_id)
  exact (Metric.isOpen_ball.inter hopen).measure_pos volume
    (I.ball_zero_inter_sub_strictMaximizerRegion_nonempty v hy hε)

end FsFltz
