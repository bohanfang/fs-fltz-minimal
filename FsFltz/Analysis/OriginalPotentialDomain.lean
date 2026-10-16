import FsFltz.Analysis.OriginalCompleteFlow
import FsFltz.Analysis.OriginalLiouvilleIdentities
import FsFltz.Analysis.OriginalFlowAbsorption
import FsFltz.Compactness
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual original potential sublevel domains

Source: `geometric-part-fsf-proof.tex`, `lem:originalends`, lines 813–818,
and `geoemtric-part-fsf.tex`, `thm:target`, G1, lines 358–360.
The compact carrier is the literal quadratic sublevel in the fixed quotient
ambient. Its native boundary is a scaled Euclidean sphere times the angle
torus. The defining function is `phi0 - A`, with strict outwardness supplied
by the original field identity and an ambient end bound.
-/

noncomputable section
open scoped BigOperators ContDiff Manifold
open Set Topology Function Metric

namespace FsFltz.Geometry
open SmoothManifold

namespace OriginalPotentialDomain

abbrev BoundaryPoint (n : ℕ) := sphere (0 : Model n) 1 × Torus n
abbrev BoundaryCoordinates (n : ℕ) := Model (n - 1) × TorusCoordinates n

private def boundaryEuclideanEquiv (n : ℕ) (hn : 1 ≤ n) :
    BoundaryCoordinates n ≃L[ℝ] Model (2 * n - 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [BoundaryCoordinates, Model, TorusCoordinates, AngleModel,
      Module.finrank_prod, Module.finrank_pi_fintype, finrank_euclideanSpace,
      Fintype.card_fin]
    omega)

private theorem sphereDimension (n : ℕ) (hn : 1 ≤ n) :
    Fact (Module.finrank ℝ (Model n) = (n - 1) + 1) :=
  ⟨by simp only [Model, finrank_euclideanSpace, Fintype.card_fin]; omega⟩

@[instance_reducible] private def boundaryNativeCharts (n : ℕ) (hn : 1 ≤ n) :
    ChartedSpace (BoundaryCoordinates n) (BoundaryPoint n) := by
  letI := sphereDimension n hn
  exact inferInstanceAs (ChartedSpace (ModelProd (Model (n - 1)) (TorusCoordinates n))
    (BoundaryPoint n))

private theorem boundaryNativeSmooth (n : ℕ) (hn : 1 ≤ n) :
    letI := boundaryNativeCharts n hn
    IsManifold 𝓘(ℝ, BoundaryCoordinates n) ∞ (BoundaryPoint n) := by
  let := sphereDimension n hn
  let := boundaryNativeCharts n hn
  let : IsManifold 𝓘(ℝ, Model (n - 1)) ∞ (sphere (0 : Model n) 1) :=
    IsManifold.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)
  change IsManifold 𝓘(ℝ, Model (n - 1) × TorusCoordinates n) ∞ (BoundaryPoint n)
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod _ _

/-- The native sphere-times-torus boundary, recharted to the prescribed
Euclidean dimension. Rank one uses the native zero-dimensional sphere. -/
def boundaryManifold (n : ℕ) (hn : 1 ≤ n) : SmoothManifold (2 * n - 1) := by
  letI := sphereDimension n hn
  letI := boundaryNativeCharts n hn
  letI := boundaryNativeSmooth n hn
  exact
    { Point := BoundaryPoint n
      topology := inferInstance
      charts := linearRechart (M := BoundaryPoint n) (boundaryEuclideanEquiv n hn)
      hausdorff := inferInstance
      secondCountable := inferInstance
      smooth := linearRechart_isManifold (M := BoundaryPoint n) (boundaryEuclideanEquiv n hn) }

/-- Euclidean coordinates scaled to the prescribed quadratic level. -/
def radialCoordinates (n : ℕ) {A : ℝ} (hA : 0 < A) : Model n ≃L[ℝ] RealSpace n :=
  (Units.mk0 (Real.sqrt (2 * A)) (by positivity)) • EuclideanSpace.equiv (Fin n) ℝ

theorem radialCoordinates_apply (n : ℕ) {A : ℝ} (hA : 0 < A) (u : Model n) :
    radialCoordinates n hA u = Real.sqrt (2 * A) • u.ofLp := by
  simp only [radialCoordinates, ContinuousLinearEquiv.smul_apply,
    EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
  rfl

private theorem radialCoordinates_normSq (n : ℕ) {A : ℝ} (hA : 0 < A) (u : Model n) :
    realSquaredNorm (radialCoordinates n hA u) = 2 * A * ‖u‖ ^ 2 := by
  rw [radialCoordinates_apply, EuclideanSpace.norm_sq_eq]
  simp only [realSquaredNorm, Pi.smul_apply, smul_eq_mul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 2 * A)]
  exact (Finset.mul_sum _ _ _).symm

/-- Literal boundary inclusion into the fixed quotient ambient. -/
def boundaryMap (n : ℕ) {A : ℝ} (hA : 0 < A) : BoundaryPoint n → LGSpace n :=
  fun x => (radialCoordinates n hA x.1.val, x.2)

theorem boundaryMap_phi0 (n : ℕ) {A : ℝ} (hA : 0 < A) (x : BoundaryPoint n) :
    phi0 (boundaryMap n hA x) = A := by
  have hx : ‖x.1.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.1.property
  change realSquaredNorm (radialCoordinates n hA x.1.val) / 2 = A
  rw [radialCoordinates_normSq, hx]
  ring

theorem isEmbedding_boundaryMap (n : ℕ) {A : ℝ} (hA : 0 < A) :
    Topology.IsEmbedding (boundaryMap n hA) := by
  exact ((radialCoordinates n hA).toHomeomorph.isEmbedding.prodMap
    (Homeomorph.refl (Torus n)).isEmbedding).comp
      (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id)

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_boundaryMap (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    letI : ChartedSpace (Model (2 * n - 1)) (BoundaryPoint n) := (boundaryManifold n hn).charts
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    ContMDiff 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, Model (2 * n)) ∞
      (boundaryMap n hA : BoundaryPoint n → (lgManifold n).Point) := by
  let := sphereDimension n hn
  let := boundaryNativeCharts n hn
  let := boundaryNativeSmooth n hn
  let : ChartedSpace (Model (2 * n - 1)) (BoundaryPoint n) := (boundaryManifold n hn).charts
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hcoe : ContMDiff 𝓘(ℝ, BoundaryCoordinates n) 𝓘(ℝ, LGCoordinates n) ∞
      (boundaryMap n hA) := by
    change ContMDiff 𝓘(ℝ, Model (n - 1) × TorusCoordinates n)
      𝓘(ℝ, RealSpace n × TorusCoordinates n) ∞ (boundaryMap n hA)
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact ((radialCoordinates n hA).contDiff.contMDiff.comp
      (contMDiff_coe_sphere (E := Model n) (n := n - 1))).prodMap contMDiff_id
  exact (contMDiff_linearRechart_id (M := LGSpace n) (lgEuclideanEquiv n)).comp
    (hcoe.comp (contMDiff_linearRechart_id_symm (M := BoundaryPoint n)
      (boundaryEuclideanEquiv n hn)))

set_option backward.isDefEq.respectTransparency false in
theorem injective_mfderiv_boundaryMap (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A)
    (x : (boundaryManifold n hn).Point) :
    letI : ChartedSpace (Model (2 * n - 1)) (BoundaryPoint n) := (boundaryManifold n hn).charts
    letI : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
    Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 1)) 𝓘(ℝ, Model (2 * n))
      (boundaryMap n hA : (boundaryManifold n hn).Point → (lgManifold n).Point) x) := by
  let := sphereDimension n hn
  let := boundaryNativeCharts n hn
  let := boundaryNativeSmooth n hn
  let : ChartedSpace (Model (2 * n - 1)) (BoundaryPoint n) := (boundaryManifold n hn).charts
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hnative : Function.Injective (mfderiv 𝓘(ℝ, BoundaryCoordinates n)
      𝓘(ℝ, LGCoordinates n) (boundaryMap n hA) x) := by
    change Function.Injective (mfderiv 𝓘(ℝ, Model (n - 1) × TorusCoordinates n)
      𝓘(ℝ, RealSpace n × TorusCoordinates n) (boundaryMap n hA) x)
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    change Function.Injective (mfderiv _ _
      (Prod.map (radialCoordinates n hA ∘ Subtype.val) id) x)
    have hs := (contMDiff_coe_sphere (E := Model n) (n := n - 1)
      (m := ∞)).mdifferentiable (by simp)
    have hr := ((radialCoordinates n hA).contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
    rw [mfderiv_prodMap ((hr.comp hs) x.1) mdifferentiableAt_id,
      mfderiv_comp x.1 (hr x.1.val) (hs x.1), mfderiv_eq_fderiv,
      (radialCoordinates n hA).fderiv, mfderiv_id]
    have hsInj : Function.Injective (mfderiv 𝓘(ℝ, Model (n - 1)) 𝓘(ℝ, Model n)
        (Subtype.val : sphere (0 : Model n) 1 → Model n) x.1) := by
      convert! injective_mvfderiv_subtypeVal_sphere x.1
    intro u v huv
    change (radialCoordinates n hA (mfderiv 𝓘(ℝ, Model (n - 1)) 𝓘(ℝ, Model n)
      Subtype.val x.1 u.1), u.2) =
      (radialCoordinates n hA (mfderiv 𝓘(ℝ, Model (n - 1)) 𝓘(ℝ, Model n)
      Subtype.val x.1 v.1), v.2) at huv
    apply Prod.ext
    · apply hsInj
      apply (radialCoordinates n hA).injective
      exact congrArg Prod.fst huv
    · have hv := congrArg Prod.snd huv
      exact hv
  let S := (linearRechartDiffeomorph (M := BoundaryPoint n)
    (boundaryEuclideanEquiv n hn)).symm
  let T := linearRechartDiffeomorph (M := LGSpace n) (lgEuclideanEquiv n)
  have hnativeSmooth : ContMDiff 𝓘(ℝ, BoundaryCoordinates n) 𝓘(ℝ, LGCoordinates n) ∞
      (boundaryMap n hA) := by
    change ContMDiff 𝓘(ℝ, Model (n - 1) × TorusCoordinates n)
      𝓘(ℝ, RealSpace n × TorusCoordinates n) ∞ (boundaryMap n hA)
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact ((radialCoordinates n hA).contDiff.contMDiff.comp
      (contMDiff_coe_sphere (E := Model n) (n := n - 1))).prodMap contMDiff_id
  change Function.Injective (mfderiv _ _ (T ∘ (boundaryMap n hA ∘ S)) x)
  rw [mfderiv_comp x (T.contMDiff.mdifferentiable (by simp) _)
    ((hnativeSmooth.comp S.contMDiff).mdifferentiable (by simp) x),
    mfderiv_comp x (hnativeSmooth.mdifferentiable (by simp) _)
      (S.contMDiff.mdifferentiable (by simp) x)]
  exact ((T.mfderivToContinuousLinearEquiv (by simp) _).injective.comp hnative).comp
    (S.mfderivToContinuousLinearEquiv (by simp) x).injective

/-- Actual native smooth boundary embedding. -/
def boundaryEmbedding (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    (boundaryManifold n hn).SmoothEmbedding (lgManifold n) where
  map := ⟨boundaryMap n hA, contMDiff_boundaryMap n hn hA⟩
  embedding := isEmbedding_boundaryMap n hA
  immersion := injective_mfderiv_boundaryMap n hn hA

private def radialHomeomorph (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (Model n × Torus n) ≃ₜ LGSpace n :=
  (radialCoordinates n hA).toHomeomorph.prodCongr (Homeomorph.refl (Torus n))

private theorem phi0_radialHomeomorph (n : ℕ) {A : ℝ} (hA : 0 < A)
    (x : Model n × Torus n) :
    phi0 (radialHomeomorph n hA x) = A * ‖x.1‖ ^ 2 := by
  change realSquaredNorm (radialCoordinates n hA x.1) / 2 = _
  rw [radialCoordinates_normSq]
  ring

private theorem image_closedBall (n : ℕ) {A : ℝ} (hA : 0 < A) :
    radialHomeomorph n hA '' (closedBall (0 : Model n) 1 ×ˢ (univ : Set (Torus n))) =
      {y : LGSpace n | phi0 y ≤ A} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx.1
    change phi0 (radialHomeomorph n hA x) ≤ A
    rw [phi0_radialHomeomorph]
    have hsq : ‖x.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x.1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hA.le
  · intro hy
    let x := (radialHomeomorph n hA).symm y
    have hφ : A * ‖x.1‖ ^ 2 ≤ A := by
      rw [← phi0_radialHomeomorph n hA x, (radialHomeomorph n hA).apply_symm_apply]
      exact hy
    refine ⟨x, ⟨?_, mem_univ _⟩, (radialHomeomorph n hA).apply_symm_apply y⟩
    rw [mem_closedBall, dist_zero_right]
    have hsq : ‖x.1‖ ^ 2 ≤ 1 := (mul_le_mul_iff_right₀ hA).mp (by simpa using hφ)
    nlinarith [norm_nonneg x.1]

private theorem range_boundaryMap_image_sphere (n : ℕ) {A : ℝ} (hA : 0 < A) :
    range (boundaryMap n hA) = radialHomeomorph n hA ''
      (sphere (0 : Model n) 1 ×ˢ (univ : Set (Torus n))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x.1.val, x.2), ⟨x.1.property, mem_univ _⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(⟨x.1, hx.1⟩, x.2), rfl⟩

theorem range_boundaryMap (n : ℕ) {A : ℝ} (hA : 0 < A) :
    range (boundaryMap n hA) = {y : LGSpace n | phi0 y = A} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact boundaryMap_phi0 n hA x
  · intro hy
    let x := (radialHomeomorph n hA).symm y
    have hφ : A * ‖x.1‖ ^ 2 = A := by
      rw [← phi0_radialHomeomorph n hA x, (radialHomeomorph n hA).apply_symm_apply]
      exact hy
    have hsq : ‖x.1‖ ^ 2 = 1 := mul_left_cancel₀ hA.ne' (by simpa using hφ)
    have hn : ‖x.1‖ = 1 := by nlinarith [norm_nonneg x.1]
    refine ⟨(⟨x.1, ?_⟩, x.2), ?_⟩
    · simpa only [mem_sphere, dist_zero_right] using hn
    · exact (radialHomeomorph n hA).apply_symm_apply y

end OriginalPotentialDomain

/-- The actual quadratic sublevel has precisely its level set as frontier. -/
theorem frontier_phi0_sublevel (n : ℕ) {A : ℝ} (hA : 0 < A) :
    frontier {y : LGSpace n | phi0 y ≤ A} = {y : LGSpace n | phi0 y = A} := by
  rw [← OriginalPotentialDomain.image_closedBall n hA,
    ← (OriginalPotentialDomain.radialHomeomorph n hA).image_frontier,
    frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero,
    ← OriginalPotentialDomain.range_boundaryMap_image_sphere,
    OriginalPotentialDomain.range_boundaryMap]

namespace OriginalPotentialDomain

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_phi0_sub_const (n : ℕ) (A : ℝ) (x : (lgManifold n).Point) :
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun y : (lgManifold n).Point => phi0 y - A) x =
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) (fun y : (lgManifold n).Point => phi0 y) x := by
  change mfderiv _ _ ((fun y : (lgManifold n).Point => phi0 y) - fun _ => A) x = _
  rw [mfderiv_sub (contMDiff_phi0.mdifferentiable (by simp) x) mdifferentiableAt_const,
    mfderiv_const, sub_zero]

set_option backward.isDefEq.respectTransparency false in
private def definingFunction {n : ℕ} (I : ToricInput n) {K Aamb A : ℝ}
    (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb) (hA : Aamb < A)
    (x : (lgManifold n).Point) (hx : x ∈ frontier {y : LGSpace n | phi0 y ≤ A}) :
    BoundaryDefiningFunction (lgManifold n) {y : LGSpace n | phi0 y ≤ A} x where
  neighbourhood := univ
  open_neighbourhood := isOpen_univ
  mem_neighbourhood := mem_univ _
  rho := fun y => phi0 y - A
  smooth_rho := (ContMDiff.sub_const A contMDiff_phi0).contMDiffOn
  sublevel := fun y _ => by change phi0 y ≤ A ↔ phi0 y - A ≤ 0; exact sub_nonpos.symm
  zero_level := by
    intro y _
    change y ∈ frontier {z : LGSpace n | phi0 z ≤ A} ↔ phi0 y - A = 0
    rw [frontier_phi0_sublevel n (hamb.1.trans hA)]
    change phi0 y = A ↔ phi0 y - A = 0
    exact sub_eq_zero.symm
  regular := by
    have hlevel : phi0 x = A := by
      rwa [frontier_phi0_sublevel n (hamb.1.trans hA)] at hx
    have hpos := scalarDerivative_phi0_originalLiouville_pos I hK hamb x
      (by rw [hlevel]; exact hA.le)
    rw [mfderiv_phi0_sub_const]
    intro hz
    unfold scalarDerivative at hpos
    rw [hz, zero_apply] at hpos
    exact (lt_irrefl 0) hpos

end OriginalPotentialDomain

set_option backward.isDefEq.respectTransparency false in
/-- The literal large quadratic sublevel in the fixed original ambient,
with its concrete scaled-sphere-times-torus native boundary. -/
def originalPotentialCompactDomain {n : ℕ} (I : ToricInput n) {K Aamb A : ℝ}
    (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb) (hA : Aamb < A) :
    CompactDomain (2 * n) where
  extension := lgManifold n
  carrier := {y : LGSpace n | phi0 y ≤ A}
  compact := isCompact_phi0_sublevel A (hamb.1.trans hA).le
  defining := OriginalPotentialDomain.definingFunction I hK hamb hA
  boundary := OriginalPotentialDomain.boundaryManifold n I.positive_rank
  boundaryInclusion := OriginalPotentialDomain.boundaryEmbedding n I.positive_rank (hamb.1.trans hA)
  boundary_range := by
    change range (OriginalPotentialDomain.boundaryMap n (hamb.1.trans hA)) =
      frontier {y : LGSpace n | phi0 y ≤ A}
    rw [OriginalPotentialDomain.range_boundaryMap, frontier_phi0_sublevel n (hamb.1.trans hA)]
  zero_boundary := by intro hdim; have hn := I.positive_rank; omega

/-- The native frontier of the actual quadratic compact domain is exactly
the prescribed potential level. -/
theorem originalPotentialCompactDomain_frontier {n : ℕ} (I : ToricInput n)
    {K Aamb A : ℝ} (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb) (hA : Aamb < A) :
    frontier (originalPotentialCompactDomain I hK hamb hA).carrier =
      {y : (lgManifold n).Point | phi0 y = A} :=
  frontier_phi0_sublevel n (hamb.1.trans hA)

set_option backward.isDefEq.respectTransparency false in
/-- The original primitive and original field restricted to the actual
quadratic compact domain. Its boundary is strictly outward. -/
def originalPotentialLiouvilleDomain {n : ℕ} (I : ToricInput n) {K Aamb A : ℝ}
    (hK : 0 ≤ K) (hamb : AmbientEndBound I Aamb) (hA : Aamb < A) :
    LiouvilleDomain (2 * n) where
  domain := originalPotentialCompactDomain I hK hamb hA
  liouville :=
    { primitive := lambdaKForm I K
      smooth_primitive := (originalCompletePrimitive I hK).smooth_primitive
      symplectic := by
        have h := (originalCompletePrimitive I hK).symplectic
        exact ⟨h.1, fun x _ => h.2.1 x (mem_univ _), fun x _ => h.2.2 x (mem_univ _)⟩
      field := (lgManifold n).liouvilleVector (lambdaKForm I K)
      smooth_field := (originalCompletePrimitive I hK).smooth_field
      contraction := fun x _ v => (originalCompletePrimitive I hK).contraction x v
      outward := by
        intro x hx
        have hlevel : phi0 x = A := by
          rwa [originalPotentialCompactDomain_frontier I hK hamb hA] at hx
        change (0 : ℝ) < mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ)
          (fun y : (lgManifold n).Point => phi0 y - A) x
            ((lgManifold n).liouvilleVector (lambdaKForm I K) x)
        rw [OriginalPotentialDomain.mfderiv_phi0_sub_const]
        exact scalarDerivative_phi0_originalLiouville_pos I hK hamb x
          (by rw [hlevel]; exact hA.le) }

end FsFltz.Geometry
