import FsFltz.Geometry.IntrinsicLiouvilleCoordinates
import FsFltz.Geometry.IntrinsicLiouvilleOutward
import FsFltz.Geometry.IntrinsicLiouvilleCollar
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The sign of an arbitrary local boundary defining function

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–130, `def:pair`, lines 132–160, and `sec:lean`, lines 783–814.
The source uses the sublevel convention `rho ≤ 0`, whereas native boundary
charts have nonnegative first coordinate. The negative proportionality of
their differentials is proved from the local sublevel inequality and
regularity; it is not supplied as an outwardness hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ}

private theorem halfSpace_mem_posTangentCone
    {a v : Model (k + 1)} (ha : a 0 = 0) (hv : 0 ≤ v 0) :
    v ∈ posTangentConeAt {y : Model (k + 1) | 0 ≤ y 0} a := by
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 ≤ (a + t • v) 0
  simpa [ha] using mul_nonneg (le_of_lt ht) hv

/-- At a regular local defining level, the differential is a strictly negative
multiple of the half-space normal covector. Only the local inequality on the
domain side is needed: it gives a local maximum and annihilates every
tangential direction by testing that direction and its negative. -/
theorem fderiv_eq_neg_normal_of_local_sublevel
    {rho : Model (k + 1) → ℝ} {a : Model (k + 1)}
    (ha : a 0 = 0) (hzero : rho a = 0)
    (hd : DifferentiableAt ℝ rho a)
    (hside : ∀ᶠ y in 𝓝 a, 0 ≤ y 0 → rho y ≤ 0)
    (hreg : fderiv ℝ rho a ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ ∀ v : Model (k + 1), fderiv ℝ rho a v = c * v 0 := by
  let L := fderiv ℝ rho a
  let n : Model (k + 1) := EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)
  have hn : n 0 = 1 := by simp [n]
  have hmax : IsLocalMaxOn rho {y : Model (k + 1) | 0 ≤ y 0} a := by
    filter_upwards [hside.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hys
    simpa [hzero] using hy hys
  have hnonpos (v : Model (k + 1)) (hv : 0 ≤ v 0) : L v ≤ 0 :=
    hmax.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt
      (halfSpace_mem_posTangentCone ha hv)
  have htangent (v : Model (k + 1)) (hv : v 0 = 0) : L v = 0 := by
    apply le_antisymm (hnonpos v (by simp [hv]))
    have h := hnonpos (-v) (by simp [hv])
    simpa using h
  have hformula (v : Model (k + 1)) : L v = L n * v 0 := by
    have ht := htangent (v - (v 0) • n) (by simp [hn])
    rw [map_sub, map_smul] at ht
    dsimp only [smul_eq_mul] at ht
    nlinarith
  have hc : L n < 0 := by
    apply lt_of_le_of_ne (hnonpos n (by simp [hn]))
    intro heq
    apply hreg
    ext v
    rw [hformula v, heq, zero_mul]
    rfl
  exact ⟨L n, hc, hformula⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- A genuine local scalar extension transports the actual native derivative
by the native chart differential. The agreement is needed only on the
half-space chart target. -/
theorem mfderiv_scalar_extension_apply
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (rho : M → ℝ) {beta : Model (k + 1) → ℝ}
    (hb : ContDiffAt ℝ ∞ beta (e.extend (𝓡∂ (k + 1)) x))
    (hag : beta =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) x)] (rho ∘ (e.extend (𝓡∂ (k + 1))).symm))
    (v : TangentSpace (𝓡∂ (k + 1)) x) :
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v =
      fderiv ℝ beta (e.extend (𝓡∂ (k + 1)) x) (chartTangentMap e x v) := by
  have hext : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (e.extend (𝓡∂ (k + 1))) x :=
    e.contMDiffAt_extend (IsManifold.subset_maximalAtlas he) hx
  have ht : Tendsto (e.extend (𝓡∂ (k + 1))) (𝓝 x)
      (𝓝[(e.extend (𝓡∂ (k + 1))).target] (e.extend (𝓡∂ (k + 1)) x)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hext.continuousAt, ?_⟩
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hy)
  have heq : rho =ᶠ[𝓝 x] beta ∘ e.extend (𝓡∂ (k + 1)) := by
    filter_upwards [ht.eventually hag, e.open_source.mem_nhds hx] with y hy hys
    simpa only [Function.comp_apply, (e.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [e.extend_source] using hys)] using hy.symm
  have hcomp := mfderiv_comp (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, Model (k + 1)))
    (I'' := 𝓘(ℝ, ℝ)) x (hb.contMDiffAt.mdifferentiableAt (by simp))
      (hext.mdifferentiableAt (by simp))
  have heqv := congrArg (fun A : TangentSpace (𝓡∂ (k + 1)) x →L[ℝ] ℝ => A v)
    (heq.mfderiv_eq (I := 𝓡∂ (k + 1)) (I' := 𝓘(ℝ, ℝ)))
  change mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v =
    mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (beta ∘ e.extend (𝓡∂ (k + 1))) x v at heqv
  rw [heqv]
  have hcompv := congrArg (fun A : TangentSpace (𝓡∂ (k + 1)) x →L[ℝ] ℝ => A v) hcomp
  rw [mfderiv_eq_fderiv] at hcompv
  exact hcompv

/-- Every regular source defining function has a strictly negative normal
differential in every native atlas chart. Smoothness across the boundary is
only a local scalar extension germ. The nonpositivity and zero-level
hypotheses are direct consequences of the source's `D = {rho ≤ 0}` convention.
No proportionality factor or sign equivalence is assumed. -/
theorem mfderiv_eq_neg_normal_of_localDefiningFunction
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint x)
    (rho : M → ℝ) (hzero : rho x = 0)
    (hside : ∀ᶠ y in 𝓝 x, rho y ≤ 0)
    (hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x ≠ 0)
    {beta : Model (k + 1) → ℝ}
    (hb : ContDiffAt ℝ ∞ beta (e.extend (𝓡∂ (k + 1)) x))
    (hag : beta =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) x)] (rho ∘ (e.extend (𝓡∂ (k + 1))).symm)) :
    ∃ c : ℝ, c < 0 ∧ ∀ v : TangentSpace (𝓡∂ (k + 1)) x,
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v =
        c * (show Model (k + 1) from chartTangentMap e x v) 0 := by
  let a := e.extend (𝓡∂ (k + 1)) x
  have hat : a ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source (by simpa only [e.extend_source] using hx)
  have ha : a 0 = 0 :=
    (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero he hx).mp hboundary
  have hza : beta a = 0 := by
    rw [hag.eq_of_nhdsWithin hat]
    simpa only [Function.comp_apply, (e.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [e.extend_source] using hx)] using hzero
  have hβside : ∀ᶠ y in 𝓝 a, 0 ≤ y 0 → beta y ≤ 0 := by
    obtain ⟨A, hAo, hA⟩ := isOpen_induced_iff.mp e.open_target
    have haA : a ∈ A := by
      have ht := e.map_source hx
      rw [← hA] at ht
      exact ht
    have htarget : ∀ᶠ y in 𝓝 a, 0 ≤ y 0 → y ∈ (e.extend (𝓡∂ (k + 1))).target := by
      filter_upwards [hAo.mem_nhds haA] with y hy hn
      let z : EuclideanHalfSpace (k + 1) := ⟨y, hn⟩
      have hz : (𝓡∂ (k + 1)).symm y = z := (𝓡∂ (k + 1)).left_inv z
      rw [OpenPartialHomeomorph.extend_target]
      refine ⟨?_, ⟨z, rfl⟩⟩
      change (𝓡∂ (k + 1)).symm y ∈ e.target
      rw [hz, ← hA]
      exact hy
    have hinv : Tendsto (e.extend (𝓡∂ (k + 1))).symm
        (𝓝[(e.extend (𝓡∂ (k + 1))).target] a) (𝓝 x) := by
      simpa only [a, (e.extend (𝓡∂ (k + 1))).left_inv
        (by simpa only [e.extend_source] using hx)] using
          (e.continuousOn_extend_symm (I := 𝓡∂ (k + 1)) a hat).tendsto
    have hp : ∀ᶠ y in 𝓝[(e.extend (𝓡∂ (k + 1))).target] a, beta y ≤ 0 := by
      filter_upwards [hag, hinv.eventually hside] with y hy hs
      exact hy ▸ hs
    filter_upwards [eventually_nhdsWithin_iff.mp hp, htarget] with y hy ht hn
    exact hy (ht hn)
  have hβreg : fderiv ℝ beta a ≠ 0 := by
    intro hz
    apply hreg
    ext v
    rw [mfderiv_scalar_extension_apply he hx rho hb hag v, hz]
    rfl
  obtain ⟨c, hc, hformula⟩ := fderiv_eq_neg_normal_of_local_sublevel ha hza
    (hb.differentiableAt (by simp)) hβside hβreg
  refine ⟨c, hc, fun v => ?_⟩
  rw [mfderiv_scalar_extension_apply he hx rho hb hag v]
  exact hformula (chartTangentMap e x v)

/-- Defining-function outwardness is equivalent to a negative native normal
coefficient, for an arbitrary regular smooth defining-function germ. -/
theorem outward_iff_negative_normal_of_localDefiningFunction
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint x)
    (rho : M → ℝ) (hzero : rho x = 0)
    (hside : ∀ᶠ y in 𝓝 x, rho y ≤ 0)
    (hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x ≠ 0)
    {beta : Model (k + 1) → ℝ}
    (hb : ContDiffAt ℝ ∞ beta (e.extend (𝓡∂ (k + 1)) x))
    (hag : beta =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) x)] (rho ∘ (e.extend (𝓡∂ (k + 1))).symm))
    (v : TangentSpace (𝓡∂ (k + 1)) x) :
    0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v) ↔
      (show Model (k + 1) from chartTangentMap e x v) 0 < 0 := by
  obtain ⟨c, hc, hformula⟩ := mfderiv_eq_neg_normal_of_localDefiningFunction
    he hx hboundary rho hzero hside hreg hb hag
  rw [hformula v]
  constructor
  · intro hpos
    by_contra hn
    have hn' : 0 ≤ (show Model (k + 1) from chartTangentMap e x v) 0 := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) hn')) hpos
  · exact mul_pos_of_neg_of_neg hc

/-- The source outward inequality yields precisely the positive native normal
coefficient of the negative field required by inward collar integration. -/
theorem inward_of_localDefiningFunction_outward
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint x)
    (rho : M → ℝ) (hzero : rho x = 0)
    (hside : ∀ᶠ y in 𝓝 x, rho y ≤ 0)
    (hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x ≠ 0)
    {beta : Model (k + 1) → ℝ}
    (hb : ContDiffAt ℝ ∞ beta (e.extend (𝓡∂ (k + 1)) x))
    (hag : beta =ᶠ[𝓝[(e.extend (𝓡∂ (k + 1))).target]
      (e.extend (𝓡∂ (k + 1)) x)] (rho ∘ (e.extend (𝓡∂ (k + 1))).symm))
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (hout : 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x (Z x))) :
    0 < (show Model (k + 1) from chartTangentMap e x (-Z x)) 0 := by
  have hn := (outward_iff_negative_normal_of_localDefiningFunction
    he hx hboundary rho hzero hside hreg hb hag (Z x)).mp hout
  have hn' : (show Model (k + 1) from chartTangentMap e x (-Z x)) =
      -(show Model (k + 1) from chartTangentMap e x (Z x)) := map_neg _ _
  rw [hn']
  exact neg_pos.mpr hn

variable [T2Space M] [CompactSpace (IntrinsicBoundary.Point k M)]

/-- A native Liouville primitive that is outward in the source's arbitrary
local defining functions constructs an actual uniform compact collar. Its
inward chart coefficient condition is discharged by the proved sign lemma.
The input contains scalar source extension germs and outward inequalities,
while the field, its extension coefficients, and the collar are derived. -/
theorem exists_uniform_collar_of_localDefiningFunction_outward
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (C : ℝ × IntrinsicBoundary.Point k M → M) (δ : ℝ), 0 < δ ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ C
        (Ico 0 δ ×ˢ univ) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C p.val) ∧
      (∀ y, C (0, y) = y.val) ∧
      (∀ y, IsMIntegralCurveOn (fun t => C (t, y))
        (fun x => -liouvilleVector α (exteriorDerivative α) x) (Ico 0 δ)) ∧
      (∀ y, ∀ t ∈ Ico 0 δ,
        ((𝓡∂ (k + 1)).IsBoundaryPoint (C (t, y)) ↔ t = 0)) ∧
      ∀ p ∈ Ico 0 δ ×ˢ univ, ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
        ContMDiffAt (𝓡∂ (k + 1)) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model k)) ∞ g (C p) ∧
        ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C q) = q := by
  apply exists_uniform_collar_of_primitive α hα hnd
  intro x
  obtain ⟨rho, beta, hzero, hside, hreg, hb, hag, hpos⟩ := hout x
  let c := IntrinsicBoundary.chartAt x
  have hx : x.val ∈ c.ambient.source := by
    have h := IntrinsicBoundary.mem_chartAt_source x
    rw [c.source_eq] at h
    exact h
  exact inward_of_localDefiningFunction_outward c.mem_atlas hx x.property rho
    hzero hside hreg hb hag (liouvilleVector α (exteriorDerivative α)) hpos

end FsFltz.Geometry.IntrinsicLiouville
