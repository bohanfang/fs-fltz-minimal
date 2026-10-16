import FsFltz.Geometry.IntrinsicExtensionLiouville
import FsFltz.Geometry.IntrinsicOutwardSign

/-!
# Outwardness for the regular defining functions of an intrinsic extension

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. A regular defining function pulled back from an ambient
extension has a strictly negative native normal differential. The proof uses
the actual within-chart derivative and the domain-side sublevel inequality;
it does not identify a chosen defining function with a collar coordinate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ}

private theorem negative_normal_of_halfSpace_localMax
    {beta : Model (k + 1) → ℝ} {a : Model (k + 1)}
    {L : Model (k + 1) →L[ℝ] ℝ} (ha : a 0 = 0) (hz : beta a = 0)
    (hd : HasFDerivWithinAt beta L {y : Model (k + 1) | 0 ≤ y 0} a)
    (hside : ∀ᶠ y in 𝓝[{y : Model (k + 1) | 0 ≤ y 0}] a, beta y ≤ 0)
    (hreg : L ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ ∀ v : Model (k + 1), L v = c * v 0 := by
  let n : Model (k + 1) := EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)
  have hn : n 0 = 1 := by simp [n]
  have hmax : IsLocalMaxOn beta {y : Model (k + 1) | 0 ≤ y 0} a := by
    filter_upwards [hside] with y hy
    simpa only [hz] using hy
  have hnonpos (v : Model (k + 1)) (hv : 0 ≤ v 0) : L v ≤ 0 := by
    apply hmax.hasFDerivWithinAt_nonpos hd
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 ≤ (a + t • v) 0
    simpa [ha] using mul_nonneg (le_of_lt ht) hv
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

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The sign comparison needs only the actual native derivative. In particular
an ambient smooth defining function needs no separately supplied open extension
of its pullback to the native manifold. -/
theorem mfderiv_eq_neg_normal_of_mdifferentiable_local_sublevel
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) {x : M} (hx : x ∈ e.source)
    (hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint x)
    (rho : M → ℝ) (hd : MDifferentiableAt (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x)
    (hzero : rho x = 0) (hside : ∀ᶠ y in 𝓝 x, rho y ≤ 0)
    (hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ ∀ v : TangentSpace (𝓡∂ (k + 1)) x,
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v =
        c * (show Model (k + 1) from chartTangentMap e x v) 0 := by
  let a := e.extend (𝓡∂ (k + 1)) x
  let beta := rho ∘ (e.extend (𝓡∂ (k + 1))).symm
  let L := fderivWithin ℝ beta (range (𝓡∂ (k + 1))) a
  have hxs : x ∈ (e.extend (𝓡∂ (k + 1))).source := by
    simpa only [e.extend_source] using hx
  have hat : a ∈ (e.extend (𝓡∂ (k + 1))).target :=
    (e.extend (𝓡∂ (k + 1))).map_source hxs
  have ha : a 0 = 0 :=
    (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero he hx).mp hboundary
  have hi := mdifferentiableWithinAt_extend_symm
    (IsManifold.subset_maximalAtlas (I := 𝓡∂ (k + 1)) (n := 1) he) hat
  have hd' : MDifferentiableAt (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho
      ((e.extend (𝓡∂ (k + 1))).symm a) := by
    simpa only [a, (e.extend (𝓡∂ (k + 1))).left_inv hxs] using hd
  have hb : DifferentiableWithinAt ℝ beta (range (𝓡∂ (k + 1))) a :=
    (hd'.comp_mdifferentiableWithinAt a hi).differentiableWithinAt
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, Model (k + 1)) (range (𝓡∂ (k + 1))) a :=
    (𝓡∂ (k + 1)).uniqueMDiffOn a (e.extend_target_subset_range hat)
  have hchain (v : Model (k + 1)) : L v = mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho
      ((e.extend (𝓡∂ (k + 1))).symm a) (inverseChartTangentMap e a v) := by
    have hc := mfderiv_comp_mfderivWithin (f := (e.extend (𝓡∂ (k + 1))).symm)
      (g := rho) a hd' hi hu
    have hv := congrArg (fun A => A v) hc
    rw [mfderivWithin_eq_fderivWithin] at hv
    exact hv
  have hformula (v : TangentSpace (𝓡∂ (k + 1)) x) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x v = L (chartTangentMap e x v) := by
    have hh := hchain (chartTangentMap e x v)
    dsimp only [a] at hh
    rw [inverseChartTangentMap_chartTangentMap he hx,
      (e.extend (𝓡∂ (k + 1))).left_inv hxs] at hh
    exact hh.symm
  have hL : L ≠ 0 := by
    intro hz
    apply hreg
    ext v
    rw [hformula v, hz]
    rfl
  have hzeroBeta : beta a = 0 := by
    simpa only [beta, Function.comp_apply, a,
      (e.extend (𝓡∂ (k + 1))).left_inv hxs] using hzero
  have hsideBeta : ∀ᶠ y in 𝓝[range (𝓡∂ (k + 1))] a, beta y ≤ 0 := by
    have ht : Tendsto (e.extend (𝓡∂ (k + 1))).symm
        (𝓝[range (𝓡∂ (k + 1))] a) (𝓝 x) := by
      exact le_of_eq (e.map_extend_symm_nhdsWithin_range hx)
    exact ht.eventually hside
  have hrange : range (𝓡∂ (k + 1)) = {y : Model (k + 1) | 0 ≤ y 0} := by
    rw [modelWithCornersEuclideanHalfSpace_toFun, range_euclideanHalfSpace]
  obtain ⟨c, hc, hcf⟩ := negative_normal_of_halfSpace_localMax ha hzeroBeta
    (by simpa only [← hrange] using hb.hasFDerivWithinAt)
    (by simpa only [← hrange] using hsideBeta) hL
  exact ⟨c, hc, fun v => (hformula v).trans (hcf _)⟩

/-- An ambient regular defining covector is positive on the actual image of
an outward native vector. Its pullback is regular because the inclusion
differential is surjective. -/
theorem outward_extension_of_negative_normal
    (N : SmoothManifold (k + 1)) (i : M → N.Point) {x : M}
    (hi : ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i x)
    (hsurj : Function.Surjective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M) (hx : x ∈ e.source)
    (hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint x)
    (v : TangentSpace (𝓡∂ (k + 1)) x)
    (hnegative : (show Model (k + 1) from chartTangentMap e x v) 0 < 0)
    (rho : N.Point → ℝ)
    (hrho : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ rho (i x))
    (hzero : rho (i x) = 0) (hside : ∀ᶠ y in 𝓝 x, rho (i y) ≤ 0)
    (hreg : mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) rho (i x) ≠ 0) :
    0 < (show ℝ from mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) rho (i x)
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x v)) := by
  have hd := mfderiv_comp (f := i) (g := rho) x
    (hrho.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  have hchain (w : TangentSpace (𝓡∂ (k + 1)) x) :
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (rho ∘ i) x w =
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) rho (i x)
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x w) :=
    congrArg (fun A => A w) hd
  have hpreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (rho ∘ i) x ≠ 0 := by
    intro hz
    apply hreg
    ext w
    obtain ⟨u, rfl⟩ := hsurj w
    have h := hchain u
    rw [hz] at h
    exact h.symm
  obtain ⟨c, hc, hformula⟩ := mfderiv_eq_neg_normal_of_mdifferentiable_local_sublevel
    he hx hboundary (rho ∘ i)
    ((hrho.comp x hi).mdifferentiableAt (by simp)) hzero hside hpreg
  rw [← hchain v, hformula v]
  exact mul_pos_of_neg_of_neg hc hnegative

/-- The actual native outward field is outward for every regular defining
function stored in a compact-domain extension. Only the proved carrier and
frontier identities are used; the choice of defining function is arbitrary. -/
theorem outward_compactDomain_extension
    (D : CompactDomain (k + 1)) (i : M → D.extension.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i)
    (hsurj : ∀ x, Function.Surjective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hrange : range i = D.carrier)
    (hfrontier : frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    (F : (x : D.extension.Point) → D.extension.Tangent x)
    (hfield : ∀ x, F (i x) = mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x (Z x))
    (hout : ∀ b : IntrinsicBoundary.Point k M,
      (show Model (k + 1) from chartTangentMap (IntrinsicBoundary.chartAt b).ambient
        b.val (Z b.val)) 0 < 0) :
    ∀ (y : D.extension.Point) (hy : y ∈ frontier D.carrier),
      0 < D.extension.scalarDerivative (D.defining y hy).rho y (F y) := by
  intro y hy
  have hyp := hy
  rw [hfrontier] at hyp
  obtain ⟨x, hx, rfl⟩ := hyp
  let b : IntrinsicBoundary.Point k M := ⟨x, hx⟩
  let R := D.defining (i x) hy
  have hneg := hout b
  have hesource : x ∈ (IntrinsicBoundary.chartAt b).ambient.source := by
    have hs := IntrinsicBoundary.mem_chartAt_source b
    rwa [(IntrinsicBoundary.chartAt b).source_eq] at hs
  have hrho : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ R.rho (i x) :=
    R.smooth_rho.contMDiffAt (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)
  have hzero : R.rho (i x) = 0 := (R.zero_level (i x) R.mem_neighbourhood).mp hy
  have hside : ∀ᶠ z in 𝓝 x, R.rho (i z) ≤ 0 := by
    filter_upwards [(hi x).continuousAt.eventually
      (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with z hz
    exact (R.sublevel (i z) hz).mp (hrange ▸ mem_range_self z)
  unfold SmoothManifold.scalarDerivative
  rw [hfield x]
  exact outward_extension_of_negative_normal D.extension i (hi x) (hsurj x)
    (IntrinsicBoundary.chartAt b).mem_atlas hesource
    hx (Z x) hneg R.rho hrho hzero hside R.regular

end FsFltz.Geometry.IntrinsicLiouville
