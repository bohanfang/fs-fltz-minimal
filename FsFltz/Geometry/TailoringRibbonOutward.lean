import FsFltz.Geometry.TailoringRibbonPrimitiveFamily
import FsFltz.Geometry.IntrinsicExtensionOutward

/-!
# Outwardness on the same transported compact tailoring carrier

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`def:chain`, lines 163–169; `geometric-part-fsf-proof.tex`,
`lem:markedfamily`, lines 975–1009, and `eq:fiberends`, lines 1208–1237.
The moving potential sublevel gives outwardness for the defining normal
of the same native compact carrier. No parameterwise replacement of that
carrier, outwardness certificate, or completion marking is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.CompactDomain
open SmoothManifold IntrinsicLiouville

/-- A smooth scalar function that is nonpositive on the actual carrier and
zero on its actual frontier detects the sign of every stored defining
normal. A positive derivative derives regularity and outwardness; no
comparison factor or native normal sign is supplied as a hypothesis. -/
theorem outward_of_sublevel_derivative {d : ℕ} (D : CompactDomain d)
    (η : D.extension.Point → ℝ)
    (hη : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ η)
    (hside : ∀ x ∈ D.carrier, η x ≤ 0)
    (hzero : ∀ x ∈ frontier D.carrier, η x = 0)
    (x : D.extension.Point) (hx : x ∈ frontier D.carrier)
    (v : D.extension.Tangent x)
    (hpos : 0 < D.extension.scalarDerivative η x v) :
    0 < D.extension.scalarDerivative (D.defining x hx).rho x v := by
  cases d with
  | zero =>
    rw [D.frontier_eq_empty_of_dimension_zero] at hx
    exact False.elim hx
  | succ k =>
    let p : D.Point := ⟨x, D.compact.isClosed.frontier_subset hx⟩
    let i : D.Point → D.extension.Point := Subtype.val
    have hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i :=
      D.contMDiff_subtype_val
    have hsurj : Function.Surjective
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i p) :=
      LinearMap.injective_iff_surjective.mp (D.injective_mfderiv_subtype_val p)
    obtain ⟨w, hw⟩ := hsurj v
    have hboundary : (𝓡∂ (k + 1)).IsBoundaryPoint p :=
      (D.isBoundaryPoint_iff_frontier p).mpr hx
    let e := (IntrinsicBoundary.chartAt (⟨p, hboundary⟩ : IntrinsicBoundary.Point k D.Point)).ambient
    have he : e ∈ atlas (EuclideanHalfSpace (k + 1)) D.Point :=
      (IntrinsicBoundary.chartAt (⟨p, hboundary⟩ : IntrinsicBoundary.Point k D.Point)).mem_atlas
    have hes : p ∈ e.source := by
      have hs := IntrinsicBoundary.mem_chartAt_source
        (⟨p, hboundary⟩ : IntrinsicBoundary.Point k D.Point)
      rwa [(IntrinsicBoundary.chartAt _).source_eq] at hs
    have hchain := mfderiv_comp (f := i) (g := η) p
      (hη.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
    have hp : 0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (η ∘ i) p w) := by
      rw [hchain]
      change 0 < (show ℝ from mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) η (i p)
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i p w))
      rw [hw]
      exact hpos
    have hreg : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) (η ∘ i) p ≠ 0 := by
      intro hz
      rw [hz] at hp
      exact (lt_irrefl (0 : ℝ)) hp
    obtain ⟨c, hc, hformula⟩ :=
      mfderiv_eq_neg_normal_of_mdifferentiable_local_sublevel he hes hboundary
        (η ∘ i) ((hη.comp hi).mdifferentiableAt (by simp))
        (hzero x hx) (Eventually.of_forall (fun y => hside y.val y.property)) hreg
    have hnegative : (show Model (k + 1) from chartTangentMap e p w) 0 < 0 := by
      rw [hformula w] at hp
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hc.le (le_of_not_gt hn))) hp
    let R := D.defining x hx
    have hrho : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ) ∞ R.rho x :=
      R.smooth_rho.contMDiffAt (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)
    have hRzero : R.rho x = 0 := (R.zero_level x R.mem_neighbourhood).mp hx
    have hRside : ∀ᶠ y in 𝓝 p, R.rho (i y) ≤ 0 := by
      filter_upwards [(hi p).continuousAt.eventually
        (R.open_neighbourhood.mem_nhds R.mem_neighbourhood)] with y hy
      exact (R.sublevel (i y) hy).mp y.property
    have h := outward_extension_of_negative_normal D.extension i (hi p) hsurj
      he hes hboundary w hnegative R.rho hrho hRzero hRside R.regular
    rw [hw] at h
    exact h

end FsFltz.Geometry.CompactDomain

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

/-- The actual transported tailoring primitives are outward on the same
nonempty fixed native compact carrier. Joint smoothness, one common
symplectic neighborhood, and both literal image equations are retained.
The boundary-normal sign is derived from the whole-end intrinsic estimate
and the actual carrier/frontier images, with no geometric certificate in
the hypotheses. -/
theorem tailoringFamily_exists_uniform_fixedCarrier_outwardPrimitiveFamily
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
      ∀ β ≥ β₀, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∃ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n))
        (O : TopologicalSpace.Opens D.extension.Point),
        D.carrier.Nonempty ∧ D.carrier ⊆ O ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        (∀ t : Parameter,
          (J t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
          (J t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) ∧
        (∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ))) O) ∧
        ∀ (t : Parameter) (x : D.extension.Point) (hx : x ∈ frontier D.carrier),
          0 < D.extension.scalarDerivative (D.defining x hx).rho x
            (D.extension.liouvilleVector
              (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) := by
  obtain ⟨Fb, hFb, Bb, hBb, hbase⟩ :=
    tailoringFamily_exists_uniform_fixedCarrier_primitiveFamily
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fe, hFe, Be, _hBe, hexhaustion⟩ :=
    tailoringFamily_exists_uniform_whole_end_intrinsic_exhaustion
      I hφ hc hU hlower hupper hEnd hhom hL hend
  obtain ⟨V, hV⟩ := (isCompact_phi0_sublevel (n := n) (L ^ 2 / 2) (by positivity)).bddAbove_image
    (hφ.continuous.comp continuous_fst).continuousOn
  let Bφ : ℝ := (2 * max V 0 + 1) / Fe
  let β₀ : ℝ := max 1 (max Bb (max Be Bφ))
  let F : ℝ := max Fb Fe
  refine ⟨F, hFb.trans_le (le_max_left _ _), β₀,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro β hβ A hA
  have hβ₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβpos : 0 < β := zero_lt_one.trans_le hβ₁
  have hβbase : Bb ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβend : Be ≤ β := (le_max_left _ _).trans
    ((le_max_right Bb _).trans ((le_max_right 1 _).trans hβ))
  have hβφ : Bφ ≤ β := (le_max_right _ _).trans
    ((le_max_right Bb _).trans ((le_max_right 1 _).trans hβ))
  have hAbase : Fb ^ 2 * β ^ 2 / 2 ≤ A := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFb.le (le_max_left _ _) 2) (sq_nonneg β)) hA
  have hAend : Fe ^ 2 * β ^ 2 / 2 ≤ A := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFe.le (le_max_right _ _) 2) (sq_nonneg β)) hA
  have hlevel : V < Fe ^ 2 * β ^ 2 / 2 := by
    have hb : 2 * max V 0 + 1 ≤ Fe * β := by
      have h := (div_le_iff₀ hFe).mp hβφ
      simpa only [mul_comm] using h
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * max V 0 + 1) hb 2
    nlinarith only [hsq, le_max_left V 0, le_max_right V 0, sq_nonneg (max V 0)]
  have hApos : 0 < A := (by positivity : 0 < Fe ^ 2 * β ^ 2 / 2).trans_le hAend
  obtain ⟨D, J, O, hDne, hDO, hJ, himages, hkernel, hμ, hsymplectic⟩ :=
    hbase β hβbase A hAbase
  refine ⟨D, J, O, hDne, hDO, hJ, himages, hkernel, hμ, hsymplectic, ?_⟩
  intro t x hx
  have hxD : x ∈ D.carrier := D.compact.isClosed.frontier_subset hx
  have himage : tailoringFamily I β t.val ((J t).map x) = 1 ∧ φ ((J t).map x).1 = A := by
    have hmem : (J t).map x ∈ (J t).map '' frontier D.carrier := ⟨x, hx, rfl⟩
    rwa [(himages t).2] at hmem
  have hxEnd : L < ‖(WithLp.toLp 2 ((J t).map x).1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra hn
    have hsq : realSquaredNorm ((J t).map x).1 ≤ L ^ 2 := by
      simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using
        (sq_le_sq₀ (norm_nonneg _) hL.le).mpr (le_of_not_gt hn)
    have hm : (J t).map x ∈ {y : LGSpace n | phi0 y ≤ L ^ 2 / 2} := by
      change realSquaredNorm ((J t).map x).1 / 2 ≤ L ^ 2 / 2
      linarith only [hsq]
    have hb := hV (mem_image_of_mem (fun y : LGSpace n => φ y.1) hm)
    change φ ((J t).map x).1 ≤ V at hb
    rw [himage.2] at hb
    exact (not_le_of_gt hlevel) (hAend.trans hb)
  let H := potentialHessianEquiv hc hlower (WithLp.toLp 2 ((J t).map x).1)
  have he : metricRadialSq H ((J t).map x).1 = 2 * A := by
    rw [metricRadialSq_potential_eq_two_mul hEnd1 hEnd hhom hc hlower hL hend _ hxEnd, himage.2]
  have hr : Fe * β ≤ Real.sqrt (metricRadialSq H ((J t).map x).1) := by
    rw [he]
    apply (Real.le_sqrt (mul_nonneg hFe.le hβpos.le) (by positivity)).mpr
    nlinarith only [hAend]
  have hd := hexhaustion β hβend t.val t.property D.extension (J t) x
    (hkernel t x hxD) hr (by simp only [himage.1, norm_one]; norm_num)
  change metricRadialSq H ((J t).map x).1 / 2 ≤
    D.extension.scalarDerivative (fun y => φ ((J t).map y).1) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) at hd
  rw [he] at hd
  have hout : 0 < D.extension.scalarDerivative (fun y => φ ((J t).map y).1) x
      (D.extension.liouvilleVector
        (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) x) := by
    linarith only [hd, hApos]
  have hvalue := contMDiff_potential_W_level_value hφ (J t)
  have hside : ∀ y ∈ D.carrier, φ ((J t).map y).1 - A ≤ 0 := by
    intro y hy
    have hmem : (J t).map y ∈ (J t).map '' D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).1] at hmem
    exact sub_nonpos.mpr hmem.2
  have hzero : ∀ y ∈ frontier D.carrier, φ ((J t).map y).1 - A = 0 := by
    intro y hy
    have hmem : (J t).map y ∈ (J t).map '' frontier D.carrier := ⟨y, hy, rfl⟩
    rw [(himages t).2] at hmem
    exact sub_eq_zero.mpr hmem.2
  apply D.outward_of_sublevel_derivative (fun y => φ ((J t).map y).1 - A)
    (hvalue.sub_const A) hside hzero x hx
  unfold scalarDerivative
  change 0 < (show ℝ from mfderiv _ _ ((fun y => φ ((J t).map y).1) - fun _ => A) x _)
  rw [mfderiv_sub (hvalue.mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mfderiv_const, sub_zero]
  exact hout

end FsFltz
