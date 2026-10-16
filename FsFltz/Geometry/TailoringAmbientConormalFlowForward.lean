import FsFltz.Geometry.TailoringFiniteBandHittingRadial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Forward retention of the actual ambient conormal superlevel

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1799–1816.
The native cone-piece uniqueness theorem and actual boundary derivative
positivity prove retention above base value one. No retention of the norm,
cone, outward ray, or positive base is supplied as an input premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Topology Manifold ContDiff

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

/-- The native scalar derivative along a local integral curve, expressed
using the actual complex differential of the prescribed function. -/
theorem hasDerivAt_re_of_isMIntegralCurveAt {d : ℕ} (M : SmoothManifold d)
    {f : M.Point → ℂ} (hf : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) ∞ f)
    {Z : (x : M.Point) → M.Tangent x} {γ : ℝ → M.Point} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ Z t) :
    HasDerivAt (fun s => (f (γ s)).re) (complexDifferential M f (γ t) (Z (γ t))).re t := by
  have h := (hasMFDerivAt_iff_hasFDerivAt.mp
    ((hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hγ.hasMFDerivAt)).hasDerivAt
  have hd : HasDerivAt (fun s => f (γ s)) (complexDifferential M f (γ t) (Z (γ t))) t := by
    apply h.congr_deriv
    change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, ℂ) f (γ t) ((1 : ℝ) • Z (γ t)) = _
    rw [one_smul]
    rfl
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd

private theorem eventually_right_gt_of_hasDerivAt_pos {f : ℝ → ℝ} {d t : ℝ}
    (hf : HasDerivAt f d t) (hd : 0 < d) :
    ∀ᶠ s in 𝓝[>] t, f t < f s := by
  have hs := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)).eventually
    (Ioi_mem_nhds hd)
  filter_upwards [hs, self_mem_nhdsWithin] with s hpos hst
  exact (slope_pos_iff hst).mp hpos

/-- A native ambient trajectory preserves its specified cone, original
angle, and real base superlevel throughout every forward time interval.
The norm lower bound is a conclusion of real base retention. -/
theorem tailoringEndpoint_exists_uniform_ambient_conePiece_forward_superlevel
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (γ : ℝ → (lgManifold n).Point) (a b : ℝ), a ≤ b →
        (∀ t ∈ Icc a b, IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        ∀ σ ∈ faceFan I, coordinateGradient φEnd (γ a).1 ∈ σ →
          (γ a).2 ∈ coneTorus σ → 1 ≤ (tailoringFamily I β 1 (γ a)).re →
          ∀ t ∈ Icc a b, γ t ∈ tailoringLegendreConic I φEnd ∧
            coordinateGradient φEnd (γ t).1 ∈ σ ∧ (γ t).2 = (γ a).2 ∧
              1 ≤ (tailoringFamily I β 1 (γ t)).re := by
  obtain ⟨Bl, hBl, hlocal⟩ := tailoringEndpoint_exists_uniform_ambient_conePiece_local_invariance
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bm, _, hmargin⟩ := tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hR heq
  obtain ⟨Bz, _, hsmall⟩ := tailoringFamily_exists_compact_norm_lt_one I 0
  refine ⟨max Bl (max Bm Bz), hBl.trans_le (le_max_left _ _), ?_⟩
  intro β hβ K hK γ a b hab hγ σ hσ hp₀ hθ₀ hbase₀
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hβl : Bl ≤ β := (le_max_left _ _).trans hβ
  have hβm : Bm ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβz : Bz ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  let f := tailoringFamily I β 1
  let A : Set ℝ := {t | Φ (γ t).1 ∈ σ ∧ (γ t).2 = (γ a).2 ∧ 1 ≤ (f (γ t)).re}
  have hγc : Continuous (fun t : Icc a b => γ t.val) :=
    (show ContinuousOn γ (Icc a b) from fun t ht =>
      (hγ t ht).continuousAt.continuousWithinAt).domRestrict
  have hAs : IsClosed {t : Icc a b | t.val ∈ A} := by
    exact ((I.isClosed_of_mem_faceFan hσ).preimage
      (Φ.continuous.comp (continuous_fst.comp hγc))).inter
      ((isClosed_eq (continuous_snd.comp hγc) continuous_const).inter
        (isClosed_le continuous_const
          (Complex.continuous_re.comp ((contMDiff_tailoringFamily_lgManifold I β 1).continuous.comp hγc))))
  have hAc : IsClosed (A ∩ Icc a b) := by
    have hh := (isClosed_Icc : IsClosed (Icc a b)).isClosedMap_subtype_val _ hAs
    have he : Subtype.val '' {t : Icc a b | t.val ∈ A} = A ∩ Icc a b := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨hs, s.property⟩
      · rintro ⟨ht, htI⟩
        exact ⟨⟨t, htI⟩, ht, rfl⟩
    exact he ▸ hh
  have hne (t : ℝ) (ht : 1 ≤ (f (γ t)).re) :
      coordinateGradient φEnd (γ t).1 ≠ 0 := by
    rw [← hΦeq, ← hΦ₀]
    intro hz
    have hu : (γ t).1 = 0 := Φ.injective hz
    have hh := hsmall β hβz 1 (γ t) (by simp [hu, realSquaredNorm])
    exact not_lt_of_ge (ht.trans (Complex.re_le_norm _)) hh
  have hpiece (t : ℝ) (ht : t ∈ A) : γ t ∈ tailoringLegendreConic I φEnd := by
    have hp : coordinateGradient φEnd (γ t).1 ∈ σ := hΦeq _ ▸ ht.1
    have hσne : σ ≠ {0} := by
      intro he
      exact hne t ht.2.2 (by simpa [he] using hp)
    exact ⟨hne t ht.2.2, σ, hσ, hσne, hp, ht.2.1.symm ▸ hθ₀⟩
  have ha : a ∈ A := ⟨(hΦeq _).symm ▸ hp₀, rfl, hbase₀⟩
  have hall : Icc a b ⊆ A := hAc.Icc_subset_of_forall_mem_nhdsWithin ha (by
    intro t ht
    have htI : t ∈ Icc a b := ⟨ht.2.1, ht.2.2.le⟩
    have hp : coordinateGradient φEnd (γ t).1 ∈ σ := hΦeq _ ▸ ht.1.1
    have hnorm : 1 ≤ ‖f (γ t)‖ := ht.1.2.2.trans (Complex.re_le_norm _)
    have hl := hlocal β hβl K hK γ t (hγ t htI) σ hσ (hne t ht.1.2.2)
      hp (ht.1.2.1.symm ▸ hθ₀) hnorm
    have hright : ∀ᶠ s in 𝓝[>] t, 1 ≤ (f (γ s)).re := by
      rcases eq_or_lt_of_le ht.1.2.2 with he | he
      · obtain ⟨ε, hε, hm⟩ := hmargin β hβm 1
        have hpos := hε.trans_le (hm (γ t) (hpiece t ht.1) ht.1.2.2 he.symm.le K hK)
        have hd := hasDerivAt_re_of_isMIntegralCurveAt (lgManifold n)
          (contMDiff_tailoringFamily_lgManifold I β 1) (hγ t htI)
        exact (eventually_right_gt_of_hasDerivAt_pos hd hpos).mono (fun s hs => by
          change 1 ≤ (tailoringFamily I β 1 (γ s)).re
          exact (he.trans_lt hs).le)
      · have hc := (Complex.continuous_re.comp
          (contMDiff_tailoringFamily_lgManifold I β 1).continuous).continuousAt.comp
            (hγ t htI).continuousAt
        exact ((hc.eventually (Ioi_mem_nhds he)).filter_mono nhdsWithin_le_nhds).mono
          (fun _ hs => hs.le)
    filter_upwards [hl.filter_mono nhdsWithin_le_nhds, hright] with s hs hr
    exact ⟨(hΦeq _).symm ▸ hs.2.2, hs.2.1.trans ht.1.2.1, hr⟩)
  intro t ht
  have hh := hall ht
  exact ⟨hpiece t hh, hΦeq _ ▸ hh.1, hh.2⟩

/-- Forward retention and strict real base increase for every actual
conormal superlevel start. This is an input-free retention producer for
finite transverse hitting, once the native trajectory has been constructed. -/
theorem tailoringEndpoint_exists_uniform_ambient_conormal_forward_superlevel
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (γ : ℝ → (lgManifold n).Point) (a b : ℝ), a ≤ b →
        (∀ t ∈ Icc a b, IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        γ a ∈ tailoringLegendreConic I φEnd → 1 ≤ (tailoringFamily I β 1 (γ a)).re →
        (∀ t ∈ Icc a b, γ t ∈ tailoringLegendreConic I φEnd ∧
          (γ t).2 = (γ a).2 ∧ 1 ≤ (tailoringFamily I β 1 (γ t)).re) ∧
        StrictMonoOn (fun t => (tailoringFamily I β 1 (γ t)).re) (Icc a b) := by
  obtain ⟨Bp, hBp, hpiece⟩ := tailoringEndpoint_exists_uniform_ambient_conePiece_forward_superlevel
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  obtain ⟨Bm, _, hmargin⟩ := tailoringEndpoint_exists_uniform_conormal_finite_base_band_margin
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hR heq
  refine ⟨max Bp Bm, hBp.trans_le (le_max_left _ _), ?_⟩
  intro β hβ K hK γ a b hab hγ hstart hbase
  obtain ⟨_, σ, hσ, _, hp, hθ⟩ := hstart
  have hr := hpiece β ((le_max_left _ _).trans hβ) K hK γ a b hab hγ σ hσ hp hθ hbase
  refine ⟨fun t ht => ⟨(hr t ht).1, (hr t ht).2.2⟩, ?_⟩
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hγc : ContinuousOn γ (Icc a b) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
    ((Complex.continuous_re.comp (contMDiff_tailoringFamily_lgManifold I β 1).continuous).comp_continuousOn hγc)
    (fun t ht => (hasDerivAt_re_of_isMIntegralCurveAt (lgManifold n)
      (contMDiff_tailoringFamily_lgManifold I β 1) (hγ t (interior_subset ht))).hasDerivWithinAt)
  intro t ht
  have hret := hr t (interior_subset ht)
  obtain ⟨ε, hε, hm⟩ := hmargin β ((le_max_right _ _).trans hβ)
    (tailoringFamily I β 1 (γ t)).re
  exact hε.trans_le (hm (γ t) hret.1 hret.2.2.2 le_rfl K hK)

/-- Every native trajectory from the actual core section stays in the
conormal region, with fixed angle and strictly increasing positive base,
at all times on its supplied forward interval of existence. -/
theorem tailoringEndpoint_exists_uniform_ambient_core_forward
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φEnd u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    {R : ℝ} (hR : 0 < R)
    (heq : ∀ u, R ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ K : ℝ, 0 ≤ K →
      ∀ (γ : ℝ → (lgManifold n).Point) (a : ℝ),
        (∀ t ≥ a, IsMIntegralCurveAt γ ((lgManifold n).liouvilleVector
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t) →
        γ a ∈ tailoringCoreSection I φEnd β →
        (∀ t ≥ a, γ t ∈ tailoringLegendreConic I φEnd ∧
          (γ t).2 = (γ a).2 ∧ 1 ≤ (tailoringFamily I β 1 (γ t)).re) ∧
        (∀ t > a, 1 < (tailoringFamily I β 1 (γ t)).re) ∧
        StrictMonoOn (fun t => (tailoringFamily I β 1 (γ t)).re) (Ici a) := by
  obtain ⟨B, hB, hforward⟩ := tailoringEndpoint_exists_uniform_ambient_conormal_forward_superlevel
    I hφ hc hU hlower hupper hEnd Φ hΦeq hΦ₀ hΦ hΦinv hR heq
  refine ⟨B, hB, ?_⟩
  intro β hβ K hK γ a hγ hcore
  have hbase : (tailoringFamily I β 1 (γ a)).re = 1 := by rw [hcore.2]; rfl
  have hr (b : ℝ) (hb : a ≤ b) := hforward β hβ K hK γ a b hb
    (fun t ht => hγ t ht.1) hcore.1 (by rw [hbase])
  refine ⟨fun t ht => (hr t ht).1 t ⟨ht, le_rfl⟩, ?_, ?_⟩
  · intro t ht
    have hh := (hr t ht.le).2 (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le) ht
    simpa only [hbase] using hh
  · intro s hs t ht hst
    exact (hr t ht).2 ⟨hs, hst.le⟩ ⟨ht, le_rfl⟩ hst

end FsFltz
