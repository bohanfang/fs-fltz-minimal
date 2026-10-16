import FsFltz.Geometry.PotentialAmbientMarking

/-!
# Full holomorphic ambient markings along the retained potential path

Source: `geometric-part-fsf-proof.tex`, choice dependencies, lines 493–521,
and `lem:originalends`, lines 770–818. The potential endpoint is retained;
the literal affine potential parameter and the coefficient parameter vary
independently. The common level precedes both parameters and every finite K.
These are actual markings at each parameter, not a joint smoothness claim
for the selected markings as a parameterized family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

/-- The lower bound for the actual Euclidean Hessian of the literal native
potential interpolation, in the coordinates used by its Liouville field. -/
theorem potentialPath_native_hessian_lowerBound
    {φ : RealSpace n → ℝ} {c : ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (u v : EuclideanSpace ℝ (Fin n)) :
    min 1 c * ‖v‖ ^ 2 ≤ inner ℝ
      (fderiv ℝ (gradient (potentialPath (fun x => realSquaredNorm x / 2) φ s ∘
        EuclideanSpace.equiv (Fin n) ℝ)) u v) v := by
  have hq : (fun x : RealSpace n => realSquaredNorm x / 2) ∘
      EuclideanSpace.equiv (Fin n) ℝ = fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2 := by
    ext x
    simp
  rw [potentialPath_comp, hq]
  exact hessian_potentialPath_lowerBound ((contDiff_id.norm_sq ℝ).div_const 2)
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
    (fun x v => by simp [hessian_half_norm_sq]) hlower hs u v

/-- The same interpolation has the fixed finite upper Hessian bound. -/
theorem potentialPath_native_hessian_upperBound
    {φ : RealSpace n → ℝ} {U : ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (fderiv ℝ (gradient (potentialPath (fun x => realSquaredNorm x / 2) φ s ∘
      EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ max 1 U * ‖v‖ ^ 2 := by
  have hq : (fun x : RealSpace n => realSquaredNorm x / 2) ∘
      EuclideanSpace.equiv (Fin n) ℝ = fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2 := by
    ext x
    simp
  rw [potentialPath_comp, hq]
  exact hessian_potentialPath_upperBound ((contDiff_id.norm_sq ℝ).div_const 2)
    (hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
    (fun x v => by simp [hessian_half_norm_sq]) hupper hs u v

/-- Every native path member is globally smooth. -/
theorem potentialPath_native_contDiff {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (s : ℝ) :
    ContDiff ℝ ∞ (potentialPath (fun x => realSquaredNorm x / 2) φ s) :=
  potentialPath_contDiff_space (contDiff_realSquaredNorm.div_const 2) hφ s

/-- Its prescribed homogeneous end is globally continuously differentiable. -/
theorem potentialPath_native_end_contDiff {φEnd : RealSpace n → ℝ}
    (hEnd1 : ContDiff ℝ 1 φEnd) (s : ℝ) :
    ContDiff ℝ 1 (potentialPath (fun x => realSquaredNorm x / 2) φEnd s) :=
  (contDiff_const.mul ((contDiff_realSquaredNorm.div_const 2).of_le (by simp))).add
    (contDiff_const.mul hEnd1)

/-- Its same prescribed end is smooth away from the origin. -/
theorem potentialPath_native_end_contDiffAt {φEnd : RealSpace n → ℝ}
    (hEnds : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u) (s : ℝ) :
    ∀ u ≠ 0, ContDiffAt ℝ ∞
      (potentialPath (fun x => realSquaredNorm x / 2) φEnd s) u := by
  intro u hu
  exact (contDiffAt_const.mul (contDiff_realSquaredNorm.div_const 2).contDiffAt).add
    (contDiffAt_const.mul (hEnds u hu))

/-- The prescribed native end retains degree two at every potential parameter. -/
theorem potentialPath_native_end_homogeneous {φEnd : RealSpace n → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u) (s : ℝ) :
    ∀ r : ℝ, 0 < r → ∀ u,
      potentialPath (fun x => realSquaredNorm x / 2) φEnd s (r • u) =
        r ^ 2 * potentialPath (fun x => realSquaredNorm x / 2) φEnd s u := by
  apply potentialPath_homogeneous_two _ hhom s
  intro r _ u
  rw [realSquaredNorm_smul]
  ring

/-- End agreement holds at the same radial threshold for every parameter. -/
theorem potentialPath_native_eq_end {φ φEnd : RealSpace n → ℝ} {L : ℝ}
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)
    (s : ℝ) : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ →
      potentialPath (fun x => realSquaredNorm x / 2) φ s u =
        potentialPath (fun x => realSquaredNorm x / 2) φEnd s u :=
  fun u hu => potentialPath_eq_of_eq_right (hend u hu) s

section RetainedPath

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

/-- The concrete complete primitive for each literal retained potential path
member and each finite nonnegative holomorphic update. -/
def potentialPath_W_ambientCompletePrimitive (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) :
    CompletePrimitive (lgManifold n) ((lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun x => realSquaredNorm x / 2) φ s)) (W I) K) :=
  potential_W_ambientCompletePrimitive (potentialPath_native_contDiff hφ s)
    (potentialPath_native_end_contDiff hEnd1 s) (potentialPath_native_end_contDiffAt hEnds s)
    (potentialPath_native_end_homogeneous hhom s) (lt_min zero_lt_one hc)
    (zero_lt_one.trans_le (le_max_left _ _))
    (potentialPath_native_hessian_lowerBound hφ hlower hs)
    (potentialPath_native_hessian_upperBound hφ hupper hs)
    hL (potentialPath_native_eq_end hend s) I hK

/-- The compact ambient domain at a literal full path-potential sublevel.
The uniform theorem below derives its outwardness from the actual field. -/
def potentialPath_W_ambientOutwardDomain (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (I : ToricInput n) {K : ℝ} (hK : 0 ≤ K) (A : ℝ)
    (hpos : ∀ y : (lgManifold n).Point,
      A ≤ potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 →
      0 < (lgManifold n).scalarDerivative
        (fun y => potentialPath (fun x => realSquaredNorm x / 2) φ s y.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm (potentialPath (fun x => realSquaredNorm x / 2) φ s)) (W I) K) y)) :
    LiouvilleDomain (2 * n) :=
  potential_W_ambientOutwardDomain (potentialPath_native_contDiff hφ s)
    (potentialPath_native_end_contDiff hEnd1 s) (potentialPath_native_end_contDiffAt hEnds s)
    (potentialPath_native_end_homogeneous hhom s) (lt_min zero_lt_one hc)
    (potentialPath_native_hessian_lowerBound hφ hlower hs)
    hL (potentialPath_native_eq_end hend s) I hK A hpos

include hφ hEnds hhom hc hlower hupper hL hend in
/-- The actual native ambient derivative is positive above a single level
uniform in the independent coefficient and retained potential parameters,
and in every finite nonnegative K. -/
theorem ToricInput.coefficientPath_potentialPath_ambient_outward (I : ToricInput n) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ K : ℝ, 0 ≤ K → ∀ y : (lgManifold n).Point,
        A₀ ≤ potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 →
        0 < (lgManifold n).scalarDerivative
          (fun y => potentialPath (fun x => realSquaredNorm x / 2) φ s y.1) y
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm (potentialPath (fun x => realSquaredNorm x / 2) φ s))
            (W (I.alongCoefficientPath t)) K) y) := by
  obtain ⟨q, hq, Lmargin, hLmargin, hmargin⟩ :=
    I.coefficientPath_metric_quantitative_ambient_margin (lt_min zero_lt_one hc)
      (zero_lt_one.trans_le (le_max_left (1 : ℝ) U))
  let Lbig := max L Lmargin
  have hLbig : 0 < Lbig := hL.trans_le (le_max_left _ _)
  obtain ⟨B, hB⟩ := (isCompact_phi0_sublevel (n := n) (Lbig ^ 2 / 2)
    (by positivity)).exists_bound_of_continuousOn
      (hφ.continuous.comp continuous_fst).continuousOn
  let Bpath := max B (Lbig ^ 2 / 2)
  let A₀ := max Bpath 0 + 1
  have hA₀ : 0 < A₀ := by dsimp [A₀]; linarith [le_max_right Bpath 0]
  refine ⟨A₀, hA₀, ?_⟩
  intro s hs t ht K hK y hy
  have hout : Lbig < ‖(WithLp.toLp 2 y.1 : EuclideanSpace ℝ (Fin n))‖ := by
    by_contra h
    have hsquare := (sq_le_sq₀ (norm_nonneg _) hLbig.le).mpr (le_of_not_gt h)
    have hx : phi0 y ≤ Lbig ^ 2 / 2 := by
      have hs' : realSquaredNorm y.1 ≤ Lbig ^ 2 := by
        simpa [EuclideanSpace.norm_sq_eq, realSquaredNorm] using hsquare
      change realSquaredNorm y.1 / 2 ≤ Lbig ^ 2 / 2
      linarith
    have hb : φ y.1 ≤ Bpath :=
      ((Real.le_norm_self _).trans (hB y hx)).trans (le_max_left _ _)
    have hq' : realSquaredNorm y.1 / 2 ≤ Bpath := hx.trans (le_max_right _ _)
    have hpath : potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 ≤ Bpath := by
      calc
        potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 =
            (1 - s) * (realSquaredNorm y.1 / 2) + s * φ y.1 := rfl
        _ ≤ (1 - s) * Bpath + s * Bpath := add_le_add
          (mul_le_mul_of_nonneg_left hq' (sub_nonneg.mpr hs.2))
          (mul_le_mul_of_nonneg_left hb hs.1)
        _ = Bpath := by ring
    dsimp [A₀] at hy
    linarith [le_max_left Bpath 0]
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  let ψ := potentialPath (fun x => realSquaredNorm x / 2) φ s
  have hψ : ContDiff ℝ ∞ ψ := potentialPath_native_contDiff hφ s
  have hlow : ∀ u v : EuclideanSpace ℝ (Fin n), min 1 c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (ψ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v :=
    potentialPath_native_hessian_lowerBound hφ hlower hs
  have hupp : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (ψ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤
        max 1 U * ‖v‖ ^ 2 := potentialPath_native_hessian_upperBound hφ hupper hs
  let H := potentialHessianEquiv (lt_min zero_lt_one hc) hlow (WithLp.toLp 2 x.1)
  have hsymm : ∀ u v, inner ℝ (H u) v = inner ℝ u (H v) :=
    inner_fderiv_gradient_symmetric (hψ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff) _
  have hl : ∀ v, min 1 c * ‖v‖ ^ 2 ≤ inner ℝ (H v) v := hlow _
  have hu : ∀ v, inner ℝ (H v) v ≤ max 1 U * ‖v‖ ^ 2 := hupp _
  have hnorm : Real.sqrt (realSquaredNorm x.1) =
      ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n)))]
    congr 1
    simp [EuclideanSpace.norm_sq_eq, realSquaredNorm]
  obtain ⟨ha, hm⟩ := hmargin t ht (lgCover x)
    (show Lmargin ≤ Real.sqrt (realSquaredNorm (lgCover x).1) by
      rw [lgCover, hnorm]; exact (le_max_right _ _).trans hout.le) H hsymm hl hu
  have hr : 0 < metricRadialSq H x.1 :=
    (mul_pos (lt_min zero_lt_one hc) (sq_pos_of_pos (hLbig.trans hout))).trans_le
      (hl (WithLp.toLp 2 x.1))
  have hqpos : 0 < potentialMetricMargin H (I.alongCoefficientPath t) (lgCover x) :=
    (mul_pos (mul_pos hq (Real.sqrt_pos.mpr hr))
      (sq_pos_of_pos ((I.alongCoefficientPath t).maxMonomialMagnitude_pos (lgCover x)))).trans_le hm
  have hx : L < ‖(WithLp.toLp 2 x.1 : EuclideanSpace ℝ (Fin n))‖ :=
    lt_of_le_of_lt (le_max_left _ _) hout
  rw [(liouville_identities_potential_W_on_homogeneous_end hψ (lt_min zero_lt_one hc) hlow
    (potentialPath_native_end_contDiffAt hEnds s) (potentialPath_native_end_homogeneous hhom s)
    hL (potentialPath_native_eq_end hend s) (I.alongCoefficientPath t) x hx hK).2]
  exact div_pos (add_pos_of_pos_of_nonneg hr (mul_nonneg hK hqpos.le)) (by positivity)

include hφ hEnd1 hEnds hhom hc hlower hupper hL hend in
/-- One common truncation level gives the full literal ambient domain and
its actual arbitrary-completion inclusion markings for every independent
coefficient and retained potential parameter and every finite K ≥ 0.
The selected markings here are pointwise; joint parameter smoothness is
a separate statement. -/
theorem ToricInput.coefficientPath_potentialPath_exists_potentialAmbient_markings (I : ToricInput n) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ s : ℝ, ∀ hs : s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ K : ℝ, ∀ hK : 0 ≤ K, ∀ A : ℝ, A₀ ≤ A →
      ∃ hpos : ∀ y : (lgManifold n).Point,
        A ≤ potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 →
        0 < (lgManifold n).scalarDerivative
          (fun y => potentialPath (fun x => realSquaredNorm x / 2) φ s y.1) y
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm (potentialPath (fun x => realSquaredNorm x / 2) φ s))
            (W (I.alongCoefficientPath t)) K) y),
      let Damb := potentialPath_W_ambientOutwardDomain hφ hEnd1 hEnds hhom hc hlower hL hend
        s hs (I.alongCoefficientPath t) hK A hpos
      let Pamb := potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnds hhom hc hlower hupper
        hL hend s hs (I.alongCoefficientPath t) hK
      Damb.domain.carrier = {y : LGSpace n |
          potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 ≤ A} ∧
        Nonempty (Completion Damb) ∧ ∀ C : Completion Damb,
          Nonempty (InclusionMarking C Pamb.toCompleteLiouvilleManifold (fun y => y.val)) := by
  obtain ⟨A₀, hA₀, hout⟩ := ToricInput.coefficientPath_potentialPath_ambient_outward
    hφ hEnds hhom hc hlower hupper hL hend I
  refine ⟨A₀, hA₀, ?_⟩
  intro s hs t ht K hK A hA
  have hpos : ∀ y : (lgManifold n).Point,
      A ≤ potentialPath (fun x => realSquaredNorm x / 2) φ s y.1 →
      0 < (lgManifold n).scalarDerivative
        (fun y => potentialPath (fun x => realSquaredNorm x / 2) φ s y.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm (potentialPath (fun x => realSquaredNorm x / 2) φ s))
          (W (I.alongCoefficientPath t)) K) y) :=
    fun y hy => hout s hs t ht K hK y (hA.trans hy)
  refine ⟨hpos, ?_, ?_, ?_⟩
  · exact potential_W_ambientOutwardDomain_carrier (potentialPath_native_contDiff hφ s)
      (potentialPath_native_end_contDiff hEnd1 s) (potentialPath_native_end_contDiffAt hEnds s)
      (potentialPath_native_end_homogeneous hhom s) (lt_min zero_lt_one hc)
      (potentialPath_native_hessian_lowerBound hφ hlower hs) hL (potentialPath_native_eq_end hend s)
      (I.alongCoefficientPath t) hK A hpos
  · exact ⟨potential_W_ambientOutwardCompletion (potentialPath_native_contDiff hφ s)
      (potentialPath_native_end_contDiff hEnd1 s) (potentialPath_native_end_contDiffAt hEnds s)
      (potentialPath_native_end_homogeneous hhom s) (lt_min zero_lt_one hc)
      (zero_lt_one.trans_le (le_max_left _ _)) (potentialPath_native_hessian_lowerBound hφ hlower hs)
      (potentialPath_native_hessian_upperBound hφ hupper hs) hL (potentialPath_native_eq_end hend s)
      (I.alongCoefficientPath t) hK A hpos⟩
  · intro C
    exact ⟨potential_W_ambientOutwardInclusionMarkingOfCompletion (potentialPath_native_contDiff hφ s)
      (potentialPath_native_end_contDiff hEnd1 s) (potentialPath_native_end_contDiffAt hEnds s)
      (potentialPath_native_end_homogeneous hhom s) (lt_min zero_lt_one hc)
      (zero_lt_one.trans_le (le_max_left _ _)) (potentialPath_native_hessian_lowerBound hφ hlower hs)
      (potentialPath_native_hessian_upperBound hφ hupper hs) hL (potentialPath_native_eq_end hend s)
      (I.alongCoefficientPath t) hK A hpos C⟩

end RetainedPath
end FsFltz.Geometry
