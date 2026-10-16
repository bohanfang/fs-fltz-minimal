import FsFltz.Geometry.TailoringConormalRadial
import FsFltz.Geometry.TailoringCriticalTorusSmooth
import FsFltz.Geometry.ConormalRadialTangent
import FsFltz.Analysis.SmoothImplicitNeighborhood
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-! # Actual embedded whole-torus conormal branches

Source: `geometric-part-fsf-proof.tex`, `lem:radial`, lines 1613–1617,
`lem:invariance`, lines 1625–1633, and `lem:stable`, lines 1709–1718.
The full-span branch is constructed by removing the redundant radial
parameter in the actual Legendre map, and using the integral face torus.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Filter Function TopologicalSpace
open scoped BigOperators ContDiff Topology Manifold

variable {n : ℕ}

/-- The affine momentum directions transverse to one radial ray. -/
def conormalTransverseSpace (V : Submodule ℝ (RealSpace n))
    (ℓ : RealSpace n →L[ℝ] ℝ) : Submodule ℝ (RealSpace n) := V ⊓ ℓ.ker

/-- The redundant radial graph has one genuinely smooth ambient neighborhood. -/
theorem tailoringRadialFunction_exists_smooth_radialNeighborhood
    (I : ToricInput n) (β : ℝ) (u : RealSpace n)
    (hu : tailoringRadialFunction I β u = 1)
    (hd : 0 < fderiv ℝ (tailoringRadialFunction I β) u u) :
    ∃ (r : RealSpace n → ℝ) (U : Set (RealSpace n)) (O : Set (RealSpace n × ℝ)),
      IsOpen U ∧ u ∈ U ∧ IsOpen O ∧ (u, 1) ∈ O ∧
      ContDiffOn ℝ ∞ r U ∧ r u = 1 ∧
      (∀ w ∈ U, (w, r w) ∈ O ∧ tailoringRadialFunction I β (r w • w) = 1) ∧
      (∀ z ∈ O, tailoringRadialFunction I β (z.2 • z.1) = 1 ↔ r z.1 = z.2) := by
  let f : RealSpace n × ℝ → ℝ := fun z => tailoringRadialFunction I β (z.2 • z.1)
  have hc : ContDiff ℝ ∞ f :=
    (contDiff_tailoringRadialFunction I β).comp (contDiff_snd.smul contDiff_fst)
  let d := fderiv ℝ (tailoringRadialFunction I β) u u
  have he : fderiv ℝ f (u, 1) ∘L ContinuousLinearMap.inr ℝ (RealSpace n) ℝ =
      d • ContinuousLinearMap.id ℝ ℝ := by
    have hr := (hc.differentiable (by simp) (u, 1)).hasFDerivAt.comp 1
      ((hasFDerivAt_const u (1 : ℝ)).prodMk (hasFDerivAt_id (1 : ℝ)))
    have hr' := (hasDerivAt_tailoringRadialFunction_ray I β u 1).hasFDerivAt
    have hder := hr.unique (by simpa only [f, Function.comp_def, one_smul] using hr')
    convert hder using 1
    · congr 1
    · ext
      simp [d, mul_comm]
  have hi : (fderiv ℝ f (u, 1) ∘L ContinuousLinearMap.inr ℝ (RealSpace n) ℝ).IsInvertible := by
    rw [he]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [smul_smul, ne_of_gt hd, d]
    · ext
      simp [smul_smul, ne_of_gt hd, d]
  obtain ⟨r, U, O, hU, huU, hO, huO, hr, hru, hg, heq⟩ :=
    exists_smooth_implicit_neighborhood hc hi
  refine ⟨r, U, O, hU, huU, hO, huO, hr, hru, ?_, ?_⟩
  · intro w hw
    simpa only [f, one_smul, hu] using hg w hw
  · intro z hz
    simpa only [f, one_smul, hu] using heq z hz

/-- Normalize momentum using a globally continuous denominator, agreeing
with the smooth normalization near every branch point. -/
def conormalNormalize (Φ : RealSpace n ≃ₜ RealSpace n)
    (p₀ : RealSpace n) (ℓ : RealSpace n →L[ℝ] ℝ)
    (K : Submodule ℝ (RealSpace n)) (P : RealSpace n →L[ℝ] K)
    (u : RealSpace n) : K :=
  P ((max (1 / 2 : ℝ) (ℓ (Φ u)))⁻¹ • Φ u - p₀)

theorem continuous_conormalNormalize (Φ : RealSpace n ≃ₜ RealSpace n)
    (p₀ : RealSpace n) (ℓ : RealSpace n →L[ℝ] ℝ)
    (K : Submodule ℝ (RealSpace n)) (P : RealSpace n →L[ℝ] K) :
    Continuous (conormalNormalize Φ p₀ ℓ K P) := by
  apply P.continuous.comp
  exact ((continuous_const.max (ℓ.continuous.comp Φ.continuous)).inv₀
    (fun u => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (le_max_left _ _)))).smul Φ.continuous |>.sub continuous_const

/-- On the affine slice, degree-one homogeneity makes the normalization
an actual left inverse of the radial map. -/
theorem conormalNormalize_radialGraph
    (Φ : RealSpace n ≃ₜ RealSpace n) (p₀ : RealSpace n)
    (ℓ : RealSpace n →L[ℝ] ℝ) (hℓ : ℓ p₀ = 1)
    (V : Submodule ℝ (RealSpace n))
    (P : RealSpace n →L[ℝ] conormalTransverseSpace V ℓ)
    (hP : LeftInverse P (conormalTransverseSpace V ℓ).subtypeL)
    (hhom : ∀ t : ℝ, 0 < t → ∀ w, Φ (t • w) = t • Φ w)
    (r : RealSpace n → ℝ) (q : conormalTransverseSpace V ℓ)
    (hr : 1 / 2 < r (Φ.symm (p₀ + q))) :
    conormalNormalize Φ p₀ ℓ _ P
      (r (Φ.symm (p₀ + q)) • Φ.symm (p₀ + q)) = q := by
  have hq : ℓ (q : RealSpace n) = 0 := q.property.2
  have ht : 0 < r (Φ.symm (p₀ + q)) := by linarith
  simp only [conormalNormalize, hhom _ ht, Homeomorph.apply_symm_apply,
    map_smul, map_add, hℓ, hq, add_zero, smul_eq_mul, mul_one, max_eq_right hr.le]
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul, add_sub_cancel_left]
  exact hP q

/-! The following construction is analytic and keeps the actual homeomorphism
and radial graph in its conclusion, so no branch is supplied as input. -/

/-- An affine full-span slice gives an embedded smooth radial section with
an explicit ambient normalization and injective native differential. -/
theorem exists_embedded_legendre_radialBranch
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n)))
    (hhom : ∀ t : ℝ, 0 < t → ∀ w, Φ (t • w) = t • Φ w)
    (p₀ : RealSpace n) (V : Submodule ℝ (RealSpace n)) (hp₀ : p₀ ∈ V)
    (ℓ : RealSpace n →L[ℝ] ℝ) (hℓ : ℓ p₀ = 1)
    (r : RealSpace n → ℝ) (U : Set (RealSpace n)) (hU : IsOpen U)
    (huU : Φ.symm p₀ ∈ U) (hr : ContDiffOn ℝ ∞ r U) (hr₀ : r (Φ.symm p₀) = 1) :
    ∃ (B : Opens (conormalTransverseSpace V ℓ))
      (g : conormalTransverseSpace V ℓ → RealSpace n)
      (P : RealSpace n →L[ℝ] conormalTransverseSpace V ℓ),
      LeftInverse P (conormalTransverseSpace V ℓ).subtypeL ∧
      (0 : conormalTransverseSpace V ℓ) ∈ B ∧ g 0 = Φ.symm p₀ ∧
      (∀ q, g q = r (Φ.symm (p₀ + q)) • Φ.symm (p₀ + q)) ∧
      (∀ q ∈ B, Φ.symm (p₀ + q) ∈ U ∧ 1 / 2 < r (Φ.symm (p₀ + q)) ∧
        ContDiffAt ℝ ∞ g q ∧ Φ (g q) ∈ V ∧
        conormalNormalize Φ p₀ ℓ _ P (g q) = q ∧
        ContDiffAt ℝ ∞ (conormalNormalize Φ p₀ ℓ _ P) (g q) ∧
        Injective (fderiv ℝ g q)) ∧
      Topology.IsEmbedding (fun q : B => g q) := by
  let K := conormalTransverseSpace V ℓ
  obtain ⟨P, hP⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (f := K.subtypeL) Subtype.val_injective
  let w : K → RealSpace n := fun q => Φ.symm (p₀ + q)
  let g : K → RealSpace n := fun q => r (w q) • w q
  have hw : Continuous w := Φ.symm.continuous.comp (continuous_const.add K.subtypeL.continuous)
  have hw₀ : w 0 = Φ.symm p₀ := by simp [w]
  have hp (q : K) : p₀ + (q : RealSpace n) ≠ 0 := by
    have hq : ℓ (q : RealSpace n) = 0 := q.property.2
    intro he
    have := congrArg ℓ he
    simp [map_add, hℓ, hq] at this
  have hws (q : K) : ContDiffAt ℝ ∞ w q := by
    exact (hΦinv.contDiffAt (isOpen_compl_singleton.mem_nhds (hp q))).comp q
      (contDiffAt_const.add K.subtypeL.contDiff.contDiffAt)
  have hnear : ∀ᶠ q in 𝓝 (0 : K), w q ∈ U ∧ 1 / 2 < r (w q) := by
    have hru : ContinuousAt r (Φ.symm p₀) :=
      (hr.contDiffAt (hU.mem_nhds huU)).continuousAt
    have hrc : ContinuousAt (fun q => r (w q)) (0 : K) := by
      have hru' : ContinuousAt r (w 0) := hw₀ ▸ hru
      exact hru'.comp hw.continuousAt
    have ht : ∀ᶠ q in 𝓝 (0 : K), 1 / 2 < r (w q) :=
      hrc (lt_mem_nhds (by change 1 / 2 < r (w 0); rw [hw₀, hr₀]; norm_num))
    exact (hw.tendsto 0 |>.eventually (by simpa [hw₀] using hU.mem_nhds huU)).and ht
  obtain ⟨B, hBsub, hBopen, h₀B⟩ := mem_nhds_iff.mp hnear
  let BO : Opens K := ⟨B, hBopen⟩
  have hleft (q : K) (hq : q ∈ B) : conormalNormalize Φ p₀ ℓ K P (g q) = q :=
    conormalNormalize_radialGraph Φ p₀ ℓ hℓ V P hP hhom r q (hBsub hq).2
  have hgs (q : K) (hq : q ∈ B) : ContDiffAt ℝ ∞ g q :=
    ((hr.contDiffAt (hU.mem_nhds (hBsub hq).1)).comp q (hws q)).smul (hws q)
  have hns (q : K) (hq : q ∈ B) :
      ContDiffAt ℝ ∞ (conormalNormalize Φ p₀ ℓ K P) (g q) := by
    have ht : 0 < r (w q) := by have := (hBsub hq).2; linarith
    have hwne : w q ≠ 0 := by
      intro he
      have := congrArg Φ he
      simp only [w, Homeomorph.apply_symm_apply, hΦ₀] at this
      exact hp q this
    have hgne : g q ≠ 0 := smul_ne_zero ht.ne' hwne
    have hΦs := hΦ.contDiffAt (isOpen_compl_singleton.mem_nhds hgne)
    have hell : 1 / 2 < ℓ (Φ (g q)) := by
      have hqℓ : ℓ (q : RealSpace n) = 0 := q.property.2
      simpa only [g, w, hhom _ ht, Homeomorph.apply_symm_apply, map_smul,
        map_add, hℓ, hqℓ, add_zero, smul_eq_mul, mul_one] using (hBsub hq).2
    have he : conormalNormalize Φ p₀ ℓ K P =ᶠ[𝓝 (g q)]
        (fun u => P ((ℓ (Φ u))⁻¹ • Φ u - p₀)) := by
      filter_upwards [(ℓ.continuous.comp Φ.continuous).tendsto (g q) |>.eventually
        (lt_mem_nhds hell)] with u hu
      change 1 / 2 < ℓ (Φ u) at hu
      simp only [conormalNormalize, max_eq_right hu.le]
    exact (P.contDiff.contDiffAt.comp (g q)
      ((((ℓ.contDiff.contDiffAt.comp (g q) hΦs).inv
        (by linarith : ℓ (Φ (g q)) ≠ 0)).smul hΦs).sub contDiffAt_const)).congr_of_eventuallyEq he
  have hgi (q : K) (hq : q ∈ B) : Injective (fderiv ℝ g q) := by
    have he : (conormalNormalize Φ p₀ ℓ K P) ∘ g =ᶠ[𝓝 q] id := by
      filter_upwards [hBopen.eventually_mem hq] with a ha
      exact hleft a ha
    have hd := ((hns q hq).differentiableAt (by simp)).hasFDerivAt.comp q
      ((hgs q hq).differentiableAt (by simp)).hasFDerivAt
    have hdid := hasFDerivAt_id (𝕜 := ℝ) q
    have hdeq := (hd.congr_of_eventuallyEq he.symm).unique hdid
    intro a b hab
    have h := congrArg (fun L : K →L[ℝ] K => L a - L b) hdeq
    simp only [ContinuousLinearMap.comp_apply, hab, sub_self,
      ContinuousLinearMap.id_apply] at h
    exact sub_eq_zero.mp h.symm
  refine ⟨BO, g, P, hP, h₀B, ?_, fun _ => rfl, ?_, ?_⟩
  · simp [g, hw₀, hr₀]
  · intro q hq
    have hq' : q ∈ B := hq
    refine ⟨(hBsub hq').1, (hBsub hq').2, hgs q hq', ?_, hleft q hq', hns q hq', hgi q hq'⟩
    have ht : 0 < r (w q) := by have := (hBsub hq').2; linarith
    change Φ (r (w q) • w q) ∈ V
    rw [hhom _ ht]
    change r (w q) • Φ (Φ.symm (p₀ + q)) ∈ V
    rw [Homeomorph.apply_symm_apply]
    exact V.smul_mem _ (V.add_mem hp₀ q.property.1)
  · have hgc : Continuous (fun q : BO => g q) := by
      apply continuous_iff_continuousAt.mpr
      intro q
      exact (hgs q q.property).continuousAt.comp continuousAt_subtype_val
    have hcomp : (conormalNormalize Φ p₀ ℓ K P) ∘ (fun q : BO => g q) = Subtype.val := by
      funext q
      exact hleft q q.property
    exact Topology.IsEmbedding.of_comp hgc (continuous_conormalNormalize Φ p₀ ℓ K P)
      (by rw [hcomp]; exact Topology.IsEmbedding.subtypeVal)

/-- Local uniqueness identifies the constructed radial image with the
literal full-span level section, rather than merely placing it inside that section. -/
theorem eventually_legendre_radialBranch_image
    (Φ : RealSpace n ≃ₜ RealSpace n)
    (hhom : ∀ t : ℝ, 0 < t → ∀ w, Φ (t • w) = t • Φ w)
    (p₀ : RealSpace n) (V : Submodule ℝ (RealSpace n)) (hp₀ : p₀ ∈ V)
    (ℓ : RealSpace n →L[ℝ] ℝ) (hℓ : ℓ p₀ = 1)
    (P : RealSpace n →L[ℝ] conormalTransverseSpace V ℓ)
    (hP : LeftInverse P (conormalTransverseSpace V ℓ).subtypeL)
    (ρ : RealSpace n → ℝ) (r : RealSpace n → ℝ)
    (O : Set (RealSpace n × ℝ)) (hO : IsOpen O) (huO : (Φ.symm p₀, 1) ∈ O)
    (hunique : ∀ z ∈ O, ρ (z.2 • z.1) = 1 ↔ r z.1 = z.2)
    (B : Opens (conormalTransverseSpace V ℓ)) (h₀B : (0 : conormalTransverseSpace V ℓ) ∈ B)
    (g : conormalTransverseSpace V ℓ → RealSpace n)
    (hg : ∀ q, g q = r (Φ.symm (p₀ + q)) • Φ.symm (p₀ + q)) :
    ∀ᶠ u in 𝓝 (Φ.symm p₀), Φ u ∈ V → ρ u = 1 →
      conormalNormalize Φ p₀ ℓ _ P u ∈ B ∧
      g (conormalNormalize Φ p₀ ℓ _ P u) = u := by
  let K := conormalTransverseSpace V ℓ
  let N := conormalNormalize Φ p₀ ℓ K P
  let t : RealSpace n → ℝ := fun u => ℓ (Φ u)
  have ht₀ : t (Φ.symm p₀) = 1 := by simp [t, hℓ]
  have htc : Continuous t := ℓ.continuous.comp Φ.continuous
  have hN₀ : N (Φ.symm p₀) = 0 := by
    simp only [N, conormalNormalize, Homeomorph.apply_symm_apply, hℓ,
      max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1), inv_one, one_smul,
      sub_self, map_zero]
  have hNc : Continuous N := continuous_conormalNormalize Φ p₀ ℓ K P
  have hNnear : ∀ᶠ u in 𝓝 (Φ.symm p₀), N u ∈ B :=
    hNc.tendsto _ |>.eventually
      (by rw [hN₀]; exact B.isOpen.eventually_mem h₀B)
  have hwc : ContinuousAt (fun u => (t u)⁻¹ • u) (Φ.symm p₀) :=
    (htc.continuousAt.inv₀ (by rw [ht₀]; norm_num)).smul continuousAt_id
  have hpair : Tendsto (fun u => ((t u)⁻¹ • u, t u))
      (𝓝 (Φ.symm p₀)) (𝓝 (Φ.symm p₀, 1)) := by
    simpa only [ht₀, inv_one, one_smul] using (hwc.prodMk htc.continuousAt).tendsto
  filter_upwards [hNnear, htc.tendsto (Φ.symm p₀) |>.eventually
    (lt_mem_nhds (by rw [ht₀]; norm_num : 1 / 2 < t (Φ.symm p₀))),
    hpair.eventually (hO.mem_nhds huO)] with u hNu htu hpu
  intro hVu hρu
  have htpos : 0 < t u := by linarith
  have htr : t u ≠ 0 := htpos.ne'
  let q : K := ⟨(t u)⁻¹ • Φ u - p₀,
    V.sub_mem (V.smul_mem _ hVu) hp₀, by
      change ℓ ((t u)⁻¹ • Φ u - p₀) = 0
      simp only [map_sub, map_smul, hℓ, smul_eq_mul]
      change (t u)⁻¹ * t u - 1 = 0
      rw [inv_mul_cancel₀ htr, sub_self]⟩
  have hNq : N u = q := by
    change P ((max (1 / 2 : ℝ) (t u))⁻¹ • Φ u - p₀) = q
    rw [max_eq_right htu.le]
    exact hP q
  have hw : Φ.symm (p₀ + (q : RealSpace n)) = (t u)⁻¹ • u := by
    apply Φ.injective
    rw [Homeomorph.apply_symm_apply, hhom _ (inv_pos.mpr htpos)]
    simp [q]
  have hscale : t u • ((t u)⁻¹ • u) = u := by
    rw [smul_smul, mul_inv_cancel₀ htr, one_smul]
  have hr : r ((t u)⁻¹ • u) = t u :=
    (hunique _ hpu).mp (by simpa only [hscale] using hρu)
  refine ⟨hNu, ?_⟩
  change g (N u) = u
  rw [hNq, hg, hw, hr, hscale]

/-- The full face-torus branch is constructed in the actual endpoint fiber.
It extends in the full real face span, has a smooth ambient inverse near
its image, and includes every quotient angle of the critical torus. -/
theorem IsStronglyCompatibleEndPotential.eventually_exists_embedded_conormalBranch
    {I : ToricInput n} {φ : RealSpace n → ℝ}
    (hφ : IsStronglyCompatibleEndPotential I φ)
    (Φ : RealSpace n ≃ₜ RealSpace n) (hΦeq : ∀ u, Φ u = coordinateGradient φ u)
    (hΦ₀ : Φ 0 = 0)
    (hΦ : ContDiffOn ℝ ∞ Φ ({0}ᶜ : Set (RealSpace n)))
    (hΦinv : ContDiffOn ℝ ∞ Φ.symm ({0}ᶜ : Set (RealSpace n))) :
    ∀ᶠ β in atTop, ∀ s : Finset (Lattice n),
      IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ y : LGSpace n, Φ y.1 ∈ positiveCone s → y.2 ∈ coneTorus (positiveCone s) →
      tailoringFamily I β 1 y = 1 →
      ∀ ℓ : RealSpace n →L[ℝ] ℝ, ℓ (Φ y.1) = 1 →
      ∃ (B : Opens (conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ))
        (g : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ → RealSpace n)
        (f : Torus (n - s.card) → Torus n)
        (R : LGSpace n →
          conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ × Torus (n - s.card)),
        (0 : conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ) ∈ B ∧
        g 0 = y.1 ∧ range f = coneTorus (positiveCone s) ∧ Continuous R ∧
        Topology.IsEmbedding (Prod.map (fun q : B => g q) f) ∧
        range (fderiv ℝ g 0) = {v | fderiv ℝ Φ y.1 v ∈ Submodule.span ℝ (positiveCone s) ∧
          fderiv ℝ (tailoringRadialFunction I β) y.1 v = 0} ∧
        (∀ q ∈ B, ∀ θ : Torus (n - s.card),
          ContMDiffAt ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
            (torusModel (n - s.card))) (lgModel n) ∞ (Prod.map g f) (q, θ) ∧
          Injective (mfderiv
            ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
              (torusModel (n - s.card))) (lgModel n) (Prod.map g f) (q, θ)) ∧
          tailoringFamily I β 1 (g q, f θ) = 1 ∧
          Φ (g q) ∈ Submodule.span ℝ (positiveCone s) ∧
          range (fderiv ℝ g q) = {v | fderiv ℝ Φ (g q) v ∈ Submodule.span ℝ (positiveCone s) ∧
            fderiv ℝ (tailoringRadialFunction I β) (g q) v = 0} ∧
          R (g q, f θ) = (q, θ) ∧
          ContMDiffAt (lgModel n)
            ((𝓘(ℝ, conormalTransverseSpace (Submodule.span ℝ (positiveCone s)) ℓ)).prod
              (torusModel (n - s.card))) ∞ R (g q, f θ)) ∧
        (∀ᶠ u in 𝓝 y.1, ∀ θ : Torus n,
          (u, θ) ∈ range (Prod.map (fun q : B => g q) f) ↔
            tailoringFamily I β 1 (u, θ) = 1 ∧
            Φ u ∈ Submodule.span ℝ (positiveCone s) ∧ θ ∈ coneTorus (positiveCone s)) := by
  have hN : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  let L := Real.log (2 * (I.vertices.card : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by
    have : (1 : ℝ) ≤ I.vertices.card := by
      exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
    linarith)
  have hlog : Real.log (I.vertices.card : ℝ) ≤ L := Real.log_le_log hN (by linarith)
  have hhom (t : ℝ) (ht : 0 < t) (w : RealSpace n) : Φ (t • w) = t • Φ w := by
    by_cases hw : w = 0
    · simp [hw, hΦ₀]
    · simp only [hΦeq]
      exact coordinateGradient_smul_of_homogeneous_two hφ.homogeneous
        (fun x hx => (hφ.smooth x hx).differentiableAt (by simp)) hw ht
  filter_upwards [hφ.eventually_conormal_family_germ,
    hφ.eventually_cone_family_eq_radial,
    tailoringRadialFunction_eventually_radial_positive I hL] with β hgerm hradial hpositive
  intro s hs hsne hsproper y hp hθ hy ℓ hℓ
  let σ := positiveCone s
  have hσ : σ ∈ faceFan I := Or.inr ⟨s, hs, hsne, hsproper, rfl⟩
  have hgrad : coordinateGradient φ y.1 ∈ σ := by rwa [← hΦeq]
  have hh : β - L ≤ supportHeight I y.1 := by
    have := tailoringEndpoint_height_lower I β y hy
    linarith
  have hu : tailoringRadialFunction I β y.1 = 1 := by
    have he := hradial σ hσ y hgrad hθ hh
    rw [hy] at he
    exact_mod_cast he.symm
  obtain ⟨r, U, O, hU, huU, hO, huO, hr, hru, hgraph, hunique⟩ :=
    tailoringRadialFunction_exists_smooth_radialNeighborhood I β y.1 hu (hpositive y.1 hh)
  have hrAt := hr.contDiffAt (hU.mem_nhds huU)
  have ht : Tendsto (fun w => r w • w) (𝓝 y.1) (𝓝 y.1) := by
    have hc : ContinuousAt (fun w => r w • w) y.1 :=
      hrAt.continuousAt.smul continuousAt_id
    simpa only [ContinuousAt, hru, one_smul] using hc
  have hQc : Continuous (fun u => fderiv ℝ (tailoringRadialFunction I β) u u) :=
    ((contDiff_tailoringRadialFunction I β).continuous_fderiv (by simp)).clm_apply continuous_id
  have hactual : ∀ᶠ w in 𝓝 y.1, w ∈ U ∧ (∀ θ ∈ coneTorus σ,
      tailoringFamily I β 1 (r w • w, θ) = 1) ∧
      0 < fderiv ℝ (tailoringRadialFunction I β) (r w • w) (r w • w) := by
    filter_upwards [hU.eventually_mem huU,
      ht.eventually (hgerm σ hσ y hgrad hθ hy),
      ht.eventually (hQc.tendsto y.1 |>.eventually (lt_mem_nhds (hpositive y.1 hh)))]
        with w hw hg hpos
    refine ⟨hw, (fun θ hθ' => ?_), hpos⟩
    rw [hg θ hθ', (hgraph w hw).2, Complex.ofReal_one]
  obtain ⟨U', hU'sub, hU'open, huU'⟩ := mem_nhds_iff.mp hactual
  have hr' : ContDiffOn ℝ ∞ r U' := hr.mono (fun w hw => (hU'sub hw).1)
  let V := Submodule.span ℝ σ
  obtain ⟨B, g, P, hP, h₀B, hg₀, hgdef, hgprops, hge⟩ :=
    exists_embedded_legendre_radialBranch Φ hΦ₀ hΦ hΦinv hhom (Φ y.1) V
      (Submodule.subset_span hp) ℓ hℓ r U' hU'open
      (by simpa using huU') hr' (by simpa using hru)
  obtain ⟨f, a, hf, ha, hleft, hfe, hfi, hfrange⟩ :=
    I.exists_smooth_coneTorus_parametrization hs hsne hsproper
  let K := conormalTransverseSpace V ℓ
  let R : LGSpace n → K × Torus (n - s.card) :=
    Prod.map (conormalNormalize Φ (Φ y.1) ℓ K P) a
  have hTangent (q : K) (hq : q ∈ B) :
      range (fderiv ℝ g q) = {v | fderiv ℝ Φ (g q) v ∈ V ∧
        fderiv ℝ (tailoringRadialFunction I β) (g q) v = 0} := by
    have hgpos : 0 < fderiv ℝ (tailoringRadialFunction I β) (g q) (g q) := by
      rw [hgdef]
      exact (hU'sub (hgprops q hq).1).2.2
    have hgneq : g q ≠ 0 := by
      intro he
      rw [he, map_zero] at hgpos
      exact lt_irrefl 0 hgpos
    have hpneq : Φ (g q) ≠ 0 := by
      intro he
      exact hgneq (Φ.injective (he.trans hΦ₀.symm))
    have hΦgAt := hΦ.contDiffAt (isOpen_compl_singleton.mem_nhds hgneq)
    obtain ⟨Hq, hHq⟩ := exists_fderiv_equiv_of_homeomorph Φ (g q)
      (hΦgAt.differentiableAt (by simp))
      ((hΦinv.contDiffAt (isOpen_compl_singleton.mem_nhds hpneq)).differentiableAt (by simp))
    have hHqder : HasFDerivAt Φ (Hq : RealSpace n →L[ℝ] RealSpace n) (g q) := by
      rw [hHq]
      exact hΦgAt.differentiableAt (by simp) |>.hasFDerivAt
    have hEulerq : Hq (g q) = Φ (g q) := by
      change (Hq : RealSpace n →L[ℝ] RealSpace n) (g q) = Φ (g q)
      rw [hHq]
      have hΦfun : (Φ : RealSpace n → RealSpace n) = coordinateGradient φ := funext hΦeq
      rw [hΦfun]
      exact coordinateHessian_apply_self_of_homogeneous_two hφ.homogeneous
        (fun x hx => (hφ.smooth x hx).differentiableAt (by simp)) hgneq
        (by simpa only [hΦfun] using hΦgAt.differentiableAt (by simp))
    let α : K → ℝ := fun a => ℓ (Φ (g a))
    have hα : DifferentiableAt ℝ α q :=
      ℓ.differentiableAt.comp q ((hΦgAt.differentiableAt (by simp)).comp q
        ((hgprops q hq).2.2.1.differentiableAt (by simp)))
    have hPhiGraph (a : K) (haB : a ∈ B) : Φ (g a) = α a • (Φ y.1 + a) := by
      have hrt := (hgprops a haB).2.1
      have ht : 0 < r (Φ.symm (Φ y.1 + a)) := by linarith
      have haℓ : ℓ (a : RealSpace n) = 0 := a.property.2
      have hΦga : Φ (g a) = r (Φ.symm (Φ y.1 + a)) • (Φ y.1 + a) := by
        rw [hgdef, hhom _ ht, Homeomorph.apply_symm_apply]
      have heℓ : α a = r (Φ.symm (Φ y.1 + a)) := by
        change ℓ (Φ (g a)) = _
        rw [hΦga, ℓ.map_smul, ℓ.map_add, hℓ, haℓ]
        simp
      rw [heℓ]
      exact hΦga
    have hαpos : 0 < α q := by
      have hqℓ : ℓ (q : RealSpace n) = 0 := q.property.2
      have ht : 0 < r (Φ.symm (Φ y.1 + q)) := by have := (hgprops q hq).2.1; linarith
      change 0 < ℓ (Φ (g q))
      rw [hgdef, hhom _ ht, Homeomorph.apply_symm_apply, ℓ.map_smul, ℓ.map_add, hℓ, hqℓ]
      simpa using ht
    have hlevel (a : K) (haB : a ∈ B) : tailoringRadialFunction I β (g a) = 1 := by
      rw [hgdef]
      exact (hgraph _ (hU'sub (hgprops a haB).1).1).2
    have hres := fullSpan_section_fderiv_range_at V ℓ K rfl (Φ y.1)
      (Submodule.subset_span hp) hℓ B B.isOpen q hq g
      (fun a haB => (hgprops a haB).2.2.1.differentiableAt (by simp)) α hα hαpos
      Φ Hq hHqder hEulerq hPhiGraph (tailoringRadialFunction I β)
      (fderiv ℝ (tailoringRadialFunction I β) (g q))
      ((contDiff_tailoringRadialFunction I β).differentiable (by simp) (g q) |>.hasFDerivAt)
      hgpos.ne' hlevel
    simpa only [ContinuousLinearEquiv.coe_coe, ← hHq] using hres
  refine ⟨B, g, f, R, h₀B, ?_, hfrange, ?_, hge.prodMap hfe, ?_, ?_, ?_⟩
  · simpa using hg₀
  · exact (continuous_conormalNormalize Φ (Φ y.1) ℓ K P).prodMap ha.continuous
  · have hgzero : g 0 = y.1 := by simpa using hg₀
    simpa only [hgzero] using hTangent 0 h₀B
  · intro q hq θ
    obtain ⟨hwU', hrt, hgs, hpV, hnorm, hns, hgi⟩ := hgprops q hq
    have hj : ContMDiffAt ((𝓘(ℝ, K)).prod (torusModel (n - s.card)))
        (lgModel n) ∞ (Prod.map g f) (q, θ) := hgs.contMDiffAt.prodMap (hf θ)
    refine ⟨hj, ?_, ?_, hpV, hTangent q hq, ?_, hns.contMDiffAt.prodMap (ha (f θ))⟩
    · rw [mfderiv_prodMap (hgs.contMDiffAt.mdifferentiableAt (by simp))
        ((hf θ).mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
      intro X Y hXY
      apply Prod.ext
      · exact hgi (congrArg Prod.fst hXY)
      · exact hfi θ (congrArg Prod.snd hXY)
    · have hfθ : f θ ∈ coneTorus σ := by rw [← hfrange]; exact mem_range_self θ
      rw [hgdef]
      exact (hU'sub hwU').2.1 (f θ) hfθ
    · change (conormalNormalize Φ (Φ y.1) ℓ K P (g q), a (f θ)) = (q, θ)
      rw [hnorm, hleft]
  · have himage := eventually_legendre_radialBranch_image Φ hhom (Φ y.1) V
      (Submodule.subset_span hp) ℓ hℓ P hP (tailoringRadialFunction I β) r O hO
      (by simpa using huO) hunique B h₀B g hgdef
    simp only [Homeomorph.symm_apply_apply] at himage
    filter_upwards [himage, hgerm σ hσ y hgrad hθ hy] with u huimg hugerm
    intro θ
    constructor
    · rintro ⟨⟨q, α⟩, h⟩
      have hug : g q = u := congrArg Prod.fst h
      have hθα : f α = θ := congrArg Prod.snd h
      have hfα : f α ∈ coneTorus σ := by rw [← hfrange]; exact mem_range_self α
      refine ⟨?_, ?_, hθα ▸ hfα⟩
      · rw [← hug, ← hθα, hgdef]
        exact (hU'sub (hgprops q q.property).1).2.1 (f α) hfα
      · rw [← hug]
        exact (hgprops q q.property).2.2.2.1
    · rintro ⟨hfu, hVu, hθu⟩
      have hρu : tailoringRadialFunction I β u = 1 := by
        have he := hugerm θ hθu
        rw [hfu] at he
        exact_mod_cast he.symm
      obtain ⟨hNu, hgNu⟩ := huimg hVu hρu
      obtain ⟨α, hα⟩ : θ ∈ range f := by rwa [hfrange]
      exact ⟨(⟨conormalNormalize Φ (Φ y.1) ℓ K P u, hNu⟩, α), Prod.ext hgNu hα⟩

end FsFltz
