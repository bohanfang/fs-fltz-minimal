import FsFltz.Geometry.SubmersionProductCoordinates
import FsFltz.Geometry.BilinearNormalTrapping

/-!
# Nonlinear expansion from an actual transverse defining map

Source: `geometric-part-fsf-proof.tex`, `lem:trapping`, lines 1672–1696.
The inverse function theorem supplies local coordinates, and an actual
rate vanishing on the defining zero set supplies the zero-section equation.
The critical-torus consumer uses its fixed normal lift and bilinear metric.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Topology ContDiff
namespace FsFltz.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Strict positivity of the normal derivative gives a nonlinear estimate
for the original defining map and rate, on a constructed neighborhood. -/
theorem exists_submersion_rate_expansion
    (δ R : E → F) (a : E) (A : E →L[ℝ] F) (L : F →L[ℝ] E)
    (G : F →L[ℝ] F →L[ℝ] ℝ)
    (hL : RightInverse L A) (hδ : ContDiffAt ℝ ∞ δ a)
    (hA : HasFDerivAt δ A a) (hzero : δ a = 0)
    (hR : ContDiffAt ℝ 1 R a)
    (hRzero : ∀ᶠ y in 𝓝 a, δ y = 0 → R y = 0)
    (hpos : ∀ v : F, v ≠ 0 → 0 < G (fderiv ℝ R a (L v)) v) :
    ∃ b : ℝ, 0 < b ∧ ∃ U : Set E, IsOpen U ∧ a ∈ U ∧
      ∀ y ∈ U, b * ‖δ y‖ ^ 2 ≤ G (R y) (δ y) := by
  obtain ⟨e, ha, ht, hezero, he, hs, hd, hdinr, hsecond⟩ :=
    exists_submersion_product_coordinates δ a A L hL hδ hA hzero
  have hea : e.symm 0 = a := by rw [← hezero, e.left_inv ha]
  let w : A.ker × F → F := fun p => R (e.symm p)
  let D : A.ker × F → F →L[ℝ] F := fun p =>
    (fderiv ℝ w p).comp (ContinuousLinearMap.inr ℝ A.ker F)
  have hw : ContDiffAt ℝ 1 w 0 := (hea.symm ▸ hR).comp 0 (hs.of_le (by simp))
  have hnear : ∀ᶠ p : A.ker × F in 𝓝 0,
      p ∈ e.target ∧ ContDiffAt ℝ 1 w p ∧ (δ (e.symm p) = 0 → R (e.symm p) = 0) := by
    have hz := hs.continuousAt.eventually (hea.symm ▸ hRzero)
    filter_upwards [e.open_target.mem_nhds ht, hw.eventually (by simp), hz] with p hp hwp hzp
    exact ⟨hp, hwp, hzp⟩
  obtain ⟨O, hOsub, hO, h₀O⟩ := mem_nhds_iff.mp hnear
  have hDc : ContinuousAt D 0 :=
    (hw.continuousAt_fderiv (by simp)).clm_comp continuousAt_const
  have hnormal : D 0 = (fderiv ℝ R a).comp L := by
    have hRa : HasFDerivAt R (fderiv ℝ R a) (e.symm 0) :=
      hea.symm ▸ (hR.differentiableAt (by simp)).hasFDerivAt
    have hchain := hRa.comp 0 hd
    change (fderiv ℝ w 0).comp _ = _
    change HasFDerivAt w _ 0 at hchain
    rw [hchain.fderiv, ContinuousLinearMap.comp_assoc, ← hd.fderiv, hdinr]
  obtain ⟨b, hb, V, hV, h₀V, hVO, hbounded, hexpand⟩ :=
    exists_local_bilinear_normal_expansion_tube G ({0} : Set A.ker) isCompact_singleton
      O hO (by
        rintro ⟨s, v⟩ ⟨rfl, rfl⟩
        exact h₀O) w D (fun s v hv => by
        have hp := (hOsub hv).2.1.differentiableAt (by simp)
        exact hp.hasFDerivAt.comp v ((hasFDerivAt_const s v).prodMk (hasFDerivAt_id v)))
      (fun c hc => by
        rcases mem_singleton_iff.mp hc with rfl
        exact hDc)
      (fun s hsO => (hOsub hsO).2.2 (by simpa using hsecond (s, 0) (hOsub hsO).1))
      (fun c hc v hv => by
        have hc0 : c = 0 := mem_singleton_iff.mp hc
        subst c
        simpa only [Prod.mk_zero_zero, hnormal, ContinuousLinearMap.comp_apply] using hpos v hv)
  have hn : e.source ∩ e ⁻¹' V ∈ 𝓝 a :=
    inter_mem (e.open_source.mem_nhds ha)
      ((e.continuousAt ha).preimage_mem_nhds (hV.mem_nhds (by
        rw [hezero]
        exact h₀V ⟨mem_singleton 0, mem_singleton 0⟩)))
  obtain ⟨U, hUsub, hU, haU⟩ := mem_nhds_iff.mp hn
  refine ⟨b, hb, U, hU, haU, ?_⟩
  intro y hy
  have hx := hexpand (e y) (hUsub hy).2
  have hsy : (e y).2 = δ y := congrArg Prod.snd (he y)
  simpa only [w, e.left_inv (hUsub hy).1, hsy] using hx

end FsFltz.Geometry
