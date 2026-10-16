import FsFltz.Geometry.IntrinsicBoundary
import FsFltz.Geometry.LiouvilleLocalFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Local inward integration in intrinsic boundary coordinates

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Smooth extension of the local coefficients is
kept explicit, in accordance with lines 119–122 and 141. These are local
Euclidean coefficient extensions, not an extension manifold of the domain.
The trajectories and their inward side are constructed from the coefficients.
Uniform gluing of these charts and a boundaryless domain extension remain
separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

/-- A coefficient field smooth on an actual open neighborhood has a
constructed smooth auxiliary action. Near the chosen point and for a
common two-sided time interval, this action solves the original ODE and
stays in the specified open neighborhood. -/
theorem exists_local_flow_of_contDiffOn {n : ℕ} {f : Model n → Model n}
    {U : Set (Model n)} {a : Model n} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U) :
    ∃ F : Flow ℝ (Model n),
      ContDiff ℝ ∞ (fun p : ℝ × Model n => F p.1 p.2) ∧
      ∃ V : Set (Model n), IsOpen V ∧ a ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ V, ∀ t ∈ Ioo (-δ) δ,
          F t x ∈ U ∧ HasDerivAt (fun s => F s x) (f (F t x)) t := by
  obtain ⟨χ, W, hχ, haW, hone, hsupport, hsub⟩ :=
    CollarExtension.exists_smooth_compact_cutoff (I := 𝓘(ℝ, Model n))
      isCompact_singleton hU (singleton_subset_iff.mpr ha)
  let g : Model n → Model n := fun x => χ x • f x
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsub hx)))
    · apply (contDiffAt_const (c := (0 : Model n))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [g, hy, Pi.zero_apply, zero_smul]
  have hgs : ContMDiff 𝓘(ℝ, Model n) (𝓘(ℝ, Model n)).tangent ∞
      (fun x => (⟨x, g x⟩ : TangentBundle 𝓘(ℝ, Model n) (Model n))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hg
  obtain ⟨F, hF, hode⟩ := CollarFlow.exists_supported_smoothFlow g hgs hsupport
    (fun x hx => by simp only [g, image_eq_zero_of_notMem_tsupport hx, zero_smul])
  have hFc : ContDiff ℝ ∞ (fun p : ℝ × Model n => F p.1 p.2) := by
    exact (hF.comp (contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff)).contDiff
  have haW' : a ∈ W := haW (mem_singleton a)
  have hpre : (fun p : ℝ × Model n => F p.1 p.2) ⁻¹' (W ∩ U) ∈ 𝓝 (0, a) :=
    hFc.continuous.continuousAt.preimage_mem_nhds (by
      rw [F.map_zero_apply]
      exact (W.isOpen.inter hU).mem_nhds ⟨haW', ha⟩)
  obtain ⟨T, hT, V, hV, hTV⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨V', hV'V, hV'o, haV'⟩ := mem_nhds_iff.mp hV
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨F, hFc, V', hV'o, haV', δ, hδ, ?_⟩
  intro x hx t ht
  have htT : t ∈ T := hδT (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht)
  have hmem : F t x ∈ (W : Set (Model n)) ∩ U :=
    hTV (show (t, x) ∈ T ×ˢ V from ⟨htT, hV'V hx⟩)
  refine ⟨hmem.2, ?_⟩
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp (hode x t)).hasDerivAt
  apply hd.congr_deriv
  change (1 : ℝ) • (χ (F t x) • f (F t x)) = f (F t x)
  rw [hone _ hmem.1, one_smul, one_smul]

/-- Strictly inward coefficients construct a smooth boundary evolution on
one rectangle. Its normal coordinate has exactly the sign of time; in
particular its nonnegative-time restriction lies in the native half-space.
The common rectangle and the evolution are conclusions, not input data. -/
theorem exists_halfSpace_flow {k : ℕ} {f : Model (k + 1) → Model (k + 1)}
    {U : Set (Model (k + 1))} {u : Model k} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hu : boundaryInsert k u ∈ U)
    (hin : 0 < f (boundaryInsert k u) 0) :
    ∃ (c : ℝ × Model k → Model (k + 1)) (V : Set (Model k)) (δ : ℝ),
      ContDiff ℝ ∞ c ∧ IsOpen V ∧ u ∈ V ∧ 0 < δ ∧
      (∀ v, c (0, v) = boundaryInsert k v) ∧
      ∀ v ∈ V, ∀ t ∈ Ioo (-δ) δ,
        c (t, v) ∈ U ∧ HasDerivAt (fun s => c (s, v)) (f (c (t, v))) t ∧
        (0 ≤ c (t, v) 0 ↔ 0 ≤ t) ∧ (0 < c (t, v) 0 ↔ 0 < t) := by
  let P : Set (Model (k + 1)) := U ∩ (fun x => f x 0) ⁻¹' Ioi 0
  have hP : IsOpen P :=
    ((EuclideanSpace.proj (0 : Fin (k + 1))).continuous.comp_continuousOn
      hf.continuousOn).isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨F, hF, A, hA, huA, δ, hδ, hode⟩ :=
    exists_local_flow_of_contDiffOn hP (hf.mono inter_subset_left) ⟨hu, hin⟩
  let c : ℝ × Model k → Model (k + 1) := fun p => F p.1 (boundaryInsert k p.2)
  let V : Set (Model k) := boundaryInsert k ⁻¹' A
  have hc : ContDiff ℝ ∞ c :=
    hF.comp (contDiff_fst.prodMk ((boundaryInsert k).contDiff.comp contDiff_snd))
  have hc0 (v : Model k) : c (0, v) = boundaryInsert k v := F.map_zero_apply _
  refine ⟨c, V, δ, hc, hA.preimage (boundaryInsert k).continuous, huA, hδ, hc0, ?_⟩
  intro v hv t ht
  have hnormal (s : ℝ) (hs : s ∈ Ioo (-δ) δ) :
      HasDerivAt (fun r => c (r, v) 0) (f (c (s, v)) 0) s :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (k + 1))).hasFDerivAt.comp_hasDerivAt s
      (hode _ hv s hs).2
  have hmono : StrictMonoOn (fun s => c (s, v) 0) (Ioo (-δ) δ) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo _ _)
      (fun s hs => (hnormal s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hnormal s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => (hode _ hv s (interior_subset hs)).1.2)
  have hz : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  refine ⟨(hode _ hv t ht).1.1, (hode _ hv t ht).2, ?_, ?_⟩
  · simpa only [hc0, boundaryInsert_zero] using hmono.le_iff_le hz ht
  · simpa only [hc0, boundaryInsert_zero] using hmono.lt_iff_lt hz ht

end FsFltz.Geometry.IntrinsicCollar
