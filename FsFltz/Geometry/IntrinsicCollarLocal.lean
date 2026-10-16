import FsFltz.Geometry.IntrinsicCollarFlow
import FsFltz.Geometry.IntrinsicCollarInverse

/-!
# Constructed locally invertible inward collar in half-space coordinates

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. An inward coefficient field constructs its
boundary evolution. Its seam derivative is transverse, so the inverse
function theorem gives an actual smooth local inverse. A single smaller
rectangle retains the ODE and side assertions and makes the evolution
injective. No collar map or inverse is supplied as input.
Compact uniform collars and completion gluing remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

/-- A strictly inward smooth coefficient field constructs a smooth,
injective collar evolution on one common rectangle. The same map has a
smooth local inverse everywhere on that rectangle and solves the original
ODE, with its normal coordinate having exactly the sign of time. -/
theorem exists_halfSpace_collar {k : ℕ} {f : Model (k + 1) → Model (k + 1)}
    {U : Set (Model (k + 1))} {u : Model k} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hu : boundaryInsert k u ∈ U)
    (hin : 0 < f (boundaryInsert k u) 0) :
    ∃ (c : ℝ × Model k → Model (k + 1)) (V : Set (Model k)) (δ : ℝ),
      ContDiff ℝ ∞ c ∧ IsOpen V ∧ u ∈ V ∧ 0 < δ ∧
      (∀ v, c (0, v) = boundaryInsert k v) ∧
      InjOn c (Ioo (-δ) δ ×ˢ V) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞ c
        (Ioo (-δ) δ ×ˢ V) ∧
      ∀ v ∈ V, ∀ t ∈ Ioo (-δ) δ,
        c (t, v) ∈ U ∧ HasDerivAt (fun s => c (s, v)) (f (c (t, v))) t ∧
        (0 ≤ c (t, v) 0 ↔ 0 ≤ t) ∧ (0 < c (t, v) 0 ↔ 0 < t) := by
  obtain ⟨c, V₀, δ₀, hc, hV₀, huV₀, hδ₀, hseam, hflow⟩ :=
    exists_halfSpace_flow hU hf hu hin
  have hz : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨neg_neg_of_pos hδ₀, hδ₀⟩
  have htime : HasDerivAt (fun t => c (t, u)) (f (boundaryInsert k u)) 0 := by
    simpa only [hseam] using (hflow u huV₀ 0 hz).2.1
  obtain ⟨e, hue, heq⟩ := isLocalDiffeomorphAt_of_seam_transverse
    isOpen_univ hc.contDiffOn (mem_univ (0, u))
    (Eventually.of_forall hseam) htime hin
  have hnb : e.source ∩ (Ioo (-δ₀) δ₀ ×ˢ V₀) ∈ 𝓝 (0, u) :=
    (e.open_source.inter (isOpen_Ioo.prod hV₀)).mem_nhds ⟨hue, hz, huV₀⟩
  obtain ⟨T, hT, W, hW, hTW⟩ := mem_nhds_prod_iff.mp hnb
  obtain ⟨V, hVW, hV, huV⟩ := mem_nhds_iff.mp hW
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp hT
  have hsub : Ioo (-δ) δ ×ˢ V ⊆ e.source ∩ (Ioo (-δ₀) δ₀ ×ˢ V₀) := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    exact hTW ⟨hδT (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht), hVW hv⟩
  refine ⟨c, V, δ, hc, hV, huV, hδ, hseam, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    apply e.toPartialEquiv.injOn (hsub hp).1 (hsub hq).1
    rw [← heq (hsub hp).1, ← heq (hsub hq).1]
    exact hpq
  · intro p
    exact ⟨e, (hsub p.property).1, heq⟩
  · intro v hv t ht
    have hold := (hsub (show (t, v) ∈ Ioo (-δ) δ ×ˢ V from ⟨ht, hv⟩)).2
    exact hflow v hold.2 t hold.1

end FsFltz.Geometry.IntrinsicCollar
