import FsFltz.Geometry.MarkedHorizontalGluing
import FsFltz.Geometry.FamilyLiouvilleLocalFlow
import FsFltz.Geometry.MarkedCurveConfinement

/-!
# Complete auxiliary flow of a marked horizontal field

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–993.
A compact cutoff retains the field on an open neighborhood of the actual
compact family; the existing supported smooth integration theorem constructs
the all-real flow. Confinement to the family over the parameter interval is
a separate producer, not an assumption of this construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set Filter Function

namespace FsFltz.Geometry

variable {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [SecondCountableTopology Q]

/-- A native field near a compact marked family constructs an all-real
smooth auxiliary flow whose field agrees with the original field on an
actual open neighborhood of that family. The field has compact support;
no global flow is supplied in the hypotheses. -/
theorem exists_supported_horizontalFlow_near_compact
    {C O : Set Q} (hC : IsCompact C) (hO : IsOpen O) (hCO : C ⊆ O)
    (V : (x : Q) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) Q)) O) :
    ∃ (P K : Set Q) (W : (x : Q) → TangentSpace 𝓘(ℝ, E) x) (Φ : Flow ℝ Q),
      IsOpen P ∧ C ⊆ P ∧ P ⊆ O ∧ IsCompact K ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) Q)) ∧
      (∀ x ∉ K, W x = 0) ∧ (∀ x ∈ P, W x = V x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × Q => Φ p.1 p.2) ∧
      ∀ x, IsMIntegralCurve (fun t => Φ t x) W := by
  obtain ⟨χ, P, hχ, hCP, hone, hsupport, hsuppO⟩ :=
    CollarExtension.exists_smooth_compact_cutoff (I := 𝓘(ℝ, E)) hC hO hCO
  let W : (x : Q) → TangentSpace 𝓘(ℝ, E) x := fun x => χ x • V x
  have hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) Q)) :=
    hχ.contMDiffOn.smul_section_of_tsupport hO hsuppO hV
  have hzero : ∀ x ∉ tsupport χ, W x = 0 := by
    intro x hx
    simp only [W, image_eq_zero_of_notMem_tsupport hx, zero_smul]
  obtain ⟨Φ, hΦ, hode⟩ := CollarFlow.exists_supported_smoothFlow W hW hsupport hzero
  have hPO : (P : Set Q) ⊆ O := by
    intro x hx
    apply hsuppO
    exact subset_closure (mem_support.mpr (by rw [hone x hx]; exact one_ne_zero))
  exact ⟨P, tsupport χ, W, Φ, P.isOpen, hCP, hPO, hsupport, hW, hzero,
    fun x hx => by simp only [W, hone x hx, one_smul], hΦ, hode⟩

section Transport

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [SecondCountableTopology Q] in
/-- A constructed flow whose field preserves the actual equations on open
neighborhoods transports the literal truncated fibers for the entire
parameter interval, in both time directions. Truncation-boundary points
retain their boundary value exactly. No confinement is assumed. -/
theorem horizontalFlow_preserves_parameter_truncation
    (τ ρ : Q → ℝ) (f : Q → F)
    (hτ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ τ)
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (w : F) (A : ℝ) (O B : Set Q) (hO : IsOpen O) (hB : IsOpen B)
    (hCO : {q | τ q ∈ Icc (0 : ℝ) 1 ∧ f q = w ∧ ρ q ≤ A} ⊆ O)
    (hCB : {q | τ q ∈ Icc (0 : ℝ) 1 ∧ f q = w ∧ ρ q = A} ⊆ B)
    (W : (x : Q) → TangentSpace 𝓘(ℝ, E) x) (Φ : Flow ℝ Q)
    (hode : ∀ x, IsMIntegralCurve (fun t => Φ t x) W)
    (hder : ∀ q ∈ O, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
      (fun x => (τ x, f x)) q (W q) = (1, 0))
    (hpot : ∀ q ∈ O ∩ B, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ q (W q) = 0) :
    ∀ p, τ p ∈ Icc (0 : ℝ) 1 → f p = w → ρ p ≤ A →
      ∀ t : ℝ, τ p + t ∈ Icc (0 : ℝ) 1 →
        τ (Φ t p) = τ p + t ∧ f (Φ t p) = w ∧ ρ (Φ t p) ≤ A ∧
        (ρ p = A → ρ (Φ t p) = A) := by
  intro p hp hpf hpρ
  let γ : ℝ → Q := fun t => Φ t p
  have hγ : Continuous γ := (hode p).continuous
  have hcomponents : ∀ q ∈ O,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ q (W q) = (1 : ℝ) ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f q (W q) = 0 := by
    intro q hq
    have h₁ := (hτ.mdifferentiableAt (x := q) (by simp)).hasMFDerivAt
    have h₂ := (hf.mdifferentiableAt (x := q) (by simp)).hasMFDerivAt
    have hj : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
        (fun x => (τ x, f x)) q
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ q).prod
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f q)) :=
      ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩
    have heq := hder q hq
    rw [hj.mfderiv] at heq
    exact ⟨congrArg (fun z : ℝ × F => z.1) heq,
      congrArg (fun z : ℝ × F => z.2) heq⟩
  have hτd : ∀ t, γ t ∈ O → HasDerivAt (τ ∘ γ) 1 t := by
    intro t ht
    have hm := (hτ.mdifferentiableAt (x := γ t) (by simp)).hasMFDerivAt.comp t (hode p t)
    apply (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt.congr_deriv
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ (γ t) ((1 : ℝ) • W (γ t)) = (1 : ℝ)
    simpa only [one_smul] using (hcomponents (γ t) ht).1
  have hfd : ∀ t, γ t ∈ O → HasFDerivAt (𝕜 := ℝ) (f ∘ γ) 0 t := by
    intro t ht
    have hm := (hf.mdifferentiableAt (x := γ t) (by simp)).hasMFDerivAt.comp t (hode p t)
    apply (hasMFDerivAt_iff_hasFDerivAt.mp hm).congr_fderiv
    apply ContinuousLinearMap.ext
    intro a
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t) (a • W (γ t)) = 0
    rw [map_smul, (hcomponents (γ t) ht).2, smul_zero]
  have hρd : ∀ t, γ t ∈ O ∩ B → HasDerivAt (ρ ∘ γ) 0 t := by
    intro t ht
    have hm := (hρ.mdifferentiableAt (x := γ t) (by simp)).hasMFDerivAt.comp t (hode p t)
    apply (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt.congr_deriv
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ (γ t) ((1 : ℝ) • W (γ t)) = 0
    rw [one_smul, hpot (γ t) ht]
  let J : Set ℝ := Icc (-τ p) (1 - τ p)
  have hzero : (0 : ℝ) ∈ J := by constructor <;> linarith [hp.1, hp.2]
  have htime : ∀ t ∈ J, τ (γ 0) + 1 * (t - 0) ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    simp only [γ, Flow.map_zero_apply, sub_zero, one_mul]
    constructor <;> linarith [ht.1, ht.2]
  have hpres := marked_curve_stays_in_parameter_slab γ hγ τ ρ f
    hτ.continuous hρ.continuous hf.continuous w A 1 O B hO hB hCO hCB hτd hfd hρd
    J isPreconnected_Icc 0 hzero
    (by simpa only [γ, Flow.map_zero_apply] using And.intro hpf hpρ) htime
  have hboundary : ρ p = A → ∀ t ∈ J, ρ (γ t) = A := by
    intro hpA
    apply eqOn_level_of_eventually_hasDerivAt_zero (hρ.continuous.comp hγ) J
      isPreconnected_Icc hzero
      (by simpa only [Function.comp_def, γ, Flow.map_zero_apply] using hpA)
    intro t ht heq
    have hpt := hpres t ht
    have hct : τ (γ t) ∈ Icc (0 : ℝ) 1 := hpt.1 ▸ htime t ht
    have hmem : γ t ∈ O ∩ B :=
      ⟨hCO ⟨hct, hpt.2⟩, hCB ⟨hct, hpt.2.1, heq⟩⟩
    have hn : ∀ᶠ u in 𝓝 t, γ u ∈ O ∩ B :=
      hγ.continuousAt.preimage_mem_nhds ((hO.inter hB).mem_nhds hmem)
    exact hn.mono (fun u hu => hρd u hu)
  intro t ht
  have htJ : t ∈ J := by constructor <;> linarith [ht.1, ht.2]
  have hpast := hpres t htJ
  simp only [γ, Flow.map_zero_apply, sub_zero, one_mul] at hpast
  exact ⟨hpast.1, hpast.2.1, hpast.2.2, fun h => hboundary h t htJ⟩

end Transport

end FsFltz.Geometry
