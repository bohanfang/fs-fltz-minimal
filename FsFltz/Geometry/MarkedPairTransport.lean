import FsFltz.Geometry.MarkedHorizontalFlow

/-!
# Simultaneous transport of a compact domain and its marked ribbon

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009.
One supported flow is constructed from compatible local differential equations.
Confinement proves that this same flow transports both compact carriers and
both marked boundaries for the entire closed parameter interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Bundle
open Set

namespace FsFltz.Geometry

variable {E Q F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [SecondCountableTopology Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compatible local equations construct one complete smooth auxiliary flow
which transports the domain, its boundary, its ribbon and the ribbon frontier.
The two confinement assertions are derived from the differential equations. -/
theorem exists_supported_pairTransport_near_compact
    (τ q ρ : Q → ℝ) (f : Q → F) (w : F) (a : ℝ)
    (hτ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ τ)
    (hq : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q)
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hcompact : IsCompact {p | τ p ∈ Icc (0 : ℝ) 1 ∧ q p ≤ 0})
    (hinc : ∀ p, τ p ∈ Icc (0 : ℝ) 1 → f p = w → ρ p ≤ a → q p ≤ 0)
    (O B R J : Set Q) (hO : IsOpen O) (hB : IsOpen B) (hR : IsOpen R) (hJ : IsOpen J)
    (hCO : {p | τ p ∈ Icc (0 : ℝ) 1 ∧ q p ≤ 0} ⊆ O)
    (hCB : {p | τ p ∈ Icc (0 : ℝ) 1 ∧ q p = 0} ⊆ B)
    (hCR : {p | τ p ∈ Icc (0 : ℝ) 1 ∧ f p = w ∧ ρ p ≤ a} ⊆ R)
    (hCJ : {p | τ p ∈ Icc (0 : ℝ) 1 ∧ f p = w ∧ ρ p = a} ⊆ J)
    (V : (p : Q) → TangentSpace 𝓘(ℝ, E) p)
    (hV : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, E) Q)) O)
    (hparam : ∀ p ∈ O, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ p (V p) = (1 : ℝ))
    (hboundary : ∀ p ∈ O ∩ B, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q p (V p) = 0)
    (hribbon : ∀ p ∈ O ∩ R, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × F)
      (fun z => (τ z, f z)) p (V p) = (1, 0))
    (hfrontier : ∀ p ∈ (O ∩ R) ∩ J, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ p (V p) = 0) :
    ∃ Φ : Flow ℝ Q,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × Q => Φ p.1 p.2) ∧
      (∀ p, τ p ∈ Icc (0 : ℝ) 1 → q p ≤ 0 →
        ∀ t : ℝ, τ p + t ∈ Icc (0 : ℝ) 1 →
          τ (Φ t p) = τ p + t ∧ q (Φ t p) ≤ 0 ∧ (q (Φ t p) = 0 ↔ q p = 0)) ∧
      (∀ p, τ p ∈ Icc (0 : ℝ) 1 → f p = w → ρ p ≤ a →
        ∀ t : ℝ, τ p + t ∈ Icc (0 : ℝ) 1 →
          τ (Φ t p) = τ p + t ∧ f (Φ t p) = w ∧ ρ (Φ t p) ≤ a ∧
            (ρ (Φ t p) = a ↔ ρ p = a)) := by
  obtain ⟨P, _K, W, Φ, hP, hCP, hPO, _hK, _hW, _hz, heq, hΦ, hode⟩ :=
    exists_supported_horizontalFlow_near_compact hcompact hO hCO V hV
  have hpair : ∀ p ∈ P, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × ℝ)
      (fun z => (τ z, (0 : ℝ))) p (W p) = (1, 0) := by
    intro p hp
    have ht := (hτ.mdifferentiableAt (x := p) (by simp)).hasMFDerivAt
    have hz := hasMFDerivAt_const (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ)) p
    have hh : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × ℝ) (fun z => (τ z, (0 : ℝ))) p
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ p).prod 0) :=
      ⟨ht.1.prodMk hz.1, ht.2.prodMk hz.2⟩
    rw [hh.mfderiv, heq p hp]
    exact Prod.ext (hparam p (hPO hp)) rfl
  have hamb := horizontalFlow_preserves_parameter_truncation τ q (fun _ => (0 : ℝ))
    hτ hq contMDiff_const 0 0 P B hP hB
    (fun p hp => hCP ⟨hp.1, hp.2.2⟩) (fun p hp => hCB ⟨hp.1, hp.2.2⟩)
    W Φ hode hpair (fun p hp => by rw [heq p hp.1]; exact hboundary p ⟨hPO hp.1, hp.2⟩)
  have hrib := horizontalFlow_preserves_parameter_truncation τ ρ f
    hτ hρ hf w a (P ∩ R) J (hP.inter hR) hJ
    (fun p hp => ⟨hCP ⟨hp.1, hinc p hp.1 hp.2.1 hp.2.2⟩, hCR hp⟩) hCJ
    W Φ hode (fun p hp => by rw [heq p hp.1]; exact hribbon p ⟨hPO hp.1, hp.2⟩)
    (fun p hp => by rw [heq p hp.1.1]; exact hfrontier p ⟨⟨hPO hp.1.1, hp.1.2⟩, hp.2⟩)
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · intro p hp hqp t ht
    have h := hamb p hp rfl hqp t ht
    refine ⟨h.1, h.2.2.1, ?_, h.2.2.2⟩
    intro hz
    have hb := hamb (Φ t p) (h.1 ▸ ht) rfl h.2.2.1 (-t)
      (by rw [h.1]; simpa only [add_neg_cancel_right] using hp)
    simpa only [← Φ.map_add, neg_add_cancel, Flow.map_zero_apply] using hb.2.2.2 hz
  · intro p hp hfp hrp t ht
    have h := hrib p hp hfp hrp t ht
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2⟩
    intro hz
    have hb := hrib (Φ t p) (h.1 ▸ ht) h.2.1 h.2.2.1 (-t)
      (by rw [h.1]; simpa only [add_neg_cancel_right] using hp)
    simpa only [← Φ.map_add, neg_add_cancel, Flow.map_zero_apply] using hb.2.2.2 hz

end FsFltz.Geometry
