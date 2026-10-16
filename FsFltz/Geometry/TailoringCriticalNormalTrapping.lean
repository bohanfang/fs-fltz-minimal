import FsFltz.Geometry.TailoringCriticalTransverseLinearization
import FsFltz.Geometry.TailoringConormalRate
import FsFltz.Geometry.BilinearNormalTrapping
import FsFltz.Geometry.TailoringNormalProductCoordinates

/-!
# One actual trapping neighborhood for the entire critical face torus

Source: `geometric-part-fsf-proof.tex`, `lem:stable`, lines 1703–1726,
and `thm:core`, lines 1738–1748. Local native estimates use one
quotient and fixed transverse metric, and compactness joins them without
identifying different product coordinates on their overlaps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Geometry Geometry.SmoothManifold Set Filter Function
open scoped Topology BigOperators ContDiff Manifold

variable {n : ℕ}

/-- A literal radial face torus is compact in its native embedded fiber,
because the embedding carries it onto the whole compact quotient torus. -/
theorem isCompact_preimage_radial_coneTorus {d : ℕ}
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
    (u : RealSpace n) (σ : Set (RealSpace n))
    (hsub : ({u} : Set (RealSpace n)) ×ˢ coneTorus σ ⊆ range j.map) :
    IsCompact (j.map ⁻¹' (({u} : Set (RealSpace n)) ×ˢ coneTorus σ)) := by
  apply j.embedding.isCompact_iff.mpr
  rw [image_preimage_eq_of_subset hsub]
  exact isCompact_singleton.prod (isCompact_coneTorus σ)

namespace ConormalTransverseNeighborhoodAt

/-- The already constructed quotient-map smoothness is transported to the
same native embedding, without selecting real-valued angular coordinates. -/
theorem native_transverse_smooth {d : ℕ}
    {I : ToricInput n} {φEnd : RealSpace n → ℝ} {β : ℝ}
    {s : Finset (Lattice n)} {u : RealSpace n} {v₀ : s}
    (W : ConormalTransverseNeighborhoodAt I φEnd β s u v₀)
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n))
    (a : N.Point) (ha : j.map a ∈ W.neighborhood) :
    ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, W.projection.ker × (s.erase v₀.val → ℝ)) ∞
      ((conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient s v₀.val) ∘ j.map) a := by
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  have hs := (W.transverse_smooth (j.map a) ha).comp (j.map a)
    (contMDiff_linearRechart_id_symm (M := LGSpace n) (lgEuclideanEquiv n)).contMDiffAt
  exact hs.comp a j.map.contMDiff.contMDiffAt

theorem hasDerivAt_transverse_native_orbit {d : ℕ}
    {I : ToricInput n} {φEnd : RealSpace n → ℝ} {β : ℝ}
    {s : Finset (Lattice n)} {u : RealSpace n} {v₀ : s}
    (W : ConormalTransverseNeighborhoodAt I φEnd β s u v₀)
    (N : SmoothManifold d) (j : N.SmoothEmbedding (lgManifold n)) (μ : N.Form 1)
    {γ : ℝ → N.Point} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (N.liouvilleVector μ) t)
    (ha : j.map (γ t) ∈ W.neighborhood) :
    HasDerivAt
      (fun τ => conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient
        s v₀.val (j.map (γ τ)))
      (conormalTransverseRate N j μ (coordinateGradient φEnd) W.quotient s v₀.val (γ t)) t := by
  have hδ := W.native_transverse_smooth N j (γ t) ha
  have hd := (hδ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hγ.self_of_nhds
  have hd' : HasFDerivAt
      (fun τ => conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient
        s v₀.val (j.map (γ τ)))
      ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, W.projection.ker × (s.erase v₀.val → ℝ))
        ((conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient s v₀.val) ∘
          j.map) (γ t)).comp
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
          (N.liouvilleVector μ (γ t)))) t := hd.hasFDerivAt
  apply hd'.hasDerivAt.congr_deriv
  change mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, W.projection.ker × (s.erase v₀.val → ℝ))
    ((conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient s v₀.val) ∘
      j.map) (γ t) ((1 : ℝ) • N.liouvilleVector μ (γ t)) = _
  rw [one_smul]
  rfl

end ConormalTransverseNeighborhoodAt

namespace CriticalFaceNormalData

variable {I : ToricInput n} {φEnd φ : RealSpace n → ℝ} {β : ℝ}
  {s : Finset (Lattice n)} {u : RealSpace n} {q : s → ℝ} {lam : ℝ}
  {B : (s → ℝ) →L[ℝ] RealSpace n} {R : (s → ℝ) →L[ℝ] (s → ℝ)}

/-- Compactness uses the same actual radius and fiber equation as the normal
metric data, including the free quotient angles of the whole critical torus. -/
theorem native_torus_compact (D : CriticalFaceNormalData I φEnd φ β s u q lam B R)
    (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n))
    (himage : range j.map = {y | tailoringFamily I β 1 y = 1}) :
    IsCompact (j.map ⁻¹' (({u} : Set (RealSpace n)) ×ˢ coneTorus (positiveCone s))) := by
  apply isCompact_preimage_radial_coneTorus N j u (positiveCone s)
  rintro ⟨w, θ⟩ ⟨hw, hθ⟩
  have hwu : w = u := mem_singleton_iff.mp hw
  subst w
  rw [himage]
  exact D.fiber_eq θ hθ

end CriticalFaceNormalData

/-- The actual local product-coordinate inequalities for one fixed defining
map and metric construct a trapping neighborhood of the entire critical torus.
Neither local expansion nor trapping is a hypothesis of this toric producer. -/
theorem tailoringEndpoint_exists_uniform_criticalFaceNormalTrapping
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : IsStronglyCompatibleEndPotential I φEnd) (hEnd1 : ContDiff ℝ 1 φEnd)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (heq : ∀ u, R₀ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ β ≥ B₀,
      ∀ (s : Finset (Lattice n)), IsPolytopeFace I.vertices s → s.Nonempty → s ≠ I.vertices →
      ∀ (u : RealSpace n) (q : s → ℝ) (lam : ℝ)
        (B : (s → ℝ) →L[ℝ] RealSpace n) (R : (s → ℝ) →L[ℝ] (s → ℝ)),
      CriticalFaceNormalData I φEnd φ β s u q lam B R →
      ∀ (N : SmoothManifold (2 * n - 2)) (j : N.SmoothEmbedding (lgManifold n)),
      range j.map = {y | tailoringFamily I β 1 y = 1} →
      ∀ v₀ : s,
      ∃ W : ConormalTransverseNeighborhoodAt I φEnd β s u v₀,
      ∃ V : Set N.Point, IsOpen V ∧
        j.map ⁻¹' (({u} : Set (RealSpace n)) ×ˢ coneTorus (positiveCone s)) ⊆ V ∧
        V ⊆ j.map ⁻¹' W.neighborhood ∧
        (∀ γ : ℝ → N.Point, (∀ t, 0 ≤ t → γ t ∈ V) →
          (∀ t, 0 ≤ t → IsMIntegralCurveAt γ
            (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))) t) →
          j.map (γ 0) ∈ range (Prod.map
            (fun p : W.branchDomain => W.radialBranch p) W.angleBranch) ∧
          j.map (γ 0) ∈ tailoringCoreSection I φEnd β) ∧
        ∀ F : CompleteLiouvilleFlow N
          (N.liouvilleVector (N.pullback (lgManifold n) j.map (lambdaPotentialForm φ))),
          flowCore F.flow V ⊆ j.map ⁻¹' tailoringCoreSection I φEnd β := by
  classical
  obtain ⟨Br, hBr, hrate⟩ := tailoringEndpoint_exists_uniform_zero_conormalTransverseRate
    I hφ hc hU hlower hupper hEnd hR₀ heq
  obtain ⟨_, _, _, _, Bπ, _, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨max Br Bπ, hBr.trans_le (le_max_left _ _), ?_⟩
  intro β hβ s hs hsne hsproper u q lam B R D N j himage v₀
  let μ := N.pullback (lgManifold n) j.map (lambdaPotentialForm φ)
  have hpi : ∀ y, tailoringFamily I β 1 y = 1 →
      0 < (lgManifold n).planePairing (lambdaPotentialForm φ) (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y) := by
    intro y hy
    exact (hπ β ((le_max_right _ _).trans hβ) 1 (by simp) y _).2.2 (by simp [hy])
  obtain ⟨W, L, hL, horth, hsym, hmetric, hcharts⟩ :=
    D.exists_same_data_fixed_transverse_linearization hEnd hEnd1 hs hφ hc hlower hpi
      N j himage v₀
  let H := fderiv ℝ (coordinateGradient φEnd) u
  let G := fixedFaceTransverseMetric H q v₀ L
  let δ : N.Point → W.projection.ker × (s.erase v₀.val → ℝ) :=
    (conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient s v₀.val) ∘ j.map
  let Rate := conormalTransverseRate N j μ (coordinateGradient φEnd) W.quotient s v₀.val
  let K := j.map ⁻¹' (({u} : Set (RealSpace n)) ×ˢ coneTorus (positiveCone s))
  let O := j.map ⁻¹' (W.neighborhood ∩ (Prod.fst ⁻¹' D.plateau) ∩
    conormalPositivePhaseNeighborhood s)
  have hO : IsOpen O :=
    ((W.neighborhood_open.inter (D.plateau_open.preimage continuous_fst)).inter
      (isOpen_conormalPositivePhaseNeighborhood s)).preimage j.map.contMDiff.continuous
  have hKO : K ⊆ O := by
    intro a ha
    have he : j.map a = (u, (j.map a).2) :=
      Prod.ext (mem_singleton_iff.mp ha.1) rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he]
      exact W.torus_mem _ ha.2
    · exact (mem_singleton_iff.mp ha.1).symm ▸ D.plateau_mem
    · exact mem_conormalPositivePhaseNeighborhood_of_mem_coneTorus I hs hsne hsproper _ ha.2
  have hδO : ∀ a ∈ O, ContMDiffAt 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, W.projection.ker × (s.erase v₀.val → ℝ)) ∞ δ a := by
    intro a ha
    exact W.native_transverse_smooth N j a ha.1.1
  have hRO : ∀ a ∈ O, δ a = 0 → Rate a = 0 := by
    intro a ha hz
    exact hrate β ((le_max_left _ _).trans hβ) N j himage W.projection.ker
      s hs hsne hsproper W.quotient W.quotient_zero v₀ a ha.2
      (D.plateau_cutoff _ ha.1.2) hz
  have hlocal : ∀ a ∈ K, ∃ k : ℝ, 0 < k ∧ ∃ V : Set N.Point,
      IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V, k * ‖δ b‖ ^ 2 ≤ G (Rate b) (δ b) := by
    intro a ha
    let θ := (j.map a).2
    have hθ : θ ∈ coneTorus (positiveCone s) := ha.2
    have he : j.map a = (u, θ) := Prod.ext (mem_singleton_iff.mp ha.1) rfl
    obtain ⟨ξ, hξ⟩ := lgCover_surjective n (j.map a)
    have hpoint : j.map a = lgCover ξ := hξ.symm
    have hξtorus : lgCover ξ = (u, θ) := hξ.trans he
    obtain ⟨C, hZ, hRate, hlin, hpair, hself, hpos⟩ :=
      (hcharts θ hθ).2 a ξ hpoint hξtorus
    have hrad : ξ.1 = u := congrArg Prod.fst hξtorus
    have hΦ : ContDiffAt ℝ ∞ (coordinateGradient φEnd) ξ.1 :=
      hrad.symm ▸ D.gradient_smooth hEnd hEnd1
    have hHΦ : H = fderiv ℝ (coordinateGradient φEnd) ξ.1 := by rw [hrad]
    have hmon : ∀ v : s, monomial 1 v.val (lgCover ξ) =
        (criticalFaceTransverseWeights β q v : ℂ) := by
      rw [hξtorus]
      exact D.transverseWeights_monomial θ hθ
    have hz : conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient
        s v₀.val (lgCover ξ) = 0 := by
      rw [hξtorus]
      exact W.torus_zero θ hθ
    have hpositive : ∀ z : W.projection.ker × (s.erase v₀.val → ℝ), z ≠ 0 →
        0 < G ((fderiv ℝ (C.coordinateTransverseRate (coordinateGradient φEnd)
          W.quotient v₀) (chartAt (Model (2 * n - 2)) a a))
            (C.transverseNormalLift v₀ L z)) z := by
      intro z hzne
      have hh := hpos z hzne
      rw [hlin, ContinuousLinearMap.comp_apply] at hh
      exact hh
    obtain ⟨k, hk, V, hV, haV, hVO, hbound⟩ :=
      C.exists_local_native_transverse_expansion hφ
        (fun b => tailoring_fullFiber_nondegenerate I β hφ hc hlower hpi j himage b)
        W.quotient v₀ hΦ hHΦ (criticalFaceTransverseWeights β q) hmon L hL hz G hpositive
        O hO (hKO ha) hδO hRO
    exact ⟨k, hk, V, hV, haV, hbound⟩
  have hδK : ∀ a ∈ K, ContinuousAt δ a :=
    fun a ha => (hδO a (hKO ha)).continuousAt
  have hzero : ∀ a ∈ K, δ a = 0 := by
    intro a ha
    have he : j.map a = (u, (j.map a).2) := Prod.ext (mem_singleton_iff.mp ha.1) rfl
    change conormalTransverseCoordinates (coordinateGradient φEnd) W.quotient s v₀.val (j.map a) = 0
    rw [he]
    exact W.torus_zero _ ha.2
  obtain ⟨V, hV, hKV, htrap⟩ := exists_compact_bilinear_trapping_neighborhood
    G hsym hmetric K (D.native_torus_compact N j himage) δ Rate hδK hzero hlocal
  let J := interior {a : N.Point | coordinateGradient φEnd (j.map a).1 ≠ 0}
  have hKJ : K ⊆ J := by
    intro a ha
    have hrad : (j.map a).1 = u := mem_singleton_iff.mp ha.1
    have hpne : coordinateGradient φEnd u ≠ 0 := by
      intro he
      have hh := W.functional_normalized
      rw [he, map_zero] at hh
      exact zero_ne_one hh
    have hg : ContinuousAt (fun b : N.Point => coordinateGradient φEnd (j.map b).1) a := by
      have hs : ContinuousAt (coordinateGradient φEnd) (j.map a).1 := by
        rw [hrad]
        exact (D.gradient_smooth hEnd hEnd1).continuousAt
      exact hs.comp (f := fun b : N.Point => (j.map b).1) (x := a)
        (continuous_fst.comp j.map.contMDiff.continuous).continuousAt
    apply mem_interior_iff_mem_nhds.mpr
    exact hg.preimage_mem_nhds (isOpen_ne.mem_nhds (hrad.symm ▸ hpne))
  have hforward (γ : ℝ → N.Point) (hstay : ∀ t, 0 ≤ t → γ t ∈ V ∩ (O ∩ J))
      (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt γ (N.liouvilleVector μ) t) :
      j.map (γ 0) ∈ range (Prod.map
        (fun p : W.branchDomain => W.radialBranch p) W.angleBranch) ∧
      j.map (γ 0) ∈ tailoringCoreSection I φEnd β := by
    have hz : δ (γ 0) = 0 := htrap γ (fun t ht => (hstay t ht).1) (by
      intro t ht
      exact W.hasDerivAt_transverse_native_orbit N j μ (hγ t ht) (hstay t ht).2.1.1.1)
    have haO := (hstay 0 le_rfl).2.1.1.1
    have hf : tailoringFamily I β 1 (j.map (γ 0)) = 1 := by
      have hm : j.map (γ 0) ∈ range j.map := ⟨γ 0, rfl⟩
      rwa [himage] at hm
    have hcone := (W.zero_iff_conormal _ haO hf).mp hz
    have hpne : coordinateGradient φEnd (j.map (γ 0)).1 ≠ 0 :=
      interior_subset (hstay 0 le_rfl).2.2
    have hsnz : positiveCone s ≠ {0} := by
      intro he
      rw [he] at hcone
      exact hpne hcone.1
    refine ⟨(W.zero_iff_branch _ haO hf).mp hz, ?_⟩
    exact ⟨⟨hpne, positiveCone s, Or.inr ⟨s, hs, hsne, hsproper, rfl⟩,
      hsnz, hcone⟩, hf⟩
  refine ⟨W, V ∩ (O ∩ J), hV.inter (hO.inter isOpen_interior),
    fun a ha => ⟨hKV ha, hKO ha, hKJ ha⟩,
    fun _ ha => ha.2.1.1.1, hforward, ?_⟩
  intro F a ha
  have hh := hforward (fun t => F.flow t a) ha
    (fun t _ => (F.isMIntegralCurve a).isMIntegralCurveAt t)
  simpa only [mem_preimage, Flow.map_zero_apply] using hh.2

end FsFltz
