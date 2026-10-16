import FsFltz.Geometry.FamilyLiouvilleLocalFlow
import FsFltz.Analysis.TailoringPoissonPositivity

/-!
# A constructed native flow near the finite tailoring region

Source: `geometric-part-fsf-proof.tex`, `prop:band`, lines 1784–1817,
and `lem:hitting`, lines 1760–1775. A compactly supported action is
constructed on coefficient times the native quotient manifold. Its
spatial equation agrees with the primitive-determined native field on
an open neighborhood of a specified compact region, at every time
whose current point belongs to that neighborhood. All-real native
completeness is not claimed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Function

namespace FsFltz.Geometry.CollarFlow

variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompleteSpace E] [FiniteDimensional ℝ E] [LocallyCompactSpace H]
  [T2Space Q] [SecondCountableTopology Q]

/-- The original family equation holds locally at every time whose
current point is in one constructed open neighborhood of the compact
region. The action and its cutoff field are constructed. -/
theorem exists_parameter_preserving_regional_smoothFlow
    (Z : ℝ → (x : Q) → TangentSpace I x)
    {Ω : Set (ℝ × Q)} (hΩ : IsOpen Ω)
    (hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × Q => (⟨p.2, Z p.1 p.2⟩ : TangentBundle I Q)) Ω)
    {C : Set (ℝ × Q)} (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∃ (V : TopologicalSpace.Opens (ℝ × Q)) (F : Flow ℝ (ℝ × Q)),
      C ⊆ (V : Set (ℝ × Q)) ∧ (V : Set (ℝ × Q)) ⊆ Ω ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
        ((𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : ℝ × (ℝ × Q) => F p.1 p.2) ∧
      (∀ t p, (F t p).1 = p.1) ∧
      ∀ p t, F t p ∈ V →
        IsMIntegralCurveAt (fun s => (F s p).2) (Z p.1) t := by
  let : LocallyCompactSpace (ModelProd ℝ H) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × H))
  let v : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => constantParameterLift (Z p.1) p
  have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, v p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) Ω := by
    have ht : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).tangent) ∞
        (fun t : ℝ => (⟨t, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
      ((ht.comp contMDiff_fst).contMDiffOn.prodMk hZ)
  obtain ⟨χ, V₀, hχ, hCV, hone, hsupport, hsuppΩ⟩ :=
    CollarExtension.exists_smooth_compact_cutoff
      (I := (𝓘(ℝ, ℝ)).prod I) hC hΩ hCΩ
  let W : (p : ℝ × Q) → TangentSpace ((𝓘(ℝ, ℝ)).prod I) p :=
    fun p => χ p • v p
  have hW : ContMDiff ((𝓘(ℝ, ℝ)).prod I)
      (((𝓘(ℝ, ℝ)).prod I).tangent) ∞
      (fun p => (⟨p, W p⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × Q))) :=
    hχ.contMDiffOn.smul_section_of_tsupport hΩ hsuppΩ hv
  obtain ⟨F, hF, hode⟩ := exists_supported_smoothFlow W hW hsupport
    (fun p hp => by simp only [W, image_eq_zero_of_notMem_tsupport hp, zero_smul])
  have hfst : ∀ t p, (F t p).1 = p.1 := by
    intro t p
    have hd : ∀ u : ℝ, HasDerivAt (fun a => (F a p).1) (0 : ℝ) u := by
      intro u
      have hm := (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (F u p)).comp u (hode p u)
      apply (hasMFDerivAt_iff_hasFDerivAt.mp hm).hasDerivAt.congr_deriv
      change (1 : ℝ) • (χ (F u p) • (0 : ℝ)) = 0
      simp only [smul_zero]
    have he : (fun a => (F a p).1) = fun _ => p.1 := by
      apply ODE_solution_unique_univ (t₀ := 0) (v := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
        (s := fun _ => univ) (K := 0) (fun _ => (LipschitzWith.const 0).lipschitzOnWith)
      · exact fun u => ⟨hd u, mem_univ _⟩
      · exact fun u => ⟨hasDerivAt_const u _, mem_univ _⟩
      · exact congrArg Prod.fst (F.map_zero_apply p)
    exact congrFun he t
  let V : TopologicalSpace.Opens (ℝ × Q) := V₀ ⊓ ⟨Ω, hΩ⟩
  refine ⟨V, F, fun p hp => ⟨hCV hp, hCΩ hp⟩,
    fun _ hp => hp.2, hF, hfst, ?_⟩
  intro p t ht
  have hnear : ∀ᶠ s in 𝓝 t, F s p ∈ V :=
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      (V.isOpen.mem_nhds ht)
  filter_upwards [hnear] with s hs
  have hd := (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (F s p)).comp s (hode p s)
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change r • (W (F s p)).2 = r • Z p.1 (F s p).2
  simp only [W, v, constantParameterLift, hone _ hs.1, one_smul, hfst]

end FsFltz.Geometry.CollarFlow

namespace FsFltz.Geometry.SmoothManifold

variable {d : ℕ} (M : SmoothManifold d)

/-- Nondegenerate affine primitive families near a compact region
construct a common smooth regional action for their actual native fields.
The coefficient is retained literally, including at interval endpoints. -/
theorem exists_affine_liouvilleVector_regional_smoothFlow
    (α₀ α₁ : M.Form 1) (hα₀ : M.IsSmoothForm α₀) (hα₁ : M.IsSmoothForm α₁)
    {C : Set (ℝ × M.Point)} (hC : IsCompact C)
    (hnd : ∀ p ∈ C, M.Nondegenerate
      (M.exteriorDerivative (α₀ + p.1 • α₁)) p.2) :
    ∃ (V : TopologicalSpace.Opens (ℝ × M.Point)) (F : Flow ℝ (ℝ × M.Point)),
      C ⊆ (V : Set (ℝ × M.Point)) ∧
      ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
        (fun p : ℝ × (ℝ × M.Point) => F p.1 p.2) ∧
      (∀ t p, (F t p).1 = p.1) ∧
      ∀ p t, F t p ∈ V → IsMIntegralCurveAt (fun s => (F s p).2)
        (M.liouvilleVector (α₀ + p.1 • α₁)) t := by
  let Z : ℝ → (x : M.Point) → M.Tangent x :=
    fun k => M.liouvilleVector (α₀ + k • α₁)
  let S : Set (Set (ℝ × M.Point)) := {U | IsOpen U ∧
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) (𝓘(ℝ, Model d)).tangent ∞
      (fun q : ℝ × M.Point => (⟨q.2, Z q.1 q.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) U}
  have hΩ : IsOpen (⋃₀ S) := isOpen_sUnion (fun _ hU => hU.1)
  have hCΩ : C ⊆ ⋃₀ S := by
    intro p hp
    let α : ℝ → M.Form 1 := fun s => α₀ + (p.1 + s) • α₁
    have hs : M.IsSmoothFormFamily α := by
      intro a
      let c := chartAt (Model d) a
      refine ⟨univ ×ˢ c.target, isOpen_univ.prod c.open_target,
        prod_mono (subset_univ _) Subset.rfl, ?_⟩
      have h₀ : ContDiffOn ℝ ∞
          (fun q : ℝ × Model d => M.formInChart a α₀ q.2) (univ ×ˢ c.target) :=
        (hα₀ a).comp contDiffOn_snd (fun _ hq => hq.2)
      have h₁ : ContDiffOn ℝ ∞
          (fun q : ℝ × Model d => M.formInChart a α₁ q.2) (univ ×ˢ c.target) :=
        (hα₁ a).comp contDiffOn_snd (fun _ hq => hq.2)
      have hk : ContDiffOn ℝ ∞ (fun q : ℝ × Model d => p.1 + q.1)
          (univ ×ˢ c.target) := contDiffOn_const.add contDiffOn_fst
      exact (h₀.add (hk.smul h₁)).congr
        (fun q _ => by
          simp only [α, formInChart_add, formInChart_smul, Pi.add_apply, Pi.smul_apply]
          rfl)
    have hn : M.Nondegenerate (M.exteriorDerivative (α 0)) p.2 := by
      simpa only [α, add_zero] using hnd p hp
    obtain ⟨U, hU, hpU, _, hz⟩ :=
      M.exists_liouvilleVector_family_neighborhood_at α hs (0, p.2)
        (by simp [parameterInterval]) hn
    let g : ℝ × M.Point → ℝ × M.Point := fun q => (q.1 - p.1, q.2)
    have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ g :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    have he (q : ℝ × M.Point) : α (g q).1 = α₀ + q.1 • α₁ := by
      dsimp only [α, g]
      congr 2
      ring
    have hz' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
        (𝓘(ℝ, Model d)).tangent ∞
        (fun q : ℝ × M.Point => (⟨q.2, Z q.1 q.2⟩ :
          TangentBundle 𝓘(ℝ, Model d) M.Point)) (g ⁻¹' U) := by
      apply (hz.comp hg.contMDiffOn (fun _ hq => hq)).congr
      intro q _
      simp only [comp_apply, he, g, Z]
    refine mem_sUnion.mpr ⟨g ⁻¹' U, ⟨hU.preimage hg.continuous, hz'⟩, ?_⟩
    simpa only [mem_preimage, g, sub_self] using hpU
  have hZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      (𝓘(ℝ, Model d)).tangent ∞
      (fun q : ℝ × M.Point => (⟨q.2, Z q.1 q.2⟩ :
        TangentBundle 𝓘(ℝ, Model d) M.Point)) (⋃₀ S) := by
    intro p hp
    obtain ⟨U, hU, hpU⟩ := mem_sUnion.mp hp
    exact (hU.2.contMDiffAt (hU.1.mem_nhds hpU)).contMDiffWithinAt
  obtain ⟨V, F, hCV, _, hF, hfst, hode⟩ :=
    CollarFlow.exists_parameter_preserving_regional_smoothFlow Z hΩ hZ hC hCΩ
  exact ⟨V, F, hCV, hF, hfst, hode⟩

end FsFltz.Geometry.SmoothManifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ}

local instance finiteNativeFlowChartedSpace :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance finiteNativeFlowIsManifold :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

/-- One native cutoff action works near any compact spatial region and
the entire finite nonnegative coefficient interval. It solves the actual
endpoint field at every current point of that region, with no supplied
flow or all-forward native premise. -/
theorem tailoringEndpoint_exists_uniform_finite_region_native_flow
    (I : ToricInput n) {φ : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ β ≥ B, ∀ Kstar : ℝ, ∀ C : Set (LGSpace n), IsCompact C →
      ∃ (V : TopologicalSpace.Opens (ℝ × LGSpace n)) (F : Flow ℝ (ℝ × LGSpace n)),
        Icc (0 : ℝ) Kstar ×ˢ C ⊆ (V : Set (ℝ × LGSpace n)) ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
          ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
          (fun p : ℝ × (ℝ × LGSpace n) => F p.1 p.2) ∧
        (∀ t p, (F t p).1 = p.1) ∧
        (∀ p t, F t p ∈ V → IsMIntegralCurveAt (fun s => (F s p).2)
          ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm φ) (tailoringFamily I β 1) p.1)) t) ∧
        ∀ K ∈ Icc (0 : ℝ) Kstar, ∀ y t, (F t (K, y)).2 ∈ C →
          IsMIntegralCurveAt (fun s => (F s (K, y)).2)
            ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
              (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t := by
  obtain ⟨B, hB, hsymp⟩ :=
    tailoringFamily_exists_uniform_symplectic I hφ hc hU hlower hupper
  refine ⟨B, hB, ?_⟩
  intro β hβ Kstar C hC
  obtain ⟨V, F, hCV, hF, hfst, hode⟩ :=
    (lgManifold n).exists_affine_liouvilleVector_regional_smoothFlow
      (lambdaPotentialForm φ) ((lgManifold n).planePullbackForm (tailoringFamily I β 1))
      (isSmoothForm_lambdaPotentialForm hφ)
      ((lgManifold n).isSmoothForm_planePullbackForm
        (contMDiff_tailoringFamily_lgManifold I β 1)) (isCompact_Icc.prod hC)
      (fun p hp => (hsymp β hβ 1 (by simp) p.1 hp.1.1).2.2 p.2 (mem_univ _))
  refine ⟨V, F, hCV, hF, hfst, hode, ?_⟩
  intro K hK y t ht
  apply hode
  exact hCV ⟨by simpa only [hfst] using hK, ht⟩

end FsFltz
