import FsFltz.Geometry.TailoringRoundedMarkingFamilyTransfer
import FsFltz.Geometry.OriginalBundleCompletionMarkingFieldRegularity
import FsFltz.Geometry.PrescribedFamilyCollarInverse
import FsFltz.Geometry.CompletionDynamics

/-!
# Interior absorption and smoothness of the actual marking family

Source: `geometric-part-fsf-proof.tex`, the actual common marking,
lines 1270–1303; `geoemtric-part-fsf.tex`, `def:chain`, lines 163–200.
Finite negative flow into the compact interior reduces completed-map
regularity to the actual compact formula. The smooth complete-flow germs
come from the already constructed completed primitive families.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold IntrinsicSmoothBundle

namespace Completion

/-- Every positive negative-flow time sends the compact carrier into its
interior. A boundary image would flow forward along a positive end ray
back into the compact carrier, contradicting overlap. -/
theorem negative_flow_mem_interior {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) {x : C.ambient.manifold.Point}
    (hx : x ∈ C.inclusion.map '' D.domain.carrier) {t : ℝ} (ht : 0 < t) :
    C.ambient.completeFlow.flow (-t) x ∈ C.inclusion.map '' interior D.domain.carrier := by
  obtain ⟨y, hy, he⟩ := C.negative_flow_mem hx ht.le
  refine ⟨y, ?_, he⟩
  apply (mem_interior_iff_notMem_frontier hy).mpr
  intro hfront
  rw [← D.domain.boundary_range] at hfront
  obtain ⟨b, hb⟩ := hfront
  have hflow : C.endMap (b, t) = x := by
    rw [C.end_flow, hb]
    rw [he, ← C.ambient.completeFlow.flow.map_add, add_neg_cancel,
      Flow.map_zero_apply]
  exact C.overlap b t ht (hflow ▸ hx)

/-- Every point in an actual completion reaches the compact interior in
finite nonpositive time, including when the native boundary is empty. -/
theorem exists_nonneg_time_mem_interior {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) (x : C.ambient.manifold.Point) :
    ∃ T : ℝ, 0 ≤ T ∧ C.ambient.completeFlow.flow (-T) x ∈
      C.inclusion.map '' interior D.domain.carrier := by
  by_cases hx : x ∈ C.inclusion.map '' D.domain.carrier
  · exact ⟨1, zero_le_one, C.negative_flow_mem_interior hx zero_lt_one⟩
  · have hc : x ∈ C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (univ ×ˢ Ici (0 : ℝ)) := by
      rw [C.covering]
      exact mem_univ _
    obtain ⟨⟨b, r⟩, hr, he⟩ := hc.resolve_left hx
    refine ⟨r + 1, add_nonneg hr.2 zero_le_one, ?_⟩
    have hcompact : C.endMap (b, 0) ∈ C.inclusion.map '' D.domain.carrier := by
      rw [C.endMap_zero]
      exact ⟨_, D.domain.boundaryInclusion_mem_carrier b, rfl⟩
    have hs : C.ambient.completeFlow.flow (-(r + 1)) x =
        C.ambient.completeFlow.flow (-1) (C.endMap (b, 0)) := by
      rw [← he, C.end_flow, C.endMap_zero, ← C.ambient.completeFlow.flow.map_add]
      congr 1
      ring
    rw [hs]
    exact C.negative_flow_mem_interior hcompact zero_lt_one

end Completion

namespace IntrinsicSmoothBundle

/-- Local real extensions of the compact formula and actual complete-flow
germs determine the whole completed map family. Finite negative absorption
is proved for native completions above; the return identity is flow
intertwining, rather than an assumption of smooth completed maps. -/
theorem hasSmoothManifoldTargetFamilyOn_of_interior_absorption
    {d e : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (f : Parameter → M.Point → N.Point) (V : Set M.Point)
    (φ : Parameter → ℝ → M.Point → M.Point)
    (ψ : Parameter → ℝ → N.Point → N.Point)
    (hφ : HasRealSmoothFlowGermsOn M univ φ)
    (hψ : HasRealSmoothFlowGermsOn N univ ψ)
    (habsorb : ∀ t x, ∃ T : ℝ, φ t (-T) x ∈ V)
    (hreturn : ∀ t r x, ψ t r (f t (φ t (-r) x)) = f t x)
    (hcompact : ∀ (t : Parameter) (x : M.Point), x ∈ V →
      ∃ U : TopologicalSpace.Opens (ℝ × M.Point), (t.val, x) ∈ U ∧
        ∃ γ : U → N.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ γ ∧
          ∀ (s : Parameter) y (hy : (s.val, y) ∈ U), γ ⟨(s.val, y), hy⟩ = f s y) :
    HasSmoothManifoldTargetFamilyOn M N univ f := by
  classical
  intro t _ x
  obtain ⟨T, hTy⟩ := habsorb t x
  let y := φ t (-T) x
  obtain ⟨A, hA, hpA, α, hα, heα⟩ := hφ t (mem_univ _) (-T) x
  obtain ⟨B, hpB, γ, hγ, heγ⟩ := hcompact t y hTy
  obtain ⟨C, hC, hpC, β, hβ, heβ⟩ := hψ t (mem_univ _) T (f t y)
  let H : ℝ × M.Point → ℝ × (ℝ × M.Point) := fun p => (p.1, (-T, p.2))
  have hH : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))) ∞ H :=
    contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)
  let U₀ : Set (ℝ × M.Point) := H ⁻¹' A
  have hU₀ : IsOpen U₀ := hA.preimage hH.continuous
  let p : ℝ × M.Point → ℝ × M.Point := fun z => (z.1, α (H z))
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞ p U₀ :=
    contMDiff_fst.contMDiffOn.prodMk (hα.comp hH.contMDiffOn (fun _ hz => hz))
  let γ' : ℝ × M.Point → N.Point := fun z => if hz : z ∈ B then γ ⟨z, hz⟩ else f t y
  have hγ' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ γ' B := by
    have he (z : B) : γ' z.val = γ z := by simp only [γ', dite_eq_left z.property]
    have hsm : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞
        (fun z : B => γ' z.val) := hγ.congr he
    intro z hz
    exact ((contMDiffAt_subtype_iff (f := γ') (x := (⟨z, hz⟩ : B))).mp
      hsm.contMDiffAt).contMDiffWithinAt
  let U₁ : Set (ℝ × M.Point) := U₀ ∩ p ⁻¹' B
  have hU₁ : IsOpen U₁ := hp.continuousOn.isOpen_inter_preimage hU₀ B.isOpen
  let q : ℝ × M.Point → ℝ × (ℝ × N.Point) := fun z => (z.1, (T, γ' (p z)))
  have hq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model e))) ∞ q U₁ :=
    contMDiff_fst.contMDiffOn.prodMk (contMDiff_const.contMDiffOn.prodMk
      (hγ'.comp (hp.mono inter_subset_left) (fun _ hz => hz.2)))
  let U : TopologicalSpace.Opens (ℝ × M.Point) :=
    ⟨U₁ ∩ q ⁻¹' C, hq.continuousOn.isOpen_inter_preimage hU₁ hC⟩
  have hpcenter : p (t.val, x) = (t.val, y) := by
    dsimp [p, H, y]
    rw [heα t (mem_univ _) (-T) x hpA]
  have hγcenter : γ' (p (t.val, x)) = f t y := by
    rw [hpcenter]
    simp only [γ', dite_eq_left hpB]
    exact heγ t y hpB
  have hcenter : (t.val, x) ∈ U := by
    refine ⟨⟨hpA, ?_⟩, ?_⟩
    · change p (t.val, x) ∈ B
      rw [hpcenter]
      exact hpB
    · change (t.val, (T, γ' (p (t.val, x)))) ∈ C
      rw [hγcenter]
      exact hpC
  let a : U → N.Point := fun z => β (q z.val)
  have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model e) ∞ a := by
    intro z
    exact (hβ.contMDiffAt (hC.mem_nhds z.property.2)).comp z
      ((hq.contMDiffAt (hU₁.mem_nhds z.property.1)).comp z
        contMDiff_subtype_val.contMDiffAt)
  refine ⟨U, hcenter, a, ha, ?_⟩
  intro s _ z hz
  have hpz : p (s.val, z) = (s.val, φ s (-T) z) := by
    dsimp [p, H]
    rw [heα s (mem_univ _) (-T) z hz.1.1]
  have hgz : γ' (p (s.val, z)) = f s (φ s (-T) z) := by
    have hm : (s.val, φ s (-T) z) ∈ B := hpz ▸ hz.1.2
    rw [hpz]
    simp only [γ', dite_eq_left hm]
    exact heγ s _ hm
  change β (s.val, (T, γ' (p (s.val, z)))) = _
  rw [heβ s (mem_univ _) T _ hz.2, hgz, hreturn]

end IntrinsicSmoothBundle
end FsFltz.Geometry
