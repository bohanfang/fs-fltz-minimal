import FsFltz.Geometry.CompactMapNeighborhood

/-!
# Compact diffeomorphisms from a common embedded image

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and the presentation junction, lines 2236–2243. Equal images of actual
same-dimensional smooth embeddings construct a compact diffeomorphism;
its square holds on open neighborhoods, hence also on full boundary tangents.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

namespace SmoothManifold.SmoothEmbedding

/-- A same-dimensional smooth embedding is a local diffeomorphism. -/
theorem isLocalDiffeomorph {d : ℕ} {M N : SmoothManifold d}
    (j : M.SmoothEmbedding N) :
    IsLocalDiffeomorph 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ j.map := by
  intro x
  apply isLocalDiffeomorphAt_of_bijective_mfderiv_manifold isOpen_univ
    j.map.contMDiff.contMDiffOn (mem_univ x)
  exact ⟨j.immersion x, LinearMap.injective_iff_surjective.mp (j.immersion x)⟩

/-- The set-theoretic inverse is smooth on the open image of the embedding. -/
theorem contMDiffOn_invFun {d : ℕ} {M N : SmoothManifold d}
    [Nonempty M.Point] (j : M.SmoothEmbedding N) :
    ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞
      (Function.invFun j.map) (range j.map) := by
  classical
  rintro _ ⟨x, rfl⟩
  let l := j.isLocalDiffeomorph x
  have h := l.localInverse_contMDiffOn.contMDiffAt
    (l.localInverse.open_source.mem_nhds l.localInverse_mem_source)
  apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [l.localInverse.open_source.mem_nhds l.localInverse_mem_source] with y hy
  apply j.embedding.injective
  exact (Function.invFun_eq ⟨l.localInverse y, l.localInverse_right_inv hy⟩).trans
    (l.localInverse_right_inv hy).symm

end SmoothManifold.SmoothEmbedding

namespace CompactDomain

/-- Equality of full embedded carriers produces the actual compact
diffeomorphism. Both map squares hold on open neighborhoods, not just on
the carrier; no primitive or completed comparison is assumed. -/
theorem exists_compactDiffeomorph_of_commonEmbedding {d : ℕ}
    (D E : CompactDomain d) (M : SmoothManifold d)
    (hD : D.carrier.Nonempty)
    (j : D.extension.SmoothEmbedding M) (k : E.extension.SmoothEmbedding M)
    (himage : j.map '' D.carrier = k.map '' E.carrier) :
    ∃ h : CompactDomainDiffeomorph D E,
      (∀ x ∈ h.sourceNeighbourhood, k.map (h.map x) = j.map x) ∧
      (∀ y ∈ h.targetNeighbourhood, j.map (h.inverse y) = k.map y) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD
  obtain ⟨y₀, _hy₀, _he₀⟩ := himage ▸ (show j.map x₀ ∈ j.map '' D.carrier from ⟨x₀, hx₀, rfl⟩)
  let : Nonempty D.extension.Point := ⟨x₀⟩
  let : Nonempty E.extension.Point := ⟨y₀⟩
  let u : D.extension.Point → E.extension.Point := Function.invFun k.map ∘ j.map
  let v : E.extension.Point → D.extension.Point := Function.invFun j.map ∘ k.map
  let U : Set D.extension.Point := j.map ⁻¹' range k.map
  let V : Set E.extension.Point := k.map ⁻¹' range j.map
  have hU : IsOpen U := k.isLocalDiffeomorph.image.isOpen.preimage j.map.contMDiff.continuous
  have hV : IsOpen V := j.isLocalDiffeomorph.image.isOpen.preimage k.map.contMDiff.continuous
  have hu (x) (hx : x ∈ U) : k.map (u x) = j.map x := by
    obtain ⟨y, hy⟩ := hx
    change k.map (Function.invFun k.map (j.map x)) = j.map x
    exact Function.invFun_eq ⟨y, hy⟩
  have hv (y) (hy : y ∈ V) : j.map (v y) = k.map y := by
    obtain ⟨x, hx⟩ := hy
    change j.map (Function.invFun j.map (k.map y)) = k.map y
    exact Function.invFun_eq ⟨x, hx⟩
  have hDU : D.carrier ⊆ U := by
    intro x hx
    obtain ⟨y, _, he⟩ := himage ▸ (show j.map x ∈ j.map '' D.carrier from ⟨x, hx, rfl⟩)
    exact ⟨y, he⟩
  have hEV : E.carrier ⊆ V := by
    intro y hy
    obtain ⟨x, _, he⟩ := himage.symm ▸ (show k.map y ∈ k.map '' E.carrier from ⟨y, hy, rfl⟩)
    exact ⟨x, he⟩
  have hus : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ u U :=
    k.contMDiffOn_invFun.comp j.map.contMDiff.contMDiffOn (fun _ hx => hx)
  have hvs : ContMDiffOn 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ v V :=
    j.contMDiffOn_invFun.comp k.map.contMDiff.contMDiffOn (fun _ hy => hy)
  have hmap : MapsTo u D.carrier E.carrier := by
    intro x hx
    obtain ⟨y, hy, he⟩ := himage ▸ (show j.map x ∈ j.map '' D.carrier from ⟨x, hx, rfl⟩)
    have huy : u x = y := k.embedding.injective ((hu x (hDU hx)).trans he.symm)
    exact huy ▸ hy
  have hinv : MapsTo v E.carrier D.carrier := by
    intro y hy
    obtain ⟨x, hx, he⟩ := himage.symm ▸ (show k.map y ∈ k.map '' E.carrier from ⟨y, hy, rfl⟩)
    have hvx : v y = x := j.embedding.injective ((hv y (hEV hy)).trans he.symm)
    exact hvx ▸ hx
  have himm (x) (hx : x ∈ D.carrier) : Function.Injective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) u x) := by
    have heq : (k.map ∘ u) =ᶠ[𝓝 x] j.map := by
      filter_upwards [hU.mem_nhds (hDU hx)] with y hy
      exact hu y hy
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
    rw [mfderiv_comp x (k.map.contMDiff.mdifferentiableAt (by simp))
      ((hus.contMDiffAt (hU.mem_nhds (hDU hx))).mdifferentiableAt (by simp))] at hd
    change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) k.map (u x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) u x) =
        mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map x at hd
    intro a b hab
    apply j.immersion x
    rw [← hd]
    exact congrArg (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) k.map (u x)) hab
  refine ⟨{ map := u
            inverse := v
            sourceNeighbourhood := U
            targetNeighbourhood := V
            open_source := hU
            open_target := hV
            contains_source := hDU
            contains_target := hEV
            smooth_map := hus
            smooth_inverse := hvs
            maps_source := hmap
            maps_target := hinv
            left_inverse := ?_
            right_inverse := ?_
            immersion := himm }, hu, hv⟩
  · intro x hx
    apply j.embedding.injective
    exact (hv (u x) (hEV (hmap hx))).trans (hu x (hDU hx))
  · intro y hy
    apply k.embedding.injective
    exact (hu (v y) (hDU (hinv hy))).trans (hv y (hEV hy))

end CompactDomain

namespace CompactDomainDiffeomorph

/-- An open embedding square gives the exact pullback identity on every
compact point, including boundary points and dimension zero. -/
theorem pullback_of_commonEmbedding {d r : ℕ} {D E : CompactDomain d}
    (h : CompactDomainDiffeomorph D E) (M : SmoothManifold d)
    (j : D.extension.SmoothEmbedding M) (k : E.extension.SmoothEmbedding M)
    (hsquare : ∀ x ∈ h.sourceNeighbourhood, k.map (h.map x) = j.map x)
    (α : M.Form r) (x : D.extension.Point) (hx : x ∈ D.carrier) :
    D.extension.pullback E.extension h.map (E.extension.pullback M k.map α) x =
      D.extension.pullback M j.map α x := by
  have heq : (k.map ∘ h.map) =ᶠ[𝓝 x] j.map := by
    filter_upwards [h.open_source.mem_nhds (h.contains_source hx)] with y hy
    exact hsquare y hy
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, Model d)) (I' := 𝓘(ℝ, Model d))
  rw [mfderiv_comp x (k.map.contMDiff.mdifferentiableAt (by simp))
    ((h.smooth_map.contMDiffAt (h.open_source.mem_nhds (h.contains_source hx))).mdifferentiableAt
      (by simp))] at hd
  change (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) k.map (h.map x)).comp
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.map x) =
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map x at hd
  unfold SmoothManifold.pullback
  ext v
  change α (k.map (h.map x))
    (fun i => ((mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) k.map (h.map x)).comp
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) h.map x)) (v i)) = _
  rw [hd, hsquare x (h.contains_source hx)]
  rfl

end CompactDomainDiffeomorph
end FsFltz.Geometry
