import FsFltz.Geometry.FlowBridge
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Order.Compact

/-!
# Uniqueness of completion boundary representatives

The nonnegative end is a closed embedding. Its compact preimages bound the
radial coordinate, so every strict completion diffeomorphism produces unique
boundary representatives and shifts at the set level. The all-real-time flow
extends the end equation from one time or large times to every real time.

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 181–189, and `sec:lean`,
lines 805–814. `BoundarySmooth` proves smoothness and smooth invertibility
of the produced boundary coordinates; `BoundaryContact` derives their
primitive pullback law.
-/

noncomputable section
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry
open SmoothManifold
open Topology Filter

/-- An immersion between smooth extension manifolds of the same dimension
is an open map. The inverse function theorem is applied in actual charts. -/
theorem SmoothManifold.SmoothEmbedding.isOpenMap {d : ℕ}
    {M N : SmoothManifold d} (f : M.SmoothEmbedding N) : IsOpenMap f.map := by
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  let c := chartAt (Model d) x
  let c' := chartAt (Model d) (f.map x)
  have hx : x ∈ c.source := mem_chart_source _ _
  have hx' : f.map x ∈ c'.source := mem_chart_source _ _
  have hcx : c.symm (c x) = x := c.left_inv hx
  have hcinv := (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model d)) (n := ∞) (x := x)).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hx))
  have hc' := (contMDiffOn_chart (I := 𝓘(ℝ, Model d)) (n := ∞) (x := f.map x)).contMDiffAt
    (c'.open_source.mem_nhds hx')
  let g : Model d → Model d := c' ∘ f.map ∘ c.symm
  have hfx := f.map.contMDiff x
  have hg : ContDiffAt ℝ ∞ g (c x) := by
    have hfc := (f.map.contMDiff (c.symm (c x))).comp (c x) hcinv
    have hc'' : ContMDiffAt 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) ∞ c'
        ((f.map ∘ c.symm) (c x)) := by
      simpa only [Function.comp_apply, hcx] using hc'
    exact (hc''.comp (c x) hfc).contDiffAt
  have hgd : Function.Bijective (fderiv ℝ g (c x)) := by
    have hd := mfderiv_comp (f := c.symm) (g := c' ∘ f.map) (c x)
      (by simpa only [hcx] using (hc'.comp x hfx).mdifferentiableAt (by simp))
      (hcinv.mdifferentiableAt (by simp))
    rw [hcx, mfderiv_comp x (hc'.mdifferentiableAt (by simp))
      (hfx.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hd
    change Function.Bijective (fderiv ℝ ((c' ∘ f.map) ∘ c.symm) (c x))
    rw [hd]
    have hdf : Function.Bijective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) f.map x) :=
      ⟨f.immersion x, LinearMap.injective_iff_surjective.mp (f.immersion x)⟩
    exact (((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) (f.map x)).mfderiv_bijective hx').comp
      hdf).comp
        ((mdifferentiable_chart (I := 𝓘(ℝ, Model d)) x).symm.mfderiv_bijective (c.map_source hx))
  let A : Model d ≃L[ℝ] Model d :=
    (LinearEquiv.ofBijective (fderiv ℝ g (c x)).toLinearMap hgd).toContinuousLinearEquiv
  have hder : HasStrictFDerivAt g (A : Model d →L[ℝ] Model d) (c x) :=
    hg.hasStrictFDerivAt (by simp)
  have he := congrArg (Filter.map c'.symm) hder.map_nhds_eq_of_equiv
  have hmaps : Filter.map (c'.symm ∘ c' ∘ f.map) (𝓝 x) = 𝓝 (f.map x) := by
    simpa only [g, Function.comp_apply, Filter.map_map, Function.comp_assoc, ← Filter.map_map,
      c.symm.map_nhds_eq (c.map_source hx), c'.symm.map_nhds_eq (c'.map_source hx'),
      hcx, c'.left_inv hx'] using he
  have heq : (c'.symm ∘ c' ∘ f.map) =ᶠ[𝓝 x] f.map := by
    filter_upwards [f.map.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (c'.open_source.mem_nhds hx')] with y hy
    exact c'.left_inv hy
  rw [Filter.map_congr heq] at hmaps
  exact hmaps.ge

namespace Completion

/-- The end parametrization uses the specified complete flow at every time. -/
theorem flow_endMap {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (x : D.domain.boundary.Point) (r t : ℝ) :
    C.ambient.completeFlow.flow t (C.endMap (x, r)) = C.endMap (x, t + r) := by
  rw [C.end_flow, C.end_flow, Flow.map_add]

@[simp]
theorem endMap_zero {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (x : D.domain.boundary.Point) :
    C.endMap (x, 0) = C.inclusion.map (D.domain.boundaryInclusion.map x) := by
  rw [C.end_flow, Flow.map_zero_apply]

/-- Translating both end points far enough forward reduces uniqueness at
arbitrary real times to the bundled nonnegative-end embedding. -/
theorem endMap_injective {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    Function.Injective C.endMap := by
  rintro ⟨x, r⟩ ⟨y, s⟩ h
  let t : ℝ := max (-r) (-s)
  have hr : 0 ≤ t + r := by dsimp [t]; linarith [le_max_left (-r) (-s)]
  have hs : 0 ≤ t + s := by dsimp [t]; linarith [le_max_right (-r) (-s)]
  have he := congrArg (C.ambient.completeFlow.flow t) h
  rw [C.flow_endMap, C.flow_endMap] at he
  have hp : (x, (⟨t + r, hr⟩ : Set.Ici (0 : ℝ))) =
      (y, (⟨t + s, hs⟩ : Set.Ici (0 : ℝ))) := C.end_embedding.injective he
  have hxy : x = y := congrArg Prod.fst hp
  have hrs : r = s := add_left_cancel (congrArg (fun p => p.2.val) hp)
  exact Prod.ext hxy hrs

/-- Both the boundary representative and the time coordinate are determined
by the point of the completed ambient. -/
theorem endMap_eq_iff {d : ℕ} {D : LiouvilleDomain d} (C : Completion D)
    (x y : D.domain.boundary.Point) (r s : ℝ) :
    C.endMap (x, r) = C.endMap (y, s) ↔ x = y ∧ r = s := by
  constructor
  · intro h
    exact Prod.mk.inj (C.endMap_injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The nonnegative end is precisely the complement of the compact piece's
interior; its time-zero section is the actual compact boundary. -/
theorem range_nonnegative_endMap {d : ℕ} {D : LiouvilleDomain d} (C : Completion D) :
    Set.range (fun p : D.domain.boundary.Point × Set.Ici (0 : ℝ) =>
      C.endMap (p.1, p.2)) = (C.inclusion.map '' interior D.domain.carrier)ᶜ := by
  ext z
  constructor
  · rintro ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ ⟨y, hy, he⟩
    change C.inclusion.map y = C.endMap (x, r) at he
    have hr' : 0 ≤ r := hr
    rcases eq_or_lt_of_le hr' with hr' | hr'
    · subst r
      rw [C.endMap_zero] at he
      have hb : D.domain.boundaryInclusion.map x ∈ frontier D.domain.carrier := by
        rw [← D.domain.boundary_range]
        exact ⟨x, rfl⟩
      rw [D.domain.compact.isClosed.frontier_eq] at hb
      exact hb.2 (C.inclusion.embedding.injective he ▸ hy)
    · exact C.overlap x r hr' ⟨y, interior_subset hy, he⟩
  · intro hz
    have hc : z ∈ C.inclusion.map '' D.domain.carrier ∪
        C.endMap '' (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
      rw [C.covering]
      exact Set.mem_univ z
    rcases hc with ⟨y, hy, rfl⟩ | ⟨⟨x, r⟩, ⟨_, hr⟩, rfl⟩
    · have hy' : y ∈ frontier D.domain.carrier := by
        rw [D.domain.compact.isClosed.frontier_eq]
        exact ⟨hy, fun h => hz ⟨y, h, rfl⟩⟩
      rw [← D.domain.boundary_range] at hy'
      obtain ⟨x, rfl⟩ := hy'
      exact ⟨(x, ⟨0, by simp⟩), C.endMap_zero x⟩
    · exact ⟨(x, ⟨r, hr⟩), rfl⟩

/-- The bundled end embedding is proper: its range is closed because the
compact-piece inclusion is open on its interior. -/
theorem isClosedEmbedding_nonnegative_endMap {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) :
    Topology.IsClosedEmbedding (fun p : D.domain.boundary.Point × Set.Ici (0 : ℝ) =>
      C.endMap (p.1, p.2)) := by
  refine ⟨C.end_embedding, ?_⟩
  rw [C.range_nonnegative_endMap]
  exact (C.inclusion.isOpenMap _ isOpen_interior).isClosed_compl

/-- Every compact subset has a uniform upper bound on the time coordinate
of end points it contains. In particular every boundary ray escapes it. -/
theorem endMap_eventually_not_mem_compact {d : ℕ} {D : LiouvilleDomain d}
    (C : Completion D) {K : Set C.ambient.manifold.Point} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (x : D.domain.boundary.Point) (r : ℝ), R ≤ r →
      C.endMap (x, r) ∉ K := by
  let e : D.domain.boundary.Point × Set.Ici (0 : ℝ) → C.ambient.manifold.Point :=
    fun p => C.endMap (p.1, p.2)
  have hc : IsCompact (e ⁻¹' K) := C.isClosedEmbedding_nonnegative_endMap.isCompact_preimage hK
  have ht : Continuous (fun p : D.domain.boundary.Point × Set.Ici (0 : ℝ) => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  obtain ⟨b, hb⟩ := (hc.image ht).bddAbove
  refine ⟨max 0 (b + 1), le_max_left _ _, ?_⟩
  intro x r hr hmem
  have hr0 : 0 ≤ r := (le_max_left _ _).trans hr
  have hbound : r ≤ b := hb ⟨(x, ⟨r, hr0⟩), hmem, rfl⟩
  linarith [le_max_right 0 (b + 1)]

/-- One equality on a boundary trajectory determines a strict ambient map
on that whole trajectory, at every real time. -/
theorem map_endMap_of_eq {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive)
    (x : D.domain.boundary.Point) (y : E.domain.boundary.Point) (s r₀ : ℝ)
    (hend : f (C.endMap (x, r₀)) = C'.endMap (y, r₀ + s)) (r : ℝ) :
    f (C.endMap (x, r)) = C'.endMap (y, r + s) := by
  have he := congrArg (C'.ambient.completeFlow.flow (r - r₀)) hend
  rw [← C.ambient.map_flow C'.ambient f hprimitive, C.flow_endMap,
    C'.flow_endMap] at he
  simpa only [← add_assoc, sub_add_cancel] using he

/-- For a strict ambient diffeomorphism, an end equation valid at all
sufficiently large times determines its value at every real time. -/
theorem map_endMap_of_eventually {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive)
    (x : D.domain.boundary.Point) (y : E.domain.boundary.Point) (s : ℝ)
    (hend : ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r →
      f (C.endMap (x, r)) = C'.endMap (y, r + s)) (r : ℝ) :
    f (C.endMap (x, r)) = C'.endMap (y, r + s) := by
  obtain ⟨r₀, hend⟩ := hend
  exact C.map_endMap_of_eq C' f hprimitive x y s r₀ (hend r₀ le_rfl) r

/-- Every strict completion diffeomorphism produces a unique boundary
representative and real shift, using actual escape from the target compact
piece and its covering by the compact piece and the end. No boundary map or
end equation is assumed. Smoothness of the resulting coordinates is separate. -/
theorem existsUnique_boundary_coordinates {d e : ℕ} {D : LiouvilleDomain d}
    {E : LiouvilleDomain e} (C : Completion D) (C' : Completion E)
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (hprimitive : C.ambient.manifold.pullback C'.ambient.manifold f
      C'.ambient.primitive = C.ambient.primitive) (x : D.domain.boundary.Point) :
    ∃! p : E.domain.boundary.Point × ℝ, ∀ r : ℝ,
      f (C.endMap (x, r)) = C'.endMap (p.1, r + p.2) := by
  have hK : IsCompact (f.symm '' (C'.inclusion.map '' E.domain.carrier)) :=
    (E.domain.compact.image C'.inclusion.map.contMDiff.continuous).image
      f.symm.contMDiff.continuous
  obtain ⟨R, _, hR⟩ := C.endMap_eventually_not_mem_compact hK
  have hn : f (C.endMap (x, R)) ∉ C'.inclusion.map '' E.domain.carrier := by
    intro hy
    exact hR x R le_rfl ⟨f (C.endMap (x, R)), hy, f.symm_apply_apply _⟩
  have hc : f (C.endMap (x, R)) ∈ C'.inclusion.map '' E.domain.carrier ∪
      C'.endMap '' (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
    rw [C'.covering]
    exact Set.mem_univ _
  rcases hc with hc | ⟨⟨y, t⟩, _, he⟩
  · exact False.elim (hn hc)
  · have he' : f (C.endMap (x, R)) = C'.endMap (y, R + (t - R)) := by
      rw [show R + (t - R) = t by ring]
      exact he.symm
    have hall := C.map_endMap_of_eq C' f hprimitive x y (t - R) R he'
    refine ⟨(y, t - R), hall, ?_⟩
    intro p hp
    have hp0 := hp 0
    have hy0 := hall 0
    simp only [zero_add] at hp0 hy0
    exact C'.endMap_injective (hp0.symm.trans hy0)

end Completion

namespace CompletionIdentification

/-- The induced boundary coordinates recorded at infinity describe the same
strict map at every real time, including the chosen source boundary section. -/
theorem map_endMap {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (x : P.ambientDomain.domain.boundary.Point)
    (r : ℝ) :
    h.ambientEquiv (P.ambientCompletion.endMap (x, r)) =
      Q.ambientCompletion.endMap (h.boundaryEquiv x, r + h.shift x) :=
  P.ambientCompletion.map_endMap_of_eventually Q.ambientCompletion h.ambientEquiv
    h.primitive x (h.boundaryEquiv x) (h.shift x) (h.induced_at_infinity x) r

/-- The map on the actual source boundary section determines its boundary
representative and time shift uniquely. -/
theorem boundary_coordinates_iff {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (x : P.ambientDomain.domain.boundary.Point)
    (y : Q.ambientDomain.domain.boundary.Point) (s : ℝ) :
    h.ambientEquiv (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x)) =
        Q.ambientCompletion.endMap (y, s) ↔ h.boundaryEquiv x = y ∧ h.shift x = s := by
  have he := h.map_endMap x 0
  simp only [Completion.endMap_zero, zero_add] at he
  rw [he, Q.ambientCompletion.endMap_eq_iff]

/-- In particular, a strict map carrying one chosen boundary point to another
has zero shift there and its induced boundary map carries those same points.
This is the boundary-section argument used in `lem:choices`, lines 455–459. -/
theorem boundary_fixed_of_boundary_sections {n : ℕ} {P Q : WitnessedPair n}
    (h : CompletionIdentification P Q) (x : P.ambientDomain.domain.boundary.Point)
    (y : Q.ambientDomain.domain.boundary.Point)
    (hxy : h.ambientEquiv (P.ambientCompletion.inclusion.map
      (P.ambientDomain.domain.boundaryInclusion.map x)) =
      Q.ambientCompletion.inclusion.map (Q.ambientDomain.domain.boundaryInclusion.map y)) :
    h.boundaryEquiv x = y ∧ h.shift x = 0 := by
  apply (h.boundary_coordinates_iff x y 0).mp
  simpa only [Completion.endMap_zero] using hxy

/-- Two completion identifications with the same ambient diffeomorphism
cannot select different boundary representatives or different time shifts. -/
theorem boundary_data_unique {n : ℕ} {P Q : WitnessedPair n}
    (h k : CompletionIdentification P Q) (hf : h.ambientEquiv = k.ambientEquiv)
    (x : P.ambientDomain.domain.boundary.Point) :
    h.boundaryEquiv x = k.boundaryEquiv x ∧ h.shift x = k.shift x := by
  apply (h.boundary_coordinates_iff x (k.boundaryEquiv x) (k.shift x)).mp
  rw [hf]
  simpa only [Completion.endMap_zero, zero_add] using k.map_endMap x 0

end CompletionIdentification

end FsFltz.Geometry
