import FsFltz.Core
import Mathlib.Topology.Connected.Clopen

/-!
# Global invariance from the local integral-curve conclusion

Source: `geometric-part-fsf-proof.tex`, `lem:invariance`, lines 1650–1658,
and `thm:core`, line 1737. The native conormal application supplies
local preservation by a constructed restricted ODE.
-/

namespace FsFltz

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- The times at which a continuous curve lies in a closed locally preserved
set are clopen, hence comprise the entire real line once nonempty. -/
theorem mem_closed_of_locally_mem {A : Set X} (hA : IsClosed A)
    {γ : ℝ → X} (hγ : Continuous γ)
    (hlocal : ∀ t, γ t ∈ A → ∀ᶠ s in 𝓝 t, γ s ∈ A)
    {t₀ : ℝ} (ht₀ : γ t₀ ∈ A) (t : ℝ) : γ t ∈ A := by
  have hopen : IsOpen (γ ⁻¹' A) := isOpen_iff_mem_nhds.mpr hlocal
  have heq := (show IsClopen (γ ⁻¹' A) from ⟨hA.preimage hγ, hopen⟩).eq_univ
    ⟨t₀, ht₀⟩
  exact (show t ∈ γ ⁻¹' A from heq ▸ mem_univ t)

/-- Local preservation at time zero on a closed set gives both-time invariance. -/
theorem flow_isInvariant_of_closed_local (F : Flow ℝ X) {A : Set X}
    (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∀ᶠ t in 𝓝 (0 : ℝ), F t x ∈ A) :
    IsInvariant F A := by
  intro t x hx
  refine mem_closed_of_locally_mem hA
    (F.continuous continuous_id (continuous_const (y := x))) ?_
    (t₀ := 0) (by simpa using hx) t
  intro s hs
  have hshift : Tendsto (fun r : ℝ => r - s) (𝓝 s) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => r - s) := by fun_prop
    simpa only [sub_self] using hcont.tendsto s
  filter_upwards [hshift.eventually (hlocal (F s x) hs)] with r hr
  simpa only [← F.map_add, sub_add_cancel, id_eq] using hr

/-- Compactness and actual invariance provide the forward-orbit half of the
full-core argument, without a trapping or critical-set hypothesis. -/
theorem isCompact_closure_forwardOrbit_of_mem_invariant [T2Space X]
    (F : Flow ℝ X) {A : Set X} (hA : IsCompact A) (hinv : IsInvariant F A)
    {x : X} (hx : x ∈ A) : IsCompact (closure (F.forwardOrbit x)) := by
  apply hA.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hA.isClosed
  rintro y ⟨t, rfl⟩
  exact hinv t hx

end FsFltz
