import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineClopenIntersectionChart
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueHomeomorphism

/-! The exact zero set of an actual continuous adic function on an affine
scheme is realized by a weakly étale affine chart. -/

namespace ManuscriptAudit.ProetalePadicZeroSlice

open AlgebraicGeometry CategoryTheory
open AffineClopenIntersectionChart (chartRing chartMap chart_range chart_weaklyEtale)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private theorem residue_zero_clopen {V : Type} [TopologicalSpace V]
    (f : C(V, ℤ_[ℓ])) (n : ℕ) :
    IsClopen {x | PadicInt.toZModPow n (f x) = 0} :=
  (isClopen_discrete ({0} : Set (ZMod (ℓ ^ n)))).preimage
    ((PadicResidueHomeomorphism.reduction_continuous ℓ n).comp f.continuous)

theorem exists_spec_chart {R : CommRingCat.{0}} (f : C(Spec R, ℤ_[ℓ])) :
    ∃ (B : CommRingCat.{0}) (g : Spec B ⟶ Spec R),
      WeaklyEtale g ∧ Set.range g = {x | f x = 0} := by
  choose e he hset using fun n ↦ PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (residue_zero_clopen ℓ f n)
  refine ⟨CommRingCat.of (chartRing e), chartMap e, chart_weaklyEtale e he, ?_⟩
  rw [chart_range]
  ext x
  change (∀ n, x ∈ (PrimeSpectrum.basicOpen (e n) : Set (PrimeSpectrum R))) ↔ f x = 0
  constructor
  · intro h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    have hn := h n
    rw [← hset n] at hn
    simpa only [Set.mem_setOf_eq, map_zero] using hn
  · intro h n
    rw [← hset n]
    change PadicInt.toZModPow n (f x) = 0
    rw [h, map_zero]

/-- The zero slice in an arbitrary native affine chart. -/
theorem exists_affine_chart {T : Scheme.{0}} [IsAffine T] (f : C(T, ℤ_[ℓ])) :
    ∃ (V : Scheme.{0}) (g : V ⟶ T), IsAffine V ∧ WeaklyEtale g ∧
      Set.range g = {x | f x = 0} := by
  let e := T.isoSpec
  let F := f.comp ⟨e.inv, e.inv.continuous⟩
  obtain ⟨B, g, hg, hZero⟩ := exists_spec_chart ℓ F
  letI : WeaklyEtale g := hg
  refine ⟨Spec B, g ≫ e.inv, inferInstance, inferInstance, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : g y ∈ {z | F z = 0} := hZero ▸ ⟨y, rfl⟩
    exact hy
  · intro hx
    have he : e.inv (e.hom x) = x := congrArg (fun a : T ⟶ T ↦ a x) e.hom_inv_id
    have hz : e.hom x ∈ Set.range g := by
      rw [hZero]
      change f (e.inv (e.hom x)) = 0
      rw [he]
      exact hx
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, (congrArg e.inv hy).trans he⟩

end

end ManuscriptAudit.ProetalePadicZeroSlice

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetalePadicZeroSlice.exists_spec_chart,
      ``ManuscriptAudit.ProetalePadicZeroSlice.exists_affine_chart] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
