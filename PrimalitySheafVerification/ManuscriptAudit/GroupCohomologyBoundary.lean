import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! The degree-one coboundaries needed for descent across the unit sequence. -/

namespace ManuscriptAudit.GroupCohomologyBoundary

open CategoryTheory
open groupCohomology

universe u

variable {G : Type u} {R : Type u} [Group G] [CommRing R]

theorem HOne_subsingleton_of_middle_and_HTwo
    (S : ShortComplex (Rep R G)) (hS : S.ShortExact)
    (hMiddle : Subsingleton (groupCohomology S.X₂ 1))
    (hFirst : Subsingleton (groupCohomology S.X₁ 2)) :
    Subsingleton (groupCohomology S.X₃ 1) := by
  have hZero : Limits.IsZero (groupCohomology S.X₂ 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr hMiddle
  let ψ := δ hS 1 2 rfl
  have hMono : Mono ψ := mono_δ_of_isZero hS 1 hZero
  have hInj := (ModuleCat.mono_iff_injective ψ).mp hMono
  exact ⟨fun x y => hInj (hFirst.elim (ψ x) (ψ y))⟩

theorem exists_principal_cocycle_of_HOne_subsingleton (A : Rep R G)
    (hOne : Subsingleton (groupCohomology A 1)) (c : G → A)
    (hc : ∀ g h, c (g * h) = c g + A.ρ g (c h)) :
    ∃ a : A, ∀ g, c g = A.ρ g a - a := by
  have hc' : c ∈ cocycles₁ A := (mem_cocycles₁_iff (A := A) c).mpr
    (fun g h => (hc g h).trans (add_comm _ _))
  let b : cocycles₁ A := ⟨c, hc'⟩
  have hb : H1π A b = 0 := hOne.elim _ _
  obtain ⟨a, ha⟩ := (H1π_eq_zero_iff b).mp hb
  exact ⟨a, fun g => (congrFun ha g).symm⟩

end ManuscriptAudit.GroupCohomologyBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GroupCohomologyBoundary.HOne_subsingleton_of_middle_and_HTwo,
      ``ManuscriptAudit.GroupCohomologyBoundary.exists_principal_cocycle_of_HOne_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
