import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Modular
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# A compact truncation of the actual level-two modular quotient

Remove the projected high horoballs in all modular coordinates. The
remaining set is a compact image of finitely many closed subsets of
the truncated standard modular fundamental domain. This is the
all-cusp set underlying the truncation used in Paper 10, physical
pp. 465, 472, and 477. Compactness here concerns the quotient topology.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane

namespace ManuscriptAudit.CompactModularCore

open LiteralCuspTruncation (GammaTwo OrbitQuotient orbitPoint)

noncomputable section

abbrev Reduced := SL(2, ZMod 2)

def reduceTwo : SL(2, ℤ) →* Reduced :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

theorem mem_gamma_iff_reduced_one (g : SL(2, ℤ)) :
    g ∈ GammaTwo ↔ reduceTwo g = 1 := Iff.rfl

def boundedHeights (Y : ℝ) : Set ℍ :=
  {z | ∀ g : SL(2, ℤ), (g • z).im ≤ Y}

def core (Y : ℝ) : Set OrbitQuotient := orbitPoint '' boundedHeights Y

def highOrbits (Y : ℝ) : Set OrbitQuotient :=
  {q | ∃ (a : SL(2, ℤ)) (z : ℍ), Y < z.im ∧ orbitPoint (a • z) = q}

private theorem continuous_sl_smul (g : SL(2, ℤ)) : Continuous (fun z : ℍ => g • z) := by
  change Continuous (fun z : ℍ => (g : GL (Fin 2) ℝ) • z)
  exact continuous_const_smul _

private theorem continuous_orbitPoint : Continuous orbitPoint :=
  continuous_quotient_mk'

private theorem boundedHeights_smul {Y : ℝ} {z : ℍ} (hz : z ∈ boundedHeights Y)
    (a : SL(2, ℤ)) : a • z ∈ boundedHeights Y := by
  intro g
  simpa only [mul_smul] using hz (g * a)

theorem boundedHeights_closed (Y : ℝ) : IsClosed (boundedHeights Y) := by
  have heq : boundedHeights Y = ⋂ g : SL(2, ℤ), {z : ℍ | (g • z).im ≤ Y} := by
    ext z
    simp [boundedHeights]
  rw [heq]
  exact isClosed_iInter (fun g =>
    isClosed_le (UpperHalfPlane.continuous_im.comp (continuous_sl_smul g)) continuous_const)

theorem core_eq_complement_highOrbits (Y : ℝ) : core Y = (highOrbits Y)ᶜ := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩ ⟨a, u, hu, heq⟩
    have hOrbit : ∃ g : GammaTwo, g • z = a • u := Quotient.exact heq
    obtain ⟨g, hg⟩ := hOrbit
    change (g : SL(2, ℤ)) • z = a • u at hg
    have ha : (a⁻¹ * (g : SL(2, ℤ))) • z = u := by
      rw [mul_smul, hg, ← mul_smul, inv_mul_cancel, one_smul]
    have hb := hz (a⁻¹ * (g : SL(2, ℤ)))
    rw [ha] at hb
    exact (not_lt_of_ge hb) hu
  · refine Quotient.inductionOn q ?_
    intro z h
    refine ⟨z, ?_, rfl⟩
    intro g
    by_contra! hgt
    exact h ⟨g⁻¹, g • z, hgt,
      congrArg orbitPoint (by rw [← mul_smul, inv_mul_cancel, one_smul])⟩

private def chooseLift (r : Reduced) : SL(2, ℤ) := by
  classical
  exact if h : ∃ a : SL(2, ℤ), reduceTwo a = r then Classical.choose h else 1

private theorem reduce_chooseLift (g : SL(2, ℤ)) :
    reduceTwo (chooseLift (reduceTwo g)) = reduceTwo g := by
  have h : ∃ a : SL(2, ℤ), reduceTwo a = reduceTwo g := ⟨g, rfl⟩
  rw [chooseLift, dif_pos h]
  exact Classical.choose_spec h

/-- The corrected all-cusp truncation is compact in the quotient topology. -/
theorem isCompact_core (Y : ℝ) : IsCompact (core Y) := by
  let F := ModularGroup.truncatedFundamentalDomain Y ∩ boundedHeights Y
  have hF : IsCompact F :=
    (ModularGroup.isCompact_truncatedFundamentalDomain Y).inter_right (boundedHeights_closed Y)
  have hCover : core Y =
      ⋃ r : Reduced, (fun z : ℍ => orbitPoint (chooseLift r • z)) '' F := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
      let r := reduceTwo g⁻¹
      have hred : reduceTwo (chooseLift r * g) = 1 := by
        change reduceTwo (chooseLift (reduceTwo g⁻¹) * g) = 1
        rw [map_mul, reduce_chooseLift (g⁻¹), map_inv, inv_mul_cancel]
      let k : GammaTwo := ⟨chooseLift r * g, (mem_gamma_iff_reduced_one _).mpr hred⟩
      have hk : k • z = chooseLift r • (g • z) := by
        change (chooseLift r * g) • z = _
        exact mul_smul _ _ _
      apply Set.mem_iUnion.2
      refine ⟨r, g • z, ⟨⟨hg, hz g⟩, boundedHeights_smul hz g⟩, ?_⟩
      exact Quotient.sound ⟨k, hk⟩
    · intro hq
      obtain ⟨r, z, hz, rfl⟩ := Set.mem_iUnion.1 hq
      exact ⟨chooseLift r • z, boundedHeights_smul hz.2 _, rfl⟩
  rw [hCover]
  exact isCompact_iUnion (fun r => hF.image
    (continuous_orbitPoint.comp (continuous_sl_smul (chooseLift r))))

theorem core_monotone : Monotone core := by
  intro Y Y' hY
  rintro q ⟨z, hz, rfl⟩
  exact ⟨z, fun g => (hz g).trans hY, rfl⟩

theorem core_exhausts : (⋃ Y : ℝ, core Y) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  obtain ⟨g, hg⟩ := ModularGroup.exists_max_im z
  exact Set.mem_iUnion.2 ⟨(g • z).im, z, hg, rfl⟩

end

end ManuscriptAudit.CompactModularCore

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CompactModularCore.core_eq_complement_highOrbits,
      ``ManuscriptAudit.CompactModularCore.isCompact_core,
      ``ManuscriptAudit.CompactModularCore.core_monotone,
      ``ManuscriptAudit.CompactModularCore.core_exhausts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
