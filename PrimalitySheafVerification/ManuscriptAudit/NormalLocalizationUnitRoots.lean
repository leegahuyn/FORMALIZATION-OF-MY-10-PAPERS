import Lean.Util.CollectAxioms
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic

/-! A unit on a normal affine domain can acquire a d-th root on a
nonempty principal open only if the root was already a global unit. -/

namespace ManuscriptAudit.NormalLocalizationUnitRoots

noncomputable section

variable (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- Restriction to a nonempty principal open detects powers of global
units in a normal domain. The given root extends as a unit. -/
theorem unit_root_extends (s : R) (hs : s ≠ 0) (d : ℕ) (hd : 0 < d) (v : Rˣ)
    (w : (Localization.Away s)ˣ)
    (hw : w ^ d = Units.map (algebraMap R (Localization.Away s)).toMonoidHom v) :
    ∃ u : Rˣ, u ^ d = v ∧
      Units.map (algebraMap R (Localization.Away s)).toMonoidHom u = w := by
  let S := Localization.Away s
  let F := FractionRing R
  have hR : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hsF : IsUnit (algebraMap R F s) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hR).mpr hs)
  let g : S →ₐ[R] F :=
    IsLocalization.Away.liftAlgHom s (f := Algebra.ofId R F) hsF
  have hg : Function.Injective g := by
    apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers s) S
      g.toRingHom
    intro a ha
    change g (algebraMap R S a) = 0 at ha
    rw [AlgHom.commutes] at ha
    have h0 : a = 0 := hR (ha.trans (map_zero _).symm)
    rw [h0, map_zero]
  have hpow : (g (w : S)) ^ d = algebraMap R F (v : R) := by
    have h := congrArg (fun t : Sˣ => g (t : S)) hw
    change g ((w : S) ^ d) = g (algebraMap R S (v : R)) at h
    rwa [map_pow, AlgHom.commutes] at h
  have hint : IsIntegral R ((g (w : S)) ^ d) := by
    rw [hpow]
    exact isIntegral_algebraMap
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hd hint
  have hbd : b ^ d = (v : R) := by
    apply hR
    rw [map_pow, hb, hpow]
  have hb' : IsUnit b := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [pow_succ] at hbd
    exact (IsUnit.mul_iff.mp (hbd.symm ▸ v.isUnit)).2
  refine ⟨hb'.unit, Units.ext ?_, Units.ext ?_⟩
  · change (↑hb'.unit : R) ^ d = (v : R)
    rwa [IsUnit.unit_spec]
  · change algebraMap R S (↑hb'.unit : R) = (w : S)
    rw [IsUnit.unit_spec]
    apply hg
    rw [AlgHom.commutes, hb]

end
end ManuscriptAudit.NormalLocalizationUnitRoots

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NormalLocalizationUnitRoots.unit_root_extends
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
