import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.QuotientRing
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicDerivedTor
import PrimalitySheafVerification.ManuscriptAudit.ZModGcdCyclicKernel

/-! The exact gcd calculation for the native derived Tor of integer residues. -/

namespace ManuscriptAudit.IntCyclicDerivedTorGcd

open CategoryTheory CategoryTheory.MonoidalCategory
open IntCyclicProjectiveResolution (residues)

noncomputable section

private abbrev C := ModuleCat.{0} ℤ

private def quotientResidueIso (n : ℕ) :
    residues n ≅ ModuleCat.of ℤ (ZMod n) := by
  let e := (Int.quotientSpanNatEquivZMod n).toAddEquiv
  let el : (ℤ ⧸ IntCyclicProjectiveResolution.ideal n) ≃ₗ[ℤ] ZMod n :=
    { e with map_smul' := fun a x ↦ e.map_zsmul x a }
  exact el.toModuleIso

/-- Degree-one native derived Tor is the residue module of the gcd, with its
actual integral module structure. The first positive modulus is ordered as
the module argument and the second as the resolved argument. -/
def torOneIsoGcdResidues (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((Tor C 1).obj (ModuleCat.of ℤ (ZMod m))).obj (ModuleCat.of ℤ (ZMod n)) ≅
      ModuleCat.of ℤ (ZMod (Nat.gcd m n)) := by
  let A := ModuleCat.of ℤ (ZMod m)
  let F := (Tor C 1).obj A
  exact (F.mapIso (quotientResidueIso n)).symm ≪≫
    IntCyclicDerivedTor.torOneEquivKernel A n hn.ne' ≪≫
    (ZModGcdCyclicKernel.gcdResiduesEquivKernel m n hm).symm.toModuleIso

end
end ManuscriptAudit.IntCyclicDerivedTorGcd

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntCyclicDerivedTorGcd.torOneIsoGcdResidues
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
