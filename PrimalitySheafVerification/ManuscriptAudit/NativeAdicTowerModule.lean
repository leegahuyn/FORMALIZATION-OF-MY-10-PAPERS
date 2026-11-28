import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicResidueScalar

/-! The actual cohomology of each finite residue coefficient has its induced
adic module structure, and the actual residue transitions are linear. -/

namespace ManuscriptAudit.NativeAdicTowerModule

open AlgebraicGeometry CategoryTheory
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees
open NativeAdicResidueScalar

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

abbrev Level (d n : ℕ) := Sheaf.H (finiteCoefficient X ℓ n) d

local instance (d n : ℕ) : Module (ZMod (ℓ^n)) (Level X ℓ d n) :=
  AddCommGroup.zmodModule (residue_cohomology_annihilated X ℓ d n)

local instance levelModule (d n : ℕ) : Module ℤ_[ℓ] (Level X ℓ d n) :=
  Module.compHom (Level X ℓ d n) (PadicInt.toZModPow n)

theorem level_smul_val (d n : ℕ) (a : ℤ_[ℓ]) (x : Level X ℓ d n) :
    a • x = (PadicInt.toZModPow n a).val • x := by
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime ℓ).ne_zero⟩
  change PadicInt.toZModPow n a • x = _
  calc
    _ = ((PadicInt.toZModPow n a).val : ZMod (ℓ^n)) • x :=
      congrArg (fun r : ZMod (ℓ^n) => r • x) (ZMod.natCast_zmod_val _).symm
    _ = _ := Nat.cast_smul_eq_nsmul (ZMod (ℓ^n)) (PadicInt.toZModPow n a).val x

/-- The actual finite transition maps commute with the adic scalar actions. -/
theorem step_smul (d n : ℕ) (r : ℤ_[ℓ]) (x : Level X ℓ d (n+1)) :
    nativeStep X ℓ d n (r • x) = r • nativeStep X ℓ d n x := by
  let z := PadicInt.toZModPow (n+1) r
  let s := PadicResidueSystems.reduction ℓ (Nat.le_succ n)
  letI : NeZero (ℓ ^ (n+1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hz : (z.val : ZMod (ℓ^n)) = PadicInt.toZModPow n r := by
    calc
      _ = s (z.val : ZMod (ℓ^(n+1))) := (map_natCast s z.val).symm
      _ = s z := by rw [ZMod.natCast_zmod_val]
      _ = _ := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n+1) (Nat.le_succ n)) r
  rw [level_smul_val X ℓ d (n+1), map_nsmul]
  change z.val • nativeStep X ℓ d n x =
    PadicInt.toZModPow n r • nativeStep X ℓ d n x
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod (ℓ^n)), hz]

/-- The true coherent tuples form an adic submodule of the product of their
finite coefficient cohomology groups. -/
def tower (d : ℕ) : Submodule ℤ_[ℓ] (∀ n, Level X ℓ d n) where
  toAddSubmonoid := (nativeCompatible X ℓ d).toAddSubmonoid
  smul_mem' r u h := by
    intro n
    change nativeStep X ℓ d n (r • u (n+1)) = r • u n
    rw [step_smul, h n]

local instance (d : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ d) :=
  NativeAdicScalarAction.adicModule X ℓ d

/-- The native integral reduction is linear for the canonical residue actions. -/
def reductionLinear (d : ℕ) : X.EllAdicCohomology ℓ d →ₗ[ℤ_[ℓ]] tower X ℓ d where
  toFun x := ⟨(reductionMap X ℓ d x).val, (reductionMap X ℓ d x).property⟩
  map_add' x y := Subtype.ext (congrArg Subtype.val (map_add (reductionMap X ℓ d) x y))
  map_smul' r x := by
    apply Subtype.ext
    funext n
    change Sheaf.H.map _ d (Sheaf.H.map (NativeAdicScalarAction.scalarMap X ℓ r) d x) =
      r • Sheaf.H.map ((ProetaleCoefficientUniverseLift.lift X).map
        (ProetaleResidueSheaves.residueReduction X ℓ n)) d x
    rw [level_smul_val X ℓ d n]
    exact reduction_scalar X ℓ d n r x

end
end ManuscriptAudit.NativeAdicTowerModule


open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAdicTowerModule.step_smul,
      ``ManuscriptAudit.NativeAdicTowerModule.tower,
      ``ManuscriptAudit.NativeAdicTowerModule.reductionLinear] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
