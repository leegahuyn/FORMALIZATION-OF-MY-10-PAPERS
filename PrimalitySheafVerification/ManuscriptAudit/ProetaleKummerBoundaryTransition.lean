import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSheafTransition

/-! The actual Kummer boundary is coherent across the power maps of
constant roots of unity, before any choice of a cyclic basis. -/

namespace ManuscriptAudit.ProetaleKummerBoundaryTransition

open AlgebraicGeometry CategoryTheory
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerBoundaryNative (unitBoundary)
open ProetaleKummerKernelTransition (kernelTransition kernelBoundary kernelBoundary_transition)
open ProetaleKummerSheafTransition (constantTransition constantKernelIso_naturality)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

local instance pow_neZero (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n (show ℓ.Prime from Fact.out).ne_zero⟩

local instance cast_pow_neZero (n : ℕ) : NeZero ((ℓ ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩

private abbrev e (n : ℕ) := cohomologyIso (X := X) (constantKernelIso k (ℓ ^ n)) 1

set_option maxHeartbeats 1200000 in
/-- Reduction of coefficients sends the actual class of the same unit to the next lower level. -/
theorem unitBoundary_transition (n : ℕ) (u : Sheaf.H (unitSheaf X) 0) :
    Sheaf.H.map (constantTransition (K := K) (X := X) ℓ n) 1 (unitBoundary k (ℓ ^ (n + 1)) u) =
      unitBoundary k (ℓ ^ n) u := by
  let a := unitBoundary k (ℓ ^ (n + 1)) u
  let g := constantTransition (K := K) (X := X) ℓ n
  let d := kernelTransition X ℓ n
  let b := (constantKernelIso k (ℓ ^ n)).hom
  let c := (constantKernelIso k (ℓ ^ (n + 1))).hom
  apply (e k ℓ n).injective
  calc
    _ = Sheaf.H.map (g ≫ b) 1 a := (Sheaf.H.map_comp_apply g b a).symm
    _ = Sheaf.H.map (c ≫ d) 1 a :=
      congrArg (fun t ↦ Sheaf.H.map t 1 a) (constantKernelIso_naturality k ℓ n)
    _ = Sheaf.H.map d 1 (e k ℓ (n + 1) a) :=
      Sheaf.H.map_comp_apply c d a
    _ = Sheaf.H.map d 1 (kernelBoundary k (ℓ ^ (n + 1)) u) := by
      rw [show e k ℓ (n + 1) a = kernelBoundary k (ℓ ^ (n + 1)) u from
        (e k ℓ (n + 1)).apply_symm_apply _]
    _ = kernelBoundary k (ℓ ^ n) u := kernelBoundary_transition ℓ n k u
    _ = _ := ((e k ℓ n).apply_symm_apply _).symm

end
end ManuscriptAudit.ProetaleKummerBoundaryTransition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleKummerBoundaryTransition.unitBoundary_transition
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
