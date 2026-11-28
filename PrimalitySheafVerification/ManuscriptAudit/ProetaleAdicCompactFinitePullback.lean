import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPowerSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCompactCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Actual reduction of compactly supported adic cohomology is
surjective when the next integral group vanishes. This transfers
the scalar of a native pullback to the finite constant sheaf. -/

namespace ManuscriptAudit.ProetaleAdicCompactFinitePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open OpenProetaleExtension (extensionByZero)
open ProetaleAdicPowerSequence (compactSequence compactSequence_shortExact)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleConstantRestriction (constant)
open ProetaleOpenContinuousPullback (compactMap)
open ProetaleOpenCompactCoefficientNaturality (compact_natural discreteIso discreteMap
  discrete_cohomology_comparison)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
  (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)

private abbrev HAd (n : ℕ) := Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] U)) n
private abbrev HRes (n : ℕ) := Sheaf.H
  ((extensionByZero j A).obj (functions (ZMod (ℓ ^ r)) U)) n
private abbrev HConst (n : ℕ) := Sheaf.H
  ((extensionByZero j A).obj (constant U (ZMod (ℓ ^ r)))) n

/-- The literal compact-support residue map at a fixed open immersion. -/
abbrev reduction (n : ℕ) : HAd j ℓ n →+ HRes j ℓ r n :=
  Sheaf.H.map (compactSequence ℓ r j).g n

set_option maxHeartbeats 6300000 in
theorem reduction_surjective (n : ℕ) (h : Subsingleton (HAd j ℓ (n + 1))) :
    Function.Surjective (reduction j ℓ r n) := by
  let T := (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  let S := compactSequence ℓ r j
  let hS := compactSequence_shortExact ℓ r j
  intro x
  have hx : x.comp hS.extClass (rfl : n + 1 = n + 1) = 0 :=
    h.elim _ _
  exact Ext.covariant_sequence_exact₃ T hS x (rfl : n + 1 = n + 1) hx

variable (f : X ⟶ X) (g : U ⟶ U) (H : IsPullback j g f j)

set_option maxHeartbeats 6500000 in
/-- Actual compact continuous pullback and the residue map form a commuting square. -/
theorem reduction_natural (n : ℕ) (x : HAd j ℓ n) :
    compactMap f g j j H (ZMod (ℓ ^ r)) n (reduction j ℓ r n x) =
      reduction j ℓ r n (compactMap f g j j H ℤ_[ℓ] n x) := by
  exact compact_natural f g j j H (PadicInt.toZModPow r).toAddMonoidHom
    (PadicResidueHomeomorphism.reduction_continuous ℓ r) n x

set_option maxHeartbeats 6500000 in
/-- A scalar established on actual integral compact cohomology is the same scalar
on the actual compact cohomology of the finite constant sheaf. -/
theorem constant_scalar (n m : ℕ) (h : Subsingleton (HAd j ℓ (n + 1)))
    (hs : ∀ x : HAd j ℓ n, compactMap f g j j H ℤ_[ℓ] n x = m • x)
    (x : HConst j ℓ r n) :
    discreteMap f g j j H (ZMod (ℓ ^ r)) n x = m • x := by
  let e := discreteIso (ZMod (ℓ ^ r)) j
  let E := cohomologyIso (X := X) e n
  let R := reduction j ℓ r n
  obtain ⟨y, hy⟩ := reduction_surjective j ℓ r n h (E x)
  apply E.injective
  change Sheaf.H.map e.hom n (discreteMap f g j j H (ZMod (ℓ ^ r)) n x) =
    Sheaf.H.map e.hom n (m • x)
  rw [← discrete_cohomology_comparison f g j j H (ZMod (ℓ ^ r)) n x]
  change compactMap f g j j H (ZMod (ℓ ^ r)) n (E x) = E (m • x)
  rw [← hy, reduction_natural, hs, map_nsmul, map_nsmul, hy]

end
end ManuscriptAudit.ProetaleAdicCompactFinitePullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleAdicCompactFinitePullback.reduction_surjective,
      ``ManuscriptAudit.ProetaleAdicCompactFinitePullback.constant_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
